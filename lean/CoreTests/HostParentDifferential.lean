import KatLang

/-!
GENERATED FILE - DO NOT EDIT BY HAND.

HOST-DIFF-1: Lean/C# differential corpus of HOST-BUILT ASTs with pre-wired `ScopeCtx`
parent chains (tests/KatLang.Tests/HostParentDifferential/HostParentDifferentialCorpus.cs).
Each program below is `LeanAstEncoder`'s encoding of the SAME constructed C# AST the C#
evaluator ran on every route (plain, counted, generic, optimized, suspending async); each
`#guard` pins the C# neutral observation and the C# published zero-argument cache entries
(per property name, and in total). A failing guard is a Lean/C# divergence on that case.

Partition (machine-checked by the `*CaseIds.length` guards below):
- corpus cases: 88
- comparable cases: 86
- known HOST-LEAN-O6 divergences, pinned on both sides and excluded from comparison: 2

Regenerate from the repo root with:
  $env:KATLANG_REGENERATE_HOST_PARENT_DIFFERENTIAL = "1"
  dotnet test .\KatLang.slnx --filter HostParentDifferential
-/

namespace HostParentDifferential
open KatLang

-- Compact graph terms contain sequential lets; this bounds elaboration of the
-- accepted join-spine fixtures without changing any evaluator limit or observation.
set_option maxRecDepth 4096

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
  | .missingOutput => "missingOutput"
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
  | .missingOutput => some { kind := "missingOutput" }
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

/-- Published zero-argument property cache entries of one run named `name` (C#: the entries the
    run-scoped publication law PUBLISHED for bindings of that name). -/
def cacheEntries (e : Expr) (name : String) : Nat :=
  match runResultWithState e with
  | .ok (_, state) => (state.zeroArgPropertyCache.filter (·.1.propertyName == name)).length
  | .error _ => 0

/-- Every published zero-argument property cache entry of one run. -/
def cacheTotal (e : Expr) : Nat :=
  match runResultWithState e with
  | .ok (_, state) => state.zeroArgPropertyCache.length
  | .error _ => 0

-- HP-01a: host parent property read through an opened block
def hp_01a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.num 7])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_01a == "ok raw=7 n=1"
#guard cacheEntries hp_01a "P" == 1
#guard cacheEntries hp_01a "Run" == 1
#guard cacheTotal hp_01a == 2

-- HP-01b: three reads of one host property share ONE entry
def hp_01b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.num 7])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.binary .add (.resolve "P") (.resolve "P")) (.resolve "P"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_01b == "ok raw=21 n=1"
#guard cacheEntries hp_01b "P" == 1
#guard cacheEntries hp_01b "Run" == 1
#guard cacheTotal hp_01b == 2

-- HP-01c: a dynamically reading host property is cached once per run (first caller's x)
def hp_01c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.param "x"])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_01c == "ok raw=S[1, 1] n=1"
#guard cacheEntries hp_01c "P" == 1
#guard cacheEntries hp_01c "Run" == 1
#guard cacheTotal hp_01c == 2

-- HP-01d: a public host property is read by the block like a private one
def hp_01d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "P" (alg [] [] [] [.num 3])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .mul (.resolve "P") (.num 2))])] [])))] [] [.resolve "Run"]))
#guard obs hp_01d == "ok raw=6 n=1"
#guard cacheEntries hp_01d "P" == 1
#guard cacheEntries hp_01d "Run" == 1
#guard cacheTotal hp_01d == 2

-- HP-02a: a grandparent host level is reached through its parent level
def hp_02a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none none)) [] [] [privateProp "W" (alg [] [] [] [.num 2])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.binary .mul (.resolve "V") (.num 10)) (.resolve "W"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_02a == "ok raw=12 n=1"
#guard cacheEntries hp_02a "Run" == 1
#guard cacheEntries hp_02a "V" == 1
#guard cacheEntries hp_02a "W" == 1
#guard cacheTotal hp_02a == 3

-- HP-02b: the nearest declaring level wins (parent V shadows grandparent V)
def hp_02b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none none)) [] [] [privateProp "V" (alg [] [] [] [.num 2])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"])] [])))] [] [.resolve "Run"]))
#guard obs hp_02b == "ok raw=2 n=1"
#guard cacheEntries hp_02b "Run" == 1
#guard cacheEntries hp_02b "V" == 1
#guard cacheTotal hp_02b == 2

-- HP-02c: a host level's own property beats its opened provider (ownership before opens)
def hp_02c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [(.algorithmExpr (alg [] [] [publicProp "V" (alg [] [] [] [.num 5])] []))] [privateProp "V" (alg [] [] [] [.num 2])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"])] [])))] [] [.resolve "Run"]))
#guard obs hp_02c == "ok raw=2 n=1"
#guard cacheEntries hp_02c "Run" == 1
#guard cacheEntries hp_02c "V" == 1
#guard cacheTotal hp_02c == 2

-- HP-02d: a grandparent's property beats the parent level's open (the whole owner walk first)
def hp_02d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none none)) [] [(.algorithmExpr (alg [] [] [publicProp "V" (alg [] [] [] [.num 5])] []))] [] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"])] [])))] [] [.resolve "Run"]))
#guard obs hp_02d == "ok raw=1 n=1"
#guard cacheEntries hp_02d "Run" == 1
#guard cacheEntries hp_02d "V" == 1
#guard cacheTotal hp_02d == 2

-- HP-02e: a name no level declares falls back to a host level's open provider
def hp_02e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none none)) [] [(.algorithmExpr (alg [] [] [publicProp "U" (alg [] [] [] [.num 5])] []))] [] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.resolve "U") (.resolve "V"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_02e == "ok raw=6 n=1"
#guard cacheEntries hp_02e "Run" == 1
#guard cacheEntries hp_02e "U" == 1
#guard cacheEntries hp_02e "V" == 1
#guard cacheTotal hp_02e == 3

-- HP-02f: an undeclared name under a host chain is an unknown name
def hp_02f : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none none)) [] [] [privateProp "W" (alg [] [] [] [.num 2])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "Z"])] [])))] [] [.resolve "Run"]))
#guard obs hp_02f == "err unknownName"
#guard errorObs hp_02f == .matched (some { kind := "unknownName", names := ["Z"], counts := [] })

-- HP-03a: a block opens a host-declared namespace and reads its PUBLIC member
def hp_03a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicProp "A" (alg [] [] [] [.num 1]), privateProp "B" (alg [] [] [] [.num 2])] [])] [] [] none none)) (alg [] [.resolve "M"] [publicProp "Run" (alg [] [] [] [.resolve "A"])] [])))] [] [.resolve "Run"]))
#guard obs hp_03a == "ok raw=1 n=1"
#guard cacheEntries hp_03a "A" == 1
#guard cacheEntries hp_03a "Run" == 1
#guard cacheTotal hp_03a == 2

-- HP-03b: a PRIVATE member is not open-provided (structured refusal)
def hp_03b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicProp "A" (alg [] [] [] [.num 1]), privateProp "B" (alg [] [] [] [.num 2])] [])] [] [] none none)) (alg [] [.resolve "M"] [publicProp "Run" (alg [] [] [] [.resolve "B"])] [])))] [] [.resolve "Run"]))
#guard obs hp_03b == "err unknownName"
#guard errorObs hp_03b == .matched (some { kind := "unknownName", names := ["B"], counts := [] })

-- HP-03c: structural dot access selects the declared PRIVATE member of a host namespace
def hp_03c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicProp "A" (alg [] [] [] [.num 1]), privateProp "B" (alg [] [] [] [.num 2])] [])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.dotCall (.resolve "M") "B" none) (.dotCall (.resolve "M") "A" none))])] [])))] [] [.resolve "Run"]))
#guard obs hp_03c == "ok raw=3 n=1"
#guard cacheEntries hp_03c "A" == 1
#guard cacheEntries hp_03c "B" == 1
#guard cacheEntries hp_03c "Run" == 1
#guard cacheTotal hp_03c == 3

-- HP-03d: a dotted open step through a private member is refused
def hp_03d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [privateProp "N" (alg [] [] [publicProp "K" (alg [] [] [] [.num 4])] [])] [])] [] [] none none)) (alg [] [(.dotCall (.resolve "M") "N" none)] [publicProp "Run" (alg [] [] [] [.resolve "K"])] [])))] [] [.resolve "Run"]))
#guard obs hp_03d == "err notPublicProperty"
#guard errorObs hp_03d == .matched (some { kind := "notPublicProperty", names := ["N"], counts := [] })

-- HP-03e: a dotted open step through a public member is open-provided
def hp_03e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicProp "N" (alg [] [] [publicProp "K" (alg [] [] [] [.num 4])] [])] [])] [] [] none none)) (alg [] [(.dotCall (.resolve "M") "N" none)] [publicProp "Run" (alg [] [] [] [.resolve "K"])] [])))] [] [.resolve "Run"]))
#guard obs hp_03e == "ok raw=4 n=1"
#guard cacheEntries hp_03e "K" == 1
#guard cacheEntries hp_03e "Run" == 1
#guard cacheTotal hp_03e == 2

-- HP-04a: a block property shadows the host parent's property of the same name
def hp_04a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"]), privateProp "V" (alg [] [] [] [.num 3])] [])))] [] [.resolve "Run"]))
#guard obs hp_04a == "ok raw=3 n=1"
#guard cacheEntries hp_04a "Run" == 1
#guard cacheEntries hp_04a "V" == 1
#guard cacheTotal hp_04a == 2

-- HP-04b: a block property shadows a host level's open provider
def hp_04b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [(.algorithmExpr (alg [] [] [publicProp "V" (alg [] [] [] [.num 9])] []))] [] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"]), privateProp "V" (alg [] [] [] [.num 3])] [])))] [] [.resolve "Run"]))
#guard obs hp_04b == "ok raw=3 n=1"
#guard cacheEntries hp_04b "Run" == 1
#guard cacheEntries hp_04b "V" == 1
#guard cacheTotal hp_04b == 2

-- HP-04c: a property of the reading body shadows both block and host declarations
def hp_04c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [privateProp "V" (alg [] [] [] [.num 4])] [.resolve "V"]), privateProp "V" (alg [] [] [] [.num 3])] [])))] [] [.resolve "Run"]))
#guard obs hp_04c == "ok raw=4 n=1"
#guard cacheEntries hp_04c "Run" == 1
#guard cacheEntries hp_04c "V" == 1
#guard cacheTotal hp_04c == 2

-- HP-05a: an unactivated local-only host property keys on the ACCESS context: one entry per G call
def hp_05a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateLocalProp "P" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_05a == "ok raw=S[1, 2] n=1"
#guard cacheEntries hp_05a "P" == 2
#guard cacheEntries hp_05a "Run" == 1
#guard cacheTotal hp_05a == 3

-- HP-05b: two reads within ONE access context share the local-only entry
def hp_05b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateLocalProp "P" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G2") [.num 3])]), publicProp "G2" (alg ["x"] [] [] [(.binary .add (.resolve "P") (.resolve "P"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_05b == "ok raw=6 n=1"
#guard cacheEntries hp_05b "P" == 1
#guard cacheEntries hp_05b "Run" == 1
#guard cacheTotal hp_05b == 2

-- HP-05c: a host level's Parameters take no part in property lookup (the name stays unknown)
def hp_05c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "x"])] [])))] [] [.resolve "Run"]))
#guard obs hp_05c == "err unknownName"
#guard errorObs hp_05c == .matched (some { kind := "unknownName", names := ["x"], counts := [] })

-- HP-05d: structural access M.L to a local-only member whose input x is named by the host level's Parameters
def hp_05d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateProp "M" (alg [] [] [publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [(.dotCall (.resolve "M") "L" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_05d == "err localOnlyProperty"
#guard errorObs hp_05d == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })

-- HP-05e: structural access M.L to a local-only member whose input x is named by no level
def hp_05e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [(.dotCall (.resolve "M") "L" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_05e == "err localOnlyProperty"
#guard errorObs hp_05e == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })

-- HP-05f: structural access M.L to a local-only member whose input x is required at owner depth 1, the host level naming it
def hp_05f : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateProp "M" (alg [] [] [{ (publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])) with requiredOwnerDepths := some [("x", some 1)] }] [])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [(.dotCall (.resolve "M") "L" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_05f == "err localOnlyProperty"
#guard errorObs hp_05f == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })

-- HP-05g: structural access M.L to a local-only member whose input x is required at owner depth 1, the host level NOT naming it
def hp_05g : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [{ (publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])) with requiredOwnerDepths := some [("x", some 1)] }] [])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [(.dotCall (.resolve "M") "L" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_05g == "err localOnlyProperty"
#guard errorObs hp_05g == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })

-- HP-05h: open access to a local-only member whose input x is named by the host level's Parameters
def hp_05h : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateProp "M" (alg [] [] [publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [])] [] [] none none)) (alg [] [.resolve "M"] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "L"])] [])))] [] [.resolve "Run"]))
#guard obs hp_05h == "err localOnlyProperty"
#guard errorObs hp_05h == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })

-- HP-05i: open access to a local-only member whose input x is named by no level
def hp_05i : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [])] [] [] none none)) (alg [] [.resolve "M"] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "L"])] [])))] [] [.resolve "Run"]))
#guard obs hp_05i == "err localOnlyProperty"
#guard errorObs hp_05i == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })

-- HP-06a: CACHE-PUB-1: H(x) = P() establishes the empty entry; the later read reuses it
def hp_06a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.param "x"])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "H") [.num 1]), (.call (.resolve "G") [.num 2])]), publicProp "H" (alg ["x"] [] [] [(.call (.resolve "P") [])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_06a == "ok raw=S[1, 1] n=1"
#guard cacheEntries hp_06a "P" == 1
#guard cacheEntries hp_06a "Run" == 1
#guard cacheTotal hp_06a == 2

-- HP-06b: an established entry is never replaced by a later fresh P()
def hp_06b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.param "x"])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "H") [.num 2]), (.call (.resolve "G") [.num 3])]), publicProp "H" (alg ["x"] [] [] [(.call (.resolve "P") [])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_06b == "ok raw=S[1, 2, 1] n=1"
#guard cacheEntries hp_06b "P" == 1
#guard cacheEntries hp_06b "Run" == 1
#guard cacheTotal hp_06b == 2

-- HP-06c: Q-37: the outermost read owns the entry, the re-entrant read publishes nothing
def hp_06c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.call (.resolve "K") [.param "x"])]), privateProp "K" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩, ⟨.bind "n", (alg [] [] [] [(.binary .add (.call (.resolve "G") [(.binary .sub (.param "n") (.num 1))]) (.num 100))])⟩]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 5])])] [])))] [] [.resolve "Run"]))
#guard obs hp_06c == "ok raw=S[101, 101] n=1"
#guard cacheEntries hp_06c "P" == 1
#guard cacheEntries hp_06c "Run" == 1
#guard cacheTotal hp_06c == 2

-- HP-06d: Q-37 with the owning access an explicit P() (CACHE-PUB-1)
def hp_06d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.call (.resolve "K") [.param "x"])]), privateProp "K" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩, ⟨.bind "n", (alg [] [] [] [(.binary .add (.call (.resolve "G") [(.binary .sub (.param "n") (.num 1))]) (.num 100))])⟩]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "H") [.num 1]), (.call (.resolve "G") [.num 5])]), publicProp "H" (alg ["x"] [] [] [(.call (.resolve "P") [])])] [])))] [] [.resolve "Run"]))
#guard obs hp_06d == "ok raw=S[101, 101] n=1"
#guard cacheEntries hp_06d "P" == 1
#guard cacheEntries hp_06d "Run" == 1
#guard cacheTotal hp_06d == 2

-- HP-07a: two calls of a host-declared F keep their own local-only L and M entries
def hp_07a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["x"] [] [privateLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.binary .mul (.param "x") (.num 10))]), privateLocalProp "M" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.binary .add (.resolve "L") (.num 1))])] [.resolve "M"])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])])] [])))] [] [.resolve "Run"]))
#guard obs hp_07a == "ok raw=S[11, 21] n=1"
#guard cacheEntries hp_07a "L" == 2
#guard cacheEntries hp_07a "M" == 2
#guard cacheEntries hp_07a "Run" == 1
#guard cacheTotal hp_07a == 5

-- HP-07b: repeated calls with one argument still bind fresh activations (D2)
def hp_07b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["x"] [] [privateLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.binary .mul (.param "x") (.num 10))]), privateLocalProp "M" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.binary .add (.resolve "L") (.num 1))])] [.resolve "M"])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.call (.resolve "F") [.num 1]) (.call (.resolve "F") [.num 1]))])] [])))] [] [.resolve "Run"]))
#guard obs hp_07b == "ok raw=22 n=1"
#guard cacheEntries hp_07b "L" == 2
#guard cacheEntries hp_07b "M" == 2
#guard cacheEntries hp_07b "Run" == 1
#guard cacheTotal hp_07b == 5

-- HP-08a: two fresh equal host levels, each with its own P: two owners
def hp_08a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.param "x"])] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.param "x"])] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08a == "ok raw=S[1, 2] n=2"
#guard cacheEntries hp_08a "P" == 2
#guard cacheEntries hp_08a "RunA" == 1
#guard cacheEntries hp_08a "RunB" == 1
#guard cacheTotal hp_08a == 4

-- HP-08b: ONE Property object declared by two distinct host levels: two owners (former 5b shape)
def hp_08b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 0) }] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 1) }] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08b == "ok raw=S[1, 2] n=2"
#guard cacheEntries hp_08b "P" == 2
#guard cacheEntries hp_08b "RunA" == 1
#guard cacheEntries hp_08b "RunB" == 1
#guard cacheTotal hp_08b == 4

-- HP-08c: two distinct host levels sharing ONE property list: two owners
def hp_08c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 0) }] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 1) }] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08c == "ok raw=S[1, 2] n=2"
#guard cacheEntries hp_08c "P" == 2
#guard cacheEntries hp_08c "RunA" == 1
#guard cacheEntries hp_08c "RunB" == 1
#guard cacheTotal hp_08c == 4

-- HP-08d: a record `with` copy of a host level is another owner
def hp_08d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 0) }] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 1) }] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08d == "ok raw=S[1, 2] n=2"
#guard cacheEntries hp_08d "P" == 2
#guard cacheEntries hp_08d "RunA" == 1
#guard cacheEntries hp_08d "RunB" == 1
#guard cacheTotal hp_08d == 4

-- HP-08e: distinct parent objects over record-equal grandparents (copies) keep two owners
def hp_08e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 0) }] [] [] none none)) [] [] [] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 1) }] [] [] none none)) [] [] [] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08e == "ok raw=S[1, 2] n=2"
#guard cacheEntries hp_08e "P" == 2
#guard cacheEntries hp_08e "RunA" == 1
#guard cacheEntries hp_08e "RunB" == 1
#guard cacheTotal hp_08e == 4

-- HP-08f: two distinct host levels with distinct declarations of different values
def hp_08f : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.num 10])] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.num 20])] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08f == "ok raw=S[10, 20] n=2"
#guard cacheEntries hp_08f "P" == 2
#guard cacheEntries hp_08f "RunA" == 1
#guard cacheEntries hp_08f "RunB" == 1
#guard cacheTotal hp_08f == 4

-- HP-08g: NEED-04: F from two fresh equal host levels is two callables
def hp_08g : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "F" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7])] [] [] none none)) (alg [] [] [publicProp "FA" (.alias none [] [] (.resolve "F"))] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "F" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7])] [] [] none none)) (alg [] [] [publicProp "FB" (.alias none [] [] (.resolve "F"))] [])))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_08g == "err type"

-- HP-08h: NEED-04: one F Property in two distinct host levels is two callables
def hp_08h : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none none)) (alg [] [] [publicProp "FA" (.alias none [] [] (.resolve "F"))] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 1) }] [] [] none none)) (alg [] [] [publicProp "FB" (.alias none [] [] (.resolve "F"))] [])))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_08h == "err type"

-- HP-08i: NEED-04: one property list in two distinct host levels is two callables
def hp_08i : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none none)) (alg [] [] [publicProp "FA" (.alias none [] [] (.resolve "F"))] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 1) }] [] [] none none)) (alg [] [] [publicProp "FB" (.alias none [] [] (.resolve "F"))] [])))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_08i == "err type"

-- HP-08j: NEED-04: a record `with` copy of the host level is another callable scope
def hp_08j : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none none)) (alg [] [] [publicProp "FA" (.alias none [] [] (.resolve "F"))] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 1) }] [] [] none none)) (alg [] [] [publicProp "FB" (.alias none [] [] (.resolve "F"))] [])))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_08j == "err type"

-- HP-08k: a host level and an evaluator-owned block declaring ONE property list are two owners
def hp_08k : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 0) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 1) }] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])])] []))), (.algorithmExpr (alg [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 2) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 3) }] []))] [] [.resolve "RunA", (.call (.resolve "G") [.num 2])]))
#guard obs hp_08k == "ok raw=S[1, 2] n=2"
#guard cacheEntries hp_08k "P" == 2
#guard cacheEntries hp_08k "RunA" == 1
#guard cacheTotal hp_08k == 3

-- HP-09a: one host level object opened by two blocks: one owner, one entry
def hp_09a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 0) }] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 0) }] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_09a == "ok raw=S[1, 1] n=2"
#guard cacheEntries hp_09a "P" == 1
#guard cacheEntries hp_09a "RunA" == 1
#guard cacheEntries hp_09a "RunB" == 1
#guard cacheTotal hp_09a == 3

-- HP-09b: one grandparent object reached through two distinct children: one owner
def hp_09b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 0) }] [] [] none none)) [] [] [privateProp "W" (alg [] [] [] [.num 1])] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 0) }] [] [] none none)) [] [] [privateProp "W" (alg [] [] [] [.num 2])] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_09b == "ok raw=S[1, 1] n=2"
#guard cacheEntries hp_09b "P" == 1
#guard cacheEntries hp_09b "RunA" == 1
#guard cacheEntries hp_09b "RunB" == 1
#guard cacheTotal hp_09b == 3

-- HP-09c: one opened block object listed twice in one open list is one provider
def hp_09c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 3)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 2) }] [] [] none none)) (alg [] [] [{ (publicProp "Run" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]))) with identity := some (.shared 0) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 1) }] [])))), (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 3)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 2) }] [] [] none none)) (alg [] [] [{ (publicProp "Run" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]))) with identity := some (.shared 0) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 1) }] []))))] [] [.resolve "Run"]))
#guard obs hp_09c == "ok raw=S[1, 1] n=1"
#guard cacheEntries hp_09c "P" == 1
#guard cacheEntries hp_09c "Run" == 1
#guard cacheTotal hp_09c == 2

-- HP-09d: NEED-04: F reached through ONE host level object twice is one callable
def hp_09d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none none)) (alg [] [] [publicProp "FA" (.alias none [] [] (.resolve "F"))] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none none)) (alg [] [] [publicProp "FB" (.alias none [] [] (.resolve "F"))] [])))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_09d == "ok raw=0 n=1"
#guard cacheEntries hp_09d "FA" == 1
#guard cacheEntries hp_09d "FB" == 1
#guard cacheTotal hp_09d == 2

-- HP-10a: a block opens a dotted path into a host-declared namespace
def hp_10a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Lib" (alg [] [] [publicProp "N" (alg [] [] [publicProp "K" (alg [] [] [] [.num 4])] [])] [])] [] [] none none)) (alg [] [(.dotCall (.resolve "Lib") "N" none)] [publicProp "Run" (alg [] [] [] [.resolve "K"])] [])))] [] [.resolve "Run"]))
#guard obs hp_10a == "ok raw=4 n=1"
#guard cacheEntries hp_10a "K" == 1
#guard cacheEntries hp_10a "Run" == 1
#guard cacheTotal hp_10a == 2

-- HP-10b: a block's own open target is another block with ITS OWN pre-wired parent
def hp_10b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Y" (alg [] [] [] [.num 100])] [] [] none none)) (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Z" (alg [] [] [] [.num 5])] [] [] none none)) (alg [] [] [publicProp "Z2" (alg [] [] [] [(.binary .add (.resolve "Z") (.num 1))])] [])))] [publicProp "Run" (alg [] [] [] [(.binary .add (.resolve "Z2") (.resolve "Y"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_10b == "ok raw=106 n=1"
#guard cacheEntries hp_10b "Run" == 1
#guard cacheEntries hp_10b "Y" == 1
#guard cacheEntries hp_10b "Z" == 1
#guard cacheEntries hp_10b "Z2" == 1
#guard cacheTotal hp_10b == 4

-- HP-10c: structural member access into a host-declared object
def hp_10c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Obj" (alg [] [] [publicProp "A" (alg [] [] [] [.num 2]), privateProp "B" (alg [] [] [] [.num 3])] [])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.dotCall (.resolve "Obj") "A" none) (.dotCall (.resolve "Obj") "B" none))])] [])))] [] [.resolve "Run"]))
#guard obs hp_10c == "ok raw=5 n=1"
#guard cacheEntries hp_10c "A" == 1
#guard cacheEntries hp_10c "B" == 1
#guard cacheEntries hp_10c "Run" == 1
#guard cacheTotal hp_10c == 3

-- HP-10d: a host level's own open target supplies a name to the block
def hp_10d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [(.algorithmExpr (alg [] [] [publicProp "Q" (alg [] [] [] [.num 8])] []))] [] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "Q"])] [])))] [] [.resolve "Run"]))
#guard obs hp_10d == "ok raw=8 n=1"
#guard cacheEntries hp_10d "Q" == 1
#guard cacheEntries hp_10d "Run" == 1
#guard cacheTotal hp_10d == 2

-- HP-10e: a member of a member through a two-level host chain
def hp_10e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "Outer" (alg [] [] [publicProp "Mid" (alg [] [] [publicProp "Leaf" (alg [] [] [] [.num 6])] [])] [])] [] [] none none)) [] [] [privateProp "W" (alg [] [] [] [.num 1])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.dotCall (.dotCall (.resolve "Outer") "Mid" none) "Leaf" none) (.resolve "W"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_10e == "ok raw=7 n=1"
#guard cacheEntries hp_10e "Leaf" == 1
#guard cacheEntries hp_10e "Run" == 1
#guard cacheEntries hp_10e "W" == 1
#guard cacheTotal hp_10e == 3

-- HP-10f: a shared expression diamond in a host parent uses compact Lean let terms
def hp_10f : Expr :=
  (let hd0 : Expr := .resolve "P"; let hd1 : Algorithm := (alg [] [] [] [hd0]); let hd2 : Expr := .num 1; let hd3 : Expr := (.binary .add (hd2) (hd2)); let hd4 : Expr := (.binary .add (hd3) (hd3)); let hd5 : Expr := (.binary .add (hd4) (hd4)); let hd6 : Expr := (.binary .add (hd5) (hd5)); let hd7 : Expr := (.binary .add (hd6) (hd6)); let hd8 : Expr := (.binary .add (hd7) (hd7)); let hd9 : Expr := (.binary .add (hd8) (hd8)); let hd10 : Expr := (.binary .add (hd9) (hd9)); let hd11 : Expr := (.binary .add (hd10) (hd10)); let hd12 : Expr := (.binary .add (hd11) (hd11)); let hd13 : Expr := (.binary .add (hd12) (hd12)); let hd14 : Expr := (.binary .add (hd13) (hd13)); let hd15 : Algorithm := (alg [] [] [] [hd14]); let hd16 : ScopeCtx := (ScopeCtx.mk none [] [] [privateProp "P" hd15] [] [] none none); let hd17 : Algorithm := (Algorithm.withParent (some hd16) (alg [] [] [publicProp "Run" hd1] [])); let hd18 : Expr := (.algorithmExpr hd17); let hd19 : Expr := .resolve "Run"; let hd20 : Algorithm := (alg [] [hd18] [] [hd19]); let hd21 : Expr := (.algorithmExpr hd20); hd21)
#guard obs hp_10f == "ok raw=4096 n=1"
#guard cacheEntries hp_10f "P" == 1
#guard cacheEntries hp_10f "Run" == 1
#guard cacheTotal hp_10f == 2

-- HP-10g: compact terms keep the declaring contexts of shared host properties distinct
def hp_10g : Expr :=
  (let hd0 : Expr := .resolve "G"; let hd1 : Expr := .num 1; let hd2 : Expr := (.call (hd0) [hd1]); let hd3 : Algorithm := (alg [] [] [] [hd2]); let hd4 : Expr := .resolve "P"; let hd5 : Algorithm := (alg ["x"] [] [] [hd4]); let hd6 : Expr := .param "x"; let hd7 : Algorithm := (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [hd6])); let hd8 : Expr := .num 1; let hd9 : Expr := (.binary .add (hd8) (hd8)); let hd10 : Expr := (.binary .add (hd9) (hd9)); let hd11 : Expr := (.binary .add (hd10) (hd10)); let hd12 : Expr := (.binary .add (hd11) (hd11)); let hd13 : Expr := (.binary .add (hd12) (hd12)); let hd14 : Expr := (.binary .add (hd13) (hd13)); let hd15 : Expr := (.binary .add (hd14) (hd14)); let hd16 : Expr := (.binary .add (hd15) (hd15)); let hd17 : Expr := (.binary .add (hd16) (hd16)); let hd18 : Expr := (.binary .add (hd17) (hd17)); let hd19 : Expr := (.binary .add (hd18) (hd18)); let hd20 : Expr := (.binary .add (hd19) (hd19)); let hd21 : Algorithm := (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [hd20])); let hd22 : ScopeCtx := (ScopeCtx.mk none [] [] [{ (privateProp "P" hd7) with identity := some (.shared 0) }, { (privateProp "Large" hd21) with identity := some (.shared 1) }] [] [] none none); let hd23 : Algorithm := (Algorithm.withParent (some hd22) (alg [] [] [publicProp "RunA" hd3, publicProp "G" hd5] [])); let hd24 : Expr := (.algorithmExpr hd23); let hd25 : Expr := .resolve "G"; let hd26 : Expr := .num 2; let hd27 : Expr := (.call (hd25) [hd26]); let hd28 : Algorithm := (alg [] [] [] [hd27]); let hd29 : Expr := .resolve "P"; let hd30 : Algorithm := (alg ["x"] [] [] [hd29]); let hd31 : Expr := .param "x"; let hd32 : Algorithm := (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [hd31])); let hd33 : Expr := .num 1; let hd34 : Expr := (.binary .add (hd33) (hd33)); let hd35 : Expr := (.binary .add (hd34) (hd34)); let hd36 : Expr := (.binary .add (hd35) (hd35)); let hd37 : Expr := (.binary .add (hd36) (hd36)); let hd38 : Expr := (.binary .add (hd37) (hd37)); let hd39 : Expr := (.binary .add (hd38) (hd38)); let hd40 : Expr := (.binary .add (hd39) (hd39)); let hd41 : Expr := (.binary .add (hd40) (hd40)); let hd42 : Expr := (.binary .add (hd41) (hd41)); let hd43 : Expr := (.binary .add (hd42) (hd42)); let hd44 : Expr := (.binary .add (hd43) (hd43)); let hd45 : Expr := (.binary .add (hd44) (hd44)); let hd46 : Algorithm := (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [hd45])); let hd47 : ScopeCtx := (ScopeCtx.mk none [] [] [{ (privateProp "P" hd32) with identity := some (.shared 2) }, { (privateProp "Large" hd46) with identity := some (.shared 3) }] [] [] none none); let hd48 : Algorithm := (Algorithm.withParent (some hd47) (alg [] [] [publicProp "RunB" hd28, publicProp "G" hd30] [])); let hd49 : Expr := (.algorithmExpr hd48); let hd50 : Expr := .resolve "RunA"; let hd51 : Expr := .resolve "RunB"; let hd52 : Algorithm := (alg [] [hd24, hd49] [] [hd50, hd51]); let hd53 : Expr := (.algorithmExpr hd52); hd53)
#guard obs hp_10g == "ok raw=S[1, 2] n=2"
#guard cacheEntries hp_10g "Large" == 0
#guard cacheEntries hp_10g "P" == 2
#guard cacheEntries hp_10g "RunA" == 1
#guard cacheEntries hp_10g "RunB" == 1
#guard cacheTotal hp_10g == 4

-- HP-10h: an evaluator-accepted spread spine beyond recursive depth uses iterative compact printing
def hp_10h : Expr :=
  (let hd0 : Expr := .resolve "P"; let hd1 : Algorithm := (alg [] [] [] [hd0]); let hd2 : Expr := .num 1; let hd3 : Expr := (.sequenceSpread (hd2)); let hd4 : Expr := (.sequenceSpread (hd3)); let hd5 : Expr := (.sequenceSpread (hd4)); let hd6 : Expr := (.sequenceSpread (hd5)); let hd7 : Expr := (.sequenceSpread (hd6)); let hd8 : Expr := (.sequenceSpread (hd7)); let hd9 : Expr := (.sequenceSpread (hd8)); let hd10 : Expr := (.sequenceSpread (hd9)); let hd11 : Expr := (.sequenceSpread (hd10)); let hd12 : Expr := (.sequenceSpread (hd11)); let hd13 : Expr := (.sequenceSpread (hd12)); let hd14 : Expr := (.sequenceSpread (hd13)); let hd15 : Expr := (.sequenceSpread (hd14)); let hd16 : Expr := (.sequenceSpread (hd15)); let hd17 : Expr := (.sequenceSpread (hd16)); let hd18 : Expr := (.sequenceSpread (hd17)); let hd19 : Expr := (.sequenceSpread (hd18)); let hd20 : Expr := (.sequenceSpread (hd19)); let hd21 : Expr := (.sequenceSpread (hd20)); let hd22 : Expr := (.sequenceSpread (hd21)); let hd23 : Expr := (.sequenceSpread (hd22)); let hd24 : Expr := (.sequenceSpread (hd23)); let hd25 : Expr := (.sequenceSpread (hd24)); let hd26 : Expr := (.sequenceSpread (hd25)); let hd27 : Expr := (.sequenceSpread (hd26)); let hd28 : Expr := (.sequenceSpread (hd27)); let hd29 : Expr := (.sequenceSpread (hd28)); let hd30 : Expr := (.sequenceSpread (hd29)); let hd31 : Expr := (.sequenceSpread (hd30)); let hd32 : Expr := (.sequenceSpread (hd31)); let hd33 : Expr := (.sequenceSpread (hd32)); let hd34 : Expr := (.sequenceSpread (hd33)); let hd35 : Expr := (.sequenceSpread (hd34)); let hd36 : Expr := (.sequenceSpread (hd35)); let hd37 : Expr := (.sequenceSpread (hd36)); let hd38 : Expr := (.sequenceSpread (hd37)); let hd39 : Expr := (.sequenceSpread (hd38)); let hd40 : Expr := (.sequenceSpread (hd39)); let hd41 : Expr := (.sequenceSpread (hd40)); let hd42 : Expr := (.sequenceSpread (hd41)); let hd43 : Expr := (.sequenceSpread (hd42)); let hd44 : Expr := (.sequenceSpread (hd43)); let hd45 : Expr := (.sequenceSpread (hd44)); let hd46 : Expr := (.sequenceSpread (hd45)); let hd47 : Expr := (.sequenceSpread (hd46)); let hd48 : Expr := (.sequenceSpread (hd47)); let hd49 : Expr := (.sequenceSpread (hd48)); let hd50 : Expr := (.sequenceSpread (hd49)); let hd51 : Expr := (.sequenceSpread (hd50)); let hd52 : Expr := (.sequenceSpread (hd51)); let hd53 : Expr := (.sequenceSpread (hd52)); let hd54 : Expr := (.sequenceSpread (hd53)); let hd55 : Expr := (.sequenceSpread (hd54)); let hd56 : Expr := (.sequenceSpread (hd55)); let hd57 : Expr := (.sequenceSpread (hd56)); let hd58 : Expr := (.sequenceSpread (hd57)); let hd59 : Expr := (.sequenceSpread (hd58)); let hd60 : Expr := (.sequenceSpread (hd59)); let hd61 : Expr := (.sequenceSpread (hd60)); let hd62 : Expr := (.sequenceSpread (hd61)); let hd63 : Expr := (.sequenceSpread (hd62)); let hd64 : Expr := (.sequenceSpread (hd63)); let hd65 : Expr := (.sequenceSpread (hd64)); let hd66 : Expr := (.sequenceSpread (hd65)); let hd67 : Expr := (.sequenceSpread (hd66)); let hd68 : Expr := (.sequenceSpread (hd67)); let hd69 : Expr := (.sequenceSpread (hd68)); let hd70 : Expr := (.sequenceSpread (hd69)); let hd71 : Expr := (.sequenceSpread (hd70)); let hd72 : Expr := (.sequenceSpread (hd71)); let hd73 : Expr := (.sequenceSpread (hd72)); let hd74 : Expr := (.sequenceSpread (hd73)); let hd75 : Expr := (.sequenceSpread (hd74)); let hd76 : Expr := (.sequenceSpread (hd75)); let hd77 : Expr := (.sequenceSpread (hd76)); let hd78 : Expr := (.sequenceSpread (hd77)); let hd79 : Expr := (.sequenceSpread (hd78)); let hd80 : Expr := (.sequenceSpread (hd79)); let hd81 : Expr := (.sequenceSpread (hd80)); let hd82 : Expr := (.sequenceSpread (hd81)); let hd83 : Expr := (.sequenceSpread (hd82)); let hd84 : Expr := (.sequenceSpread (hd83)); let hd85 : Expr := (.sequenceSpread (hd84)); let hd86 : Expr := (.sequenceSpread (hd85)); let hd87 : Expr := (.sequenceSpread (hd86)); let hd88 : Expr := (.sequenceSpread (hd87)); let hd89 : Expr := (.sequenceSpread (hd88)); let hd90 : Expr := (.sequenceSpread (hd89)); let hd91 : Expr := (.sequenceSpread (hd90)); let hd92 : Expr := (.sequenceSpread (hd91)); let hd93 : Expr := (.sequenceSpread (hd92)); let hd94 : Expr := (.sequenceSpread (hd93)); let hd95 : Expr := (.sequenceSpread (hd94)); let hd96 : Expr := (.sequenceSpread (hd95)); let hd97 : Expr := (.sequenceSpread (hd96)); let hd98 : Expr := (.sequenceSpread (hd97)); let hd99 : Expr := (.sequenceSpread (hd98)); let hd100 : Expr := (.sequenceSpread (hd99)); let hd101 : Expr := (.sequenceSpread (hd100)); let hd102 : Expr := (.sequenceSpread (hd101)); let hd103 : Expr := (.sequenceSpread (hd102)); let hd104 : Expr := (.sequenceSpread (hd103)); let hd105 : Expr := (.sequenceSpread (hd104)); let hd106 : Expr := (.sequenceSpread (hd105)); let hd107 : Expr := (.sequenceSpread (hd106)); let hd108 : Expr := (.sequenceSpread (hd107)); let hd109 : Expr := (.sequenceSpread (hd108)); let hd110 : Expr := (.sequenceSpread (hd109)); let hd111 : Expr := (.sequenceSpread (hd110)); let hd112 : Expr := (.sequenceSpread (hd111)); let hd113 : Expr := (.sequenceSpread (hd112)); let hd114 : Expr := (.sequenceSpread (hd113)); let hd115 : Expr := (.sequenceSpread (hd114)); let hd116 : Expr := (.sequenceSpread (hd115)); let hd117 : Expr := (.sequenceSpread (hd116)); let hd118 : Expr := (.sequenceSpread (hd117)); let hd119 : Expr := (.sequenceSpread (hd118)); let hd120 : Expr := (.sequenceSpread (hd119)); let hd121 : Expr := (.sequenceSpread (hd120)); let hd122 : Expr := (.sequenceSpread (hd121)); let hd123 : Expr := (.sequenceSpread (hd122)); let hd124 : Expr := (.sequenceSpread (hd123)); let hd125 : Expr := (.sequenceSpread (hd124)); let hd126 : Expr := (.sequenceSpread (hd125)); let hd127 : Expr := (.sequenceSpread (hd126)); let hd128 : Expr := (.sequenceSpread (hd127)); let hd129 : Expr := (.sequenceSpread (hd128)); let hd130 : Expr := (.sequenceSpread (hd129)); let hd131 : Expr := (.sequenceSpread (hd130)); let hd132 : Expr := (.sequenceSpread (hd131)); let hd133 : Expr := (.sequenceSpread (hd132)); let hd134 : Expr := (.sequenceSpread (hd133)); let hd135 : Expr := (.sequenceSpread (hd134)); let hd136 : Expr := (.sequenceSpread (hd135)); let hd137 : Expr := (.sequenceSpread (hd136)); let hd138 : Expr := (.sequenceSpread (hd137)); let hd139 : Expr := (.sequenceSpread (hd138)); let hd140 : Expr := (.sequenceSpread (hd139)); let hd141 : Expr := (.sequenceSpread (hd140)); let hd142 : Expr := (.sequenceSpread (hd141)); let hd143 : Expr := (.sequenceSpread (hd142)); let hd144 : Expr := (.sequenceSpread (hd143)); let hd145 : Expr := (.sequenceSpread (hd144)); let hd146 : Expr := (.sequenceSpread (hd145)); let hd147 : Expr := (.sequenceSpread (hd146)); let hd148 : Expr := (.sequenceSpread (hd147)); let hd149 : Expr := (.sequenceSpread (hd148)); let hd150 : Expr := (.sequenceSpread (hd149)); let hd151 : Expr := (.sequenceSpread (hd150)); let hd152 : Expr := (.sequenceSpread (hd151)); let hd153 : Expr := (.sequenceSpread (hd152)); let hd154 : Expr := (.sequenceSpread (hd153)); let hd155 : Expr := (.sequenceSpread (hd154)); let hd156 : Expr := (.sequenceSpread (hd155)); let hd157 : Expr := (.sequenceSpread (hd156)); let hd158 : Expr := (.sequenceSpread (hd157)); let hd159 : Expr := (.sequenceSpread (hd158)); let hd160 : Expr := (.sequenceSpread (hd159)); let hd161 : Expr := (.sequenceSpread (hd160)); let hd162 : Expr := (.sequenceSpread (hd161)); let hd163 : Expr := (.sequenceSpread (hd162)); let hd164 : Expr := (.sequenceSpread (hd163)); let hd165 : Expr := (.sequenceSpread (hd164)); let hd166 : Expr := (.sequenceSpread (hd165)); let hd167 : Expr := (.sequenceSpread (hd166)); let hd168 : Expr := (.sequenceSpread (hd167)); let hd169 : Expr := (.sequenceSpread (hd168)); let hd170 : Expr := (.sequenceSpread (hd169)); let hd171 : Expr := (.sequenceSpread (hd170)); let hd172 : Expr := (.sequenceSpread (hd171)); let hd173 : Expr := (.sequenceSpread (hd172)); let hd174 : Expr := (.sequenceSpread (hd173)); let hd175 : Expr := (.sequenceSpread (hd174)); let hd176 : Expr := (.sequenceSpread (hd175)); let hd177 : Expr := (.sequenceSpread (hd176)); let hd178 : Expr := (.sequenceSpread (hd177)); let hd179 : Expr := (.sequenceSpread (hd178)); let hd180 : Expr := (.sequenceSpread (hd179)); let hd181 : Expr := (.sequenceSpread (hd180)); let hd182 : Expr := (.sequenceSpread (hd181)); let hd183 : Expr := (.sequenceSpread (hd182)); let hd184 : Expr := (.sequenceSpread (hd183)); let hd185 : Expr := (.sequenceSpread (hd184)); let hd186 : Expr := (.sequenceSpread (hd185)); let hd187 : Expr := (.sequenceSpread (hd186)); let hd188 : Expr := (.sequenceSpread (hd187)); let hd189 : Expr := (.sequenceSpread (hd188)); let hd190 : Expr := (.sequenceSpread (hd189)); let hd191 : Expr := (.sequenceSpread (hd190)); let hd192 : Expr := (.sequenceSpread (hd191)); let hd193 : Expr := (.sequenceSpread (hd192)); let hd194 : Expr := (.sequenceSpread (hd193)); let hd195 : Expr := (.sequenceSpread (hd194)); let hd196 : Expr := (.sequenceSpread (hd195)); let hd197 : Expr := (.sequenceSpread (hd196)); let hd198 : Expr := (.sequenceSpread (hd197)); let hd199 : Expr := (.sequenceSpread (hd198)); let hd200 : Expr := (.sequenceSpread (hd199)); let hd201 : Expr := (.sequenceSpread (hd200)); let hd202 : Expr := (.sequenceSpread (hd201)); let hd203 : Expr := (.sequenceSpread (hd202)); let hd204 : Expr := (.sequenceSpread (hd203)); let hd205 : Expr := (.sequenceSpread (hd204)); let hd206 : Expr := (.sequenceSpread (hd205)); let hd207 : Expr := (.sequenceSpread (hd206)); let hd208 : Expr := (.sequenceSpread (hd207)); let hd209 : Expr := (.sequenceSpread (hd208)); let hd210 : Expr := (.sequenceSpread (hd209)); let hd211 : Expr := (.sequenceSpread (hd210)); let hd212 : Expr := (.sequenceSpread (hd211)); let hd213 : Expr := (.sequenceSpread (hd212)); let hd214 : Expr := (.sequenceSpread (hd213)); let hd215 : Expr := (.sequenceSpread (hd214)); let hd216 : Expr := (.sequenceSpread (hd215)); let hd217 : Expr := (.sequenceSpread (hd216)); let hd218 : Expr := (.sequenceSpread (hd217)); let hd219 : Expr := (.sequenceSpread (hd218)); let hd220 : Expr := (.sequenceSpread (hd219)); let hd221 : Expr := (.sequenceSpread (hd220)); let hd222 : Expr := (.sequenceSpread (hd221)); let hd223 : Expr := (.sequenceSpread (hd222)); let hd224 : Expr := (.sequenceSpread (hd223)); let hd225 : Expr := (.sequenceSpread (hd224)); let hd226 : Expr := (.sequenceSpread (hd225)); let hd227 : Expr := (.sequenceSpread (hd226)); let hd228 : Expr := (.sequenceSpread (hd227)); let hd229 : Expr := (.sequenceSpread (hd228)); let hd230 : Expr := (.sequenceSpread (hd229)); let hd231 : Expr := (.sequenceSpread (hd230)); let hd232 : Expr := (.sequenceSpread (hd231)); let hd233 : Expr := (.sequenceSpread (hd232)); let hd234 : Expr := (.sequenceSpread (hd233)); let hd235 : Expr := (.sequenceSpread (hd234)); let hd236 : Expr := (.sequenceSpread (hd235)); let hd237 : Expr := (.sequenceSpread (hd236)); let hd238 : Expr := (.sequenceSpread (hd237)); let hd239 : Expr := (.sequenceSpread (hd238)); let hd240 : Expr := (.sequenceSpread (hd239)); let hd241 : Expr := (.sequenceSpread (hd240)); let hd242 : Expr := (.sequenceSpread (hd241)); let hd243 : Expr := (.sequenceSpread (hd242)); let hd244 : Expr := (.sequenceSpread (hd243)); let hd245 : Expr := (.sequenceSpread (hd244)); let hd246 : Expr := (.sequenceSpread (hd245)); let hd247 : Expr := (.sequenceSpread (hd246)); let hd248 : Expr := (.sequenceSpread (hd247)); let hd249 : Expr := (.sequenceSpread (hd248)); let hd250 : Expr := (.sequenceSpread (hd249)); let hd251 : Expr := (.sequenceSpread (hd250)); let hd252 : Expr := (.sequenceSpread (hd251)); let hd253 : Expr := (.sequenceSpread (hd252)); let hd254 : Expr := (.sequenceSpread (hd253)); let hd255 : Expr := (.sequenceSpread (hd254)); let hd256 : Expr := (.sequenceSpread (hd255)); let hd257 : Expr := (.sequenceSpread (hd256)); let hd258 : Expr := (.sequenceSpread (hd257)); let hd259 : Expr := (.sequenceSpread (hd258)); let hd260 : Expr := (.sequenceSpread (hd259)); let hd261 : Expr := (.sequenceSpread (hd260)); let hd262 : Expr := (.sequenceSpread (hd261)); let hd263 : Expr := (.sequenceSpread (hd262)); let hd264 : Expr := (.sequenceSpread (hd263)); let hd265 : Expr := (.sequenceSpread (hd264)); let hd266 : Expr := (.sequenceSpread (hd265)); let hd267 : Expr := (.sequenceSpread (hd266)); let hd268 : Expr := (.sequenceSpread (hd267)); let hd269 : Expr := (.sequenceSpread (hd268)); let hd270 : Expr := (.sequenceSpread (hd269)); let hd271 : Expr := (.sequenceSpread (hd270)); let hd272 : Expr := (.sequenceSpread (hd271)); let hd273 : Expr := (.sequenceSpread (hd272)); let hd274 : Expr := (.sequenceSpread (hd273)); let hd275 : Expr := (.sequenceSpread (hd274)); let hd276 : Expr := (.sequenceSpread (hd275)); let hd277 : Expr := (.sequenceSpread (hd276)); let hd278 : Expr := (.sequenceSpread (hd277)); let hd279 : Expr := (.sequenceSpread (hd278)); let hd280 : Expr := (.sequenceSpread (hd279)); let hd281 : Expr := (.sequenceSpread (hd280)); let hd282 : Expr := (.sequenceSpread (hd281)); let hd283 : Expr := (.sequenceSpread (hd282)); let hd284 : Expr := (.sequenceSpread (hd283)); let hd285 : Expr := (.sequenceSpread (hd284)); let hd286 : Expr := (.sequenceSpread (hd285)); let hd287 : Expr := (.sequenceSpread (hd286)); let hd288 : Expr := (.sequenceSpread (hd287)); let hd289 : Expr := (.sequenceSpread (hd288)); let hd290 : Expr := (.sequenceSpread (hd289)); let hd291 : Expr := (.sequenceSpread (hd290)); let hd292 : Expr := (.sequenceSpread (hd291)); let hd293 : Expr := (.sequenceSpread (hd292)); let hd294 : Expr := (.sequenceSpread (hd293)); let hd295 : Expr := (.sequenceSpread (hd294)); let hd296 : Expr := (.sequenceSpread (hd295)); let hd297 : Expr := (.sequenceSpread (hd296)); let hd298 : Expr := (.sequenceSpread (hd297)); let hd299 : Expr := (.sequenceSpread (hd298)); let hd300 : Expr := (.sequenceSpread (hd299)); let hd301 : Expr := (.sequenceSpread (hd300)); let hd302 : Expr := (.sequenceSpread (hd301)); let hd303 : Expr := (.sequenceSpread (hd302)); let hd304 : Algorithm := (alg [] [] [] [hd303]); let hd305 : ScopeCtx := (ScopeCtx.mk none [] [] [privateProp "P" hd304] [] [] none none); let hd306 : Algorithm := (Algorithm.withParent (some hd305) (alg [] [] [publicProp "Run" hd1] [])); let hd307 : Expr := (.algorithmExpr hd306); let hd308 : Expr := .resolve "Run"; let hd309 : Algorithm := (alg [] [hd307] [] [hd308]); let hd310 : Expr := (.algorithmExpr hd309); hd310)
#guard obs hp_10h == "ok raw=1 n=1"
#guard cacheEntries hp_10h "P" == 1
#guard cacheEntries hp_10h "Run" == 1
#guard cacheTotal hp_10h == 2

-- HP-10i: an evaluator-accepted join spine preserves the non-spread empty-leaf rule
def hp_10i : Expr :=
  (let hd0 : Expr := .resolve "P"; let hd1 : Algorithm := (alg [] [] [] [hd0]); let hd2 : Expr := .num 1; let hd3 : Expr := (.emptySequence 0); let hd4 : Expr := (.sequenceConstruct (hd2) (hd3)); let hd5 : Expr := (.emptySequence 0); let hd6 : Expr := (.sequenceConstruct (hd4) (hd5)); let hd7 : Expr := (.emptySequence 0); let hd8 : Expr := (.sequenceConstruct (hd6) (hd7)); let hd9 : Expr := (.emptySequence 0); let hd10 : Expr := (.sequenceConstruct (hd8) (hd9)); let hd11 : Expr := (.emptySequence 0); let hd12 : Expr := (.sequenceConstruct (hd10) (hd11)); let hd13 : Expr := (.emptySequence 0); let hd14 : Expr := (.sequenceConstruct (hd12) (hd13)); let hd15 : Expr := (.emptySequence 0); let hd16 : Expr := (.sequenceConstruct (hd14) (hd15)); let hd17 : Expr := (.emptySequence 0); let hd18 : Expr := (.sequenceConstruct (hd16) (hd17)); let hd19 : Expr := (.emptySequence 0); let hd20 : Expr := (.sequenceConstruct (hd18) (hd19)); let hd21 : Expr := (.emptySequence 0); let hd22 : Expr := (.sequenceConstruct (hd20) (hd21)); let hd23 : Expr := (.emptySequence 0); let hd24 : Expr := (.sequenceConstruct (hd22) (hd23)); let hd25 : Expr := (.emptySequence 0); let hd26 : Expr := (.sequenceConstruct (hd24) (hd25)); let hd27 : Expr := (.emptySequence 0); let hd28 : Expr := (.sequenceConstruct (hd26) (hd27)); let hd29 : Expr := (.emptySequence 0); let hd30 : Expr := (.sequenceConstruct (hd28) (hd29)); let hd31 : Expr := (.emptySequence 0); let hd32 : Expr := (.sequenceConstruct (hd30) (hd31)); let hd33 : Expr := (.emptySequence 0); let hd34 : Expr := (.sequenceConstruct (hd32) (hd33)); let hd35 : Expr := (.emptySequence 0); let hd36 : Expr := (.sequenceConstruct (hd34) (hd35)); let hd37 : Expr := (.emptySequence 0); let hd38 : Expr := (.sequenceConstruct (hd36) (hd37)); let hd39 : Expr := (.emptySequence 0); let hd40 : Expr := (.sequenceConstruct (hd38) (hd39)); let hd41 : Expr := (.emptySequence 0); let hd42 : Expr := (.sequenceConstruct (hd40) (hd41)); let hd43 : Expr := (.emptySequence 0); let hd44 : Expr := (.sequenceConstruct (hd42) (hd43)); let hd45 : Expr := (.emptySequence 0); let hd46 : Expr := (.sequenceConstruct (hd44) (hd45)); let hd47 : Expr := (.emptySequence 0); let hd48 : Expr := (.sequenceConstruct (hd46) (hd47)); let hd49 : Expr := (.emptySequence 0); let hd50 : Expr := (.sequenceConstruct (hd48) (hd49)); let hd51 : Expr := (.emptySequence 0); let hd52 : Expr := (.sequenceConstruct (hd50) (hd51)); let hd53 : Expr := (.emptySequence 0); let hd54 : Expr := (.sequenceConstruct (hd52) (hd53)); let hd55 : Expr := (.emptySequence 0); let hd56 : Expr := (.sequenceConstruct (hd54) (hd55)); let hd57 : Expr := (.emptySequence 0); let hd58 : Expr := (.sequenceConstruct (hd56) (hd57)); let hd59 : Expr := (.emptySequence 0); let hd60 : Expr := (.sequenceConstruct (hd58) (hd59)); let hd61 : Expr := (.emptySequence 0); let hd62 : Expr := (.sequenceConstruct (hd60) (hd61)); let hd63 : Expr := (.emptySequence 0); let hd64 : Expr := (.sequenceConstruct (hd62) (hd63)); let hd65 : Expr := (.emptySequence 0); let hd66 : Expr := (.sequenceConstruct (hd64) (hd65)); let hd67 : Expr := (.emptySequence 0); let hd68 : Expr := (.sequenceConstruct (hd66) (hd67)); let hd69 : Expr := (.emptySequence 0); let hd70 : Expr := (.sequenceConstruct (hd68) (hd69)); let hd71 : Expr := (.emptySequence 0); let hd72 : Expr := (.sequenceConstruct (hd70) (hd71)); let hd73 : Expr := (.emptySequence 0); let hd74 : Expr := (.sequenceConstruct (hd72) (hd73)); let hd75 : Expr := (.emptySequence 0); let hd76 : Expr := (.sequenceConstruct (hd74) (hd75)); let hd77 : Expr := (.emptySequence 0); let hd78 : Expr := (.sequenceConstruct (hd76) (hd77)); let hd79 : Expr := (.emptySequence 0); let hd80 : Expr := (.sequenceConstruct (hd78) (hd79)); let hd81 : Expr := (.emptySequence 0); let hd82 : Expr := (.sequenceConstruct (hd80) (hd81)); let hd83 : Expr := (.emptySequence 0); let hd84 : Expr := (.sequenceConstruct (hd82) (hd83)); let hd85 : Expr := (.emptySequence 0); let hd86 : Expr := (.sequenceConstruct (hd84) (hd85)); let hd87 : Expr := (.emptySequence 0); let hd88 : Expr := (.sequenceConstruct (hd86) (hd87)); let hd89 : Expr := (.emptySequence 0); let hd90 : Expr := (.sequenceConstruct (hd88) (hd89)); let hd91 : Expr := (.emptySequence 0); let hd92 : Expr := (.sequenceConstruct (hd90) (hd91)); let hd93 : Expr := (.emptySequence 0); let hd94 : Expr := (.sequenceConstruct (hd92) (hd93)); let hd95 : Expr := (.emptySequence 0); let hd96 : Expr := (.sequenceConstruct (hd94) (hd95)); let hd97 : Expr := (.emptySequence 0); let hd98 : Expr := (.sequenceConstruct (hd96) (hd97)); let hd99 : Expr := (.emptySequence 0); let hd100 : Expr := (.sequenceConstruct (hd98) (hd99)); let hd101 : Expr := (.emptySequence 0); let hd102 : Expr := (.sequenceConstruct (hd100) (hd101)); let hd103 : Expr := (.emptySequence 0); let hd104 : Expr := (.sequenceConstruct (hd102) (hd103)); let hd105 : Expr := (.emptySequence 0); let hd106 : Expr := (.sequenceConstruct (hd104) (hd105)); let hd107 : Expr := (.emptySequence 0); let hd108 : Expr := (.sequenceConstruct (hd106) (hd107)); let hd109 : Expr := (.emptySequence 0); let hd110 : Expr := (.sequenceConstruct (hd108) (hd109)); let hd111 : Expr := (.emptySequence 0); let hd112 : Expr := (.sequenceConstruct (hd110) (hd111)); let hd113 : Expr := (.emptySequence 0); let hd114 : Expr := (.sequenceConstruct (hd112) (hd113)); let hd115 : Expr := (.emptySequence 0); let hd116 : Expr := (.sequenceConstruct (hd114) (hd115)); let hd117 : Expr := (.emptySequence 0); let hd118 : Expr := (.sequenceConstruct (hd116) (hd117)); let hd119 : Expr := (.emptySequence 0); let hd120 : Expr := (.sequenceConstruct (hd118) (hd119)); let hd121 : Expr := (.emptySequence 0); let hd122 : Expr := (.sequenceConstruct (hd120) (hd121)); let hd123 : Expr := (.emptySequence 0); let hd124 : Expr := (.sequenceConstruct (hd122) (hd123)); let hd125 : Expr := (.emptySequence 0); let hd126 : Expr := (.sequenceConstruct (hd124) (hd125)); let hd127 : Expr := (.emptySequence 0); let hd128 : Expr := (.sequenceConstruct (hd126) (hd127)); let hd129 : Expr := (.emptySequence 0); let hd130 : Expr := (.sequenceConstruct (hd128) (hd129)); let hd131 : Expr := (.emptySequence 0); let hd132 : Expr := (.sequenceConstruct (hd130) (hd131)); let hd133 : Expr := (.emptySequence 0); let hd134 : Expr := (.sequenceConstruct (hd132) (hd133)); let hd135 : Expr := (.emptySequence 0); let hd136 : Expr := (.sequenceConstruct (hd134) (hd135)); let hd137 : Expr := (.emptySequence 0); let hd138 : Expr := (.sequenceConstruct (hd136) (hd137)); let hd139 : Expr := (.emptySequence 0); let hd140 : Expr := (.sequenceConstruct (hd138) (hd139)); let hd141 : Expr := (.emptySequence 0); let hd142 : Expr := (.sequenceConstruct (hd140) (hd141)); let hd143 : Expr := (.emptySequence 0); let hd144 : Expr := (.sequenceConstruct (hd142) (hd143)); let hd145 : Expr := (.emptySequence 0); let hd146 : Expr := (.sequenceConstruct (hd144) (hd145)); let hd147 : Expr := (.emptySequence 0); let hd148 : Expr := (.sequenceConstruct (hd146) (hd147)); let hd149 : Expr := (.emptySequence 0); let hd150 : Expr := (.sequenceConstruct (hd148) (hd149)); let hd151 : Expr := (.emptySequence 0); let hd152 : Expr := (.sequenceConstruct (hd150) (hd151)); let hd153 : Expr := (.emptySequence 0); let hd154 : Expr := (.sequenceConstruct (hd152) (hd153)); let hd155 : Expr := (.emptySequence 0); let hd156 : Expr := (.sequenceConstruct (hd154) (hd155)); let hd157 : Expr := (.emptySequence 0); let hd158 : Expr := (.sequenceConstruct (hd156) (hd157)); let hd159 : Expr := (.emptySequence 0); let hd160 : Expr := (.sequenceConstruct (hd158) (hd159)); let hd161 : Expr := (.emptySequence 0); let hd162 : Expr := (.sequenceConstruct (hd160) (hd161)); let hd163 : Expr := (.emptySequence 0); let hd164 : Expr := (.sequenceConstruct (hd162) (hd163)); let hd165 : Expr := (.emptySequence 0); let hd166 : Expr := (.sequenceConstruct (hd164) (hd165)); let hd167 : Expr := (.emptySequence 0); let hd168 : Expr := (.sequenceConstruct (hd166) (hd167)); let hd169 : Expr := (.emptySequence 0); let hd170 : Expr := (.sequenceConstruct (hd168) (hd169)); let hd171 : Expr := (.emptySequence 0); let hd172 : Expr := (.sequenceConstruct (hd170) (hd171)); let hd173 : Expr := (.emptySequence 0); let hd174 : Expr := (.sequenceConstruct (hd172) (hd173)); let hd175 : Expr := (.emptySequence 0); let hd176 : Expr := (.sequenceConstruct (hd174) (hd175)); let hd177 : Expr := (.emptySequence 0); let hd178 : Expr := (.sequenceConstruct (hd176) (hd177)); let hd179 : Expr := (.emptySequence 0); let hd180 : Expr := (.sequenceConstruct (hd178) (hd179)); let hd181 : Expr := (.emptySequence 0); let hd182 : Expr := (.sequenceConstruct (hd180) (hd181)); let hd183 : Expr := (.emptySequence 0); let hd184 : Expr := (.sequenceConstruct (hd182) (hd183)); let hd185 : Expr := (.emptySequence 0); let hd186 : Expr := (.sequenceConstruct (hd184) (hd185)); let hd187 : Expr := (.emptySequence 0); let hd188 : Expr := (.sequenceConstruct (hd186) (hd187)); let hd189 : Expr := (.emptySequence 0); let hd190 : Expr := (.sequenceConstruct (hd188) (hd189)); let hd191 : Expr := (.emptySequence 0); let hd192 : Expr := (.sequenceConstruct (hd190) (hd191)); let hd193 : Expr := (.emptySequence 0); let hd194 : Expr := (.sequenceConstruct (hd192) (hd193)); let hd195 : Expr := (.emptySequence 0); let hd196 : Expr := (.sequenceConstruct (hd194) (hd195)); let hd197 : Expr := (.emptySequence 0); let hd198 : Expr := (.sequenceConstruct (hd196) (hd197)); let hd199 : Expr := (.emptySequence 0); let hd200 : Expr := (.sequenceConstruct (hd198) (hd199)); let hd201 : Expr := (.emptySequence 0); let hd202 : Expr := (.sequenceConstruct (hd200) (hd201)); let hd203 : Expr := (.emptySequence 0); let hd204 : Expr := (.sequenceConstruct (hd202) (hd203)); let hd205 : Expr := (.emptySequence 0); let hd206 : Expr := (.sequenceConstruct (hd204) (hd205)); let hd207 : Expr := (.emptySequence 0); let hd208 : Expr := (.sequenceConstruct (hd206) (hd207)); let hd209 : Expr := (.emptySequence 0); let hd210 : Expr := (.sequenceConstruct (hd208) (hd209)); let hd211 : Expr := (.emptySequence 0); let hd212 : Expr := (.sequenceConstruct (hd210) (hd211)); let hd213 : Expr := (.emptySequence 0); let hd214 : Expr := (.sequenceConstruct (hd212) (hd213)); let hd215 : Expr := (.emptySequence 0); let hd216 : Expr := (.sequenceConstruct (hd214) (hd215)); let hd217 : Expr := (.emptySequence 0); let hd218 : Expr := (.sequenceConstruct (hd216) (hd217)); let hd219 : Expr := (.emptySequence 0); let hd220 : Expr := (.sequenceConstruct (hd218) (hd219)); let hd221 : Expr := (.emptySequence 0); let hd222 : Expr := (.sequenceConstruct (hd220) (hd221)); let hd223 : Expr := (.emptySequence 0); let hd224 : Expr := (.sequenceConstruct (hd222) (hd223)); let hd225 : Expr := (.emptySequence 0); let hd226 : Expr := (.sequenceConstruct (hd224) (hd225)); let hd227 : Expr := (.emptySequence 0); let hd228 : Expr := (.sequenceConstruct (hd226) (hd227)); let hd229 : Expr := (.emptySequence 0); let hd230 : Expr := (.sequenceConstruct (hd228) (hd229)); let hd231 : Expr := (.emptySequence 0); let hd232 : Expr := (.sequenceConstruct (hd230) (hd231)); let hd233 : Expr := (.emptySequence 0); let hd234 : Expr := (.sequenceConstruct (hd232) (hd233)); let hd235 : Expr := (.emptySequence 0); let hd236 : Expr := (.sequenceConstruct (hd234) (hd235)); let hd237 : Expr := (.emptySequence 0); let hd238 : Expr := (.sequenceConstruct (hd236) (hd237)); let hd239 : Expr := (.emptySequence 0); let hd240 : Expr := (.sequenceConstruct (hd238) (hd239)); let hd241 : Expr := (.emptySequence 0); let hd242 : Expr := (.sequenceConstruct (hd240) (hd241)); let hd243 : Expr := (.emptySequence 0); let hd244 : Expr := (.sequenceConstruct (hd242) (hd243)); let hd245 : Expr := (.emptySequence 0); let hd246 : Expr := (.sequenceConstruct (hd244) (hd245)); let hd247 : Expr := (.emptySequence 0); let hd248 : Expr := (.sequenceConstruct (hd246) (hd247)); let hd249 : Expr := (.emptySequence 0); let hd250 : Expr := (.sequenceConstruct (hd248) (hd249)); let hd251 : Expr := (.emptySequence 0); let hd252 : Expr := (.sequenceConstruct (hd250) (hd251)); let hd253 : Expr := (.emptySequence 0); let hd254 : Expr := (.sequenceConstruct (hd252) (hd253)); let hd255 : Expr := (.emptySequence 0); let hd256 : Expr := (.sequenceConstruct (hd254) (hd255)); let hd257 : Expr := (.emptySequence 0); let hd258 : Expr := (.sequenceConstruct (hd256) (hd257)); let hd259 : Expr := (.emptySequence 0); let hd260 : Expr := (.sequenceConstruct (hd258) (hd259)); let hd261 : Expr := (.emptySequence 0); let hd262 : Expr := (.sequenceConstruct (hd260) (hd261)); let hd263 : Expr := (.emptySequence 0); let hd264 : Expr := (.sequenceConstruct (hd262) (hd263)); let hd265 : Expr := (.emptySequence 0); let hd266 : Expr := (.sequenceConstruct (hd264) (hd265)); let hd267 : Expr := (.emptySequence 0); let hd268 : Expr := (.sequenceConstruct (hd266) (hd267)); let hd269 : Expr := (.emptySequence 0); let hd270 : Expr := (.sequenceConstruct (hd268) (hd269)); let hd271 : Expr := (.emptySequence 0); let hd272 : Expr := (.sequenceConstruct (hd270) (hd271)); let hd273 : Expr := (.emptySequence 0); let hd274 : Expr := (.sequenceConstruct (hd272) (hd273)); let hd275 : Expr := (.emptySequence 0); let hd276 : Expr := (.sequenceConstruct (hd274) (hd275)); let hd277 : Expr := (.emptySequence 0); let hd278 : Expr := (.sequenceConstruct (hd276) (hd277)); let hd279 : Expr := (.emptySequence 0); let hd280 : Expr := (.sequenceConstruct (hd278) (hd279)); let hd281 : Expr := (.emptySequence 0); let hd282 : Expr := (.sequenceConstruct (hd280) (hd281)); let hd283 : Expr := (.emptySequence 0); let hd284 : Expr := (.sequenceConstruct (hd282) (hd283)); let hd285 : Expr := (.emptySequence 0); let hd286 : Expr := (.sequenceConstruct (hd284) (hd285)); let hd287 : Expr := (.emptySequence 0); let hd288 : Expr := (.sequenceConstruct (hd286) (hd287)); let hd289 : Expr := (.emptySequence 0); let hd290 : Expr := (.sequenceConstruct (hd288) (hd289)); let hd291 : Expr := (.emptySequence 0); let hd292 : Expr := (.sequenceConstruct (hd290) (hd291)); let hd293 : Expr := (.emptySequence 0); let hd294 : Expr := (.sequenceConstruct (hd292) (hd293)); let hd295 : Expr := (.emptySequence 0); let hd296 : Expr := (.sequenceConstruct (hd294) (hd295)); let hd297 : Expr := (.emptySequence 0); let hd298 : Expr := (.sequenceConstruct (hd296) (hd297)); let hd299 : Expr := (.emptySequence 0); let hd300 : Expr := (.sequenceConstruct (hd298) (hd299)); let hd301 : Expr := (.emptySequence 0); let hd302 : Expr := (.sequenceConstruct (hd300) (hd301)); let hd303 : Expr := (.emptySequence 0); let hd304 : Expr := (.sequenceConstruct (hd302) (hd303)); let hd305 : Expr := (.emptySequence 0); let hd306 : Expr := (.sequenceConstruct (hd304) (hd305)); let hd307 : Expr := (.emptySequence 0); let hd308 : Expr := (.sequenceConstruct (hd306) (hd307)); let hd309 : Expr := (.emptySequence 0); let hd310 : Expr := (.sequenceConstruct (hd308) (hd309)); let hd311 : Expr := (.emptySequence 0); let hd312 : Expr := (.sequenceConstruct (hd310) (hd311)); let hd313 : Expr := (.emptySequence 0); let hd314 : Expr := (.sequenceConstruct (hd312) (hd313)); let hd315 : Expr := (.emptySequence 0); let hd316 : Expr := (.sequenceConstruct (hd314) (hd315)); let hd317 : Expr := (.emptySequence 0); let hd318 : Expr := (.sequenceConstruct (hd316) (hd317)); let hd319 : Expr := (.emptySequence 0); let hd320 : Expr := (.sequenceConstruct (hd318) (hd319)); let hd321 : Expr := (.emptySequence 0); let hd322 : Expr := (.sequenceConstruct (hd320) (hd321)); let hd323 : Expr := (.emptySequence 0); let hd324 : Expr := (.sequenceConstruct (hd322) (hd323)); let hd325 : Expr := (.emptySequence 0); let hd326 : Expr := (.sequenceConstruct (hd324) (hd325)); let hd327 : Expr := (.emptySequence 0); let hd328 : Expr := (.sequenceConstruct (hd326) (hd327)); let hd329 : Expr := (.emptySequence 0); let hd330 : Expr := (.sequenceConstruct (hd328) (hd329)); let hd331 : Expr := (.emptySequence 0); let hd332 : Expr := (.sequenceConstruct (hd330) (hd331)); let hd333 : Expr := (.emptySequence 0); let hd334 : Expr := (.sequenceConstruct (hd332) (hd333)); let hd335 : Expr := (.emptySequence 0); let hd336 : Expr := (.sequenceConstruct (hd334) (hd335)); let hd337 : Expr := (.emptySequence 0); let hd338 : Expr := (.sequenceConstruct (hd336) (hd337)); let hd339 : Expr := (.emptySequence 0); let hd340 : Expr := (.sequenceConstruct (hd338) (hd339)); let hd341 : Expr := (.emptySequence 0); let hd342 : Expr := (.sequenceConstruct (hd340) (hd341)); let hd343 : Expr := (.emptySequence 0); let hd344 : Expr := (.sequenceConstruct (hd342) (hd343)); let hd345 : Expr := (.emptySequence 0); let hd346 : Expr := (.sequenceConstruct (hd344) (hd345)); let hd347 : Expr := (.emptySequence 0); let hd348 : Expr := (.sequenceConstruct (hd346) (hd347)); let hd349 : Expr := (.emptySequence 0); let hd350 : Expr := (.sequenceConstruct (hd348) (hd349)); let hd351 : Expr := (.emptySequence 0); let hd352 : Expr := (.sequenceConstruct (hd350) (hd351)); let hd353 : Expr := (.emptySequence 0); let hd354 : Expr := (.sequenceConstruct (hd352) (hd353)); let hd355 : Expr := (.emptySequence 0); let hd356 : Expr := (.sequenceConstruct (hd354) (hd355)); let hd357 : Expr := (.emptySequence 0); let hd358 : Expr := (.sequenceConstruct (hd356) (hd357)); let hd359 : Expr := (.emptySequence 0); let hd360 : Expr := (.sequenceConstruct (hd358) (hd359)); let hd361 : Expr := (.emptySequence 0); let hd362 : Expr := (.sequenceConstruct (hd360) (hd361)); let hd363 : Expr := (.emptySequence 0); let hd364 : Expr := (.sequenceConstruct (hd362) (hd363)); let hd365 : Expr := (.emptySequence 0); let hd366 : Expr := (.sequenceConstruct (hd364) (hd365)); let hd367 : Expr := (.emptySequence 0); let hd368 : Expr := (.sequenceConstruct (hd366) (hd367)); let hd369 : Expr := (.emptySequence 0); let hd370 : Expr := (.sequenceConstruct (hd368) (hd369)); let hd371 : Expr := (.emptySequence 0); let hd372 : Expr := (.sequenceConstruct (hd370) (hd371)); let hd373 : Expr := (.emptySequence 0); let hd374 : Expr := (.sequenceConstruct (hd372) (hd373)); let hd375 : Expr := (.emptySequence 0); let hd376 : Expr := (.sequenceConstruct (hd374) (hd375)); let hd377 : Expr := (.emptySequence 0); let hd378 : Expr := (.sequenceConstruct (hd376) (hd377)); let hd379 : Expr := (.emptySequence 0); let hd380 : Expr := (.sequenceConstruct (hd378) (hd379)); let hd381 : Expr := (.emptySequence 0); let hd382 : Expr := (.sequenceConstruct (hd380) (hd381)); let hd383 : Expr := (.emptySequence 0); let hd384 : Expr := (.sequenceConstruct (hd382) (hd383)); let hd385 : Expr := (.emptySequence 0); let hd386 : Expr := (.sequenceConstruct (hd384) (hd385)); let hd387 : Expr := (.emptySequence 0); let hd388 : Expr := (.sequenceConstruct (hd386) (hd387)); let hd389 : Expr := (.emptySequence 0); let hd390 : Expr := (.sequenceConstruct (hd388) (hd389)); let hd391 : Expr := (.emptySequence 0); let hd392 : Expr := (.sequenceConstruct (hd390) (hd391)); let hd393 : Expr := (.emptySequence 0); let hd394 : Expr := (.sequenceConstruct (hd392) (hd393)); let hd395 : Expr := (.emptySequence 0); let hd396 : Expr := (.sequenceConstruct (hd394) (hd395)); let hd397 : Expr := (.emptySequence 0); let hd398 : Expr := (.sequenceConstruct (hd396) (hd397)); let hd399 : Expr := (.emptySequence 0); let hd400 : Expr := (.sequenceConstruct (hd398) (hd399)); let hd401 : Expr := (.emptySequence 0); let hd402 : Expr := (.sequenceConstruct (hd400) (hd401)); let hd403 : Expr := (.emptySequence 0); let hd404 : Expr := (.sequenceConstruct (hd402) (hd403)); let hd405 : Expr := (.emptySequence 0); let hd406 : Expr := (.sequenceConstruct (hd404) (hd405)); let hd407 : Expr := (.emptySequence 0); let hd408 : Expr := (.sequenceConstruct (hd406) (hd407)); let hd409 : Expr := (.emptySequence 0); let hd410 : Expr := (.sequenceConstruct (hd408) (hd409)); let hd411 : Expr := (.emptySequence 0); let hd412 : Expr := (.sequenceConstruct (hd410) (hd411)); let hd413 : Expr := (.emptySequence 0); let hd414 : Expr := (.sequenceConstruct (hd412) (hd413)); let hd415 : Expr := (.emptySequence 0); let hd416 : Expr := (.sequenceConstruct (hd414) (hd415)); let hd417 : Expr := (.emptySequence 0); let hd418 : Expr := (.sequenceConstruct (hd416) (hd417)); let hd419 : Expr := (.emptySequence 0); let hd420 : Expr := (.sequenceConstruct (hd418) (hd419)); let hd421 : Expr := (.emptySequence 0); let hd422 : Expr := (.sequenceConstruct (hd420) (hd421)); let hd423 : Expr := (.emptySequence 0); let hd424 : Expr := (.sequenceConstruct (hd422) (hd423)); let hd425 : Expr := (.emptySequence 0); let hd426 : Expr := (.sequenceConstruct (hd424) (hd425)); let hd427 : Expr := (.emptySequence 0); let hd428 : Expr := (.sequenceConstruct (hd426) (hd427)); let hd429 : Expr := (.emptySequence 0); let hd430 : Expr := (.sequenceConstruct (hd428) (hd429)); let hd431 : Expr := (.emptySequence 0); let hd432 : Expr := (.sequenceConstruct (hd430) (hd431)); let hd433 : Expr := (.emptySequence 0); let hd434 : Expr := (.sequenceConstruct (hd432) (hd433)); let hd435 : Expr := (.emptySequence 0); let hd436 : Expr := (.sequenceConstruct (hd434) (hd435)); let hd437 : Expr := (.emptySequence 0); let hd438 : Expr := (.sequenceConstruct (hd436) (hd437)); let hd439 : Expr := (.emptySequence 0); let hd440 : Expr := (.sequenceConstruct (hd438) (hd439)); let hd441 : Expr := (.emptySequence 0); let hd442 : Expr := (.sequenceConstruct (hd440) (hd441)); let hd443 : Expr := (.emptySequence 0); let hd444 : Expr := (.sequenceConstruct (hd442) (hd443)); let hd445 : Expr := (.emptySequence 0); let hd446 : Expr := (.sequenceConstruct (hd444) (hd445)); let hd447 : Expr := (.emptySequence 0); let hd448 : Expr := (.sequenceConstruct (hd446) (hd447)); let hd449 : Expr := (.emptySequence 0); let hd450 : Expr := (.sequenceConstruct (hd448) (hd449)); let hd451 : Expr := (.emptySequence 0); let hd452 : Expr := (.sequenceConstruct (hd450) (hd451)); let hd453 : Expr := (.emptySequence 0); let hd454 : Expr := (.sequenceConstruct (hd452) (hd453)); let hd455 : Expr := (.emptySequence 0); let hd456 : Expr := (.sequenceConstruct (hd454) (hd455)); let hd457 : Expr := (.emptySequence 0); let hd458 : Expr := (.sequenceConstruct (hd456) (hd457)); let hd459 : Expr := (.emptySequence 0); let hd460 : Expr := (.sequenceConstruct (hd458) (hd459)); let hd461 : Expr := (.emptySequence 0); let hd462 : Expr := (.sequenceConstruct (hd460) (hd461)); let hd463 : Expr := (.emptySequence 0); let hd464 : Expr := (.sequenceConstruct (hd462) (hd463)); let hd465 : Expr := (.emptySequence 0); let hd466 : Expr := (.sequenceConstruct (hd464) (hd465)); let hd467 : Expr := (.emptySequence 0); let hd468 : Expr := (.sequenceConstruct (hd466) (hd467)); let hd469 : Expr := (.emptySequence 0); let hd470 : Expr := (.sequenceConstruct (hd468) (hd469)); let hd471 : Expr := (.emptySequence 0); let hd472 : Expr := (.sequenceConstruct (hd470) (hd471)); let hd473 : Expr := (.emptySequence 0); let hd474 : Expr := (.sequenceConstruct (hd472) (hd473)); let hd475 : Expr := (.emptySequence 0); let hd476 : Expr := (.sequenceConstruct (hd474) (hd475)); let hd477 : Expr := (.emptySequence 0); let hd478 : Expr := (.sequenceConstruct (hd476) (hd477)); let hd479 : Expr := (.emptySequence 0); let hd480 : Expr := (.sequenceConstruct (hd478) (hd479)); let hd481 : Expr := (.emptySequence 0); let hd482 : Expr := (.sequenceConstruct (hd480) (hd481)); let hd483 : Expr := (.emptySequence 0); let hd484 : Expr := (.sequenceConstruct (hd482) (hd483)); let hd485 : Expr := (.emptySequence 0); let hd486 : Expr := (.sequenceConstruct (hd484) (hd485)); let hd487 : Expr := (.emptySequence 0); let hd488 : Expr := (.sequenceConstruct (hd486) (hd487)); let hd489 : Expr := (.emptySequence 0); let hd490 : Expr := (.sequenceConstruct (hd488) (hd489)); let hd491 : Expr := (.emptySequence 0); let hd492 : Expr := (.sequenceConstruct (hd490) (hd491)); let hd493 : Expr := (.emptySequence 0); let hd494 : Expr := (.sequenceConstruct (hd492) (hd493)); let hd495 : Expr := (.emptySequence 0); let hd496 : Expr := (.sequenceConstruct (hd494) (hd495)); let hd497 : Expr := (.emptySequence 0); let hd498 : Expr := (.sequenceConstruct (hd496) (hd497)); let hd499 : Expr := (.emptySequence 0); let hd500 : Expr := (.sequenceConstruct (hd498) (hd499)); let hd501 : Expr := (.emptySequence 0); let hd502 : Expr := (.sequenceConstruct (hd500) (hd501)); let hd503 : Expr := (.emptySequence 0); let hd504 : Expr := (.sequenceConstruct (hd502) (hd503)); let hd505 : Expr := (.emptySequence 0); let hd506 : Expr := (.sequenceConstruct (hd504) (hd505)); let hd507 : Expr := (.emptySequence 0); let hd508 : Expr := (.sequenceConstruct (hd506) (hd507)); let hd509 : Expr := (.emptySequence 0); let hd510 : Expr := (.sequenceConstruct (hd508) (hd509)); let hd511 : Expr := (.emptySequence 0); let hd512 : Expr := (.sequenceConstruct (hd510) (hd511)); let hd513 : Expr := (.emptySequence 0); let hd514 : Expr := (.sequenceConstruct (hd512) (hd513)); let hd515 : Expr := (.emptySequence 0); let hd516 : Expr := (.sequenceConstruct (hd514) (hd515)); let hd517 : Expr := (.emptySequence 0); let hd518 : Expr := (.sequenceConstruct (hd516) (hd517)); let hd519 : Expr := (.emptySequence 0); let hd520 : Expr := (.sequenceConstruct (hd518) (hd519)); let hd521 : Expr := (.emptySequence 0); let hd522 : Expr := (.sequenceConstruct (hd520) (hd521)); let hd523 : Expr := (.emptySequence 0); let hd524 : Expr := (.sequenceConstruct (hd522) (hd523)); let hd525 : Expr := (.emptySequence 0); let hd526 : Expr := (.sequenceConstruct (hd524) (hd525)); let hd527 : Expr := (.emptySequence 0); let hd528 : Expr := (.sequenceConstruct (hd526) (hd527)); let hd529 : Expr := (.emptySequence 0); let hd530 : Expr := (.sequenceConstruct (hd528) (hd529)); let hd531 : Expr := (.emptySequence 0); let hd532 : Expr := (.sequenceConstruct (hd530) (hd531)); let hd533 : Expr := (.emptySequence 0); let hd534 : Expr := (.sequenceConstruct (hd532) (hd533)); let hd535 : Expr := (.emptySequence 0); let hd536 : Expr := (.sequenceConstruct (hd534) (hd535)); let hd537 : Expr := (.emptySequence 0); let hd538 : Expr := (.sequenceConstruct (hd536) (hd537)); let hd539 : Expr := (.emptySequence 0); let hd540 : Expr := (.sequenceConstruct (hd538) (hd539)); let hd541 : Expr := (.emptySequence 0); let hd542 : Expr := (.sequenceConstruct (hd540) (hd541)); let hd543 : Expr := (.emptySequence 0); let hd544 : Expr := (.sequenceConstruct (hd542) (hd543)); let hd545 : Expr := (.emptySequence 0); let hd546 : Expr := (.sequenceConstruct (hd544) (hd545)); let hd547 : Expr := (.emptySequence 0); let hd548 : Expr := (.sequenceConstruct (hd546) (hd547)); let hd549 : Expr := (.emptySequence 0); let hd550 : Expr := (.sequenceConstruct (hd548) (hd549)); let hd551 : Expr := (.emptySequence 0); let hd552 : Expr := (.sequenceConstruct (hd550) (hd551)); let hd553 : Expr := (.emptySequence 0); let hd554 : Expr := (.sequenceConstruct (hd552) (hd553)); let hd555 : Expr := (.emptySequence 0); let hd556 : Expr := (.sequenceConstruct (hd554) (hd555)); let hd557 : Expr := (.emptySequence 0); let hd558 : Expr := (.sequenceConstruct (hd556) (hd557)); let hd559 : Expr := (.emptySequence 0); let hd560 : Expr := (.sequenceConstruct (hd558) (hd559)); let hd561 : Expr := (.emptySequence 0); let hd562 : Expr := (.sequenceConstruct (hd560) (hd561)); let hd563 : Expr := (.emptySequence 0); let hd564 : Expr := (.sequenceConstruct (hd562) (hd563)); let hd565 : Expr := (.emptySequence 0); let hd566 : Expr := (.sequenceConstruct (hd564) (hd565)); let hd567 : Expr := (.emptySequence 0); let hd568 : Expr := (.sequenceConstruct (hd566) (hd567)); let hd569 : Expr := (.emptySequence 0); let hd570 : Expr := (.sequenceConstruct (hd568) (hd569)); let hd571 : Expr := (.emptySequence 0); let hd572 : Expr := (.sequenceConstruct (hd570) (hd571)); let hd573 : Expr := (.emptySequence 0); let hd574 : Expr := (.sequenceConstruct (hd572) (hd573)); let hd575 : Expr := (.emptySequence 0); let hd576 : Expr := (.sequenceConstruct (hd574) (hd575)); let hd577 : Expr := (.emptySequence 0); let hd578 : Expr := (.sequenceConstruct (hd576) (hd577)); let hd579 : Expr := (.emptySequence 0); let hd580 : Expr := (.sequenceConstruct (hd578) (hd579)); let hd581 : Expr := (.emptySequence 0); let hd582 : Expr := (.sequenceConstruct (hd580) (hd581)); let hd583 : Expr := (.emptySequence 0); let hd584 : Expr := (.sequenceConstruct (hd582) (hd583)); let hd585 : Expr := (.emptySequence 0); let hd586 : Expr := (.sequenceConstruct (hd584) (hd585)); let hd587 : Expr := (.emptySequence 0); let hd588 : Expr := (.sequenceConstruct (hd586) (hd587)); let hd589 : Expr := (.emptySequence 0); let hd590 : Expr := (.sequenceConstruct (hd588) (hd589)); let hd591 : Expr := (.emptySequence 0); let hd592 : Expr := (.sequenceConstruct (hd590) (hd591)); let hd593 : Expr := (.emptySequence 0); let hd594 : Expr := (.sequenceConstruct (hd592) (hd593)); let hd595 : Expr := (.emptySequence 0); let hd596 : Expr := (.sequenceConstruct (hd594) (hd595)); let hd597 : Expr := (.emptySequence 0); let hd598 : Expr := (.sequenceConstruct (hd596) (hd597)); let hd599 : Expr := (.emptySequence 0); let hd600 : Expr := (.sequenceConstruct (hd598) (hd599)); let hd601 : Expr := (.emptySequence 0); let hd602 : Expr := (.sequenceConstruct (hd600) (hd601)); let hd603 : Expr := (.emptySequence 0); let hd604 : Expr := (.sequenceConstruct (hd602) (hd603)); let hd605 : Algorithm := (alg [] [] [] [hd604]); let hd606 : ScopeCtx := (ScopeCtx.mk none [] [] [privateProp "P" hd605] [] [] none none); let hd607 : Algorithm := (Algorithm.withParent (some hd606) (alg [] [] [publicProp "Run" hd1] [])); let hd608 : Expr := (.algorithmExpr hd607); let hd609 : Expr := .resolve "Run"; let hd610 : Algorithm := (alg [] [hd608] [] [hd609]); let hd611 : Expr := (.algorithmExpr hd610); hd611)
#guard obs hp_10i == "ok raw=1 n=1"
#guard cacheEntries hp_10i "P" == 1
#guard cacheEntries hp_10i "Run" == 1
#guard cacheTotal hp_10i == 2

-- HP-11a: a host-declared static alias calls its target
def hp_11a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "A" (.alias none [] [] (.resolve "Inc"))] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "A") [.num 5])])] [])))] [] [.resolve "Run"]))
#guard obs hp_11a == "ok raw=6 n=1"
#guard cacheEntries hp_11a "Run" == 1
#guard cacheTotal hp_11a == 1

-- HP-11b: a host alias chain B -> A -> Inc
def hp_11b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "A" (.alias none [] [] (.resolve "Inc")), privateProp "B" (.alias none [] [] (.resolve "A"))] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "B") [.num 5])])] [])))] [] [.resolve "Run"]))
#guard obs hp_11b == "ok raw=6 n=1"
#guard cacheEntries hp_11b "Run" == 1
#guard cacheTotal hp_11b == 1

-- HP-11c: a host alias resolves its target in the HOST scope, never the block's shadowing Inc
def hp_11c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "A" (.alias none [] [] (.resolve "Inc"))] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.call (.resolve "Inc") [.num 5]))]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [])))] [] [.resolve "Run"]))
#guard obs hp_11c == "ok raw=111 n=1"
#guard cacheEntries hp_11c "Run" == 1
#guard cacheTotal hp_11c == 1

-- HP-11d: a block alias over a host-declared target
def hp_11d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "A2") [.num 5])]), privateProp "A2" (.alias none [] [] (.resolve "Inc"))] [])))] [] [.resolve "Run"]))
#guard obs hp_11d == "ok raw=6 n=1"
#guard cacheEntries hp_11d "Run" == 1
#guard cacheTotal hp_11d == 1

-- HP-11e: an alias in a grandparent level through a member path
def hp_11e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicProp "Twice" (alg ["x"] [] [] [(.binary .mul (.param "x") (.num 2))])] [])] [] [] none none)) [] [] [privateProp "T" (.alias none [] [] ((.dotCall (.resolve "M") "Twice" none)))] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "T") [.num 21])])] [])))] [] [.resolve "Run"]))
#guard obs hp_11e == "ok raw=42 n=1"
#guard cacheEntries hp_11e "Run" == 1
#guard cacheTotal hp_11e == 1

-- HP-12a: D4 terminal fallback: a zero-parameter target keeps ordinary-property semantics (A, A(), A, A())
def hp_12a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "F" (alg [] [] [] [.num 7]), privateProp "Capture" (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]), privateProp "R" (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]), privateProp "A" (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none)))] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "A", (.call (.resolve "A") []), .resolve "A", (.call (.resolve "A") [])])] [])))] [] [.resolve "Run"]))
#guard obs hp_12a == "ok raw=S[7, 7, 7, 7] n=1"
#guard cacheEntries hp_12a "A" == 1
#guard cacheEntries hp_12a "F" == 1
#guard cacheEntries hp_12a "R" == 1
#guard cacheEntries hp_12a "Run" == 1
#guard cacheTotal hp_12a == 4

-- HP-12b: D3 parameterized forwarding: A(args) is a fresh call of the projected F
def hp_12b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "F" (alg ["v"] [] [] [(.binary .add (.param "v") (.num 1))]), privateProp "Capture" (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]), privateProp "R" (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [.num 1])])]), privateProp "A" (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none)))] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "A") [.num 5]), (.call (.resolve "A") [.num 10])])] [])))] [] [.resolve "Run"]))
#guard obs hp_12b == "ok raw=S[6, 11] n=1"
#guard cacheEntries hp_12b "A" == 0
#guard cacheEntries hp_12b "R" == 1
#guard cacheEntries hp_12b "Run" == 1
#guard cacheTotal hp_12b == 2

-- HP-12c: one host object opened twice shares the alias's declaring namespace (HOST-ALIAS-R14)
def hp_12c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 2) }, { (privateProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 3) }] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [.resolve "A"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 2) }, { (privateProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 3) }] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "A") [])])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_12c == "ok raw=S[7, 7] n=2"
#guard cacheEntries hp_12c "A" == 1
#guard cacheEntries hp_12c "F" == 1
#guard cacheEntries hp_12c "R" == 1
#guard cacheEntries hp_12c "RunA" == 1
#guard cacheEntries hp_12c "RunB" == 1
#guard cacheTotal hp_12c == 5

-- HP-12d: record-equal host objects sharing the member list keep one namespace each (HOST-ALIAS-R14)
def hp_12d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 2) }, { (privateProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 3) }] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [.resolve "A"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 4) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 5) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 6) }, { (privateProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 7) }] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "A") [])])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_12d == "ok raw=S[7, 7] n=2"
#guard cacheEntries hp_12d "A" == 2
#guard cacheEntries hp_12d "F" == 2
#guard cacheEntries hp_12d "R" == 2
#guard cacheEntries hp_12d "RunA" == 1
#guard cacheEntries hp_12d "RunB" == 1
#guard cacheTotal hp_12d == 8

-- HP-13a: a host property whose CONDITIONAL value carries its own parent: lookup wiring replaces it
def hp_13a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "K" (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none none)) (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.resolve "V"])⟩, ⟨.bind "n", (alg [] [] [] [(.binary .add (.param "n") (.resolve "V"))])⟩]))] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "K") [.num 0]), (.call (.resolve "K") [.num 5])])] [])))] [] [.resolve "Run"]))
#guard obs hp_13a == "ok raw=S[1, 6] n=1"
#guard cacheEntries hp_13a "Run" == 1
#guard cacheEntries hp_13a "V" == 1
#guard cacheTotal hp_13a == 2

-- HP-13b: a host property whose ALIAS value carries its own parent: lookup wiring replaces it
def hp_13b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "A" (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none none)) (.alias none [] [] (.resolve "Inc")))] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "A") [.num 1])])] [])))] [] [.resolve "Run"]))
#guard obs hp_13b == "ok raw=2 n=1"
#guard cacheEntries hp_13b "Run" == 1
#guard cacheTotal hp_13b == 1

-- HP-13c: a pre-wired CONDITIONAL as an open target is refused when a lookup reaches it
def hp_13c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none none)) (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩])))] [] [.resolve "Z"]))
#guard obs hp_13c == "err illegalInOpen"

-- HP-13d: a pre-wired ALIAS as an open target is refused when a lookup reaches it
def hp_13d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none none)) (.alias none [] [] (.resolve "Inc"))))] [] [.resolve "Z"]))
#guard obs hp_13d == "err illegalInOpen"

-- HP-13e: a pre-wired PROGRAM ROOT is wired under the prelude: its host parent is replaced
def hp_13e : Expr :=
  (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none none)) (alg [] [] [] [.resolve "V"])))
#guard obs hp_13e == "err unknownName"
#guard errorObs hp_13e == .matched (some { kind := "unknownName", names := ["V"], counts := [] })

-- HP-13f: a pre-wired inline block in VALUE position is wired to its caller
def hp_13f : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none none)) (alg [] [] [] [.resolve "V"])))])] [])))] [] [.resolve "Run"]))
#guard obs hp_13f == "ok raw=1 n=1"
#guard cacheEntries hp_13f "Run" == 1
#guard cacheEntries hp_13f "V" == 1
#guard cacheTotal hp_13f == 2

-- HP-13g: a pre-wired inline CALLEE is wired to its caller
def hp_13g : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none none)) (alg ["y"] [] [] [(.binary .add (.param "y") (.resolve "V"))]))) [.num 3])])] [])))] [] [.resolve "Run"]))
#guard obs hp_13g == "ok raw=4 n=1"
#guard cacheEntries hp_13g "Run" == 1
#guard cacheEntries hp_13g "V" == 1
#guard cacheTotal hp_13g == 2

-- HP-13h: a pre-wired inline CONDITIONAL callee is wired to its caller
def hp_13h : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none none)) (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.resolve "V"])⟩, ⟨.bind "n", (alg [] [] [] [(.binary .add (.param "n") (.resolve "V"))])⟩]))) [.num 0])])] [])))] [] [.resolve "Run"]))
#guard obs hp_13h == "ok raw=1 n=1"
#guard cacheEntries hp_13h "Run" == 1
#guard cacheEntries hp_13h "V" == 1
#guard cacheTotal hp_13h == 2

-- HP-13i: a pre-wired inline ALIAS callee resolves its target from the caller
def hp_13i : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none none)) (.alias none [] [] (.resolve "Inc")))) [.num 2])])] [])))] [] [.resolve "Run"]))
#guard obs hp_13i == "ok raw=3 n=1"
#guard cacheEntries hp_13i "Run" == 1
#guard cacheTotal hp_13i == 1

-- HP-13j: a pre-wired property value of the BLOCK itself is replaced by the block's wiring
def hp_13j : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "U"]), privateProp "U" (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none none)) (alg [] [] [] [.resolve "V"]))] [])))] [] [.resolve "Run"]))
#guard obs hp_13j == "ok raw=1 n=1"
#guard cacheEntries hp_13j "Run" == 1
#guard cacheEntries hp_13j "U" == 1
#guard cacheEntries hp_13j "V" == 1
#guard cacheTotal hp_13j == 3

-- HP-13k: a structural receiver block with a pre-wired parent is wired to its caller
def hp_13k : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [(.dotCall (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none none)) (alg [] [] [publicProp "W" (alg [] [] [] [.resolve "V"])] []))) "W" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_13k == "ok raw=1 n=1"
#guard cacheEntries hp_13k "Run" == 1
#guard cacheEntries hp_13k "V" == 1
#guard cacheEntries hp_13k "W" == 1
#guard cacheTotal hp_13k == 3

-- HP-13l: an explicitly wired module open preserves its host root instead of taking the caller's V
def hp_13l : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.module 0)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"])] []))))] [privateProp "V" (alg [] [] [] [.num 1])] [.resolve "Run"]))
#guard obs hp_13l == "ok raw=99 n=1"
#guard cacheEntries hp_13l "Run" == 1
#guard cacheEntries hp_13l "V" == 1
#guard cacheTotal hp_13l == 2

-- HP-13m: a module property roots at the supplied host chain, which has no implicit prelude count
def hp_13m : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (Algorithm.withDeclarationId (some (.module 0)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "count" (alg ["x"] [] [] [.num 99])] [] [] none none)) (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [])])])))] [] [] none none)) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "M"])] [])))] [] [.resolve "Run"]))
#guard obs hp_13m == "err unknownName"
#guard errorObs hp_13m == .matched (some { kind := "unknownName", names := ["count"], counts := [] })

-- HP-14a: control: one declaration opened twice under ONE empty host level object is one provider
def hp_14a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none none)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] [])))), (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none none)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [] [.resolve "F"]))
#guard obs hp_14a == "ok raw=7 n=1"
#guard cacheEntries hp_14a "F" == 1
#guard cacheTotal hp_14a == 1

-- HP-14b [KNOWN DIVERGENCE - excluded from the comparable partition]: one declaration opened twice under two DISTINCT empty host level objects
-- Reason: HOST-LEAN-O6 O6-18 (Q-19 open-provider identity over EMPTY host levels): C# compares host levels by object reference, Lean by content, and an empty level has no PropDef to carry a per-object identity; a faithful encoding needs a Lean host-level token (deferred design E, owner decision OD-1).
-- C# observes err ambiguousOpen (pinned by HostParentDifferentialTests).
def hp_14b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none none)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] [])))), (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none none)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [] [.resolve "F"]))
#guard obs hp_14b == "ok raw=7 n=1"
#guard obs hp_14b != "err ambiguousOpen"

-- HP-14c: control: fresh host levels with their own nested declarations keep (S, P.Q) per level
def hp_14c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "S" (alg [] [] [] [.param "x"]), privateProp "P" (alg [] [] [publicProp "Q" (alg [] [] [] [.resolve "S"])] [])] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "S", (.dotCall (.resolve "P") "Q" none)])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "S" (alg [] [] [] [.param "x"]), privateProp "P" (alg [] [] [publicProp "Q" (alg [] [] [] [.resolve "S"])] [])] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "S", (.dotCall (.resolve "P") "Q" none)])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_14c == "ok raw=S[S[1, 1], S[2, 2]] n=2"
#guard cacheEntries hp_14c "Q" == 2
#guard cacheEntries hp_14c "RunA" == 1
#guard cacheEntries hp_14c "RunB" == 1
#guard cacheEntries hp_14c "S" == 2
#guard cacheTotal hp_14c == 6

-- HP-14d [KNOWN DIVERGENCE - excluded from the comparable partition]: an owned Q nested under two record-equal host levels that share ONE property list
-- Reason: HOST-LEAN-O6 O6-11x (C# pass-through policy): C# keys the host DECLARING level by reference but a host level PASSED THROUGH by structure, so the second level's P.Q reuses the first level's entry; the per-object encoding keeps Lean's two levels distinct. Which policy is the contract awaits owner decision OD-1.
-- C# observes ok raw=S[S[1, 1], S[2, 1]] n=2 (pinned by HostParentDifferentialTests).
def hp_14d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "S" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 0) }, { (privateProp "P" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [{ (publicProp "Q" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [.resolve "S"]))) with identity := some (.shared 2) }] []))) with identity := some (.shared 1) }] [] [] none none)) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "S", (.dotCall (.resolve "P") "Q" none)])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "S" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.param "x"]))) with identity := some (.shared 3) }, { (privateProp "P" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [{ (publicProp "Q" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [.resolve "S"]))) with identity := some (.shared 2) }] []))) with identity := some (.shared 4) }] [] [] none none)) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "S", (.dotCall (.resolve "P") "Q" none)])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_14d == "ok raw=S[S[1, 1], S[2, 2]] n=2"
#guard obs hp_14d != "ok raw=S[S[1, 1], S[2, 1]] n=2"

-- HP-15a: a deconstruction helper copied over another argument, copy read first (H04)
def hp_15a : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "a" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])])), privateProp "b" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])]), privateProp "q" (alg [] [] [] [(.capture [.num 7, .num 8])]), privateProp "c" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "q"])]))] [.resolve "c", .resolve "a"]))
#guard obs hp_15a == "ok raw=S[7, 1] n=2"
#guard cacheEntries hp_15a "$deconstruct$0" == 1
#guard cacheEntries hp_15a "a" == 1
#guard cacheEntries hp_15a "c" == 1
#guard cacheEntries hp_15a "q" == 1
#guard cacheTotal hp_15a == 4

-- HP-15b: a deconstruction helper copied over another argument, original read first (H05)
def hp_15b : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "a" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])])), privateProp "b" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])]), privateProp "q" (alg [] [] [] [(.capture [.num 7, .num 8])]), privateProp "c" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "q"])]))] [.resolve "a", .resolve "c"]))
#guard obs hp_15b == "ok raw=S[1, 7] n=2"
#guard cacheEntries hp_15b "$deconstruct$0" == 1
#guard cacheEntries hp_15b "a" == 1
#guard cacheEntries hp_15b "c" == 1
#guard cacheEntries hp_15b "q" == 1
#guard cacheTotal hp_15b == 4

-- HP-15c: a deconstruction helper copy with a changed unpacking pattern, copy read first (V05)
def hp_15c : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.listLiteral [.num 1]), .num 2])]), privateProp "a" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])])), privateProp "b" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])]), privateProp "c" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.listValue [.capture { name := "a" }], .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])]))] [.resolve "c", .resolve "a"]))
#guard obs hp_15c == "ok raw=S[1, L[1]] n=2"
#guard cacheEntries hp_15c "$deconstruct$0" == 1
#guard cacheEntries hp_15c "a" == 1
#guard cacheEntries hp_15c "c" == 1
#guard cacheTotal hp_15c == 3

-- HP-15d: a deconstruction helper copy with a changed unpacking pattern, original read first (V06)
def hp_15d : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.listLiteral [.num 1]), .num 2])]), privateProp "a" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])])), privateProp "b" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])]), privateProp "c" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.listValue [.capture { name := "a" }], .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])]))] [.resolve "a", .resolve "c"]))
#guard obs hp_15d == "ok raw=S[L[1], 1] n=2"
#guard cacheEntries hp_15d "$deconstruct$0" == 1
#guard cacheEntries hp_15d "a" == 1
#guard cacheEntries hp_15d "c" == 1
#guard cacheTotal hp_15d == 3

-- HP-15e: a deconstruction target body copied with a local shadowing source (V07)
def hp_15e : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.capture [.num 1, .num 2])])), privateProp "a" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])])), privateProp "b" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])]), privateProp "c" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [privateProp "$deconstruct$0" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7, .num 8]))] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])]))] [.resolve "a", .resolve "c"]))
#guard obs hp_15e == "ok raw=S[1, 7] n=2"
#guard cacheEntries hp_15e "$deconstruct$0" == 2
#guard cacheEntries hp_15e "a" == 1
#guard cacheEntries hp_15e "c" == 1
#guard cacheTotal hp_15e == 4

/--
Machine-checked comparable partition count: the id list is built by the loop that emits the guards
above, while the expected total is computed independently from the corpus partition.
-/
def comparableCaseIds : List String := [
  "HP-01a",
  "HP-01b",
  "HP-01c",
  "HP-01d",
  "HP-02a",
  "HP-02b",
  "HP-02c",
  "HP-02d",
  "HP-02e",
  "HP-02f",
  "HP-03a",
  "HP-03b",
  "HP-03c",
  "HP-03d",
  "HP-03e",
  "HP-04a",
  "HP-04b",
  "HP-04c",
  "HP-05a",
  "HP-05b",
  "HP-05c",
  "HP-05d",
  "HP-05e",
  "HP-05f",
  "HP-05g",
  "HP-05h",
  "HP-05i",
  "HP-06a",
  "HP-06b",
  "HP-06c",
  "HP-06d",
  "HP-07a",
  "HP-07b",
  "HP-08a",
  "HP-08b",
  "HP-08c",
  "HP-08d",
  "HP-08e",
  "HP-08f",
  "HP-08g",
  "HP-08h",
  "HP-08i",
  "HP-08j",
  "HP-08k",
  "HP-09a",
  "HP-09b",
  "HP-09c",
  "HP-09d",
  "HP-10a",
  "HP-10b",
  "HP-10c",
  "HP-10d",
  "HP-10e",
  "HP-10f",
  "HP-10g",
  "HP-10h",
  "HP-10i",
  "HP-11a",
  "HP-11b",
  "HP-11c",
  "HP-11d",
  "HP-11e",
  "HP-12a",
  "HP-12b",
  "HP-12c",
  "HP-12d",
  "HP-13a",
  "HP-13b",
  "HP-13c",
  "HP-13d",
  "HP-13e",
  "HP-13f",
  "HP-13g",
  "HP-13h",
  "HP-13i",
  "HP-13j",
  "HP-13k",
  "HP-13l",
  "HP-13m",
  "HP-14a",
  "HP-14c",
  "HP-15a",
  "HP-15b",
  "HP-15c",
  "HP-15d",
  "HP-15e"
]
#guard comparableCaseIds.length == 86

/--
Machine-checked known-divergence partition count (HOST-LEAN-O6 shapes pinned on both sides).
-/
def divergentCaseIds : List String := [
  "HP-14b",
  "HP-14d"
]
#guard divergentCaseIds.length == 2

-- 86 comparable cases, 2 known divergences.
end HostParentDifferential
