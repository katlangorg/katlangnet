import KatLang
import CoreTests.StructuralIdentity

/-!
GENERATED FILE - DO NOT EDIT BY HAND.

HOST-DIFF-1: Lean/C# differential corpus of HOST-BUILT ASTs with pre-wired `ScopeCtx`
parent chains (dotnet/tests/KatLang.Tests/HostParentDifferential/HostParentDifferentialCorpus.cs).
Each program below is `LeanAstEncoder`'s encoding of the SAME constructed C# AST the C#
evaluator ran on every route (plain, counted, generic, optimized, suspending async); each
`#guard` pins the C# neutral observation and the C# published zero-argument cache entries
(per property name, and in total), on success and on failure alike (KL-06). A successful
case's `structural` guard also pins the C# `kl-struct-v1` identity of its value against the
Lean exporter's text (KL-07 pilot; `CoreTests/StructuralIdentity.lean`). A failing guard is
a Lean/C# divergence on that case.

Partition (machine-checked by the `*CaseIds.length` guards below):
- corpus cases: 203
- comparable cases: 203
- known HOST-LEAN-O6 divergences, pinned on both sides and excluded from comparison: 0

Regenerate from the repo root with:
  $env:KATLANG_REGENERATE_HOST_PARENT_DIFFERENTIAL = "1"
  dotnet test .\dotnet\KatLang.slnx --filter HostParentDifferential
-/

namespace HostParentDifferential
open KatLang

-- Compact graph terms contain sequential lets; this bounds elaboration of the
-- accepted join-spine fixtures without changing any evaluator limit or observation.
set_option maxRecDepth 4096

/-- Neutral raw-structure encoding shared with the C# harness:
    atom -> `1`, string -> `'x'`, Boolean -> `true` / `false`,
    sequence -> `S[a, b]`, empty -> `S[]`, exact list -> `L[a, b]`,
    call reference and argument view -> `CallReference` (never a run result: the run boundary refuses both),
    deferred list item and pending list -> `Deferred` (never a run result: a run value is materialized). -/
partial def neutral : Result -> String
  | .atom n => toString n
  | .str s => "'" ++ s ++ "'"
  | .bool b => Result.boolText b
  | .sequenceValue rs => "S[" ++ String.intercalate ", " (rs.map neutral) ++ "]"
  | .listValue rs => "L[" ++ String.intercalate ", " (rs.map neutral) ++ "]"
  | .callRef _ => "CallReference"
  | .argView _ => "CallReference"
  | .deferred _ => "Deferred"
  | .pendingList _ => "Deferred"

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
  -- A run value is materialized before it leaves the run (lazy collections, issue #204),
  -- exactly as `runResultM` materializes it; the root emitted count is kept.
  let value <- materializeVia demandNeedRecursive counted.fst
  let _ <- exportRunValue value
  pure (value, counted.snd)

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

/-- KL-06: the comparable publication set of ONE finished run, read from its outcome and its
    final state. `EvalM` keeps the completed state on failure (`runResultWithState` drops it
    there), so a failed run still shows every entry a successful owner published before the
    failure, while a failed owner published none. An incomplete outcome (R7; no public run
    returns it) or an owner still active when the run ended has NO comparable publication set
    (C#: the harness requires every owner released): it observes `none`, which no guard
    expects, and never an empty cache (`some []`). -/
def publicationsOf (outcome : Except Error Result) (state : EvalState) : Option ZeroArgPropertyCache :=
  if outcome.isIncomplete || !state.activeZeroArgProperties.isEmpty then none
  else some state.zeroArgPropertyCache

/-- The zero-argument property cache entries ONE plain run published, on success AND on
    failure. Every `#guard` is its own evaluation, so each cache guard below runs its
    program once. -/
def publications (e : Expr) : Option ZeroArgPropertyCache :=
  match (runResultM e).runState EvalState.empty with
  | (outcome, state) => publicationsOf outcome state

/-- Published zero-argument property cache entries of one run named `name` (C#: the entries the
    run-scoped publication law PUBLISHED for bindings of that name, kept beside a failure). -/
def cacheEntries (e : Expr) (name : String) : Option Nat :=
  (publications e).map fun cache => (cache.filter (·.1.propertyName == name)).length

/-- Every published zero-argument property cache entry of one run. -/
def cacheTotal (e : Expr) : Option Nat :=
  (publications e).map List.length

-- KL-06 observation states (hand-written states, not evaluator programs): NO OBSERVATION
-- (`none`: an incomplete outcome, or an owner still active), a completed run with an EMPTY
-- cache (`some 0`) and a completed run with entries are three different observations, and
-- a failed run keeps the entries of its state exactly as a successful one does.
def observedEntryProbe : ZeroArgPropertyCacheKey :=
  { accessKind := .lexical, owner := "", hostOwners := [], componentOwners := [], propertyName := "P",
    propertyAlgorithm := "", valEnv := none, bindingContext := none }
#guard (publicationsOf (.error .fuelExhausted) EvalState.empty).isNone
#guard (publicationsOf (.ok (.atom 0)) { EvalState.empty with activeZeroArgProperties := [observedEntryProbe] }).isNone
#guard (publicationsOf (.ok (.atom 0)) EvalState.empty).map List.length == some 0
#guard (publicationsOf (.error .divByZero) EvalState.empty).map List.length == some 0
#guard (publicationsOf (.error .divByZero)
    { EvalState.empty with zeroArgPropertyCache := [(observedEntryProbe, (.atom 7, 1))] }).map List.length == some 1
/-- KL-07 pilot: the `kl-struct-v1` identity (`StructuralIdentity.encode`,
    `CoreTests/StructuralIdentity.lean`) of the value ONE plain run returns; `none` on
    failure. Each successful case's guard compares it with the C# encoder's text of the C#
    value (`MetamorphicStructuralIdentity.Encode`): unlike the neutral text, which writes
    strings between unescaped quotes, it never writes two different values alike. Every
    `#guard` is its own evaluation, so each structural guard runs its program once more. -/
def structural (e : Expr) : Option String :=
  match runResult e with
  | .ok value => StructuralIdentity.encode value
  | .error _ => none

-- Exporter cross-check (KL-07; StructuralIdentityExamples): every Lean-comparable example
-- value was built by C# and is written here as a Lean literal; the expected text is the C#
-- encoder's text of the C# value.
-- zero
#guard StructuralIdentity.encode (.atom 0) == some "kl-struct-v1:1:n1:0"
-- negative-zero
#guard StructuralIdentity.encode (.atom 0) == some "kl-struct-v1:1:n1:0"
-- seven
#guard StructuralIdentity.encode (.atom 7) == some "kl-struct-v1:1:n3:7e0"
-- integer-1200
#guard StructuralIdentity.encode (.atom 1200) == some "kl-struct-v1:1:n4:12e2"
-- integer-1200.00
#guard StructuralIdentity.encode (.atom 1200) == some "kl-struct-v1:1:n4:12e2"
-- negative-5
#guard StructuralIdentity.encode (.atom (-5)) == some "kl-struct-v1:1:n4:-5e0"
-- negative-120
#guard StructuralIdentity.encode (.atom (-120)) == some "kl-struct-v1:1:n5:-12e1"
-- collision-two-strings
#guard StructuralIdentity.encode (.listValue [(.str "a"), (.str "b")]) == some "kl-struct-v1:3:t1:at1:bl2:0,1,;"
-- collision-one-string
#guard StructuralIdentity.encode (.listValue [(.str "a', 'b")]) == some "kl-struct-v1:2:t6:a', 'bl1:0,;"
-- empty-sequence
#guard StructuralIdentity.encode (.sequenceValue []) == some "kl-struct-v1:1:s0:;"
-- empty-list
#guard StructuralIdentity.encode (.listValue []) == some "kl-struct-v1:1:l0:;"
-- booleans
#guard StructuralIdentity.encode (.listValue [(.bool true), (.bool false)]) == some "kl-struct-v1:3:b1b0l2:0,1,;"
-- kinds
#guard StructuralIdentity.encode (.listValue [(.atom 1), (.str "1"), (.bool true)]) == some "kl-struct-v1:4:n3:1e0t1:1b1l3:0,1,2,;"
-- backslash
#guard StructuralIdentity.encode (.str "a\\b") == some "kl-struct-v1:1:t3:a\\\\b"
-- printable
#guard StructuralIdentity.encode (.str "\"q\" ~") == some "kl-struct-v1:1:t5:\"q\" ~"
-- controls
#guard StructuralIdentity.encode (.str "a\nb\t") == some "kl-struct-v1:1:t4:a\\u000Ab\\u0009"
-- non-bmp
#guard StructuralIdentity.encode (.str "😀") == some "kl-struct-v1:1:t2:\\uD83D\\uDE00"
-- bmp-and-non-bmp
#guard StructuralIdentity.encode (.str "é𐐷x") == some "kl-struct-v1:1:t4:\\u00E9\\uD801\\uDC37x"
-- nested
#guard StructuralIdentity.encode (.sequenceValue [(.atom 1), (.listValue [(.atom 2), (.sequenceValue [])]), (.listValue [])]) == some "kl-struct-v1:6:n3:1e0n3:2e0s0:;l2:1,2,;l0:;s3:0,3,4,;"
-- shared-subtree
#guard StructuralIdentity.encode (.sequenceValue [(.listValue [(.atom 1), (.str "a")]), (.listValue [(.atom 1), (.str "a")])]) == some "kl-struct-v1:4:n3:1e0t1:al2:0,1,;s2:2,2,;"
-- independent-subtrees
#guard StructuralIdentity.encode (.sequenceValue [(.listValue [(.atom 1), (.str "a")]), (.listValue [(.atom 1), (.str "a")])]) == some "kl-struct-v1:4:n3:1e0t1:al2:0,1,;s2:2,2,;"
-- repeated-atom
#guard StructuralIdentity.encode (.listValue [(.atom 7), (.atom 7)]) == some "kl-struct-v1:2:n3:7e0l2:0,0,;"
-- repeated-across-levels
#guard StructuralIdentity.encode (.listValue [(.listValue [(.atom 1)]), (.atom 1)]) == some "kl-struct-v1:3:n3:1e0l1:0,;l2:1,0,;"
-- eleven-atoms
#guard StructuralIdentity.encode (.listValue [(.atom 0), (.atom 1), (.atom 2), (.atom 3), (.atom 4), (.atom 5), (.atom 6), (.atom 7), (.atom 8), (.atom 9), (.atom 10)]) == some "kl-struct-v1:12:n1:0n3:1e0n3:2e0n3:3e0n3:4e0n3:5e0n3:6e0n3:7e0n3:8e0n3:9e0n3:1e1l11:0,1,2,3,4,5,6,7,8,9,10,;"
-- long-string
#guard StructuralIdentity.encode (.str "hello, world") == some "kl-struct-v1:1:t12:hello, world"


-- HP-01a: host parent property read through an opened block
def hp_01a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.num 7])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_01a == "ok raw=7 n=1"
#guard structural hp_01a == some "kl-struct-v1:1:n3:7e0"
#guard cacheEntries hp_01a "P" == some 1
#guard cacheEntries hp_01a "Run" == some 1
#guard cacheTotal hp_01a == some 2

-- HP-01b: three reads of one host property share ONE entry
def hp_01b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.num 7])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.binary .add (.resolve "P") (.resolve "P")) (.resolve "P"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_01b == "ok raw=21 n=1"
#guard structural hp_01b == some "kl-struct-v1:1:n4:21e0"
#guard cacheEntries hp_01b "P" == some 1
#guard cacheEntries hp_01b "Run" == some 1
#guard cacheTotal hp_01b == some 2

-- HP-01c: an exported host property is evaluated once per run (both readers get the first evaluation)
def hp_01c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_01c == "ok raw=S[1, 1] n=1"
#guard structural hp_01c == some "kl-struct-v1:2:n3:1e0s2:0,0,;"
#guard cacheEntries hp_01c "P" == some 1
#guard cacheEntries hp_01c "Run" == some 1
#guard cacheTotal hp_01c == some 2

-- HP-01d: a public host property is read by the block like a private one
def hp_01d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "P" (alg [] [] [] [.num 3])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .mul (.resolve "P") (.num 2))])] [])))] [] [.resolve "Run"]))
#guard obs hp_01d == "ok raw=6 n=1"
#guard structural hp_01d == some "kl-struct-v1:1:n3:6e0"
#guard cacheEntries hp_01d "P" == some 1
#guard cacheEntries hp_01d "Run" == some 1
#guard cacheTotal hp_01d == some 2

-- HP-02a: a grandparent host level is reached through its parent level
def hp_02a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none (some (.host 0)))) [] [] [privateProp "W" (alg [] [] [] [.num 2])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.binary .mul (.resolve "V") (.num 10)) (.resolve "W"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_02a == "ok raw=12 n=1"
#guard structural hp_02a == some "kl-struct-v1:1:n4:12e0"
#guard cacheEntries hp_02a "Run" == some 1
#guard cacheEntries hp_02a "V" == some 1
#guard cacheEntries hp_02a "W" == some 1
#guard cacheTotal hp_02a == some 3

-- HP-02b: the nearest declaring level wins (parent V shadows grandparent V)
def hp_02b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none (some (.host 0)))) [] [] [privateProp "V" (alg [] [] [] [.num 2])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"])] [])))] [] [.resolve "Run"]))
#guard obs hp_02b == "ok raw=2 n=1"
#guard structural hp_02b == some "kl-struct-v1:1:n3:2e0"
#guard cacheEntries hp_02b "Run" == some 1
#guard cacheEntries hp_02b "V" == some 1
#guard cacheTotal hp_02b == some 2

-- HP-02c: a host level's own property beats its opened provider (ownership before opens)
def hp_02c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [(.algorithmExpr (alg [] [] [publicProp "V" (alg [] [] [] [.num 5])] []))] [privateProp "V" (alg [] [] [] [.num 2])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"])] [])))] [] [.resolve "Run"]))
#guard obs hp_02c == "ok raw=2 n=1"
#guard structural hp_02c == some "kl-struct-v1:1:n3:2e0"
#guard cacheEntries hp_02c "Run" == some 1
#guard cacheEntries hp_02c "V" == some 1
#guard cacheTotal hp_02c == some 2

-- HP-02d: a grandparent's property beats the parent level's open (the whole owner walk first)
def hp_02d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none (some (.host 0)))) [] [(.algorithmExpr (alg [] [] [publicProp "V" (alg [] [] [] [.num 5])] []))] [] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"])] [])))] [] [.resolve "Run"]))
#guard obs hp_02d == "ok raw=1 n=1"
#guard structural hp_02d == some "kl-struct-v1:1:n3:1e0"
#guard cacheEntries hp_02d "Run" == some 1
#guard cacheEntries hp_02d "V" == some 1
#guard cacheTotal hp_02d == some 2

-- HP-02e: a name no level declares falls back to a host level's open provider
def hp_02e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none (some (.host 0)))) [] [(.algorithmExpr (alg [] [] [publicProp "U" (alg [] [] [] [.num 5])] []))] [] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.resolve "U") (.resolve "V"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_02e == "ok raw=6 n=1"
#guard structural hp_02e == some "kl-struct-v1:1:n3:6e0"
#guard cacheEntries hp_02e "Run" == some 1
#guard cacheEntries hp_02e "U" == some 1
#guard cacheEntries hp_02e "V" == some 1
#guard cacheTotal hp_02e == some 3

-- HP-02f: an undeclared name under a host chain is an unknown name
def hp_02f : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none (some (.host 0)))) [] [] [privateProp "W" (alg [] [] [] [.num 2])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "Z"])] [])))] [] [.resolve "Run"]))
#guard obs hp_02f == "err unknownName"
#guard errorObs hp_02f == .matched (some { kind := "unknownName", names := ["Z"], counts := [] })
#guard cacheTotal hp_02f == some 0

-- HP-03a: a block opens a host-declared namespace and reads its PUBLIC member
def hp_03a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicProp "A" (alg [] [] [] [.num 1]), privateProp "B" (alg [] [] [] [.num 2])] [])] [] [] none (some (.host 0)))) (alg [] [.resolve "M"] [publicProp "Run" (alg [] [] [] [.resolve "A"])] [])))] [] [.resolve "Run"]))
#guard obs hp_03a == "ok raw=1 n=1"
#guard structural hp_03a == some "kl-struct-v1:1:n3:1e0"
#guard cacheEntries hp_03a "A" == some 1
#guard cacheEntries hp_03a "Run" == some 1
#guard cacheTotal hp_03a == some 2

-- HP-03b: a PRIVATE member is not open-provided (structured refusal)
def hp_03b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicProp "A" (alg [] [] [] [.num 1]), privateProp "B" (alg [] [] [] [.num 2])] [])] [] [] none (some (.host 0)))) (alg [] [.resolve "M"] [publicProp "Run" (alg [] [] [] [.resolve "B"])] [])))] [] [.resolve "Run"]))
#guard obs hp_03b == "err unknownName"
#guard errorObs hp_03b == .matched (some { kind := "unknownName", names := ["B"], counts := [] })
#guard cacheTotal hp_03b == some 0

-- HP-03c: structural dot access selects the declared PRIVATE member of a host namespace
def hp_03c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicProp "A" (alg [] [] [] [.num 1]), privateProp "B" (alg [] [] [] [.num 2])] [])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.dotCall (.resolve "M") "B" none) (.dotCall (.resolve "M") "A" none))])] [])))] [] [.resolve "Run"]))
#guard obs hp_03c == "ok raw=3 n=1"
#guard structural hp_03c == some "kl-struct-v1:1:n3:3e0"
#guard cacheEntries hp_03c "A" == some 1
#guard cacheEntries hp_03c "B" == some 1
#guard cacheEntries hp_03c "Run" == some 1
#guard cacheTotal hp_03c == some 3

-- HP-03d: a dotted open step through a private member is refused
def hp_03d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [privateProp "N" (alg [] [] [publicProp "K" (alg [] [] [] [.num 4])] [])] [])] [] [] none (some (.host 0)))) (alg [] [(.dotCall (.resolve "M") "N" none)] [publicProp "Run" (alg [] [] [] [.resolve "K"])] [])))] [] [.resolve "Run"]))
#guard obs hp_03d == "err notPublicProperty"
#guard errorObs hp_03d == .matched (some { kind := "notPublicProperty", names := ["N"], counts := [] })
#guard cacheTotal hp_03d == some 0

-- HP-03e: a dotted open step through a public member is open-provided
def hp_03e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicProp "N" (alg [] [] [publicProp "K" (alg [] [] [] [.num 4])] [])] [])] [] [] none (some (.host 0)))) (alg [] [(.dotCall (.resolve "M") "N" none)] [publicProp "Run" (alg [] [] [] [.resolve "K"])] [])))] [] [.resolve "Run"]))
#guard obs hp_03e == "ok raw=4 n=1"
#guard structural hp_03e == some "kl-struct-v1:1:n3:4e0"
#guard cacheEntries hp_03e "K" == some 1
#guard cacheEntries hp_03e "Run" == some 1
#guard cacheTotal hp_03e == some 2

-- HP-04a: a block property shadows the host parent's property of the same name
def hp_04a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"]), privateProp "V" (alg [] [] [] [.num 3])] [])))] [] [.resolve "Run"]))
#guard obs hp_04a == "ok raw=3 n=1"
#guard structural hp_04a == some "kl-struct-v1:1:n3:3e0"
#guard cacheEntries hp_04a "Run" == some 1
#guard cacheEntries hp_04a "V" == some 1
#guard cacheTotal hp_04a == some 2

-- HP-04b: a block property shadows a host level's open provider
def hp_04b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [(.algorithmExpr (alg [] [] [publicProp "V" (alg [] [] [] [.num 9])] []))] [] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"]), privateProp "V" (alg [] [] [] [.num 3])] [])))] [] [.resolve "Run"]))
#guard obs hp_04b == "ok raw=3 n=1"
#guard structural hp_04b == some "kl-struct-v1:1:n3:3e0"
#guard cacheEntries hp_04b "Run" == some 1
#guard cacheEntries hp_04b "V" == some 1
#guard cacheTotal hp_04b == some 2

-- HP-04c: a property of the reading body shadows both block and host declarations
def hp_04c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [privateProp "V" (alg [] [] [] [.num 4])] [.resolve "V"]), privateProp "V" (alg [] [] [] [.num 3])] [])))] [] [.resolve "Run"]))
#guard obs hp_04c == "ok raw=4 n=1"
#guard structural hp_04c == some "kl-struct-v1:1:n3:4e0"
#guard cacheEntries hp_04c "Run" == some 1
#guard cacheEntries hp_04c "V" == some 1
#guard cacheTotal hp_04c == some 2

-- HP-05a: an unactivated local-only host property keys on the ACCESS context: one entry per G call
def hp_05a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateLocalProp "P" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_05a == "ok raw=S[1, 2] n=1"
#guard structural hp_05a == some "kl-struct-v1:3:n3:1e0n3:2e0s2:0,1,;"
#guard cacheEntries hp_05a "P" == some 2
#guard cacheEntries hp_05a "Run" == some 1
#guard cacheTotal hp_05a == some 3

-- HP-05b: two reads within ONE access context share the local-only entry
def hp_05b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateLocalProp "P" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G2") [.num 3])]), publicProp "G2" (alg ["x"] [] [] [(.binary .add (.resolve "P") (.resolve "P"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_05b == "ok raw=2 n=1"
#guard structural hp_05b == some "kl-struct-v1:1:n3:2e0"
#guard cacheEntries hp_05b "P" == some 1
#guard cacheEntries hp_05b "Run" == some 1
#guard cacheTotal hp_05b == some 2

-- HP-05c: a host level's Parameters take no part in property lookup (the name stays unknown)
def hp_05c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "x"])] [])))] [] [.resolve "Run"]))
#guard obs hp_05c == "err unknownName"
#guard errorObs hp_05c == .matched (some { kind := "unknownName", names := ["x"], counts := [] })
#guard cacheTotal hp_05c == some 0

-- HP-05d: structural access M.L to a local-only member whose input x is named by the host level's Parameters
def hp_05d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateProp "M" (alg [] [] [publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [(.dotCall (.resolve "M") "L" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_05d == "err localOnlyProperty"
#guard errorObs hp_05d == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })
#guard cacheTotal hp_05d == some 0

-- HP-05e: structural access M.L to a local-only member whose input x is named by no level
def hp_05e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [(.dotCall (.resolve "M") "L" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_05e == "err localOnlyProperty"
#guard errorObs hp_05e == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })
#guard cacheTotal hp_05e == some 0

-- HP-05f: structural access M.L to a local-only member whose input x is required at owner depth 1, the host level naming it
def hp_05f : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateProp "M" (alg [] [] [{ (publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])) with requiredOwnerDepths := some [("x", some 1)] }] [])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [(.dotCall (.resolve "M") "L" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_05f == "err localOnlyProperty"
#guard errorObs hp_05f == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })
#guard cacheTotal hp_05f == some 0

-- HP-05g: structural access M.L to a local-only member whose input x is required at owner depth 1, the host level NOT naming it
def hp_05g : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [{ (publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])) with requiredOwnerDepths := some [("x", some 1)] }] [])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [(.dotCall (.resolve "M") "L" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_05g == "err localOnlyProperty"
#guard errorObs hp_05g == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })
#guard cacheTotal hp_05g == some 0

-- HP-05h: open access to a local-only member whose input x is named by the host level's Parameters
def hp_05h : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateProp "M" (alg [] [] [publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [])] [] [] none (some (.host 0)))) (alg [] [.resolve "M"] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "L"])] [])))] [] [.resolve "Run"]))
#guard obs hp_05h == "err localOnlyProperty"
#guard errorObs hp_05h == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })
#guard cacheTotal hp_05h == some 0

-- HP-05i: open access to a local-only member whose input x is named by no level
def hp_05i : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [])] [] [] none (some (.host 0)))) (alg [] [.resolve "M"] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "L"])] [])))] [] [.resolve "Run"]))
#guard obs hp_05i == "err localOnlyProperty"
#guard errorObs hp_05i == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })
#guard cacheTotal hp_05i == some 0

-- HP-05j: structural access Box.L to a local-only member naming an unbound input, exact owners ABSENT
def hp_05j : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Box" (alg [] [] [publicLocalProp "L" (.localCapturedAncestorParams ["absent"]) (alg [] [] [] [.num 7])] [])] [(.dotCall (.resolve "Box") "L" none)]))
#guard obs hp_05j == "err localOnlyProperty"
#guard errorObs hp_05j == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })
#guard cacheTotal hp_05j == some 0

-- HP-05k: structural access Box.L to a local-only member naming an unbound input, exact owners EMPTY
def hp_05k : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Box" (alg [] [] [{ (publicLocalProp "L" (.localCapturedAncestorParams ["absent"]) (alg [] [] [] [.num 7])) with requiredOwnerDepths := some [] }] [])] [(.dotCall (.resolve "Box") "L" none)]))
#guard obs hp_05k == "ok raw=7 n=1"
#guard structural hp_05k == some "kl-struct-v1:1:n3:7e0"
#guard cacheEntries hp_05k "L" == some 1
#guard cacheTotal hp_05k == some 1

-- HP-06a: CACHE-PUB-1: H(x) = P() establishes the empty entry; the later read reuses it
def hp_06a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "H") [.num 1]), (.call (.resolve "G") [.num 2])]), publicProp "H" (alg ["x"] [] [] [(.call (.resolve "P") [])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_06a == "ok raw=S[1, 1] n=1"
#guard structural hp_06a == some "kl-struct-v1:2:n3:1e0s2:0,0,;"
#guard cacheEntries hp_06a "P" == some 1
#guard cacheEntries hp_06a "Run" == some 1
#guard cacheTotal hp_06a == some 2

-- HP-06b: an established entry is never replaced by a later fresh P()
def hp_06b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "H") [.num 2]), (.call (.resolve "G") [.num 3])]), publicProp "H" (alg ["x"] [] [] [(.call (.resolve "P") [])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_06b == "ok raw=S[1, 2, 1] n=1"
#guard structural hp_06b == some "kl-struct-v1:3:n3:1e0n3:2e0s3:0,1,0,;"
#guard cacheEntries hp_06b "P" == some 1
#guard cacheEntries hp_06b "Run" == some 1
#guard cacheTotal hp_06b == some 2

-- HP-06c: Q-37: the outermost read owns the entry, the re-entrant read publishes nothing
def hp_06c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.call (.resolve "K") [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])])]), privateProp "K" (.conditional none [] [⟨.litInt 1, (alg [] [] [] [(.binary .add (.call (.resolve "G") [.num 0]) (.num 100))])⟩, ⟨.bind "n", (alg [] [] [] [.num 1])⟩]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 5])])] [])))] [] [.resolve "Run"]))
#guard obs hp_06c == "ok raw=S[101, 101] n=1"
#guard structural hp_06c == some "kl-struct-v1:2:n5:101e0s2:0,0,;"
#guard cacheEntries hp_06c "P" == some 1
#guard cacheEntries hp_06c "Run" == some 1
#guard cacheTotal hp_06c == some 2

-- HP-06d: Q-37 with the owning access an explicit P() (CACHE-PUB-1)
def hp_06d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.call (.resolve "K") [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])])]), privateProp "K" (.conditional none [] [⟨.litInt 1, (alg [] [] [] [(.binary .add (.call (.resolve "G") [.num 0]) (.num 100))])⟩, ⟨.bind "n", (alg [] [] [] [.num 1])⟩]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "H") [.num 1]), (.call (.resolve "G") [.num 5])]), publicProp "H" (alg ["x"] [] [] [(.call (.resolve "P") [])])] [])))] [] [.resolve "Run"]))
#guard obs hp_06d == "ok raw=S[101, 101] n=1"
#guard structural hp_06d == some "kl-struct-v1:2:n5:101e0s2:0,0,;"
#guard cacheEntries hp_06d "P" == some 1
#guard cacheEntries hp_06d "Run" == some 1
#guard cacheTotal hp_06d == some 2

-- HP-07a: two calls of a host-declared F keep their own local-only L and M entries
def hp_07a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["x"] [] [privateLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.binary .mul (.param "x") (.num 10))]), privateLocalProp "M" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.binary .add (.resolve "L") (.num 1))])] [.resolve "M"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])])] [])))] [] [.resolve "Run"]))
#guard obs hp_07a == "ok raw=S[11, 21] n=1"
#guard structural hp_07a == some "kl-struct-v1:3:n4:11e0n4:21e0s2:0,1,;"
#guard cacheEntries hp_07a "L" == some 2
#guard cacheEntries hp_07a "M" == some 2
#guard cacheEntries hp_07a "Run" == some 1
#guard cacheTotal hp_07a == some 5

-- HP-07b: repeated calls with one argument still bind fresh activations (D2)
def hp_07b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["x"] [] [privateLocalProp "L" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.binary .mul (.param "x") (.num 10))]), privateLocalProp "M" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.binary .add (.resolve "L") (.num 1))])] [.resolve "M"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.call (.resolve "F") [.num 1]) (.call (.resolve "F") [.num 1]))])] [])))] [] [.resolve "Run"]))
#guard obs hp_07b == "ok raw=22 n=1"
#guard structural hp_07b == some "kl-struct-v1:1:n4:22e0"
#guard cacheEntries hp_07b "L" == some 2
#guard cacheEntries hp_07b "M" == some 2
#guard cacheEntries hp_07b "Run" == some 1
#guard cacheTotal hp_07b == some 5

-- HP-08a: two fresh equal host levels, each with its own P: two owners
def hp_08a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08a == "ok raw=S[1, 2] n=2"
#guard structural hp_08a == some "kl-struct-v1:3:n3:1e0n3:2e0s2:0,1,;"
#guard cacheEntries hp_08a "P" == some 2
#guard cacheEntries hp_08a "RunA" == some 1
#guard cacheEntries hp_08a "RunB" == some 1
#guard cacheTotal hp_08a == some 4

-- HP-08b: ONE Property object declared by two distinct host levels: two owners (former 5b shape)
def hp_08b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 1)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08b == "ok raw=S[1, 2] n=2"
#guard structural hp_08b == some "kl-struct-v1:3:n3:1e0n3:2e0s2:0,1,;"
#guard cacheEntries hp_08b "P" == some 2
#guard cacheEntries hp_08b "RunA" == some 1
#guard cacheEntries hp_08b "RunB" == some 1
#guard cacheTotal hp_08b == some 4

-- HP-08c: two distinct host levels sharing ONE property list: two owners
def hp_08c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 1)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08c == "ok raw=S[1, 2] n=2"
#guard structural hp_08c == some "kl-struct-v1:3:n3:1e0n3:2e0s2:0,1,;"
#guard cacheEntries hp_08c "P" == some 2
#guard cacheEntries hp_08c "RunA" == some 1
#guard cacheEntries hp_08c "RunB" == some 1
#guard cacheTotal hp_08c == some 4

-- HP-08d: a record `with` copy of a host level is another owner
def hp_08d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 1)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08d == "ok raw=S[1, 2] n=2"
#guard structural hp_08d == some "kl-struct-v1:3:n3:1e0n3:2e0s2:0,1,;"
#guard cacheEntries hp_08d "P" == some 2
#guard cacheEntries hp_08d "RunA" == some 1
#guard cacheEntries hp_08d "RunB" == some 1
#guard cacheTotal hp_08d == some 4

-- HP-08e: distinct parent objects over record-equal grandparents (copies) keep two owners
def hp_08e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) [] [] [] [] [] none (some (.host 1)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 2)))) [] [] [] [] [] none (some (.host 3)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08e == "ok raw=S[1, 2] n=2"
#guard structural hp_08e == some "kl-struct-v1:3:n3:1e0n3:2e0s2:0,1,;"
#guard cacheEntries hp_08e "P" == some 2
#guard cacheEntries hp_08e "RunA" == some 1
#guard cacheEntries hp_08e "RunB" == some 1
#guard cacheTotal hp_08e == some 4

-- HP-08f: two distinct host levels with distinct declarations of different values
def hp_08f : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.num 10])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.num 20])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_08f == "ok raw=S[10, 20] n=2"
#guard structural hp_08f == some "kl-struct-v1:3:n3:1e1n3:2e1s2:0,1,;"
#guard cacheEntries hp_08f "P" == some 2
#guard cacheEntries hp_08f "RunA" == some 1
#guard cacheEntries hp_08f "RunB" == some 1
#guard cacheTotal hp_08f == some 4

-- HP-08g: NEED-04: F from two fresh equal host levels is two callables
def hp_08g : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "F" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "FA" (.alias none [] [] (.resolve "F"))] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "F" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "FB" (.alias none [] [] (.resolve "F"))] [])))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_08g == "err type"
#guard cacheTotal hp_08g == some 0

-- HP-08h: NEED-04: one F Property in two distinct host levels is two callables
def hp_08h : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "FA" (.alias none [] [] (.resolve "F"))] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none (some (.host 1)))) (alg [] [] [publicProp "FB" (.alias none [] [] (.resolve "F"))] [])))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_08h == "err type"
#guard cacheTotal hp_08h == some 0

-- HP-08i: NEED-04: one property list in two distinct host levels is two callables
def hp_08i : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "FA" (.alias none [] [] (.resolve "F"))] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none (some (.host 1)))) (alg [] [] [publicProp "FB" (.alias none [] [] (.resolve "F"))] [])))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_08i == "err type"
#guard cacheTotal hp_08i == some 0

-- HP-08j: NEED-04: a record `with` copy of the host level is another callable scope
def hp_08j : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "FA" (.alias none [] [] (.resolve "F"))] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none (some (.host 1)))) (alg [] [] [publicProp "FB" (.alias none [] [] (.resolve "F"))] [])))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_08j == "err type"
#guard cacheTotal hp_08j == some 0

-- HP-08k: a host level and an evaluator-owned block declaring ONE property list are two owners
def hp_08k : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 1) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])])] []))), (.algorithmExpr (alg [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 2) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 3) }] []))] [] [.resolve "RunA", (.call (.resolve "G") [.num 2])]))
#guard obs hp_08k == "ok raw=S[1, 2] n=2"
#guard structural hp_08k == some "kl-struct-v1:3:n3:1e0n3:2e0s2:0,1,;"
#guard cacheEntries hp_08k "P" == some 2
#guard cacheEntries hp_08k "RunA" == some 1
#guard cacheTotal hp_08k == some 3

-- HP-09a: one host level object opened by two blocks: one owner, one entry
def hp_09a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_09a == "ok raw=S[1, 1] n=2"
#guard structural hp_09a == some "kl-struct-v1:2:n3:1e0s2:0,0,;"
#guard cacheEntries hp_09a "P" == some 1
#guard cacheEntries hp_09a "RunA" == some 1
#guard cacheEntries hp_09a "RunB" == some 1
#guard cacheTotal hp_09a == some 3

-- HP-09b: one grandparent object reached through two distinct children: one owner
def hp_09b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) [] [] [privateProp "W" (alg [] [] [] [.num 1])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) [] [] [privateProp "W" (alg [] [] [] [.num 2])] [] [] none (some (.host 2)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_09b == "ok raw=S[1, 1] n=2"
#guard structural hp_09b == some "kl-struct-v1:2:n3:1e0s2:0,0,;"
#guard cacheEntries hp_09b "P" == some 1
#guard cacheEntries hp_09b "RunA" == some 1
#guard cacheEntries hp_09b "RunB" == some 1
#guard cacheTotal hp_09b == some 3

-- HP-09c: one opened block object listed twice in one open list is one provider
def hp_09c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 3)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 2) }] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "Run" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]))) with identity := some (.shared 0) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 1) }] [])))), (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 3)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 2) }] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "Run" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]))) with identity := some (.shared 0) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 1) }] []))))] [] [.resolve "Run"]))
#guard obs hp_09c == "ok raw=S[1, 1] n=1"
#guard structural hp_09c == some "kl-struct-v1:2:n3:1e0s2:0,0,;"
#guard cacheEntries hp_09c "P" == some 1
#guard cacheEntries hp_09c "Run" == some 1
#guard cacheTotal hp_09c == some 2

-- HP-09d: NEED-04: F reached through ONE host level object twice is one callable
def hp_09d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "FA" (.alias none [] [] (.resolve "F"))] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "FB" (.alias none [] [] (.resolve "F"))] [])))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_09d == "ok raw=0 n=1"
#guard structural hp_09d == some "kl-struct-v1:1:n1:0"
#guard cacheTotal hp_09d == some 0

-- HP-10a: a block opens a dotted path into a host-declared namespace
def hp_10a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Lib" (alg [] [] [publicProp "N" (alg [] [] [publicProp "K" (alg [] [] [] [.num 4])] [])] [])] [] [] none (some (.host 0)))) (alg [] [(.dotCall (.resolve "Lib") "N" none)] [publicProp "Run" (alg [] [] [] [.resolve "K"])] [])))] [] [.resolve "Run"]))
#guard obs hp_10a == "ok raw=4 n=1"
#guard structural hp_10a == some "kl-struct-v1:1:n3:4e0"
#guard cacheEntries hp_10a "K" == some 1
#guard cacheEntries hp_10a "Run" == some 1
#guard cacheTotal hp_10a == some 2

-- HP-10b: a block's own open target is another block with ITS OWN pre-wired parent
def hp_10b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Y" (alg [] [] [] [.num 100])] [] [] none (some (.host 1)))) (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Z" (alg [] [] [] [.num 5])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Z2" (alg [] [] [] [(.binary .add (.resolve "Z") (.num 1))])] [])))] [publicProp "Run" (alg [] [] [] [(.binary .add (.resolve "Z2") (.resolve "Y"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_10b == "ok raw=106 n=1"
#guard structural hp_10b == some "kl-struct-v1:1:n5:106e0"
#guard cacheEntries hp_10b "Run" == some 1
#guard cacheEntries hp_10b "Y" == some 1
#guard cacheEntries hp_10b "Z" == some 1
#guard cacheEntries hp_10b "Z2" == some 1
#guard cacheTotal hp_10b == some 4

-- HP-10c: structural member access into a host-declared object
def hp_10c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Obj" (alg [] [] [publicProp "A" (alg [] [] [] [.num 2]), privateProp "B" (alg [] [] [] [.num 3])] [])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.dotCall (.resolve "Obj") "A" none) (.dotCall (.resolve "Obj") "B" none))])] [])))] [] [.resolve "Run"]))
#guard obs hp_10c == "ok raw=5 n=1"
#guard structural hp_10c == some "kl-struct-v1:1:n3:5e0"
#guard cacheEntries hp_10c "A" == some 1
#guard cacheEntries hp_10c "B" == some 1
#guard cacheEntries hp_10c "Run" == some 1
#guard cacheTotal hp_10c == some 3

-- HP-10d: a host level's own open target supplies a name to the block
def hp_10d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [(.algorithmExpr (alg [] [] [publicProp "Q" (alg [] [] [] [.num 8])] []))] [] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "Q"])] [])))] [] [.resolve "Run"]))
#guard obs hp_10d == "ok raw=8 n=1"
#guard structural hp_10d == some "kl-struct-v1:1:n3:8e0"
#guard cacheEntries hp_10d "Q" == some 1
#guard cacheEntries hp_10d "Run" == some 1
#guard cacheTotal hp_10d == some 2

-- HP-10e: a member of a member through a two-level host chain
def hp_10e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "Outer" (alg [] [] [publicProp "Mid" (alg [] [] [publicProp "Leaf" (alg [] [] [] [.num 6])] [])] [])] [] [] none (some (.host 0)))) [] [] [privateProp "W" (alg [] [] [] [.num 1])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.dotCall (.dotCall (.resolve "Outer") "Mid" none) "Leaf" none) (.resolve "W"))])] [])))] [] [.resolve "Run"]))
#guard obs hp_10e == "ok raw=7 n=1"
#guard structural hp_10e == some "kl-struct-v1:1:n3:7e0"
#guard cacheEntries hp_10e "Leaf" == some 1
#guard cacheEntries hp_10e "Run" == some 1
#guard cacheEntries hp_10e "W" == some 1
#guard cacheTotal hp_10e == some 3

-- HP-10f: a shared expression diamond in a host parent uses compact Lean let terms
def hp_10f : Expr :=
  (let hd0 : Expr := .resolve "P"; let hd1 : Algorithm := (alg [] [] [] [hd0]); let hd2 : Expr := .num 1; let hd3 : Expr := (.binary .add (hd2) (hd2)); let hd4 : Expr := (.binary .add (hd3) (hd3)); let hd5 : Expr := (.binary .add (hd4) (hd4)); let hd6 : Expr := (.binary .add (hd5) (hd5)); let hd7 : Expr := (.binary .add (hd6) (hd6)); let hd8 : Expr := (.binary .add (hd7) (hd7)); let hd9 : Expr := (.binary .add (hd8) (hd8)); let hd10 : Expr := (.binary .add (hd9) (hd9)); let hd11 : Expr := (.binary .add (hd10) (hd10)); let hd12 : Expr := (.binary .add (hd11) (hd11)); let hd13 : Expr := (.binary .add (hd12) (hd12)); let hd14 : Expr := (.binary .add (hd13) (hd13)); let hd15 : Algorithm := (alg [] [] [] [hd14]); let hd16 : ScopeCtx := (ScopeCtx.mk none [] [] [privateProp "P" hd15] [] [] none (some (.host 0))); let hd17 : Algorithm := (Algorithm.withParent (some hd16) (alg [] [] [publicProp "Run" hd1] [])); let hd18 : Expr := (.algorithmExpr hd17); let hd19 : Expr := .resolve "Run"; let hd20 : Algorithm := (alg [] [hd18] [] [hd19]); let hd21 : Expr := (.algorithmExpr hd20); hd21)
#guard obs hp_10f == "ok raw=4096 n=1"
#guard structural hp_10f == some "kl-struct-v1:1:n6:4096e0"
#guard cacheEntries hp_10f "P" == some 1
#guard cacheEntries hp_10f "Run" == some 1
#guard cacheTotal hp_10f == some 2

-- HP-10g: compact terms keep the declaring contexts of shared host properties distinct
def hp_10g : Expr :=
  (let hd0 : Expr := .resolve "G"; let hd1 : Expr := .num 1; let hd2 : Expr := (.call (hd0) [hd1]); let hd3 : Algorithm := (alg [] [] [] [hd2]); let hd4 : Expr := .resolve "P"; let hd5 : Algorithm := (alg ["x"] [] [] [hd4]); let hd6 : Expr := (.algorithmExpr (Algorithm.builtin .tickBuiltin)); let hd7 : Expr := (.call (hd6) []); let hd8 : Algorithm := (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [hd7])); let hd9 : Expr := .num 1; let hd10 : Expr := (.binary .add (hd9) (hd9)); let hd11 : Expr := (.binary .add (hd10) (hd10)); let hd12 : Expr := (.binary .add (hd11) (hd11)); let hd13 : Expr := (.binary .add (hd12) (hd12)); let hd14 : Expr := (.binary .add (hd13) (hd13)); let hd15 : Expr := (.binary .add (hd14) (hd14)); let hd16 : Expr := (.binary .add (hd15) (hd15)); let hd17 : Expr := (.binary .add (hd16) (hd16)); let hd18 : Expr := (.binary .add (hd17) (hd17)); let hd19 : Expr := (.binary .add (hd18) (hd18)); let hd20 : Expr := (.binary .add (hd19) (hd19)); let hd21 : Expr := (.binary .add (hd20) (hd20)); let hd22 : Algorithm := (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [hd21])); let hd23 : ScopeCtx := (ScopeCtx.mk none [] [] [{ (privateProp "P" hd8) with identity := some (.shared 0) }, { (privateProp "Large" hd22) with identity := some (.shared 1) }] [] [] none (some (.host 0))); let hd24 : Algorithm := (Algorithm.withParent (some hd23) (alg [] [] [publicProp "RunA" hd3, publicProp "G" hd5] [])); let hd25 : Expr := (.algorithmExpr hd24); let hd26 : Expr := .resolve "G"; let hd27 : Expr := .num 2; let hd28 : Expr := (.call (hd26) [hd27]); let hd29 : Algorithm := (alg [] [] [] [hd28]); let hd30 : Expr := .resolve "P"; let hd31 : Algorithm := (alg ["x"] [] [] [hd30]); let hd32 : Expr := (.algorithmExpr (Algorithm.builtin .tickBuiltin)); let hd33 : Expr := (.call (hd32) []); let hd34 : Algorithm := (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [hd33])); let hd35 : Expr := .num 1; let hd36 : Expr := (.binary .add (hd35) (hd35)); let hd37 : Expr := (.binary .add (hd36) (hd36)); let hd38 : Expr := (.binary .add (hd37) (hd37)); let hd39 : Expr := (.binary .add (hd38) (hd38)); let hd40 : Expr := (.binary .add (hd39) (hd39)); let hd41 : Expr := (.binary .add (hd40) (hd40)); let hd42 : Expr := (.binary .add (hd41) (hd41)); let hd43 : Expr := (.binary .add (hd42) (hd42)); let hd44 : Expr := (.binary .add (hd43) (hd43)); let hd45 : Expr := (.binary .add (hd44) (hd44)); let hd46 : Expr := (.binary .add (hd45) (hd45)); let hd47 : Expr := (.binary .add (hd46) (hd46)); let hd48 : Algorithm := (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [hd47])); let hd49 : ScopeCtx := (ScopeCtx.mk none [] [] [{ (privateProp "P" hd34) with identity := some (.shared 0) }, { (privateProp "Large" hd48) with identity := some (.shared 1) }] [] [] none (some (.host 1))); let hd50 : Algorithm := (Algorithm.withParent (some hd49) (alg [] [] [publicProp "RunB" hd29, publicProp "G" hd31] [])); let hd51 : Expr := (.algorithmExpr hd50); let hd52 : Expr := .resolve "RunA"; let hd53 : Expr := .resolve "RunB"; let hd54 : Algorithm := (alg [] [hd25, hd51] [] [hd52, hd53]); let hd55 : Expr := (.algorithmExpr hd54); hd55)
#guard obs hp_10g == "ok raw=S[1, 2] n=2"
#guard structural hp_10g == some "kl-struct-v1:3:n3:1e0n3:2e0s2:0,1,;"
#guard cacheEntries hp_10g "Large" == some 0
#guard cacheEntries hp_10g "P" == some 2
#guard cacheEntries hp_10g "RunA" == some 1
#guard cacheEntries hp_10g "RunB" == some 1
#guard cacheTotal hp_10g == some 4

-- HP-10h: an evaluator-accepted spread spine beyond recursive depth uses iterative compact printing
def hp_10h : Expr :=
  (let hd0 : Expr := .resolve "P"; let hd1 : Algorithm := (alg [] [] [] [hd0]); let hd2 : Expr := .num 1; let hd3 : Expr := (.sequenceSpread (hd2)); let hd4 : Expr := (.sequenceSpread (hd3)); let hd5 : Expr := (.sequenceSpread (hd4)); let hd6 : Expr := (.sequenceSpread (hd5)); let hd7 : Expr := (.sequenceSpread (hd6)); let hd8 : Expr := (.sequenceSpread (hd7)); let hd9 : Expr := (.sequenceSpread (hd8)); let hd10 : Expr := (.sequenceSpread (hd9)); let hd11 : Expr := (.sequenceSpread (hd10)); let hd12 : Expr := (.sequenceSpread (hd11)); let hd13 : Expr := (.sequenceSpread (hd12)); let hd14 : Expr := (.sequenceSpread (hd13)); let hd15 : Expr := (.sequenceSpread (hd14)); let hd16 : Expr := (.sequenceSpread (hd15)); let hd17 : Expr := (.sequenceSpread (hd16)); let hd18 : Expr := (.sequenceSpread (hd17)); let hd19 : Expr := (.sequenceSpread (hd18)); let hd20 : Expr := (.sequenceSpread (hd19)); let hd21 : Expr := (.sequenceSpread (hd20)); let hd22 : Expr := (.sequenceSpread (hd21)); let hd23 : Expr := (.sequenceSpread (hd22)); let hd24 : Expr := (.sequenceSpread (hd23)); let hd25 : Expr := (.sequenceSpread (hd24)); let hd26 : Expr := (.sequenceSpread (hd25)); let hd27 : Expr := (.sequenceSpread (hd26)); let hd28 : Expr := (.sequenceSpread (hd27)); let hd29 : Expr := (.sequenceSpread (hd28)); let hd30 : Expr := (.sequenceSpread (hd29)); let hd31 : Expr := (.sequenceSpread (hd30)); let hd32 : Expr := (.sequenceSpread (hd31)); let hd33 : Expr := (.sequenceSpread (hd32)); let hd34 : Expr := (.sequenceSpread (hd33)); let hd35 : Expr := (.sequenceSpread (hd34)); let hd36 : Expr := (.sequenceSpread (hd35)); let hd37 : Expr := (.sequenceSpread (hd36)); let hd38 : Expr := (.sequenceSpread (hd37)); let hd39 : Expr := (.sequenceSpread (hd38)); let hd40 : Expr := (.sequenceSpread (hd39)); let hd41 : Expr := (.sequenceSpread (hd40)); let hd42 : Expr := (.sequenceSpread (hd41)); let hd43 : Expr := (.sequenceSpread (hd42)); let hd44 : Expr := (.sequenceSpread (hd43)); let hd45 : Expr := (.sequenceSpread (hd44)); let hd46 : Expr := (.sequenceSpread (hd45)); let hd47 : Expr := (.sequenceSpread (hd46)); let hd48 : Expr := (.sequenceSpread (hd47)); let hd49 : Expr := (.sequenceSpread (hd48)); let hd50 : Expr := (.sequenceSpread (hd49)); let hd51 : Expr := (.sequenceSpread (hd50)); let hd52 : Expr := (.sequenceSpread (hd51)); let hd53 : Expr := (.sequenceSpread (hd52)); let hd54 : Expr := (.sequenceSpread (hd53)); let hd55 : Expr := (.sequenceSpread (hd54)); let hd56 : Expr := (.sequenceSpread (hd55)); let hd57 : Expr := (.sequenceSpread (hd56)); let hd58 : Expr := (.sequenceSpread (hd57)); let hd59 : Expr := (.sequenceSpread (hd58)); let hd60 : Expr := (.sequenceSpread (hd59)); let hd61 : Expr := (.sequenceSpread (hd60)); let hd62 : Expr := (.sequenceSpread (hd61)); let hd63 : Expr := (.sequenceSpread (hd62)); let hd64 : Expr := (.sequenceSpread (hd63)); let hd65 : Expr := (.sequenceSpread (hd64)); let hd66 : Expr := (.sequenceSpread (hd65)); let hd67 : Expr := (.sequenceSpread (hd66)); let hd68 : Expr := (.sequenceSpread (hd67)); let hd69 : Expr := (.sequenceSpread (hd68)); let hd70 : Expr := (.sequenceSpread (hd69)); let hd71 : Expr := (.sequenceSpread (hd70)); let hd72 : Expr := (.sequenceSpread (hd71)); let hd73 : Expr := (.sequenceSpread (hd72)); let hd74 : Expr := (.sequenceSpread (hd73)); let hd75 : Expr := (.sequenceSpread (hd74)); let hd76 : Expr := (.sequenceSpread (hd75)); let hd77 : Expr := (.sequenceSpread (hd76)); let hd78 : Expr := (.sequenceSpread (hd77)); let hd79 : Expr := (.sequenceSpread (hd78)); let hd80 : Expr := (.sequenceSpread (hd79)); let hd81 : Expr := (.sequenceSpread (hd80)); let hd82 : Expr := (.sequenceSpread (hd81)); let hd83 : Expr := (.sequenceSpread (hd82)); let hd84 : Expr := (.sequenceSpread (hd83)); let hd85 : Expr := (.sequenceSpread (hd84)); let hd86 : Expr := (.sequenceSpread (hd85)); let hd87 : Expr := (.sequenceSpread (hd86)); let hd88 : Expr := (.sequenceSpread (hd87)); let hd89 : Expr := (.sequenceSpread (hd88)); let hd90 : Expr := (.sequenceSpread (hd89)); let hd91 : Expr := (.sequenceSpread (hd90)); let hd92 : Expr := (.sequenceSpread (hd91)); let hd93 : Expr := (.sequenceSpread (hd92)); let hd94 : Expr := (.sequenceSpread (hd93)); let hd95 : Expr := (.sequenceSpread (hd94)); let hd96 : Expr := (.sequenceSpread (hd95)); let hd97 : Expr := (.sequenceSpread (hd96)); let hd98 : Expr := (.sequenceSpread (hd97)); let hd99 : Expr := (.sequenceSpread (hd98)); let hd100 : Expr := (.sequenceSpread (hd99)); let hd101 : Expr := (.sequenceSpread (hd100)); let hd102 : Expr := (.sequenceSpread (hd101)); let hd103 : Expr := (.sequenceSpread (hd102)); let hd104 : Expr := (.sequenceSpread (hd103)); let hd105 : Expr := (.sequenceSpread (hd104)); let hd106 : Expr := (.sequenceSpread (hd105)); let hd107 : Expr := (.sequenceSpread (hd106)); let hd108 : Expr := (.sequenceSpread (hd107)); let hd109 : Expr := (.sequenceSpread (hd108)); let hd110 : Expr := (.sequenceSpread (hd109)); let hd111 : Expr := (.sequenceSpread (hd110)); let hd112 : Expr := (.sequenceSpread (hd111)); let hd113 : Expr := (.sequenceSpread (hd112)); let hd114 : Expr := (.sequenceSpread (hd113)); let hd115 : Expr := (.sequenceSpread (hd114)); let hd116 : Expr := (.sequenceSpread (hd115)); let hd117 : Expr := (.sequenceSpread (hd116)); let hd118 : Expr := (.sequenceSpread (hd117)); let hd119 : Expr := (.sequenceSpread (hd118)); let hd120 : Expr := (.sequenceSpread (hd119)); let hd121 : Expr := (.sequenceSpread (hd120)); let hd122 : Expr := (.sequenceSpread (hd121)); let hd123 : Expr := (.sequenceSpread (hd122)); let hd124 : Expr := (.sequenceSpread (hd123)); let hd125 : Expr := (.sequenceSpread (hd124)); let hd126 : Expr := (.sequenceSpread (hd125)); let hd127 : Expr := (.sequenceSpread (hd126)); let hd128 : Expr := (.sequenceSpread (hd127)); let hd129 : Expr := (.sequenceSpread (hd128)); let hd130 : Expr := (.sequenceSpread (hd129)); let hd131 : Expr := (.sequenceSpread (hd130)); let hd132 : Expr := (.sequenceSpread (hd131)); let hd133 : Expr := (.sequenceSpread (hd132)); let hd134 : Expr := (.sequenceSpread (hd133)); let hd135 : Expr := (.sequenceSpread (hd134)); let hd136 : Expr := (.sequenceSpread (hd135)); let hd137 : Expr := (.sequenceSpread (hd136)); let hd138 : Expr := (.sequenceSpread (hd137)); let hd139 : Expr := (.sequenceSpread (hd138)); let hd140 : Expr := (.sequenceSpread (hd139)); let hd141 : Expr := (.sequenceSpread (hd140)); let hd142 : Expr := (.sequenceSpread (hd141)); let hd143 : Expr := (.sequenceSpread (hd142)); let hd144 : Expr := (.sequenceSpread (hd143)); let hd145 : Expr := (.sequenceSpread (hd144)); let hd146 : Expr := (.sequenceSpread (hd145)); let hd147 : Expr := (.sequenceSpread (hd146)); let hd148 : Expr := (.sequenceSpread (hd147)); let hd149 : Expr := (.sequenceSpread (hd148)); let hd150 : Expr := (.sequenceSpread (hd149)); let hd151 : Expr := (.sequenceSpread (hd150)); let hd152 : Expr := (.sequenceSpread (hd151)); let hd153 : Expr := (.sequenceSpread (hd152)); let hd154 : Expr := (.sequenceSpread (hd153)); let hd155 : Expr := (.sequenceSpread (hd154)); let hd156 : Expr := (.sequenceSpread (hd155)); let hd157 : Expr := (.sequenceSpread (hd156)); let hd158 : Expr := (.sequenceSpread (hd157)); let hd159 : Expr := (.sequenceSpread (hd158)); let hd160 : Expr := (.sequenceSpread (hd159)); let hd161 : Expr := (.sequenceSpread (hd160)); let hd162 : Expr := (.sequenceSpread (hd161)); let hd163 : Expr := (.sequenceSpread (hd162)); let hd164 : Expr := (.sequenceSpread (hd163)); let hd165 : Expr := (.sequenceSpread (hd164)); let hd166 : Expr := (.sequenceSpread (hd165)); let hd167 : Expr := (.sequenceSpread (hd166)); let hd168 : Expr := (.sequenceSpread (hd167)); let hd169 : Expr := (.sequenceSpread (hd168)); let hd170 : Expr := (.sequenceSpread (hd169)); let hd171 : Expr := (.sequenceSpread (hd170)); let hd172 : Expr := (.sequenceSpread (hd171)); let hd173 : Expr := (.sequenceSpread (hd172)); let hd174 : Expr := (.sequenceSpread (hd173)); let hd175 : Expr := (.sequenceSpread (hd174)); let hd176 : Expr := (.sequenceSpread (hd175)); let hd177 : Expr := (.sequenceSpread (hd176)); let hd178 : Expr := (.sequenceSpread (hd177)); let hd179 : Expr := (.sequenceSpread (hd178)); let hd180 : Expr := (.sequenceSpread (hd179)); let hd181 : Expr := (.sequenceSpread (hd180)); let hd182 : Expr := (.sequenceSpread (hd181)); let hd183 : Expr := (.sequenceSpread (hd182)); let hd184 : Expr := (.sequenceSpread (hd183)); let hd185 : Expr := (.sequenceSpread (hd184)); let hd186 : Expr := (.sequenceSpread (hd185)); let hd187 : Expr := (.sequenceSpread (hd186)); let hd188 : Expr := (.sequenceSpread (hd187)); let hd189 : Expr := (.sequenceSpread (hd188)); let hd190 : Expr := (.sequenceSpread (hd189)); let hd191 : Expr := (.sequenceSpread (hd190)); let hd192 : Expr := (.sequenceSpread (hd191)); let hd193 : Expr := (.sequenceSpread (hd192)); let hd194 : Expr := (.sequenceSpread (hd193)); let hd195 : Expr := (.sequenceSpread (hd194)); let hd196 : Expr := (.sequenceSpread (hd195)); let hd197 : Expr := (.sequenceSpread (hd196)); let hd198 : Expr := (.sequenceSpread (hd197)); let hd199 : Expr := (.sequenceSpread (hd198)); let hd200 : Expr := (.sequenceSpread (hd199)); let hd201 : Expr := (.sequenceSpread (hd200)); let hd202 : Expr := (.sequenceSpread (hd201)); let hd203 : Expr := (.sequenceSpread (hd202)); let hd204 : Expr := (.sequenceSpread (hd203)); let hd205 : Expr := (.sequenceSpread (hd204)); let hd206 : Expr := (.sequenceSpread (hd205)); let hd207 : Expr := (.sequenceSpread (hd206)); let hd208 : Expr := (.sequenceSpread (hd207)); let hd209 : Expr := (.sequenceSpread (hd208)); let hd210 : Expr := (.sequenceSpread (hd209)); let hd211 : Expr := (.sequenceSpread (hd210)); let hd212 : Expr := (.sequenceSpread (hd211)); let hd213 : Expr := (.sequenceSpread (hd212)); let hd214 : Expr := (.sequenceSpread (hd213)); let hd215 : Expr := (.sequenceSpread (hd214)); let hd216 : Expr := (.sequenceSpread (hd215)); let hd217 : Expr := (.sequenceSpread (hd216)); let hd218 : Expr := (.sequenceSpread (hd217)); let hd219 : Expr := (.sequenceSpread (hd218)); let hd220 : Expr := (.sequenceSpread (hd219)); let hd221 : Expr := (.sequenceSpread (hd220)); let hd222 : Expr := (.sequenceSpread (hd221)); let hd223 : Expr := (.sequenceSpread (hd222)); let hd224 : Expr := (.sequenceSpread (hd223)); let hd225 : Expr := (.sequenceSpread (hd224)); let hd226 : Expr := (.sequenceSpread (hd225)); let hd227 : Expr := (.sequenceSpread (hd226)); let hd228 : Expr := (.sequenceSpread (hd227)); let hd229 : Expr := (.sequenceSpread (hd228)); let hd230 : Expr := (.sequenceSpread (hd229)); let hd231 : Expr := (.sequenceSpread (hd230)); let hd232 : Expr := (.sequenceSpread (hd231)); let hd233 : Expr := (.sequenceSpread (hd232)); let hd234 : Expr := (.sequenceSpread (hd233)); let hd235 : Expr := (.sequenceSpread (hd234)); let hd236 : Expr := (.sequenceSpread (hd235)); let hd237 : Expr := (.sequenceSpread (hd236)); let hd238 : Expr := (.sequenceSpread (hd237)); let hd239 : Expr := (.sequenceSpread (hd238)); let hd240 : Expr := (.sequenceSpread (hd239)); let hd241 : Expr := (.sequenceSpread (hd240)); let hd242 : Expr := (.sequenceSpread (hd241)); let hd243 : Expr := (.sequenceSpread (hd242)); let hd244 : Expr := (.sequenceSpread (hd243)); let hd245 : Expr := (.sequenceSpread (hd244)); let hd246 : Expr := (.sequenceSpread (hd245)); let hd247 : Expr := (.sequenceSpread (hd246)); let hd248 : Expr := (.sequenceSpread (hd247)); let hd249 : Expr := (.sequenceSpread (hd248)); let hd250 : Expr := (.sequenceSpread (hd249)); let hd251 : Expr := (.sequenceSpread (hd250)); let hd252 : Expr := (.sequenceSpread (hd251)); let hd253 : Expr := (.sequenceSpread (hd252)); let hd254 : Expr := (.sequenceSpread (hd253)); let hd255 : Expr := (.sequenceSpread (hd254)); let hd256 : Expr := (.sequenceSpread (hd255)); let hd257 : Expr := (.sequenceSpread (hd256)); let hd258 : Expr := (.sequenceSpread (hd257)); let hd259 : Expr := (.sequenceSpread (hd258)); let hd260 : Expr := (.sequenceSpread (hd259)); let hd261 : Expr := (.sequenceSpread (hd260)); let hd262 : Expr := (.sequenceSpread (hd261)); let hd263 : Expr := (.sequenceSpread (hd262)); let hd264 : Expr := (.sequenceSpread (hd263)); let hd265 : Expr := (.sequenceSpread (hd264)); let hd266 : Expr := (.sequenceSpread (hd265)); let hd267 : Expr := (.sequenceSpread (hd266)); let hd268 : Expr := (.sequenceSpread (hd267)); let hd269 : Expr := (.sequenceSpread (hd268)); let hd270 : Expr := (.sequenceSpread (hd269)); let hd271 : Expr := (.sequenceSpread (hd270)); let hd272 : Expr := (.sequenceSpread (hd271)); let hd273 : Expr := (.sequenceSpread (hd272)); let hd274 : Expr := (.sequenceSpread (hd273)); let hd275 : Expr := (.sequenceSpread (hd274)); let hd276 : Expr := (.sequenceSpread (hd275)); let hd277 : Expr := (.sequenceSpread (hd276)); let hd278 : Expr := (.sequenceSpread (hd277)); let hd279 : Expr := (.sequenceSpread (hd278)); let hd280 : Expr := (.sequenceSpread (hd279)); let hd281 : Expr := (.sequenceSpread (hd280)); let hd282 : Expr := (.sequenceSpread (hd281)); let hd283 : Expr := (.sequenceSpread (hd282)); let hd284 : Expr := (.sequenceSpread (hd283)); let hd285 : Expr := (.sequenceSpread (hd284)); let hd286 : Expr := (.sequenceSpread (hd285)); let hd287 : Expr := (.sequenceSpread (hd286)); let hd288 : Expr := (.sequenceSpread (hd287)); let hd289 : Expr := (.sequenceSpread (hd288)); let hd290 : Expr := (.sequenceSpread (hd289)); let hd291 : Expr := (.sequenceSpread (hd290)); let hd292 : Expr := (.sequenceSpread (hd291)); let hd293 : Expr := (.sequenceSpread (hd292)); let hd294 : Expr := (.sequenceSpread (hd293)); let hd295 : Expr := (.sequenceSpread (hd294)); let hd296 : Expr := (.sequenceSpread (hd295)); let hd297 : Expr := (.sequenceSpread (hd296)); let hd298 : Expr := (.sequenceSpread (hd297)); let hd299 : Expr := (.sequenceSpread (hd298)); let hd300 : Expr := (.sequenceSpread (hd299)); let hd301 : Expr := (.sequenceSpread (hd300)); let hd302 : Expr := (.sequenceSpread (hd301)); let hd303 : Expr := (.sequenceSpread (hd302)); let hd304 : Algorithm := (alg [] [] [] [hd303]); let hd305 : ScopeCtx := (ScopeCtx.mk none [] [] [privateProp "P" hd304] [] [] none (some (.host 0))); let hd306 : Algorithm := (Algorithm.withParent (some hd305) (alg [] [] [publicProp "Run" hd1] [])); let hd307 : Expr := (.algorithmExpr hd306); let hd308 : Expr := .resolve "Run"; let hd309 : Algorithm := (alg [] [hd307] [] [hd308]); let hd310 : Expr := (.algorithmExpr hd309); hd310)
#guard obs hp_10h == "ok raw=1 n=1"
#guard structural hp_10h == some "kl-struct-v1:1:n3:1e0"
#guard cacheEntries hp_10h "P" == some 1
#guard cacheEntries hp_10h "Run" == some 1
#guard cacheTotal hp_10h == some 2

-- HP-10i: an evaluator-accepted join spine preserves the non-spread empty-leaf rule
def hp_10i : Expr :=
  (let hd0 : Expr := .resolve "P"; let hd1 : Algorithm := (alg [] [] [] [hd0]); let hd2 : Expr := .num 1; let hd3 : Expr := (.emptySequence 0); let hd4 : Expr := (.sequenceConstruct (hd2) (hd3)); let hd5 : Expr := (.emptySequence 0); let hd6 : Expr := (.sequenceConstruct (hd4) (hd5)); let hd7 : Expr := (.emptySequence 0); let hd8 : Expr := (.sequenceConstruct (hd6) (hd7)); let hd9 : Expr := (.emptySequence 0); let hd10 : Expr := (.sequenceConstruct (hd8) (hd9)); let hd11 : Expr := (.emptySequence 0); let hd12 : Expr := (.sequenceConstruct (hd10) (hd11)); let hd13 : Expr := (.emptySequence 0); let hd14 : Expr := (.sequenceConstruct (hd12) (hd13)); let hd15 : Expr := (.emptySequence 0); let hd16 : Expr := (.sequenceConstruct (hd14) (hd15)); let hd17 : Expr := (.emptySequence 0); let hd18 : Expr := (.sequenceConstruct (hd16) (hd17)); let hd19 : Expr := (.emptySequence 0); let hd20 : Expr := (.sequenceConstruct (hd18) (hd19)); let hd21 : Expr := (.emptySequence 0); let hd22 : Expr := (.sequenceConstruct (hd20) (hd21)); let hd23 : Expr := (.emptySequence 0); let hd24 : Expr := (.sequenceConstruct (hd22) (hd23)); let hd25 : Expr := (.emptySequence 0); let hd26 : Expr := (.sequenceConstruct (hd24) (hd25)); let hd27 : Expr := (.emptySequence 0); let hd28 : Expr := (.sequenceConstruct (hd26) (hd27)); let hd29 : Expr := (.emptySequence 0); let hd30 : Expr := (.sequenceConstruct (hd28) (hd29)); let hd31 : Expr := (.emptySequence 0); let hd32 : Expr := (.sequenceConstruct (hd30) (hd31)); let hd33 : Expr := (.emptySequence 0); let hd34 : Expr := (.sequenceConstruct (hd32) (hd33)); let hd35 : Expr := (.emptySequence 0); let hd36 : Expr := (.sequenceConstruct (hd34) (hd35)); let hd37 : Expr := (.emptySequence 0); let hd38 : Expr := (.sequenceConstruct (hd36) (hd37)); let hd39 : Expr := (.emptySequence 0); let hd40 : Expr := (.sequenceConstruct (hd38) (hd39)); let hd41 : Expr := (.emptySequence 0); let hd42 : Expr := (.sequenceConstruct (hd40) (hd41)); let hd43 : Expr := (.emptySequence 0); let hd44 : Expr := (.sequenceConstruct (hd42) (hd43)); let hd45 : Expr := (.emptySequence 0); let hd46 : Expr := (.sequenceConstruct (hd44) (hd45)); let hd47 : Expr := (.emptySequence 0); let hd48 : Expr := (.sequenceConstruct (hd46) (hd47)); let hd49 : Expr := (.emptySequence 0); let hd50 : Expr := (.sequenceConstruct (hd48) (hd49)); let hd51 : Expr := (.emptySequence 0); let hd52 : Expr := (.sequenceConstruct (hd50) (hd51)); let hd53 : Expr := (.emptySequence 0); let hd54 : Expr := (.sequenceConstruct (hd52) (hd53)); let hd55 : Expr := (.emptySequence 0); let hd56 : Expr := (.sequenceConstruct (hd54) (hd55)); let hd57 : Expr := (.emptySequence 0); let hd58 : Expr := (.sequenceConstruct (hd56) (hd57)); let hd59 : Expr := (.emptySequence 0); let hd60 : Expr := (.sequenceConstruct (hd58) (hd59)); let hd61 : Expr := (.emptySequence 0); let hd62 : Expr := (.sequenceConstruct (hd60) (hd61)); let hd63 : Expr := (.emptySequence 0); let hd64 : Expr := (.sequenceConstruct (hd62) (hd63)); let hd65 : Expr := (.emptySequence 0); let hd66 : Expr := (.sequenceConstruct (hd64) (hd65)); let hd67 : Expr := (.emptySequence 0); let hd68 : Expr := (.sequenceConstruct (hd66) (hd67)); let hd69 : Expr := (.emptySequence 0); let hd70 : Expr := (.sequenceConstruct (hd68) (hd69)); let hd71 : Expr := (.emptySequence 0); let hd72 : Expr := (.sequenceConstruct (hd70) (hd71)); let hd73 : Expr := (.emptySequence 0); let hd74 : Expr := (.sequenceConstruct (hd72) (hd73)); let hd75 : Expr := (.emptySequence 0); let hd76 : Expr := (.sequenceConstruct (hd74) (hd75)); let hd77 : Expr := (.emptySequence 0); let hd78 : Expr := (.sequenceConstruct (hd76) (hd77)); let hd79 : Expr := (.emptySequence 0); let hd80 : Expr := (.sequenceConstruct (hd78) (hd79)); let hd81 : Expr := (.emptySequence 0); let hd82 : Expr := (.sequenceConstruct (hd80) (hd81)); let hd83 : Expr := (.emptySequence 0); let hd84 : Expr := (.sequenceConstruct (hd82) (hd83)); let hd85 : Expr := (.emptySequence 0); let hd86 : Expr := (.sequenceConstruct (hd84) (hd85)); let hd87 : Expr := (.emptySequence 0); let hd88 : Expr := (.sequenceConstruct (hd86) (hd87)); let hd89 : Expr := (.emptySequence 0); let hd90 : Expr := (.sequenceConstruct (hd88) (hd89)); let hd91 : Expr := (.emptySequence 0); let hd92 : Expr := (.sequenceConstruct (hd90) (hd91)); let hd93 : Expr := (.emptySequence 0); let hd94 : Expr := (.sequenceConstruct (hd92) (hd93)); let hd95 : Expr := (.emptySequence 0); let hd96 : Expr := (.sequenceConstruct (hd94) (hd95)); let hd97 : Expr := (.emptySequence 0); let hd98 : Expr := (.sequenceConstruct (hd96) (hd97)); let hd99 : Expr := (.emptySequence 0); let hd100 : Expr := (.sequenceConstruct (hd98) (hd99)); let hd101 : Expr := (.emptySequence 0); let hd102 : Expr := (.sequenceConstruct (hd100) (hd101)); let hd103 : Expr := (.emptySequence 0); let hd104 : Expr := (.sequenceConstruct (hd102) (hd103)); let hd105 : Expr := (.emptySequence 0); let hd106 : Expr := (.sequenceConstruct (hd104) (hd105)); let hd107 : Expr := (.emptySequence 0); let hd108 : Expr := (.sequenceConstruct (hd106) (hd107)); let hd109 : Expr := (.emptySequence 0); let hd110 : Expr := (.sequenceConstruct (hd108) (hd109)); let hd111 : Expr := (.emptySequence 0); let hd112 : Expr := (.sequenceConstruct (hd110) (hd111)); let hd113 : Expr := (.emptySequence 0); let hd114 : Expr := (.sequenceConstruct (hd112) (hd113)); let hd115 : Expr := (.emptySequence 0); let hd116 : Expr := (.sequenceConstruct (hd114) (hd115)); let hd117 : Expr := (.emptySequence 0); let hd118 : Expr := (.sequenceConstruct (hd116) (hd117)); let hd119 : Expr := (.emptySequence 0); let hd120 : Expr := (.sequenceConstruct (hd118) (hd119)); let hd121 : Expr := (.emptySequence 0); let hd122 : Expr := (.sequenceConstruct (hd120) (hd121)); let hd123 : Expr := (.emptySequence 0); let hd124 : Expr := (.sequenceConstruct (hd122) (hd123)); let hd125 : Expr := (.emptySequence 0); let hd126 : Expr := (.sequenceConstruct (hd124) (hd125)); let hd127 : Expr := (.emptySequence 0); let hd128 : Expr := (.sequenceConstruct (hd126) (hd127)); let hd129 : Expr := (.emptySequence 0); let hd130 : Expr := (.sequenceConstruct (hd128) (hd129)); let hd131 : Expr := (.emptySequence 0); let hd132 : Expr := (.sequenceConstruct (hd130) (hd131)); let hd133 : Expr := (.emptySequence 0); let hd134 : Expr := (.sequenceConstruct (hd132) (hd133)); let hd135 : Expr := (.emptySequence 0); let hd136 : Expr := (.sequenceConstruct (hd134) (hd135)); let hd137 : Expr := (.emptySequence 0); let hd138 : Expr := (.sequenceConstruct (hd136) (hd137)); let hd139 : Expr := (.emptySequence 0); let hd140 : Expr := (.sequenceConstruct (hd138) (hd139)); let hd141 : Expr := (.emptySequence 0); let hd142 : Expr := (.sequenceConstruct (hd140) (hd141)); let hd143 : Expr := (.emptySequence 0); let hd144 : Expr := (.sequenceConstruct (hd142) (hd143)); let hd145 : Expr := (.emptySequence 0); let hd146 : Expr := (.sequenceConstruct (hd144) (hd145)); let hd147 : Expr := (.emptySequence 0); let hd148 : Expr := (.sequenceConstruct (hd146) (hd147)); let hd149 : Expr := (.emptySequence 0); let hd150 : Expr := (.sequenceConstruct (hd148) (hd149)); let hd151 : Expr := (.emptySequence 0); let hd152 : Expr := (.sequenceConstruct (hd150) (hd151)); let hd153 : Expr := (.emptySequence 0); let hd154 : Expr := (.sequenceConstruct (hd152) (hd153)); let hd155 : Expr := (.emptySequence 0); let hd156 : Expr := (.sequenceConstruct (hd154) (hd155)); let hd157 : Expr := (.emptySequence 0); let hd158 : Expr := (.sequenceConstruct (hd156) (hd157)); let hd159 : Expr := (.emptySequence 0); let hd160 : Expr := (.sequenceConstruct (hd158) (hd159)); let hd161 : Expr := (.emptySequence 0); let hd162 : Expr := (.sequenceConstruct (hd160) (hd161)); let hd163 : Expr := (.emptySequence 0); let hd164 : Expr := (.sequenceConstruct (hd162) (hd163)); let hd165 : Expr := (.emptySequence 0); let hd166 : Expr := (.sequenceConstruct (hd164) (hd165)); let hd167 : Expr := (.emptySequence 0); let hd168 : Expr := (.sequenceConstruct (hd166) (hd167)); let hd169 : Expr := (.emptySequence 0); let hd170 : Expr := (.sequenceConstruct (hd168) (hd169)); let hd171 : Expr := (.emptySequence 0); let hd172 : Expr := (.sequenceConstruct (hd170) (hd171)); let hd173 : Expr := (.emptySequence 0); let hd174 : Expr := (.sequenceConstruct (hd172) (hd173)); let hd175 : Expr := (.emptySequence 0); let hd176 : Expr := (.sequenceConstruct (hd174) (hd175)); let hd177 : Expr := (.emptySequence 0); let hd178 : Expr := (.sequenceConstruct (hd176) (hd177)); let hd179 : Expr := (.emptySequence 0); let hd180 : Expr := (.sequenceConstruct (hd178) (hd179)); let hd181 : Expr := (.emptySequence 0); let hd182 : Expr := (.sequenceConstruct (hd180) (hd181)); let hd183 : Expr := (.emptySequence 0); let hd184 : Expr := (.sequenceConstruct (hd182) (hd183)); let hd185 : Expr := (.emptySequence 0); let hd186 : Expr := (.sequenceConstruct (hd184) (hd185)); let hd187 : Expr := (.emptySequence 0); let hd188 : Expr := (.sequenceConstruct (hd186) (hd187)); let hd189 : Expr := (.emptySequence 0); let hd190 : Expr := (.sequenceConstruct (hd188) (hd189)); let hd191 : Expr := (.emptySequence 0); let hd192 : Expr := (.sequenceConstruct (hd190) (hd191)); let hd193 : Expr := (.emptySequence 0); let hd194 : Expr := (.sequenceConstruct (hd192) (hd193)); let hd195 : Expr := (.emptySequence 0); let hd196 : Expr := (.sequenceConstruct (hd194) (hd195)); let hd197 : Expr := (.emptySequence 0); let hd198 : Expr := (.sequenceConstruct (hd196) (hd197)); let hd199 : Expr := (.emptySequence 0); let hd200 : Expr := (.sequenceConstruct (hd198) (hd199)); let hd201 : Expr := (.emptySequence 0); let hd202 : Expr := (.sequenceConstruct (hd200) (hd201)); let hd203 : Expr := (.emptySequence 0); let hd204 : Expr := (.sequenceConstruct (hd202) (hd203)); let hd205 : Expr := (.emptySequence 0); let hd206 : Expr := (.sequenceConstruct (hd204) (hd205)); let hd207 : Expr := (.emptySequence 0); let hd208 : Expr := (.sequenceConstruct (hd206) (hd207)); let hd209 : Expr := (.emptySequence 0); let hd210 : Expr := (.sequenceConstruct (hd208) (hd209)); let hd211 : Expr := (.emptySequence 0); let hd212 : Expr := (.sequenceConstruct (hd210) (hd211)); let hd213 : Expr := (.emptySequence 0); let hd214 : Expr := (.sequenceConstruct (hd212) (hd213)); let hd215 : Expr := (.emptySequence 0); let hd216 : Expr := (.sequenceConstruct (hd214) (hd215)); let hd217 : Expr := (.emptySequence 0); let hd218 : Expr := (.sequenceConstruct (hd216) (hd217)); let hd219 : Expr := (.emptySequence 0); let hd220 : Expr := (.sequenceConstruct (hd218) (hd219)); let hd221 : Expr := (.emptySequence 0); let hd222 : Expr := (.sequenceConstruct (hd220) (hd221)); let hd223 : Expr := (.emptySequence 0); let hd224 : Expr := (.sequenceConstruct (hd222) (hd223)); let hd225 : Expr := (.emptySequence 0); let hd226 : Expr := (.sequenceConstruct (hd224) (hd225)); let hd227 : Expr := (.emptySequence 0); let hd228 : Expr := (.sequenceConstruct (hd226) (hd227)); let hd229 : Expr := (.emptySequence 0); let hd230 : Expr := (.sequenceConstruct (hd228) (hd229)); let hd231 : Expr := (.emptySequence 0); let hd232 : Expr := (.sequenceConstruct (hd230) (hd231)); let hd233 : Expr := (.emptySequence 0); let hd234 : Expr := (.sequenceConstruct (hd232) (hd233)); let hd235 : Expr := (.emptySequence 0); let hd236 : Expr := (.sequenceConstruct (hd234) (hd235)); let hd237 : Expr := (.emptySequence 0); let hd238 : Expr := (.sequenceConstruct (hd236) (hd237)); let hd239 : Expr := (.emptySequence 0); let hd240 : Expr := (.sequenceConstruct (hd238) (hd239)); let hd241 : Expr := (.emptySequence 0); let hd242 : Expr := (.sequenceConstruct (hd240) (hd241)); let hd243 : Expr := (.emptySequence 0); let hd244 : Expr := (.sequenceConstruct (hd242) (hd243)); let hd245 : Expr := (.emptySequence 0); let hd246 : Expr := (.sequenceConstruct (hd244) (hd245)); let hd247 : Expr := (.emptySequence 0); let hd248 : Expr := (.sequenceConstruct (hd246) (hd247)); let hd249 : Expr := (.emptySequence 0); let hd250 : Expr := (.sequenceConstruct (hd248) (hd249)); let hd251 : Expr := (.emptySequence 0); let hd252 : Expr := (.sequenceConstruct (hd250) (hd251)); let hd253 : Expr := (.emptySequence 0); let hd254 : Expr := (.sequenceConstruct (hd252) (hd253)); let hd255 : Expr := (.emptySequence 0); let hd256 : Expr := (.sequenceConstruct (hd254) (hd255)); let hd257 : Expr := (.emptySequence 0); let hd258 : Expr := (.sequenceConstruct (hd256) (hd257)); let hd259 : Expr := (.emptySequence 0); let hd260 : Expr := (.sequenceConstruct (hd258) (hd259)); let hd261 : Expr := (.emptySequence 0); let hd262 : Expr := (.sequenceConstruct (hd260) (hd261)); let hd263 : Expr := (.emptySequence 0); let hd264 : Expr := (.sequenceConstruct (hd262) (hd263)); let hd265 : Expr := (.emptySequence 0); let hd266 : Expr := (.sequenceConstruct (hd264) (hd265)); let hd267 : Expr := (.emptySequence 0); let hd268 : Expr := (.sequenceConstruct (hd266) (hd267)); let hd269 : Expr := (.emptySequence 0); let hd270 : Expr := (.sequenceConstruct (hd268) (hd269)); let hd271 : Expr := (.emptySequence 0); let hd272 : Expr := (.sequenceConstruct (hd270) (hd271)); let hd273 : Expr := (.emptySequence 0); let hd274 : Expr := (.sequenceConstruct (hd272) (hd273)); let hd275 : Expr := (.emptySequence 0); let hd276 : Expr := (.sequenceConstruct (hd274) (hd275)); let hd277 : Expr := (.emptySequence 0); let hd278 : Expr := (.sequenceConstruct (hd276) (hd277)); let hd279 : Expr := (.emptySequence 0); let hd280 : Expr := (.sequenceConstruct (hd278) (hd279)); let hd281 : Expr := (.emptySequence 0); let hd282 : Expr := (.sequenceConstruct (hd280) (hd281)); let hd283 : Expr := (.emptySequence 0); let hd284 : Expr := (.sequenceConstruct (hd282) (hd283)); let hd285 : Expr := (.emptySequence 0); let hd286 : Expr := (.sequenceConstruct (hd284) (hd285)); let hd287 : Expr := (.emptySequence 0); let hd288 : Expr := (.sequenceConstruct (hd286) (hd287)); let hd289 : Expr := (.emptySequence 0); let hd290 : Expr := (.sequenceConstruct (hd288) (hd289)); let hd291 : Expr := (.emptySequence 0); let hd292 : Expr := (.sequenceConstruct (hd290) (hd291)); let hd293 : Expr := (.emptySequence 0); let hd294 : Expr := (.sequenceConstruct (hd292) (hd293)); let hd295 : Expr := (.emptySequence 0); let hd296 : Expr := (.sequenceConstruct (hd294) (hd295)); let hd297 : Expr := (.emptySequence 0); let hd298 : Expr := (.sequenceConstruct (hd296) (hd297)); let hd299 : Expr := (.emptySequence 0); let hd300 : Expr := (.sequenceConstruct (hd298) (hd299)); let hd301 : Expr := (.emptySequence 0); let hd302 : Expr := (.sequenceConstruct (hd300) (hd301)); let hd303 : Expr := (.emptySequence 0); let hd304 : Expr := (.sequenceConstruct (hd302) (hd303)); let hd305 : Expr := (.emptySequence 0); let hd306 : Expr := (.sequenceConstruct (hd304) (hd305)); let hd307 : Expr := (.emptySequence 0); let hd308 : Expr := (.sequenceConstruct (hd306) (hd307)); let hd309 : Expr := (.emptySequence 0); let hd310 : Expr := (.sequenceConstruct (hd308) (hd309)); let hd311 : Expr := (.emptySequence 0); let hd312 : Expr := (.sequenceConstruct (hd310) (hd311)); let hd313 : Expr := (.emptySequence 0); let hd314 : Expr := (.sequenceConstruct (hd312) (hd313)); let hd315 : Expr := (.emptySequence 0); let hd316 : Expr := (.sequenceConstruct (hd314) (hd315)); let hd317 : Expr := (.emptySequence 0); let hd318 : Expr := (.sequenceConstruct (hd316) (hd317)); let hd319 : Expr := (.emptySequence 0); let hd320 : Expr := (.sequenceConstruct (hd318) (hd319)); let hd321 : Expr := (.emptySequence 0); let hd322 : Expr := (.sequenceConstruct (hd320) (hd321)); let hd323 : Expr := (.emptySequence 0); let hd324 : Expr := (.sequenceConstruct (hd322) (hd323)); let hd325 : Expr := (.emptySequence 0); let hd326 : Expr := (.sequenceConstruct (hd324) (hd325)); let hd327 : Expr := (.emptySequence 0); let hd328 : Expr := (.sequenceConstruct (hd326) (hd327)); let hd329 : Expr := (.emptySequence 0); let hd330 : Expr := (.sequenceConstruct (hd328) (hd329)); let hd331 : Expr := (.emptySequence 0); let hd332 : Expr := (.sequenceConstruct (hd330) (hd331)); let hd333 : Expr := (.emptySequence 0); let hd334 : Expr := (.sequenceConstruct (hd332) (hd333)); let hd335 : Expr := (.emptySequence 0); let hd336 : Expr := (.sequenceConstruct (hd334) (hd335)); let hd337 : Expr := (.emptySequence 0); let hd338 : Expr := (.sequenceConstruct (hd336) (hd337)); let hd339 : Expr := (.emptySequence 0); let hd340 : Expr := (.sequenceConstruct (hd338) (hd339)); let hd341 : Expr := (.emptySequence 0); let hd342 : Expr := (.sequenceConstruct (hd340) (hd341)); let hd343 : Expr := (.emptySequence 0); let hd344 : Expr := (.sequenceConstruct (hd342) (hd343)); let hd345 : Expr := (.emptySequence 0); let hd346 : Expr := (.sequenceConstruct (hd344) (hd345)); let hd347 : Expr := (.emptySequence 0); let hd348 : Expr := (.sequenceConstruct (hd346) (hd347)); let hd349 : Expr := (.emptySequence 0); let hd350 : Expr := (.sequenceConstruct (hd348) (hd349)); let hd351 : Expr := (.emptySequence 0); let hd352 : Expr := (.sequenceConstruct (hd350) (hd351)); let hd353 : Expr := (.emptySequence 0); let hd354 : Expr := (.sequenceConstruct (hd352) (hd353)); let hd355 : Expr := (.emptySequence 0); let hd356 : Expr := (.sequenceConstruct (hd354) (hd355)); let hd357 : Expr := (.emptySequence 0); let hd358 : Expr := (.sequenceConstruct (hd356) (hd357)); let hd359 : Expr := (.emptySequence 0); let hd360 : Expr := (.sequenceConstruct (hd358) (hd359)); let hd361 : Expr := (.emptySequence 0); let hd362 : Expr := (.sequenceConstruct (hd360) (hd361)); let hd363 : Expr := (.emptySequence 0); let hd364 : Expr := (.sequenceConstruct (hd362) (hd363)); let hd365 : Expr := (.emptySequence 0); let hd366 : Expr := (.sequenceConstruct (hd364) (hd365)); let hd367 : Expr := (.emptySequence 0); let hd368 : Expr := (.sequenceConstruct (hd366) (hd367)); let hd369 : Expr := (.emptySequence 0); let hd370 : Expr := (.sequenceConstruct (hd368) (hd369)); let hd371 : Expr := (.emptySequence 0); let hd372 : Expr := (.sequenceConstruct (hd370) (hd371)); let hd373 : Expr := (.emptySequence 0); let hd374 : Expr := (.sequenceConstruct (hd372) (hd373)); let hd375 : Expr := (.emptySequence 0); let hd376 : Expr := (.sequenceConstruct (hd374) (hd375)); let hd377 : Expr := (.emptySequence 0); let hd378 : Expr := (.sequenceConstruct (hd376) (hd377)); let hd379 : Expr := (.emptySequence 0); let hd380 : Expr := (.sequenceConstruct (hd378) (hd379)); let hd381 : Expr := (.emptySequence 0); let hd382 : Expr := (.sequenceConstruct (hd380) (hd381)); let hd383 : Expr := (.emptySequence 0); let hd384 : Expr := (.sequenceConstruct (hd382) (hd383)); let hd385 : Expr := (.emptySequence 0); let hd386 : Expr := (.sequenceConstruct (hd384) (hd385)); let hd387 : Expr := (.emptySequence 0); let hd388 : Expr := (.sequenceConstruct (hd386) (hd387)); let hd389 : Expr := (.emptySequence 0); let hd390 : Expr := (.sequenceConstruct (hd388) (hd389)); let hd391 : Expr := (.emptySequence 0); let hd392 : Expr := (.sequenceConstruct (hd390) (hd391)); let hd393 : Expr := (.emptySequence 0); let hd394 : Expr := (.sequenceConstruct (hd392) (hd393)); let hd395 : Expr := (.emptySequence 0); let hd396 : Expr := (.sequenceConstruct (hd394) (hd395)); let hd397 : Expr := (.emptySequence 0); let hd398 : Expr := (.sequenceConstruct (hd396) (hd397)); let hd399 : Expr := (.emptySequence 0); let hd400 : Expr := (.sequenceConstruct (hd398) (hd399)); let hd401 : Expr := (.emptySequence 0); let hd402 : Expr := (.sequenceConstruct (hd400) (hd401)); let hd403 : Expr := (.emptySequence 0); let hd404 : Expr := (.sequenceConstruct (hd402) (hd403)); let hd405 : Expr := (.emptySequence 0); let hd406 : Expr := (.sequenceConstruct (hd404) (hd405)); let hd407 : Expr := (.emptySequence 0); let hd408 : Expr := (.sequenceConstruct (hd406) (hd407)); let hd409 : Expr := (.emptySequence 0); let hd410 : Expr := (.sequenceConstruct (hd408) (hd409)); let hd411 : Expr := (.emptySequence 0); let hd412 : Expr := (.sequenceConstruct (hd410) (hd411)); let hd413 : Expr := (.emptySequence 0); let hd414 : Expr := (.sequenceConstruct (hd412) (hd413)); let hd415 : Expr := (.emptySequence 0); let hd416 : Expr := (.sequenceConstruct (hd414) (hd415)); let hd417 : Expr := (.emptySequence 0); let hd418 : Expr := (.sequenceConstruct (hd416) (hd417)); let hd419 : Expr := (.emptySequence 0); let hd420 : Expr := (.sequenceConstruct (hd418) (hd419)); let hd421 : Expr := (.emptySequence 0); let hd422 : Expr := (.sequenceConstruct (hd420) (hd421)); let hd423 : Expr := (.emptySequence 0); let hd424 : Expr := (.sequenceConstruct (hd422) (hd423)); let hd425 : Expr := (.emptySequence 0); let hd426 : Expr := (.sequenceConstruct (hd424) (hd425)); let hd427 : Expr := (.emptySequence 0); let hd428 : Expr := (.sequenceConstruct (hd426) (hd427)); let hd429 : Expr := (.emptySequence 0); let hd430 : Expr := (.sequenceConstruct (hd428) (hd429)); let hd431 : Expr := (.emptySequence 0); let hd432 : Expr := (.sequenceConstruct (hd430) (hd431)); let hd433 : Expr := (.emptySequence 0); let hd434 : Expr := (.sequenceConstruct (hd432) (hd433)); let hd435 : Expr := (.emptySequence 0); let hd436 : Expr := (.sequenceConstruct (hd434) (hd435)); let hd437 : Expr := (.emptySequence 0); let hd438 : Expr := (.sequenceConstruct (hd436) (hd437)); let hd439 : Expr := (.emptySequence 0); let hd440 : Expr := (.sequenceConstruct (hd438) (hd439)); let hd441 : Expr := (.emptySequence 0); let hd442 : Expr := (.sequenceConstruct (hd440) (hd441)); let hd443 : Expr := (.emptySequence 0); let hd444 : Expr := (.sequenceConstruct (hd442) (hd443)); let hd445 : Expr := (.emptySequence 0); let hd446 : Expr := (.sequenceConstruct (hd444) (hd445)); let hd447 : Expr := (.emptySequence 0); let hd448 : Expr := (.sequenceConstruct (hd446) (hd447)); let hd449 : Expr := (.emptySequence 0); let hd450 : Expr := (.sequenceConstruct (hd448) (hd449)); let hd451 : Expr := (.emptySequence 0); let hd452 : Expr := (.sequenceConstruct (hd450) (hd451)); let hd453 : Expr := (.emptySequence 0); let hd454 : Expr := (.sequenceConstruct (hd452) (hd453)); let hd455 : Expr := (.emptySequence 0); let hd456 : Expr := (.sequenceConstruct (hd454) (hd455)); let hd457 : Expr := (.emptySequence 0); let hd458 : Expr := (.sequenceConstruct (hd456) (hd457)); let hd459 : Expr := (.emptySequence 0); let hd460 : Expr := (.sequenceConstruct (hd458) (hd459)); let hd461 : Expr := (.emptySequence 0); let hd462 : Expr := (.sequenceConstruct (hd460) (hd461)); let hd463 : Expr := (.emptySequence 0); let hd464 : Expr := (.sequenceConstruct (hd462) (hd463)); let hd465 : Expr := (.emptySequence 0); let hd466 : Expr := (.sequenceConstruct (hd464) (hd465)); let hd467 : Expr := (.emptySequence 0); let hd468 : Expr := (.sequenceConstruct (hd466) (hd467)); let hd469 : Expr := (.emptySequence 0); let hd470 : Expr := (.sequenceConstruct (hd468) (hd469)); let hd471 : Expr := (.emptySequence 0); let hd472 : Expr := (.sequenceConstruct (hd470) (hd471)); let hd473 : Expr := (.emptySequence 0); let hd474 : Expr := (.sequenceConstruct (hd472) (hd473)); let hd475 : Expr := (.emptySequence 0); let hd476 : Expr := (.sequenceConstruct (hd474) (hd475)); let hd477 : Expr := (.emptySequence 0); let hd478 : Expr := (.sequenceConstruct (hd476) (hd477)); let hd479 : Expr := (.emptySequence 0); let hd480 : Expr := (.sequenceConstruct (hd478) (hd479)); let hd481 : Expr := (.emptySequence 0); let hd482 : Expr := (.sequenceConstruct (hd480) (hd481)); let hd483 : Expr := (.emptySequence 0); let hd484 : Expr := (.sequenceConstruct (hd482) (hd483)); let hd485 : Expr := (.emptySequence 0); let hd486 : Expr := (.sequenceConstruct (hd484) (hd485)); let hd487 : Expr := (.emptySequence 0); let hd488 : Expr := (.sequenceConstruct (hd486) (hd487)); let hd489 : Expr := (.emptySequence 0); let hd490 : Expr := (.sequenceConstruct (hd488) (hd489)); let hd491 : Expr := (.emptySequence 0); let hd492 : Expr := (.sequenceConstruct (hd490) (hd491)); let hd493 : Expr := (.emptySequence 0); let hd494 : Expr := (.sequenceConstruct (hd492) (hd493)); let hd495 : Expr := (.emptySequence 0); let hd496 : Expr := (.sequenceConstruct (hd494) (hd495)); let hd497 : Expr := (.emptySequence 0); let hd498 : Expr := (.sequenceConstruct (hd496) (hd497)); let hd499 : Expr := (.emptySequence 0); let hd500 : Expr := (.sequenceConstruct (hd498) (hd499)); let hd501 : Expr := (.emptySequence 0); let hd502 : Expr := (.sequenceConstruct (hd500) (hd501)); let hd503 : Expr := (.emptySequence 0); let hd504 : Expr := (.sequenceConstruct (hd502) (hd503)); let hd505 : Expr := (.emptySequence 0); let hd506 : Expr := (.sequenceConstruct (hd504) (hd505)); let hd507 : Expr := (.emptySequence 0); let hd508 : Expr := (.sequenceConstruct (hd506) (hd507)); let hd509 : Expr := (.emptySequence 0); let hd510 : Expr := (.sequenceConstruct (hd508) (hd509)); let hd511 : Expr := (.emptySequence 0); let hd512 : Expr := (.sequenceConstruct (hd510) (hd511)); let hd513 : Expr := (.emptySequence 0); let hd514 : Expr := (.sequenceConstruct (hd512) (hd513)); let hd515 : Expr := (.emptySequence 0); let hd516 : Expr := (.sequenceConstruct (hd514) (hd515)); let hd517 : Expr := (.emptySequence 0); let hd518 : Expr := (.sequenceConstruct (hd516) (hd517)); let hd519 : Expr := (.emptySequence 0); let hd520 : Expr := (.sequenceConstruct (hd518) (hd519)); let hd521 : Expr := (.emptySequence 0); let hd522 : Expr := (.sequenceConstruct (hd520) (hd521)); let hd523 : Expr := (.emptySequence 0); let hd524 : Expr := (.sequenceConstruct (hd522) (hd523)); let hd525 : Expr := (.emptySequence 0); let hd526 : Expr := (.sequenceConstruct (hd524) (hd525)); let hd527 : Expr := (.emptySequence 0); let hd528 : Expr := (.sequenceConstruct (hd526) (hd527)); let hd529 : Expr := (.emptySequence 0); let hd530 : Expr := (.sequenceConstruct (hd528) (hd529)); let hd531 : Expr := (.emptySequence 0); let hd532 : Expr := (.sequenceConstruct (hd530) (hd531)); let hd533 : Expr := (.emptySequence 0); let hd534 : Expr := (.sequenceConstruct (hd532) (hd533)); let hd535 : Expr := (.emptySequence 0); let hd536 : Expr := (.sequenceConstruct (hd534) (hd535)); let hd537 : Expr := (.emptySequence 0); let hd538 : Expr := (.sequenceConstruct (hd536) (hd537)); let hd539 : Expr := (.emptySequence 0); let hd540 : Expr := (.sequenceConstruct (hd538) (hd539)); let hd541 : Expr := (.emptySequence 0); let hd542 : Expr := (.sequenceConstruct (hd540) (hd541)); let hd543 : Expr := (.emptySequence 0); let hd544 : Expr := (.sequenceConstruct (hd542) (hd543)); let hd545 : Expr := (.emptySequence 0); let hd546 : Expr := (.sequenceConstruct (hd544) (hd545)); let hd547 : Expr := (.emptySequence 0); let hd548 : Expr := (.sequenceConstruct (hd546) (hd547)); let hd549 : Expr := (.emptySequence 0); let hd550 : Expr := (.sequenceConstruct (hd548) (hd549)); let hd551 : Expr := (.emptySequence 0); let hd552 : Expr := (.sequenceConstruct (hd550) (hd551)); let hd553 : Expr := (.emptySequence 0); let hd554 : Expr := (.sequenceConstruct (hd552) (hd553)); let hd555 : Expr := (.emptySequence 0); let hd556 : Expr := (.sequenceConstruct (hd554) (hd555)); let hd557 : Expr := (.emptySequence 0); let hd558 : Expr := (.sequenceConstruct (hd556) (hd557)); let hd559 : Expr := (.emptySequence 0); let hd560 : Expr := (.sequenceConstruct (hd558) (hd559)); let hd561 : Expr := (.emptySequence 0); let hd562 : Expr := (.sequenceConstruct (hd560) (hd561)); let hd563 : Expr := (.emptySequence 0); let hd564 : Expr := (.sequenceConstruct (hd562) (hd563)); let hd565 : Expr := (.emptySequence 0); let hd566 : Expr := (.sequenceConstruct (hd564) (hd565)); let hd567 : Expr := (.emptySequence 0); let hd568 : Expr := (.sequenceConstruct (hd566) (hd567)); let hd569 : Expr := (.emptySequence 0); let hd570 : Expr := (.sequenceConstruct (hd568) (hd569)); let hd571 : Expr := (.emptySequence 0); let hd572 : Expr := (.sequenceConstruct (hd570) (hd571)); let hd573 : Expr := (.emptySequence 0); let hd574 : Expr := (.sequenceConstruct (hd572) (hd573)); let hd575 : Expr := (.emptySequence 0); let hd576 : Expr := (.sequenceConstruct (hd574) (hd575)); let hd577 : Expr := (.emptySequence 0); let hd578 : Expr := (.sequenceConstruct (hd576) (hd577)); let hd579 : Expr := (.emptySequence 0); let hd580 : Expr := (.sequenceConstruct (hd578) (hd579)); let hd581 : Expr := (.emptySequence 0); let hd582 : Expr := (.sequenceConstruct (hd580) (hd581)); let hd583 : Expr := (.emptySequence 0); let hd584 : Expr := (.sequenceConstruct (hd582) (hd583)); let hd585 : Expr := (.emptySequence 0); let hd586 : Expr := (.sequenceConstruct (hd584) (hd585)); let hd587 : Expr := (.emptySequence 0); let hd588 : Expr := (.sequenceConstruct (hd586) (hd587)); let hd589 : Expr := (.emptySequence 0); let hd590 : Expr := (.sequenceConstruct (hd588) (hd589)); let hd591 : Expr := (.emptySequence 0); let hd592 : Expr := (.sequenceConstruct (hd590) (hd591)); let hd593 : Expr := (.emptySequence 0); let hd594 : Expr := (.sequenceConstruct (hd592) (hd593)); let hd595 : Expr := (.emptySequence 0); let hd596 : Expr := (.sequenceConstruct (hd594) (hd595)); let hd597 : Expr := (.emptySequence 0); let hd598 : Expr := (.sequenceConstruct (hd596) (hd597)); let hd599 : Expr := (.emptySequence 0); let hd600 : Expr := (.sequenceConstruct (hd598) (hd599)); let hd601 : Expr := (.emptySequence 0); let hd602 : Expr := (.sequenceConstruct (hd600) (hd601)); let hd603 : Expr := (.emptySequence 0); let hd604 : Expr := (.sequenceConstruct (hd602) (hd603)); let hd605 : Algorithm := (alg [] [] [] [hd604]); let hd606 : ScopeCtx := (ScopeCtx.mk none [] [] [privateProp "P" hd605] [] [] none (some (.host 0))); let hd607 : Algorithm := (Algorithm.withParent (some hd606) (alg [] [] [publicProp "Run" hd1] [])); let hd608 : Expr := (.algorithmExpr hd607); let hd609 : Expr := .resolve "Run"; let hd610 : Algorithm := (alg [] [hd608] [] [hd609]); let hd611 : Expr := (.algorithmExpr hd610); hd611)
#guard obs hp_10i == "ok raw=1 n=1"
#guard structural hp_10i == some "kl-struct-v1:1:n3:1e0"
#guard cacheEntries hp_10i "P" == some 1
#guard cacheEntries hp_10i "Run" == some 1
#guard cacheTotal hp_10i == some 2

-- HP-11a: a host-declared static alias calls its target
def hp_11a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "A" (.alias none [] [] (.resolve "Inc"))] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "A") [.num 5])])] [])))] [] [.resolve "Run"]))
#guard obs hp_11a == "ok raw=6 n=1"
#guard structural hp_11a == some "kl-struct-v1:1:n3:6e0"
#guard cacheEntries hp_11a "Run" == some 1
#guard cacheTotal hp_11a == some 1

-- HP-11b: a host alias chain B -> A -> Inc
def hp_11b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "A" (.alias none [] [] (.resolve "Inc")), privateProp "B" (.alias none [] [] (.resolve "A"))] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "B") [.num 5])])] [])))] [] [.resolve "Run"]))
#guard obs hp_11b == "ok raw=6 n=1"
#guard structural hp_11b == some "kl-struct-v1:1:n3:6e0"
#guard cacheEntries hp_11b "Run" == some 1
#guard cacheTotal hp_11b == some 1

-- HP-11c: a host alias resolves its target in the HOST scope, never the block's shadowing Inc
def hp_11c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "A" (.alias none [] [] (.resolve "Inc"))] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.call (.resolve "Inc") [.num 5]))]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [])))] [] [.resolve "Run"]))
#guard obs hp_11c == "ok raw=111 n=1"
#guard structural hp_11c == some "kl-struct-v1:1:n5:111e0"
#guard cacheEntries hp_11c "Run" == some 1
#guard cacheTotal hp_11c == some 1

-- HP-11d: a block alias over a host-declared target
def hp_11d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "A2") [.num 5])]), privateProp "A2" (.alias none [] [] (.resolve "Inc"))] [])))] [] [.resolve "Run"]))
#guard obs hp_11d == "ok raw=6 n=1"
#guard structural hp_11d == some "kl-struct-v1:1:n3:6e0"
#guard cacheEntries hp_11d "Run" == some 1
#guard cacheTotal hp_11d == some 1

-- HP-11e: an alias in a grandparent level through a member path
def hp_11e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [privateProp "M" (alg [] [] [publicProp "Twice" (alg ["x"] [] [] [(.binary .mul (.param "x") (.num 2))])] [])] [] [] none (some (.host 0)))) [] [] [privateProp "T" (.alias none [] [] ((.dotCall (.resolve "M") "Twice" none)))] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "T") [.num 21])])] [])))] [] [.resolve "Run"]))
#guard obs hp_11e == "ok raw=42 n=1"
#guard structural hp_11e == some "kl-struct-v1:1:n4:42e0"
#guard cacheEntries hp_11e "Run" == some 1
#guard cacheTotal hp_11e == some 1

-- HP-12a: D4 terminal fallback: a zero-parameter target keeps ordinary-property semantics (A, A(), A, A())
def hp_12a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "F" (alg [] [] [] [.num 7]), privateProp "Capture" (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]), privateProp "R" (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]), privateProp "A" (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none)))] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "A", (.call (.resolve "A") []), .resolve "A", (.call (.resolve "A") [])])] [])))] [] [.resolve "Run"]))
#guard obs hp_12a == "ok raw=S[7, 7, 7, 7] n=1"
#guard structural hp_12a == some "kl-struct-v1:2:n3:7e0s4:0,0,0,0,;"
#guard cacheEntries hp_12a "A" == some 0
#guard cacheEntries hp_12a "F" == some 1
#guard cacheEntries hp_12a "R" == some 1
#guard cacheEntries hp_12a "Run" == some 1
#guard cacheTotal hp_12a == some 3

-- HP-12b: D3 parameterized forwarding: A(args) is a fresh call of the projected F
def hp_12b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "F" (alg ["v"] [] [] [(.binary .add (.param "v") (.num 1))]), privateProp "Capture" (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]), privateProp "R" (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [.num 1])])]), privateProp "A" (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none)))] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "A") [.num 5]), (.call (.resolve "A") [.num 10])])] [])))] [] [.resolve "Run"]))
#guard obs hp_12b == "ok raw=S[6, 11] n=1"
#guard structural hp_12b == some "kl-struct-v1:3:n3:6e0n4:11e0s2:0,1,;"
#guard cacheEntries hp_12b "A" == some 0
#guard cacheEntries hp_12b "R" == some 1
#guard cacheEntries hp_12b "Run" == some 1
#guard cacheTotal hp_12b == some 2

-- HP-12c: one host object opened twice shares the alias's declaring namespace (HOST-ALIAS-R14)
def hp_12c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 2) }, { (privateProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 3) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [.resolve "A"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 2) }, { (privateProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 3) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "A") [])])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_12c == "ok raw=S[7, 7] n=2"
#guard structural hp_12c == some "kl-struct-v1:2:n3:7e0s2:0,0,;"
#guard cacheEntries hp_12c "A" == some 0
#guard cacheEntries hp_12c "F" == some 1
#guard cacheEntries hp_12c "R" == some 1
#guard cacheEntries hp_12c "RunA" == some 1
#guard cacheEntries hp_12c "RunB" == some 1
#guard cacheTotal hp_12c == some 4

-- HP-12d: record-equal host objects sharing the member list keep one namespace each (HOST-ALIAS-R14)
def hp_12d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 2) }, { (privateProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 3) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [.resolve "A"])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 2) }, { (privateProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 3) }] [] [] none (some (.host 1)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "A") [])])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_12d == "ok raw=S[7, 7] n=2"
#guard structural hp_12d == some "kl-struct-v1:2:n3:7e0s2:0,0,;"
#guard cacheEntries hp_12d "A" == some 0
#guard cacheEntries hp_12d "F" == some 2
#guard cacheEntries hp_12d "R" == some 2
#guard cacheEntries hp_12d "RunA" == some 1
#guard cacheEntries hp_12d "RunB" == some 1
#guard cacheTotal hp_12d == some 6

-- HP-13a: a host property whose CONDITIONAL value carries its own parent: lookup wiring replaces it
def hp_13a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "K" (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none (some (.host 1)))) (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.resolve "V"])⟩, ⟨.bind "n", (alg [] [] [] [(.binary .add (.param "n") (.resolve "V"))])⟩]))] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "K") [.num 0]), (.call (.resolve "K") [.num 5])])] [])))] [] [.resolve "Run"]))
#guard obs hp_13a == "ok raw=S[1, 6] n=1"
#guard structural hp_13a == some "kl-struct-v1:3:n3:1e0n3:6e0s2:0,1,;"
#guard cacheEntries hp_13a "Run" == some 1
#guard cacheEntries hp_13a "V" == some 1
#guard cacheTotal hp_13a == some 2

-- HP-13b: a host property whose ALIAS value carries its own parent: lookup wiring replaces it
def hp_13b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "A" (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none (some (.host 1)))) (.alias none [] [] (.resolve "Inc")))] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "A") [.num 1])])] [])))] [] [.resolve "Run"]))
#guard obs hp_13b == "ok raw=2 n=1"
#guard structural hp_13b == some "kl-struct-v1:1:n3:2e0"
#guard cacheEntries hp_13b "Run" == some 1
#guard cacheTotal hp_13b == some 1

-- HP-13c: a pre-wired CONDITIONAL as an open target is refused when a lookup reaches it
def hp_13c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none (some (.host 0)))) (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩])))] [] [.resolve "Z"]))
#guard obs hp_13c == "err illegalInOpen"
#guard cacheTotal hp_13c == some 0

-- HP-13d: a pre-wired ALIAS as an open target is refused when a lookup reaches it
def hp_13d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none (some (.host 0)))) (.alias none [] [] (.resolve "Inc"))))] [] [.resolve "Z"]))
#guard obs hp_13d == "err illegalInOpen"
#guard cacheTotal hp_13d == some 0

-- HP-13e: a pre-wired PROGRAM ROOT is wired under the prelude: its host parent is replaced
def hp_13e : Expr :=
  (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none (some (.host 0)))) (alg [] [] [] [.resolve "V"])))
#guard obs hp_13e == "err unknownName"
#guard errorObs hp_13e == .matched (some { kind := "unknownName", names := ["V"], counts := [] })
#guard cacheTotal hp_13e == some 0

-- HP-13f: a pre-wired inline block in VALUE position is wired to its caller
def hp_13f : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none (some (.host 0)))) (alg [] [] [] [.resolve "V"])))])] [])))] [] [.resolve "Run"]))
#guard obs hp_13f == "ok raw=1 n=1"
#guard structural hp_13f == some "kl-struct-v1:1:n3:1e0"
#guard cacheEntries hp_13f "Run" == some 1
#guard cacheEntries hp_13f "V" == some 1
#guard cacheTotal hp_13f == some 2

-- HP-13g: a pre-wired inline CALLEE is wired to its caller
def hp_13g : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none (some (.host 0)))) (alg ["y"] [] [] [(.binary .add (.param "y") (.resolve "V"))]))) [.num 3])])] [])))] [] [.resolve "Run"]))
#guard obs hp_13g == "ok raw=4 n=1"
#guard structural hp_13g == some "kl-struct-v1:1:n3:4e0"
#guard cacheEntries hp_13g "Run" == some 1
#guard cacheEntries hp_13g "V" == some 1
#guard cacheTotal hp_13g == some 2

-- HP-13h: a pre-wired inline CONDITIONAL callee is wired to its caller
def hp_13h : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none (some (.host 0)))) (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.resolve "V"])⟩, ⟨.bind "n", (alg [] [] [] [(.binary .add (.param "n") (.resolve "V"))])⟩]))) [.num 0])])] [])))] [] [.resolve "Run"]))
#guard obs hp_13h == "ok raw=1 n=1"
#guard structural hp_13h == some "kl-struct-v1:1:n3:1e0"
#guard cacheEntries hp_13h "Run" == some 1
#guard cacheEntries hp_13h "V" == some 1
#guard cacheTotal hp_13h == some 2

-- HP-13i: a pre-wired inline ALIAS callee resolves its target from the caller
def hp_13i : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none (some (.host 0)))) (.alias none [] [] (.resolve "Inc")))) [.num 2])])] [])))] [] [.resolve "Run"]))
#guard obs hp_13i == "ok raw=3 n=1"
#guard structural hp_13i == some "kl-struct-v1:1:n3:3e0"
#guard cacheEntries hp_13i "Run" == some 1
#guard cacheTotal hp_13i == some 1

-- HP-13j: a pre-wired property value of the BLOCK itself is replaced by the block's wiring
def hp_13j : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "U"]), privateProp "U" (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none (some (.host 0)))) (alg [] [] [] [.resolve "V"]))] [])))] [] [.resolve "Run"]))
#guard obs hp_13j == "ok raw=1 n=1"
#guard structural hp_13j == some "kl-struct-v1:1:n3:1e0"
#guard cacheEntries hp_13j "Run" == some 1
#guard cacheEntries hp_13j "U" == some 1
#guard cacheEntries hp_13j "V" == some 1
#guard cacheTotal hp_13j == some 3

-- HP-13k: a structural receiver block with a pre-wired parent is wired to its caller
def hp_13k : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 1]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.dotCall (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "W" (alg [] [] [] [.resolve "V"])] []))) "W" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_13k == "ok raw=1 n=1"
#guard structural hp_13k == some "kl-struct-v1:1:n3:1e0"
#guard cacheEntries hp_13k "Run" == some 1
#guard cacheEntries hp_13k "V" == some 1
#guard cacheEntries hp_13k "W" == some 1
#guard cacheTotal hp_13k == some 3

-- HP-13l: an explicitly wired module open preserves its host root instead of taking the caller's V
def hp_13l : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.module 0)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "V" (alg [] [] [] [.num 99]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 100))])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "V"])] []))))] [privateProp "V" (alg [] [] [] [.num 1])] [.resolve "Run"]))
#guard obs hp_13l == "ok raw=99 n=1"
#guard structural hp_13l == some "kl-struct-v1:1:n4:99e0"
#guard cacheEntries hp_13l "Run" == some 1
#guard cacheEntries hp_13l "V" == some 1
#guard cacheTotal hp_13l == some 2

-- HP-13m: a module property roots at the supplied host chain, which has no implicit prelude count
def hp_13m : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "M" (Algorithm.withDeclarationId (some (.module 0)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "count" (alg ["x"] [] [] [.num 99])] [] [] none (some (.host 1)))) (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [])])])))] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "M"])] [])))] [] [.resolve "Run"]))
#guard obs hp_13m == "err unknownName"
#guard errorObs hp_13m == .matched (some { kind := "unknownName", names := ["count"], counts := [] })
#guard cacheEntries hp_13m "M" == some 0
#guard cacheTotal hp_13m == some 0

-- HP-14a: control: one declaration opened twice under ONE empty host level object is one provider
def hp_14a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] [])))), (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [] [.resolve "F"]))
#guard obs hp_14a == "ok raw=7 n=1"
#guard structural hp_14a == some "kl-struct-v1:1:n3:7e0"
#guard cacheEntries hp_14a "F" == some 1
#guard cacheTotal hp_14a == some 1

-- HP-14b: Q-19: one declaration opened twice under two DISTINCT empty host level objects is two providers
def hp_14b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] [])))), (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 1)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 1) }] []))))] [] [.resolve "F"]))
#guard obs hp_14b == "err ambiguousOpen"
#guard errorObs hp_14b == .matched (some { kind := "ambiguousOpen", names := ["F"], counts := [] })
#guard cacheEntries hp_14b "F" == some 0
#guard cacheTotal hp_14b == some 0

-- HP-14c: control: fresh host levels with their own nested declarations keep (S, P.Q) per level
def hp_14c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "S" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]), privateProp "P" (alg [] [] [publicProp "Q" (alg [] [] [] [.resolve "S"])] [])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "S", (.dotCall (.resolve "P") "Q" none)])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "S" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]), privateProp "P" (alg [] [] [publicProp "Q" (alg [] [] [] [.resolve "S"])] [])] [] [] none (some (.host 1)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "S", (.dotCall (.resolve "P") "Q" none)])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_14c == "ok raw=S[S[1, 1], S[2, 2]] n=2"
#guard structural hp_14c == some "kl-struct-v1:5:n3:1e0s2:0,0,;n3:2e0s2:2,2,;s2:1,3,;"
#guard cacheEntries hp_14c "Q" == some 2
#guard cacheEntries hp_14c "RunA" == some 1
#guard cacheEntries hp_14c "RunB" == some 1
#guard cacheEntries hp_14c "S" == some 2
#guard cacheTotal hp_14c == some 6

-- HP-14d: an owned Q nested under two record-equal host levels that share ONE property list keeps (S, P.Q) per level
def hp_14d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "S" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }, { (privateProp "P" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [{ (publicProp "Q" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [.resolve "S"]))) with identity := some (.shared 2) }] []))) with identity := some (.shared 1) }] [] [] none (some (.host 0)))) (alg [] [] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])]), publicProp "G" (alg ["x"] [] [] [.resolve "S", (.dotCall (.resolve "P") "Q" none)])] []))), (.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "S" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }, { (privateProp "P" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [{ (publicProp "Q" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [.resolve "S"]))) with identity := some (.shared 3) }] []))) with identity := some (.shared 1) }] [] [] none (some (.host 1)))) (alg [] [] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "S", (.dotCall (.resolve "P") "Q" none)])] [])))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_14d == "ok raw=S[S[1, 1], S[2, 2]] n=2"
#guard structural hp_14d == some "kl-struct-v1:5:n3:1e0s2:0,0,;n3:2e0s2:2,2,;s2:1,3,;"
#guard cacheEntries hp_14d "Q" == some 2
#guard cacheEntries hp_14d "RunA" == some 1
#guard cacheEntries hp_14d "RunB" == some 1
#guard cacheEntries hp_14d "S" == some 2
#guard cacheTotal hp_14d == some 6

-- HP-14e: an owned P under two DISTINCT empty host ancestors is two cache owners (one evaluation per owner)
def hp_14e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 1) }] []))))] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])])] [])), (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 1)))) (alg [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 2) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 3) }] []))))] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])])] []))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_14e == "ok raw=S[1, 2] n=2"
#guard structural hp_14e == some "kl-struct-v1:3:n3:1e0n3:2e0s2:0,1,;"
#guard cacheEntries hp_14e "P" == some 2
#guard cacheEntries hp_14e "RunA" == some 1
#guard cacheEntries hp_14e "RunB" == some 1
#guard cacheTotal hp_14e == some 4

-- HP-14f: control: the owned P under ONE empty host ancestor object reached twice is one cache owner
def hp_14f : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 1) }] []))))] [publicProp "RunA" (alg [] [] [] [(.call (.resolve "G") [.num 1])])] [])), (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (privateProp "P" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])]))) with identity := some (.shared 0) }, { (publicProp "G" (Algorithm.withDeclarationId (some (.shared 1)) (alg ["x"] [] [] [.resolve "P"]))) with identity := some (.shared 1) }] []))))] [publicProp "RunB" (alg [] [] [] [(.call (.resolve "G") [.num 2])])] []))] [] [.resolve "RunA", .resolve "RunB"]))
#guard obs hp_14f == "ok raw=S[1, 1] n=2"
#guard structural hp_14f == some "kl-struct-v1:2:n3:1e0s2:0,0,;"
#guard cacheEntries hp_14f "P" == some 1
#guard cacheEntries hp_14f "RunA" == some 1
#guard cacheEntries hp_14f "RunB" == some 1
#guard cacheTotal hp_14f == some 3

-- HP-14g: NEED-04: one F declaration under two DISTINCT empty host ancestors is two callables
def hp_14g : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [publicProp "FA" (.alias none [] [] (.resolve "F"))] [])), (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 1)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 1) }] []))))] [publicProp "FB" (.alias none [] [] (.resolve "F"))] []))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_14g == "err type"
#guard cacheTotal hp_14g == some 0

-- HP-14h: NEED-04 control: one F declaration under ONE empty host ancestor object is one callable
def hp_14h : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [publicProp "FA" (.alias none [] [] (.resolve "F"))] [])), (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [publicProp "FB" (.alias none [] [] (.resolve "F"))] []))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_14h == "ok raw=0 n=1"
#guard structural hp_14h == some "kl-struct-v1:1:n1:0"
#guard cacheTotal hp_14h == some 0

-- HP-14i: runtime alias cells under two DISTINCT empty host ancestors project two callables (NEED-04 refuses)
def hp_14i : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 4)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg ["v"] [] [] [(.binary .add (.param "v") (.num 1))]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [.num 1])])]))) with identity := some (.shared 2) }, { (publicProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 3) }] []))))] [publicProp "FA" (.alias none [] [] (.resolve "A"))] [])), (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 4)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 1)))) (alg [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg ["v"] [] [] [(.binary .add (.param "v") (.num 1))]))) with identity := some (.shared 4) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 5) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [.num 1])])]))) with identity := some (.shared 6) }, { (publicProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 7) }] []))))] [publicProp "FB" (.alias none [] [] (.resolve "A"))] []))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_14i == "err type"
#guard cacheEntries hp_14i "R" == some 2
#guard cacheTotal hp_14i == some 2

-- HP-14j: control: runtime alias cells under ONE empty host ancestor object project one callable
def hp_14j : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 4)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg ["v"] [] [] [(.binary .add (.param "v") (.num 1))]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [.num 1])])]))) with identity := some (.shared 2) }, { (publicProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 3) }] []))))] [publicProp "FA" (.alias none [] [] (.resolve "A"))] [])), (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 4)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg ["v"] [] [] [(.binary .add (.param "v") (.num 1))]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.shared 1)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [.num 1])])]))) with identity := some (.shared 2) }, { (publicProp "A" (Algorithm.withDeclarationId (some (.shared 3)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none))))) with identity := some (.shared 3) }] []))))] [publicProp "FB" (.alias none [] [] (.resolve "A"))] []))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_14j == "ok raw=0 n=1"
#guard structural hp_14j == some "kl-struct-v1:1:n1:0"
#guard cacheEntries hp_14j "R" == some 1
#guard cacheTotal hp_14j == some 1

-- HP-14k: NEED-04: owned views with distinct nonempty property lists are distinct declaring scopes
def hp_14k : Expr :=
  (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 7 5)) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 3 2)) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 1 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [publicProp "FA" (Algorithm.withDeclarationId (some (.sharedView 2 0)) (.alias none [] [] (.resolve "F")))] []))), (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 5 4)) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 1 3)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 1) }] []))))] [publicProp "FB" (Algorithm.withDeclarationId (some (.sharedView 4 0)) (.alias none [] [] (.resolve "F")))] [])))] [privateProp "P" (Algorithm.withDeclarationId (some (.sharedView 6 0)) (alg ["f", "f"] [] [] [.num 0]))] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])])))
#guard obs hp_14k == "err type"
#guard cacheTotal hp_14k == some 0

-- HP-14l: NEED-04: owned views with distinct nonempty opens lists are distinct declaring scopes
def hp_14l : Expr :=
  (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 9 6)) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 5 3)) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 3 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 1 1)) (alg [] [] [{ (publicProp "Unused" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 3]))) with identity := some (.shared 0) }] [])))] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.sharedView 2 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 1) }] []))))] [publicProp "FA" (Algorithm.withDeclarationId (some (.sharedView 4 0)) (.alias none [] [] (.resolve "F")))] []))), (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 7 5)) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 3 4)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 1 1)) (alg [] [] [{ (publicProp "Unused" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 3]))) with identity := some (.shared 0) }] [])))] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.sharedView 2 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 2) }] []))))] [publicProp "FB" (Algorithm.withDeclarationId (some (.sharedView 6 0)) (.alias none [] [] (.resolve "F")))] [])))] [privateProp "P" (Algorithm.withDeclarationId (some (.sharedView 8 0)) (alg ["f", "f"] [] [] [.num 0]))] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])])))
#guard obs hp_14l == "err type"
#guard cacheTotal hp_14l == some 0

-- HP-14m: NEED-04 control: copied empty opens lists keep equivalent owned scopes
def hp_14m : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [publicProp "FA" (.alias none [] [] (.resolve "F"))] [])), (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [publicProp "FB" (.alias none [] [] (.resolve "F"))] []))] [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "FA", .resolve "FB"])]))
#guard obs hp_14m == "ok raw=0 n=1"
#guard structural hp_14m == some "kl-struct-v1:1:n1:0"
#guard cacheTotal hp_14m == some 0

-- HP-14n: NEED-04: replacing a callable's OWN lists preserves its declaration identity
def hp_14n : Expr :=
  (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 3 3)) (alg [] [] [privateProp "P" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg ["f", "f"] [] [] [.num 0]))] [(.call (.resolve "P") [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 2 1)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.sharedView 1 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 0) }] []))), (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 2 2)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.sharedView 1 0)) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]))) with identity := some (.shared 1) }] [])))])])))
#guard obs hp_14n == "ok raw=0 n=1"
#guard structural hp_14n == some "kl-struct-v1:1:n1:0"
#guard cacheTotal hp_14n == some 0

-- HP-14o: Q-19: provider declarations under owned views with different nonempty lists stay distinct
def hp_14o : Expr :=
  (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 3 4)) (alg [] [(.dotCall (.resolve "A") "Lib" none), (.dotCall (.resolve "B") "Lib" none)] [privateProp "A" (Algorithm.withDeclarationId (some (.sharedView 2 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "Lib" (Algorithm.withDeclarationId (some (.sharedView 1 1)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }] []))), privateProp "B" (Algorithm.withDeclarationId (some (.sharedView 2 3)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "Lib" (Algorithm.withDeclarationId (some (.sharedView 1 1)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 3) }] []))) with identity := some (.shared 2) }] [])))] [.resolve "F"])))
#guard obs hp_14o == "err ambiguousOpen"
#guard errorObs hp_14o == .matched (some { kind := "ambiguousOpen", names := ["F"], counts := [] })
#guard cacheTotal hp_14o == some 0

-- HP-14p: Q-19 control: providers under equivalent owned reconstructions share identity
def hp_14p : Expr :=
  (.algorithmExpr (alg [] [(.dotCall (.resolve "A") "Lib" none), (.dotCall (.resolve "B") "Lib" none)] [privateProp "A" (Algorithm.withDeclarationId (some (.shared 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "Lib" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }] []))), privateProp "B" (Algorithm.withDeclarationId (some (.shared 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "Lib" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }] [])))] [.resolve "F"]))
#guard obs hp_14p == "ok raw=7 n=1"
#guard structural hp_14p == some "kl-struct-v1:1:n3:7e0"
#guard cacheEntries hp_14p "F" == some 1
#guard cacheTotal hp_14p == some 1

-- HP-14q: shared runtime alias literal under property-free owned parents with distinct opens lists
def hp_14q : Expr :=
  (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 8 4)) (alg [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.sharedView 1 0)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.sharedView 2 0)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 2) }] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 6 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 4) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.sharedView 1 0)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 5) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.sharedView 2 0)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 6) }] [] [] none (some (.host 0)))) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 4 1)) (alg [] [] [{ (publicProp "Unused" (Algorithm.withDeclarationId (some (.sharedView 3 0)) (alg [] [] [] [.num 3]))) with identity := some (.shared 3) }] [])))] [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 5 0)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none)))))])))), (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 7 3)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 4) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.sharedView 1 0)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 5) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.sharedView 2 0)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 6) }] [] [] none (some (.host 0)))) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 4 1)) (alg [] [] [{ (publicProp "Unused" (Algorithm.withDeclarationId (some (.sharedView 3 0)) (alg [] [] [] [.num 3]))) with identity := some (.shared 3) }] [])))] [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 5 0)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none)))))]))))])))
#guard obs hp_14q == "ok raw=S[7, 7] n=2"
#guard structural hp_14q == some "kl-struct-v1:2:n3:7e0s2:0,0,;"
#guard cacheEntries hp_14q "F" == some 1
#guard cacheEntries hp_14q "R" == some 1
#guard cacheTotal hp_14q == some 2

-- HP-14r: control: shared runtime alias literal under owned parents sharing their opens list
def hp_14r : Expr :=
  (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 8 3)) (alg [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.sharedView 1 0)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 1) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.sharedView 2 0)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 2) }] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 6 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 4) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.sharedView 1 0)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 5) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.sharedView 2 0)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 6) }] [] [] none (some (.host 0)))) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 4 1)) (alg [] [] [{ (publicProp "Unused" (Algorithm.withDeclarationId (some (.sharedView 3 0)) (alg [] [] [] [.num 3]))) with identity := some (.shared 3) }] [])))] [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 5 0)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none)))))])))), (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 7 2)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [{ (privateProp "F" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 4) }, { (privateProp "Capture" (Algorithm.withDeclarationId (some (.sharedView 1 0)) (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]))) with identity := some (.shared 5) }, { (privateProp "R" (Algorithm.withDeclarationId (some (.sharedView 2 0)) (alg [] [] [] [(.call (.resolve "Capture") [(.call (.resolve "F") [])])]))) with identity := some (.shared 6) }] [] [] none (some (.host 0)))) (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 4 1)) (alg [] [] [{ (publicProp "Unused" (Algorithm.withDeclarationId (some (.sharedView 3 0)) (alg [] [] [] [.num 3]))) with identity := some (.shared 3) }] [])))] [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 5 0)) (.alias none [] [] ((.dotCall (.resolve "R") "Algorithm" none)))))]))))])))
#guard obs hp_14r == "ok raw=S[7, 7] n=2"
#guard structural hp_14r == some "kl-struct-v1:2:n3:7e0s2:0,0,;"
#guard cacheEntries hp_14r "F" == some 1
#guard cacheEntries hp_14r "R" == some 1
#guard cacheTotal hp_14r == some 2

-- HP-14s: NEED-04: one shared block as an open target and a property is two callables
def hp_14s : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg ["x"] [] [] [.param "x"]))) with identity := some (.shared 0) }] [])))] [publicProp "N" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg ["x"] [] [] [.param "x"]))) with identity := some (.shared 1) }] [])), privateProp "P" (alg ["f", "f", "f"] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "F", (.dotCall (.resolve "N") "F" none), .resolve "F"])]))
#guard obs hp_14s == "err type"
#guard cacheTotal hp_14s == some 0

-- HP-14t: NEED-04: one block under two host levels and the prelude, at one depth, is three callables
def hp_14t : Expr :=
  (.algorithmExpr (alg [] [] [publicProp "P" (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg ["x"] [] [] [.param "x"]))) with identity := some (.shared 0) }] []))))] [publicProp "G" (.alias none [] [] (.resolve "F"))] []), publicProp "Q" (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg ["x"] [] [] [.param "x"]))) with identity := some (.shared 1) }] [])))] [publicProp "G" (.alias none [] [] (.resolve "F"))] []), publicProp "R" (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 1)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg ["x"] [] [] [.param "x"]))) with identity := some (.shared 2) }] []))))] [publicProp "G" (.alias none [] [] (.resolve "F"))] []), privateProp "Same" (alg ["f", "f", "f"] [] [] [.num 0])] [(.call (.resolve "Same") [(.dotCall (.resolve "P") "G" none), (.dotCall (.resolve "Q") "G" none), (.dotCall (.resolve "R") "G" none)])]))
#guard obs hp_14t == "err type"
#guard cacheTotal hp_14t == some 0

-- HP-14u: Q-19: one declaration under two DISTINCT empty host levels, interleaved with another provider and a repeat, stays two providers
def hp_14u : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] [])))), (.algorithmExpr (alg [] [] [publicProp "G" (alg [] [] [] [.num 9])] [])), (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 1)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 1) }] [])))), (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [] [(.binary .add (.resolve "F") (.resolve "G"))]))
#guard obs hp_14u == "err ambiguousOpen"
#guard errorObs hp_14u == .matched (some { kind := "ambiguousOpen", names := ["F"], counts := [] })
#guard cacheTotal hp_14u == some 0

-- HP-14v: Q-19 control: the same interleaving under ONE empty host level object is one provider of F
def hp_14v : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] [])))), (.algorithmExpr (alg [] [] [publicProp "G" (alg [] [] [] [.num 9])] [])), (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] [])))), (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 1)) (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [{ (publicProp "F" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 7]))) with identity := some (.shared 0) }] []))))] [] [(.binary .add (.resolve "F") (.resolve "G"))]))
#guard obs hp_14v == "ok raw=16 n=1"
#guard structural hp_14v == some "kl-struct-v1:1:n4:16e0"
#guard cacheEntries hp_14v "F" == some 1
#guard cacheEntries hp_14v "G" == some 1
#guard cacheTotal hp_14v == some 2

-- HP-15a: a deconstruction helper copied over another argument, copy read first (H04)
def hp_15a : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "a" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])])), privateProp "b" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])]), privateProp "q" (alg [] [] [] [(.capture [.num 7, .num 8])]), privateProp "c" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "q"])]))] [.resolve "c", .resolve "a"]))
#guard obs hp_15a == "ok raw=S[7, 1] n=2"
#guard structural hp_15a == some "kl-struct-v1:3:n3:7e0n3:1e0s2:0,1,;"
#guard cacheEntries hp_15a "$deconstruct$0" == some 1
#guard cacheEntries hp_15a "a" == some 1
#guard cacheEntries hp_15a "c" == some 1
#guard cacheEntries hp_15a "q" == some 1
#guard cacheTotal hp_15a == some 4

-- HP-15b: a deconstruction helper copied over another argument, original read first (H05)
def hp_15b : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "a" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])])), privateProp "b" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])]), privateProp "q" (alg [] [] [] [(.capture [.num 7, .num 8])]), privateProp "c" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "q"])]))] [.resolve "a", .resolve "c"]))
#guard obs hp_15b == "ok raw=S[1, 7] n=2"
#guard structural hp_15b == some "kl-struct-v1:3:n3:1e0n3:7e0s2:0,1,;"
#guard cacheEntries hp_15b "$deconstruct$0" == some 1
#guard cacheEntries hp_15b "a" == some 1
#guard cacheEntries hp_15b "c" == some 1
#guard cacheEntries hp_15b "q" == some 1
#guard cacheTotal hp_15b == some 4

-- HP-15c: a deconstruction helper copy with a changed unpacking pattern, copy read first (V05)
def hp_15c : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.listLiteral [.num 1]), .num 2])]), privateProp "a" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])])), privateProp "b" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])]), privateProp "c" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.listValue [.capture { name := "a" }], .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])]))] [.resolve "c", .resolve "a"]))
#guard obs hp_15c == "ok raw=S[1, L[1]] n=2"
#guard structural hp_15c == some "kl-struct-v1:3:n3:1e0l1:0,;s2:0,1,;"
#guard cacheEntries hp_15c "$deconstruct$0" == some 1
#guard cacheEntries hp_15c "a" == some 1
#guard cacheEntries hp_15c "c" == some 1
#guard cacheTotal hp_15c == some 3

-- HP-15d: a deconstruction helper copy with a changed unpacking pattern, original read first (V06)
def hp_15d : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.listLiteral [.num 1]), .num 2])]), privateProp "a" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])])), privateProp "b" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])]), privateProp "c" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.shared 0)) (algWithParameterPatterns [.unpacking [.listValue [.capture { name := "a" }], .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])]))] [.resolve "a", .resolve "c"]))
#guard obs hp_15d == "ok raw=S[L[1], 1] n=2"
#guard structural hp_15d == some "kl-struct-v1:3:n3:1e0l1:0,;s2:1,0,;"
#guard cacheEntries hp_15d "$deconstruct$0" == some 1
#guard cacheEntries hp_15d "a" == some 1
#guard cacheEntries hp_15d "c" == some 1
#guard cacheTotal hp_15d == some 3

-- HP-15e: a deconstruction target body copied with a local shadowing source (V07)
def hp_15e : Expr :=
  (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 5 2)) (alg [] [] [privateProp "$deconstruct$0" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [(.capture [.num 1, .num 2])])), privateProp "a" (Algorithm.withDeclarationId (some (.sharedView 2 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 1 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])])), privateProp "b" (Algorithm.withDeclarationId (some (.sharedView 4 0)) (alg [] [] [] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 3 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"]))) [.resolve "$deconstruct$0"])])), privateProp "c" (Algorithm.withDeclarationId (some (.sharedView 2 1)) (alg [] [] [privateProp "$deconstruct$0" (Algorithm.withDeclarationId (some (.sharedView 0 0)) (alg [] [] [] [.num 7, .num 8]))] [(.call (.algorithmExpr (Algorithm.withDeclarationId (some (.sharedView 1 0)) (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"]))) [.resolve "$deconstruct$0"])]))] [.resolve "a", .resolve "c"])))
#guard obs hp_15e == "ok raw=S[1, 7] n=2"
#guard structural hp_15e == some "kl-struct-v1:3:n3:1e0n3:7e0s2:0,1,;"
#guard cacheEntries hp_15e "$deconstruct$0" == some 2
#guard cacheEntries hp_15e "a" == some 1
#guard cacheEntries hp_15e "c" == some 1
#guard cacheTotal hp_15e == some 4

-- HP-16a: a run that fails after X = 7 was published keeps the entry (rows X, 1 / 0)
def hp_16a : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "X" (alg [] [] [] [.num 7])] [.resolve "X", (.binary .div (.num 1) (.num 0))]))
#guard obs hp_16a == "err div0"
#guard errorObs hp_16a == .matched (some { kind := "div0", names := [], counts := [] })
#guard cacheEntries hp_16a "X" == some 1
#guard cacheTotal hp_16a == some 1

-- HP-16b: a failing host property and the failing owner reading it publish nothing
def hp_16b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.binary .div (.num 1) (.num 0))])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_16b == "err div0"
#guard errorObs hp_16b == .matched (some { kind := "div0", names := [], counts := [] })
#guard cacheEntries hp_16b "P" == some 0
#guard cacheEntries hp_16b "Run" == some 0
#guard cacheTotal hp_16b == some 0

-- HP-16c: a failed owner publishes nothing while its host dependency P stays published
def hp_16c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.num 7])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "P", (.binary .div (.num 1) (.num 0))])] [])))] [] [.resolve "Run"]))
#guard obs hp_16c == "err div0"
#guard errorObs hp_16c == .matched (some { kind := "div0", names := [], counts := [] })
#guard cacheEntries hp_16c "P" == some 1
#guard cacheEntries hp_16c "Run" == some 0
#guard cacheTotal hp_16c == some 1

-- HP-17a: KL-07: a host property holding the list of the two strings a and b
def hp_17a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [.stringLiteral "a", .stringLiteral "b"])])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_17a == "ok raw=L['a', 'b'] n=1"
#guard structural hp_17a == some "kl-struct-v1:3:t1:at1:bl2:0,1,;"
#guard cacheEntries hp_17a "P" == some 1
#guard cacheEntries hp_17a "Run" == some 1
#guard cacheTotal hp_17a == some 2

-- HP-17b: KL-07: a host property holding the list of the ONE host-built string a', 'b
def hp_17b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [.stringLiteral "a', 'b"])])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_17b == "ok raw=L['a', 'b'] n=1"
#guard structural hp_17b == some "kl-struct-v1:2:t6:a', 'bl1:0,;"
#guard cacheEntries hp_17b "P" == some 1
#guard cacheEntries hp_17b "Run" == some 1
#guard cacheTotal hp_17b == some 2

-- HP-18a: an exported host property reading a name it does not bind is refused, whoever reads it
def hp_18a : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [privateProp "P" (alg [] [] [] [.param "x"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_18a == "err unknownName"
#guard errorObs hp_18a == .matched (some { kind := "unknownName", names := ["x"], counts := [] })
#guard cacheEntries hp_18a "P" == some 0
#guard cacheTotal hp_18a == some 0

-- HP-18b: the same exported property declared by the evaluator-owned block is refused
def hp_18b : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"]), privateProp "P" (alg [] [] [] [.param "x"])] [])))] [] [.resolve "Run"]))
#guard obs hp_18b == "err unknownName"
#guard errorObs hp_18b == .matched (some { kind := "unknownName", names := ["x"], counts := [] })
#guard cacheEntries hp_18b "P" == some 0
#guard cacheTotal hp_18b == some 0

-- HP-18c: a local-only host property reading a parameter its unactivated host level names is refused
def hp_18c : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none ["x"] [] [privateLocalProp "P" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "G") [.num 1]), (.call (.resolve "G") [.num 2])]), publicProp "G" (alg ["x"] [] [] [.resolve "P"])] [])))] [] [.resolve "Run"]))
#guard obs hp_18c == "err unknownName"
#guard errorObs hp_18c == .matched (some { kind := "unknownName", names := ["x"], counts := [] })
#guard cacheEntries hp_18c "P" == some 0
#guard cacheTotal hp_18c == some 0

-- HP-18d: a falsely exported P = y * 10 is refused in ONE call (formerly 10)
def hp_18d : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["y"] [] [privateProp "P" (alg [] [] [] [(.binary .mul (.param "y") (.num 10))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 1])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18d == "err unknownName"
#guard errorObs hp_18d == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_18d "P" == some 0
#guard cacheTotal hp_18d == some 0

-- HP-18e: the same P is refused in TWO calls (formerly S[10, 10]: the first call's value twice)
def hp_18e : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["y"] [] [privateProp "P" (alg [] [] [] [(.binary .mul (.param "y") (.num 10))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18e == "err unknownName"
#guard errorObs hp_18e == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_18e "P" == some 0
#guard cacheTotal hp_18e == some 0

-- HP-18f: an explicit P() of the falsely exported P is refused (formerly it published the first call's value)
def hp_18f : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["y"] [] [privateProp "P" (alg [] [] [] [(.binary .mul (.param "y") (.num 10))])] [(.binary .add (.call (.resolve "P") []) (.resolve "P"))])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18f == "err unknownName"
#guard errorObs hp_18f == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_18f "P" == some 0
#guard cacheTotal hp_18f == some 0

-- HP-18g: a falsely exported P navigating a local-only member is refused when the owner's call comes first (formerly S[10, 10])
def hp_18g : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["y"] [] [privateProp "Box" (alg [] [] [publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .mul (.param "y") (.num 10))])] []), privateProp "P" (alg [] [] [] [(.binary .add (.dotCall (.resolve "Box") "Q" none) (.num 0))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 1]), (.dotCall (.resolve "F") "P" none)])] [])))] [] [.resolve "Run"]))
#guard obs hp_18g == "err localOnlyProperty"
#guard errorObs hp_18g == .matched (some { kind := "localOnlyProperty", names := ["Q", "captured"], counts := [] })
#guard cacheEntries hp_18g "P" == some 0
#guard cacheEntries hp_18g "Q" == some 0
#guard cacheTotal hp_18g == some 0

-- HP-18h: the same navigation is refused when the outside read comes first
def hp_18h : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["y"] [] [privateProp "Box" (alg [] [] [publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .mul (.param "y") (.num 10))])] []), privateProp "P" (alg [] [] [] [(.binary .add (.dotCall (.resolve "Box") "Q" none) (.num 0))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.dotCall (.resolve "F") "P" none), (.call (.resolve "F") [.num 1])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18h == "err localOnlyProperty"
#guard errorObs hp_18h == .matched (some { kind := "localOnlyProperty", names := ["Q", "captured"], counts := [] })
#guard cacheEntries hp_18h "P" == some 0
#guard cacheEntries hp_18h "Q" == some 0
#guard cacheTotal hp_18h == some 0

-- HP-18i: a falsely exported P reading an ESTABLISHED local-only entry is refused (formerly S[21, 31])
def hp_18i : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["y"] [] [privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .mul (.param "y") (.num 10))]), privateProp "P" (alg [] [] [] [(.binary .add (.resolve "L") (.num 1))])] [(.binary .add (.resolve "L") (.resolve "P"))])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18i == "err localOnlyProperty"
#guard errorObs hp_18i == .matched (some { kind := "localOnlyProperty", names := ["L", "captured"], counts := [] })
#guard cacheEntries hp_18i "L" == some 1
#guard cacheEntries hp_18i "P" == some 0
#guard cacheTotal hp_18i == some 1

-- HP-18j: control: the same P declared local-only keeps one value per call
def hp_18j : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["y"] [] [privateLocalProp "P" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .mul (.param "y") (.num 10))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18j == "ok raw=S[10, 20] n=1"
#guard structural hp_18j == some "kl-struct-v1:3:n3:1e1n3:2e1s2:0,1,;"
#guard cacheEntries hp_18j "P" == some 2
#guard cacheEntries hp_18j "Run" == some 1
#guard cacheTotal hp_18j == some 3

-- HP-18k: control: a self-contained exported member of a called owner is evaluated once in each call of the owner
def hp_18k : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["y"] [] [privateProp "T" (alg [] [] [] [(.call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) [])])] [(.binary .add (.resolve "T") (.param "y"))])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18k == "ok raw=S[2, 4] n=1"
#guard structural hp_18k == some "kl-struct-v1:3:n3:2e0n3:4e0s2:0,1,;"
#guard cacheEntries hp_18k "Run" == some 1
#guard cacheEntries hp_18k "T" == some 2
#guard cacheTotal hp_18k == some 3

-- HP-18l: a falsely exported P = y(5) + 0 is refused where the parameter is INVOKED (formerly notAnAlgorithm)
def hp_18l : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), publicProp "F" (alg ["y"] [] [privateProp "P" (alg [] [] [] [(.binary .add (.call (.param "y") [.num 5]) (.num 0))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.resolve "Inc"])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18l == "err unknownName"
#guard errorObs hp_18l == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_18l "P" == some 0
#guard cacheTotal hp_18l == some 0

-- HP-18m: control: the same P declared local-only invokes the supplied callable
def hp_18m : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), publicProp "F" (alg ["y"] [] [privateLocalProp "P" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.call (.param "y") [.num 5]) (.num 0))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.resolve "Inc"])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18m == "ok raw=6 n=1"
#guard structural hp_18m == some "kl-struct-v1:1:n3:6e0"
#guard cacheEntries hp_18m "P" == some 1
#guard cacheEntries hp_18m "Run" == some 1
#guard cacheTotal hp_18m == some 2

-- HP-18n: a falsely exported P = Ignore(y) + 0 is refused where the parameter is TRANSPORTED, although the callee ignores it (formerly 42)
def hp_18n : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "Ignore" (alg ["z"] [] [] [.num 42]), publicProp "F" (alg ["y"] [] [privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "Ignore") [.param "y"]) (.num 0))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 7])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18n == "err unknownName"
#guard errorObs hp_18n == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_18n "P" == some 0
#guard cacheTotal hp_18n == some 0

-- HP-18o: control: the same P declared local-only transports the parameter and the callee ignores it
def hp_18o : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "Ignore" (alg ["z"] [] [] [.num 42]), publicProp "F" (alg ["y"] [] [privateLocalProp "P" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.call (.resolve "Ignore") [.param "y"]) (.num 0))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 7])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18o == "ok raw=42 n=1"
#guard structural hp_18o == some "kl-struct-v1:1:n4:42e0"
#guard cacheEntries hp_18o "P" == some 1
#guard cacheEntries hp_18o "Run" == some 1
#guard cacheTotal hp_18o == some 2

-- HP-18p: a static owner's parameter is refused where a navigated member INVOKES it, never the caller's same-named callable (formerly 2)
def hp_18p : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), publicProp "G" (alg ["y"] [] [publicProp "F" (alg ["n"] [] [] [(.call (.param "y") [.param "n"])])] [.num 0]), publicProp "H" (alg ["y"] [] [] [(.call (.dotCall (.resolve "G") "F" none) [.num 1])])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "H") [.resolve "Inc"])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18p == "err unknownName"
#guard errorObs hp_18p == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheTotal hp_18p == some 0

-- HP-18q: a static owner's parameter is refused where a navigated member TRANSPORTS it (formerly 43)
def hp_18q : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "Ignore" (alg ["z"] [] [] [.num 42]), publicProp "G" (alg ["y"] [] [publicProp "F" (alg ["n"] [] [] [(.binary .add (.call (.resolve "Ignore") [.param "y"]) (.param "n"))])] [.num 0]), publicProp "H" (alg ["y"] [] [] [(.call (.dotCall (.resolve "G") "F" none) [.num 1])])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "H") [.num 7])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18q == "err unknownName"
#guard errorObs hp_18q == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheTotal hp_18q == some 0

-- HP-18r: a falsely exported P = y.string is refused at the intrinsic's receiver
def hp_18r : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["y"] [] [privateProp "P" (alg [] [] [] [(.dotCall (.param "y") "string" none)])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 7])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18r == "err unknownName"
#guard errorObs hp_18r == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_18r "P" == some 0
#guard cacheTotal hp_18r == some 0

-- HP-18s: control: the same P declared local-only reads the receiver's text
def hp_18s : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "F" (alg ["y"] [] [privateLocalProp "P" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.dotCall (.param "y") "string" none)])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 7])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18s == "ok raw='7' n=1"
#guard structural hp_18s == some "kl-struct-v1:1:t1:7"
#guard cacheEntries hp_18s "P" == some 1
#guard cacheEntries hp_18s "Run" == some 1
#guard cacheTotal hp_18s == some 2

-- HP-18t: a falsely exported P = Inc(y*) + 0 is refused at the spread operand
def hp_18t : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), publicProp "F" (alg ["y"] [] [privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "Inc") [(.sequenceSpread (.param "y"))]) (.num 0))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 7])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18t == "err unknownName"
#guard errorObs hp_18t == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_18t "P" == some 0
#guard cacheTotal hp_18t == some 0

-- HP-18u: control: the same P declared local-only spreads the parameter
def hp_18u : Expr :=
  (.algorithmExpr (alg [] [(.algorithmExpr (Algorithm.withParent (some (ScopeCtx.mk none [] [] [publicProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), publicProp "F" (alg ["y"] [] [privateLocalProp "P" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.call (.resolve "Inc") [(.sequenceSpread (.param "y"))]) (.num 0))])] [.resolve "P"])] [] [] none (some (.host 0)))) (alg [] [] [publicProp "Run" (alg [] [] [] [(.call (.resolve "F") [.num 7])])] [])))] [] [.resolve "Run"]))
#guard obs hp_18u == "ok raw=8 n=1"
#guard structural hp_18u == some "kl-struct-v1:1:n3:8e0"
#guard cacheEntries hp_18u "P" == some 1
#guard cacheEntries hp_18u "Run" == some 1
#guard cacheTotal hp_18u == some 2

-- HP-19a: R-1: a falsely exported sibling reusing the call's established alias cell is refused with the alias's localOnlyProperty (formerly S[S[6, 6], S[10, 10]], unrefused)
def hp_19a : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), privateProp "Dbl" (alg ["n"] [] [] [(.binary .mul (.param "n") (.num 2))]), privateProp "Sel" (alg ["k"] [] [] [(.call (.resolve "if") [(.comparison (.param "k") [{ op := .eq, operand := (.num 1) }]), (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.call (.resolve "Cap") [(.call (.resolve "Dbl") [.num 0])])])]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Sel") [.param "y"]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19a == "err localOnlyProperty"
#guard errorObs hp_19a == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard cacheEntries hp_19a "P" == some 0
#guard cacheTotal hp_19a == some 0

-- HP-19b: R-1: the same sibling establishing the cell itself is refused at the written y, the direct read's unknownName (the other row order)
def hp_19b : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), privateProp "Dbl" (alg ["n"] [] [] [(.binary .mul (.param "n") (.num 2))]), privateProp "Sel" (alg ["k"] [] [] [(.call (.resolve "if") [(.comparison (.param "k") [{ op := .eq, operand := (.num 1) }]), (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.call (.resolve "Cap") [(.call (.resolve "Dbl") [.num 0])])])]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Sel") [.param "y"]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19b == "err unknownName"
#guard errorObs hp_19b == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_19b "P" == some 0
#guard cacheTotal hp_19b == some 0

-- HP-19c: R-1: a falsely exported bare read of a parameter-rooted path alias after an attached read is refused (the value route)
def hp_19c : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "G" (alg ["v"] [] [] [(.binary .add (.param "v") (.num 1))]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.param "y") "G" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.resolve "A") (.num 0))])] [(.binary .add (.resolve "A") (.num 0)), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19c == "err localOnlyProperty"
#guard errorObs hp_19c == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard cacheEntries hp_19c "P" == some 0
#guard cacheTotal hp_19c == some 0

-- HP-19d: R-1: a local-only HIT inside the cell's computation is recorded, so the reuse is refused
def hp_19d : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), privateProp "Dbl" (alg ["n"] [] [] [(.binary .mul (.param "n") (.num 2))]), privateProp "Sel" (alg ["k"] [] [] [(.call (.resolve "if") [(.comparison (.param "k") [{ op := .eq, operand := (.num 1) }]), (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.call (.resolve "Cap") [(.call (.resolve "Dbl") [.num 0])])])]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.call (.resolve "Sel") [.param "y"])])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "L") "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.dotCall (.resolve "L") "Algorithm" (some [.num 5])), (.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19d == "err localOnlyProperty"
#guard errorObs hp_19d == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard cacheEntries hp_19d "L" == some 1
#guard cacheEntries hp_19d "P" == some 0
#guard cacheTotal hp_19d == some 1

-- HP-19e: R-1: a cell whose computation reuses another retained cell takes its read, so the reuse is refused
def hp_19e : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), privateProp "Dbl" (alg ["n"] [] [] [(.binary .mul (.param "n") (.num 2))]), privateProp "Sel" (alg ["k"] [] [] [(.call (.resolve "if") [(.comparison (.param "k") [{ op := .eq, operand := (.num 1) }]), (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.call (.resolve "Cap") [(.call (.resolve "Dbl") [.num 0])])])]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Sel") [.param "y"]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "B") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "B") [.num 5]), (.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19e == "err localOnlyProperty"
#guard errorObs hp_19e == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard cacheEntries hp_19e "P" == some 0
#guard cacheTotal hp_19e == some 0

-- HP-19f: R-1 control: an INDEPENDENT local-only alias cell is shared with the falsely exported sibling
def hp_19f : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), privateProp "Dbl" (alg ["n"] [] [] [(.binary .mul (.param "n") (.num 2))]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "if") [.boolLiteral true, (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.call (.resolve "Cap") [(.call (.resolve "Dbl") [.param "y"])])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19f == "ok raw=S[S[6, 6], S[6, 6]] n=2"
#guard structural hp_19f == some "kl-struct-v1:3:n3:6e0s2:0,0,;s2:1,1,;"
#guard cacheEntries hp_19f "P" == some 2
#guard cacheTotal hp_19f == some 2

-- HP-19g: R-1 control: the witness correctly classified keeps S[S[6, 6], S[10, 10]]
def hp_19g : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), privateProp "Dbl" (alg ["n"] [] [] [(.binary .mul (.param "n") (.num 2))]), privateProp "Sel" (alg ["k"] [] [] [(.call (.resolve "if") [(.comparison (.param "k") [{ op := .eq, operand := (.num 1) }]), (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.call (.resolve "Cap") [(.call (.resolve "Dbl") [.num 0])])])]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Sel") [.param "y"]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "P" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [(.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19g == "ok raw=S[S[6, 6], S[10, 10]] n=2"
#guard structural hp_19g == some "kl-struct-v1:5:n3:6e0s2:0,0,;n3:1e1s2:2,2,;s2:1,3,;"
#guard cacheEntries hp_19g "P" == some 2
#guard cacheTotal hp_19g == some 2

-- HP-19h: R-1: a falsely exported sibling reading a lazy position of a reused cell is refused at the deferred read (formerly S[S[2, 2], S[2, 3]], unrefused)
def hp_19h : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 5]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.index (.resolve "A") [.num 0]) (.num 0))]), { (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.index (.resolve "P") [.num 0]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["v"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "y"))]))]))])) with requiredOwnerDepths := some [("y", some 1)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])])) with requiredOwnerDepths := some [("y", some 0)] }] [(.dotCall (.resolve "A") "count" none), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19h == "err unknownName"
#guard errorObs hp_19h == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_19h "P" == some 0
#guard cacheEntries hp_19h "Z" == some 1
#guard cacheTotal hp_19h == some 1

-- HP-19i: R-1: the same sibling establishing the cell itself is refused at the same deferred read (the other row order)
def hp_19i : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 5]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.index (.resolve "A") [.num 0]) (.num 0))]), { (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.index (.resolve "P") [.num 0]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["v"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "y"))]))]))])) with requiredOwnerDepths := some [("y", some 1)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "P", (.dotCall (.resolve "A") "count" none)])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19i == "err unknownName"
#guard errorObs hp_19i == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_19i "P" == some 0
#guard cacheEntries hp_19i "Z" == some 1
#guard cacheTotal hp_19i == some 1

-- HP-19j: R-1 (owner decision): after the sibling read only the count, the attached row's later read of a position uses the row's own input
def hp_19j : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 5]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.dotCall (.resolve "A") "count" none) (.num 0))]), { (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.index (.resolve "P") [.num 0]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["v"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "y"))]))]))])) with requiredOwnerDepths := some [("y", some 1)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])])) with requiredOwnerDepths := some [("y", some 0)] }] [(.dotCall (.resolve "A") "count" none), .resolve "P", (.index (.resolve "A") [.num 1])])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19j == "ok raw=S[S[2, 2, 3], S[2, 2, 4]] n=2"
#guard structural hp_19j == some "kl-struct-v1:6:n3:2e0n3:3e0s3:0,0,1,;n3:4e0s3:0,0,3,;s2:2,4,;"
#guard cacheEntries hp_19j "P" == some 2
#guard cacheEntries hp_19j "Z" == some 2
#guard cacheTotal hp_19j == some 4

-- HP-19k: R-1: a lazy value carried out of the sibling unread and read by the ROW is the row's own read
def hp_19k : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 5]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.dotCall (.resolve "A") "take" (some [.num 2]))]), { (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.index (.resolve "P") [.num 0]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["v"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "y"))]))]))])) with requiredOwnerDepths := some [("y", some 1)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])])) with requiredOwnerDepths := some [("y", some 0)] }] [(.dotCall (.resolve "A") "count" none), (.index (.resolve "P") [.num 0])])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19k == "ok raw=S[S[2, 2], S[2, 3]] n=2"
#guard structural hp_19k == some "kl-struct-v1:5:n3:2e0s2:0,0,;n3:3e0s2:0,2,;s2:1,3,;"
#guard cacheEntries hp_19k "P" == some 2
#guard cacheEntries hp_19k "Z" == some 2
#guard cacheTotal hp_19k == some 4

-- HP-19l: R-1: a cell whose VALUE is another cell's lazy value is refused at the deferred read
def hp_19l : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 5]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Mk2") [.num 0]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.index (.resolve "A") [.num 0]) (.num 0))]), { (privateLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["v"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "y"))]))]))])) with requiredOwnerDepths := some [("y", some 1)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "Mk2" (.localCapturedAncestorParams ["y"]) (alg ["v"] [] [{ (privateLocalProp "W" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.resolve "B"])) with requiredOwnerDepths := some [("y", some 1)] }] [(.call (.resolve "Cap") [(.call (.resolve "W") [])])])) with requiredOwnerDepths := some [("y", some 0)] }] [(.dotCall (.resolve "B") "count" none), (.dotCall (.resolve "A") "count" none), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19l == "err unknownName"
#guard errorObs hp_19l == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_19l "P" == some 0
#guard cacheEntries hp_19l "W" == some 1
#guard cacheEntries hp_19l "Z" == some 1
#guard cacheTotal hp_19l == some 2

-- HP-19m: R-1 control: an INDEPENDENT lazy value is shared with the falsely exported sibling
def hp_19m : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Dbl" (alg ["n"] [] [] [(.binary .mul (.param "n") (.num 2))]), privateProp "Z0" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]))]))]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "if") [.boolLiteral true, (.call (.resolve "Cap") [(.call (.resolve "Z0") [])]), (.call (.resolve "Cap") [(.call (.resolve "Dbl") [.param "y"])])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.index (.resolve "A") [.num 0]) (.num 0))])] [(.dotCall (.resolve "A") "count" none), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19m == "ok raw=S[S[2, 2], S[2, 2]] n=2"
#guard structural hp_19m == some "kl-struct-v1:3:n3:2e0s2:0,0,;s2:1,1,;"
#guard cacheEntries hp_19m "P" == some 2
#guard cacheEntries hp_19m "Z0" == some 1
#guard cacheTotal hp_19m == some 3

-- HP-19n: R-1 control: the lazy witness correctly classified keeps S[S[2, 2], S[2, 3]]
def hp_19n : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 5]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "P" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.index (.resolve "A") [.num 0]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.index (.resolve "P") [.num 0]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["v"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "y"))]))]))])) with requiredOwnerDepths := some [("y", some 1)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])])) with requiredOwnerDepths := some [("y", some 0)] }] [(.dotCall (.resolve "A") "count" none), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19n == "ok raw=S[S[2, 2], S[2, 3]] n=2"
#guard structural hp_19n == some "kl-struct-v1:5:n3:2e0s2:0,0,;n3:3e0s2:0,2,;s2:1,3,;"
#guard cacheEntries hp_19n "P" == some 2
#guard cacheEntries hp_19n "Z" == some 2
#guard cacheTotal hp_19n == some 4

-- HP-19o: R-1 (owner decision): the count-only sibling FIRST establishes the cell at the call's own watermark, and the row's later position read uses the row's own input
def hp_19o : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 5]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.dotCall (.resolve "A") "count" none) (.num 0))]), { (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.index (.resolve "P") [.num 0]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["v"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "y"))]))]))])) with requiredOwnerDepths := some [("y", some 1)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "P", (.dotCall (.resolve "A") "count" none), (.index (.resolve "A") [.num 1])])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19o == "ok raw=S[S[2, 2, 3], S[2, 2, 4]] n=2"
#guard structural hp_19o == some "kl-struct-v1:6:n3:2e0n3:3e0s3:0,0,1,;n3:4e0s3:0,0,3,;s2:2,4,;"
#guard cacheEntries hp_19o "P" == some 2
#guard cacheEntries hp_19o "Z" == some 2
#guard cacheTotal hp_19o == some 4

-- HP-19p: R-1: a warm cell still enforces the reader's access — the sibling demands a position the row already read, and its reuse is refused
def hp_19p : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 5]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.index (.resolve "A") [.num 1]) (.num 0))]), { (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.index (.resolve "P") [.num 0]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["v"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "y"))]))]))])) with requiredOwnerDepths := some [("y", some 1)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])])) with requiredOwnerDepths := some [("y", some 0)] }] [(.dotCall (.resolve "A") "count" none), (.index (.resolve "A") [.num 1]), .resolve "P"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19p == "err localOnlyProperty"
#guard errorObs hp_19p == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard cacheEntries hp_19p "P" == some 0
#guard cacheEntries hp_19p "Z" == some 1
#guard cacheTotal hp_19p == some 1

-- HP-19q: R-1: a second falsely exported sibling that demands the escaped position is refused at the deferred read
def hp_19q : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 5]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.dotCall (.resolve "A") "take" (some [.num 2]))]), privateProp "Q" (alg [] [] [] [(.binary .add (.index (.resolve "P") [.num 0]) (.num 0))]), { (privateLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["v"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "y"))]))]))])) with requiredOwnerDepths := some [("y", some 1)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])])) with requiredOwnerDepths := some [("y", some 0)] }] [(.dotCall (.resolve "A") "count" none), .resolve "Q"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_19q == "err unknownName"
#guard errorObs hp_19q == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_19q "P" == some 1
#guard cacheEntries hp_19q "Q" == some 0
#guard cacheEntries hp_19q "Z" == some 1
#guard cacheTotal hp_19q == some 2

-- HP-19r: R-1 control (correctly classified): a list forwarded through a second root alias keeps its freshly owned input
def hp_19r : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "A" (.alias none [] [] ((.dotCall (.call (.resolve "Build2") [.num 0]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.dotCall (.resolve "A") "count" none) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Build" (alg ["z"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["z"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "z"))]))]))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])]), privateProp "Build2" (alg ["v"] [] [privateProp "W" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.resolve "B"])] [(.call (.resolve "Cap") [(.call (.resolve "W") [])])])] [(.dotCall (.resolve "B") "count" none), (.dotCall (.resolve "A") "count" none), .resolve "Observe", (.index (.resolve "A") [.num 0])]))
#guard obs hp_19r == "ok raw=S[2, 2, 2, 6] n=4"
#guard structural hp_19r == some "kl-struct-v1:3:n3:2e0n3:6e0s4:0,0,0,1,;"
#guard cacheEntries hp_19r "Observe" == some 1
#guard cacheEntries hp_19r "W" == some 1
#guard cacheEntries hp_19r "Z" == some 1
#guard cacheTotal hp_19r == some 3

-- HP-19s: R-1 control (correctly classified): the same with the count reads in the other order
def hp_19s : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "A" (.alias none [] [] ((.dotCall (.call (.resolve "Build2") [.num 0]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.dotCall (.resolve "A") "count" none) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Build" (alg ["z"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["z"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "z"))]))]))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])]), privateProp "Build2" (alg ["v"] [] [privateProp "W" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.resolve "B"])] [(.call (.resolve "Cap") [(.call (.resolve "W") [])])])] [(.dotCall (.resolve "A") "count" none), (.dotCall (.resolve "B") "count" none), .resolve "Observe", (.index (.resolve "A") [.num 0])]))
#guard obs hp_19s == "ok raw=S[2, 2, 2, 6] n=4"
#guard structural hp_19s == some "kl-struct-v1:3:n3:2e0n3:6e0s4:0,0,0,1,;"
#guard cacheEntries hp_19s "Observe" == some 1
#guard cacheEntries hp_19s "W" == some 1
#guard cacheEntries hp_19s "Z" == some 1
#guard cacheTotal hp_19s == some 3

-- HP-19t: R-1 control (correctly classified): the same with the exported reader establishing the second alias
def hp_19t : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "A" (.alias none [] [] ((.dotCall (.call (.resolve "Build2") [.num 0]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.dotCall (.resolve "A") "count" none) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Build" (alg ["z"] [] [{ (privateLocalProp "Z" (.localCapturedAncestorParams ["z"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "z"))]))]))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "Z") [])])]), privateProp "Build2" (alg ["v"] [] [privateProp "W" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.resolve "B"])] [(.call (.resolve "Cap") [(.call (.resolve "W") [])])])] [(.dotCall (.resolve "B") "count" none), .resolve "Observe", (.index (.resolve "A") [.num 0])]))
#guard obs hp_19t == "ok raw=S[2, 2, 6] n=3"
#guard structural hp_19t == some "kl-struct-v1:3:n3:2e0n3:6e0s3:0,0,1,;"
#guard cacheEntries hp_19t "Observe" == some 1
#guard cacheEntries hp_19t "W" == some 1
#guard cacheEntries hp_19t "Z" == some 1
#guard cacheTotal hp_19t == some 3

-- HP-19u: R-1: an admitted access of a local-only member is the cell's input read, so the sibling's reuse is refused although the member's body never reads y
def hp_19u : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [privateProp "Box" (alg [] [] [{ (publicLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["x"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.binary .add (.param "x") (.num 1)), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.dotCall (.resolve "Box") "G" (some [.num 0]))]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_19u == "err localOnlyProperty"
#guard errorObs hp_19u == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard cacheEntries hp_19u "P" == some 0
#guard cacheTotal hp_19u == some 0

-- HP-19v: R-1: the same sibling establishing the cell is refused at the member access (the other row order)
def hp_19v : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [privateProp "Box" (alg [] [] [{ (publicLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["x"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.binary .add (.param "x") (.num 1)), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.dotCall (.resolve "Box") "G" (some [.num 0]))]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_19v == "err localOnlyProperty"
#guard errorObs hp_19v == .matched (some { kind := "localOnlyProperty", names := ["G", "captured"], counts := [] })
#guard cacheEntries hp_19v "P" == some 0
#guard cacheTotal hp_19v == some 0

-- HP-19w: R-1 control: the member witness correctly classified keeps S[6, 6]
def hp_19w : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [privateProp "Box" (alg [] [] [{ (publicLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["x"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.binary .add (.param "x") (.num 1)), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.dotCall (.resolve "Box") "G" (some [.num 0]))]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "P" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [(.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_19w == "ok raw=S[6, 6] n=1"
#guard structural hp_19w == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_19w "P" == some 1
#guard cacheTotal hp_19w == some 1

-- HP-19x: R-1: the same through a CALL of the local-only member as the cell's receiver
def hp_19x : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "F" (alg ["y"] [] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["k"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.dotCall (.resolve "Box") "Mk" (some [.num 0])) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_19x == "err localOnlyProperty"
#guard errorObs hp_19x == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard cacheEntries hp_19x "P" == some 0
#guard cacheTotal hp_19x == some 0

-- HP-19y: R-1: the member call with the sibling first is refused at the member access
def hp_19y : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "F" (alg ["y"] [] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Mk" (.localCapturedAncestorParams ["y"]) (alg ["k"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.dotCall (.resolve "Box") "Mk" (some [.num 0])) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_19y == "err localOnlyProperty"
#guard errorObs hp_19y == .matched (some { kind := "localOnlyProperty", names := ["Mk", "captured"], counts := [] })
#guard cacheEntries hp_19y "P" == some 0
#guard cacheTotal hp_19y == some 0

-- HP-19z: R-1: a cold VALUE channel of a cell known to depend on y is refused before it runs
def hp_19z : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Effect" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.call (.resolve "tick") [])]), privateProp "Sel" (alg ["k"] [] [] [(.call (.resolve "if") [(.comparison (.param "k") [{ op := .eq, operand := (.num 1) }]), (.call (.resolve "Cap") [(.call (.resolve "Effect") [])]), (.call (.resolve "Cap") [(.call (.resolve "Effect") [])])])]), privateProp "Same" (alg ["f", "f"] [] [] [.num 0]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Sel") [.param "y"]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.resolve "A") (.num 0))])] [(.call (.resolve "Same") [.resolve "A", .resolve "A"]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_19z == "err localOnlyProperty"
#guard errorObs hp_19z == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard cacheEntries hp_19z "P" == some 0
#guard cacheTotal hp_19z == some 0

-- HP-20a: R-1 (open route): an open-provided local-only member's admitted access is the cell's input read, so the sibling's reuse is refused (formerly S[6, 6], unrefused)
def hp_20a : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "Box"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["x"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.binary .add (.param "x") (.num 1)), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_20a == "err localOnlyProperty"
#guard errorObs hp_20a == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard cacheEntries hp_20a "P" == some 0
#guard cacheTotal hp_20a == some 0

-- HP-20b: R-1 (open route): the same sibling establishing the cell is refused at the member access in the row (the other row order)
def hp_20b : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "Box"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["x"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.binary .add (.param "x") (.num 1)), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_20b == "err localOnlyProperty"
#guard errorObs hp_20b == .matched (some { kind := "localOnlyProperty", names := ["G", "captured"], counts := [] })
#guard cacheEntries hp_20b "P" == some 0
#guard cacheTotal hp_20b == some 0

-- HP-20c: R-1 control: the open witness correctly classified keeps S[6, 6]
def hp_20c : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "Box"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["x"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.binary .add (.param "x") (.num 1)), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "P" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_20c == "ok raw=S[6, 6] n=1"
#guard structural hp_20c == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_20c "P" == some 1
#guard cacheTotal hp_20c == some 1

-- HP-20d: R-1 (open route): the access recorded on a cell whose reuse the row's cell makes is forwarded, so the sibling's reuse is refused
def hp_20d : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "Box"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["x"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.binary .add (.param "x") (.num 1)), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "B" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "B") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "B") [.num 5]), (.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_20d == "err localOnlyProperty"
#guard errorObs hp_20d == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard cacheEntries hp_20d "P" == some 0
#guard cacheTotal hp_20d == some 0

-- HP-20e: R-1 (open route): the forwarded shape with the sibling first is refused at the member access
def hp_20e : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "Box"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["x"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.binary .add (.param "x") (.num 1)), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "B" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "B") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "B") [.num 5]), (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_20e == "err localOnlyProperty"
#guard errorObs hp_20e == .matched (some { kind := "localOnlyProperty", names := ["G", "captured"], counts := [] })
#guard cacheEntries hp_20e "P" == some 0
#guard cacheTotal hp_20e == some 0

-- HP-20f: R-1 (open route): a cold VALUE channel of a cell known to depend on an open access is refused before its effect runs
def hp_20f : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Effect" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.call (.resolve "tick") [])]), privateProp "Same" (alg ["f", "f"] [] [] [.num 0]), privateProp "F" (alg ["y"] [.resolve "Box"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sel" (.localCapturedAncestorParams ["y"]) (alg ["k"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "Cap") [(.call (.resolve "Effect") [])]), (.binary .add (.param "y") (.num 0))])])) with requiredOwnerDepths := some [("y", some 1)] }] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Sel") [.num 1]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.resolve "A") (.num 0))])] [(.call (.resolve "Same") [.resolve "A", .resolve "A"]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_20f == "err localOnlyProperty"
#guard errorObs hp_20f == .matched (some { kind := "localOnlyProperty", names := ["A", "captured"], counts := [] })
#guard ((runCountedM hp_20f).runState EvalState.empty).2.tickCounter == 0
#guard cacheEntries hp_20f "P" == some 0
#guard cacheTotal hp_20f == some 0

-- HP-20g: R-1 control: an EXPORTED member of a local-only provider is no input; the exported sibling shares the cell
def hp_20g : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "Box"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "H" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.param "y") (.num 0))])) with requiredOwnerDepths := some [("y", some 1)] }, publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), privateProp "A" (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none))), privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_20g == "ok raw=S[6, 6] n=1"
#guard structural hp_20g == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_20g "P" == some 1
#guard cacheTotal hp_20g == some 1

-- HP-20h: R-1 open-target qualification: a local-only open target's path step is not recorded — the sibling's reuse is not refused (attached read first)
def hp_20h : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none)] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_20h == "ok raw=S[6, 6] n=1"
#guard structural hp_20h == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_20h "P" == some 1
#guard cacheTotal hp_20h == some 1

-- HP-20i: R-1 open-target qualification: the same with the sibling first
def hp_20i : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none)] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_20i == "ok raw=S[6, 6] n=1"
#guard structural hp_20i == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_20i "P" == some 1
#guard cacheTotal hp_20i == some 1

-- HP-22a: R-1 open-target decision: the sibling's own direct use through open Box.Sub is refused at the step Sub
def hp_22a : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none)] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "K" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "G") [.num 5]) (.num 0))])] [.resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22a == "err localOnlyProperty"
#guard errorObs hp_22a == .matched (some { kind := "localOnlyProperty", names := ["Sub", "captured"], counts := [] })
#guard cacheEntries hp_22a "P" == some 0
#guard cacheTotal hp_22a == some 0

-- HP-22b: R-1 open-target decision: open L with L = Box.Sub, attached read first — the reuse is not refused
def hp_22b : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "L"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "K" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "Box") "Sub" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22b == "ok raw=S[6, 6] n=1"
#guard structural hp_22b == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_22b "P" == some 1
#guard cacheTotal hp_22b == some 1

-- HP-22c: R-1 open-target decision: open L with L = Box.Sub, the sibling first — not refused
def hp_22c : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "L"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "K" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "Box") "Sub" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22c == "ok raw=S[6, 6] n=1"
#guard structural hp_22c == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_22c "P" == some 1
#guard cacheTotal hp_22c == some 1

-- HP-22d: R-1 open-target decision: the sibling's own direct use through open L is refused at the reference's step Sub
def hp_22d : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "L"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "K" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "Box") "Sub" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "G") [.num 5]) (.num 0))])] [.resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22d == "err localOnlyProperty"
#guard errorObs hp_22d == .matched (some { kind := "localOnlyProperty", names := ["Sub", "captured"], counts := [] })
#guard cacheEntries hp_22d "P" == some 0
#guard cacheTotal hp_22d == some 0

-- HP-22e: R-1 open-target decision: the row reads through the level first (memoized in C#), attached read of the cell next — not refused
def hp_22e : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none)] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "K" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "G") [.num 1]), (.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22e == "ok raw=S[2, 6, 6] n=1"
#guard structural hp_22e == some "kl-struct-v1:3:n3:2e0n3:6e0s3:0,1,1,;"
#guard cacheEntries hp_22e "P" == some 1
#guard cacheTotal hp_22e == some 1

-- HP-22f: R-1 open-target decision: the row reads through the level first, the sibling establishes the cell — not refused
def hp_22f : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none)] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "K" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "G") [.num 1]), .resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22f == "ok raw=S[2, 6, 6] n=1"
#guard structural hp_22f == some "kl-struct-v1:3:n3:2e0n3:6e0s3:0,1,1,;"
#guard cacheEntries hp_22f "P" == some 1
#guard cacheTotal hp_22f == some 1

-- HP-22g: R-1 open-target decision: G from the self-contained Other beside a local-only sibling target, attached read first — not refused
def hp_22g : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none), .resolve "Other"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "H" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [(.call (.resolve "A") [.num 5]), .resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22g == "ok raw=S[6, 6] n=1"
#guard structural hp_22g == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_22g "P" == some 1
#guard cacheTotal hp_22g == some 1

-- HP-22h: R-1 open-target decision: the unrelated local-only sibling target, the sibling first — not refused
def hp_22h : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none), .resolve "Other"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "H" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22h == "ok raw=S[6, 6] n=1"
#guard structural hp_22h == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_22h "P" == some 1
#guard cacheTotal hp_22h == some 1

-- HP-22i: R-1 open-target decision: the sibling's own direct use is refused at the unrelated target's step (fail-fast resolution)
def hp_22i : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none), .resolve "Other"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "H" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "G") [.num 5]) (.num 0))])] [.resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22i == "err localOnlyProperty"
#guard errorObs hp_22i == .matched (some { kind := "localOnlyProperty", names := ["Sub", "captured"], counts := [] })
#guard cacheEntries hp_22i "P" == some 0
#guard cacheTotal hp_22i == some 0

-- HP-22j: R-1 open-target decision: a consulted level that does not decide the name (the root's open Other does), the sibling first — not refused
def hp_22j : Expr :=
  (.algorithmExpr (alg [] [.resolve "Other"] [privateProp "Other" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none)] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "H" (alg ["x"] [] [] [.param "x"])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22j == "ok raw=S[6, 6] n=1"
#guard structural hp_22j == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_22j "P" == some 1
#guard cacheTotal hp_22j == some 1

-- HP-22k: R-1 open-target decision: the sibling's own direct use is refused at the consulted level's step
def hp_22k : Expr :=
  (.algorithmExpr (alg [] [.resolve "Other"] [privateProp "Other" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none)] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "H" (alg ["x"] [] [] [.param "x"])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "G") [.num 5]) (.num 0))])] [.resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22k == "err localOnlyProperty"
#guard errorObs hp_22k == .matched (some { kind := "localOnlyProperty", names := ["Sub", "captured"], counts := [] })
#guard cacheEntries hp_22k "P" == some 0
#guard cacheTotal hp_22k == some 0

-- HP-22l: R-1 open-target decision: a sibling target that can never pass fails every lookup of its level (genuinely exported P)
def hp_22l : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "Other", (.dotCall (.resolve "Lib") "Inner" none)] [privateProp "Other" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), privateProp "A" (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none))), privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))]), privateProp "Lib" (alg ["p"] [] [{ (publicLocalProp "Inner" (.localCapturedAncestorParams ["p"]) (.alias none [] [publicProp "Z" (alg [] [] [] [.num 1])] (.param "p") none false)) with requiredOwnerDepths := some [("p", some 0)] }] [.param "p"])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22l == "err localOnlyProperty"
#guard errorObs hp_22l == .matched (some { kind := "localOnlyProperty", names := ["Inner", "captured"], counts := [] })
#guard cacheEntries hp_22l "P" == some 0
#guard cacheTotal hp_22l == some 0

-- HP-22m: R-1 open-target decision control: F's own G shadows the open-provided one, no open is consulted; the genuinely exported sibling shares
def hp_22m : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none)] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "K" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), privateProp "A" (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none))), privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))]), privateProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22m == "ok raw=S[6, 6] n=1"
#guard structural hp_22m == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_22m "P" == some 1
#guard cacheTotal hp_22m == some 1

-- HP-22n: R-1 open-target decision: two providers offer G (host tree), the sibling first — the lookup's ambiguousOpen
def hp_22n : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none), .resolve "Other"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22n == "err ambiguousOpen"
#guard errorObs hp_22n == .matched (some { kind := "ambiguousOpen", names := ["G"], counts := [] })
#guard cacheEntries hp_22n "P" == some 0
#guard cacheTotal hp_22n == some 0

-- HP-22o: R-1 open-target decision: the falsely exported sibling's own direct use on the ambiguous host tree is refused at Sub first
def hp_22o : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none), .resolve "Other"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "G") [.num 5]) (.num 0))])] [.resolve "P"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22o == "err localOnlyProperty"
#guard errorObs hp_22o == .matched (some { kind := "localOnlyProperty", names := ["Sub", "captured"], counts := [] })
#guard cacheEntries hp_22o "P" == some 0
#guard cacheTotal hp_22o == some 0

-- HP-22p: R-1 open-target decision control: an exported target step is admitted through no activation; the genuinely exported sibling shares
def hp_22p : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none)] [privateProp "Box" (alg [] [] [publicProp "Sub" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (publicLocalProp "H" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.param "y") (.num 0))])) with requiredOwnerDepths := some [("y", some 1)] }] []), privateProp "A" (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none))), privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22p == "ok raw=S[6, 6] n=1"
#guard structural hp_22p == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_22p "P" == some 1
#guard cacheTotal hp_22p == some 1

-- HP-22q: R-1 open-target decision control: the same exported step through L = Box.Sub
def hp_22q : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "L"] [privateProp "Box" (alg [] [] [publicProp "Sub" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (publicLocalProp "H" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.param "y") (.num 0))])) with requiredOwnerDepths := some [("y", some 1)] }] []), privateProp "L" (.alias none [] [] ((.dotCall (.resolve "Box") "Sub" none))), privateProp "A" (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none))), privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22q == "ok raw=S[6, 6] n=1"
#guard structural hp_22q == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_22q "P" == some 1
#guard cacheTotal hp_22q == some 1

-- HP-22r: R-1 open-target decision control: a nearer level decides the name, F's local-only target is never consulted; the genuinely exported sibling shares
def hp_22r : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Box") "Sub" none)] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), privateProp "A" (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 0]) "Algorithm" none))), privateProp "P" (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))]), privateProp "Mk" (alg ["k"] [.resolve "Other"] [] [(.call (.resolve "Cap") [(.call (.resolve "G") [.param "k"])])])] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22r == "ok raw=S[6, 6] n=1"
#guard structural hp_22r == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_22r "P" == some 1
#guard cacheTotal hp_22r == some 1

-- HP-22s: R-1 open-target decision control: correctly classified, the local-only sibling reads the cell through open L attached
def hp_22s : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [.resolve "L"] [privateProp "Box" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "G" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "K" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), { (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "Box") "Sub" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "P" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.call (.resolve "A") [.num 5]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "P", (.call (.resolve "A") [.num 5])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_22s == "ok raw=S[6, 6] n=1"
#guard structural hp_22s == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_22s "P" == some 1
#guard cacheTotal hp_22s == some 1

-- HP-21a: the escaped element projects its alias under the element's detached watermark and refuses y before tick
def hp_21a : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Dbl" (alg ["x"] [] [] [(.binary .mul (.param "x") (.num 2))]), privateProp "Sel" (alg ["k"] [] [] [(.call (.resolve "if") [(.comparison (.binary .add (.param "k") (.call (.resolve "tick") [])) [{ op := .eq, operand := (.num 2) }]), (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.call (.resolve "Cap") [(.call (.resolve "Dbl") [.num 0])])])]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Sel") [.param "y"]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "P" (alg [] [] [] [(.listLiteral [(.call (.resolve "A") [.num 5])])])] [(.index (.resolve "P") [.num 0])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_21a == "err unknownName"
#guard errorObs hp_21a == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard ((runCountedM hp_21a).runState EvalState.empty).2.tickCounter == 0
#guard cacheEntries hp_21a "P" == some 1
#guard cacheTotal hp_21a == some 1

-- HP-23a: returned callable: the row establishes B first, the detached Observe reads Build's z through it (formerly unknownName z)
def hp_23a : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Build" (alg ["z"] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["z"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.param "z"))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])] [(.call (.resolve "B") [.num 2]), .resolve "Observe"]))
#guard obs hp_23a == "ok raw=S[7, 6] n=2"
#guard structural hp_23a == some "kl-struct-v1:3:n3:7e0n3:6e0s2:0,1,;"
#guard cacheEntries hp_23a "Observe" == some 1
#guard cacheTotal hp_23a == some 1

-- HP-23b: returned callable: the detached Observe first (S[6, 7] before and after)
def hp_23b : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Build" (alg ["z"] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["z"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.param "z"))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])] [.resolve "Observe", (.call (.resolve "B") [.num 2])]))
#guard obs hp_23b == "ok raw=S[6, 7] n=2"
#guard structural hp_23b == some "kl-struct-v1:3:n3:6e0n3:7e0s2:0,1,;"
#guard cacheEntries hp_23b "Observe" == some 1
#guard cacheTotal hp_23b == some 1

-- HP-23c: returned callable inside a call of F, the row first: F's activation encloses Observe, Build's does not
def hp_23c : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), privateProp "Build" (alg ["z"] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["z"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.param "z"))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])] [(.call (.resolve "B") [.num 2]), .resolve "Observe", .param "y"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_23c == "ok raw=S[7, 6, 1] n=1"
#guard structural hp_23c == some "kl-struct-v1:4:n3:7e0n3:6e0n3:1e0s3:0,1,2,;"
#guard cacheEntries hp_23c "Observe" == some 1
#guard cacheTotal hp_23c == some 1

-- HP-23d: returned callable inside fresh calls F(1), F(2), the sibling first
def hp_23d : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), privateProp "Build" (alg ["z"] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["z"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.param "z"))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])] [.resolve "Observe", (.call (.resolve "B") [.num 2]), .param "y"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_23d == "ok raw=S[S[6, 7, 1], S[6, 7, 2]] n=2"
#guard structural hp_23d == some "kl-struct-v1:7:n3:6e0n3:7e0n3:1e0s3:0,1,2,;n3:2e0s3:0,1,4,;s2:3,5,;"
#guard cacheEntries hp_23d "Observe" == some 2
#guard cacheTotal hp_23d == some 2

-- HP-23e: the callable of a call-reference value, C.Algorithm(2) first
def hp_23e : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "C" (alg [] [] [] [(.call (.resolve "Build") [.num 5])]), privateProp "Observe" (alg [] [] [] [(.binary .add (.dotCall (.resolve "C") "Algorithm" (some [.num 1])) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Build" (alg ["z"] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["z"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.param "z"))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])] [(.dotCall (.resolve "C") "Algorithm" (some [.num 2])), .resolve "Observe"]))
#guard obs hp_23e == "ok raw=S[7, 6] n=2"
#guard structural hp_23e == some "kl-struct-v1:3:n3:7e0n3:6e0s2:0,1,;"
#guard cacheEntries hp_23e "C" == some 1
#guard cacheEntries hp_23e "Observe" == some 1
#guard cacheTotal hp_23e == some 2

-- HP-23f: a local-only member of the callable's level, keyed on Build's activation, read by the callable for the detached Observe
def hp_23f : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Build" (alg ["z"] [] [{ (privateLocalProp "L" (.localCapturedAncestorParams ["z"]) (alg [] [] [] [(.binary .add (.param "z") (.num 1))])) with requiredOwnerDepths := some [("z", some 0)] }, { (privateLocalProp "G" (.localCapturedAncestorParams ["z"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.resolve "L"))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])] [(.call (.resolve "B") [.num 2]), .resolve "Observe"]))
#guard obs hp_23f == "ok raw=S[8, 7] n=2"
#guard structural hp_23f == some "kl-struct-v1:3:n3:8e0n3:7e0s2:0,1,;"
#guard cacheEntries hp_23f "L" == some 1
#guard cacheEntries hp_23f "Observe" == some 1
#guard cacheTotal hp_23f == some 2

-- HP-23g: R-1: a local-only alias of the callable's level read Mk's y; the reuse judgment admits the detached Observe (dependsFor)
def hp_23g : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 1]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 5]) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), privateProp "Dbl" (alg ["n"] [] [] [(.binary .mul (.param "n") (.num 2))]), privateProp "Sel" (alg ["k"] [] [] [(.call (.resolve "if") [(.comparison (.param "k") [{ op := .eq, operand := (.num 1) }]), (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.call (.resolve "Cap") [(.call (.resolve "Dbl") [.num 0])])])]), privateProp "Mk" (alg ["y"] [] [{ (privateLocalProp "C" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Sel") [.param "y"]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["x"] [] [] [(.binary .add (.call (.resolve "C") [.param "x"]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])] [(.call (.resolve "B") [.num 5]), .resolve "Observe"]))
#guard obs hp_23g == "ok raw=S[6, 6] n=2"
#guard structural hp_23g == some "kl-struct-v1:2:n3:6e0s2:0,0,;"
#guard cacheEntries hp_23g "Observe" == some 1
#guard cacheTotal hp_23g == some 1

-- HP-23h: R-1: a retained cell's row invokes another cell's returned callable; the detached Observe reuses it
def hp_23h : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B2" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Re") [.num 1]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Build" (alg ["z"] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["z"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.param "z"))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])]), privateProp "Re" (alg ["w"] [] [{ (privateLocalProp "u" (.localCapturedAncestorParams ["w"]) (alg [] [] [] [(.call (.resolve "B2") [.param "w"])])) with requiredOwnerDepths := some [("w", some 0)] }, { (privateLocalProp "H" (.localCapturedAncestorParams ["w"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.param "w"))])) with requiredOwnerDepths := some [("w", some 0)] }] [(.call (.resolve "if") [(.comparison (.resolve "u") [{ op := .gt, operand := (.num 0) }]), (.call (.resolve "Cap") [(.call (.resolve "H") [.num 0])]), (.call (.resolve "Cap") [(.call (.resolve "H") [.num 1])])])])] [(.call (.resolve "B2") [.num 1]), (.call (.resolve "B") [.num 2]), .resolve "Observe"]))
#guard obs hp_23h == "ok raw=S[6, 3, 2] n=3"
#guard structural hp_23h == some "kl-struct-v1:4:n3:6e0n3:3e0n3:2e0s3:0,1,2,;"
#guard cacheEntries hp_23h "Observe" == some 1
#guard cacheEntries hp_23h "u" == some 1
#guard cacheTotal hp_23h == some 2

-- HP-23i: the callable reads F's y too: forced exported, the detached Observe is refused at y (the row first)
def hp_23i : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), { (privateLocalProp "Build" (.localCapturedAncestorParams ["y"]) (alg ["z"] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["y", "z"]) (alg ["x"] [] [] [(.binary .add (.binary .add (.param "x") (.param "z")) (.param "y"))])) with requiredOwnerDepths := some [("y", some 1), ("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])) with requiredOwnerDepths := some [("y", some 0)] }] [(.call (.resolve "B") [.num 2]), .resolve "Observe"])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_23i == "err unknownName"
#guard errorObs hp_23i == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_23i "Observe" == some 0
#guard cacheTotal hp_23i == some 0

-- HP-23j: the callable reads F's y too: forced exported, refused at y (the sibling first)
def hp_23j : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), { (privateLocalProp "Build" (.localCapturedAncestorParams ["y"]) (alg ["z"] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["y", "z"]) (alg ["x"] [] [] [(.binary .add (.binary .add (.param "x") (.param "z")) (.param "y"))])) with requiredOwnerDepths := some [("y", some 1), ("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "Observe", (.call (.resolve "B") [.num 2])])] [(.call (.resolve "F") [.num 1])]))
#guard obs hp_23j == "err unknownName"
#guard errorObs hp_23j == .matched (some { kind := "unknownName", names := ["y"], counts := [] })
#guard cacheEntries hp_23j "Observe" == some 0
#guard cacheTotal hp_23j == some 0

-- HP-23k: a falsely exported Q declared in the callable's level, read through the callable, is refused at z
def hp_23k : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Build" (alg ["z"] [] [privateProp "Q" (alg [] [] [] [(.binary .add (.param "z") (.num 1))]), { (privateLocalProp "G" (.localCapturedAncestorParams ["z"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.resolve "Q"))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])] [(.call (.resolve "B") [.num 2]), .resolve "Observe"]))
#guard obs hp_23k == "err unknownName"
#guard errorObs hp_23k == .matched (some { kind := "unknownName", names := ["z"], counts := [] })
#guard cacheEntries hp_23k "Observe" == some 0
#guard cacheTotal hp_23k == some 0

-- HP-23l: a deferred position of the returned callable's cell reads its own captured y while Observe is served
def hp_23l : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 1]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Mk" (alg ["y"] [] [{ (privateLocalProp "C" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Cap") [(.call (.resolve "Z") [])]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "Z" (.localCapturedAncestorParams ["y"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.param "y"))]))]))])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["i"] [] [] [(.binary .add (.index (.resolve "C") [.param "i"]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])] [(.call (.resolve "B") [.num 0]), .resolve "Observe"]))
#guard obs hp_23l == "ok raw=S[2, 3] n=2"
#guard structural hp_23l == some "kl-struct-v1:3:n3:2e0n3:3e0s2:0,1,;"
#guard cacheEntries hp_23l "Observe" == some 1
#guard cacheEntries hp_23l "Z" == some 1
#guard cacheTotal hp_23l == some 2

-- HP-23n: R-1: the reader's own enclosing call is recorded after the cell's read of Mk's y; the record keeps every read and the reader detaches none
def hp_23n : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Mk") [.num 1]) "Algorithm" none))), privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "Inc" (alg ["n"] [] [] [(.binary .add (.param "n") (.num 1))]), privateProp "Dbl" (alg ["n"] [] [] [(.binary .mul (.param "n") (.num 2))]), privateProp "Sel" (alg ["k"] [] [] [(.call (.resolve "if") [(.comparison (.param "k") [{ op := .eq, operand := (.num 1) }]), (.call (.resolve "Cap") [(.call (.resolve "Inc") [.num 0])]), (.call (.resolve "Cap") [(.call (.resolve "Dbl") [.num 0])])])]), privateProp "Mk" (alg ["y"] [] [{ (privateLocalProp "C" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.call (.resolve "Sel") [.param "y"]) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg ["x"] [] [] [(.binary .add (.call (.resolve "C") [.param "x"]) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])]), privateProp "K" (alg ["v"] [] [privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 5]) (.num 0))])] [.resolve "Observe", .param "v"])] [(.call (.resolve "B") [.num 5]), (.call (.resolve "K") [.num 3])]))
#guard obs hp_23n == "ok raw=S[6, S[6, 3]] n=2"
#guard structural hp_23n == some "kl-struct-v1:4:n3:6e0n3:3e0s2:0,1,;s2:0,2,;"
#guard cacheEntries hp_23n "Observe" == some 1
#guard cacheTotal hp_23n == some 1

-- HP-23m: per-call isolation: each call of F has its own activation of Build and its own exported T, shared by the row and Observe
def hp_23m : Expr :=
  (.algorithmExpr (alg [] [] [privateProp "Cap" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"]), privateProp "F" (alg ["y"] [] [privateProp "B" (.alias none [] [] ((.dotCall (.call (.resolve "Build") [.num 5]) "Algorithm" none))), privateProp "Observe" (alg [] [] [] [(.binary .add (.call (.resolve "B") [.num 1]) (.num 0))]), privateProp "Build" (alg ["z"] [] [privateProp "T" (alg [] [] [] [(.call (.resolve "tick") [])]), { (privateLocalProp "G" (.localCapturedAncestorParams ["z"]) (alg ["x"] [] [] [(.binary .add (.binary .add (.param "x") (.param "z")) (.resolve "T"))])) with requiredOwnerDepths := some [("z", some 0)] }] [(.call (.resolve "Cap") [(.call (.resolve "G") [.num 0])])])] [(.call (.resolve "B") [.num 2]), .resolve "Observe", .param "y"])] [(.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])]))
#guard obs hp_23m == "ok raw=S[S[8, 7, 1], S[9, 8, 2]] n=2"
#guard structural hp_23m == some "kl-struct-v1:8:n3:8e0n3:7e0n3:1e0s3:0,1,2,;n3:9e0n3:2e0s3:4,0,5,;s2:3,6,;"
#guard ((runCountedM hp_23m).runState EvalState.empty).2.tickCounter == 2
#guard cacheEntries hp_23m "Observe" == some 2
#guard cacheEntries hp_23m "T" == some 2
#guard cacheTotal hp_23m == some 4

-- KL-07 acceptance (HP-17a / HP-17b): both values have the neutral text ok raw=L['a', 'b'] n=1,
-- pinned above, but different kl-struct-v1 identities: neither Lean value has the other's.
#guard structural hp_17a != some "kl-struct-v1:2:t6:a', 'bl1:0,;"
#guard structural hp_17b != some "kl-struct-v1:3:t1:at1:bl2:0,1,;"

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
  "HP-05j",
  "HP-05k",
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
  "HP-14b",
  "HP-14c",
  "HP-14d",
  "HP-14e",
  "HP-14f",
  "HP-14g",
  "HP-14h",
  "HP-14i",
  "HP-14j",
  "HP-14k",
  "HP-14l",
  "HP-14m",
  "HP-14n",
  "HP-14o",
  "HP-14p",
  "HP-14q",
  "HP-14r",
  "HP-14s",
  "HP-14t",
  "HP-14u",
  "HP-14v",
  "HP-15a",
  "HP-15b",
  "HP-15c",
  "HP-15d",
  "HP-15e",
  "HP-16a",
  "HP-16b",
  "HP-16c",
  "HP-17a",
  "HP-17b",
  "HP-18a",
  "HP-18b",
  "HP-18c",
  "HP-18d",
  "HP-18e",
  "HP-18f",
  "HP-18g",
  "HP-18h",
  "HP-18i",
  "HP-18j",
  "HP-18k",
  "HP-18l",
  "HP-18m",
  "HP-18n",
  "HP-18o",
  "HP-18p",
  "HP-18q",
  "HP-18r",
  "HP-18s",
  "HP-18t",
  "HP-18u",
  "HP-19a",
  "HP-19b",
  "HP-19c",
  "HP-19d",
  "HP-19e",
  "HP-19f",
  "HP-19g",
  "HP-19h",
  "HP-19i",
  "HP-19j",
  "HP-19k",
  "HP-19l",
  "HP-19m",
  "HP-19n",
  "HP-19o",
  "HP-19p",
  "HP-19q",
  "HP-19r",
  "HP-19s",
  "HP-19t",
  "HP-19u",
  "HP-19v",
  "HP-19w",
  "HP-19x",
  "HP-19y",
  "HP-19z",
  "HP-20a",
  "HP-20b",
  "HP-20c",
  "HP-20d",
  "HP-20e",
  "HP-20f",
  "HP-20g",
  "HP-20h",
  "HP-20i",
  "HP-22a",
  "HP-22b",
  "HP-22c",
  "HP-22d",
  "HP-22e",
  "HP-22f",
  "HP-22g",
  "HP-22h",
  "HP-22i",
  "HP-22j",
  "HP-22k",
  "HP-22l",
  "HP-22m",
  "HP-22n",
  "HP-22o",
  "HP-22p",
  "HP-22q",
  "HP-22r",
  "HP-22s",
  "HP-21a",
  "HP-23a",
  "HP-23b",
  "HP-23c",
  "HP-23d",
  "HP-23e",
  "HP-23f",
  "HP-23g",
  "HP-23h",
  "HP-23i",
  "HP-23j",
  "HP-23k",
  "HP-23l",
  "HP-23n",
  "HP-23m"
]
#guard comparableCaseIds.length == 203

/--
Machine-checked known-divergence partition count (HOST-LEAN-O6 shapes pinned on both sides).
-/
def divergentCaseIds : List String := [

]
#guard divergentCaseIds.length == 0

-- 203 comparable cases, 0 known divergences.
end HostParentDifferential
