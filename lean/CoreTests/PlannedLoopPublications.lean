import KatLang

/-!
KL-06 F01 (owner decision Option A, November 21 2026): the zero-argument property publications of
loop rounds whose step declares zero-argument properties.

A publication is counted when a zero-argument property first establishes a reusable value in its
owning invocation. A loop round is a fresh invocation of the step. Either a bare read or a qualifying
zero-supply call can establish an exported or local-only property's value in the round (CACHE-PUB-1).
Later reads and fresh calls leave the count alone. An undemanded property or a calculation that
fails before establishing its value contributes zero. A later failure preserves earlier publications.

This model already counted these entries: every round binds a fresh context, so its entries have
their own keys (`zeroArgPropertyCacheKey`). The C# planned loop keeps such a value in the frame slot
of the round instead of the property cache, and until this decision its optimized route reported no
publication for it (the first program below: three entries here and on the generic C# route, none on
the optimized one, the same result `S[3, 6]`). C# now reports the store of a frame slot as the
publication it is (`LoopRunFrame.EstablishTempSlot`, `IPlannedLoopPublicationObserver`). The pair
`while-state-row-demands-temp` / `while-twin-never-demands-temp` is the original F01 demand witness
and its no-demand twin: the same four rounds and the same result `S[3, 6]`, with `T` published three
times against never, so only the cache guards tell the two apart.

HAND-MAINTAINED, and pinned from C#: the test class `PlannedLoopPublicationTests` holds the table of
sources and reviewed expectations, runs every case on the generic, optimized and suspending async
routes (proving from the planner diagnostics that the optimized run planned the loop), and checks that
this module holds, between the two marker lines, exactly the `LeanAstEncoder` encoding of each
elaborated program with its neutral and cache guards, and above them the observation definitions the
four generated differential artifacts share, verbatim. To change a case, change the C# table and copy
the text its failing check prints.
-/

namespace PlannedLoopPublications
open KatLang

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

-- BEGIN PLANNED-LOOP PUBLICATION TABLE (checked by PlannedLoopPublicationTests)
-- local-only-temp-read-twice: Step(n, total) = { \n     Next = n + 1 \n     Next, total + Next \n } \n Step(0, 0).repeat(3)
def plpLocalOnlyTempReadTwice : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n", "total"] [] [{ (privateLocalProp "Next" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .add (.param "n") (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }] [.resolve "Next", (.binary .add (.param "total") (.resolve "Next"))])] [(.dotCall (.call (.resolve "Step") [.num 0, .num 0]) "repeat" (some [.num 3]))])
#guard obs plpLocalOnlyTempReadTwice == "ok raw=S[3, 6] n=1"
#guard cacheEntries plpLocalOnlyTempReadTwice "Next" == some 3
#guard cacheTotal plpLocalOnlyTempReadTwice == some 3

-- exported-constant-temp: Step(s) = { \n     T = 5 \n     s + T \n } \n Step(0).repeat(3)
def plpExportedConstantTemp : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["s"] [] [privateProp "T" (alg [] [] [] [.num 5])] [(.binary .add (.param "s") (.resolve "T"))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpExportedConstantTemp == "ok raw=15 n=1"
#guard cacheEntries plpExportedConstantTemp "T" == some 3
#guard cacheTotal plpExportedConstantTemp == some 3

-- two-temps-one-reads-the-other: Step(n) = { \n     A = n + 1 \n     B = A * 2 \n     B + A \n } \n Step(0).repeat(3)
def plpTwoTempsOneReadsTheOther : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .add (.param "n") (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }, { (privateLocalProp "B" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .mul (.resolve "A") (.num 2))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.resolve "B") (.resolve "A"))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpTwoTempsOneReadsTheOther == "ok raw=39 n=1"
#guard cacheEntries plpTwoTempsOneReadsTheOther "A" == some 3
#guard cacheEntries plpTwoTempsOneReadsTheOther "B" == some 3
#guard cacheTotal plpTwoTempsOneReadsTheOther == some 6

-- call-establishes-then-read: Step(n) = { \n     A = n * 10 + 1 \n     n + A() + A \n } \n Step(0).repeat(3)
def plpCallEstablishesThenRead : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .add (.binary .mul (.param "n") (.num 10)) (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.binary .add (.param "n") (.call (.resolve "A") [])) (.resolve "A"))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpCallEstablishesThenRead == "ok raw=926 n=1"
#guard cacheEntries plpCallEstablishesThenRead "A" == some 3
#guard cacheTotal plpCallEstablishesThenRead == some 3

-- read-establishes-then-call: Step(n) = { \n     A = n * 10 + 1 \n     n + A + A() \n } \n Step(0).repeat(3)
def plpReadEstablishesThenCall : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .add (.binary .mul (.param "n") (.num 10)) (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.binary .add (.param "n") (.resolve "A")) (.call (.resolve "A") []))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpReadEstablishesThenCall == "ok raw=926 n=1"
#guard cacheEntries plpReadEstablishesThenCall "A" == some 3
#guard cacheTotal plpReadEstablishesThenCall == some 3

-- call-twice: Step(n) = { \n     A = n * 10 + 1 \n     n + A() + A() \n } \n Step(0).repeat(3)
def plpCallTwice : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .add (.binary .mul (.param "n") (.num 10)) (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.binary .add (.param "n") (.call (.resolve "A") [])) (.call (.resolve "A") []))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpCallTwice == "ok raw=926 n=1"
#guard cacheEntries plpCallTwice "A" == some 3
#guard cacheTotal plpCallTwice == some 3

-- exported-temp-call-then-read: Step(n) = { \n     E = 6 * 7 \n     n + E() + E \n } \n Step(0).repeat(3)
def plpExportedTempCallThenRead : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [privateProp "E" (alg [] [] [] [(.binary .mul (.num 6) (.num 7))])] [(.binary .add (.binary .add (.param "n") (.call (.resolve "E") [])) (.resolve "E"))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpExportedTempCallThenRead == "ok raw=252 n=1"
#guard cacheEntries plpExportedTempCallThenRead "E" == some 3
#guard cacheTotal plpExportedTempCallThenRead == some 3

-- alias-temp-publishes-its-target: Step(n) = { \n     A = n + 1 \n     B = A \n     B + B \n } \n Step(0).repeat(3)
def plpAliasTempPublishesItsTarget : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .add (.param "n") (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }, { (privateLocalProp "B" (.localCapturedAncestorParams ["n"]) (.alias none [] [] (.resolve "A"))) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.resolve "B") (.resolve "B"))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpAliasTempPublishesItsTarget == "ok raw=14 n=1"
#guard cacheEntries plpAliasTempPublishesItsTarget "A" == some 3
#guard cacheEntries plpAliasTempPublishesItsTarget "B" == some 0
#guard cacheTotal plpAliasTempPublishesItsTarget == some 3

-- while-condition-row-establishes: Step(n) = { \n     Next = n + 1 \n     Next, Next < 3 \n } \n Step(0).while
def plpWhileConditionRowEstablishes : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [{ (privateLocalProp "Next" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .add (.param "n") (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }] [.resolve "Next", (.comparison (.resolve "Next") [{ op := .lt, operand := (.num 3) }])])] [(.dotCall (.call (.resolve "Step") [.num 0]) "while" none)])
#guard obs plpWhileConditionRowEstablishes == "ok raw=2 n=1"
#guard cacheEntries plpWhileConditionRowEstablishes "Next" == some 3
#guard cacheTotal plpWhileConditionRowEstablishes == some 3

-- while-state-row-demands-temp: Step(n, acc) = { \n     T = n * 2 \n     n + 1, acc + T, n < 3 \n } \n Step(0, 0).while
def plpWhileStateRowDemandsTemp : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n", "acc"] [] [{ (privateLocalProp "T" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .mul (.param "n") (.num 2))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.param "n") (.num 1)), (.binary .add (.param "acc") (.resolve "T")), (.comparison (.param "n") [{ op := .lt, operand := (.num 3) }])])] [(.dotCall (.call (.resolve "Step") [.num 0, .num 0]) "while" none)])
#guard obs plpWhileStateRowDemandsTemp == "ok raw=S[3, 6] n=1"
#guard cacheEntries plpWhileStateRowDemandsTemp "T" == some 3
#guard cacheTotal plpWhileStateRowDemandsTemp == some 3

-- while-twin-never-demands-temp: Step(n, acc) = { \n     T = n * 2 \n     n + 1, acc + n * 2, n < 3 \n } \n Step(0, 0).while
def plpWhileTwinNeverDemandsTemp : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n", "acc"] [] [{ (privateLocalProp "T" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .mul (.param "n") (.num 2))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.param "n") (.num 1)), (.binary .add (.param "acc") (.binary .mul (.param "n") (.num 2))), (.comparison (.param "n") [{ op := .lt, operand := (.num 3) }])])] [(.dotCall (.call (.resolve "Step") [.num 0, .num 0]) "while" none)])
#guard obs plpWhileTwinNeverDemandsTemp == "ok raw=S[3, 6] n=1"
#guard cacheEntries plpWhileTwinNeverDemandsTemp "T" == some 0
#guard cacheTotal plpWhileTwinNeverDemandsTemp == some 0

-- unused-temp: Step(n) = { \n     Unused = n + 1 \n     n + 2 \n } \n Step(0).repeat(3)
def plpUnusedTemp : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [{ (privateLocalProp "Unused" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .add (.param "n") (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.param "n") (.num 2))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpUnusedTemp == "ok raw=6 n=1"
#guard cacheEntries plpUnusedTemp "Unused" == some 0
#guard cacheTotal plpUnusedTemp == some 0

-- temp-fails-before-establishing: Step(n) = { \n     Bad = 1 / n \n     n + Bad \n } \n Step(0).repeat(3)
def plpTempFailsBeforeEstablishing : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [{ (privateLocalProp "Bad" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .div (.num 1) (.param "n"))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.param "n") (.resolve "Bad"))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpTempFailsBeforeEstablishing == "err div0"
#guard cacheEntries plpTempFailsBeforeEstablishing "Bad" == some 0
#guard cacheTotal plpTempFailsBeforeEstablishing == some 0

-- temp-fails-in-a-later-round: Step(n) = { \n     T = 1 / (1 - n) \n     n + T \n } \n Step(0).repeat(3)
def plpTempFailsInALaterRound : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [{ (privateLocalProp "T" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .div (.num 1) (.binary .sub (.num 1) (.param "n")))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.param "n") (.resolve "T"))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpTempFailsInALaterRound == "err div0"
#guard cacheEntries plpTempFailsInALaterRound "T" == some 1
#guard cacheTotal plpTempFailsInALaterRound == some 1

-- failure-after-publication-in-the-round: Step(n) = { \n     T = n + 1 \n     T + 0 / (2 - T) \n } \n Step(0).repeat(3)
def plpFailureAfterPublicationInTheRound : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["n"] [] [{ (privateLocalProp "T" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .add (.param "n") (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.resolve "T") (.binary .div (.num 0) (.binary .sub (.num 2) (.resolve "T"))))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3]))])
#guard obs plpFailureAfterPublicationInTheRound == "err div0"
#guard cacheEntries plpFailureAfterPublicationInTheRound "T" == some 2
#guard cacheTotal plpFailureAfterPublicationInTheRound == some 2

-- failure-after-the-loop: Step(s) = { \n     T = 5 \n     s + T \n } \n Step(0).repeat(3) \n 1 / 0
def plpFailureAfterTheLoop : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["s"] [] [privateProp "T" (alg [] [] [] [.num 5])] [(.binary .add (.param "s") (.resolve "T"))])] [(.dotCall (.call (.resolve "Step") [.num 0]) "repeat" (some [.num 3])), (.binary .div (.num 1) (.num 0))])
#guard obs plpFailureAfterTheLoop == "err div0"
#guard cacheEntries plpFailureAfterTheLoop "T" == some 3
#guard cacheTotal plpFailureAfterTheLoop == some 3

-- handover-continues-generically: Step(a, n) = { \n     T = n + 1 \n     a, T \n } \n Step((), 0).repeat(3)
def plpHandoverContinuesGenerically : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["a", "n"] [] [{ (privateLocalProp "T" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .add (.param "n") (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }] [.param "a", .resolve "T"])] [(.dotCall (.call (.resolve "Step") [(.emptySequence 0), .num 0]) "repeat" (some [.num 3]))])
#guard obs plpHandoverContinuesGenerically == "ok raw=S[S[], 3] n=1"
#guard cacheEntries plpHandoverContinuesGenerically "T" == some 3
#guard cacheTotal plpHandoverContinuesGenerically == some 3
-- END PLANNED-LOOP PUBLICATION TABLE

end PlannedLoopPublications
