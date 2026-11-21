namespace KatLang.Tests;

/// <summary>
/// The shared Lean observation machinery emitted into every generated
/// differential artifact (<c>lean/SemanticExplorerCases.lean</c>,
/// <c>lean/LanguageSpecCases.lean</c>, <c>lean/CoreTests/HostParentDifferential.lean</c>,
/// <c>lean/CoreTests/SemanticGeneratedCases.lean</c> and
/// <c>lean/CoreTests/ModuleDifferential.lean</c>). The artifacts are self-contained
/// Lean files, but their observation definitions originate from these C#
/// constants, so they can never drift apart. The category names in
/// <c>errCategory</c> must stay aligned with
/// <see cref="SemanticExplorerHarness.ErrorCategory"/>.
/// </summary>
internal static class LeanObsTemplate
{
    internal static void AppendErrorGuard(System.Text.StringBuilder builder, string leanName, SharedErrorPayload? payload)
    {
        if (payload is not null)
            builder.Append($"#guard errorObs {leanName} == .matched {payload.Lean}\n");
    }

    internal static void AppendProjectionContracts(System.Text.StringBuilder builder)
    {
        builder.Append("-- Independent error-constructor projection goldens (not evaluator programs).\n");
        foreach (var c in DifferentialErrorContracts.All)
            builder.Append($"#guard sharedError {c.LeanError} == {c.Expected?.Lean ?? "none"}\n");
        builder.Append('\n');
    }

    /// <summary>The number of <c>#guard</c> lines <see cref="AppendCacheObservationContracts"/> emits.</summary>
    internal const int CacheObservationContractGuards = 5;

    /// <summary>
    /// KL-06 observation-state guards on <c>publicationsOf</c> itself (hand-written states, not
    /// evaluator programs): a finished run without a comparable publication set observes
    /// <c>none</c>; a completed run observes its cache, empty or not, whether it succeeded or failed.
    /// So a guard at <c>some 0</c> can never be satisfied by a missing observation.
    /// </summary>
    internal static void AppendCacheObservationContracts(System.Text.StringBuilder builder)
    {
        builder.Append("""
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

            """.ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// KL-06 Lean definitions of the zero-argument cache observation, shared by the four generated
    /// artifacts: <c>publicationsOf</c> (the comparable publication set of a finished run, or
    /// <c>none</c>), <c>publications</c> (one plain run), <c>cacheEntries</c> (per property name)
    /// and <c>cacheTotal</c>. The C# counterpart is <see cref="ZeroArgPublicationObserver"/>.
    /// </summary>
    public const string CacheObservationDefinitions = """
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
        """;

    /// <summary>
    /// Lean definitions for <c>neutral</c>, <c>errCategory</c>,
    /// <c>runCountedM</c>, and <c>obs</c> — the neutral observation encoding
    /// shared verbatim with the C# harness, including the per-case
    /// plain/counted evaluator cross-check.
    /// </summary>
    public const string SharedDefinitions = """
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
        """;
}
