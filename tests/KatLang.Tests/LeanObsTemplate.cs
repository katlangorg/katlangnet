namespace KatLang.Tests;

/// <summary>
/// The shared Lean observation machinery emitted into every generated
/// differential artifact (<c>lean/SemanticExplorerCases.lean</c> and
/// <c>lean/LanguageSpecCases.lean</c>). Both artifacts are self-contained
/// Lean files, but their observation definitions originate from this single
/// C# constant, so the two can never drift apart. The category names in
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

    /// <summary>
    /// Lean definitions for <c>neutral</c>, <c>errCategory</c>,
    /// <c>runCountedM</c>, and <c>obs</c> — the neutral observation encoding
    /// shared verbatim with the C# harness, including the per-case
    /// plain/counted evaluator cross-check.
    /// </summary>
    public const string SharedDefinitions = """
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
            | .illegalInOpen _ | .badOpenForm _ | .illegalInEval _ => none

        /-- Counted variant of `runResultM`: the same declaration identification and root wiring, but keeping the
            root emitted count (`evalAlgOutputCounted` / `evalCounted`), matching the
            C# `Evaluator.RunCounted` observation. -/
        def runCountedM (e : Expr) : EvalM CountedResult := do
          let e := (identifyPropertyExpr e).run' 0
          validateExplicitParamOutputInvariantExpr e
          let ctx := { callStack := [preludeAlg] }
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
