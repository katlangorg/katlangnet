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
    /// <summary>
    /// Lean definitions for <c>neutral</c>, <c>errCategory</c>,
    /// <c>runCountedM</c>, and <c>obs</c> — the neutral observation encoding
    /// shared verbatim with the C# harness, including the per-case
    /// plain/counted evaluator cross-check.
    /// </summary>
    public const string SharedDefinitions = """
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
        """;
}
