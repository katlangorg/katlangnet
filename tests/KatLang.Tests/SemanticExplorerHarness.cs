namespace KatLang.Tests;

/// <summary>
/// One observed explorer case: the typed outcome plus every observable facet
/// the invariants compare (raw structure, emitted count, display, round-trip).
/// </summary>
public sealed record ExplorerObservation(
    string CaseId,
    string Source,
    string Outcome,          // "ok" | "err" | "parseError"
    string? Raw,             // neutral raw structure (ok only)
    int? Emitted,            // root emitted count (ok only)
    string? Display,         // engine display text (ok only)
    string? ErrorCategory,   // innermost error category (err only)
    Result? Value)           // raw result tree (ok only)
{
    /// <summary>Supplementary shared semantic fields, outside the neutral observation.</summary>
    public SharedErrorPayload? ErrorPayload { get; init; }

    /// <summary>
    /// Neutral observation string shared verbatim with the generated Lean
    /// artifact: <c>ok raw=... n=...</c> or <c>err CATEGORY</c>.
    /// </summary>
    public string Neutral => Outcome switch
    {
        "ok" => $"ok raw={Raw} n={Emitted}",
        "err" => $"err {ErrorCategory}",
        _ => "parseError",
    };
}

/// <summary>
/// Runs explorer cases through the real front end and evaluator and encodes
/// results in the neutral comparison format. Raw structure is read from the
/// evaluator's <see cref="Result"/> tree, never from display text.
/// </summary>
public static class SemanticExplorerHarness
{
    public static ExplorerObservation Observe(ExplorerCase explorerCase)
        => Observe(explorerCase.Id, explorerCase.Source);

    public static ExplorerObservation Observe(string caseId, string source)
        => Observe(caseId, source, static text => KatLangEngine.Run(text));

    internal static ExplorerObservation Observe(string caseId, string source, Func<string, RunResult> runEngine)
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
        {
            RequireEngineParseFailure(caseId, parsed, runEngine(source));
            return new ExplorerObservation(caseId, source, "parseError", null, null, null, null, null);
        }

        var root = new Expr.AlgorithmExpr(parsed.Root);
        var counted = Evaluator.RunCounted(root);

        // Plain/counted cross-check, mirroring the generated Lean artifact's
        // `obs` (which compares `runResult` against `runCountedM` on every
        // case). Without it the surface corpus observed only the COUNTED C#
        // evaluator, so a plain-evaluator regression could not fail any of the
        // ~1500 generated guards. ObserveAst already applied the same check to
        // the internal-node cases.
        var plain = Evaluator.Run(root);
        if (counted.IsError != plain.IsError)
        {
            throw new InvalidOperationException(
                $"Plain/counted evaluator disagreement for '{caseId}': one errored, the other succeeded.");
        }

        if (counted.IsError)
        {
            var countedCategory = ErrorCategory(counted.Error);
            DifferentialErrors.RequireAgreement(caseId, counted.Error, plain.Error);
            RequireEngineFailure(caseId, counted.Error, runEngine(source));
            return new ExplorerObservation(
                caseId, source, "err", null, null, null, countedCategory, null)
                { ErrorPayload = DifferentialErrors.Observe(counted.Error).Payload };
        }

        if (!Result.ValueComparer.Equals(counted.Value.Value, plain.Value))
        {
            throw new InvalidOperationException(
                $"Plain/counted evaluator disagreement for '{caseId}': " +
                $"{Neutral(plain.Value)} vs {Neutral(counted.Value.Value)}.");
        }

        // Display comes from the public engine path so display-facing invariants
        // observe exactly what users see.
        var engineRun = runEngine(source);
        if (engineRun is not RunResult.Success success)
        {
            throw new InvalidOperationException(
                $"Harness disagreement for '{caseId}': Evaluator.RunCounted succeeded but " +
                $"KatLangEngine.Run returned {engineRun.GetType().Name}.");
        }

        if (!Result.ValueComparer.Equals(success.Value, counted.Value.Value)
            || success.EmittedCount != counted.Value.EmittedCount)
        {
            throw new InvalidOperationException(
                $"Harness disagreement for '{caseId}': engine value/count differs from RunCounted.");
        }

        return new ExplorerObservation(
            caseId,
            source,
            "ok",
            Neutral(counted.Value.Value),
            counted.Value.EmittedCount,
            success.ToDisplayString(),
            null,
            counted.Value.Value);
    }

    /// <summary>
    /// Observe a program constructed directly as an AST (no source form).
    /// The root output expression is wrapped as one root output slot, exactly
    /// like a parsed single-row program. Also cross-checks the plain and
    /// counted C# evaluators on the same AST (mirroring the Lean artifact's
    /// internal-consistency check) and throws on disagreement.
    /// </summary>
    public static ExplorerObservation ObserveAst(string caseId, Expr rootOutput)
    {
        var root = new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: [rootOutput]));

        var counted = Evaluator.RunCounted(root);
        var plain = Evaluator.Run(root);

        if (counted.IsError != plain.IsError)
        {
            throw new InvalidOperationException(
                $"Plain/counted evaluator disagreement for '{caseId}': one errored, the other succeeded.");
        }

        if (counted.IsError)
        {
            var countedCategory = ErrorCategory(counted.Error);
            DifferentialErrors.RequireAgreement(caseId, counted.Error, plain.Error);
            return new ExplorerObservation(caseId, "<ast>", "err", null, null, null, countedCategory, null)
                { ErrorPayload = DifferentialErrors.Observe(counted.Error).Payload };
        }

        if (!Result.ValueComparer.Equals(counted.Value.Value, plain.Value))
        {
            throw new InvalidOperationException(
                $"Plain/counted evaluator disagreement for '{caseId}': " +
                $"{Neutral(plain.Value)} vs {Neutral(counted.Value.Value)}.");
        }

        return new ExplorerObservation(
            caseId, "<ast>", "ok",
            Neutral(counted.Value.Value), counted.Value.EmittedCount,
            null, null, counted.Value.Value);
    }

    /// <summary>
    /// Neutral raw-structure encoding, deliberately distinct from display
    /// syntax so orphan singleton wrappers stay visible:
    /// atom -&gt; 1, string -&gt; 'x', sequence -&gt; S[a, b], empty -&gt; S[],
    /// exact list -&gt; L[a, b].
    /// </summary>
    public static string Neutral(Result result) => result switch
    {
        Result.Atom a => KatLang.Rendering.ValueTextRenderer.FormatNumberInvariant(a.Value),
        Result.Str s => "'" + s.Value + "'",
        // Boolean -> `true` / `false`, distinct from the atoms `1` / `0`.
        Result.Bool b => KatLang.Rendering.ValueTextRenderer.FormatBool(b.Value),
        Result.SequenceValue g => "S[" + string.Join(", ", g.Items.Select(Neutral)) + "]",
        Result.ListValue l => "L[" + string.Join(", ", l.Items.Select(Neutral)) + "]",
        // A run result never holds one (the run boundary refuses it).
        Result.CallReference => "CallReference",
    };

    /// <summary>
    /// Count sequence nodes with exactly one item anywhere in the tree.
    /// Such nodes are unwritable as literals under sequence normalization,
    /// so any occurrence is an orphan-wrapper invariant violation. Exact
    /// list values carry no singleton rule (`[x]` IS literal-writable), but
    /// their elements are still traversed for nested sequence orphans.
    /// </summary>
    public static int SingletonNodeCount(Result result) => result switch
    {
        Result.SequenceValue g => (g.Items.Count == 1 ? 1 : 0) + g.Items.Sum(SingletonNodeCount),
        Result.ListValue l => l.Items.Sum(SingletonNodeCount),
        _ => 0,
    };

    /// <summary>
    /// Innermost-error category shared with the generated Lean artifact.
    /// Category names must stay aligned with <c>errCategory</c> in
    /// <c>lean/SemanticExplorerCases.lean</c>.
    /// </summary>
    public static string ErrorCategory(EvalError error) => DifferentialErrors.Observe(error).Category;

    internal static void RequireEngineParseFailure(string caseId, ParseResult parsed, RunResult engine)
    {
        if (engine is not RunResult.ParseFailure failure
            || failure.Errors.Any(e => e.Source is not null)
            || !parsed.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)
                .Select(d => KatLangError.FromDiagnostic(d).Code).SequenceEqual(failure.Errors.Select(e => e.Code)))
            throw new InvalidOperationException($"Public engine phase/diagnostic disagreement for '{caseId}'.");
    }

    internal static void RequireEngineFailure(string caseId, EvalError error, RunResult engine)
    {
        // Root absence is a distinct public outcome. A demanded output-less property/call
        // is EvalFailure even though its innermost category is also missingOutput.
        var rootAbsence = error is EvalError.WithContext
            { ErrorContext: ProgramEvaluationContext, Inner: EvalError.MissingOutput };
        KatLangError diagnostic = (rootAbsence, engine) switch
        {
            (true, RunResult.NoProgramOutput none) => none.Diagnostic,
            (false, RunResult.EvalFailure failure) when failure.Errors.Count == 1 => failure.Errors[0],
            _ => throw new InvalidOperationException($"Public engine failure phase disagreement for '{caseId}': {engine.GetType().Name}."),
        };
        if (diagnostic.Source is null || diagnostic.Code != error.Code)
            throw new InvalidOperationException($"Public engine error category disagreement for '{caseId}'.");
        DifferentialErrors.RequireAgreement(caseId, error, diagnostic.Source);
    }

    /// <summary>
    /// Shallow single-item boundary erasure for constructed sequence slots
    /// (same shape as the evaluator's CombineOutputSlots / explicit
    /// sequence-value construction, kept here so the invariants can compute
    /// expected spliced values structurally). Collection BUILTIN results no
    /// longer use this shape — they materialize exact list values; see
    /// <see cref="ExpectedCollectionList"/>.
    /// </summary>
    public static Result ShallowCombine(IReadOnlyList<Result> items)
        => items.Count == 1 ? items[0] : new Result.SequenceValue(items);

    /// <summary>
    /// Expected collection-producing builtin result: ONE list
    /// of the kept/projected items (mirror of the evaluator's
    /// MakeCollectionListResult — zero items form [], a single kept item is
    /// never erased, and nested values stay exact elements).
    /// </summary>
    public static Result ExpectedCollectionList(IReadOnlyList<Result> items)
        => new Result.ListValue(items);
}
