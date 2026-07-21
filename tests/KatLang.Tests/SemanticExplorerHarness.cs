using System.Globalization;

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
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
            return new ExplorerObservation(caseId, source, "parseError", null, null, null, null, null);

        var counted = Evaluator.RunCounted(new Expr.Block(parsed.Root));
        if (counted.IsError)
        {
            return new ExplorerObservation(
                caseId, source, "err", null, null, null, ErrorCategory(counted.Error), null);
        }

        // Display comes from the public engine path so display-facing invariants
        // observe exactly what users see.
        var engineRun = KatLangEngine.Run(source);
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
        var root = new Expr.Block(new Algorithm.User(
            Parent: null, Parameters: [], Opens: [], Properties: [], Output: [rootOutput]));

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
            var plainCategory = ErrorCategory(plain.Error);
            if (countedCategory != plainCategory)
            {
                throw new InvalidOperationException(
                    $"Plain/counted evaluator disagreement for '{caseId}': err {countedCategory} vs err {plainCategory}.");
            }

            return new ExplorerObservation(caseId, "<ast>", "err", null, null, null, countedCategory, null);
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
        Result.Atom a => a.Value.ToString(CultureInfo.InvariantCulture),
        Result.Str s => "'" + s.Value + "'",
        Result.SequenceValue g => "S[" + string.Join(", ", g.Items.Select(Neutral)) + "]",
        Result.ListValue l => "L[" + string.Join(", ", l.Items.Select(Neutral)) + "]",
        _ => "?",
    };

    /// <summary>
    /// Count sequence nodes with exactly one item anywhere in the tree.
    /// Such nodes are unwritable as literals under current canonicalization,
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
    public static string ErrorCategory(EvalError error)
    {
        while (error is EvalError.WithContext withContext)
            error = withContext.Inner;

        return error switch
        {
            EvalError.ArityMismatch => "arity",
            EvalError.VariadicArityMismatch => "arity",
            EvalError.BadArity => "arity",
            EvalError.BranchArityMismatch => "arity",
            EvalError.BranchOutputArityMismatch => "arity",
            EvalError.BadIndex => "index",
            EvalError.TypeMismatch => "type",
            EvalError.MissingOutput => "missingOutput",
            EvalError.SpreadMissingOutput => "spreadMissingOutput",
            EvalError.UnknownName => "unknownName",
            EvalError.DivByZero => "div0",
            EvalError.NoMatchingBranch => "branch",
            EvalError.UnknownProperty => "unknownProperty",
            EvalError.NotPublicProperty => "notPublicProperty",
            EvalError.LocalOnlyProperty => "localOnlyProperty",
            EvalError.NotAnAlgorithm => "notAnAlgorithm",
            EvalError.IllegalInOpen => "illegalInOpen",
            EvalError.BadOpenForm => "badOpenForm",
            EvalError.IllegalInEval => "illegalInEval",
            EvalError.AmbiguousOpen => "ambiguousOpen",
            EvalError.DuplicateProperty => "duplicateProperty",
            EvalError.DuplicateBranchPattern => "duplicateBranchPattern",
            EvalError.SpecialOutputAccess => "specialOutputAccess",
            EvalError.ExplicitParametersRequireOutput => "explicitParamsRequireOutput",
            EvalError.UnresolvedImplicitParams => "unresolvedImplicitParams",
            // C#-only: the Lean core uses unbounded Int and cannot overflow.
            EvalError.NumericOverflow => "numericOverflow",
            // C#-only host resource policy: the Lean evaluator is unbounded and models
            // no execution budget, so these categories have no Lean counterpart.
            EvalError.EvaluationDepthExceeded => "evaluationDepthExceeded",
            EvalError.EvaluationStepLimitExceeded => "evaluationStepLimitExceeded",
            EvalError.EvaluationStackExhausted => "evaluationStackExhausted",
            _ => error.GetType().Name,
        };
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
    /// Expected collection-producing builtin result: ONE exact immutable list
    /// of the kept/projected items (mirror of the evaluator's
    /// MakeCollectionListResult — zero items form [], a single kept item is
    /// never erased, and nested values stay exact elements).
    /// </summary>
    public static Result ExpectedCollectionList(IReadOnlyList<Result> items)
        => new Result.ListValue(items);
}
