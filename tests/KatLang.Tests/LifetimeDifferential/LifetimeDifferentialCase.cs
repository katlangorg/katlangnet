using System.Globalization;
using KatLang.Tests.CountedMatrix;

namespace KatLang.Tests.LifetimeDifferential;

/// <summary>
/// The lifetime-history scenario a differential case exercises. Every member
/// must have at least one row in <see cref="LifetimeDifferentialCorpus"/>
/// (enforced by the coverage meta-test), so the campaign cannot quietly
/// shrink. AST-identity reuse and the ModuleLoader-instance ownership
/// contract are covered by dedicated facts in
/// <c>LifetimeDifferentialTests</c> because their mechanics do not fit the
/// fresh-vs-polluted table shape.
/// </summary>
public enum LifetimeScenario
{
    /// <summary>Unrelated SUCCESSFUL prior programs must not change the target.</summary>
    FreshVsPriorSuccess,

    /// <summary>Running the same program again (and again) must observe identically —
    /// no state keyed by source text, AST identity, or "seen before".</summary>
    RepeatStability,

    /// <summary>A prior parse failure must not poison the next unrelated program.</summary>
    ParseErrorPoisoning,

    /// <summary>A prior front-end elaboration failure (load guard, load-position,
    /// paren-declaration rejection) must not poison the next program.</summary>
    FrontEndErrorPoisoning,

    /// <summary>A prior module fetch/parse/cycle/domain failure must not poison the
    /// next program.</summary>
    ModuleLoadErrorPoisoning,

    /// <summary>A prior evaluation failure (index error, resource-limit rejection)
    /// must not poison the next program.</summary>
    RuntimeErrorPoisoning,

    /// <summary>A failed version of module identity M, then a corrected version under
    /// the SAME identity, must match a fresh host that only ever saw the corrected
    /// version (cache-invalidation / failure-entry lifetime).</summary>
    SameIdentityCorrection,

    /// <summary>A successful version of module identity M, then a broken/changed
    /// version under the SAME identity, must match a fresh host that only ever saw
    /// the final version (no stale successful front-end state).</summary>
    StaleSuccessInvalidation,

    /// <summary>Prior programs using the SAME identifiers with incompatible meanings
    /// (values, arities, clause families, collecting parameters, nested scopes,
    /// modules) must not contaminate the target's scope graph.</summary>
    NameScopeCollision,

    /// <summary>Module dependency graphs (diamond, repeated import) and alternative
    /// prior load orders must not change the target.</summary>
    ModuleGraphAndOrder,

    /// <summary>Module/source identity is the loader's normalized URL: equivalent
    /// spellings are one identity, distinct spellings are distinct modules, and
    /// none of it may depend on host history.</summary>
    SourceIdentity,

    /// <summary>Multi-output / zero-output counted sentinels: a leaked front-end
    /// state cannot hide behind a scalar result because the observation carries the
    /// root emitted count and structural cardinality shape.</summary>
    CountedSentinel,
}

/// <summary>
/// A reusable in-memory module host: the caller-owned <c>DownloadCode</c>
/// delegate is the ONE production seam that crosses runs, so a single host
/// instance is deliberately shared by every step of a polluted history.
/// Content is mutable (SetFiles) to model "same identity, different content";
/// every fetch is logged so loader-level facts can assert download counts.
/// The loader hands the delegate its NORMALIZED url (Uri.AbsoluteUri), so
/// files are keyed by normalized form.
/// </summary>
public sealed class LifetimeModuleHost
{
    private readonly Dictionary<string, string> _files = new(StringComparer.Ordinal);

    public List<string> DownloadLog { get; } = [];

    public LifetimeModuleHost(params (string Url, string Content)[] files) => SetFiles(files);

    public void SetFiles(params (string Url, string Content)[] files)
    {
        _files.Clear();
        foreach (var (url, content) in files)
            _files[url] = content;
    }

    public string Download(string url)
    {
        DownloadLog.Add(url);
        return _files.TryGetValue(url, out var content)
            ? content
            : throw new InvalidOperationException($"404: no module registered for '{url}'");
    }

    /// <summary>
    /// The async downloader contract over the in-memory map. The ValueTasks complete
    /// synchronously (a missing file throws synchronously), so every
    /// downloader-configured run in this campaign completes synchronously too.
    /// </summary>
    public Func<string, CancellationToken, ValueTask<string>> Downloader
        => (url, _) => ValueTask.FromResult(Download(url));
}

/// <summary>
/// One semantic observation of a program, canonicalized for differential
/// comparison. The oracle of every lifetime case is EQUALITY between the
/// fresh observation and the history-polluted observation — nothing here is a
/// hand-written snapshot. The comparable form carries the outcome class, the
/// neutral raw structure, the root emitted count, the structural cardinality
/// shape (counted-matrix encoding), the innermost error category, the engine
/// display, and the ordered front-end diagnostics, so a leak that only
/// changes counts, shapes, error categories, or diagnostic accumulation is
/// still visible.
/// </summary>
public sealed record LifetimeObservation(
    string Outcome,                       // "ok" | "err" | "parseError"
    string? Raw,
    int? Emitted,
    string? Shape,
    string? ErrorCategory,
    string? Display,
    IReadOnlyList<string> FrontEndDiagnostics)
{
    public string Comparable => Outcome switch
    {
        "ok" => $"ok raw={Raw} n={Emitted?.ToString(CultureInfo.InvariantCulture)} shape={Shape} display={Display?.ReplaceLineEndings("\\n")}",
        "err" => $"err {ErrorCategory}",
        _ => "parseError\n" + string.Join("\n", FrontEndDiagnostics),
    };

    public override string ToString() => Comparable;
}

/// <summary>
/// One lifetime differential case: run the target on a fresh host and after
/// the given history on a reused host, and require identical observations.
///
/// <para>Module content is modeled in two phases: <see cref="HistoryModules"/>
/// is the module map while history steps run (defaults to
/// <see cref="TargetModules"/>), and <see cref="TargetModules"/> is the map
/// when the target runs — and therefore also the FRESH baseline's map, so
/// "same identity, different content" cases compare the corrected/replaced
/// graph against a host that only ever saw the final content.</para>
/// </summary>
public sealed record LifetimeCase
{
    public required string Id { get; init; }

    public required LifetimeScenario Scenario { get; init; }

    /// <summary>The lifetime invariant this case pins, with implementation anchor.</summary>
    public required string Invariant { get; init; }

    public required string Target { get; init; }

    /// <summary>Expected outcome class of the FRESH baseline ("ok" | "err" | "parseError").
    /// This is not the oracle (equality is); it keeps the case's POWER visible — a target
    /// that silently stops parsing would otherwise degrade the differential to
    /// parseError == parseError.</summary>
    public required string ExpectedFreshOutcome { get; init; }

    public string[] History { get; init; } = [];

    /// <summary>Expected outcome class per history step, same order. A poisoning case
    /// whose history stops failing (or an unrelated-success case whose history stops
    /// succeeding) has lost its meaning; this keeps it loud.</summary>
    public string[]? ExpectedHistoryOutcomes { get; init; }

    /// <summary>Module map at target time AND for the fresh baseline. Null = no module
    /// host at all (pure process-static differential); empty = host present, no files.</summary>
    public (string Url, string Content)[]? TargetModules { get; init; }

    /// <summary>Module map while history steps run. Null = same as <see cref="TargetModules"/>.</summary>
    public (string Url, string Content)[]? HistoryModules { get; init; }

    /// <summary>
    /// Optional ABSOLUTE anchor: the fresh baseline's root emitted count,
    /// hand-derived from the counted rules. A pure differential cannot see a
    /// process-global leak that skews the fresh baseline and the polluted run
    /// identically; this anchor (like the counted matrix for module-less
    /// semantics) pins the fresh side absolutely on the module-content rows
    /// where staleness would change the count.
    /// </summary>
    public int? ExpectedFreshEmitted { get; init; }
}

/// <summary>
/// Observation runner: parses/evaluates through the PRODUCTION paths
/// (public <see cref="Parser.Parse(string)"/> overloads, both evaluators, and
/// <see cref="KatLangEngine.Run(string, RunOptions?)"/>) and canonicalizes the
/// result. Mirrors <see cref="SemanticExplorerHarness"/> — including its
/// plain/counted and engine cross-checks — extended with the module-provider
/// overloads that harness does not take.
/// </summary>
public static class LifetimeHarness
{
    public static LifetimeObservation Observe(string source, LifetimeModuleHost? host)
    {
        // Source loading is async-only; the in-memory host's ValueTasks complete
        // synchronously, so the async entry points complete synchronously here and
        // GetResult is plain result extraction on a completed task.
        var parsed = host is null
            ? Parser.Parse(source)
            : Parser.ParseAsync(source, new RunOptions { DownloadCode = host.Downloader })
                .GetAwaiter().GetResult();
        var engineRun = host is null
            ? KatLangEngine.Run(source)
            : KatLangEngine.RunAsync(source, new RunOptions { DownloadCode = host.Downloader })
                .GetAwaiter().GetResult();

        if (parsed.HasErrors)
        {
            if (engineRun is RunResult.Success)
            {
                throw new InvalidOperationException(
                    "Front-end/engine disagreement: Parser.Parse reported errors but KatLangEngine.Run succeeded.");
            }

            var diagnostics = parsed.Diagnostics
                .Select(d => $"{d.Severity}: {d.Message.Split('\n')[0]}")
                .ToList();
            return new LifetimeObservation("parseError", null, null, null, null, null, diagnostics);
        }

        var root = new Expr.AlgorithmExpr(parsed.Root);
        var counted = Evaluator.RunCounted(root);
        var plain = Evaluator.Run(root);

        if (counted.IsError != plain.IsError)
        {
            throw new InvalidOperationException(
                "Plain/counted evaluator disagreement: one errored, the other succeeded.");
        }

        if (counted.IsError)
        {
            var countedCategory = SemanticExplorerHarness.ErrorCategory(counted.Error);
            var plainCategory = SemanticExplorerHarness.ErrorCategory(plain.Error);
            if (countedCategory != plainCategory)
            {
                throw new InvalidOperationException(
                    $"Plain/counted evaluator disagreement: err {countedCategory} vs err {plainCategory}.");
            }

            if (engineRun is RunResult.Success)
            {
                throw new InvalidOperationException(
                    "Engine/evaluator disagreement: RunCounted errored but KatLangEngine.Run succeeded.");
            }

            return new LifetimeObservation("err", null, null, null, countedCategory, null, []);
        }

        if (!Result.ValueComparer.Equals(counted.Value.Value, plain.Value))
        {
            throw new InvalidOperationException(
                "Plain/counted evaluator disagreement on the result value.");
        }

        if (engineRun is not RunResult.Success success)
        {
            throw new InvalidOperationException(
                $"Engine/evaluator disagreement: RunCounted succeeded but KatLangEngine.Run returned {engineRun.GetType().Name}.");
        }

        if (!Result.ValueComparer.Equals(success.Value, counted.Value.Value)
            || success.EmittedCount != counted.Value.EmittedCount)
        {
            throw new InvalidOperationException(
                "Engine value/count differs from RunCounted on the same source.");
        }

        return new LifetimeObservation(
            "ok",
            SemanticExplorerHarness.Neutral(counted.Value.Value),
            counted.Value.EmittedCount,
            CountedMatrixCase.ShapeOf(counted.Value.Value),
            null,
            success.ToDisplayString(),
            []);
    }
}
