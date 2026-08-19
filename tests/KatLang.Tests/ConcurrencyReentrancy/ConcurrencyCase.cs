using System.Globalization;
using KatLang.Evaluation.Caching;
using KatLang.Tests.CountedMatrix;

namespace KatLang.Tests.ConcurrencyReentrancy;

/// <summary>
/// The concurrency scenario a differential PAIR case exercises. Every member
/// must have at least one row in <see cref="ConcurrencyCorpus"/> (enforced by
/// the coverage meta-test), so the campaign cannot quietly shrink.
///
/// <para>Shapes that do not fit the two-lane pair table live as dedicated
/// facts in <c>ConcurrencyDifferentialTests</c> and <c>ReentrancyTests</c>:
/// same-AST-object concurrency, deterministically GATED overlap (one run
/// suspended mid-evaluation while another completes), budget-counter
/// isolation proofs, module-loading engine concurrency, host-callback
/// reentrancy, and post-failure cleanup sentinels.</para>
/// </summary>
public enum ConcurrencyScenario
{
    /// <summary>Two unrelated programs through the same entry point at the same
    /// time must each observe exactly their sequential baseline.</summary>
    IndependentRun,

    /// <summary>Two programs through DIFFERENT public entry points at the same
    /// time (Run vs RunCounted vs RunFlat vs the engine) must not interact.</summary>
    CrossEntryPoint,

    /// <summary>The SAME source text in both lanes (each lane parses its own
    /// AST) — no state may be keyed by source text or structural equality.</summary>
    SameProgram,

    /// <summary>Structurally similar scope graphs with identical names but
    /// distinct identities, including error paths that render owner names
    /// through <c>Evaluator.ScopeOwnerAlgorithms</c> — no run may observe the
    /// other run's owners, values, or diagnostic paths.</summary>
    ScopeOwnership,

    /// <summary>Zero-argument property caching is run-scoped SEMANTIC state:
    /// same-named, same-shaped cached properties with different values (or one
    /// failing) must never leak across concurrent runs, and the
    /// <c>A</c>-vs-<c>A()</c> cache/bypass distinction must survive
    /// concurrency.</summary>
    RunScopedCache,

    /// <summary>Evaluation budgets are per-run: one run's consumption or
    /// budget FAILURE must not change another concurrent run's verdict, even
    /// when both runs share one immutable <see cref="EvaluationLimits"/>
    /// instance.</summary>
    BudgetIsolation,

    /// <summary>Deterministic failure overlap (success‖error, error‖error,
    /// budget-failure‖success): exceptional exits of one run must not disturb
    /// the other, and a sequential sentinel run AFTERWARDS must still match
    /// its baseline (no process-global pollution left behind).</summary>
    ConcurrentFailure,

    /// <summary>Prelude/Math/builtin-registry structures are process-global
    /// and immutable: concurrent evaluator wiring must derive per-run copies
    /// rather than mutating the shared originals.</summary>
    SharedImmutable,
}

/// <summary>
/// The production execution surface a lane runs through. Each lane of a pair
/// uses exactly ONE entry point so a failure names the interacting surfaces.
/// </summary>
public enum EvalEntryPoint
{
    /// <summary>Public <see cref="Evaluator.Run(Expr, EvaluationLimits?)"/>.</summary>
    RunPlain,

    /// <summary>Internal <see cref="Evaluator.RunCounted(Expr)"/> — the counted
    /// channel (fresh run-scoped cache per call, like the public overloads).</summary>
    RunCounted,

    /// <summary>Public <see cref="Evaluator.RunFlat(Expr, EvaluationLimits?)"/> —
    /// the host-atom boundary.</summary>
    RunFlat,

    /// <summary>Public <see cref="KatLangEngine.Run(string, RunOptions?)"/> —
    /// full front end + evaluation + display.</summary>
    EngineRun,
}

/// <summary>
/// Observation runner and deterministic interleaving harness.
///
/// <para><b>Oracle.</b> Every concurrency test compares a lane's observation
/// against the SAME lane's sequential baseline — semantic equivalence, never
/// "did not crash". Observations reuse the campaign encodings:
/// <see cref="SemanticExplorerHarness.Neutral"/> raw structure,
/// <see cref="CountedMatrixCase.ShapeOf"/> cardinality shape,
/// <see cref="SemanticExplorerHarness.ErrorCategory"/> error classes, and the
/// engine's public display (differential equality, not a wording snapshot).</para>
///
/// <para><b>Interleaving.</b> Lanes run on dedicated threads released
/// together by a <see cref="Barrier"/>; deterministic MID-EVALUATION overlap
/// uses <see cref="EvaluationGate"/> through the
/// <see cref="IZeroArgPropertyResultCache"/> seam (the only host-code-inside-
/// evaluation seam, per <c>BudgetConservationTests</c>) or a gated
/// <c>DownloadCode</c> provider at the engine front end. Every wait is
/// bounded; no test uses sleeps for synchronization.</para>
/// </summary>
public static class ConcurrencyHarness
{
    /// <summary>Bound on every gate wait and lane join: generous enough for CI
    /// machines, small enough that a deadlocked lane fails the test rather
    /// than hanging the suite.</summary>
    public static readonly TimeSpan WaitBudget = TimeSpan.FromSeconds(45);

    /// <summary>Parses (inside the lane, so parsing itself is exercised under
    /// concurrency) and evaluates through one entry point, returning the
    /// canonical comparable observation string.</summary>
    public static string Observe(EvalEntryPoint entryPoint, string source, EvaluationLimits? limits = null)
        => entryPoint == EvalEntryPoint.EngineRun
            ? ObserveEngine(source, limits)
            : ObservePrepared(entryPoint, ParseRoot(source), limits);

    /// <summary>Evaluates an already-parsed (possibly SHARED) root through one
    /// non-engine entry point. Used by the same-AST-object lanes: the exact
    /// same <see cref="Expr"/> instance may be handed to several concurrent
    /// lanes because evaluation wires derived structures and never mutates the
    /// input tree.</summary>
    public static string ObservePrepared(EvalEntryPoint entryPoint, Expr root, EvaluationLimits? limits = null)
        => entryPoint switch
        {
            EvalEntryPoint.RunPlain => EncodePlain(Evaluator.Run(root, limits)),
            EvalEntryPoint.RunCounted => EncodeCounted(
                Evaluator.RunCounted(root, new RunScopedZeroArgPropertyResultCache(), limits)),
            EvalEntryPoint.RunFlat => EncodeFlat(Evaluator.RunFlat(root, limits)),
            _ => throw new InvalidOperationException(
                $"Entry point {entryPoint} takes source text, not a prepared AST."),
        };

    /// <summary>Canonical encoding of a counted evaluator outcome, exposed so
    /// gated/reentrant tests running through custom caches encode identically
    /// to the ordinary lanes.</summary>
    internal static string EncodeCounted(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? $"err {SemanticExplorerHarness.ErrorCategory(result.Error)}"
            : $"ok raw={SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount.ToString(CultureInfo.InvariantCulture)} shape={CountedMatrixCase.ShapeOf(result.Value.Value)}";

    internal static string EncodePlain(EvalResult<Result> result)
        => result.IsError
            ? $"err {SemanticExplorerHarness.ErrorCategory(result.Error)}"
            : $"ok raw={SemanticExplorerHarness.Neutral(result.Value)}";

    internal static string EncodeFlat(EvalResult<IReadOnlyList<decimal>> result)
        => result.IsError
            ? $"err {SemanticExplorerHarness.ErrorCategory(result.Error)}"
            : $"ok atoms={string.Join(" ", result.Value.Select(a => a.ToString(CultureInfo.InvariantCulture)))}";

    /// <summary>Full engine observation: outcome kind, emitted count on
    /// success, and the public display string (errors included — differential
    /// equality against the same lane's baseline, never a wording snapshot).</summary>
    public static string ObserveEngine(string source, EvaluationLimits? limits = null, RunOptions? options = null)
    {
        var effective = options ?? (limits is null ? null : new RunOptions { EvaluationLimits = limits });
        // Source loading is async-only, so downloader-configured observations go
        // through the async engine entry. Corpus downloaders complete synchronously
        // (possibly after blocking the lane thread on a test gate, which preserves the
        // lanes' overlap semantics), so the returned task is already completed and
        // GetResult is plain result extraction, not a blocking bridge.
        var run = effective?.DownloadCode is null
            ? KatLangEngine.Run(source, effective)
            : KatLangEngine.RunAsync(source, effective).GetAwaiter().GetResult();
        var display = run.ToDisplayString().ReplaceLineEndings("\\n");
        return run switch
        {
            RunResult.Success s => $"engine ok n={s.EmittedCount.ToString(CultureInfo.InvariantCulture)} display={display}",
            RunResult.NoProgramOutput => $"engine noOutput display={display}",
            RunResult.ParseFailure p => $"engine parseFailure errors={p.Errors.Count.ToString(CultureInfo.InvariantCulture)} display={display}",
            RunResult.EvalFailure => $"engine evalFailure display={display}",
            _ => throw new InvalidOperationException($"Unknown RunResult variant {run.GetType().Name}."),
        };
    }

    /// <summary>Parses one lane's source with the strict front-end oracle: a
    /// corpus program that stops parsing must fail loudly, never degrade the
    /// differential to comparing recovery trees.</summary>
    public static Expr ParseRoot(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    /// <summary>
    /// Runs every lane body on its own dedicated thread (never the xUnit pool,
    /// so a gated lane cannot starve the runner), released simultaneously by a
    /// start barrier, and returns the observations in lane order. A lane
    /// exception, a barrier timeout, or an unfinished join fails the test with
    /// the lane label. Threads are created per call: the corpus programs are
    /// tiny and dedicated threads keep lane scheduling independent of ambient
    /// test parallelism.
    /// </summary>
    public static string[] RunConcurrently(params (string Label, Func<string> Body)[] lanes)
    {
        var barrier = new Barrier(lanes.Length);
        var observations = new string?[lanes.Length];
        var failures = new Exception?[lanes.Length];
        var threads = new Thread[lanes.Length];

        for (var i = 0; i < lanes.Length; i++)
        {
            var index = i;
            threads[i] = new Thread(() =>
            {
                try
                {
                    if (!barrier.SignalAndWait(WaitBudget))
                        throw new TimeoutException("Lane start barrier timed out — another lane never started.");
                    observations[index] = lanes[index].Body();
                }
                catch (Exception ex)
                {
                    failures[index] = ex;
                }
            })
            {
                IsBackground = true,
                Name = $"katlang-lane-{lanes[index].Label}",
            };
        }

        foreach (var thread in threads)
            thread.Start();

        for (var i = 0; i < threads.Length; i++)
        {
            if (!threads[i].Join(WaitBudget))
            {
                Assert.Fail(
                    $"Lane '{lanes[i].Label}' did not finish within {WaitBudget.TotalSeconds:0}s. "
                    + "A lane that never completes under concurrency is itself a defect "
                    + "(deadlock, lost gate release, or runaway evaluation).");
            }
        }

        for (var i = 0; i < lanes.Length; i++)
        {
            if (failures[i] is { } failure)
            {
                throw new InvalidOperationException(
                    $"Lane '{lanes[i].Label}' failed with {failure.GetType().Name}: {failure.Message}", failure);
            }
        }

        return observations.Select(o => o!).ToArray();
    }

    /// <summary>
    /// Builds the standard two-lane failure report: both programs, entry
    /// points, synchronization strategy, sequential baselines, and concurrent
    /// observations — everything needed to reproduce the interleaving.
    /// </summary>
    public static string PairReport(
        string invariant,
        string synchronization,
        (string Label, string Program, string Entry, string Baseline, string Observed) a,
        (string Label, string Program, string Entry, string Baseline, string Observed) b)
        => $"""
            Violated invariant: {invariant}
            Synchronization: {synchronization}

            Lane {a.Label} [{a.Entry}]:
            {a.Program}
              sequential baseline: {a.Baseline}
              concurrent observed: {a.Observed}

            Lane {b.Label} [{b.Entry}]:
            {b.Program}
              sequential baseline: {b.Baseline}
              concurrent observed: {b.Observed}
            """;
}

/// <summary>
/// A two-event rendezvous for deterministic mid-evaluation suspension:
/// the gated run calls <see cref="Pass"/> at the chosen point (signalling
/// <c>Reached</c>, then blocking on <c>Resume</c>); the orchestrating test
/// waits for <see cref="WaitUntilInside"/>, does other work while the run is
/// provably suspended inside evaluation, then calls <see cref="Release"/>.
/// Tests must call <see cref="Release"/> from a <c>finally</c> so a failing
/// assertion can never leave the gated lane blocked until its own timeout.
/// </summary>
public sealed class EvaluationGate
{
    private readonly ManualResetEventSlim _reached = new(initialState: false);
    private readonly ManualResetEventSlim _resume = new(initialState: false);

    /// <summary>Called by the instrumented seam on the gated access.</summary>
    public void Pass()
    {
        _reached.Set();
        if (!_resume.Wait(ConcurrencyHarness.WaitBudget))
            throw new TimeoutException("Gated evaluation was never released.");
    }

    /// <summary>Blocks the TEST thread until the gated run is provably suspended
    /// inside evaluation.</summary>
    public void WaitUntilInside()
        => Assert.True(
            _reached.Wait(ConcurrencyHarness.WaitBudget),
            "The gated run never reached its gate — the program did not perform the instrumented access.");

    public bool WasReached => _reached.IsSet;

    public void Release() => _resume.Set();
}

/// <summary>
/// Wraps a fresh production <see cref="RunScopedZeroArgPropertyResultCache"/>
/// and suspends the run at the k-th zero-argument property access via an
/// <see cref="EvaluationGate"/>. The gate fires BEFORE delegating, i.e. inside
/// the charged invocation region the evaluator enters before consulting the
/// cache (<c>GetOrEvaluateZeroArgPropertyResult</c>), so the run is suspended
/// mid-evaluation with live run-scoped state — the deterministic overlap point
/// for concurrency tests. Semantics are unchanged: every access still goes to
/// the real run-scoped cache.
/// </summary>
internal sealed class GatedZeroArgPropertyResultCache(EvaluationGate gate, int gateAtAccess = 1)
    : IZeroArgPropertyResultCache
{
    private readonly RunScopedZeroArgPropertyResultCache _inner = new();
    private int _accesses;

    public int Accesses => _accesses;

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        if (++_accesses == gateAtAccess)
            gate.Pass();

        return _inner.GetOrEvaluate(execution, evaluate);
    }
}

/// <summary>
/// Wraps a caller-supplied production cache and invokes a host action at the
/// k-th zero-argument property access, BEFORE delegating — i.e. host code runs
/// while the outer evaluation is suspended inside a charged invocation region.
/// This is the reentrancy seam: the host action may invoke full nested
/// evaluator/engine runs. The inner cache is caller-supplied so the
/// shared-cache-instance contract (run isolation by run identity) can be
/// tested with the SAME instance serving outer and nested runs.
/// </summary>
internal sealed class HostActionZeroArgPropertyResultCache(
    IZeroArgPropertyResultCache inner,
    int actAtAccess,
    Action hostAction) : IZeroArgPropertyResultCache
{
    private int _accesses;

    public int Accesses => _accesses;

    public bool ActionRan { get; private set; }

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        if (++_accesses == actAtAccess)
        {
            ActionRan = true;
            hostAction();
        }

        return inner.GetOrEvaluate(execution, evaluate);
    }
}
