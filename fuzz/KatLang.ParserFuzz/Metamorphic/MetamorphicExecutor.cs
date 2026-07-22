using System.Globalization;
using System.Runtime.ExceptionServices;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Thrown when the harness itself is broken (an observation changed the run it observed, an
/// unregistered family reached execution, ...). Distinct from a metamorphic MISMATCH: this
/// says the measuring apparatus is untrustworthy, not that the language is wrong.
/// </summary>
internal sealed class MetamorphicHarnessException(string message) : Exception(message);

/// <summary>The result of running one case's pair: accepted with both observations, or rejected.</summary>
internal sealed record MetamorphicExecution(
    MetamorphicCase Case,
    bool Accepted,
    string RejectionReason,
    MetamorphicOperationalObservation? Left,
    MetamorphicOperationalObservation? Right);

/// <summary>
/// Executes both members of a metamorphic pair with fully independent run state.
///
/// <para>Isolation is by construction, not by cleanup. Each side re-parses its OWN source, so
/// no front-end state crosses; each observed run creates its own <c>EvaluationBudget</c>, so the
/// counters cannot be shared or reset; and each side gets a freshly allocated zero-argument
/// property cache. The one thing the two sides DO share is the immutable
/// <see cref="EvaluationLimits"/> and <see cref="RunOptions"/> instances — deliberately, because
/// "a reused configuration object must not carry counters" is exactly the property this executor
/// should be exercising. There is no static mutable state anywhere in this harness.</para>
///
/// <para>Observation reuses the real run-scoped budget the evaluator charged. It never
/// re-evaluates, never rebuilds a value, and is checked afterwards to have left every counter
/// untouched.</para>
/// </summary>
internal static class MetamorphicExecutor
{
    /// <summary>An unrelated program used to prove one run cannot influence the next.</summary>
    internal const string IsolationProbeSource = "V = range(1, 7)\nOutput = V.count + V.sum + V.count";

    /// <summary>
    /// Distinct threads a <see cref="MetamorphicRunPlan.BoundedParallel"/> case starts. Fixed and
    /// small; never derived from the input.
    /// </summary>
    internal const int ParallelTaskCount = 4;

    /// <summary>Unrelated runs a <see cref="MetamorphicRunPlan.AfterInterleavedRuns"/> case interposes.</summary>
    internal const int InterleavedRunCount = 3;

    /// <summary>
    /// The platform-dependent host-stack backstop. It can only stop a run EARLIER than the
    /// deterministic depth limit, so a case that hits it is not comparing what it declared and is
    /// rejected rather than compared — exactly the treatment stack sufficiency deserves.
    /// </summary>
    private const string StackBackstopCategory = "EvaluationStackExhausted";

    internal static MetamorphicExecution Execute(MetamorphicCase testCase)
    {
        ArgumentNullException.ThrowIfNull(testCase);

        if (!testCase.Precondition.Satisfied)
            return new MetamorphicExecution(testCase, false, testCase.Precondition.Reason, null, null);

        var leftOptions = OptionsFor(testCase.LeftProfile);
        var rightOptions = OptionsFor(testCase.RightProfile);
        var evidence = testCase.CollectsEvidence;

        // A RIGHT-FIRST case observes the right member before anything else has run in this
        // process pass. It is still reported as the right member: only the order changes, so a
        // relation that holds one way round and not the other is a state leak, not a policy.
        MetamorphicOperationalObservation? first = null;
        if (testCase.ExecutionOrder == MetamorphicExecutionOrder.RightFirst)
        {
            if (!ObserveRight(testCase, rightOptions, evidence, out var early, out var earlyReason))
                return new MetamorphicExecution(testCase, false, "right-" + earlyReason, null, null);
            first = early;
        }

        if (!TryObserve(testCase.LeftSource, testCase.LeftProfile, leftOptions, evidence, out var left, out var leftReason))
            return new MetamorphicExecution(testCase, false, "left-" + leftReason, null, first);

        if (RunInterference(testCase) is { } interferenceReason)
            return new MetamorphicExecution(testCase, false, interferenceReason, left, first);

        MetamorphicOperationalObservation right;
        if (first is { } observedFirst && testCase.RunPlan == MetamorphicRunPlan.Sequential)
        {
            // Nothing between the two observations to re-run; the early one IS the right member.
            right = observedFirst;
        }
        else if (!ObserveRight(testCase, rightOptions, evidence, out right, out var rightReason))
        {
            return new MetamorphicExecution(testCase, false, "right-" + rightReason, left, null);
        }

        if (StackBackstopReason(left, right) is { } stackReason)
            return new MetamorphicExecution(testCase, false, stackReason, left, right);

        if (testCase.LeftEvidence.Unsatisfied(left, "left") is { } leftEvidence)
            return new MetamorphicExecution(testCase, false, leftEvidence, left, right);

        if (testCase.RightEvidence.Unsatisfied(right, "right") is { } rightEvidence)
            return new MetamorphicExecution(testCase, false, rightEvidence, left, right);

        return new MetamorphicExecution(testCase, true, "ok", left, right);
    }

    /// <summary>Observes the right member under whichever run plan the case declared.</summary>
    private static bool ObserveRight(
        MetamorphicCase testCase,
        RunOptions rightOptions,
        bool evidence,
        out MetamorphicOperationalObservation right,
        out string reason)
        => testCase.RunPlan == MetamorphicRunPlan.BoundedParallel
            ? TryObserveInParallel(testCase, rightOptions, evidence, out right, out reason)
            : TryObserve(testCase.RightSource, testCase.RightProfile, rightOptions, evidence, out right, out reason);

    /// <summary>
    /// Runs ONE program through one entry point with fresh state and reports what it produced
    /// and what it charged. Returns <c>false</c> only for a template precondition failure (a
    /// surface that needs a parsable source was given one the front end rejects); every
    /// unexpected exception escapes.
    /// </summary>
    internal static bool TryObserve(
        string source,
        MetamorphicExecutionProfile profile,
        RunOptions options,
        bool collectEvidence,
        out MetamorphicOperationalObservation observation,
        out string reason)
        => MetamorphicSurfaces.TryObserve(source, profile, options, collectEvidence, out observation, out reason);

    /// <summary>The Phase 1/2 signature: the observed evaluator surface under one shared policy.</summary>
    internal static bool TryObserve(
        string source,
        EvaluationLimits? limits,
        bool enableOptimizations,
        out MetamorphicOperationalObservation observation,
        out string reason)
    {
        var profile = MetamorphicExecutionProfile.Observed(limits, enableOptimizations);
        return TryObserve(source, profile, OptionsFor(profile), collectEvidence: false, out observation, out reason);
    }

    /// <summary>
    /// One immutable <see cref="RunOptions"/> per profile, created once and reused for every
    /// invocation that profile drives — including the parallel tasks. Sharing it is the point:
    /// no counters, caches, or diagnostics may live on configuration.
    /// </summary>
    internal static RunOptions OptionsFor(MetamorphicExecutionProfile profile)
    {
        ArgumentNullException.ThrowIfNull(profile);
        return new RunOptions { EvaluationLimits = profile.Limits };
    }

    /// <summary>
    /// Executes whatever the run plan interposes between the two observations. Returns a
    /// rejection reason when the interference itself did not do its job (a "failed reservation"
    /// run that unexpectedly succeeded proves nothing about recovery), otherwise <c>null</c>.
    /// </summary>
    private static string? RunInterference(MetamorphicCase testCase)
    {
        switch (testCase.RunPlan)
        {
            case MetamorphicRunPlan.Sequential:
            case MetamorphicRunPlan.BoundedParallel:
                return null;

            case MetamorphicRunPlan.AfterFailedRun:
            {
                if (testCase.InterferenceSource is not { } source)
                    return "interference-source-missing";

                var profile = testCase.RightProfile with { Limits = testCase.InterferenceLimits ?? testCase.RightProfile.Limits };
                if (!TryObserve(source, profile, OptionsFor(profile), collectEvidence: false, out var failed, out var reason))
                    return "interference-" + reason;

                return failed.Semantic.Outcome == "err" ? null : "interference-run-did-not-fail";
            }

            case MetamorphicRunPlan.AfterInterleavedRuns:
            {
                var source = testCase.InterferenceSource ?? IsolationProbeSource;
                var profile = testCase.RightProfile with { Limits = testCase.InterferenceLimits };
                var options = OptionsFor(profile);
                for (var i = 0; i < InterleavedRunCount; i++)
                {
                    if (!TryObserve(source, profile, options, collectEvidence: false, out _, out var reason))
                        return "interference-" + reason;
                }

                return null;
            }

            default:
                throw new MetamorphicHarnessException($"No execution is implemented for run plan {testCase.RunPlan}.");
        }
    }

    /// <summary>
    /// Observes the right member from a bounded set of DISTINCT threads that all coexist and all
    /// share one immutable limits/options instance, entering the evaluator in index order.
    ///
    /// <para>Results are collected BY INDEX, never by completion order, and the reported
    /// observation is thread 0 unless some thread differs — in which case the LOWEST differing
    /// index is reported, so a leak becomes a deterministic mismatch instead of an intermittent
    /// pass. Nothing here asserts timing.</para>
    ///
    /// <para><b>Why the evaluations are handed off rather than overlapped.</b> The fuzzing engine's
    /// feedback is edge instrumentation woven into the language assembly, and that instrumentation
    /// keeps its "previous location" in ONE process-wide slot with no synchronisation and no thread
    /// affinity. Two evaluations running at the same instant therefore interleave their
    /// read-modify-writes of that slot and stamp edge indices that no sequential execution can
    /// produce — so the coverage of a concurrent run is a function of the thread schedule, not of
    /// the input. Measured on this repository: forty parallel corpus files replayed three times
    /// produced 69237, 70798 and 68518 features for an unchanged 8 covered edges, while forty
    /// sequential files produced 22317/22324/22329. The engine reads every one of those phantom
    /// features as new coverage, saves the input, and mutates around it forever — which is how a
    /// law with only forty distinct cases came to hold 2137 of 2820 corpus units, and, worse, how
    /// schedule noise came to occupy the shared feature map that every OTHER family's genuine
    /// coverage has to compete for.</para>
    ///
    /// <para>So the threads are real, they coexist, they share one immutable configuration
    /// instance and they hand the evaluator over in a fixed order. That still exercises everything
    /// this law is about — run state that is thread-affine, static mutable state, a configuration
    /// object that accumulates, a cache or budget that outlives its run — because each observation
    /// happens on a different thread from the one before it. What it deliberately no longer does
    /// inside the fuzzing loop is overlap two evaluations in time; simultaneous execution is
    /// covered by <c>MetamorphicPhase3FamilyTests</c>, which runs without instrumentation and can
    /// therefore afford it.</para>
    /// </summary>
    private static bool TryObserveInParallel(
        MetamorphicCase testCase,
        RunOptions options,
        bool collectEvidence,
        out MetamorphicOperationalObservation observation,
        out string reason)
    {
        var observations = new MetamorphicOperationalObservation?[ParallelTaskCount];
        var reasons = new string[ParallelTaskCount];
        var failures = new Exception?[ParallelTaskCount];

        // Thread i may enter the evaluator only once thread i-1 has left it. Thread 0 starts open,
        // so the hand-off order is 0, 1, ... and the edge sequence is a function of the input.
        var admit = new ManualResetEventSlim[ParallelTaskCount];
        var threads = new Thread[ParallelTaskCount];
        for (var i = 0; i < ParallelTaskCount; i++) admit[i] = new ManualResetEventSlim(i == 0);

        for (var i = 0; i < ParallelTaskCount; i++)
        {
            var index = i;
            threads[index] = new Thread(() =>
            {
                admit[index].Wait();
                try
                {
                    observations[index] = TryObserve(
                        testCase.RightSource, testCase.RightProfile, options, collectEvidence, out var one, out var why)
                        ? one
                        : null;
                    reasons[index] = why;
                }
                catch (Exception exception)
                {
                    // Carried out and rethrown on the calling thread: a crash the fuzzing engine
                    // must see may not be swallowed by a worker, and may not deadlock the rest.
                    failures[index] = exception;
                    reasons[index] = "thread-faulted";
                }
                finally
                {
                    if (index + 1 < ParallelTaskCount) admit[index + 1].Set();
                }
            })
            {
                IsBackground = true,
                Name = "metamorphic-isolation-" + index.ToString(CultureInfo.InvariantCulture),
            };
        }

        foreach (var thread in threads) thread.Start();
        foreach (var thread in threads) thread.Join();
        foreach (var gate in admit) gate.Dispose();

        // Rethrown with its ORIGINAL type and stack, not wrapped: the fuzzing engine classifies a
        // crash by what escaped, and an isolation worker must not disguise it.
        foreach (var failure in failures)
        {
            if (failure is not null) ExceptionDispatchInfo.Capture(failure).Throw();
        }

        if (observations[0] is not { } first)
        {
            observation = null!;
            reason = reasons[0];
            return false;
        }

        for (var index = 1; index < ParallelTaskCount; index++)
        {
            if (observations[index] is not { } other)
            {
                observation = null!;
                reason = reasons[index];
                return false;
            }

            if (other != first)
            {
                observation = other;
                reason = "ok";
                return true;
            }
        }

        observation = first;
        reason = "ok";
        return true;
    }

    /// <summary>The rejection reason when either side hit the machine-dependent stack backstop.</summary>
    private static string? StackBackstopReason(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
        => IsStackBackstop(left) || IsStackBackstop(right) ? "platform-dependent-stack-backstop" : null;

    private static bool IsStackBackstop(MetamorphicOperationalObservation observation)
        => string.Equals(observation.Semantic.ErrorCategory, StackBackstopCategory, StringComparison.Ordinal);

    /// <summary>
    /// A/B/A state-isolation check for the executor: observe <paramref name="source"/>,
    /// observe an unrelated program, observe <paramref name="source"/> again. The two
    /// observations of the same program must be identical, counters included.
    /// </summary>
    internal static void AssertIsolated(string source, EvaluationLimits? limits, bool enableOptimizations)
        => AssertIsolated(source, MetamorphicExecutionProfile.Observed(limits, enableOptimizations));

    internal static void AssertIsolated(string source, MetamorphicExecutionProfile profile)
    {
        var options = OptionsFor(profile);
        if (!TryObserve(source, profile, options, collectEvidence: false, out var first, out var reason)) return;

        var probeProfile = MetamorphicExecutionProfile.Observed(null, profile.EnableOptimizations);
        _ = TryObserve(IsolationProbeSource, probeProfile, OptionsFor(probeProfile), false, out _, out _);

        if (!TryObserve(source, profile, options, collectEvidence: false, out var second, out _) || first != second)
        {
            throw new MetamorphicHarnessException(
                "A/B/A isolation failed: an unrelated evaluation changed a later observation of the same program.\n" +
                $"  source:  {source.Replace("\n", "\\n", StringComparison.Ordinal)}\n" +
                $"  profile: {profile}\n" +
                $"  reason:  {reason}\n" +
                $"  first:   {first}\n" +
                $"  second:  {second}");
        }
    }

    /// <summary>Stable description of how one case was executed, for reports and fingerprints.</summary>
    internal static string DescribeRunPlan(MetamorphicCase testCase)
    {
        ArgumentNullException.ThrowIfNull(testCase);
        return testCase.RunPlan switch
        {
            MetamorphicRunPlan.Sequential => "sequential",
            MetamorphicRunPlan.AfterFailedRun => "after-failed-run",
            MetamorphicRunPlan.AfterInterleavedRuns =>
                "after-" + InterleavedRunCount.ToString(CultureInfo.InvariantCulture) + "-interleaved-runs",
            // Named for what it actually does: that many distinct coexisting threads, entering the
            // evaluator in a fixed order. Calling it "parallel" would overstate the fuzz-loop plan.
            MetamorphicRunPlan.BoundedParallel =>
                "threads-" + ParallelTaskCount.ToString(CultureInfo.InvariantCulture) + "-ordered",
            _ => testCase.RunPlan.ToString(),
        };
    }
}
