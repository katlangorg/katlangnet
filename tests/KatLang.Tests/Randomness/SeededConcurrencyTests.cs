using System.Numerics;
using KatLang.Tests.ConcurrencyReentrancy;
using static KatLang.Tests.Randomness.SeededRun;

namespace KatLang.Tests.Randomness;

/// <summary>
/// Isolation of seeded streams under concurrency, beyond the pair matrix in
/// <see cref="ConcurrencyCorpus"/> (scenario <see cref="ConcurrencyScenario.SeededStream"/>):
/// the absolute anchor that the seeded sentinels mean what the oracle says, a
/// DETERMINISTICALLY interleaved overlap (one seeded run suspended mid-stream while
/// same-seed runs complete), and cancellation beside a seeded run. No locking exists
/// on the per-run source — isolation by run identity is the whole mechanism.
/// </summary>
public class SeededConcurrencyTests
{
    private static readonly long Seed = ConcurrencyCorpus.SharedSeededOptions.RandomSeed!.Value;

    /// <summary>The oracle's expectation for <see cref="ConcurrencyCorpus.SeededRandom"/>, in evaluation order.</summary>
    private static IReadOnlyList<Decimal128> ExpectedSeededRandom()
    {
        var words = Words(Seed);
        var fraction = ReferenceRandomOracle.Random(words, D(0), D(1));
        var scaled = ReferenceRandomOracle.Random(words, D(2), D(6));
        var p = ReferenceRandomOracle.RandomInt(words, 0, 1_000_000);   // P: drawn once, reused
        var pCall = ReferenceRandomOracle.RandomInt(words, 0, 1_000_000); // P(): redrawn
        var total = Decimal128.Zero;
        for (var i = 0; i < 4; i++)
            total += ReferenceRandomOracle.RandomInt(words, 0, 10);
        var last = ReferenceRandomOracle.RandomInt(words, -5, 5);
        return [fraction, scaled, p, p, pCall, total, last];
    }

    [Fact]
    public void PowerAnchor_TheSeededSentinelMeansWhatTheOracleSays()
    {
        // A pure differential cannot see a defect that skews baseline and concurrent
        // observation identically; the sentinel's absolute meaning is pinned here.
        var success = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run(ConcurrencyCorpus.SeededRandom, ConcurrencyCorpus.SharedSeededOptions));

        AssertSameAtoms(ExpectedSeededRandom(), success.Atoms);
    }

    [Fact]
    public void SeededRun_SuspendedMidStream_OthersCompleteWithTheSameSeed_AndItResumesToItsBaseline()
    {
        // The gated run has already consumed the first two draws when it suspends at
        // its first property access (P); same-seed runs then execute the WHOLE program
        // to completion. A shared or continued generator would advance the suspended
        // run's stream, so its later values would diverge from the baseline.
        var root = ConcurrencyHarness.ParseRoot(ConcurrencyCorpus.SeededRandom);
        var baseline = ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, root, randomSeed: Seed);
        var baselineEngine = ConcurrencyHarness.ObserveEngine(ConcurrencyCorpus.SeededRandom, options: ConcurrencyCorpus.SharedSeededOptions);
        Assert.StartsWith("ok", baseline, StringComparison.Ordinal);

        var gate = new EvaluationGate();
        var gatedCache = new GatedZeroArgPropertyResultCache(gate, gateAtAccess: 1);
        string? gatedObservation = null;
        Exception? gatedFailure = null;
        var gatedThread = new Thread(() =>
        {
            try
            {
                gatedObservation = ConcurrencyHarness.EncodeCounted(Evaluator.RunCounted(root, gatedCache, randomSeed: Seed));
            }
            catch (Exception ex)
            {
                gatedFailure = ex;
            }
        })
        {
            IsBackground = true,
            Name = "katlang-gated-seeded",
        };

        gatedThread.Start();
        try
        {
            gate.WaitUntilInside();

            for (var i = 0; i < 3; i++)
            {
                Assert.Equal(baseline, ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, root, randomSeed: Seed));
                Assert.Equal(baselineEngine, ConcurrencyHarness.ObserveEngine(ConcurrencyCorpus.SeededRandom, options: ConcurrencyCorpus.SharedSeededOptions));
            }
        }
        finally
        {
            gate.Release();
        }

        Assert.True(gatedThread.Join(ConcurrencyHarness.WaitBudget), "the gated seeded run never finished after release");
        Assert.Null(gatedFailure);
        Assert.True(
            gatedObservation == baseline,
            "A seeded run suspended mid-stream resumed to a DIFFERENT observation than its sequential baseline — "
            + $"same-seed runs that completed during its suspension advanced or reseeded its stream.\n"
            + $"  baseline: {baseline}\n  observed: {gatedObservation}");
    }

    [Fact]
    public void CancelledSeededRun_BesideACompletingOne_LeavesTheOtherAndLaterRunsAtTheirBaseline()
    {
        var root = ConcurrencyHarness.ParseRoot(ConcurrencyCorpus.SeededRandom);
        var baseline = ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunPlain, root, randomSeed: Seed);
        using var cancelled = new CancellationTokenSource();
        cancelled.Cancel();

        var observed = ConcurrencyHarness.RunConcurrently(
            ("cancelled", () =>
            {
                Assert.Throws<OperationCanceledException>(() => Evaluator.Run(root, null, Seed, cancelled.Token));
                return "cancelled";
            }),
            ("seeded", () => ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunPlain, root, randomSeed: Seed)));

        Assert.Equal("cancelled", observed[0]);
        Assert.Equal(baseline, observed[1]);

        // A later run with the same seed starts the stream from its beginning.
        Assert.Equal(baseline, ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunPlain, root, randomSeed: Seed));
        Assert.Equal(baseline, ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunPlain, root, randomSeed: Seed));
    }
}
