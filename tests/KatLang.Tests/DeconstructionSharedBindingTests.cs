using System.Text;
using System.Threading.Tasks;

namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the shared lazy binding of one assignment deconstruction. A comma binding
/// pattern <c>x0, ..., x{N-1} = RHS</c> elaborates to N target properties that each apply the SAME
/// shared N-capture pattern to the SAME hoisted <c>$deconstruct$</c> source. Demanding every target
/// formerly rebound the whole N-capture pattern once per target — O(N^2) (and, because one bind was
/// itself O(N), effectively O(N^3)). The correction binds the group once per binding context in a
/// run-scoped cache and projects each target's slot in O(1), and makes the single bind itself linear.
///
/// <para>These tests pin the preserved semantics (deferred binding, per-position values across every
/// pattern shape, written-pattern arity errors, demand-order independence, run isolation) AND the
/// operational contract that demanding any number of targets any number of times performs exactly ONE
/// full bind per group per run, measured through a passive RUN-SCOPED <see cref="EvaluationObservations"/>
/// object (one per observed run, carried through the evaluation context, no static state and no reset).
/// Its <see cref="EvaluationObservations.DeconstructionFullBindCount"/> is recorded in the single bind
/// path shared by the old and new implementations, so "== 1" fails under the old per-target path
/// (which records N).</para>
/// </summary>
public class DeconstructionSharedBindingTests
{
    private static decimal[] Atoms(string source) => KatLangEngine.EvaluateToAtoms(source).ToArray();

    /// <summary>Runs <paramref name="source"/> and returns (atoms, number of full deconstruction binds).</summary>
    private static (decimal[] Atoms, long Binds) RunCountingBinds(string source)
        => (Atoms(source), CountFullBinds(source));

    /// <summary>
    /// Full deconstruction binds performed by ONE fresh observed run of <paramref name="source"/>. A
    /// new <see cref="EvaluationObservations"/> is created per call (zero by construction — no reset),
    /// so sequential, repeated, and concurrent measurements are independent. Works for programs whose
    /// evaluation fails too: a failed full bind is still one begun binding computation and is counted.
    /// </summary>
    private static long CountFullBinds(string source)
    {
        var frontEnd = FrontEndPipeline.Process(source);
        Assert.False(
            frontEnd.HasErrors,
            "expected a parseable program: " + string.Join("; ", frontEnd.Diagnostics.Select(d => d.Message)));

        var observations = new EvaluationObservations();
        _ = Evaluator.RunCountedObserved(new Expr.Block(frontEnd.ElaboratedRoot), observations: observations);
        return observations.DeconstructionFullBindCount;
    }

    private static string WideSource(int n, string rhs)
    {
        var sb = new StringBuilder();
        for (var i = 0; i < n; i++)
            sb.Append(i == 0 ? "x0" : $", x{i}");
        return sb.Append(" = ").Append(rhs).ToString();
    }

    private static string AllTargets(int n)
    {
        var sb = new StringBuilder();
        for (var i = 0; i < n; i++)
            sb.Append(i == 0 ? "x0" : $", x{i}");
        return sb.ToString();
    }

    // ───────────────────────── single-target compatibility ─────────────────────────

    [Fact]
    public void DemandFirstTargetOnly_ReturnsItsValue_WithOneBind()
    {
        var (atoms, binds) = RunCountingBinds("a, b, c, d = (10, 20, 30, 40)\nOutput = a");
        Assert.Equal([10m], atoms);
        Assert.Equal(1, binds);
    }

    [Fact]
    public void DemandMiddleTargetOnly_ReturnsItsValue_WithOneBind()
    {
        var (atoms, binds) = RunCountingBinds("a, b, c, d = (10, 20, 30, 40)\nOutput = c");
        Assert.Equal([30m], atoms);
        Assert.Equal(1, binds);
    }

    [Fact]
    public void DemandLastTargetOnly_ReturnsItsValue_WithOneBind()
    {
        var (atoms, binds) = RunCountingBinds("a, b, c, d = (10, 20, 30, 40)\nOutput = d");
        Assert.Equal([40m], atoms);
        Assert.Equal(1, binds);
    }

    // ───────────────────────── all-target reuse (one shared bind) ─────────────────────────

    [Fact]
    public void DemandAllTargets_PerformsExactlyOneBind()
    {
        const int n = 200;
        var (atoms, binds) = RunCountingBinds(WideSource(n, $"range(1, {n})") + $"\nOutput = sum(({AllTargets(n)}))");
        Assert.Equal([n * (n + 1) / 2m], atoms); // sum 1..n
        Assert.Equal(1, binds);
    }

    [Fact]
    public void DemandAllTargetsTwice_StillOneBind()
    {
        const int n = 60;
        // Reference every target in two separate output rows: still one shared bind for the run.
        var source = WideSource(n, $"range(1, {n})") + $"\nOutput = sum(({AllTargets(n)})), sum(({AllTargets(n)}))";
        var (atoms, binds) = RunCountingBinds(source);
        var expected = n * (n + 1) / 2m;
        Assert.Equal([expected, expected], atoms);
        Assert.Equal(1, binds);
    }

    [Fact]
    public void DemandTargetsInReverseAndInterleavedOrder_AreEquivalent_AndOneBind()
    {
        const string forward = "a, b, c, d = (1, 2, 3, 4)\nOutput = a, b, c, d";
        const string reverse = "a, b, c, d = (1, 2, 3, 4)\nOutput = d, c, b, a";
        const string interleaved = "a, b, c, d = (1, 2, 3, 4)\nOutput = c, a, d, b, a, d";

        var (forwardAtoms, forwardBinds) = RunCountingBinds(forward);
        Assert.Equal([1m, 2m, 3m, 4m], forwardAtoms);
        Assert.Equal(1, forwardBinds);

        var (reverseAtoms, reverseBinds) = RunCountingBinds(reverse);
        Assert.Equal([4m, 3m, 2m, 1m], reverseAtoms);
        Assert.Equal(1, reverseBinds);

        var (interleavedAtoms, interleavedBinds) = RunCountingBinds(interleaved);
        Assert.Equal([3m, 1m, 4m, 2m, 1m, 4m], interleavedAtoms);
        Assert.Equal(1, interleavedBinds); // repeated references never rebind
    }

    // ───────────────────────── pattern semantics (via the shared bind) ─────────────────────────

    [Fact]
    public void FixedTargets_BindByPosition()
        => Assert.Equal([1m, 2m, 3m], Atoms("a, b, c = (1, 2, 3)\na, b, c"));

    [Fact]
    public void CollectingBindingInMiddle_CollectsMovableItems()
        => Assert.Equal([1m, 2m, 4m], Atoms("a, *b, c = (1, 2, 3, 4)\na, b.count, c"));

    [Fact]
    public void CollectingBindingAtBeginning_CollectsLeadingItems()
        => Assert.Equal([2m, 3m], Atoms("*a, b = (1, 2, 3)\na.count, b"));

    [Fact]
    public void CollectingBindingAtEnd_CollectsTrailingItems()
        => Assert.Equal([1m, 2m], Atoms("a, *b = (1, 2, 3)\na, b.count"));

    [Fact]
    public void EmptyCollectingBinding_CollectsEmptyList()
        => Assert.Equal([1m, 2m, 0m], Atoms("a, b, *c = (1, 2)\na, b, c.count"));

    [Fact]
    public void ListRightHandSide_OpensLikeSequence()
        => Assert.Equal([1m, 2m, 3m], Atoms("a, b, c = [1, 2, 3]\na, b, c"));

    [Fact]
    public void SequenceRightHandSide_Splits()
        => Assert.Equal([1m, 2m], Atoms("a, b = (1, 2)\na, b"));

    [Fact]
    public void NestedStructuredValues_StayIntactPerTarget()
        => Assert.Equal([3m, 7m], Atoms("a, b = ((1, 2), (3, 4))\nsum(a), sum(b)"));

    // ───────────────────────── deferred + errors ─────────────────────────

    [Fact]
    public void UnusedInvalidDeconstruction_IsSilent_AndNeverBinds()
    {
        var (atoms, binds) = RunCountingBinds("x, y = 1\nOutput = 0");
        Assert.Equal([0m], atoms);
        Assert.Equal(0, binds); // deferred: nothing demanded, nothing bound
    }

    [Fact]
    public void WrongArity_WhenDemanded_FailsAgainstWrittenPattern()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("x, y, z = (1, 2)\nOutput = x"));
        var message = failure.ToDisplayString();
        Assert.Contains("Assignment pattern `x, y, z`", message, StringComparison.Ordinal);
        Assert.DoesNotContain("(inline library)", message, StringComparison.Ordinal);
    }

    [Fact]
    public void RightHandSideError_IsDeferred_SurfacingOnlyWhenATargetIsDemanded()
    {
        // Unused: the erroring RHS never evaluates through the shared bind.
        Assert.Equal([5m], Atoms("x, y = (1, 1 / 0)\nOutput = 5"));
        // Demanded: the RHS evaluates through the shared bind and its error surfaces.
        Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("x, y = (1, 1 / 0)\nOutput = x"));
    }

    [Fact]
    public void FailedBind_Counting_IsDeferredAndNotCached()
    {
        // Documented FAILURE-PATH policy (a residual, NOT a shared/linear path): a failed full bind is
        // counted like a successful one (it is one begun binding computation), but failures are never
        // cached, so the failure path is not shared across targets the way success is.
        //   * unused invalid deconstruction: no bind at all (deferred).
        Assert.Equal(0, CountFullBinds("x, y, z = (1, 2)\nOutput = 0"));
        //   * one demanded invalid target: exactly one failed full bind.
        Assert.Equal(1, CountFullBinds("x, y, z = (1, 2)\nOutput = x"));
        //   * demanding more targets does not add binds here because evaluation short-circuits at the
        //     first failed target, so ordinary output reaches the group's bind once. (An uncached
        //     failure would rebind only if the group were demanded again past the error, which
        //     short-circuit semantics prevent within one run.)
        Assert.Equal(1, CountFullBinds("x, y, z = (1, 2)\nOutput = x, y, z"));
    }

    // ───────────────────────── binding context separation ─────────────────────────

    [Fact]
    public void RightHandSideIsEvaluatedOnce_AcrossAllTargets()
    {
        // The shared source $deconstruct$ is a zero-argument property, evaluated once and cached; the
        // shared bind consumes that one value. A side-effect-free proxy for "evaluated once" is that a
        // wide all-target demand performs exactly one bind (already covered) AND yields consistent
        // per-position values regardless of how many targets are demanded.
        Assert.Equal([1m, 5m, 10m], Atoms("a, b, c, d, e, f, g, h, i, j = range(1, 10)\na, e, j"));
    }

    [Fact]
    public void DistinctDeconstructions_EachBindOnce()
    {
        // Two independent deconstruction groups, all targets demanded: one bind per group.
        var (atoms, binds) = RunCountingBinds(
            "a, b = (1, 2)\nc, d = (3, 4)\nOutput = a, b, c, d");
        Assert.Equal([1m, 2m, 3m, 4m], atoms);
        Assert.Equal(2, binds);
    }

    [Fact]
    public void SameGroupInDifferentCallContexts_BindsPerContext()
    {
        // One deconstruction whose RHS depends on the enclosing parameter, demanded from two calls.
        // Each call is a distinct binding context (a=1 vs a=2), so the shared-bind cache must NOT
        // collapse them: two binds, correct per-call values.
        const string source =
            """
            F(a) = {
                p, q = (a, a * 10)
                Output = p + q
            }
            Output = F(1), F(2)
            """;
        var (atoms, binds) = RunCountingBinds(source);
        Assert.Equal([11m, 22m], atoms); // 1+10, 2+20
        Assert.Equal(2, binds);
    }

    // ───────────────────────── run isolation ─────────────────────────

    [Fact]
    public void SeparateRuns_EachRebindFreshly()
    {
        const string source = "a, b, c = (1, 2, 3)\nOutput = a, b, c";

        var first = RunCountingBinds(source);
        Assert.Equal([1m, 2m, 3m], first.Atoms);
        Assert.Equal(1, first.Binds);

        // A second, independent run gets its own run-scoped cache: it rebinds (no cross-run leakage).
        var second = RunCountingBinds(source);
        Assert.Equal([1m, 2m, 3m], second.Atoms);
        Assert.Equal(1, second.Binds);
    }

    [Fact]
    public void ObservationsAreIndependentAcrossInterleavedRuns()
    {
        // A/B/A: an unrelated run B between two runs of A must not perturb A's observation, and the
        // order of observation must not matter. Each run owns a fresh observations object.
        const string a = "a, b = (1, 2)\nOutput = a, b";                 // one group
        const string b = "p, q = (1, 2)\nr, s = (3, 4)\nOutput = p, q, r, s"; // two groups

        Assert.Equal(1, CountFullBinds(a));
        Assert.Equal(2, CountFullBinds(b));
        Assert.Equal(1, CountFullBinds(a));
    }

    [Fact]
    public void ConcurrentRuns_ObserveIndependentBindCounts()
    {
        // Run-scoped observations live on one object per run, so concurrent runs on different threads
        // never contend or leak — the exact failure mode a [ThreadStatic] or ambient counter risks.
        // Each of many parallel runs must see EXACTLY its own group's single shared bind.
        const string source = "a, b, c, d = (1, 2, 3, 4)\nOutput = sum((a, b, c, d))";
        var binds = new long[64];

        Parallel.For(0, binds.Length, i => binds[i] = CountFullBinds(source));

        Assert.All(binds, count => Assert.Equal(1, count));
    }

    [Fact]
    public void FreshRunAfterFailedBinding_Succeeds()
    {
        Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("x, y, z = (1, 2)\nOutput = x"));
        // A failed bind is never cached across runs; a subsequent valid run is unaffected.
        Assert.Equal([1m, 2m, 3m], Atoms("x, y, z = (1, 2, 3)\nx, y, z"));
    }

    // ───────────────────────── scaling regression ─────────────────────────

    [Fact]
    public void DemandAllTargets_BindCountIsOne_RegardlessOfTargetCount()
    {
        // The defining operational property: one full bind for the whole group no matter how many
        // targets are demanded. The old per-target path performed N binds; this asserts exactly one.
        foreach (var n in new[] { 50, 250, 1000 })
        {
            var (_, binds) = RunCountingBinds(WideSource(n, $"range(1, {n})") + $"\nOutput = sum(({AllTargets(n)}))");
            Assert.Equal(1, binds);
        }
    }

    [Fact]
    public void EvaluateAllTargets_AllocationGrowsLinearlyInTargetCount()
    {
        // Deterministic scaling guard over the WHOLE evaluate-all path (shared bind + per-target
        // projection). Demanding every target of a 2N deconstruction must allocate only a small linear
        // factor over N. The old path rebound the full N-capture pattern per target and each bind was
        // itself O(N), so doubling N grew the work far more than 2x; the corrected path is ~2x.
        // Thread-local allocation is measured (parallel tests never pollute it) and only the growth
        // RATIO is asserted, never elapsed time.
        _ = Atoms(EvaluateAllSource(256)); // warm

        var baseAllocation = MeasureEvaluateAllAllocation(1000);
        var doubleAllocation = MeasureEvaluateAllAllocation(2000);

        var ratio = (double)doubleAllocation / baseAllocation;
        Assert.True(
            ratio < 3.0,
            $"evaluate-all allocation for 2N targets grew {ratio:F2}x over N (expected ~2x linear; the " +
            $"previous per-target quadratic path grew super-linearly). N={baseAllocation} bytes, 2N={doubleAllocation} bytes.");
    }

    private static string EvaluateAllSource(int n)
        => WideSource(n, $"range(1, {n})") + $"\nOutput = sum(({AllTargets(n)}))";

    private static long MeasureEvaluateAllAllocation(int n)
    {
        var source = EvaluateAllSource(n);
        _ = Atoms(source); // JIT this exact size before measuring

        var before = GC.GetAllocatedBytesForCurrentThread();
        _ = Atoms(source);
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }
}
