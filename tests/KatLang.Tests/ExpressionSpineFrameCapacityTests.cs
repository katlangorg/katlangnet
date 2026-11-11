using System.Text;
using KatLang.Evaluation;
using KatLang.Tests.AsyncEvaluation;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// 2.08a: the expression-spine machines (the synchronous <c>EvalExpressionSpineCounted</c> and its async
/// twin) start their frame buffer at a small shared capacity and grow it by doubling. This is an
/// implementation-only optimization: every spine kind nested past the initial capacity several times
/// over keeps its exact value, error code, message, span, emitted count, step and expression-checkpoint
/// charges on the sync generic, sync optimized and async twin routes, and the per-spine-run allocation
/// stays below what the former sixteen-frame buffer cost on its own.
/// </summary>
public class ExpressionSpineFrameCapacityTests
{
    private sealed record Observation(string Outcome, long Steps, long Checkpoints);

    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static Observation Observe((EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) run)
    {
        var (result, budget) = run;
        var outcome = result.IsOk
            ? $"ok {InvocationRouteCorpus.Value(result.Value.Value)} n={result.Value.EmittedCount}"
            : $"err {result.Error.Code} | {KatLangError.FromEvalError(result.Error).Message.Replace("\n", " / ", StringComparison.Ordinal)} @{result.Error.Span}";
        return new Observation(outcome, budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints);
    }

    /// <summary>One observation per route; the three must agree exactly.</summary>
    private static async Task<Observation> ObserveAllRoutes(string source)
    {
        var program = Program(source);
        var generic = Observe(Evaluator.RunCountedObserved(program, enableOptimizations: false));
        var optimized = Observe(Evaluator.RunCountedObserved(program, enableOptimizations: true));
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var twin = Observe(await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: cache)));
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Equal(generic, optimized);
        Assert.Equal(generic, twin);
        Assert.True(generic.Checkpoints > 0, generic.ToString());
        return generic;
    }

    // ── Spine programs whose machine run needs exactly `depth` frames ────────────────────────────────

    /// <summary><c>k</c> right-nested additions of 1 (k machine frames; value k + 1).</summary>
    private static string RightSum(int k) => k == 0 ? "1" : "1 + (" + RightSum(k - 1) + ")";

    private static string Repeat(string text, int count) => new StringBuilder().Insert(0, text, count).ToString();

    private static readonly string Tens =
        "xs = [" + string.Join(", ", Enumerable.Range(1, 40).Select(i => (i * 10).ToString(System.Globalization.CultureInfo.InvariantCulture))) + "]\n";

    private static (string Source, string Expected) Spine(string kind, int depth) => kind switch
    {
        "binary-right" => (RightSum(depth), $"ok {depth + 1} n=1"),
        "binary-left" => ("1" + Repeat(" + 1", depth), $"ok {depth + 1} n=1"),
        "unary" => (Repeat("-(", depth) + "1" + Repeat(")", depth), depth % 2 == 0 ? "ok 1 n=1" : "ok -1 n=1"),
        // The comparison frame, then the nested operand's frames; the chain's links add no frame.
        "comparison" => ($"0 < {RightSum(depth - 1)} < {depth + 1}", "ok true n=1"),
        // The selection frame, then the nested selector's frames (selection is zero-based).
        "index" => (Tens + $"xs[{RightSum(depth - 1)}]", $"ok {(depth + 1) * 10} n=1"),
        "list" => (Repeat("[", depth) + "1" + Repeat("]", depth), "ok " + Repeat("[", depth) + "1" + Repeat("]", depth) + " n=1"),
        // The interpolation frame, then the nested hole's frames.
        "interpolation" => ($"\"v{{{RightSum(depth - 1)}}}\"", $"ok 'v{depth}' n=1"),
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };

    private static readonly string[] Kinds = ["binary-right", "binary-left", "unary", "comparison", "index", "list", "interpolation"];

    private static readonly int[] Depths = [1, 2, 3, 4, 5, 6, 7, 8, 9, 17, 33];

    public static TheoryData<string, int> SpineCases()
    {
        var data = new TheoryData<string, int>();
        foreach (var kind in Kinds)
            foreach (var depth in Depths)
                data.Add(kind, depth);
        return data;
    }

    [Theory]
    [MemberData(nameof(SpineCases))]
    public async Task Spine_AcrossTheInitialCapacity_HasTheExactValue_AndOneResourceProfile_OnAllRoutes(string kind, int depth)
    {
        var (source, expected) = Spine(kind, depth);
        var observed = await ObserveAllRoutes(source);
        Assert.Equal(expected, observed.Outcome);
    }

    [Fact]
    public async Task SpineCharges_GrowLinearlyWithDepth_SoNoNodeIsSkippedOrRepeated()
    {
        // Each extra right-nested addition is one Binary node plus one literal: a constant step and
        // checkpoint increment per level on every route, across every buffer doubling.
        var observations = new List<Observation>();
        for (var k = 1; k <= 33; k++)
            observations.Add(await ObserveAllRoutes(RightSum(k)));
        var stepIncrement = observations[1].Steps - observations[0].Steps;
        var checkpointIncrement = observations[1].Checkpoints - observations[0].Checkpoints;
        Assert.True(checkpointIncrement > 0);
        for (var i = 1; i < observations.Count; i++)
        {
            Assert.Equal(stepIncrement, observations[i].Steps - observations[i - 1].Steps);
            Assert.Equal(checkpointIncrement, observations[i].Checkpoints - observations[i - 1].Checkpoints);
        }
    }

    // ── Errors unwound through a resized buffer ──────────────────────────────────────────────────────

    public static TheoryData<string, string> ErrorCases => new()
    {
        // The selection frame plus five selector frames: the buffer has doubled twice when the
        // selection fails; the error is positioned at its written selector slot.
        { "xs = [1, 2, 3]\nxs[1 + (1 + (1 + (1 + (1 + 1))))]", "err BadIndex | Bad index @[2:4, 2:33)" },
        { "xs = [1, 2, 3]\nxs[" + RightSum(32) + "]", "err BadIndex | Bad index @[2:4, 2:197)" },
        // The interpolation frame, the selection frame, five selector frames.
        { "xs = [1, 2]\n\"{xs[1 + (1 + (1 + (1 + (1 + 1))))]}\"", "err BadIndex | Bad index @[2:6, 2:35)" },
        { "xs = [1, 2]\n\"{xs[" + RightSum(32) + "]}\"", "err BadIndex | Bad index @[2:6, 2:199)" },
        // A failure at the deepest frame's own apply step, under 17 frames (the operand is a string).
        { Repeat("-(", 17) + "'a'" + Repeat(")", 17), "err TypeMismatch | Type mismatch: operator `-` expects a numeric scalar operand, but the operand was a string: 'a' @[1:32, 1:40)" },
        // A failure whose operand is evaluated at the bottom of 32 frames and decorated on the way out.
        { "xs = [1]\n" + RightSum(31).Replace("(1)", "(xs[2])", StringComparison.Ordinal), "err BadIndex | Bad index @[2:159, 2:160)" },
    };

    [Theory]
    [MemberData(nameof(ErrorCases))]
    public async Task Error_UnwoundThroughAResizedBuffer_HasTheExactCodeMessageAndSpan_OnAllRoutes(string source, string expected)
    {
        var observed = await ObserveAllRoutes(source);
        Assert.Equal(expected, observed.Outcome);
    }

    // ── Allocation guard ─────────────────────────────────────────────────────────────────────────────

    private const int Properties = 256;

    /// <summary>
    /// <paramref name="Properties"/> properties, each read once: <c>Pi = 1 + 1</c> starts one spine run
    /// per property, <c>Pi = 2</c> none; everything else about the two programs is the same.
    /// </summary>
    private static Expr PropertyProgram(string body)
    {
        var source = new StringBuilder();
        for (var i = 0; i < Properties; i++)
            source.Append('P').Append(i).Append(" = ").Append(body).Append('\n');
        source.AppendJoin(", ", Enumerable.Range(0, Properties).Select(i => "P" + i)).Append('\n');
        return Program(source.ToString());
    }

    private static long MinimumAllocation(Func<Evaluator.CountedResult> run)
    {
        for (var i = 0; i < 3; i++)
            _ = run();
        var minimum = long.MaxValue;
        for (var i = 0; i < 5; i++)
        {
            var before = GC.GetAllocatedBytesForCurrentThread();
            _ = run();
            minimum = Math.Min(minimum, GC.GetAllocatedBytesForCurrentThread() - before);
        }

        return minimum;
    }

    private static Evaluator.CountedResult RunSync(Expr program)
    {
        var (result, _) = Evaluator.RunCountedObserved(program, enableOptimizations: true);
        Assert.True(result.IsOk);
        return result.Value;
    }

    private static Evaluator.CountedResult RunTwin(Expr program)
    {
        // Nothing in these programs can suspend, so the twin completes inline on this thread and the
        // thread's allocation counter sees the whole run.
        var pending = Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache());
        Assert.True(pending.IsCompleted);
        var (result, _) = pending.Result;
        Assert.True(result.IsOk);
        return result.Value;
    }

    /// <summary>
    /// The slope also carries the run's own work (the binary result, the property's cached value, and on
    /// the twin its async machinery), so each route has its own bound. Measured in November 2026 on
    /// the Debug test build (x64): with the former sixteen-frame buffer (16 × 56 + 24 = 920 bytes) the
    /// slope was 1,558.5 bytes synchronously and 3,887.4 on the twin; with the two-frame buffer
    /// (2 × 56 + 24 = 136 bytes) it is 774.5 and 3,103.4 — exactly the 784-byte difference on both.
    /// Most of that slope was never the spine: it was the run's pre-evaluation reference tables,
    /// which grew by doubling over the larger tree. Since 2026-11-11 those tables are sized from the
    /// node count an earlier walk of the same run produced, and the slopes are 540.8 and 3,036.5
    /// (the twin's entry walks no tree first, so only its validation tables are sized); sixteen
    /// frames would make them 1,324.8 and 3,820.5. The synchronous bound sits between the sized and
    /// the unsized slope, so it fails both when sixteen frames return and when the sizing is lost;
    /// the twin's sits near the midpoint to sixteen frames. Unrelated noise fails neither: each
    /// window is the minimum of five runs over 256 spine runs, so one background-GC quantum moves
    /// the slope by at most about 32 bytes. A coarse in-process ratio, not a strict count.
    /// </summary>
    [Theory]
    [InlineData(false, 660)]
    [InlineData(true, 3_400)]
    public void PerSpineRunAllocation_StaysBelowTheFormerSixteenFrameBuffer(bool asyncTwin, int bound)
    {
        var withSpine = PropertyProgram("1 + 1");
        var withoutSpine = PropertyProgram("2");
        Func<Expr, Evaluator.CountedResult> run = asyncTwin ? RunTwin : RunSync;
        Assert.Equal(InvocationRouteCorpus.Value(run(withoutSpine).Value), InvocationRouteCorpus.Value(run(withSpine).Value));

        var slope = (MinimumAllocation(() => run(withSpine)) - MinimumAllocation(() => run(withoutSpine))) / (double)Properties;

        Assert.True(slope < bound, $"{(asyncTwin ? "async twin" : "sync")}: {slope:F1} bytes per spine run (bound {bound})");
    }
}
