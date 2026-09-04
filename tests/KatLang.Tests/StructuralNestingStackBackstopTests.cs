using System.Text.RegularExpressions;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// In-process contracts of the structural-nesting stack backstop (audit finding K2-R1,
/// September 2026; the process-survival proof on hostile small stacks is
/// <see cref="StructuralNestingStackBackstopProcessTests"/>): the probe at the two row-loop
/// funnels changes no completing run, moves no operational counter, keeps the synchronous
/// and async twin families in agreement, and when it fires it is the stack-resource verdict —
/// never the deterministic depth or step verdict. A source-level mirror pin keeps all four
/// funnel sites (two synchronous, two twins) in lock-step.
/// </summary>
public class StructuralNestingStackBackstopTests
{
    /// <summary>
    /// Widths that are shallow for BOTH families on an ordinary test-host thread. The
    /// alternating list/group shape accumulates the most frames per level, and the twin
    /// family's async frames are larger than the synchronous ones, so it stays narrow.
    /// </summary>
    private static int[] ShallowWidths(string kind)
        => kind == "list-alternation" ? [1, 2, 3] : [1, 5, 15];

    public static TheoryData<string, int> ShallowShapes()
    {
        var data = new TheoryData<string, int>();
        foreach (var kind in StructuralNestingStackBackstopProcessTests.Kinds)
        {
            foreach (var width in ShallowWidths(kind))
                data.Add(kind, width);
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(ShallowShapes))]
    public async Task ShallowNesting_CompletesIdenticallyOnBothFamilies(string kind, int width)
    {
        const int depth = 6;
        var ast = AsyncEvaluationHarness.Ast(StructuralNestingStackBackstopProcessTests.Program(kind, width, depth));
        var expected = StructuralNestingStackBackstopProcessTests.ExpectedAtoms(kind, width, depth);

        var syncDefault = Evaluator.RunCounted(ast);
        var (syncGeneric, syncBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (twin, twinBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));

        Assert.True(syncDefault.IsOk, syncDefault.IsError ? syncDefault.Error.ToString() : null);
        Assert.True(syncDefault.Value.Value.TryToHostAtoms(int.MaxValue, out var atoms));
        Assert.Equal(expected, atoms);

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncDefault), AsyncEvaluationHarness.NeutralOf(syncGeneric));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncDefault), AsyncEvaluationHarness.NeutralOf(twin));
        Assert.True(Result.ValueComparer.Equals(syncDefault.Value.Value, twin.Value.Value));

        // The probe executes once per nesting level on both families and moves no counter.
        Assert.Equal(syncBudget.ConsumedSteps, twinBudget.ConsumedSteps);
        Assert.Equal(syncBudget.PeakDepth, twinBudget.PeakDepth);
        Assert.Equal(syncBudget.MaterializedItems, twinBudget.MaterializedItems);
        Assert.Equal(syncBudget.MaterializedStringChars, twinBudget.MaterializedStringChars);
    }

    [Theory]
    [InlineData("brace")]
    [InlineData("capture")]
    [InlineData("list-group")]
    public void NestingWidth_ChargesNoStepsAndNoDepth(string kind)
    {
        // Structural nesting is written syntax: it charges neither a step nor a dynamic
        // depth level, and the backstop probe that now runs once per nesting level must
        // keep it that way. Every shallow width therefore charges identical steps (one per
        // invocation) and reaches the identical peak depth (the recursion itself).
        const int depth = 6;
        var observed = ShallowWidths(kind)
            .Select(width => Evaluator.RunCountedObserved(
                AsyncEvaluationHarness.Ast(StructuralNestingStackBackstopProcessTests.Program(kind, width, depth))))
            .ToList();

        Assert.All(observed, run => Assert.True(run.Result.IsOk, run.Result.IsError ? run.Result.Error.ToString() : null));
        Assert.Single(observed.Select(static run => run.Budget.ConsumedSteps).Distinct());
        Assert.Single(observed.Select(static run => run.Budget.PeakDepth).Distinct());
        Assert.Equal(depth + 1, observed[0].Budget.PeakDepth);
    }

    [Fact]
    public void AuditMinimalRepro_OnAnOrdinaryThread_IsStructuredOrCompletes_NeverDepthOrSteps()
    {
        // Whatever stack the test host gives this thread, the audit reproduction either
        // completes (value 0) or stops with the STACK backstop; the deterministic depth
        // limit (128, recursion depth is 9) and a generous step budget are never the
        // reported verdict, on either family.
        var ast = AsyncEvaluationHarness.Ast(StructuralNestingStackBackstopProcessTests.AuditMinimalRepro);

        foreach (var outcome in new[]
        {
            Evaluator.RunCounted(ast),
            Evaluator.RunCounted(ast, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(), new EvaluationLimits { MaxSteps = 1_000_000 }),
            RunTwin(ast),
        })
        {
            if (outcome.IsOk)
            {
                Assert.True(outcome.Value.Value.TryToHostAtoms(int.MaxValue, out var atoms));
                Assert.Equal([0m], atoms);
                continue;
            }

            Assert.Equal("evaluationStackExhausted", SemanticExplorerHarness.ErrorCategory(outcome.Error));
            Assert.True(outcome.Error.IsResourceLimit);
            Assert.NotNull(outcome.Error.Span);
        }
    }

    [Fact]
    public void AllFourRowLoopFunnels_OpenWithTheStackProbe()
    {
        // Mirror pin: the backstop is meaningful only while BOTH synchronous funnels and
        // BOTH async twins carry it as their first statement. Removing it from any one site
        // re-opens K2-R1 on that family without changing any ordinary test result.
        var sourceRoot = Path.Combine(FindRepoRoot(), "src", "KatLang");
        foreach (var (file, method) in new[]
        {
            ("Evaluator.PatternMatching.cs", "EvalOutputRowsPreparedCore"),
            ("Evaluator.ParameterBinding.cs", "EvalExplicitSequenceValueRowSlots"),
            ("Evaluator.Async.cs", "EvalOutputRowsPreparedCoreAsync"),
            ("Evaluator.Async.cs", "EvalExplicitSequenceValueRowSlotsAsync"),
        })
        {
            var text = File.ReadAllText(Path.Combine(sourceRoot, file));
            var match = Regex.Match(
                text,
                @"\s" + Regex.Escape(method) + @"\((?:[^{}]|\r|\n)*?\)\s*\{\s*(?<first>[^\r\n]*)",
                RegexOptions.Singleline);
            Assert.True(match.Success, $"{file}: definition of {method} not found");
            Assert.Equal(
                "if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())",
                match.Groups["first"].Value.Trim());
        }
    }

    private static EvalResult<Evaluator.CountedResult> RunTwin(Expr ast)
    {
        var pending = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache());
        Assert.True(pending.IsCompleted);
        return pending.GetAwaiter().GetResult();
    }

    private static string FindRepoRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "KatLang.slnx")))
            directory = directory.Parent;

        Assert.True(directory is not null, "Could not locate the repository root (KatLang.slnx).");
        return directory!.FullName;
    }
}
