using KatLang.Tests.InvocationRoute;
using KatLang.Tests.LanguageSpec;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// 2026-11 call-binding allocation follow-up, part B: a synchronous run walks its program three
/// times before evaluation — the entry guard for deferred module regions
/// (<c>DeferredModuleRegion.RequiresAsyncEvaluation</c>), the structural preflight
/// (<c>AstStructuralPreflight.CheckAdmittedProgram</c>) and the pre-evaluation validation walk
/// (<c>AlgorithmValidation.FindFirstPreEvaluationViolation</c>) — and each builds reference-identity
/// tables over the whole graph. Each later pass now sizes its tables from the node count an earlier
/// pass of the same run produced, instead of growing them by doubling. The count is CAPACITY ONLY:
/// every pass still makes its own complete walk, in the same order, and reaches the same verdict
/// with the same position whatever count it is handed. Implementation-only.
/// </summary>
public class PreEvaluationTableSizingTests(ITestOutputHelper output)
{
    private const AstConsumerProfile Profile = AstConsumerProfile.EvaluatorIterativeJoinSpines;

    private static readonly int Limit = EvaluationLimits.Default.EffectiveMaxAstDepth;

    private static HostOperations CorpusOperations() => HostOperations.Create(
        HostOperation.Create("trace", static (args, _) => args[0], "x"),
        HostOperation.Create("boom", static (_, _) => new Result.Atom(0)),
        HostOperation.Create("aflag", static (_, _) => new Result.Bool(true)),
        HostOperation.Create("stop", static (_, _) => new Result.Bool(true)));

    private static List<(string Label, Expr Program)> CorpusPrograms()
    {
        var options = new RunOptions { HostOperations = CorpusOperations() };
        return InvocationRouteCorpus.Cases
            .Where(static c => c.Module is null)
            .Select(c => (Label: "route " + c.Id, Parsed: Parser.Parse(InvocationRouteCorpus.Core + (c.Plain ? InvocationRouteCorpus.Plain : InvocationRouteCorpus.Meta) + c.Source, options)))
            .Concat(LanguageSpecCorpus.AllCases().Select(static c => (Label: "spec " + c.Id, Parsed: Parser.Parse(c.Source))))
            .Where(static program => !program.Parsed.HasErrors)
            .Select(static program => (program.Label, (Expr)new Expr.AlgorithmExpr(program.Parsed.Root)))
            .ToList();
    }

    // ── Host-built graphs the corpora cannot contain ────────────────────────────────────────────────

    private static Expr Shared()
    {
        // One literal reached through two edges: a DAG, not a tree.
        var shared = new Expr.Num(1);
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [new Expr.Binary(BinaryOp.Add, shared, shared)]));
    }

    private static Expr TooDeep()
    {
        Expr spine = new Expr.Num(1);
        for (var i = 0; i < EvaluationLimits.MaxSupportedAstDepth + 50; i++)
            spine = new Expr.Unary(UnaryOp.Minus, spine);
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [spine]));
    }

    private static Expr Cyclic()
    {
        // A caller-owned property list that holds its own algorithm.
        var properties = new List<Property>();
        var algorithm = new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]);
        properties.Add(new Property("Self", algorithm));
        return new Expr.AlgorithmExpr(algorithm);
    }

    // A written parameter list without output; the parameter is written on its own line.
    private static Algorithm.User WithoutOutput(string parameter, int line)
        => new(null, [new CaptureParameterPattern(parameter, new SourceSpan(line, 1, line, 2))], [], [], [])
        {
            HasExplicitParameterList = true,
        };

    // Two explicit-parameter violations in declaration order (the first must be reported), under padding.
    private static Expr TwoViolations(int padding)
    {
        var properties = Enumerable.Range(0, padding)
            .Select(static i => new Property("Pad" + i, new Algorithm.User(null, [], [], [], [new Expr.Num(i)])))
            .Append(new Property("First", WithoutOutput("a", 1)))
            .Append(new Property("Second", WithoutOutput("b", 2)))
            .ToList();
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]));
    }

    private static Expr SingletonSequencePattern()
    {
        var callee = new Algorithm.User(
            null, [new SequenceValueParameterPattern([new CaptureParameterPattern("only")])], [], [], [new Expr.Num(1)]);
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", callee)], [new Expr.Num(1)]));
    }

    // ── The counts ──────────────────────────────────────────────────────────────────────────────────

    [Fact]
    public void TheEntryGuardAndThePreflight_CountTheSameNodes_OnEveryCorpusProgram()
    {
        // The guard's count sizes the preflight's table, and the preflight's count the validation
        // walk's: on a region-free program both walks meet exactly the same distinct nodes.
        var programs = CorpusPrograms();
        long nodes = 0;
        var trees = 0;
        foreach (var (label, program) in programs)
        {
            Assert.False(DeferredModuleRegion.RequiresAsyncEvaluationCounting(program, out var guardCount), label);
            Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
            Assert.True(facts.NodeCount > 0, label);
            Assert.Equal(guardCount, facts.NodeCount);
            // TreeNodeCount is the same count when no node is shared, and 0 otherwise.
            Assert.True(facts.TreeNodeCount == 0 || facts.TreeNodeCount == facts.NodeCount, label);
            if (facts.TreeNodeCount != 0) trees++;
            nodes += facts.NodeCount;
        }

        output.WriteLine($"programs={programs.Count} trees={trees} nodes={nodes}");
        Assert.True(programs.Count >= 300, programs.Count.ToString(System.Globalization.CultureInfo.InvariantCulture));
        Assert.True(trees > 0 && trees < programs.Count, $"trees={trees} of {programs.Count}");
    }

    [Fact]
    public void NodeCount_CountsASharedNodeOnce_WhereTheTreeCountIsZero()
    {
        var shared = Shared();
        Assert.False(DeferredModuleRegion.RequiresAsyncEvaluationCounting(shared, out var guardCount));
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(shared, Limit, Profile, out var facts));
        Assert.Equal(0, facts.TreeNodeCount);
        Assert.Equal(guardCount, facts.NodeCount);

        // The same program with two separate literals has exactly one node more.
        var separate = new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [], [new Expr.Binary(BinaryOp.Add, new Expr.Num(1), new Expr.Num(1))]));
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(separate, Limit, Profile, out var separateFacts));
        Assert.Equal(separateFacts.NodeCount, separateFacts.TreeNodeCount);
        Assert.Equal(facts.NodeCount + 1, separateFacts.NodeCount);
    }

    // ── The count is capacity only ──────────────────────────────────────────────────────────────────

    private static int[] Hints(int exact) => [0, 1, exact / 2, exact, exact + 1, exact * 4 + 64];

    [Fact]
    public void ThePreflight_ReachesTheSameVerdictAndFacts_WhateverCountItIsHanded()
    {
        var subjects = CorpusPrograms().Where(static (_, index) => index % 7 == 0)
            .Append(("shared", Shared()))
            .Append(("too deep", TooDeep()))
            .Append(("cyclic", Cyclic()))
            .Append(("two violations", TwoViolations(40)))
            .ToList();
        var rejected = 0;
        foreach (var (label, program) in subjects)
        {
            var expected = AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var expectedFacts);
            if (expected is not null) rejected++;
            _ = DeferredModuleRegion.RequiresAsyncEvaluationCounting(program, out var exact);
            foreach (var hint in Hints(exact))
            {
                var actual = AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts, hint);
                Assert.True(expected == actual, $"{label}: hint {hint}: {actual} instead of {expected}");
                Assert.True(expectedFacts == facts, $"{label}: hint {hint}: {facts} instead of {expectedFacts}");
            }
        }

        // The depth and cycle rejections were among the subjects, with their kinds.
        Assert.Equal(2, rejected);
        Assert.Equal(AstStructuralViolation.DepthExceeded, AstStructuralPreflight.CheckAdmittedProgram(TooDeep(), Limit, Profile, out _, 1_000_000)!.Kind);
        Assert.Equal(AstStructuralViolation.CycleDetected, AstStructuralPreflight.CheckAdmittedProgram(Cyclic(), Limit, Profile, out _, 1_000_000)!.Kind);
    }

    [Fact]
    public void TheValidationWalk_ReportsTheSameFirstViolation_WhateverCountItIsHanded()
    {
        var subjects = CorpusPrograms().Where(static (_, index) => index % 7 == 0)
            .Append(("shared", Shared()))
            .Append(("two violations", TwoViolations(0)))
            .Append(("two violations, padded", TwoViolations(40)))
            .Append(("singleton sequence pattern", SingletonSequencePattern()))
            .ToList();
        var violations = 0;
        foreach (var (label, program) in subjects)
        {
            var expected = AlgorithmValidation.FindFirstPreEvaluationViolation(program);
            if (expected is not null) violations++;
            Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
            foreach (var hint in Hints(facts.NodeCount))
            {
                var actual = AlgorithmValidation.FindFirstPreEvaluationViolation(program, observations: null, hint);
                Assert.True(Equals(expected, actual), $"{label}: hint {hint}: {actual} instead of {expected}");
            }
        }

        Assert.Equal(3, violations);
        // The FIRST of two violations, by declaration order, at every count.
        var first = Assert.IsType<PreEvaluationAstViolation.ExplicitParametersWithoutOutput>(
            AlgorithmValidation.FindFirstPreEvaluationViolation(TwoViolations(40), observations: null, 4096));
        Assert.Equal(first, AlgorithmValidation.FindFirstPreEvaluationViolation(TwoViolations(40)));
        Assert.Equal(new SourceSpan(1, 1, 1, 2), first.Span);
        Assert.IsType<PreEvaluationAstViolation.SingletonSequencePattern>(
            AlgorithmValidation.FindFirstPreEvaluationViolation(SingletonSequencePattern(), observations: null, 4096));
    }

    [Fact]
    public void ARun_RefusesInTheSameOrder_AndWithTheSameError_AsItsPassesDoAlone()
    {
        // A run's refusal is still the structural preflight's when both a structural and a validation
        // defect are present, and the validation walk's first violation otherwise.
        static EvalError Refusal(Expr program)
        {
            var (result, _) = Evaluator.RunCountedObserved(program);
            Assert.True(result.IsError);
            return result.Error;
        }

        Assert.IsType<EvalError.AstDepthLimitExceeded>(Refusal(TooDeep()));
        Assert.IsType<EvalError.AstCycleDetected>(Refusal(Cyclic()));
        // The FIRST violation's own position (WithoutOutput's written parameter), padded or not.
        var padded = Assert.IsType<EvalError.ExplicitParametersRequireOutput>(Refusal(TwoViolations(40)));
        var plain = Assert.IsType<EvalError.ExplicitParametersRequireOutput>(Refusal(TwoViolations(0)));
        Assert.Equal(new SourceSpan(1, 1, 1, 2), padded.Span);
        Assert.Equal(padded.Span, plain.Span);

        // A too-deep spine that ALSO holds a validation defect: the structural refusal comes first.
        Expr spine = new Expr.Num(1);
        for (var i = 0; i < EvaluationLimits.MaxSupportedAstDepth + 50; i++)
            spine = new Expr.Unary(UnaryOp.Minus, spine);
        var both = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("First", WithoutOutput("a", 1))], [spine]));
        Assert.IsType<EvalError.AstDepthLimitExceeded>(Refusal(both));
    }

    // ── What the sizing saves (coarse, in-process) ──────────────────────────────────────────────────

    private static long MinimumBytes(Action action)
    {
        for (var i = 0; i < 3; i++)
            action();
        var minimum = long.MaxValue;
        for (var i = 0; i < 5; i++)
        {
            var before = GC.GetAllocatedBytesForCurrentThread();
            action();
            minimum = Math.Min(minimum, GC.GetAllocatedBytesForCurrentThread() - before);
        }
        return minimum;
    }

    [Fact]
    public void SizedTables_AllocateWellUnderTheDoublingOnes_OnAThousandNodeProgram()
    {
        // The benchmark's ParameterizedCall program (201 chained calls, about a thousand nodes). A table
        // grown by doubling allocates every intermediate size and overshoots the final one; a sized
        // table allocates its final size once. Measured on 2026-11-11 (x64, .NET 11), 1,011 nodes:
        // preflight 113,832 → 42,632 bytes, validation walk 190,712 → 68,536 (Debug test build). A coarse ratio.
        var source = "Inc(v) = v + 1\n" + string.Join(" + ", Enumerable.Repeat("Inc(0)", 201)) + "\n";
        Expr program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(program));
        var nodes = facts.NodeCount;
        Assert.InRange(nodes, 900, 1_200);

        var preflightGrown = MinimumBytes(() => _ = AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out _));
        var preflightSized = MinimumBytes(() => _ = AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out _, nodes));
        var walkGrown = MinimumBytes(() => _ = AlgorithmValidation.FindFirstPreEvaluationViolation(program, observations: null));
        var walkSized = MinimumBytes(() => _ = AlgorithmValidation.FindFirstPreEvaluationViolation(program, observations: null, nodes));
        output.WriteLine($"nodes={nodes} preflight {preflightGrown} -> {preflightSized}, validation walk {walkGrown} -> {walkSized}");
        Assert.True(preflightSized * 2 < preflightGrown, $"preflight {preflightGrown} -> {preflightSized}");
        Assert.True(walkSized * 2 < walkGrown, $"validation walk {walkGrown} -> {walkSized}");
    }
}
