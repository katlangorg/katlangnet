using System.Numerics;
using KatLang.Evaluation;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// SHARED-DAG GUARANTEE for signature validity and clause-head checks
/// (docs/design/language-rules/evaluator-and-hosting.md § Shared-DAG guarantee): a host-built
/// pattern that holds the same sub-pattern twice per level is validated with work linear in its
/// distinct nodes, and with exactly the verdict, rule order and first witness of the equivalent
/// tree. The per-occurrence APIs (<see cref="ParameterPattern.FlattenCaptures"/>,
/// <see cref="Algorithm.User.Parameters"/>, …) keep their contracts and serve as the tree oracle.
/// </summary>
public class SharedPatternDagValidationTests(ITestOutputHelper output)
{
    private const int DiamondLevels = 45;
    private const int BudgetLimit = 1_000_000;

    // Reads per distinct item edge (two per diamond level) the validation may spend.
    private const int ReadsPerEdge = 16;
    private const int RunReadsPerEdge = 16;

    public static TheoryData<string, string> KindsAndBottoms()
    {
        var data = new TheoryData<string, string>();
        foreach (var kind in new[] { "sequence", "list", "unpack" })
        foreach (var bottom in new[] { "plain", "singleton", "collectors", "repeated" })
            data.Add(kind, bottom);
        return data;
    }

    // ── 1. The predicates on a 45/90-level diamond ──────────────────────────

    [Theory]
    [MemberData(nameof(KindsAndBottoms))]
    public void SignatureValidity_OnASharedDiamond_IsTheTreeVerdict_AndLinear(string kind, string bottom)
    {
        var expected = ParameterPattern.FindSignatureViolation([ParameterTree(kind, bottom, 4)]);
        Assert.Equal(ExpectedViolation(bottom), expected);

        var reads45 = MeasureSignatureValidation(kind, bottom, DiamondLevels, expected);
        var reads90 = MeasureSignatureValidation(kind, bottom, 2 * DiamondLevels, expected);
        output.WriteLine($"{kind}/{bottom}: reads at 45 levels = {reads45}, at 90 levels = {reads90}");

        Assert.InRange(reads45, 1, ReadsPerEdge * 2 * DiamondLevels);
        // Linear: twice the levels cost at most twice the reads, up to one level's constant.
        Assert.InRange(reads90, 1, 2 * reads45 + 2 * ReadsPerEdge);
    }

    private static int MeasureSignatureValidation(string kind, string bottom, int levels, ParameterSignatureViolation? expected)
    {
        var budget = new PatternReadBudget(BudgetLimit);
        ParameterPattern[] patterns = [ParameterDiamond(kind, bottom, levels, budget)];
        Assert.Equal(expected, ParameterPattern.FindSignatureViolation(patterns));
        Assert.Equal(bottom == "singleton", ParameterPattern.FindSingletonSequenceGroup(patterns) is not null);
        Assert.Equal(bottom == "collectors", ParameterPattern.HasMultipleCollectingCapturesAtAnyLevel(patterns));
        // (*a, *b) also repeats a collecting name across paths; rule 2 is reported first.
        Assert.Equal(bottom is "repeated" or "collectors", ParameterPattern.HasRepeatedCaptureNameIncludingCollecting(patterns));
        // Every bottom repeats its names along the 2^levels paths.
        Assert.True(ParameterPattern.HasRepeatedCaptureNames(patterns));
        Assert.Equal(bottom switch { "collectors" => "a", "repeated" => "xs", _ => "x" },
            ParameterPattern.FindFirstCapture(patterns, requireSpan: false)?.Name);
        Assert.Null(ParameterPattern.FindFirstCapture(patterns, requireSpan: true));
        return budget.Reads;
    }

    // ── 2. Differential: random small DAGs against their cloned trees ───────

    [Fact]
    public void RandomSmallDags_AgreeWithTheirClonedTrees()
    {
        var random = new Random(20261109);
        var verdicts = new Dictionary<string, int>(StringComparer.Ordinal);
        var sharedCases = 0;
        for (var round = 0; round < 1000; round++)
        {
            var (dag, sharesNodes) = RandomDag(random);
            if (sharesNodes)
                sharedCases++;
            var origin = new Dictionary<ParameterPattern, ParameterPattern>(ReferenceEqualityComparer.Instance);
            var tree = dag.Select(pattern => CloneTree(pattern, origin)).ToArray();
            var context = $"round {round}: {string.Join(", ", dag.Select(static p => p.DisplayName))}";

            var expectedViolation = OracleViolation(tree);
            Assert.True(expectedViolation == ParameterPattern.FindSignatureViolation(dag), context);
            Assert.True(expectedViolation == ParameterPattern.FindSignatureViolation(tree), context);
            verdicts[expectedViolation?.ToString() ?? "valid"] = verdicts.GetValueOrDefault(expectedViolation?.ToString() ?? "valid") + 1;

            var treeSingleton = OracleSingleton(tree);
            var dagSingleton = ParameterPattern.FindSingletonSequenceGroup(dag);
            Assert.True(treeSingleton is null ? dagSingleton is null : ReferenceEquals(origin[treeSingleton], dagSingleton), context);

            Assert.True(OracleMultipleCollecting(tree) == ParameterPattern.HasMultipleCollectingCapturesAtAnyLevel(dag), context);

            var treeCaptures = ParameterPattern.FlattenCaptures(tree);
            var repeated = treeCaptures.GroupBy(static c => c.Name, StringComparer.Ordinal).Any(static g => g.Count() > 1);
            Assert.True(repeated == ParameterPattern.HasRepeatedCaptureNames(dag), context);
            Assert.True(repeated == ParameterPattern.HasRepeatedCaptureNames(dag.Select(static p => p)), context);
            var repeatedCollecting = treeCaptures.GroupBy(static c => c.Name, StringComparer.Ordinal)
                .Any(static g => g.Count() > 1 && g.Any(static c => c.Kind == ParameterKind.Collecting));
            Assert.True(repeatedCollecting == ParameterPattern.HasRepeatedCaptureNameIncludingCollecting(dag), context);
            Assert.True(repeatedCollecting == ParameterPattern.HasRepeatedCaptureNameIncludingCollecting(dag.Select(static p => p)), context);

            Assert.Same(treeCaptures.FirstOrDefault(), ParameterPattern.FindFirstCapture(dag, requireSpan: false));
            Assert.Same(treeCaptures.FirstOrDefault(static c => c.Span is not null), ParameterPattern.FindFirstCapture(dag, requireSpan: true));

            var head = RandomClauseHead(random);
            var headOrigin = new Dictionary<Pattern, Pattern>(ReferenceEqualityComparer.Instance);
            var headTree = CloneHead(head, headOrigin);
            var treeHeadSingleton = OracleHeadSingleton(headTree);
            var dagHeadSingleton = head.FindHeadSingletonSequenceGroup();
            Assert.True(treeHeadSingleton is null ? dagHeadSingleton is null : ReferenceEquals(headOrigin[treeHeadSingleton], dagHeadSingleton), $"head round {round}");
        }

        output.WriteLine($"1000 cases, {sharedCases} with shared nodes: {string.Join(", ", verdicts.Select(static v => $"{v.Key}={v.Value}"))}");
        Assert.True(sharedCases > 500);
        Assert.Equal(4, verdicts.Count);
        Assert.All(verdicts.Values, count => Assert.True(count >= 20));
    }

    // ── 3. The public route ─────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(KindsAndBottoms))]
    public async Task PublicRunRoutes_OnASharedSignature_GiveTheTreeOutcome_WithBoundedReads(string kind, string bottom)
    {
        var expected = Outcome(Evaluator.Run(HostileRoot(ParameterTree(kind, bottom, 4))));
        Assert.Equal(ExpectedOutcome(bottom), expected);

        var reads = new List<int>();
        foreach (var route in new[] { "Run", "RunAsync", "RunFlat", "RunFlatAsync" })
        {
            var budget = new PatternReadBudget(BudgetLimit);
            var root = HostileRoot(ParameterDiamond(kind, bottom, DiamondLevels, budget));
            var actual = route switch
            {
                "Run" => Outcome(Evaluator.Run(root)),
                "RunAsync" => Outcome(await Evaluator.RunAsync(root)),
                "RunFlat" => FlatOutcome(Evaluator.RunFlat(root)),
                _ => FlatOutcome(await Evaluator.RunFlatAsync(root)),
            };
            Assert.Equal(expected, actual);
            reads.Add(budget.Reads);
            Assert.InRange(budget.Reads, 1, RunReadsPerEdge * 2 * DiamondLevels);
        }

        output.WriteLine($"{kind}/{bottom}: reads per route = {string.Join(", ", reads)}");
    }

    // ── 4. Clause heads ─────────────────────────────────────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ClauseHead_OnASharedDiamond_IsTheTreeVerdict_WithBoundedReads(bool singletonAtTheBottom)
    {
        var expected = Outcome(Evaluator.Run(ClauseRoot(HeadTree(singletonAtTheBottom, 4))));
        Assert.Equal(singletonAtTheBottom ? $"illegal {Parser.SingletonSequencePatternDiagnostic}" : "ok 7", expected);

        foreach (var route in new[] { "Run", "RunAsync", "RunFlat", "RunFlatAsync" })
        {
            var budget = new PatternReadBudget(BudgetLimit);
            var root = ClauseRoot(HeadDiamond(singletonAtTheBottom, DiamondLevels, budget));
            var actual = route switch
            {
                "Run" => Outcome(Evaluator.Run(root)),
                "RunAsync" => Outcome(await Evaluator.RunAsync(root)),
                "RunFlat" => FlatOutcome(Evaluator.RunFlat(root)),
                _ => FlatOutcome(await Evaluator.RunFlatAsync(root)),
            };
            Assert.Equal(expected, actual);
            output.WriteLine($"singleton={singletonAtTheBottom} {route}: reads = {budget.Reads}");
            Assert.InRange(budget.Reads, 1, RunReadsPerEdge * 2 * DiamondLevels);
        }

        var predicateBudget = new PatternReadBudget(BudgetLimit);
        var head = new Pattern.SequenceValue([HeadDiamond(singletonAtTheBottom, 2 * DiamondLevels, predicateBudget)]);
        Assert.Equal(singletonAtTheBottom, head.HeadHasSingletonSequenceGroup());
        Assert.InRange(predicateBudget.Reads, 1, ReadsPerEdge * 2 * 2 * DiamondLevels);
    }

    // ── 5. The explicit-parameter anchor ────────────────────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ExplicitParameterAnchor_OnASharedDiamond_IsTheTreeSpan_WithBoundedReads(bool spannedBottom)
    {
        var span = spannedBottom ? new SourceSpan(3, 5, 3, 6) : (SourceSpan?)null;
        var treeError = Assert.IsType<EvalError.ExplicitParametersRequireOutput>(
            Evaluator.Run(OutputlessRoot(SpannedTree(span, 4))).Error);
        Assert.Equal(span, treeError.Span);

        var budget = new PatternReadBudget(BudgetLimit);
        var error = Assert.IsType<EvalError.ExplicitParametersRequireOutput>(
            Evaluator.Run(OutputlessRoot(SpannedDiamond(span, DiamondLevels, budget))).Error);
        Assert.Equal(treeError.Span, error.Span);
        output.WriteLine($"spanned={spannedBottom}: reads = {budget.Reads}");
        Assert.InRange(budget.Reads, 1, RunReadsPerEdge * 2 * DiamondLevels);
    }

    // ── Shapes ──────────────────────────────────────────────────────────────

    private static ParameterSignatureViolation? ExpectedViolation(string bottom) => bottom switch
    {
        "singleton" => ParameterSignatureViolation.SingletonSequencePattern,
        "collectors" => ParameterSignatureViolation.MultipleCollectingAtOneLevel,
        "repeated" => ParameterSignatureViolation.RepeatedNameIncludesCollecting,
        _ => null,
    };

    private static string ExpectedOutcome(string bottom) => bottom switch
    {
        "singleton" => $"illegal {Parser.SingletonSequencePatternDiagnostic}",
        "collectors" => $"illegal {Parser.MultipleCollectingBindingsPerLevelDiagnostic}",
        "repeated" => $"illegal {Parser.RepeatedNameIncludesCollectingDiagnostic}",
        _ => "ok 7",
    };

    // A fresh bottom: x; (x); (*a, *b); (*xs, y).
    private static ParameterPattern Bottom(string bottom) => bottom switch
    {
        "singleton" => new SequenceValueParameterPattern([new CaptureParameterPattern("x")]),
        "collectors" => new SequenceValueParameterPattern([
            new CaptureParameterPattern("a", Kind: ParameterKind.Collecting),
            new CaptureParameterPattern("b", Kind: ParameterKind.Collecting)]),
        "repeated" => new SequenceValueParameterPattern([
            new CaptureParameterPattern("xs", Kind: ParameterKind.Collecting),
            new CaptureParameterPattern("y")]),
        _ => new CaptureParameterPattern("x"),
    };

    private static ParameterPattern Structural(string kind, IReadOnlyList<ParameterPattern> items) => kind switch
    {
        "sequence" => new SequenceValueParameterPattern(items),
        "list" => new ListValueParameterPattern(items),
        _ => new UnpackingParameterPattern(items),
    };

    // Shares one sub-pattern twice per level: levels + 1 distinct nodes, 2^levels bottom occurrences.
    private static ParameterPattern ParameterDiamond(string kind, string bottom, int levels, PatternReadBudget budget)
    {
        var pattern = Bottom(bottom);
        for (var level = 0; level < levels; level++)
            pattern = Structural(kind, new BudgetedPatternItems<ParameterPattern>(pattern, pattern, budget));
        return pattern;
    }

    // The same shape with a fresh node per occurrence.
    private static ParameterPattern ParameterTree(string kind, string bottom, int levels)
        => levels == 0 ? Bottom(bottom) : Structural(kind, [ParameterTree(kind, bottom, levels - 1), ParameterTree(kind, bottom, levels - 1)]);

    private static ParameterPattern SpannedDiamond(SourceSpan? span, int levels, PatternReadBudget budget)
    {
        ParameterPattern pattern = new CaptureParameterPattern("x", span);
        for (var level = 0; level < levels; level++)
            pattern = new SequenceValueParameterPattern(new BudgetedPatternItems<ParameterPattern>(pattern, pattern, budget));
        return pattern;
    }

    private static ParameterPattern SpannedTree(SourceSpan? span, int levels)
        => levels == 0
            ? new CaptureParameterPattern("x", span)
            : new SequenceValueParameterPattern([SpannedTree(span, levels - 1), SpannedTree(span, levels - 1)]);

    private static Pattern HeadBottom(bool singleton)
        => singleton ? new Pattern.SequenceValue([new Pattern.Bind("x")]) : new Pattern.Bind("x");

    private static Pattern HeadDiamond(bool singleton, int levels, PatternReadBudget budget)
    {
        var pattern = HeadBottom(singleton);
        for (var level = 0; level < levels; level++)
            pattern = new Pattern.SequenceValue(new BudgetedPatternItems<Pattern>(pattern, pattern, budget));
        return pattern;
    }

    private static Pattern HeadTree(bool singleton, int levels)
        => levels == 0 ? HeadBottom(singleton) : new Pattern.SequenceValue([HeadTree(singleton, levels - 1), HeadTree(singleton, levels - 1)]);

    private static Expr HostileRoot(ParameterPattern shared)
    {
        var callee = new Algorithm.User(null, [shared], [], [], [new Expr.Num(1)]);
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", callee)], [new Expr.Num(7)]));
    }

    private static Expr ClauseRoot(Pattern nested)
    {
        var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var family = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.SequenceValue([nested]), body)]);
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", family)], [new Expr.Num(7)]));
    }

    private static Expr OutputlessRoot(ParameterPattern shared)
    {
        var callee = new Algorithm.User(null, [shared], [], [], []) { HasExplicitParameterList = true };
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", callee)], [new Expr.Num(7)]));
    }

    private static string Outcome(EvalResult<Result> result)
        => result.IsError
            ? result.Error is EvalError.IllegalInEval illegal ? $"illegal {illegal.Reason}" : $"error {result.Error}"
            : result.Value is Result.Atom atom ? $"ok {atom.Value}" : $"ok {result.Value}";

    private static string FlatOutcome(EvalResult<IReadOnlyList<Decimal128>> result)
        => result.IsError
            ? result.Error is EvalError.IllegalInEval illegal ? $"illegal {illegal.Reason}" : $"error {result.Error}"
            : $"ok {string.Join(" ", result.Value)}";

    // ── Random DAGs and the tree oracle ─────────────────────────────────────

    private static readonly string[] Names = ["a", "b", "c"];
    private static readonly string[] Kinds = ["sequence", "list", "unpack"];

    private static (ParameterPattern[] Patterns, bool SharesNodes) RandomDag(Random random)
    {
        var pool = new List<(ParameterPattern Node, int Height)>();
        var leaves = random.Next(1, 4);
        for (var index = 0; index < leaves; index++)
        {
            var span = random.Next(2) == 0 ? new SourceSpan(index + 1, 1, index + 1, 2) : (SourceSpan?)null;
            var kind = random.Next(4) == 0 ? ParameterKind.Collecting : ParameterKind.Normal;
            pool.Add((new CaptureParameterPattern(Names[random.Next(Names.Length)], span, kind), 0));
        }

        var uses = new Dictionary<ParameterPattern, int>(ReferenceEqualityComparer.Instance);
        var structural = random.Next(1, 7);
        for (var index = 0; index < structural; index++)
        {
            var items = new List<ParameterPattern>();
            var height = 0;
            var count = random.Next(0, 4);
            for (var item = 0; item < count; item++)
            {
                var candidates = pool.Where(static entry => entry.Height < 6).ToList();
                // Prefer recent nodes so the DAG grows deep as well as wide.
                var pick = candidates[Math.Max(0, candidates.Count - 1 - random.Next(Math.Min(3, candidates.Count)) - (random.Next(3) == 0 ? random.Next(candidates.Count) : 0))];
                items.Add(pick.Node);
                uses[pick.Node] = uses.GetValueOrDefault(pick.Node) + 1;
                height = Math.Max(height, pick.Height + 1);
            }

            pool.Add((Structural(Kinds[random.Next(Kinds.Length)], items), Math.Max(1, height)));
        }

        var top = new ParameterPattern[random.Next(1, 4)];
        for (var index = 0; index < top.Length; index++)
        {
            var pick = pool[Math.Max(0, pool.Count - 1 - random.Next(Math.Min(3, pool.Count)))].Node;
            top[index] = pick;
            uses[pick] = uses.GetValueOrDefault(pick) + 1;
        }

        return (top, uses.Values.Any(static count => count > 1));
    }

    private static ParameterPattern CloneTree(ParameterPattern pattern, Dictionary<ParameterPattern, ParameterPattern> origin)
    {
        ParameterPattern clone = ParameterPattern.StructuralItems(pattern) is { } items
            ? ParameterPattern.WithStructuralItems(pattern, items.Select(item => CloneTree(item, origin)).ToArray())
            : new CaptureParameterPattern(((CaptureParameterPattern)pattern).Parameter);
        origin[clone] = pattern;
        return clone;
    }

    private static ParameterSignatureViolation? OracleViolation(IReadOnlyList<ParameterPattern> tree)
    {
        if (OracleSingleton(tree) is not null)
            return ParameterSignatureViolation.SingletonSequencePattern;
        if (OracleMultipleCollecting(tree))
            return ParameterSignatureViolation.MultipleCollectingAtOneLevel;
        return ParameterPattern.FlattenCaptures(tree).GroupBy(static c => c.Name, StringComparer.Ordinal)
            .Any(static g => g.Count() > 1 && g.Any(static c => c.Kind == ParameterKind.Collecting))
            ? ParameterSignatureViolation.RepeatedNameIncludesCollecting
            : null;
    }

    private static ParameterPattern? OracleSingleton(IReadOnlyList<ParameterPattern> tree)
    {
        foreach (var pattern in tree)
        {
            if (pattern is SequenceValueParameterPattern sequence && ParameterPattern.IsSingletonSequenceItems(sequence.Items))
                return pattern;
            if (ParameterPattern.StructuralItems(pattern) is { } items && OracleSingleton(items) is { } nested)
                return nested;
        }

        return null;
    }

    private static bool OracleMultipleCollecting(IReadOnlyList<ParameterPattern> tree)
        => tree.Count(static p => p is CaptureParameterPattern { Kind: ParameterKind.Collecting }) > 1
            || tree.Any(static p => ParameterPattern.StructuralItems(p) is { } items && OracleMultipleCollecting(items));

    private static Pattern RandomClauseHead(Random random)
    {
        var pool = new List<(Pattern Node, int Height)> { (new Pattern.Bind("x"), 0), (new Pattern.LitInt(1), 0) };
        var structural = random.Next(1, 7);
        for (var index = 0; index < structural; index++)
        {
            var items = new List<Pattern>();
            var height = 0;
            var count = random.Next(0, 4);
            for (var item = 0; item < count; item++)
            {
                var candidates = pool.Where(static entry => entry.Height < 6).ToList();
                var pick = candidates[Math.Max(0, candidates.Count - 1 - random.Next(Math.Min(3, candidates.Count)))];
                items.Add(pick.Node);
                height = Math.Max(height, pick.Height + 1);
            }

            pool.Add((random.Next(3) == 0 ? new Pattern.ListValue(items) : new Pattern.SequenceValue(items), Math.Max(1, height)));
        }

        return new Pattern.SequenceValue([pool[^1].Node, pool[random.Next(pool.Count)].Node]);
    }

    private static Pattern CloneHead(Pattern pattern, Dictionary<Pattern, Pattern> origin)
    {
        Pattern clone = pattern switch
        {
            Pattern.SequenceValue sequence => new Pattern.SequenceValue(sequence.Items.Select(item => CloneHead(item, origin)).ToArray()),
            Pattern.ListValue list => new Pattern.ListValue(list.Items.Select(item => CloneHead(item, origin)).ToArray()),
            Pattern.Bind bind => new Pattern.Bind(bind.Name),
            _ => pattern with { },
        };
        origin[clone] = pattern;
        return clone;
    }

    // The head's own top-level sequence is its argument list and is not itself checked.
    private static Pattern? OracleHeadSingleton(Pattern head)
        => head is Pattern.SequenceValue(var items) ? OracleNestedSingleton(items) : OracleNestedSingleton([head]);

    private static Pattern? OracleNestedSingleton(IReadOnlyList<Pattern> items)
    {
        foreach (var item in items)
        {
            switch (item)
            {
                case Pattern.SequenceValue sequence when Pattern.IsSingletonSequenceItems(sequence.Items):
                    return sequence;
                case Pattern.SequenceValue(var nested) when OracleNestedSingleton(nested) is { } found:
                    return found;
                case Pattern.ListValue(var nested) when OracleNestedSingleton(nested) is { } found:
                    return found;
            }
        }

        return null;
    }
}
