using System.Reflection;
using KatLang.Tests.AsyncEvaluation;
using KatLang.Tests.InvocationRoute;
using KatLang.Tests.LanguageSpec;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// 2026-11 follow-up of the pre-evaluation table sizing (<see cref="PreEvaluationTableSizingTests"/>). A run's
/// pre-evaluation passes now hand their reference-identity table STORAGE on to each other through one
/// per-run token (<see cref="PreEvaluationTables"/>): the synchronous entry guard's node set becomes the
/// validation walk's visited set, and the structural preflight's height table its alias-reach table, each
/// CLEARED on take. The preflight also proves whether the graph holds an alias at all
/// (<see cref="AstStructuralPreflight.AdmittedProgramFacts.IsAliasFree"/>); an alias-free graph's validation
/// walk builds no alias-reach table. The async entries carry their deciding walk's node count in the tree
/// fact (<see cref="Evaluator.TreeRouteFact"/>), so their preflight is presized too. Implementation-only:
/// every pass, check, refusal, order and diagnostic is unchanged, which these tests pin.
/// </summary>
public class PreEvaluationTableHandOverTests(ITestOutputHelper output)
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

    // ── Host-built graphs ───────────────────────────────────────────────────────────────────────────

    // A written parameter list without output; the parameter is written on its own line.
    private static Algorithm.User WithoutOutput(string parameter, int line)
        => new(null, [new CaptureParameterPattern(parameter, new SourceSpan(line, 1, line, 2))], [], [], [])
        {
            HasExplicitParameterList = true,
        };

    // Two explicit-parameter violations in declaration order (the first must be reported), under padding:
    // the walk must reach the very last properties to find either.
    private static Expr TwoViolations(int padding)
    {
        var properties = Enumerable.Range(0, padding)
            .Select(static i => new Property("Pad" + i, new Algorithm.User(null, [], [], [], [new Expr.Num(i)])))
            .Append(new Property("First", WithoutOutput("a", 1)))
            .Append(new Property("Second", WithoutOutput("b", 2)))
            .ToList();
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]));
    }

    private const int AliasDepth = 120;

    /// <summary>
    /// <paramref name="members"/> held <see cref="AliasDepth"/> blocks deep: each level is a property holding
    /// the next level's algorithm, so the alias sits far below everything else in the graph.
    /// </summary>
    private static Expr DeeplyNested(IReadOnlyList<Property> members)
    {
        Algorithm level = new Algorithm.User(null, [], [], members, [new Expr.Num(0)]);
        for (var i = 0; i < AliasDepth; i++)
            level = new Algorithm.User(null, [], [], [new Property("L" + i, level), new Property("V" + i, Constant(i))], [new Expr.Num(i)]);
        return new Expr.AlgorithmExpr(level);
    }

    private static Algorithm.User Constant(int value) => new(null, [], [], [], [new Expr.Num(value)]);

    private static readonly SourceSpan TargetSpan = new(7, 3, 7, 4);

    // Where a two-alias cycle is reported: at the target of the alias that closes it (StaticAliasTargets.FindCycle).
    private static readonly SourceSpan ClosingTargetSpan = new(8, 3, 8, 4);

    // One alias whose written target is no static path.
    private static Expr DeepNotStaticAlias()
        => DeeplyNested([new("A", new Algorithm.Alias(null, [], [], new Expr.Num(1) { Span = TargetSpan }))]);

    // Two aliases naming each other.
    private static Expr DeepAliasCycle()
        => DeeplyNested(
        [
            new("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("B") { Span = TargetSpan })),
            new("B", new Algorithm.Alias(null, [], [], new Expr.Resolve("A") { Span = ClosingTargetSpan })),
        ]);

    // An alias cycle in a host-built parent scope of a deep block: the walk's parent-scope chain.
    private static Expr DeepParentScopeAliasCycle()
    {
        var scope = new ScopeCtx(null, [],
        [
            new("X", new Algorithm.Alias(null, [], [], new Expr.Resolve("Y") { Span = TargetSpan })),
            new("Y", new Algorithm.Alias(null, [], [], new Expr.Resolve("X"))),
        ]);
        return DeeplyNested([new("Held", new Algorithm.User(scope, [], [], [], [new Expr.Num(5)]))]);
    }

    // A legal alias deep inside (source-free): `K` names a sibling callable.
    private static Expr DeepLegalAlias()
        => DeeplyNested(
        [
            new("F", new Algorithm.User(null, Algorithm.NormalParameters(["x"]), [], [], [new Expr.Param("x")])),
            new("K", new Algorithm.Alias(null, [], [], new Expr.Resolve("F"))),
        ]);

    private static IEnumerable<(string Label, Expr Program)> HostBuiltSubjects()
    {
        yield return ("two violations", TwoViolations(0));
        yield return ("two violations, padded", TwoViolations(60));
        yield return ("deep alias, not a static path", DeepNotStaticAlias());
        yield return ("deep alias cycle", DeepAliasCycle());
        yield return ("deep parent-scope alias cycle", DeepParentScopeAliasCycle());
        yield return ("deep legal alias", DeepLegalAlias());
    }

    private static List<(string Label, Expr Program)> Subjects()
        => [.. CorpusPrograms().Where(static (_, index) => index % 5 == 0), .. HostBuiltSubjects()];

    /// <summary>Every node the preflight's child enumeration reaches from <paramref name="root"/>, once each.</summary>
    private static HashSet<object> GraphNodes(object root)
    {
        var nodes = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!nodes.Add(node))
                continue;
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return nodes;
    }

    /// <summary>
    /// Every public counter of an observer, by name, except the two table counters: which tables a walk took over or
    /// built is what these tests vary, and each test asserts them on their own.
    /// </summary>
    private static SortedDictionary<string, long> WalkCounters(FrontEndTraversalObservations observations)
    {
        var counters = new SortedDictionary<string, long>(StringComparer.Ordinal);
        foreach (var property in typeof(FrontEndTraversalObservations).GetProperties(BindingFlags.Instance | BindingFlags.Public))
        {
            if (property.Name is nameof(FrontEndTraversalObservations.PreEvaluationHandedOverTables)
                or nameof(FrontEndTraversalObservations.PreEvaluationAliasReachTables))
                continue;
            if (property.PropertyType == typeof(long) || property.PropertyType == typeof(int))
                counters[property.Name] = Convert.ToInt64(property.GetValue(observations), System.Globalization.CultureInfo.InvariantCulture);
        }

        return counters;
    }

    private static string Show(SortedDictionary<string, long> counters)
        => string.Join(", ", counters.Where(static c => c.Value != 0).Select(static c => $"{c.Key}={c.Value}"));

    /// <summary>A fresh walk over <paramref name="program"/>, with no handed-over storage: the reference.</summary>
    private static (PreEvaluationAstViolation? Violation, FrontEndTraversalObservations Observations) FreshWalk(
        Expr program, bool graphIsAliasFree = false)
    {
        var observations = new FrontEndTraversalObservations();
        var violation = AlgorithmValidation.FindFirstPreEvaluationViolation(
            program, observations, nodeCountHint: 0, tables: null, graphIsAliasFree);
        return (violation, observations);
    }

    private static void AssertSameWalk(
        string label,
        (PreEvaluationAstViolation? Violation, FrontEndTraversalObservations Observations) expected,
        PreEvaluationAstViolation? violation,
        FrontEndTraversalObservations observations)
    {
        Assert.True(Equals(expected.Violation, violation), $"{label}: {violation} instead of {expected.Violation}");
        var expectedCounters = WalkCounters(expected.Observations);
        var actualCounters = WalkCounters(observations);
        Assert.True(expectedCounters.SequenceEqual(actualCounters),
            $"{label}: walk counters {Show(actualCounters)} instead of {Show(expectedCounters)}");
    }

    // ── The token: one owner at a time, storage only ────────────────────────────────────────────────

    [Fact]
    public void Take_MovesTheTableOutEmpty_AndLeavesNothingBehind()
    {
        var tables = new PreEvaluationTables();
        Assert.Null(tables.TakeNodeSet(16));
        Assert.Null(tables.TakeNodeTable(16));

        var marked = new object();
        var set = new HashSet<object>(ReferenceEqualityComparer.Instance) { marked, new() };
        var table = new Dictionary<object, int>(ReferenceEqualityComparer.Instance) { [marked] = 7 };
        tables.HandOver(set);
        tables.HandOver(table);

        var takenSet = Assert.IsType<HashSet<object>>(tables.TakeNodeSet(64));
        var takenTable = Assert.IsType<Dictionary<object, int>>(tables.TakeNodeTable(64));
        Assert.Same(set, takenSet);
        Assert.Same(table, takenTable);
        Assert.Empty(takenSet);
        Assert.Empty(takenTable);
        Assert.DoesNotContain(marked, takenSet);
        Assert.False(takenTable.ContainsKey(marked));
        Assert.True(takenSet.EnsureCapacity(0) >= 64);
        Assert.True(takenTable.EnsureCapacity(0) >= 64);

        // Moved: a second take finds nothing, so no two passes can hold one table.
        Assert.Null(tables.TakeNodeSet(16));
        Assert.Null(tables.TakeNodeTable(16));
    }

    [Fact]
    public void HandOver_IntoAnOccupiedSlot_OrOfAStructuralTable_FailsLoud()
    {
        var tables = new PreEvaluationTables();
        tables.HandOver(new HashSet<object>(ReferenceEqualityComparer.Instance));
        tables.HandOver(new Dictionary<object, int>(ReferenceEqualityComparer.Instance));
        Assert.Throws<InvalidOperationException>(() => tables.HandOver(new HashSet<object>(ReferenceEqualityComparer.Instance)));
        Assert.Throws<InvalidOperationException>(() => tables.HandOver(new Dictionary<object, int>(ReferenceEqualityComparer.Instance)));

        var fresh = new PreEvaluationTables();
        Assert.Throws<InvalidOperationException>(() => fresh.HandOver(new HashSet<object>()));
        Assert.Throws<InvalidOperationException>(() => fresh.HandOver(new Dictionary<object, int>()));
        Assert.Null(fresh.TakeNodeSet(0));
        Assert.Null(fresh.TakeNodeTable(0));
    }

    [Fact]
    public void ThePasses_HandOverOnlyWhenTheyAdmit()
    {
        // The guard and the preflight hand their tables over as their last act on an admitted graph only.
        var program = TwoViolations(3);
        var tables = new PreEvaluationTables();
        Assert.False(DeferredModuleRegion.RequiresAsyncEvaluationCounting(program, out var guardCount, tables));
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts, guardCount, tables));
        Assert.Equal(guardCount, facts.NodeCount);
        Assert.Empty(Assert.IsType<HashSet<object>>(tables.TakeNodeSet(0)));
        Assert.Empty(Assert.IsType<Dictionary<object, int>>(tables.TakeNodeTable(0)));

        // A rejected graph hands nothing over: a too-deep spine and a cycle.
        Expr spine = new Expr.Num(1);
        for (var i = 0; i < EvaluationLimits.MaxSupportedAstDepth + 50; i++)
            spine = new Expr.Unary(UnaryOp.Minus, spine);
        var tooDeep = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [spine]));
        var cycleProperties = new List<Property>();
        var cyclic = new Algorithm.User(null, [], [], cycleProperties, [new Expr.Num(1)]);
        cycleProperties.Add(new Property("Self", cyclic));
        foreach (var rejected in new Expr[] { tooDeep, new Expr.AlgorithmExpr(cyclic) })
        {
            var refused = new PreEvaluationTables();
            Assert.NotNull(AstStructuralPreflight.CheckAdmittedProgram(rejected, Limit, Profile, out _, 0, refused));
            Assert.Null(refused.TakeNodeTable(0));
        }
    }

    // ── A handed-over or pre-filled table cannot hide a node ────────────────────────────────────────

    [Fact]
    public void TheValidationWalk_OverAGraphTheEarlierPassesMarkedEntirely_StillVisitsAndChecksEveryNode()
    {
        // The entry guard's set holds EVERY node of the graph and the preflight's table a height for EVERY
        // node. Read as the walk's visited set, the first would make the walk skip the whole graph; read
        // as alias-reach answers, the second would skip or fake contextual alias visits. Taken through
        // the token, they arrive empty: the walk visits and checks exactly what a fresh walk does.
        var subjects = Subjects();
        var aliasSubjects = 0;
        foreach (var (label, program) in subjects)
        {
            var tables = new PreEvaluationTables();
            Assert.False(DeferredModuleRegion.RequiresAsyncEvaluationCounting(program, out var guardCount, tables), label);
            Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts, guardCount, tables));
            // The previous passes marked every node: the guard's set and the preflight's table are full.
            Assert.Equal(GraphNodes(program).Count, guardCount);
            Assert.Equal(guardCount, facts.NodeCount);

            // The reference walk checks aliases everywhere (no alias-free proof, no hand-over).
            var expected = FreshWalk(program);
            var observations = new FrontEndTraversalObservations();
            // Without the alias-free proof the walk takes BOTH tables; with it, only the set.
            var violation = AlgorithmValidation.FindFirstPreEvaluationViolation(
                program, observations, facts.NodeCount, tables, graphIsAliasFree: false);
            AssertSameWalk(label, expected, violation, observations);
            Assert.Equal(2, observations.PreEvaluationHandedOverTables);
            Assert.Equal(1, observations.PreEvaluationAliasReachTables);
            if (!facts.IsAliasFree) aliasSubjects++;
        }

        output.WriteLine($"subjects={subjects.Count} with an alias={aliasSubjects}");
        Assert.True(aliasSubjects >= 4, aliasSubjects.ToString(System.Globalization.CultureInfo.InvariantCulture));
    }

    [Fact]
    public void TheValidationWalk_HandedAdversariallyPrefilledTables_StillFindsEveryViolation()
    {
        // Not a pass's leftovers but the worst a stale table could say: every node (and every parameter
        // pattern list the walk marks) already visited, and every node answered "reaches no alias" —
        // or "reaches an alias". Neither may hide a node, an alias check or a violation.
        foreach (var (label, program) in Subjects())
        {
            var expected = FreshWalk(program);
            var nodes = GraphNodes(program);
            foreach (var aliasAnswer in new[] { AstStructuralPreflight.AliasNotReached, AstStructuralPreflight.AliasReached })
            {
                var stale = new HashSet<object>(nodes, ReferenceEqualityComparer.Instance);
                foreach (var node in nodes)
                    if (node is Algorithm algorithm)
                        stale.Add(algorithm.ParameterPatterns);
                var staleAnswers = nodes.ToDictionary(static node => node, _ => aliasAnswer, ReferenceEqualityComparer.Instance);
                var tables = new PreEvaluationTables();
                tables.HandOver(stale);
                tables.HandOver(staleAnswers);

                var observations = new FrontEndTraversalObservations();
                var violation = AlgorithmValidation.FindFirstPreEvaluationViolation(
                    program, observations, nodes.Count, tables, graphIsAliasFree: false);
                AssertSameWalk($"{label} (stale answer {aliasAnswer})", expected, violation, observations);
                Assert.Equal(2, observations.PreEvaluationHandedOverTables);
            }
        }

        // The deep alias violations are among them, at their exact positions.
        var notStatic = Assert.IsType<PreEvaluationAstViolation.AliasTargetNotStaticPath>(FreshWalk(DeepNotStaticAlias()).Violation);
        Assert.Equal(TargetSpan, notStatic.Target.Span);
        var cycle = Assert.IsType<PreEvaluationAstViolation.AliasCycle>(FreshWalk(DeepAliasCycle()).Violation);
        Assert.Equal(ClosingTargetSpan, cycle.Target.Span);
        Assert.IsType<PreEvaluationAstViolation.AliasCycle>(FreshWalk(DeepParentScopeAliasCycle()).Violation);
        Assert.Null(FreshWalk(DeepLegalAlias()).Violation);
    }

    // ── The alias-free proof and skip ───────────────────────────────────────────────────────────────

    [Fact]
    public void TheAliasFreeFact_IsDecidedOverTheWholeGraph_AndProvesNoNodeReachesAnAlias()
    {
        // The admission walk's fact is exactly "no node of the whole graph is an alias": decided by a walk
        // that visits every node, never a sample. Where it holds, the alias reach answers false for every
        // node of the graph — the nodes the validation walk asks about — so skipping the table changes nothing.
        var subjects = Subjects();
        var aliasFree = 0;
        foreach (var (label, program) in subjects)
        {
            Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
            var nodes = GraphNodes(program);
            Assert.Equal(!nodes.Any(AstStructuralPreflight.IsValidationAlias), facts.IsAliasFree);
            if (!facts.IsAliasFree)
            {
                Assert.True(AstStructuralPreflight.ReachesAlias(program, new(ReferenceEqualityComparer.Instance)), label);
                continue;
            }

            aliasFree++;
            var memo = new Dictionary<object, int>(ReferenceEqualityComparer.Instance);
            foreach (var node in nodes)
                Assert.False(AstStructuralPreflight.ReachesAlias(node, memo), label);
            var skipped = FreshWalk(program, graphIsAliasFree: true);
            AssertSameWalk(label, FreshWalk(program), skipped.Violation, skipped.Observations);
            Assert.Equal(0, skipped.Observations.PreEvaluationAliasReachTables);
        }

        output.WriteLine($"subjects={subjects.Count} alias-free={aliasFree}");
        Assert.True(aliasFree > 0 && aliasFree < subjects.Count, $"alias-free={aliasFree} of {subjects.Count}");

        // The other admission checks never claim the proof: only the complete admission walk decides it.
        var free = TwoViolations(2);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(free, Limit, Profile, out var admitted));
        Assert.True(admitted.IsAliasFree);
        Assert.False(default(AstStructuralPreflight.AdmittedProgramFacts).IsAliasFree);
    }

    private static FrontEndTraversalObservations ObservedSyncRun(Expr program, out EvalResult<Evaluator.CountedResult> result)
    {
        var traversal = new FrontEndTraversalObservations();
        (result, _) = Evaluator.RunCountedObserved(
            program, observations: new EvaluationObservations { PreEvaluationTraversal = traversal },
            hostOperations: CorpusOperations(), randomSeed: 1);
        return traversal;
    }

    [Fact]
    public void ASynchronousRun_BuildsNoAliasReachTable_ForAnAliasFreeProgram_AndReusesTheGuardsSet()
    {
        var subjects = Subjects();
        var counted = 0;
        foreach (var (label, program) in subjects)
        {
            Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
            var traversal = ObservedSyncRun(program, out _);
            // The guard's set always becomes the visited set; the preflight's table becomes the alias-reach
            // table exactly when the graph may hold an alias.
            Assert.Equal(facts.IsAliasFree ? 0 : 1, traversal.PreEvaluationAliasReachTables);
            Assert.Equal(facts.IsAliasFree ? 1 : 2, traversal.PreEvaluationHandedOverTables);
            Assert.Equal(facts.NodeCount, traversal.StructuralPreflightCapacityHints);
            counted++;
        }

        Assert.Equal(subjects.Count, counted);

        // A source program with a callable alias (`K = cos`): the table is built. Without one it is not.
        // (Not `P = { K = 1; K }`: braces are no nested scope, so that `P` elaborates as an alias of `K`.)
        var source = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("K = cos\nK(0)").Root);
        var sourceTraversal = ObservedSyncRun(source, out var sourceResult);
        Assert.True(sourceResult.IsOk, sourceResult.IsError ? sourceResult.Error.ToString() : null);
        Assert.Equal(1, sourceTraversal.PreEvaluationAliasReachTables);
        Assert.Equal(2, sourceTraversal.PreEvaluationHandedOverTables);
        var plain = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("K = 1\nK").Root);
        var plainTraversal = ObservedSyncRun(plain, out var plainResult);
        Assert.True(plainResult.IsOk, plainResult.IsError ? plainResult.Error.ToString() : null);
        Assert.Equal(0, plainTraversal.PreEvaluationAliasReachTables);
        Assert.Equal(1, plainTraversal.PreEvaluationHandedOverTables);
    }

    public static TheoryData<string> DeepAliasPrograms() => ["not a static path", "cycle", "parent-scope cycle"];

    private static Expr DeepAliasProgram(string name) => name switch
    {
        "not a static path" => DeepNotStaticAlias(),
        "cycle" => DeepAliasCycle(),
        "parent-scope cycle" => DeepParentScopeAliasCycle(),
        _ => throw new ArgumentOutOfRangeException(nameof(name)),
    };

    private static string Describe(EvalError error)
        => $"{error.GetType().Name} {error.Span}: {(error as EvalError.IllegalInEval)?.Reason}";

    [Theory]
    [MemberData(nameof(DeepAliasPrograms))]
    public async Task ADeeplyNestedAlias_StillGetsTheAliasCheck_AndItsExactDiagnostic(string name)
    {
        var program = DeepAliasProgram(name);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
        Assert.False(facts.IsAliasFree);

        // The exact refusal the walk alone reports, with its position.
        var violation = FreshWalk(program).Violation;
        EvalError expected = violation switch
        {
            PreEvaluationAstViolation.AliasTargetNotStaticPath v =>
                new EvalError.IllegalInEval(Evaluator.AliasTargetNotStaticPathMessage(v.Target)) { Span = v.Target.Span },
            PreEvaluationAstViolation.AliasCycle v => new EvalError.IllegalInEval(Evaluator.AliasCycleMessage) { Span = v.Target.Span },
            _ => throw new InvalidOperationException($"{name}: {violation}"),
        };
        if (name == "not a static path")
            Assert.Equal(TargetSpan, expected.Span);
        if (name == "cycle")
            Assert.Equal(ClosingTargetSpan, expected.Span);

        var traversal = ObservedSyncRun(program, out var syncResult);
        Assert.True(syncResult.IsError);
        Assert.Equal(Describe(expected), Describe(syncResult.Error));
        Assert.Equal(1, traversal.PreEvaluationAliasReachTables);
        Assert.Equal(2, traversal.PreEvaluationHandedOverTables);

        // The async entry and the twin path refuse it identically.
        var (asyncResult, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(program));
        Assert.Equal(Describe(expected), Describe(asyncResult.Error));
        var (twinResult, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new KatLang.Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache()));
        Assert.Equal(Describe(expected), Describe(twinResult.Error));
    }

    // ── The async entry's tree fact sizes the preflight ─────────────────────────────────────────────

    [Fact]
    public async Task TheAsyncEntry_PresizesThePreflightTable_AndMatchesTheSyncEntry()
    {
        var subjects = Subjects();
        foreach (var (label, program) in subjects)
        {
            Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
            var fact = Evaluator.DecideTreeRequiresAsyncEvaluation(program, CorpusOperations());
            Assert.Equal(new Evaluator.TreeRouteFact(false, facts.NodeCount), fact);

            var syncTraversal = ObservedSyncRun(program, out var syncResult);

            // The async entry decides the fact (its one walk) and hands its count to the fast path's preflight.
            var asyncTraversal = new FrontEndTraversalObservations();
            var (asyncResult, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                program, observations: new EvaluationObservations { PreEvaluationTraversal = asyncTraversal },
                hostOperations: CorpusOperations(), randomSeed: 1));
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncResult), AsyncEvaluationHarness.NeutralOf(asyncResult));
            Assert.Equal(facts.NodeCount, asyncTraversal.StructuralPreflightCapacityHints);
            Assert.Equal(syncTraversal.StructuralPreflightCapacityHints, asyncTraversal.StructuralPreflightCapacityHints);
            // The fast path's guard made no walk, so only the preflight's table can be handed over.
            Assert.Equal(facts.IsAliasFree ? 0 : 1, asyncTraversal.PreEvaluationHandedOverTables);
            Assert.Equal(syncTraversal.PreEvaluationAliasReachTables, asyncTraversal.PreEvaluationAliasReachTables);

            // An internal caller handing no fact: the route rule decides it, with its count, once.
            var undecidedTraversal = new FrontEndTraversalObservations();
            var undecided = await AsyncEvaluationHarness.Complete(Evaluator.RunAsync(
                program, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(),
                observations: new EvaluationObservations { PreEvaluationTraversal = undecidedTraversal },
                hostOperations: CorpusOperations(), randomSeed: 1));
            Assert.Equal(facts.NodeCount, undecidedTraversal.StructuralPreflightCapacityHints);
            Assert.Equal(
                syncResult.IsError ? $"err {SemanticExplorerHarness.ErrorCategory(syncResult.Error)}" : $"ok raw={SemanticExplorerHarness.Neutral(syncResult.Value.Value)}",
                AsyncEvaluationHarness.NeutralOf(undecided));
        }
    }

    [Fact]
    public async Task TheTwinPath_IsPresizedFromADecidedFact_AndFromNothingWithoutOne()
    {
        // A deferred-region root: the deciding walk stops at the placeholder, and that partial count sizes
        // the twin's preflight. The result is unchanged (the selected branch materializes: 2).
        var parsed = await Parser.ParseAsync(
            "F(0) = 1\nF(1) = {\n    open 'https://katlang.org/lazy/b.kat'\n    B\n}\nF(1)",
            new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("public B = 2") });
        Assert.False(parsed.HasErrors);
        var deferred = new Expr.AlgorithmExpr(parsed.Root);
        var fact = Evaluator.DecideTreeRequiresAsyncEvaluation(deferred, hostOperations: null);
        Assert.True(fact?.RequiresAsyncEvaluation);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(deferred, Limit, Profile, out var facts));
        Assert.InRange(fact!.Value.NodeCountHint, 1, facts.NodeCount);

        var deferredTraversal = new FrontEndTraversalObservations();
        var (deferredResult, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            deferred, observations: new EvaluationObservations { PreEvaluationTraversal = deferredTraversal }));
        Assert.Equal("ok raw=2 n=1", AsyncEvaluationHarness.NeutralOf(deferredResult));
        Assert.Equal(fact.Value.NodeCountHint, deferredTraversal.StructuralPreflightCapacityHints);

        // An async-capable cache routes before any walk: no fact, no count, the preflight starts from 0.
        var program = TwoViolations(3);
        var twinTraversal = new FrontEndTraversalObservations();
        var (twinResult, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new KatLang.Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache(),
            observations: new EvaluationObservations { PreEvaluationTraversal = twinTraversal }));
        Assert.IsType<EvalError.ExplicitParametersRequireOutput>(twinResult.Error);
        Assert.Equal(0, twinTraversal.StructuralPreflightCapacityHints);
        // The twin's walk still takes the preflight's storage only when it needs an alias-reach table.
        Assert.Equal(0, twinTraversal.PreEvaluationHandedOverTables);
        Assert.Equal(0, twinTraversal.PreEvaluationAliasReachTables);
    }

    // ── What the hand-over saves (coarse, in-process) ───────────────────────────────────────────────

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
    public void TheValidationWalk_TakingTheGuardsSet_OverAnAliasFreeGraph_AllocatesFarLessThanASizedFreshWalk()
    {
        // The benchmark's ParameterizedCall program (201 chained calls, about a thousand nodes). The sized
        // fresh walk of 2026-11-11 allocated its visited set and its alias-reach table at their final size;
        // taking the guard's set and building no alias-reach table removes both. A coarse ratio.
        var source = "Inc(v) = v + 1\n" + string.Join(" + ", Enumerable.Repeat("Inc(0)", 201)) + "\n";
        Expr program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
        Assert.True(facts.IsAliasFree);
        var nodes = facts.NodeCount;
        Assert.False(DeferredModuleRegion.RequiresAsyncEvaluationCounting(program, out _, new PreEvaluationTables()));
        var guardSet = new HashSet<object>(GraphNodes(program), ReferenceEqualityComparer.Instance);

        var sized = MinimumBytes(() => _ = AlgorithmValidation.FindFirstPreEvaluationViolation(program, observations: null, nodes));
        var handedOver = MinimumBytes(() =>
        {
            var tables = new PreEvaluationTables();
            tables.HandOver(guardSet);
            _ = AlgorithmValidation.FindFirstPreEvaluationViolation(program, observations: null, nodes, tables, facts.IsAliasFree);
        });
        output.WriteLine($"nodes={nodes} validation walk sized {sized} -> handed over, alias-free {handedOver}");
        Assert.True(handedOver * 3 < sized, $"validation walk {sized} -> {handedOver}");
    }
}
