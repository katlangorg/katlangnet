using System.Globalization;
using System.Numerics;
using System.Reflection;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// LITERAL CLAUSE RUNS (2026-11-22; finding <c>values-builtins-numerics-literal-clause-table-quadratic</c> of the
/// 2026-11-21 adversarial performance and reliability investigation, baseline <c>8947d21e</c>). A clause family
/// dispatch attempted its clauses in written order, so a lookup table of N literal clauses cost O(N) attempts per
/// call and O(N²) for a workload that reads every key (8,390,656 attempts for 4,096 keys, 16,781,312 when every key
/// misses). A run of consecutive literal-only clauses of one arity is now indexed once per run per family
/// (<see cref="Evaluator.LiteralClauseRun"/>), and its selector replays only the ordered attempts that demand a
/// supplied value or select (at most <c>2·arity + 1</c> per run). Implementation-only: these tests pin the index's
/// lookups against <c>MatchLiteralPattern</c>, the selector against the ordered binder it replays (selection, demand
/// order, errors, recorded attempts), and whole programs against the ordered route itself
/// (<see cref="OrderedClauseDispatchTestSeam"/>) on the plain, counted generic, optimized, invocation-plan, async and
/// suspending routes — values, errors and spans, effects, ticks, every budget counter, the step-limit and depth-limit
/// outcomes and cancellation — plus the attempt counts, the absence of per-call allocation and the preparation's
/// lifetime. The programs the Lean model shares are guarded there too (<c>CoreTests/LiteralClauseTables.lean</c>), and
/// the Lean-compared corpus programs that now select through a run are pinned to the ordered route's outcomes.
/// </summary>
public class LiteralClauseRunTests
{
    // ── reflection handles ───────────────────────────────────────────────────────────────────────

    private delegate EvalResult<bool> MatchLiteral(Pattern literal, Result result, Evaluator.EvalCtx ctx);

    private delegate IReadOnlyList<Evaluator.NeedPattern> ClauseHead(Pattern pattern);

    private delegate EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?> BindLiteral(
        IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply, in Evaluator.EvalCtx ctx);

    private delegate EvalResult<int> SelectRun(Evaluator.LiteralClauseRun run, IReadOnlyList<NeedCell> supply, EvaluationObservations? observations);

    private delegate ValueTask<EvalResult<int>> SelectRunAsync(Evaluator.LiteralClauseRun run, IReadOnlyList<NeedCell> supply, EvaluationObservations? observations);

    private static T Private<T>(string name) where T : Delegate
        => typeof(Evaluator).GetMethod(name, BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<T>();

    private static readonly MatchLiteral Match = Private<MatchLiteral>("MatchLiteralPattern");
    private static readonly ClauseHead TranslateHead = Private<ClauseHead>("NeedClauseHead");
    private static readonly BindLiteral BindOrdered = Private<BindLiteral>("BindFlatLiteralHead");
    private static readonly SelectRun Select = Private<SelectRun>("SelectLiteralRunClause");
    private static readonly SelectRunAsync SelectAsync = Private<SelectRunAsync>("SelectLiteralRunClauseAsync");

    private static Decimal128 D(string text) => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);

    private static Pattern Head(params Pattern[] items) => items.Length == 1 ? items[0] : new Pattern.SequenceValue(items);

    private static IReadOnlyList<Evaluator.NeedPattern>[] Heads(IEnumerable<Pattern> patterns) => patterns.Select(p => TranslateHead(p)).ToArray();

    private static string Text(int length, char fill = 'k') => new(fill, length);

    // ── 1. the index answers exactly what MatchLiteralPattern answers ─────────────────────────────

    /// <summary>Numeric literals and values across quanta, signs of zero, NaN, infinities and the range ends.</summary>
    private static Decimal128[] Numbers()
    {
        var values = new List<Decimal128>
        {
            D("0"), D("-0"), D("0.000"), D("0E+12"), D("1"), D("1.0"), D("1.000"), D("10E-1"), D("-1"), D("-1.00"),
            D("2"), D("2.5"), D("2.50"), D("100"), D("1E2"), D("100.0"), D("0.3"), D("0.30"), D("0.1") + D("0.2"),
            D("1234567890123456789012345678901234"), D("1234567890123456789012345678901235"), D("1.234567890123456789012345678901234E+6000"),
            Decimal128.MaxValue, Decimal128.MinValue, Decimal128.Epsilon, -Decimal128.Epsilon, Decimal128.NaN, -Decimal128.NaN,
            Decimal128.PositiveInfinity, Decimal128.NegativeInfinity, Decimal128.PositiveInfinity - Decimal128.PositiveInfinity,
        };
        for (var i = 3; i < 40; i += 7)
            values.Add(Decimal128.ScaleB((Decimal128)i, -2) * 100);
        return [.. values];
    }

    private static string[] Texts() =>
    [
        "", "a", "A", "a ", "ab", "1", "true", "zero", "k", "naïve", "naı̈ve", "é", "é",
        Text(62), Text(63), Text(63, 'q'), Text(64), Text(65), Text(64, 'q'), Text(100), Text(62) + "x",
    ];

    private static Result[] Values()
    {
        var values = new List<Result>();
        values.AddRange(Numbers().Select(static n => (Result)new Result.Atom(n)));
        values.AddRange(Texts().Select(static t => (Result)new Result.Str(t)));
        values.Add(new Result.Bool(true));
        values.Add(new Result.Bool(false));
        values.Add(new Result.SequenceValue([]));
        values.Add(new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]));
        values.Add(new Result.ListValue([new Result.Atom(1)]));
        values.Add(new Result.ListValue([]));
        values.Add(new Result.ListValue([new Result.Str("a")]));
        return [.. values];
    }

    /// <summary>Every indexable literal of the value pool: numbers, Booleans and strings shorter than 64 code units.</summary>
    private static Pattern[] IndexableLiterals()
        => [.. Numbers().Select(static n => (Pattern)new Pattern.LitInt(n)),
            .. Texts().Where(static t => t.Length < Result.ValueSemanticComparer.StringCharsPerUnit).Select(static t => (Pattern)new Pattern.LitString(t)),
            new Pattern.LitBool(true), new Pattern.LitBool(false)];

    public static TheoryData<int, int> LiteralPoolCuts => new() { { 0, 2 }, { 0, 4 }, { 0, 5 }, { 3, 9 }, { 0, 200 }, { 20, 200 }, { 31, 33 } };

    [Theory]
    [MemberData(nameof(LiteralPoolCuts))]
    public void ARunsFirstPosition_FindsTheFirstClauseWhoseLiteralMatchLiteralPatternMatches(int skip, int take)
    {
        // Duplicates by value (1 and 1.0, 0 and -0, every NaN) are kept: the first one is the path's clause.
        var literals = IndexableLiterals().Skip(skip).Take(take).ToArray();
        var runs = Evaluator.PrepareLiteralClauseRuns(Heads(literals), CancellationToken.None);
        var run = Assert.IsType<Evaluator.LiteralClauseRun>(Assert.Single(runs!, static r => r is not null));
        Assert.Equal((0, literals.Length, 1), (run.Start, run.End, run.Arity));
        foreach (var value in Values())
        {
            int? expected = null;
            for (var clause = 0; clause < literals.Length && expected is null; clause++)
            {
                var matched = Match(literals[clause], value, Evaluator.EvalCtx.Empty);
                Assert.True(matched.IsOk, "an indexable literal never fails its comparison");
                if (matched.Value) expected = clause;
            }
            Assert.Equal(expected, run.Root.Find(value)?.First);
        }
    }

    [Fact]
    public void TheNumberComparer_IsDecimal128Equality_WithAConsistentHash()
    {
        var numbers = Numbers().ToList();
        var random = new Random(20261122);
        for (var i = 0; i < 400; i++)
        {
            // One value spelled at several quanta: coefficient c·10^z at exponent e − z.
            var coefficient = random.NextInt64(0, 10_000_000_000);
            var exponent = random.Next(-6100, 6000);
            for (var z = 0; z < 5; z++)
            {
                var value = Decimal128.ScaleB((Decimal128)(coefficient * (long)Math.Pow(10, z)), exponent - z);
                numbers.Add(value);
                numbers.Add(-value);
            }
        }
        var comparer = Evaluator.LiteralNumberEquality.Instance;
        foreach (var x in numbers)
        {
            foreach (var y in numbers)
            {
                Assert.Equal(x.Equals(y), comparer.Equals(x, y));
                if (x.Equals(y))
                    Assert.True(comparer.GetHashCode(x) == comparer.GetHashCode(y), $"{x} and {y} are equal but hash apart");
            }
        }
    }

    // ── 2. which heads form a run ─────────────────────────────────────────────────────────────────

    public static TheoryData<string, string> RunCases => new()
    {
        // spec: clauses separated by ';', positions by ','; n = number, s = short string, L = 64-unit string,
        // N = null string, b = Boolean, x/y = names, v = repeated name, ( ) = structural, * = collector.
        { "1;2", "0-2/1" },
        { "1", "" },
        { "1;2;x;3;4", "0-2/1 3-5/1" },
        { "1;2;3;x", "0-3/1" },
        { "x;1;2", "1-3/1" },
        { "1,2;1,3;2,2", "0-3/2" },
        { "1;2;1,2;1,3", "0-2/1 2-4/2" },
        { "1,2;1,x;2,2;3,3", "2-4/2" },
        { "1,2;1,x;2,2;x,3", "" },
        { "s;b;1;s;b", "0-5/1" },
        { "1;L;2;3", "2-4/1" },
        { "1;N;2;3", "2-4/1" },
        { "1;(x,y);2;3", "2-4/1" },
        { "1;*;2;3", "2-4/1" },
        { "v,v;1,2;3,4", "1-3/2" },
        { "W16;W16;W17;W17", "0-2/16" },
    };

    private static Pattern RunSpecHead(string clause, int index)
    {
        Pattern Item(string item, int position) => item switch
        {
            "s" => new Pattern.LitString("s" + index),
            "L" => new Pattern.LitString(Text(Result.ValueSemanticComparer.StringCharsPerUnit)),
            "N" => new Pattern.LitString(null!),
            "b" => new Pattern.LitBool(index % 2 == 0),
            "x" => new Pattern.Bind("x" + position),
            "y" => new Pattern.Bind("y" + position),
            "v" => new Pattern.Bind("v"),
            "*" => new Pattern.Bind("rest") { ParameterKind = ParameterKind.Collecting },
            "(x,y)" => new Pattern.SequenceValue([new Pattern.Bind("p"), new Pattern.Bind("q")]),
            _ => new Pattern.LitInt(int.Parse(item, CultureInfo.InvariantCulture)),
        };
        if (clause.StartsWith('W'))
            return Head(Enumerable.Range(0, int.Parse(clause[1..], CultureInfo.InvariantCulture)).Select(p => (Pattern)new Pattern.LitInt(p + index)).ToArray());
        if (clause == "(x,y)")
            return new Pattern.SequenceValue([Item(clause, 0)]);
        return Head(clause.Split(',').Select(Item).ToArray());
    }

    [Theory]
    [MemberData(nameof(RunCases))]
    public void Runs_AreTheMaximalSequencesOfLiteralOnlyHeadsOfOneArity(string spec, string expected)
    {
        var heads = Heads(spec.Split(';').Select(RunSpecHead));
        var runs = Evaluator.PrepareLiteralClauseRuns(heads, CancellationToken.None);
        var found = runs is null
            ? ""
            : string.Join(" ", runs.Select((run, start) => (run, start)).Where(static p => p.run is not null)
                .Select(static p => { Assert.Equal(p.start, p.run!.Start); return $"{p.run.Start}-{p.run.End}/{p.run.Arity}"; }));
        Assert.Equal(expected, found);
        if (runs is not null)
            Assert.Equal(heads.Length, runs.Length);
    }

    // ── 3. the selector replays the ordered attempts ──────────────────────────────────────────────

    // A cell that logs its first (evaluating) demand, then yields `value` or fails.
    private static NeedCell Logged(List<int> log, int id, EvalResult<Evaluator.CountedResult> value)
        => new(() => { log.Add(id); return value; }, () => { log.Add(id); return new(value); });

    private static EvalResult<Evaluator.CountedResult> Ok(Result value) => EvalResult<Evaluator.CountedResult>.Ok(new(value, 1));

    private static string Trace(ClauseAttemptObservations attempts)
        => string.Join(" ", attempts.Attempts.Select(static a => $"{a.Dispatch}:{a.Clause}:{a.Outcome}"));

    private sealed record Replay(string Outcome, string Demands, IReadOnlyList<ClauseAttempt> Attempts);

    // The ordered route over a run alone: BindFlatLiteralHead per clause, in order, recorded as the drivers record.
    private static Replay Ordered(IReadOnlyList<Evaluator.NeedPattern>[] heads, Func<List<int>, NeedCell[]> supply)
    {
        var log = new List<int>();
        var cells = supply(log);
        var attempts = new ClauseAttemptObservations();
        var family = new Algorithm.Conditional(Parent: null, Opens: [], Branches: []);
        attempts.BeginDispatch(family);
        string outcome = "none";
        for (var clause = 0; clause < heads.Length; clause++)
        {
            attempts.RecordAttempt(clause);
            var bound = BindOrdered(heads[clause], cells, Evaluator.EvalCtx.Empty);
            attempts.RecordOutcome(bound.IsError ? ClauseAttemptOutcome.Error : bound.Value is null ? ClauseAttemptOutcome.NonMatch : ClauseAttemptOutcome.Matched);
            if (bound.IsError) { outcome = "err " + bound.Error.Code; break; }
            if (bound.Value is not null) { Assert.Empty(bound.Value); outcome = "clause " + clause; break; }
        }
        return new(outcome, string.Join(",", log), attempts.Attempts);
    }

    private static Replay Indexed(Evaluator.LiteralClauseRun run, Func<List<int>, NeedCell[]> supply, bool asynchronous)
    {
        var log = new List<int>();
        var cells = supply(log);
        var attempts = new ClauseAttemptObservations();
        var observations = new EvaluationObservations { ClauseAttempts = attempts };
        attempts.BeginDispatch(new Algorithm.Conditional(Parent: null, Opens: [], Branches: []));
        var selected = asynchronous ? SelectAsync(run, cells, observations).GetAwaiter().GetResult() : Select(run, cells, observations);
        Assert.Equal(1, observations.LiteralClauseRunSelectionCount);
        var outcome = selected.IsError ? "err " + selected.Error.Code : selected.Value < 0 ? "none" : "clause " + selected.Value;
        return new(outcome, string.Join(",", log), attempts.Attempts);
    }

    // The recorded attempts of the index are a subsequence of the ordered ones, with their outcomes, starting with the
    // run's first clause and ending with the ordered route's last attempt whenever that one matched or failed.
    private static void AssertReplayed(Replay ordered, Replay indexed, string label)
    {
        Assert.True(ordered.Outcome == indexed.Outcome, $"{label}: ordered {ordered.Outcome}, indexed {indexed.Outcome}");
        Assert.True(ordered.Demands == indexed.Demands, $"{label}: ordered demands [{ordered.Demands}], indexed [{indexed.Demands}]");
        var next = 0;
        foreach (var attempt in indexed.Attempts)
        {
            while (next < ordered.Attempts.Count && ordered.Attempts[next].Clause != attempt.Clause) next++;
            Assert.True(next < ordered.Attempts.Count, $"{label}: indexed attempt {attempt.Clause} is not an ordered one in order");
            Assert.Equal(ordered.Attempts[next].Outcome, attempt.Outcome);
            next++;
        }
        Assert.Equal(ordered.Attempts[0].Clause, indexed.Attempts[0].Clause);
        if (ordered.Attempts[^1].Outcome is not ClauseAttemptOutcome.NonMatch)
            Assert.Equal((ordered.Attempts[^1].Clause, ordered.Attempts[^1].Outcome), (indexed.Attempts[^1].Clause, indexed.Attempts[^1].Outcome));
    }

    public static TheoryData<int, int, int> RandomRunShapes => new()
    {
        // arity, clauses, seed
        { 1, 2, 1 }, { 1, 3, 2 }, { 1, 12, 3 }, { 1, 40, 4 }, { 2, 6, 5 }, { 2, 30, 6 }, { 3, 25, 7 }, { 3, 60, 8 }, { 4, 50, 9 },
    };

    [Theory]
    [MemberData(nameof(RandomRunShapes))]
    public void TheSelector_ReplaysTheOrderedAttempts_SelectionDemandsErrorsAndRecordedOutcomes(int arity, int clauses, int seed)
    {
        // Literals from a small domain so that clauses share prefixes; mixed kinds, duplicates by value included.
        var random = new Random(seed);
        Pattern[] domain = [new Pattern.LitInt(0), new Pattern.LitInt(1), new Pattern.LitInt(D("1.0")), new Pattern.LitInt(2),
            new Pattern.LitString("a"), new Pattern.LitString(""), new Pattern.LitBool(true), new Pattern.LitBool(false)];
        var patterns = Enumerable.Range(0, clauses)
            .Select(_ => Head(Enumerable.Range(0, arity).Select(_ => domain[random.Next(domain.Length)]).ToArray())).ToArray();
        var heads = Heads(patterns);
        var run = Assert.Single(Evaluator.PrepareLiteralClauseRuns(heads, CancellationToken.None)!, static r => r is not null)!;
        Result[] values = [new Result.Atom(0), new Result.Atom(D("1.00")), new Result.Atom(2), new Result.Atom(3),
            new Result.Str("a"), new Result.Str(""), new Result.Str("b"), new Result.Bool(true), new Result.Bool(false), new Result.ListValue([])];
        for (var trial = 0; trial < 300; trial++)
        {
            // Each position a value from the domain (often matching a prefix), or a failure.
            var slots = Enumerable.Range(0, arity).Select(_ => random.Next(12) == 0
                ? (EvalResult<Evaluator.CountedResult>)new EvalError.BadIndex()
                : Ok(values[random.Next(values.Length)])).ToArray();
            NeedCell[] Supply(List<int> log) => slots.Select((slot, i) => Logged(log, i, slot)).ToArray();
            var ordered = Ordered(heads, Supply);
            AssertReplayed(ordered, Indexed(run, Supply, asynchronous: false), $"seed {seed} trial {trial}");
            AssertReplayed(ordered, Indexed(run, Supply, asynchronous: true), $"seed {seed} trial {trial} (async)");
            Assert.True(Indexed(run, Supply, asynchronous: false).Attempts.Count <= 2 * arity + 1);
        }
    }

    public static TheoryData<string, string, string> ArityOneTraces => new()
    {
        // value, ordered trace of an eight-clause table T(0..7), indexed trace
        { "0", "1:0:Matched", "1:0:Matched" },
        { "1", "1:0:NonMatch 1:1:Matched", "1:0:NonMatch 1:1:Matched" },
        { "2", "1:0:NonMatch 1:1:NonMatch 1:2:Matched", "1:0:NonMatch 1:1:NonMatch 1:2:Matched" },
        { "7", "1:0:NonMatch 1:1:NonMatch 1:2:NonMatch 1:3:NonMatch 1:4:NonMatch 1:5:NonMatch 1:6:NonMatch 1:7:Matched", "1:0:NonMatch 1:1:NonMatch 1:7:Matched" },
        { "9", "1:0:NonMatch 1:1:NonMatch 1:2:NonMatch 1:3:NonMatch 1:4:NonMatch 1:5:NonMatch 1:6:NonMatch 1:7:NonMatch", "1:0:NonMatch 1:1:NonMatch" },
        { "fail", "1:0:Error", "1:0:Error" },
    };

    [Theory]
    [MemberData(nameof(ArityOneTraces))]
    public void AnEightClauseTable_RecordsTheReplayedAttempts(string value, string orderedTrace, string indexedTrace)
    {
        var heads = Heads(Enumerable.Range(0, 8).Select(static i => (Pattern)new Pattern.LitInt(i)));
        var run = Evaluator.PrepareLiteralClauseRuns(heads, CancellationToken.None)![0]!;
        NeedCell[] Supply(List<int> log) => [Logged(log, 0, value == "fail" ? new EvalError.BadIndex() : Ok(new Result.Atom(int.Parse(value, CultureInfo.InvariantCulture))))];
        static string TraceOf(IReadOnlyList<ClauseAttempt> attempts) => string.Join(" ", attempts.Select(static a => $"{a.Dispatch}:{a.Clause}:{a.Outcome}"));
        var ordered = Ordered(heads, Supply);
        Assert.Equal(orderedTrace, TraceOf(ordered.Attempts));
        Assert.Equal(indexedTrace, TraceOf(Indexed(run, Supply, asynchronous: false).Attempts));
        Assert.Equal(indexedTrace, TraceOf(Indexed(run, Supply, asynchronous: true).Attempts));
    }

    [Fact]
    public void ATwoPositionTable_DemandsTheSecondValueOnlyWhereAClauseMatchesTheFirst()
    {
        // G(0, 0..3), G(1, 0..3): the second value is demanded only when the first is 0 or 1.
        var patterns = Enumerable.Range(0, 8).Select(static c => Head(new Pattern.LitInt(c / 4), new Pattern.LitInt(c % 4))).ToArray();
        var heads = Heads(patterns);
        var run = Evaluator.PrepareLiteralClauseRuns(heads, CancellationToken.None)![0]!;
        foreach (var (first, second, demands, outcome) in new[]
        {
            (1, 2, "0,1", "clause 6"), (0, 3, "0,1", "clause 3"), (5, 0, "0", "none"), (1, 9, "0,1", "none"), (-1, 0, "0", "none"),
        })
        {
            NeedCell[] Supply(List<int> log) => [Logged(log, 0, Ok(new Result.Atom(first))), Logged(log, 1, Ok(new Result.Atom(second)))];
            foreach (var asynchronous in new[] { false, true })
            {
                var indexed = Indexed(run, Supply, asynchronous);
                Assert.Equal((outcome, demands), (indexed.Outcome, indexed.Demands));
                AssertReplayed(Ordered(heads, Supply), indexed, $"G({first}, {second})");
            }
        }
    }

    // ── 4. whole programs: the index against the ordered route, on every route ────────────────────

    private sealed class EffectLog
    {
        private readonly List<string> _calls = [];

        public string Calls { get { lock (_calls) return string.Join(",", _calls); } }

        public HostOperations Operations(CancellationTokenSource? cancellation = null) => HostOperations.Create(
            HostOperation.Create("effect", (args, _) => { lock (_calls) _calls.Add(InvocationRouteCorpus.Value(args[0])); return args[0]; }, "x"),
            HostOperation.Create("stop", (args, _) => { lock (_calls) _calls.Add("stop"); cancellation?.Cancel(); return args[0]; }, "x"));
    }

    private enum Route { Plain, Generic, Optimized, Planned, ForcedTwin, SuspendingTwin }

    private static readonly Route[] AllRoutes = [Route.Plain, Route.Generic, Route.Optimized, Route.Planned, Route.ForcedTwin, Route.SuspendingTwin];

    private sealed record Observed(string Outcome, string Counters, string Effects, IReadOnlyList<ClauseAttempt> Attempts, long Selections, long Runs);

    private static string Describe(EvalResult<Result> result)
        => result.IsOk
            ? "ok " + InvocationRouteCorpus.Value(result.Value)
            : $"err {result.Error.Code} | {KatLangError.FromEvalError(result.Error).Message.Replace("\n", " / ", StringComparison.Ordinal)} @{result.Error.Span}";

    private static string Describe(EvalResult<Evaluator.CountedResult> result)
        => result.IsOk ? $"ok {InvocationRouteCorpus.Value(result.Value.Value)} n={result.Value.EmittedCount}" : Describe(EvalResult<Result>.Err(result.Error));

    private static string Counters(EvaluationBudget budget)
        => $"steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} structural={budget.ConsumedStructuralWorkUnits} "
            + $"depth={budget.PeakDepth} items={budget.MaterializedItems} chars={budget.MaterializedStringChars}";

    private static Expr Program(string source, HostOperations? operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static async Task<Observed> Observe(Route route, string source, bool ordered, EvaluationLimits? limits = null)
    {
        var log = new EffectLog();
        var operations = log.Operations();
        var expr = Program(source, operations);
        var attempts = new ClauseAttemptObservations();
        var observations = new EvaluationObservations { ClauseAttempts = attempts };
        using var seam = ordered ? OrderedClauseDispatchTestSeam.Activate() : null;
        string outcome, counters;
        switch (route)
        {
            case Route.Plain:
                outcome = Describe(Evaluator.Run(expr, new RunScopedZeroArgPropertyResultCache(), enableLoopOptimization: true, loopDiagnostics: null,
                    enableSequencePipelineOptimization: true, sequenceDiagnostics: null, limits: limits, observations: observations, hostOperations: operations));
                counters = "";
                break;
            case Route.Generic or Route.Optimized:
            {
                var (result, budget) = Evaluator.RunCountedObserved(expr, limits, enableOptimizations: route is Route.Optimized,
                    observations: observations, hostOperations: operations);
                (outcome, counters) = (Describe(result), Counters(budget));
                break;
            }
            case Route.Planned:
            {
                using var plans = InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam());
                var (result, budget) = Evaluator.RunCountedObserved(expr, limits, enableOptimizations: false, observations: observations, hostOperations: operations);
                (outcome, counters) = (Describe(result), Counters(budget));
                break;
            }
            default:
            {
                IZeroArgPropertyResultCache cache = route is Route.SuspendingTwin ? new SuspendingAsyncZeroArgPropertyResultCache() : new RunScopedAsyncZeroArgPropertyResultCache();
                var (result, budget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(expr, limits,
                    zeroArgPropertyResultCache: cache, observations: observations, hostOperations: operations));
                (outcome, counters) = (Describe(result), Counters(budget));
                break;
            }
        }
        return new(outcome, counters, log.Calls, attempts.Attempts, observations.LiteralClauseRunSelectionCount, observations.LiteralClauseRunCount);
    }

    // The index and the ordered route agree on everything a program can observe; the recorded attempts of the index are
    // a subsequence of the ordered ones (with their outcomes) and never more.
    private static async Task<(Observed Indexed, Observed Ordered)> AssertAgreement(Route route, string source, EvaluationLimits? limits = null)
    {
        var indexed = await Observe(route, source, ordered: false, limits);
        var ordered = await Observe(route, source, ordered: true, limits);
        var label = $"{route}: {source.Replace("\n", " / ", StringComparison.Ordinal)}";
        Assert.True(ordered.Outcome == indexed.Outcome, $"{label}\n  ordered {ordered.Outcome}\n  indexed {indexed.Outcome}");
        Assert.True(ordered.Counters == indexed.Counters, $"{label}\n  ordered {ordered.Counters}\n  indexed {indexed.Counters}");
        Assert.True(ordered.Effects == indexed.Effects, $"{label}\n  ordered effects {ordered.Effects}\n  indexed effects {indexed.Effects}");
        Assert.Equal(0, ordered.Selections);
        Assert.Equal(0, ordered.Runs);
        AssertSubsequence(ordered.Attempts, indexed.Attempts, label);
        return (indexed, ordered);
    }

    private static void AssertSubsequence(IReadOnlyList<ClauseAttempt> ordered, IReadOnlyList<ClauseAttempt> indexed, string label)
    {
        // Each route parsed its own program, so families are compared by the order in which each trace first meets
        // them. Dispatches are numbered by their first attempt, which both routes record before any demand.
        var orderedKeys = Keys(ordered);
        var indexedKeys = Keys(indexed);
        var next = 0;
        foreach (var attempt in indexedKeys)
        {
            while (next < orderedKeys.Count && orderedKeys[next] != attempt) next++;
            Assert.True(next < orderedKeys.Count, $"{label}: indexed attempt {attempt} has no ordered counterpart in order");
            next++;
        }
        Assert.Equal(ordered.Select(static a => a.Dispatch).Distinct(), indexed.Select(static a => a.Dispatch).Distinct());
    }

    private static List<(int Dispatch, int Family, int Copy, int Clause, ClauseAttemptOutcome Outcome)> Keys(IReadOnlyList<ClauseAttempt> attempts)
    {
        var families = new Dictionary<object, int>(ReferenceEqualityComparer.Instance);
        return attempts.Select(a =>
        {
            object family = a.Family is { } declaration ? declaration : "none";
            if (!families.TryGetValue(family, out var ordinal))
                families.Add(family, ordinal = families.Count);
            return (a.Dispatch, ordinal, a.Copy, a.Clause, a.Outcome);
        }).ToList();
    }

    private static string Table(string name, int count, Func<int, string> key, Func<int, string> body)
        => string.Join("\n", Enumerable.Range(0, count).Select(i => $"{name}({key(i)}) = {body(i)}"));

    private static string Int(int value) => value.ToString(CultureInfo.InvariantCulture);

    private static readonly string Table20 = Table("T", 20, Int, static i => Int(3 * i));

    public static TheoryData<string> Programs => new()
    {
        // Hits, misses through the default, and the misses of a table without a default.
        $"{Table20}\nT(k) = -1\nrange(0, 25).map{{T(x)}}",
        $"{Table20}\nT(3), T(19), T(0)",
        $"{Table20}\nT(25)",
        // A default before the run: the run is never reached.
        $"T(k) = -1\n{Table20}\nT(5), T(25)",
        // Runs split by a structural clause, a repeated name and a mixed head.
        $"{Table("T", 8, Int, Int)}\nT((a, b)) = a + b\n{Table("T", 8, static i => Int(i + 8), Int)}\nT(k) = -1\nT(3), T((4, 5)), T(12), T(40), T([1])",
        $"{Table("G", 6, static i => $"{i}, {i + 1}", Int)}\nG(v, v) = 100 + v\n{Table("G", 6, static i => $"{i + 10}, {i}", Int)}\nG(a, b) = -1\nG(2, 3), G(4, 4), G(12, 2), G(7, 8)",
        $"{Table("G", 4, static i => $"0, {i}", Int)}\nG(0, y) = 50 + y\n{Table("G", 4, static i => $"1, {i}", Int)}\nG(a, b) = -1\nG(0, 2), G(0, 9), G(1, 3), G(1, 1 / 0), G(2, 1 / 0)",
        // Numbers by value: quanta, signed zeros, computed values, 34 digits, specials.
        "T(0) = 'zero'\nT(1) = 'one'\nT(2.5) = 'two and a half'\nT(1234567890123456789012345678901234) = 'big'\nT(k) = 'other'\n"
            + "T(-0), T(0 * -1), T(0.5 * 2), T(10 / 10), T(1.000), T(2.50), T(5 / 2), T(1234567890123456789012345678901234), T(1234567890123456789012345678901235), T(10 ^ 7000), T(10 ^ 7000 - 10 ^ 7000)",
        "T(0.3) = 'p3'\nT(0.1) = 'p1'\nT(k) = 'other'\nT(0.1 + 0.2), T(0.30), T(1 / 10), T(0.1 * 3)",
        // Strings: short keys, the empty string, the longest indexable length and the first that is not.
        $"S('') = 'empty'\nS('a') = 'a'\nS('A') = 'upper'\nS('{Text(63)}') = 'sixty-three'\nS('1') = 'digit'\nS(s) = 'other'\n"
            + $"S(''), S('a'), S('A'), S('b'), S('{Text(63)}'), S('{Text(64)}'), S('{Text(65)}'), S(1), S(1.string)",
        $"S('a') = 1\nS('b') = 2\nS('{Text(64)}') = 3\nS('c') = 4\nS('d') = 5\nS(s) = 0\nS('{Text(64)}'), S('d'), S('{Text(63)}k'), S('a')",
        // Booleans are not numbers, and texts are neither.
        "F(true) = 1\nF(false) = 0\nF(1) = 2\nF('true') = 3\nF(x) = -1\nF(1 > 0), F(0 > 1), F(1), F('true'), F([true]), F((true, false))",
        // Two positions: the second value is demanded only where a clause matches the first.
        $"{Table("G", 16, static c => $"{c / 4}, {c % 4}", Int)}\nG(a, b) = -1\nG(effect(2), effect(3)), G(effect(9), effect(1)), G(effect(1), effect(7)), G(effect(3), 1 / 0)",
        $"{Table("G", 16, static c => $"{c / 4}, {c % 4}", Int)}\nG(a, b) = -1\nG(1, 1 / 0)",
        $"{Table("G", 16, static c => $"{c / 4}, {c % 4}", Int)}\nG(a, b) = -1\nG(9, 1 / 0), G(tick(), tick()), G(tick(), tick()), tick()",
        // Nested lookups: an inner dispatch runs inside the outer one's first demand.
        $"{Table("N", 12, Int, static i => Int((i + 5) % 12))}\nN(k) = 0\nrange(0, 13).map{{N(N(N(x)))}}",
        $"{Table("N", 12, Int, static i => Int((i + 5) % 12))}\nN(N(40))",
        $"{Table("N", 12, Int, static i => Int((i + 5) % 12))}\nN(k) = 0\nN(N(1 / 0))",
        // Recursion through literal base cases, loops over a state table, callbacks and filters.
        $"{Table("D", 30, Int, Int)}\nD(n) = D(n - 1) + 1\nD(75)",
        $"{Table("Next", 10, Int, static i => Int((i * 3 + 1) % 10))}\nStep(s, c) = Next(s), c + 1, c < 25\nStep(0, 0).while",
        $"{Table("Next", 10, Int, static i => Int((i * 7 + 3) % 10))}\nStep(s) = Next(s)\nrepeat(Step(4), 17)",
        $"{Table("Prime", 20, Int, static i => i is 2 or 3 or 5 or 7 or 11 or 13 or 17 or 19 ? "true" : "false")}\nfilter(range(0, 19), Prime), map([3, 4, 5], Prime), count(filter(range(0, 19), {{ Prime(x) }}))",
        // Ticks observe each evaluating demand: a miss after a match, and every argument demanded once.
        $"{Table20}\nT(k) = -1\nT(tick()), T(tick() + 30), T(tick()), tick()",
        // A captured call through a run.
        $"Cap(meta r) = r\n{Table20}\nR = Cap(T(7))\nR.Invoke(), R.Invoke(), R.Arguments[0]",
        // Arguments that read properties: the suspending twin suspends inside the selector's demands.
        $"{Table20}\nT(k) = -1\nK = 7\nJ = K + 30\nT(K), T(J), T(K + 1), T(J - 30)",
        $"{Table("G", 16, static c => $"{c / 4}, {c % 4}", Int)}\nG(a, b) = -1\nA = 2\nB = A + 1\nG(A, B), G(B, A), G(B + 5, A), G(A, B + 5)",
    };

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task Programs_ObserveTheOrderedRoute_OnEveryRoute(string source)
    {
        // Every program prepares a run; all but the one whose default precedes its run select through one.
        var reachesARun = !source.StartsWith("T(k) = -1\n", StringComparison.Ordinal);
        foreach (var route in AllRoutes)
        {
            var (indexed, _) = await AssertAgreement(route, source);
            Assert.True(reachesARun == indexed.Selections > 0, $"{route}: {indexed.Selections} selections through a literal run");
            Assert.True(indexed.Runs > 0, $"{route}: the program should prepare a literal run");
        }
    }

    [Fact]
    public async Task HostBuiltRuns_NaNInfinityAndNullLiterals_ObserveTheOrderedRoute()
    {
        static Algorithm.User Body(Expr output) => new(null, [], [], [], [output]);
        var family = new Algorithm.Conditional(Parent: null, Opens: [], Branches:
        [
            new(new Pattern.LitInt(Decimal128.NaN), Body(new Expr.Num(1))),
            new(new Pattern.LitInt(Decimal128.PositiveInfinity), Body(new Expr.Num(2))),
            new(new Pattern.LitInt(Decimal128.NegativeInfinity), Body(new Expr.Num(3))),
            new(new Pattern.LitInt(D("-0")), Body(new Expr.Num(4))),
            new(new Pattern.LitString(Text(Result.ValueSemanticComparer.StringCharsPerUnit)), Body(new Expr.Num(5))),
            new(new Pattern.LitString("n"), Body(new Expr.Num(6))),
            new(new Pattern.LitString("m"), Body(new Expr.Num(7))),
            new(new Pattern.Bind("k"), Body(new Expr.Num(8))),
        ]);
        Expr Call(Expr argument) => new Expr.Call(new Expr.Resolve("F"), new OutputBundle([argument]));
        Expr Pow(int exponent) => new Expr.Binary(BinaryOp.Pow, new Expr.Num(10), new Expr.Num(exponent));
        var root = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", family, IsPublic: true)],
        [
            Call(new Expr.Binary(BinaryOp.Sub, Pow(7000), Pow(7000))), Call(Pow(7000)), Call(new Expr.Unary(UnaryOp.Minus, Pow(7000))),
            Call(new Expr.Num(0)), Call(new Expr.StringLiteral("m")), Call(new Expr.StringLiteral("z")),
        ]));
        foreach (var ordered in new[] { false, true })
        {
            using var seam = ordered ? OrderedClauseDispatchTestSeam.Activate() : null;
            var observations = new EvaluationObservations();
            var (result, _) = Evaluator.RunCountedObserved(root, observations: observations);
            Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
            // NaN matches NaN, the signed infinities their own literal, 0 matches -0; the 64-unit string literal
            // ends the first run (its comparison is the ordered route's, charged by length) and matches nothing.
            Assert.Equal("(1, 2, 3, 4, 7, 8)", InvocationRouteCorpus.Value(result.Value.Value));
            Assert.Equal(ordered ? 0 : 2, observations.LiteralClauseRunCount);
        }
    }

    // ── 5. step and depth limits refuse at the same operation ──────────────────────────────────────

    public static TheoryData<string> LimitPrograms => new()
    {
        $"{Table20}\nT(k) = -1\nrange(0, 22).map{{T(x)}}.sum",
        $"{Table("G", 16, static c => $"{c / 4}, {c % 4}", Int)}\nG(a, b) = -1\nG(effect(2), effect(3)), G(effect(9), effect(1)), G(1, effect(2))",
        $"{Table("N", 12, Int, static i => Int((i + 5) % 12))}\nN(k) = 0\nrange(0, 5).map{{N(N(N(x)))}}",
    };

    [Theory]
    [MemberData(nameof(LimitPrograms))]
    public async Task EveryStepLimit_RefusesAtTheSameOperation_OnBothRoutes(string source)
    {
        var unlimited = await Observe(Route.Generic, source, ordered: false);
        Assert.StartsWith("ok ", unlimited.Outcome, StringComparison.Ordinal);
        var steps = long.Parse(unlimited.Counters.Split(' ')[0]["steps=".Length..], CultureInfo.InvariantCulture);
        for (var limit = 1L; limit <= steps; limit++)
        {
            foreach (var route in new[] { Route.Generic, Route.ForcedTwin })
                await AssertAgreement(route, source, new EvaluationLimits { MaxSteps = limit });
        }
    }

    [Fact]
    public async Task EveryDepthLimit_RefusesAtTheSameCall_OnBothRoutes()
    {
        var source = $"{Table("D", 12, Int, Int)}\nD(n) = D(n - 1) + 1\nD(30)";
        for (var depth = 1; depth <= 24; depth++)
        {
            foreach (var route in new[] { Route.Generic, Route.Optimized, Route.ForcedTwin })
                await AssertAgreement(route, source, new EvaluationLimits { MaxDepth = depth });
        }
    }

    // ── 6. measured attempts ─────────────────────────────────────────────────────────────────────

    public static TheoryData<int> TableSizes => new() { 2, 3, 8, 64, 512 };

    [Theory]
    [MemberData(nameof(TableSizes))]
    public async Task ATableRead_AttemptsAtMostThreeClausesPerCall_WhereTheOrderedRouteAttemptedEveryEarlierClause(int size)
    {
        // Every key once, then as many misses through the default.
        var source = $"{Table("T", size, Int, Int)}\nT(k) = -1\nrange(0, {2 * size - 1}).map{{T(x)}}.sum";
        var (indexed, ordered) = await AssertAgreement(Route.Generic, source);
        static int Attempts(IReadOnlyList<ClauseAttempt> attempts, int dispatch) => attempts.Count(a => a.Dispatch == dispatch);
        // Key 0 is the first clause, key 1 the second, every other key its run's first clause, the probe and itself; a
        // miss is the first clause, the probe and the default.
        var expected = 1 + 2 + 3 * (size - 2) + 3 * size;
        Assert.Equal(expected, indexed.Attempts.Count);
        Assert.Equal(size * (size + 1) / 2 + size * (size + 1), ordered.Attempts.Count);
        Assert.All(Enumerable.Range(1, 2 * size), dispatch => Assert.InRange(Attempts(indexed.Attempts, dispatch), 1, 3));
        Assert.Equal(2 * size, indexed.Selections);
        Assert.Equal(1, indexed.Runs);
    }

    [Theory]
    [InlineData(2, 8)]
    [InlineData(3, 4)]
    public async Task AWideTableRead_AttemptsAtMostTwiceItsArityPlusOneClausesPerCall(int arity, int side)
    {
        var cells = (int)Math.Pow(side, arity);
        string Key(int c) => string.Join(", ", Enumerable.Range(0, arity).Select(p => Int(c / (int)Math.Pow(side, arity - 1 - p) % side)));
        var call = string.Join(", ", Enumerable.Range(0, arity).Select(p => $"x div {(int)Math.Pow(side, arity - 1 - p)} mod {side}"));
        var source = $"{Table("G", cells, Key, Int)}\nrange(0, {cells - 1}).map{{G({call})}}.sum";
        var (indexed, ordered) = await AssertAgreement(Route.Generic, source);
        Assert.Equal($"ok {cells * (cells - 1) / 2} n=1", indexed.Outcome.Split('\t')[0]);
        Assert.Equal(cells * (cells + 1) / 2, ordered.Attempts.Count);
        Assert.All(indexed.Attempts.GroupBy(static a => a.Dispatch), dispatch => Assert.InRange(dispatch.Count(), 1, 2 * arity + 1));
    }

    // ── 7. cancellation ──────────────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AReadySpreadBeforeACancellingArgument_ObservesCancellationAtTheNextInspectingClause(bool asynchronous)
    {
        const string source = "G(0, 0) = 0\nG(0, 1) = 1\nG(0, 2) = 2\nG([0]*, stop(9))";
        foreach (var ordered in new[] { true, false })
        {
            using var cancellation = new CancellationTokenSource();
            var log = new EffectLog();
            var operations = log.Operations(cancellation);
            var expr = Program(source, operations);
            var attempts = new ClauseAttemptObservations();
            var observations = new EvaluationObservations { ClauseAttempts = attempts };
            using var seam = ordered ? OrderedClauseDispatchTestSeam.Activate() : null;
            var token = cancellation.Token;
            var thrown = asynchronous
                ? await Assert.ThrowsAnyAsync<OperationCanceledException>(() => AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(expr,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), observations: observations, hostOperations: operations, cancellationToken: token)))
                : Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(expr, observations: observations, hostOperations: operations, cancellationToken: token));
            Assert.Equal(token, thrown.CancellationToken);
            Assert.Equal("stop", log.Calls);
            Assert.Equal("1:0:NonMatch 1:1:Pending", Trace(attempts));
        }
    }

    [Fact]
    public void PreparationObservesCancellationWhileScanningHeadsThatCannotFormARun()
    {
        var heads = Heads([new Pattern.Bind("x")]);
        var token = new CancellationToken(canceled: true);
        var thrown = Assert.Throws<OperationCanceledException>(() => Evaluator.PrepareLiteralClauseRuns(heads, token));
        Assert.Equal(token, thrown.CancellationToken);
    }

    [Theory]
    [InlineData(0, "1:0:Matched")]
    [InlineData(1, "1:0:NonMatch 1:1:Pending")]
    [InlineData(7, "1:0:NonMatch 1:1:Pending")]
    [InlineData(40, "1:0:NonMatch 1:1:Pending")]
    public async Task ACancellationRequestedWhileTheFirstValueIsComputed_IsObservedWhereTheOrderedRouteObservesIt(int key, string trace)
    {
        // stop(k) cancels the token and returns normally: the ordered route's next demand observes the request, which
        // is the second clause's (the index replays it); a match on the first clause demands nothing more here.
        var source = $"{Table20}\nT(k) = -1\nT(stop({key})), effect(1)";
        foreach (var route in new[] { Route.Plain, Route.Generic, Route.ForcedTwin })
        {
            foreach (var ordered in new[] { false, true })
            {
                using var cancellation = new CancellationTokenSource();
                var log = new EffectLog();
                var operations = log.Operations(cancellation);
                var expr = Program(source, operations);
                var attempts = new ClauseAttemptObservations();
                var observations = new EvaluationObservations { ClauseAttempts = attempts };
                using var seam = ordered ? OrderedClauseDispatchTestSeam.Activate() : null;
                var token = cancellation.Token;
                var thrown = route switch
                {
                    Route.Plain => Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.Run(expr, operations, null, null, token)),
                    Route.Generic => Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(expr, observations: observations, hostOperations: operations, cancellationToken: token)),
                    _ => await Assert.ThrowsAnyAsync<OperationCanceledException>(() => AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(expr,
                        zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), observations: observations, hostOperations: operations, cancellationToken: token))),
                };
                Assert.Equal(token, thrown.CancellationToken);
                Assert.Equal("stop", log.Calls);
                if (route is not Route.Plain)
                    Assert.Equal(trace, Trace(attempts));
            }
        }
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(19)]
    [InlineData(40)]
    public async Task ACancellationRequestedByTheLastRowsArgument_EndsTheRunAsTheOrderedRouteEndsIt(int key)
    {
        // Nothing follows the call, so the selected body is the run's last work: the outcome — the run's token or a
        // value — is the ordered route's on every route.
        var source = $"{Table20}\nT(k) = -1\nT(stop({key}))";
        foreach (var route in new[] { Route.Plain, Route.Generic, Route.Optimized, Route.ForcedTwin })
        {
            var outcomes = new List<string>();
            foreach (var ordered in new[] { false, true })
            {
                using var cancellation = new CancellationTokenSource();
                var log = new EffectLog();
                var operations = log.Operations(cancellation);
                var expr = Program(source, operations);
                var attempts = new ClauseAttemptObservations();
                var observations = new EvaluationObservations { ClauseAttempts = attempts };
                using var seam = ordered ? OrderedClauseDispatchTestSeam.Activate() : null;
                var token = cancellation.Token;
                string outcome;
                try
                {
                    outcome = route switch
                    {
                        Route.Plain => Describe(Evaluator.Run(expr, operations, null, null, token)),
                        Route.Generic or Route.Optimized => Describe(Evaluator.RunCountedObserved(expr, enableOptimizations: route is Route.Optimized,
                            observations: observations, hostOperations: operations, cancellationToken: token).Result),
                        _ => Describe((await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(expr,
                            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), observations: observations,
                            hostOperations: operations, cancellationToken: token))).Result),
                    };
                }
                catch (OperationCanceledException cancelled)
                {
                    Assert.Equal(token, cancelled.CancellationToken);
                    outcome = "cancelled";
                }
                outcomes.Add($"{outcome} | {log.Calls} | {(route is Route.Plain ? "" : Trace(attempts))}");
            }
            Assert.True(outcomes[0] == outcomes[1], $"{route} key {key}\n  indexed {outcomes[0]}\n  ordered {outcomes[1]}");
        }
    }

    // ── 8. preparation lifetime ──────────────────────────────────────────────────────────────────

    [Fact]
    public void ARunsIndex_IsPreparedOncePerRun_AndHostEditsBetweenRunsAreObserved()
    {
        static Algorithm.User Body(int value) => new(null, [], [], [], [new Expr.Num(value)]);
        var branches = Enumerable.Range(0, 6).Select(static i => new CondBranch(new Pattern.LitInt(i), Body(10 * i))).ToList();
        branches.Add(new CondBranch(new Pattern.Bind("k"), Body(-1)));
        var family = new Algorithm.Conditional(Parent: null, Opens: [], Branches: branches);
        Expr Call(int key) => new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(key)]));
        var root = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", family, IsPublic: true)], [Call(5), Call(8), Call(2)]));

        string RunOnce(out EvaluationObservations observations)
        {
            observations = new EvaluationObservations();
            var (result, _) = Evaluator.RunCountedObserved(root, observations: observations);
            return result.IsOk ? InvocationRouteCorpus.Value(result.Value.Value) : "err " + result.Error.Code;
        }

        Assert.Equal("(50, -1, 20)", RunOnce(out var first));
        Assert.Equal((1L, 1L, 3L), (first.ClauseFamilyPreparationCount, first.LiteralClauseRunCount, first.LiteralClauseRunSelectionCount));

        // Between runs: a literal changes and a clause joins the run.
        branches[5] = new CondBranch(new Pattern.LitInt(8), Body(80));
        branches.Insert(6, new CondBranch(new Pattern.LitInt(5), Body(55)));
        Assert.Equal("(55, 80, 20)", RunOnce(out var second));
        Assert.Equal((1L, 1L), (second.ClauseFamilyPreparationCount, second.LiteralClauseRunCount));

        // A copy that replaces the list is prepared, and indexed, on its own.
        var copy = family with { Branches = [new CondBranch(new Pattern.LitInt(1), Body(1)), new CondBranch(new Pattern.LitInt(2), Body(2))] };
        var both = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", family, IsPublic: true), new Property("G", copy, IsPublic: true)],
            [Call(2), new Expr.Call(new Expr.Resolve("G"), new OutputBundle([new Expr.Num(2)]))]));
        var observations = new EvaluationObservations();
        var (result, _) = Evaluator.RunCountedObserved(both, observations: observations);
        Assert.Equal("(20, 2)", InvocationRouteCorpus.Value(result.Value.Value));
        Assert.Equal((2L, 2L), (observations.ClauseFamilyPreparationCount, observations.LiteralClauseRunCount));
    }

    [Fact]
    public void ADuplicateFamily_IsRefusedBeforeAnyRunIsIndexed()
    {
        static Algorithm.User Body(int value) => new(null, [], [], [], [new Expr.Num(value)]);
        var family = new Algorithm.Conditional(Parent: null, Opens: [], Branches:
            [new(new Pattern.LitInt(1), Body(1)), new(new Pattern.LitInt(2), Body(2)), new(new Pattern.LitInt(D("1.0")), Body(3))]);
        var root = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", family, IsPublic: true)],
            [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(2)]))]));
        var observations = new EvaluationObservations();
        var (result, _) = Evaluator.RunCountedObserved(root, observations: observations);
        Assert.True(result.IsError);
        Assert.Equal(KatLangErrorCode.DuplicateBranchPattern, result.Error.Code);
        Assert.Equal((1L, 0L, 0L), (observations.ClauseFamilyPreparationCount, observations.LiteralClauseRunCount, observations.LiteralClauseRunSelectionCount));
    }

    // ── 9. allocation ────────────────────────────────────────────────────────────────────────────

    [Fact]
    public void ASelection_AllocatesNothing_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        // A 64-clause table over numbers, strings and Booleans, and an 8×8 two-position table, over Ready cells.
        Pattern Literal(int i) => (i % 3) switch { 0 => new Pattern.LitInt(i), 1 => new Pattern.LitString("s" + i), _ => new Pattern.LitBool(i == 2) };
        var single = Evaluator.PrepareLiteralClauseRuns(Heads(Enumerable.Range(0, 62).Select(Literal)), CancellationToken.None)![0]!;
        var pairs = Evaluator.PrepareLiteralClauseRuns(Heads(Enumerable.Range(0, 64).Select(c => Head(new Pattern.LitInt(c / 8), new Pattern.LitInt(c % 8)))), CancellationToken.None)![0]!;
        NeedCell Ready(Result value) => NeedCell.Ready(new(value, 1));
        NeedCell[][] singles = [[Ready(new Result.Atom(0))], [Ready(new Result.Atom(60))], [Ready(new Result.Str("s31"))], [Ready(new Result.Bool(false))],
            [Ready(new Result.Atom(D("3.0")))], [Ready(new Result.Atom(-7))], [Ready(new Result.Str(Text(200)))], [Ready(new Result.ListValue([]))]];
        NeedCell[][] doubles = [[Ready(new Result.Atom(7)), Ready(new Result.Atom(7))], [Ready(new Result.Atom(3)), Ready(new Result.Atom(9))], [Ready(new Result.Atom(9)), Ready(new Result.Atom(0))]];
        var selected = 0L;
        void Round()
        {
            foreach (var supply in singles) selected += Select(single, supply, null).Value;
            foreach (var supply in doubles) selected += Select(pairs, supply, null).Value;
        }
        for (var i = 0; i < 200; i++) Round();

        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < 1000; i++) Round();
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(0, allocated);
        Assert.NotEqual(0, selected);
        GcIsolatedAllocation.Complete();
    }

    [Fact]
    public void ATableRead_AllocatesWhatTheOrderedRouteAllocates_AndItsIndexOnce()
    {
        // The index is the only addition, built once per run; nothing is allocated per call. Its own allocation is
        // measured by building it from the same heads, and the two runs may differ from that by the counter's
        // allocation quantum (~8 KB under a background GC) in either direction, which the bounds allow twice over.
        const int Size = 512;
        var source = $"{Table("T", Size, Int, Int)}\nT(k) = -1\nrange(0, {2 * Size - 1}).map{{T(x)}}.sum";
        var expr = Program(source, null);
        long Best(Func<long> measure)
        {
            for (var i = 0; i < 3; i++) measure();
            var best = long.MaxValue;
            for (var i = 0; i < 5; i++) best = Math.Min(best, measure());
            return best;
        }
        long Run(bool ordered)
        {
            using var seam = ordered ? OrderedClauseDispatchTestSeam.Activate() : null;
            var before = GC.GetAllocatedBytesForCurrentThread();
            var (result, _) = Evaluator.RunCountedObserved(expr);
            var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.True(result.IsOk);
            return allocated;
        }
        var heads = Heads(Enumerable.Range(0, Size).Select(static i => (Pattern)new Pattern.LitInt(i)).Append(new Pattern.Bind("k")));
        var index = Best(() =>
        {
            var before = GC.GetAllocatedBytesForCurrentThread();
            Assert.NotNull(Evaluator.PrepareLiteralClauseRuns(heads, CancellationToken.None));
            return GC.GetAllocatedBytesForCurrentThread() - before;
        });
        var indexed = Best(() => Run(ordered: false));
        var ordered = Best(() => Run(ordered: true));
        Assert.InRange(index, Size * 24, Size * 200);
        Assert.InRange(indexed - ordered - index, -16 * 1024, 16 * 1024);
    }

    // ── 10. the programs the Lean model shares ───────────────────────────────────────────────────

    /// <summary>
    /// The table programs <c>lean/CoreTests/LiteralClauseTables.lean</c> evaluates with the same expected values
    /// (integer, Boolean and string literals, ticks and failures — the shared tier). Lean's family dispatcher is the
    /// ordered clause search; C# selects through the index here, and through the ordered route under the seam.
    /// </summary>
    public static TheoryData<string, string> LeanSharedPrograms => new()
    {
        { $"{Table("T", 16, Int, static i => Int(3 * i))}\nT(k) = 100\n" + string.Join(", ", Enumerable.Range(0, 18).Select(static k => $"T({k})")),
            "ok (0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 100, 100) n=18" },
        { $"{Table("T", 16, Int, static i => Int(3 * i))}\nT(20)", "err NoMatchingBranch" },
        { $"{Table("G", 16, static c => $"{c / 4}, {c % 4}", Int)}\nG(a, b) = 99\nG(2, 3), G(3, 0), G(5, 1 / 0), G(0, 9), G(tick(), tick()), G(tick(), tick()), tick()",
            "ok (11, 12, 99, 99, 6, 99, 5) n=7" },
        { $"{Table("G", 16, static c => $"{c / 4}, {c % 4}", Int)}\nG(a, b) = 99\nG(1, 1 / 0)", "err DivisionByZero" },
        { $"{Table("N", 8, Int, static i => Int((i + 3) % 8))}\nN(N(N(2))), N(N(5))", "ok (3, 3) n=2" },
        { $"{Table("S", 8, static i => $"'k{i}'", Int)}\nS(s) = -1\nS('k5'), S('k'), S(5), S('k7')", "ok (5, -1, -1, 7) n=4" },
        { "F(true) = 1\nF(false) = 2\nF(1) = 3\nF(0) = 4\nF(x) = 5\nF(1 > 0), F(1), F(0 > 1), F(0), F(7)", "ok (1, 3, 2, 4, 5) n=5" },
        { $"{Table("T", 8, Int, Int)}\nT((a, b)) = a * b\n{Table("T", 8, static i => Int(i + 8), static i => Int(i + 8))}\nT(k) = -1\nT(3), T((6, 7)), T(12), T(40)",
            "ok (3, 42, 12, -1) n=4" },
    };

    private sealed class LiteralRunFinder : AstWalker
    {
        public bool Found { get; private set; }

        protected override bool VisitsExplicitParameterDeclarations => false;

        protected override void VisitConditionalAlgorithm(Algorithm.Conditional algorithm)
        {
            Found |= Evaluator.PrepareLiteralClauseRuns(Heads(algorithm.Branches.Select(static b => b.Pattern)), CancellationToken.None) is not null;
            base.VisitConditionalAlgorithm(algorithm);
        }
    }

    /// <summary>
    /// The Lean-compared corpora — whose C# outcomes the generated Lean modules pin and <c>lake build</c> checks against
    /// the Lean model — include programs that now select through a literal run. Each of them, run with the index and on
    /// the ordered route, has the same outcome and counters, so the existing Lean comparison of those programs checks
    /// the indexed route.
    /// </summary>
    [Fact]
    public async Task TheLeanComparedCorpora_SelectThroughLiteralRuns_AsTheOrderedRouteSelects()
    {
        var sources = LanguageSpec.LanguageSpecCorpus.AllCases()
            .Where(static c => c.IsLeanRepresentable && c.Outcome is not LanguageSpec.SpecOutcome.ParseError)
            .Select(static c => ("spec/" + c.Id, c.Source))
            .Concat(SemanticExplorerCorpus.AllCases().Where(static c => c.LeanProgram is not null).Select(static c => ("explorer/" + c.Id, c.Source)));
        var selecting = new List<string>();
        foreach (var (id, source) in sources)
        {
            var parsed = Parser.Parse(source);
            if (parsed.HasErrors) continue;
            var finder = new LiteralRunFinder();
            finder.VisitAlgorithm(parsed.Root);
            if (!finder.Found) continue;
            var (indexed, _) = await AssertAgreement(Route.Generic, source);
            if (indexed.Selections > 0) selecting.Add(id);
        }
        // The 2026-11-22 corpora; a program may join the list, none may leave it unnoticed.
        string[] known =
        [
            "spec/boolean-predicates-and-patterns", "spec/loop-step-family-no-match-is-ordinary",
            "spec/conditional-branch-inline-open-does-not-shadow-an-enclosing-open-in-sibling-branches",
            "spec/string-literal-pattern-selects-a-clause", "explorer/special__loopStepFamilyNoMatch",
            "explorer/special__aliasOfUnnameableFamily", "explorer/special__huntA12Edge2G06FamilyBool",
        ];
        Assert.True(known.All(selecting.Contains), "Lean-compared programs selecting through a literal run: " + string.Join(", ", selecting));
    }

    [Theory]
    [MemberData(nameof(LeanSharedPrograms))]
    public async Task TheProgramsLeanShares_ComputeLeansValues_OnEveryRoute(string source, string expected)
    {
        foreach (var route in AllRoutes)
        {
            var (indexed, _) = await AssertAgreement(route, source);
            if (expected.StartsWith("err ", StringComparison.Ordinal))
                Assert.StartsWith(expected + " ", indexed.Outcome, StringComparison.Ordinal);
            else if (route is Route.Plain)
                Assert.Equal(expected.Split(" n=")[0], indexed.Outcome);
            else
                Assert.Equal(expected, indexed.Outcome);
        }
    }
}
