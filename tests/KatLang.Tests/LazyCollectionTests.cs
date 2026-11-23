using KatLang.Evaluation;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// LISTS AND PIPELINES ARE EVALUATED ON DEMAND (issue #204, November 2026; Lean first:
/// <c>Result.deferred</c> / <c>Result.pendingList</c> and § "Lazy collections" of <c>KatLang.lean</c>,
/// C# <c>Evaluator.LazyLists.cs</c>). A list literal captures one deferred VALUE computation per ordinary
/// written element (explicit spreads are formed with the list); <c>map</c> keeps positions and runs its mapper
/// on the first read of a position; <c>filter</c> discovers its matches in source order and never inspects a
/// candidate twice; <c>take</c> is a prefix sharing its source's state. A consumer reads what it needs:
/// <c>count</c> the cardinality, <c>first</c> / selection the positions they name, a pattern the kind and
/// the cardinality before any field; a spread, a strict builtin, evaluator equality and the run result read
/// the level or the whole value they are about.
/// <para>Unless a test names its route, every program runs on the six established routes
/// (<see cref="SixRouteAgreement"/>: the synchronous and asynchronous engines, the engine's genuinely
/// suspending asynchronous twin, the generic and the optimized evaluator, and the forced twin), which must
/// agree on the value, every error (code, message, span) and the exact host-call log. Lean:
/// <c>CoreTests/LazyCollections.lean</c>; spec cases <c>lazy-list-*</c>, <c>lazy-map-*</c>,
/// <c>lazy-filter-*</c>.</para>
/// </summary>
public sealed class LazyCollectionTests
{
    private static Task<SixRouteAgreement.Observation> RunAsync(string source)
        => SixRouteAgreement.OnEveryRouteAsync(source);

    private static string Outcome(SixRouteAgreement.Observation observation) => observation.Kind switch
    {
        "ok" => $"ok {observation.Value}",
        "err" => $"err {observation.Errors[0][..observation.Errors[0].IndexOf(':')]}",
        _ => observation.Kind,
    };

    private static async Task Expect(string source, string expected, string hostCalls)
    {
        var observation = await RunAsync(source);
        Assert.Equal(expected, Outcome(observation));
        Assert.Equal(hostCalls, string.Join(",", observation.HostCalls));
    }

    // ── 1. The issue's examples and the sharing pins ──────────────────────────────────────────

    /// <summary>source, expected outcome, expected host-call log.</summary>
    public static TheoryData<string, string, string> AcceptanceCases() => new()
    {
        { "[10, 1 / 0][0]", "ok 10", "" },
        { "[1, 2].map{if(n == 1, 10, 1 / 0)}.first", "ok 10", "" },
        { "[1, 0].filter{1 / n > 0}.take(1)", "ok L[1]", "" },
        // Sharing is per position per list instance; effects follow the order positions are read in.
        { "L = [tick(), tick(), tick()]\nL[2, 0, 2], L[0], tick()", "ok S[S[1, 2, 1], 2, 3]", "" },
        // The run's output is assembled first and read afterwards, left to right.
        { "L = [tick()]\nL, tick()", "ok S[L[2], 1]", "" },
        // `map` reads the source item first, then projects its mapper.
        { "first(map([1 / 0], 7))", "err DivisionByZero", "" },
        // Counting a map of known length reads no element and projects no mapper.
        { "count(map([1 / 0, 2], 7))", "ok 2", "" },
    };

    [Theory]
    [MemberData(nameof(AcceptanceCases))]
    public Task TheIssueExamples(string source, string expected, string hostCalls) => Expect(source, expected, hostCalls);

    // ── 2. List literals ──────────────────────────────────────────────────────────────────────

    public static TheoryData<string, string, string> LiteralCases() => new()
    {
        // The cardinality is known when the literal is built: nothing is read.
        { "[trace(1), trace(2)].count", "ok 2", "" },
        { "[trace(1), trace(2)][1]", "ok 2", "trace(2)" },
        { "[trace(1), trace(2)].last", "ok 2", "trace(2)" },
        { "[trace(1), trace(2)].first", "ok 1", "trace(1)" },
        // An explicit spread is formed with the list; the ordinary elements around it stay deferred.
        { "[trace(1), (trace(2), trace(3))*, trace(4)].count", "ok 4", "trace(2),trace(3)" },
        { "[trace(1), (trace(2), trace(3))*][0]", "ok 1", "trace(2),trace(3),trace(1)" },
        // One list instance shares each position; two evaluations build two instances.
        { "X = [trace(1)]\nX[0], X[0]", "ok S[1, 1]", "trace(1)" },
        { "F = [trace(1)]\nF()[0], F()[0]", "ok S[1, 1]", "trace(1),trace(1)" },
        // An element is evaluated in the literal's own environment.
        { "F(a) = [a + 1, a / 0]\nF(4)[0]", "ok 5", "" },
        // A parameter element is the parameter's own computation: one completion for both.
        { "F(a) = [a, a][1] + a\nF(trace(3))", "ok 6", "trace(3)" },
        // Nested lists are positions like any other.
        { "[[1 / 0], 2][1]", "ok 2", "" },
        { "[[1 / 0], 2][0].count", "ok 1", "" },
        { "[[trace(1), trace(2)], trace(3)]", "ok L[L[1, 2], 3]", "trace(1),trace(2),trace(3)" },
        { "[]", "ok L[]", "" },
        { "[()]", "ok L[S[]]", "" },
    };

    [Theory]
    [MemberData(nameof(LiteralCases))]
    public Task AListLiteral_DefersItsOrdinaryElements(string source, string expected, string hostCalls)
        => Expect(source, expected, hostCalls);

    // ── 3. map ────────────────────────────────────────────────────────────────────────────────

    public static TheoryData<string, string, string> MapCases() => new()
    {
        { "[trace(1), trace(2)].map{x * 10}[1]", "ok 20", "trace(2)" },
        { "[1, 2, 3].map{trace(x)}.count", "ok 3", "" },
        { "[1, 2, 3].map{trace(x)}.last", "ok 3", "trace(3)" },
        // A mapped position is computed once per list instance.
        { "M = [1, 2, 3].map{trace(x)}\nM[1], M[1], M.count", "ok S[2, 2, 3]", "trace(2)" },
        // An empty or unread stage never projects its callback.
        { "map([], 7)", "ok L[]", "" },
        { "map([1], 7).count", "ok 1", "" },
        { "map([1], 7)", "err NotAnAlgorithm", "" },
        { "map([trace(1)], 7).first", "err NotAnAlgorithm", "trace(1)" },
        // A sequence or a scalar collection is mapped through the same positions.
        { "(trace(1), trace(2)).map{x + 1}.first", "ok 2", "trace(1),trace(2)" },
        { "map(5, {x + 1})", "ok L[6]", "" },
        // Named, dotted, aliased and forwarded reads share the one stage.
        { "Twice(x) = trace(x) * 2\nM = map([1, 2], Twice)\nA = M\nM.first, A.first, A[1]", "ok S[2, 2, 4]", "trace(1),trace(2)" },
        { "Twice(x) = trace(x) * 2\nPass(v) = v[0]\nPass([1, 2].map(Twice)), 0", "ok S[2, 0]", "trace(1)" },
        // A pipeline across a call boundary.
        { "Stage(xs) = xs.map{trace(x) + 1}\nStage([1, 2, 3])[2]", "ok 4", "trace(3)" },
    };

    [Theory]
    [MemberData(nameof(MapCases))]
    public Task Map_PreservesPositions_AndRunsItsMapperOnFirstUse(string source, string expected, string hostCalls)
        => Expect(source, expected, hostCalls);

    // ── 4. filter ─────────────────────────────────────────────────────────────────────────────

    public static TheoryData<string, string, string> FilterCases() => new()
    {
        // Matches are discovered in source order, and only as far as the consumer needs.
        { "[trace(1), trace(2), trace(3)].filter{x > 1}.first", "ok 2", "trace(1),trace(2)" },
        { "[trace(1), trace(2), trace(3)].filter{x > 1}.count", "ok 2", "trace(1),trace(2),trace(3)" },
        // A later discovery resumes after the candidates already inspected.
        { "F = [trace(1), trace(2), trace(3)].filter{x > 1}\nF.first, F.count, F.first", "ok S[2, 2, 2]", "trace(1),trace(2),trace(3)" },
        { "F = [1, 2, 3].filter{trace(x) > 1}\nF.first, F[1], F.count", "ok S[2, 3, 2]", "trace(1),trace(2),trace(3)" },
        // An ordinary failure stays at the scan's frontier: the matches before it remain readable.
        { "[1, 0, 2].filter{1 / x > 0}.take(1)", "ok L[1]", "" },
        { "[1, 0, 2].filter{1 / x > 0}.take(2)", "err DivisionByZero", "" },
        { "F = [1, 0, 2].filter{1 / x > 0}\nF.first, F.take(1), F.first", "ok S[1, L[1], 1]", "" },
        { "F = [1, 0, 2].filter{1 / x > 0}\nF.first, F.count", "err DivisionByZero", "" },
        // An empty or unread stage never projects its callback; a scan projects it at its first candidate.
        { "filter([], 7)", "ok L[]", "" },
        { "[1].filter(7).take(0)", "ok L[]", "" },
        { "[1].filter(7).count", "err NotAnAlgorithm", "" },
        { "[1, 2].filter{x}", "err TypeMismatch", "" },
        // A candidate's value is read before its predicate runs.
        { "[1 / 0, 2].filter{true}.count", "err DivisionByZero", "" },
        // Alternating stages scan together, one candidate at a time.
        { "[1, 2, 3, 4, 5, 6].filter{x > 1}.map{x * 10}.filter{x > 30}.take(2)", "ok L[40, 50]", "" },
        { "[trace(1), trace(2), trace(3), trace(4)].filter{x > 1}.map{x * 10}.first", "ok 20", "trace(1),trace(2)" },
        { "[trace(1), trace(2), trace(3)].map{x * 10}.filter{x > 10}.first", "ok 20", "trace(1),trace(2)" },
        { "[1, 2, 3, 4].map{trace(x)}.filter{x > 2}.map{x + 100}.take(1)", "ok L[103]", "trace(1),trace(2),trace(3)" },
        // The predicate receives the source index of its candidate.
        { "[5, 6, 7].filter{x > 5}.filter{x > 6}.first", "ok 7", "" },
    };

    [Theory]
    [MemberData(nameof(FilterCases))]
    public Task Filter_DiscoversItsMatchesInSourceOrder(string source, string expected, string hostCalls)
        => Expect(source, expected, hostCalls);

    // ── 5. take, first, last, count and selection ─────────────────────────────────────────────

    public static TheoryData<string, string, string> ConsumerCases() => new()
    {
        // `take` validates its count before any position; a non-positive count reads nothing.
        { "[trace(1), trace(2)].take(0)", "ok L[]", "" },
        { "[trace(1), trace(2)].take(-3)", "ok L[]", "" },
        { "[trace(1), trace(2)].take(1)", "ok L[1]", "trace(1)" },
        { "[1, 2, 3].take(99)", "ok L[1, 2, 3]", "" },
        { "[1 / 0].take('a')", "err TypeMismatch", "" },
        { "[1 / 0].take(1 / 0)", "err DivisionByZero", "" },
        { "[1 / 0, 2].take(2).count", "ok 2", "" },
        // A prefix shares its source's positions.
        { "L = [tick(), tick()]\nL.take(1), L[0], tick()", "ok S[L[1], 1, 2]", "" },
        { "L = [tick(), tick()]\nP = L.take(1)\nP[0], L[0], tick()", "ok S[1, 1, 2]", "" },
        // A full prefix inspects no further candidate.
        { "[trace(1), trace(2), trace(3)].filter{x > 0}.take(2)", "ok L[1, 2]", "trace(1),trace(2)" },
        { "[1, 2, 1 / 0].filter{x > 0}.take(2).count", "ok 2", "" },
        // `first`, `last` and `count` over an empty list.
        { "[1].filter{x > 9}.first", "err BadIndex", "" },
        { "[1].filter{x > 9}.last", "err BadIndex", "" },
        { "[1].filter{x > 9}.count", "ok 0", "" },
        // Selection validates and reads its selectors in written order.
        { "[trace(1), trace(2), trace(3)][2, 0]", "ok S[3, 1]", "trace(3),trace(1)" },
        { "[1, 1 / 0][5]", "err BadIndex", "" },
        { "[1 / 0, 2][0, 'a']", "err DivisionByZero", "" },
        { "[1 / 0, 2]['a', 0]", "err TypeMismatch", "" },
        { "[1 / 0, 2][1, 9]", "err BadIndex", "" },
        { "[1, 2, 3].filter{x > 1}[1]", "ok 3", "" },
        { "[1, 2, 3].filter{x > 1}[2]", "err BadIndex", "" },
        { "[trace(1)].filter{x > 0}[2147483647]", "err BadIndex", "trace(1)" },
        { "[1, 0].filter{1 / x > 0}[2147483648]", "err DivisionByZero", "" },
        { "[trace(1), trace(2), trace(3)].filter{x > 0}[1, 0]", "ok S[2, 1]", "trace(1),trace(2)" },
        { "[trace(1), trace(2)][]", "ok S[]", "" },
    };

    [Theory]
    [MemberData(nameof(ConsumerCases))]
    public Task AConsumer_ReadsOnlyThePositionsItNeeds(string source, string expected, string hostCalls)
        => Expect(source, expected, hostCalls);

    // ── 6. Patterns and deconstruction ────────────────────────────────────────────────────────

    public static TheoryData<string, string, string> PatternCases() => new()
    {
        // Kind and cardinality are checked before any field; a name is bound to its position.
        { "P([a, b]) = 7\nP([trace(1), trace(2)])", "ok 7", "" },
        { "P([a, b]) = b\nP([trace(1), trace(2)])", "ok 2", "trace(2)" },
        { "P([a, b]) = a + a\nP([trace(1), trace(2)])", "ok 2", "trace(1)" },
        { "P([a, b]) = a\nP([1 / 0])", "err ArityMismatch", "" },
        { "P([a]) = 1\nP(x) = 2\nP([1 / 0, 2])", "ok 2", "" },
        // A scalar literal rejects a list by kind without scanning it.
        { "P(0) = 1\nP(x) = 2\nP([1 / 0])", "ok 2", "" },
        { "P(0) = 1\nP(x) = 2\nP([1].filter{1 / 0 > 0})", "ok 2", "" },
        // The empty-list pattern may need discovery.
        { "P([]) = 1\nP(x) = 2\nP([1].filter{x > 9})", "ok 1", "" },
        { "P([]) = 1\nP(x) = 2\nP([trace(1)].filter{x > 0})", "ok 2", "trace(1)" },
        // A collecting binding keeps the original positions.
        { "P([a, *rest]) = rest.count\nP([1, 1 / 0, 1 / 0])", "ok 2", "" },
        { "P([a, *rest]) = rest[1]\nP([trace(1), trace(2), trace(3)])", "ok 3", "trace(3)" },
        // A nested pattern opens only the position it names.
        { "P([[a, b], c]) = b\nP([[trace(1), trace(2)], trace(3)])", "ok 2", "trace(2)" },
        // A literal field is a field: it is read after the cardinality is known.
        { "P([0, b]) = 1\nP(x) = 2\nP([trace(5), trace(6)])", "ok 2", "trace(5)" },
        // Deconstruction binds positions too.
        { "a, b = [trace(1), 1 / 0]\na", "ok 1", "trace(1)" },
        { "a, b = [trace(1), trace(2)].map{x * 10}\nb", "ok 20", "trace(2)" },
        // A pattern-bound position is a value: it carries no callable identity.
        // A repeated name compares whole values.
        { "P(x, x) = x\nP([1 + 1], [2])", "ok L[2]", "" },
        { "P(x, x) = 1\nP(x, y) = 2\nP([trace(1)], [trace(2)])", "ok 2", "trace(1),trace(2)" },
    };

    [Theory]
    [MemberData(nameof(PatternCases))]
    public Task APattern_ChecksKindAndCardinalityBeforeItsFields(string source, string expected, string hostCalls)
        => Expect(source, expected, hostCalls);

    // ── 7. Spread, strict builtins, equality, the run result and host arguments ───────────────

    public static TheoryData<string, string, string> WholeValueCases() => new()
    {
        // An explicit spread reads the level it opens, in order, and supplies values.
        { "F(*xs) = xs.count\nF([trace(1), trace(2)]*)", "ok 2", "trace(1),trace(2)" },
        { "F(*xs) = xs[1]\nF([trace(1), trace(2)].filter{x > 0}*)", "ok 2", "trace(1),trace(2)" },
        { "[[trace(1)], trace(2)]*", "ok S[L[1], 2]", "trace(2),trace(1)" },
        // A strict collection builtin reads its positions in order.
        { "sum([trace(1), trace(2)])", "ok 3", "trace(1),trace(2)" },
        { "[trace(3), trace(1)].order", "ok L[1, 3]", "trace(3),trace(1)" },
        { "skip([trace(1), trace(2)], 1)", "ok L[2]", "trace(1),trace(2)" },
        { "contains([[trace(1)], 2], [1])", "ok true", "trace(1)" },
        { "distinct([[trace(1)], [trace(1)]]).count", "ok 1", "trace(1),trace(1)" },
        { "atoms([[trace(1)], trace(2)])", "ok L[1, 2]", "trace(1),trace(2)" },
        // `reduce` obtains the complete collection first; its accumulators stay lazy.
        { "Pick(item, acc) = item\nreduce([trace(1), trace(2)], Pick, 1 / 0)", "ok 2", "trace(1),trace(2)" },
        // Evaluator equality reads both operands whole, the left one first.
        { "[trace(1)] == [trace(2)]", "ok false", "trace(1),trace(2)" },
        { "[1, 1 / 0] == [2, 3]", "err DivisionByZero", "" },
        { "[trace(1), [trace(2)]] != [1, [2]]", "ok false", "trace(1),trace(2)" },
        // The run result is read left to right, depth first, after the output is assembled.
        { "[trace(1), [trace(2), trace(3)]], trace(4)", "ok S[L[1, L[2, 3]], 4]", "trace(4),trace(1),trace(2),trace(3)" },
        { "[1, 1 / 0]", "err DivisionByZero", "" },
        // A host operation receives a concrete argument, read where the operation is called.
        { "trace([1 + 1, 2])", "ok L[2, 2]", "trace(L[2, 2])" },
        { "trace([trace(1)].map{x + 1})", "ok L[2]", "trace(1),trace(L[2])" },
    };

    [Theory]
    [MemberData(nameof(WholeValueCases))]
    public Task AWholeValueConsumer_ReadsEveryPositionInOrder(string source, string expected, string hostCalls)
        => Expect(source, expected, hostCalls);

    // ── 8. Diagnostics read nothing ───────────────────────────────────────────────────────────

    [Fact]
    public async Task ADiagnostic_NamesAListWithoutReadingIt()
    {
        var literal = await RunAsync("[1, trace(2)] + 1");
        Assert.Equal("err TypeMismatch", Outcome(literal));
        Assert.Empty(literal.HostCalls);
        Assert.Contains("a list value with 2 elements: [1, <deferred>]", literal.Errors[0], StringComparison.Ordinal);

        var scan = await RunAsync("[trace(1)].filter{x > 0} + 1");
        Assert.Equal("err TypeMismatch", Outcome(scan));
        Assert.Empty(scan.HostCalls);
        Assert.Contains("a list value whose elements are not yet evaluated", scan.Errors[0], StringComparison.Ordinal);
    }

    [Fact]
    public async Task ADeferredStep_ReportsUnderTheCallThatBuiltItsStage()
    {
        // The stage is built by `filter` and read by `count`: the predicate's failure keeps the frame and the
        // position the `filter` call gave it, under the consumer's own frame.
        var observation = await RunAsync("count(filter([1, 2], {x}))");
        Assert.Equal("err TypeMismatch", Outcome(observation));
        Assert.Contains("while evaluating call to count: while evaluating call to filter:", observation.Errors[0], StringComparison.Ordinal);
        Assert.Contains("filter predicate result must be a Boolean", observation.Errors[0], StringComparison.Ordinal);

        var mapped = await RunAsync("[1, 2].map{x / 0}.first");
        Assert.Equal("err DivisionByZero", Outcome(mapped));
        Assert.Contains("while evaluating dotCall .map of [1, 2]", mapped.Errors[0], StringComparison.Ordinal);
    }

    // ── 9. Cycles ─────────────────────────────────────────────────────────────────────────────

    [Theory]
    // A position that reads its own list's position.
    [InlineData("L = [L[0]]\nL")]
    // A list that holds itself: building it reads nothing, reading it whole never ends.
    [InlineData("L = [L]\nL")]
    [InlineData("L = [1, [L]]\nL == L")]
    // A predicate that needs the scan it is part of.
    [InlineData("S = [1].filter{S.count >= x}\nS")]
    // A mapped position that reads itself.
    [InlineData("M = [1].map{x + M[0]}\nM")]
    public async Task ADemandCycle_IsReported_NotLoopedOn(string source)
        => Assert.Equal("err DemandCycle", Outcome(await RunAsync(source)));

    [Fact]
    public async Task ASelfContainingList_IsUsableWhereItIsNotReadWhole()
    {
        await Expect("L = [L]\nL.count", "ok 1", "");
        await Expect("L = [1, L]\nL[0], L[1].count", "ok S[1, 2]", "");
    }

    // ── 10. Stack safety ──────────────────────────────────────────────────────────────────────

    [Fact]
    public async Task DeepNesting_IsBuiltReadAndComparedWithoutNativeRecursion()
    {
        await Expect("W(x) = [x]\nA = W(1).repeat(4000)\nA.count", "ok 1", "");
        await Expect("W(x) = [x]\nA = W(1).repeat(4000)\nB = W(1).repeat(4000)\nA == B", "ok true", "");
        await Expect("W(x) = [x]\nA = W(1).repeat(4000)\natoms(A)", "ok L[1]", "");
    }

    [Theory]
    // A loop that maps its own list every round stacks one stage per round: the top position's
    // step reads the position below it, and so on down. Counting such a list asks no stage.
    [InlineData("Step(xs) = xs.map{x + 1}\nrepeat(Step([0]), 6000).first", "ok 6000")]
    [InlineData("Step(xs) = xs.map{x + 1}\nrepeat(Step([0, 5]), 6000)", "ok L[6000, 6005]")]
    [InlineData("Step(xs) = xs.map{x + 1}\nrepeat(Step([0, 5]), 6000).count", "ok 2")]
    [InlineData("Step(xs) = xs.map{x + 1}.take(2)\nrepeat(Step([0, 5, 9]), 6000).last", "ok 6005")]
    // The same pipeline over a scan, and under one.
    [InlineData("Step(xs) = xs.map{x + 1}\nrepeat(Step([0, 5].filter{x > 1}), 6000)", "ok L[6005]")]
    [InlineData("Step(xs) = xs.map{x + 1}\nrepeat(Step([0, 5]), 6000).filter{x > 6000}.count", "ok 1")]
    // A failing position deep in the pipeline is the failure of every position above it.
    [InlineData("Step(xs) = xs.map{x + 1}\nrepeat(Step([1 / 0]), 6000).first", "err DivisionByZero")]
    [InlineData("Step(xs) = xs.map{x + 1}\nrepeat(Step([1 / 0, 2]), 6000).last", "ok 6002")]
    public async Task APipelineStackedAtRunTime_IsReadWithoutNativeRecursionPerStage(string source, string expected)
        => await Expect(source, expected, "");

    [Fact]
    public async Task ScansStackedAtRunTime_AreFoundWithoutCrashingTheHost()
    {
        // A scan over a scan asks the scan below for its next position. A moderate height is read.
        await Expect("Step(xs) = xs.filter{x >= 0}\nrepeat(Step([0, 1]), 100).count", "ok 2", "");
        await Expect("Step(xs) = xs.filter{x >= 0}.map{x + 1}\nrepeat(Step([0, 1]), 100)", "ok L[100, 101]", "");
    }

    [Theory]
    // A result that nests itself forever: every level is a fresh invocation that returns its list
    // at once, so no call ever nests. Reading it whole ends at the recursion limit, as the same
    // program did when `map` ran its callback itself — through a callback and through a loop step.
    [InlineData("F(x) = [x].map(F)\nF(1)", "err EvaluationDepthExceeded")]
    [InlineData("F(x) = [repeat(F(x), 1)]\nF(1)", "err EvaluationDepthExceeded")]
    [InlineData("F(x) = [x].map(F)\nF(1) == F(1)", "err EvaluationDepthExceeded")]
    // Building or counting such a list reads nothing.
    [InlineData("F(x) = [x].map(F)\nF(1).count", "ok 1")]
    [InlineData("F(x) = [x].map(F)\nF(1)[0][0][0].count", "ok 1")]
    // A list built by reading a list built by reading a list: admitted up to the recursion limit…
    [InlineData("Nest(n) = if(n == 0, [7], [Nest(n - 1)])\natoms(Nest(100))", "ok L[7]")]
    [InlineData("Nest(n) = if(n == 0, [7], [Nest(n - 1)])\natoms(Nest(200))", "err EvaluationDepthExceeded")]
    // …while a structure of any depth that was built BEFORE it is read is not such a chain.
    [InlineData("W(x) = [x]\natoms(W(5).repeat(4000))", "ok L[5]")]
    [InlineData("Cons(l, n) = [n * 2, l], n + 1\natoms(repeat(Cons([], 0), 3000)).count", "ok 3001")]
    public async Task AResultThatKeepsBuildingListsWhileItIsRead_EndsAtTheRecursionLimit(string source, string expected)
        => await Expect(source, expected, "");

    // ── 11. Limits, cancellation ──────────────────────────────────────────────────────────────

    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static Evaluator.LazyList Positions(string source, Evaluator.EvalCtx ctx)
    {
        var result = Evaluator.EvalCounted(Program(source), ctx, []);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        return Assert.IsAssignableFrom<Evaluator.LazyList>(Assert.IsType<Result.ListValue>(result.Value.Value).Lazy);
    }

    [Fact]
    public async Task Map_AllocatesPositionStorageOnlyForTheIndicesRead()
    {
        var ctx = Evaluator.EvalCtx.Empty with { CallStack = [BuiltinRegistry.CreateRuntimePreludeAlgorithm()] };
        var known = Positions("range(1, 16384).map{x + 1}", ctx);
        known.Slot(0);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var last = known.Slot(16383);
        var sparseBytes = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Same(last, known.Slot(16383));
        Assert.True(sparseBytes < 32 * 1024, $"One distant mapped position allocated {sparseBytes} bytes.");

        var pending = Positions("range(1, 512).filter{x > 0}.map{x + 1}", ctx);
        long allocated = 0;
        for (var index = 0; index < 512; index++)
        {
            Assert.Null(await pending.Discover(index + 1, asynchronous: false));
            before = GC.GetAllocatedBytesForCurrentThread();
            pending.Slot(index);
            allocated += GC.GetAllocatedBytesForCurrentThread() - before;
        }

        // Includes each mapped position and its need cell. Copying the growing prefix at
        // each discovery would allocate over 1 MiB for array references alone.
        Assert.True(allocated < 512 * 1024, $"Caching 512 discovered mapped positions allocated {allocated} bytes.");
    }

    [Fact]
    public async Task AFailedFrontierKeepsItsPrefixAndDoesNotRetryThePredicate()
    {
        var ctx = Evaluator.EvalCtx.Empty with { CallStack = [BuiltinRegistry.CreateRuntimePreludeAlgorithm()] };
        var positions = Positions("[1, -1, 0].filter{tick() * (1 / x) > 0}", ctx);
        var failure = await positions.Discover(2, asynchronous: false);
        Assert.Equal(KatLangErrorCode.DivisionByZero, failure?.Code);
        Assert.Equal(3, ctx.Budget.TickCount);
        Assert.Null(await positions.Discover(1, asynchronous: false));
        Assert.Equal(new Result.Atom(1), positions.Slot(0));
        Assert.Same(failure, await positions.Discover(2, asynchronous: false));
        Assert.Equal(3, ctx.Budget.TickCount);

        var terminal = ctx.Budget.RetainTerminal(new EvalError.EvaluationDepthExceeded(1));
        Assert.Same(terminal, await positions.Discover(1, asynchronous: false));
        Assert.Same(terminal, await positions.Discover(2, asynchronous: false));
    }

    [Fact]
    public async Task OverlappingReadersJoinTheSameFilterVerdictAndMappedPosition()
    {
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.CreateAsync("gate", async (_, _) =>
        {
            Interlocked.Increment(ref calls);
            await release.Task;
            return new Result.Atom(2);
        }));
        var parsed = Parser.Parse("[gate()].map{x + 1}.filter{x > 0}", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        var budget = EvaluationBudget.Create(null, operations);
        budget.MarkAsynchronousRun();
        var ctx = Evaluator.EvalCtx.Empty with
        {
            Budget = budget,
            CallStack = [operations.RuntimePreludeAlgorithm],
            Services = Evaluator.RunServices.Unconfigured with
            {
                EnableLoopOptimization = false,
                EnableSequencePipelineOptimization = false,
                ZeroArgPropertyResultCache = new KatLang.Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache(),
            },
        };
        var staged = Evaluator.EvalCounted(new Expr.AlgorithmExpr(parsed.Root), ctx, []);
        Assert.True(staged.IsOk);
        var positions = Assert.IsAssignableFrom<Evaluator.LazyList>(Assert.IsType<Result.ListValue>(staged.Value.Value).Lazy);
        var first = positions.Discover(1, asynchronous: true);
        var second = positions.Discover(1, asynchronous: true);
        try
        {
            Assert.False(first.IsCompleted);
            Assert.False(second.IsCompleted);
            Assert.Equal(1, Volatile.Read(ref calls));
        }
        finally
        {
            release.SetResult();
        }

        Assert.Null(await first);
        Assert.Null(await second);
        var position = Assert.IsType<NeedCell>(positions.Slot(0));
        var value = await position.DemandAsync();
        Assert.True(value.IsOk);
        Assert.Equal(new Result.Atom(3), value.Value.Value);
        Assert.Equal(1, calls);
    }

    [Fact]
    public async Task ACollectionLimit_IsATerminalRefusal_WhenAScanIsCompleted()
    {
        var ctx = Evaluator.EvalCtx.Empty with
        {
            CallStack = [BuiltinRegistry.CreateRuntimePreludeAlgorithm()],
            Budget = EvaluationBudget.Create(new EvaluationLimits { MaxMaterializedItems = 3 }),
        };
        var positions = Positions("[1, 2, 3].filter{tick() + x > 0}", ctx);
        Assert.Null(await positions.Discover(3, asynchronous: false));
        Assert.Equal(3, ctx.Budget.TickCount);
        Assert.Equal(3, ctx.Budget.MaterializedItems);

        var refused = await positions.Discover(4, asynchronous: false);
        Assert.Equal(KatLangErrorCode.MaterializationLimitExceeded, refused?.Code);
        Assert.False(positions.IsExhausted);
        var cached = await positions.Discover(1, asynchronous: false);
        Assert.Equal(KatLangErrorCode.MaterializationLimitExceeded, cached?.Code);
        Assert.Equal(3, ctx.Budget.MaterializedItems);
    }

    [Fact]
    public void AStepLimit_ReachedWhileTheResultIsRead_IsTheRunsFailure()
    {
        // Counting the mapped list invokes no mapper; reading it invokes ten. The smallest step
        // budget that counts it is therefore spent while the run's result is read.
        const string mapped = "Slow(x) = x + 1\n[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map(Slow)";
        var smallest = Enumerable.Range(1, 64).First(steps =>
            Evaluator.Run(Program(mapped + ".count"), new EvaluationLimits { MaxSteps = steps }).IsOk);
        var result = Evaluator.Run(Program(mapped), new EvaluationLimits { MaxSteps = smallest });
        Assert.True(result.IsError);
        Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, result.Error.Code);
    }

    [Fact]
    public async Task Cancellation_ReachedWhileAPositionIsRead_EndsTheRun()
    {
        using var cancellation = new CancellationTokenSource();
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("stop", async (_, _) =>
            {
                await Task.Yield();
                cancellation.Cancel();
                return new Result.Atom(1);
            }));
        var options = new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token };
        var parsed = Parser.Parse("[stop(), 2].map{x + 1}", options);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));

        // The list and its stage are built without calling the host; the cancellation arrives while the
        // run reads its result, and it is the run's outcome.
        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => KatLangEngine.RunAsync("[stop(), 2].map{x + 1}", options));
        Assert.Equal(cancellation.Token, thrown.CancellationToken);
    }

    // ── 12. Passive observations ──────────────────────────────────────────────────────────────

    [Fact]
    public void APassiveObservation_ShowsAListTheRunReadWhole_AndWithholdsOneItNeverRead()
    {
        var options = new RunOptions { ObservePropertyValues = true };

        // `Whole` is the run's output: read whole, so its concrete form is observed.
        var read = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Whole = [1 + 1, 2]\nWhole", options));
        var whole = Assert.Single(read.PropertyObservations!, static o => o.Name == "Whole");
        Assert.Equal(PropertyValueStatus.Available, whole.Status);
        Assert.Equal("L[2, 2]", SixRouteAgreement.Neutral(whole.Value!));

        // `Part` is only counted: no position is read, and an observation reads nothing.
        var counted = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Part = [1 + 1, 1 / 0]\nPart.count", options));
        var part = Assert.Single(counted.PropertyObservations!, static o => o.Name == "Part");
        Assert.Equal(PropertyValueStatus.Withheld, part.Status);
        Assert.Null(part.Value);
    }
}
