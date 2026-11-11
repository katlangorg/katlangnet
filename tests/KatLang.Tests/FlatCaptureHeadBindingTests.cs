using System.Reflection;
using KatLang.Evaluation;
using KatLang.TestInfrastructure;
using KatLang.Tests.AsyncEvaluation;
using KatLang.Tests.InvocationRoute;
using KatLang.Tests.LanguageSpec;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// 2026-11 call-binding allocation follow-up: an ordinary call whose callee head is a FLAT PLAIN
/// CAPTURE HEAD — at most <see cref="Evaluator.FlatUniqueNameBindingWidth"/> plain captures with
/// unique names, supplied exactly as many cells — binds straight from the stored
/// <c>ParameterPatterns</c> (<c>BindFlatCaptureHead</c>) instead of translating them on every call,
/// and one call projects the callee's parameter names once (<c>EvalBoundUserBodyCounted</c>).
/// Both are implementation-only optimizations. On every such head and supply the direct path
/// returns exactly the environment the translated path returns (<c>NeedParameterPatterns</c>, the
/// cardinality gate, <c>BindAcceptedNeedPatterns</c>) — the same names, the same cells, the same
/// order, the same shape — and demands and projects nothing; every other head and every other
/// supply count is refused and keeps the translated path. Nothing derived from a head is kept, so a
/// host that edits its caller-owned pattern list between runs, or between two calls of one run, is
/// observed by the next call exactly as before.
/// </summary>
public class FlatCaptureHeadBindingTests(ITestOutputHelper output)
{
    private delegate IReadOnlyList<(string Name, NeedCell Cell)>? BindFlat(
        IReadOnlyList<ParameterPattern> patterns, IReadOnlyList<NeedCell> supply);

    private delegate IReadOnlyList<Evaluator.NeedPattern> Translate(IReadOnlyList<ParameterPattern> patterns);

    private delegate bool AcceptsCardinality(IReadOnlyList<Evaluator.NeedPattern> patterns, int supplied);

    private delegate ValueTask<EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?>> BindAccepted(
        IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply, Evaluator.EvalCtx ctx,
        bool asynchronous, bool family, IReadOnlyList<Expr?>? occurrences);

    private delegate EvalResult<Evaluator.CountedResult> BoundBody(
        Algorithm callee, Evaluator.EvalCtx ctx, IReadOnlyList<(string Name, Result Value)> values, IReadOnlyList<string> names);

    private delegate EvalResult<Evaluator.CountedResult> SharedBody(
        Algorithm alg, Evaluator.EvalCtx ctx, IReadOnlyList<(string Name, Result Value)> valEnv);

    private static T Private<T>(string name) where T : Delegate
        => typeof(Evaluator).GetMethod(name, BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<T>();

    private static readonly BindFlat Direct = Private<BindFlat>("BindFlatCaptureHead");
    private static readonly Translate Translated = Private<Translate>("NeedParameterPatterns");
    private static readonly AcceptsCardinality Accepts = Private<AcceptsCardinality>("NeedAcceptsCardinality");
    private static readonly BindAccepted General = Private<BindAccepted>("BindAcceptedNeedPatterns");

    // ── Host-built heads ────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// A head written item by item, separated by <c>|</c>: <c>a</c> a plain capture, <c>*a</c> a
    /// collecting one, <c>meta:a</c> a META one, <c>(a,b)</c> a sequence group, <c>[a,b]</c> a list
    /// group, <c>{a,b}</c> an unpacking group. The list is a caller-owned <see cref="List{T}"/>.
    /// </summary>
    private static List<ParameterPattern> Head(string spec)
        => spec.Length == 0 ? [] : spec.Split('|').Select(Item).ToList();

    private static ParameterPattern Item(string part) => part[0] switch
    {
        '*' => new CaptureParameterPattern(part[1..], Kind: ParameterKind.Collecting),
        '(' => new SequenceValueParameterPattern(Group(part)),
        '[' => new ListValueParameterPattern(Group(part)),
        '{' => new UnpackingParameterPattern(Group(part)),
        _ when part.StartsWith("meta:", StringComparison.Ordinal) => new CaptureParameterPattern(part[5..], Kind: ParameterKind.Meta),
        _ => new CaptureParameterPattern(part),
    };

    private static ParameterPattern[] Group(string part)
        => part[1..^1].Split(',').Select(static name => (ParameterPattern)new CaptureParameterPattern(name)).ToArray();

    private static string Wide(int width) => string.Join("|", Enumerable.Range(1, width).Select(static i => "p" + i));

    public static TheoryData<string> HeadSpecs
    {
        get
        {
            var data = new TheoryData<string>
            {
                // Flat plain capture heads: the direct path.
                "", "a", "a|b", "a|A", "x|y|z", "a|b|c|d|e|f|g|h|i",
                // A repeated name keeps NEED-04's group-aware agreement.
                "a|a", "a|b|a", "a|b|c|b",
                // Collecting, META and structural items keep their own rules.
                "*xs", "a|*rest", "*rest|a", "a|*mid|b", "meta:op", "meta:op|k", "k|meta:op",
                "(a,b)", "a|(b,c)", "(a,b)|c", "[a,b]", "a|[b]", "{a,b}", "a|{b,c}", "a|(b,c)|*rest",
            };
            // Every width across the direct path's bound.
            for (var width = 2; width <= Evaluator.FlatUniqueNameBindingWidth + 2; width++)
                data.Add(Wide(width));
            return data;
        }
    }

    /// <summary>The direct path's domain, decided here independently of the production recognizer.</summary>
    private static bool IsFlatPlainHead(IReadOnlyList<ParameterPattern> head)
        => head.Count <= Evaluator.FlatUniqueNameBindingWidth
            && head.All(static pattern => pattern is CaptureParameterPattern { Kind: ParameterKind.Normal })
            && head.Select(static pattern => ((CaptureParameterPattern)pattern).Name).Distinct(StringComparer.Ordinal).Count() == head.Count;

    // A cell that records every VALUE demand and every CALLABLE projection made on it.
    private static NeedCell Logged(List<string> log, int id)
    {
        var value = EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom(id), 1));
        return new NeedCell(
            () => { log.Add("value " + id); return value; },
            () => { log.Add("value " + id); return new(value); },
            project: () => { log.Add("callable " + id); return EvalResult<Algorithm?>.Ok(null); });
    }

    private static NeedCell[] Cells(List<string> log, int count)
        => Enumerable.Range(0, count).Select(id => Logged(log, id)).ToArray();

    // The translated route's binding of a supply its cardinality gate accepts; null when the gate
    // refuses the count (the call then reports its arity error).
    private static IReadOnlyList<(string Name, NeedCell Cell)>? BindTranslated(IReadOnlyList<ParameterPattern> head, NeedCell[] supply)
    {
        var patterns = Translated(head);
        if (!Accepts(patterns, supply.Length))
            return null;
        var pending = General(patterns, supply, Evaluator.EvalCtx.Empty, false, false, null);
        Assert.True(pending.IsCompleted, "A flat plain head never suspends.");
        var bound = pending.GetAwaiter().GetResult();
        Assert.True(bound.IsOk, bound.IsError ? bound.Error.ToString() : null);
        return bound.Value!;
    }

    /// <summary>
    /// The differential: for every supply count around the head's own, the direct path binds exactly
    /// when the head is a flat plain capture head supplied its own count, and then returns what the
    /// translated path returns. Returns how many (head, count) pairs took the direct path.
    /// </summary>
    private static int AssertDirectEqualsTranslated(IReadOnlyList<ParameterPattern> head, string label)
    {
        var bound = 0;
        var flat = IsFlatPlainHead(head);
        for (var supplied = 0; supplied <= head.Count + 2; supplied++)
        {
            var directLog = new List<string>();
            var directSupply = Cells(directLog, supplied);
            var direct = Direct(head, directSupply);
            Assert.True((flat && supplied == head.Count) == direct is not null, $"{label}: {supplied} supplied");
            Assert.Empty(directLog);
            if (direct is null)
            {
                // A flat plain head refused for its count alone: the translated gate refuses it too.
                if (flat)
                    Assert.False(Accepts(Translated(head), supplied), $"{label}: {supplied} supplied");
                continue;
            }

            bound++;
            var translatedLog = new List<string>();
            var translatedSupply = Cells(translatedLog, supplied);
            var translated = BindTranslated(head, translatedSupply);
            Assert.True(translated is not null, $"{label}: the translated gate refused {supplied}");
            Assert.Empty(translatedLog);
            // The same environment shape (the shared empty list, the one-binding list, an array).
            Assert.Equal(translated!.GetType(), direct.GetType());
            Assert.Equal(translated.Count, direct.Count);
            Assert.Equal(head.Count, direct.Count);
            for (var i = 0; i < direct.Count; i++)
            {
                Assert.Equal(translated[i].Name, direct[i].Name);
                Assert.Equal(((CaptureParameterPattern)head[i]).Name, direct[i].Name);
                // Pattern i binds supplied cell i on both routes.
                Assert.Same(directSupply[i], direct[i].Cell);
                Assert.Same(translatedSupply[i], translated[i].Cell);
            }

            // A fresh environment per call (the empty one is the shared empty list on both routes).
            var again = Direct(head, directSupply);
            if (head.Count == 0)
                Assert.Same(direct, again);
            else
                Assert.NotSame(direct, again);
        }

        return bound;
    }

    [Theory]
    [MemberData(nameof(HeadSpecs))]
    public void HostBuiltHead_BindsDirectlyExactlyWhenFlat_AndThenExactlyAsTheTranslatedPath(string spec)
    {
        var head = Head(spec);
        var bound = AssertDirectEqualsTranslated(head, spec);
        Assert.Equal(IsFlatPlainHead(head) ? 1 : 0, bound);
    }

    [Fact]
    public void DirectPath_ReadsTheStoredList_OnEveryCall()
    {
        // The same caller-owned list, edited between calls: each call binds the CURRENT head, and a
        // head edited out of the direct path's domain is refused at once.
        var head = Head("a|b");
        var log = new List<string>();
        var supply = Cells(log, 2);
        Assert.Equal(["a", "b"], Direct(head, supply)!.Select(static binding => binding.Name));

        head.Reverse();
        Assert.Equal(["b", "a"], Direct(head, supply)!.Select(static binding => binding.Name));

        head[1] = new CaptureParameterPattern("renamed");
        Assert.Equal(["b", "renamed"], Direct(head, supply)!.Select(static binding => binding.Name));

        head[1] = new CaptureParameterPattern("rest", Kind: ParameterKind.Collecting);
        Assert.Null(Direct(head, supply));

        head[1] = new CaptureParameterPattern("b");
        Assert.Null(Direct(head, supply)); // (b, b): a repeated name

        head.RemoveAt(1);
        Assert.Null(Direct(head, supply)); // one pattern, two cells
        Assert.Equal(["b"], Direct(head, Cells(log, 1))!.Select(static binding => binding.Name));
        Assert.Empty(log);
    }

    // ── Every head of the corpora ───────────────────────────────────────────────────────────────────

    private sealed class HeadCollector : AstWalker
    {
        private readonly HashSet<object> _seen = new(ReferenceEqualityComparer.Instance);

        public List<IReadOnlyList<ParameterPattern>> Heads { get; } = [];

        protected override void VisitUserAlgorithm(Algorithm.User algorithm)
        {
            if (_seen.Add(algorithm.ParameterPatterns))
                Heads.Add(algorithm.ParameterPatterns);
            base.VisitUserAlgorithm(algorithm);
        }
    }

    private static HostOperations CorpusOperations() => HostOperations.Create(
        HostOperation.Create("trace", static (args, _) => args[0], "x"),
        HostOperation.Create("boom", static (_, _) => new Result.Atom(0)),
        HostOperation.Create("aflag", static (_, _) => new Result.Bool(true)),
        HostOperation.Create("stop", static (_, _) => new Result.Bool(true)));

    [Fact]
    public void EveryHeadOfTheCorpora_BindsDirectlyExactlyAsTheTranslatedPath()
    {
        // The stored head of every user algorithm of every cleanly parsed program of the invocation-route
        // corpus and the language specification corpus, against every supply count around its own.
        var options = new RunOptions { HostOperations = CorpusOperations() };
        var sources = InvocationRouteCorpus.Cases
            .Where(static c => c.Module is null)
            .Select(c => (Label: "route " + c.Id, Parsed: Parser.Parse(InvocationRouteCorpus.Core + (c.Plain ? InvocationRouteCorpus.Plain : InvocationRouteCorpus.Meta) + c.Source, options)))
            .Concat(LanguageSpecCorpus.AllCases().Select(static c => (Label: "spec " + c.Id, Parsed: Parser.Parse(c.Source))))
            .Where(static program => !program.Parsed.HasErrors)
            .ToList();

        int programs = 0, heads = 0, flatHeads = 0, otherHeads = 0, directBindings = 0;
        foreach (var (label, parsed) in sources)
        {
            var collector = new HeadCollector();
            collector.VisitAlgorithm(parsed.Root);
            programs++;
            foreach (var head in collector.Heads)
            {
                heads++;
                if (IsFlatPlainHead(head)) flatHeads++;
                else otherHeads++;
                directBindings += AssertDirectEqualsTranslated(head, label);
            }
        }

        output.WriteLine($"programs={programs} heads={heads} flat={flatHeads} other={otherHeads} directBindings={directBindings}");
        // Not vacuous: both kinds of head occur, and every flat head bound once (at its own count).
        Assert.True(programs >= 300, $"programs={programs}");
        Assert.True(flatHeads >= 1000, $"flat={flatHeads}");
        Assert.True(otherHeads >= 50, $"other={otherHeads}");
        Assert.Equal(flatHeads, directBindings);
    }

    // ── Programs on the three engines: host-built heads, edited between runs ────────────────────────

    private static Expr Reads(string name) => new Expr.Param(name);

    // a * 10 + b: the two names weigh differently, so any misbinding changes the value.
    private static Expr Weighted(string first, string second)
        => new Expr.Binary(BinaryOp.Add, new Expr.Binary(BinaryOp.Mul, Reads(first), new Expr.Num(10)), Reads(second));

    private static Expr.AlgorithmExpr CallProgram(IReadOnlyList<ParameterPattern> head, Expr body, params Expr[] arguments)
    {
        var callee = new Algorithm.User(Parent: null, ParameterPatterns: head, Opens: [], Properties: [], Output: [body]);
        return new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [new Property("F", callee)],
            [new Expr.Call(new Expr.Resolve("F"), OutputBundle.TakeOwnership(arguments))]));
    }

    private static string Describe((EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) run)
    {
        var (result, budget) = run;
        var outcome = result.IsOk
            ? $"ok {InvocationRouteCorpus.Value(result.Value.Value)} n={result.Value.EmittedCount}"
            : $"err {result.Error.Code} | {KatLangError.FromEvalError(result.Error).Message.Replace("\n", " / ", StringComparison.Ordinal)} @{result.Error.Span}";
        return $"{outcome}\tsteps={budget.ConsumedSteps}\tcheckpoints={budget.ConsumedExpressionCheckpoints}";
    }

    private static Task<string> ObserveAllEngines(Expr program)
        => ObserveAllEngines(() => (program, null));

    /// <summary>
    /// One observation per engine (sync generic, sync optimized, async twin); the three must agree.
    /// <paramref name="build"/> supplies each engine its program, so a program whose host operation
    /// edits it during a run starts every engine from the same state.
    /// </summary>
    private static async Task<string> ObserveAllEngines(Func<(Expr Program, HostOperations? Operations)> build)
    {
        var (genericProgram, genericOperations) = build();
        var generic = Describe(Evaluator.RunCountedObserved(genericProgram, enableOptimizations: false, hostOperations: genericOperations));
        var (optimizedProgram, optimizedOperations) = build();
        var optimized = Describe(Evaluator.RunCountedObserved(optimizedProgram, enableOptimizations: true, hostOperations: optimizedOperations));
        var (twinProgram, twinOperations) = build();
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var twin = Describe(await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(twinProgram, zeroArgPropertyResultCache: cache, hostOperations: twinOperations)));
        Assert.Equal(generic, optimized);
        Assert.Equal(generic, twin);
        return generic;
    }

    public static TheoryData<string, string, string, string> HeadEdits => new()
    {
        // initial head, edited head, the outcome before, the outcome after (F(1, 2), body a * 10 + b).
        { "a|b", "b|a", "ok 12", "ok 21" },
        { "b|a", "a|b", "ok 21", "ok 12" },
        // Out of the direct path's domain and back.
        { "a|b", "a|*b", "ok 12", "err TypeMismatch | while evaluating call to F: while evaluating `a * 10 + b`: Type mismatch" },
        { "a|*b", "a|b", "err TypeMismatch", "ok 12" },
        { "a|b", "a|b|c", "ok 12", "err ArityMismatch | Callable `F(a, b, c)` expects 3 arguments, but was called with 2 arguments." },
        { "a|b|c", "a|b", "err ArityMismatch | Callable `F(a, b, c)` expects 3 arguments", "ok 12" },
        { "a|b", "(a,b)", "ok 12", "err ArityMismatch | Callable `F((a, b))` expects 1 argument, but was called with 2 arguments." },
        { "a|b", "a|a", "ok 12", "err ArityMismatch | while evaluating call to F: repeated parameter 'a' requires equal arguments: Bad arity" },
        { "a|b", "x|b", "ok 12", "err UnknownName | while evaluating call to F: Unknown name: a" },
        { "x|b", "a|b", "err UnknownName", "ok 12" },
        { "a|b", "meta:a|b", "ok 12", "err NotAnAlgorithm | while evaluating call to F: while binding meta parameter 'a'" },
    };

    [Theory]
    [MemberData(nameof(HeadEdits))]
    public async Task HostEditsOfTheStoredHead_BetweenRuns_AreObservedByTheNextRun_OnAllEngines(
        string initial, string edited, string before, string after)
    {
        // ONE program object over ONE caller-owned pattern list, run, edited in place, and run again:
        // each run must equal a control built from scratch in that state, so nothing derived from the
        // head survives a run.
        Expr[] Arguments() => [new Expr.Num(1), new Expr.Num(2)];
        var head = Head(initial);
        var program = CallProgram(head, Weighted("a", "b"), Arguments());

        var first = await ObserveAllEngines(program);
        Assert.Equal(await ObserveAllEngines(CallProgram(Head(initial), Weighted("a", "b"), Arguments())), first);
        Assert.StartsWith(before, first, StringComparison.Ordinal);

        head.Clear();
        head.AddRange(Head(edited));
        var second = await ObserveAllEngines(program);
        Assert.Equal(await ObserveAllEngines(CallProgram(Head(edited), Weighted("a", "b"), Arguments())), second);
        Assert.StartsWith(after, second, StringComparison.Ordinal);
        Assert.NotEqual(first, second);
        output.WriteLine($"{initial} => {edited}: {first} => {second}");

        // And back again: the first state's observation returns exactly.
        head.Clear();
        head.AddRange(Head(initial));
        Assert.Equal(first, await ObserveAllEngines(program));
    }

    [Theory]
    [InlineData("b|a", "ok (12, 0, 21)")]
    [InlineData("a|b|c", "err ArityMismatch | Callable `F(a, b, c)` expects 3 arguments, but was called with 2 arguments.")]
    [InlineData("a|*b", "err TypeMismatch | while evaluating call to F: while evaluating `a * 10 + b`: Type mismatch")]
    public async Task HostEditOfTheStoredHead_BetweenTwoCallsOfOneRun_IsObservedByTheSecondCall(string edited, string expected)
    {
        // F(1, 2), Edit(), F(1, 2): the host operation edits F's caller-owned head between the two calls.
        (Expr Program, HostOperations? Operations) Build()
        {
            var head = Head("a|b");
            var edit = HostOperation.Create("EditHead", (_, _) =>
            {
                head.Clear();
                head.AddRange(Head(edited));
                return new Result.Atom(0);
            });
            var callee = new Algorithm.User(null, head, [], [], [Weighted("a", "b")]);
            Expr Call() => new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(1), new Expr.Num(2)]);
            var program = new Expr.AlgorithmExpr(new Algorithm.User(
                null, [], [], [new Property("F", callee)],
                [Call(), new Expr.NativeCall(edit.NativeName, []), Call()]));
            return (program, HostOperations.Create(edit));
        }

        var observed = await ObserveAllEngines(Build);
        output.WriteLine($"{edited}: {observed}");
        Assert.StartsWith(expected, observed, StringComparison.Ordinal);
        Assert.Equal(observed, await ObserveAllEngines(Build));
    }

    public static TheoryData<int> Widths
    {
        get
        {
            var data = new TheoryData<int>();
            for (var width = 0; width <= Evaluator.FlatUniqueNameBindingWidth + 2; width++) data.Add(width);
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(Widths))]
    public async Task HostBuiltCall_OfEveryWidth_BindsEachArgumentToItsOwnParameter_OnAllEngines(int width)
    {
        // F(p1, …, pW) = 1 * p1 + 2 * p2 + … called as F(1, …, W): Σ i², across the direct path's bound.
        var head = Head(width == 0 ? "" : Wide(width));
        Expr body = new Expr.Num(0);
        for (var i = 1; i <= width; i++)
            body = new Expr.Binary(BinaryOp.Add, body, new Expr.Binary(BinaryOp.Mul, new Expr.Num(i), Reads("p" + i)));
        var arguments = Enumerable.Range(1, width).Select(static i => (Expr)new Expr.Num(i)).ToArray();

        var observed = await ObserveAllEngines(CallProgram(head, body, arguments));
        Assert.StartsWith($"ok {Enumerable.Range(1, width).Sum(static i => i * i)} n=1", observed, StringComparison.Ordinal);

        // One argument too many, and one too few, is the call's arity error on every engine.
        var surplus = await ObserveAllEngines(CallProgram(head, body, [.. arguments, new Expr.Num(0)]));
        Assert.StartsWith("err ArityMismatch", surplus, StringComparison.Ordinal);
        if (width > 0)
            Assert.StartsWith("err ArityMismatch", await ObserveAllEngines(CallProgram(head, body, arguments[1..])), StringComparison.Ordinal);
    }

    [Fact]
    public async Task BoundBodyEntry_KeepsTheSharedCoresAccessErrors_OnAllEngines()
    {
        // A host-built callee with a duplicated property: the call binds its head and then fails at
        // body entry exactly as before, on the short pairwise scan and on the set alike.
        static Property Constant(string name, int value)
            => new(name, new Algorithm.User(null, [], [], [], [new Expr.Num(value)]));

        foreach (var count in new[] { 2, AlgorithmAccessors.LinearDuplicatePropertyScanLimit, AlgorithmAccessors.LinearDuplicatePropertyScanLimit + 4 })
        {
            var properties = Enumerable.Range(0, count - 1).Select(static i => Constant("P" + i, i)).ToList();
            var unique = new Algorithm.User(null, Head("a"), [], [.. properties, Constant("Last", 0)], [Reads("a")]);
            var duplicated = new Algorithm.User(null, Head("a"), [], [.. properties, Constant("P0", 0)], [Reads("a")]);
            Expr.AlgorithmExpr Calls(Algorithm callee) => new(new Algorithm.User(
                null, [], [], [new Property("F", callee)], [new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(5)])]));

            Assert.StartsWith("ok 5 n=1", await ObserveAllEngines(Calls(unique)), StringComparison.Ordinal);
            Assert.StartsWith("err DuplicateProperty", await ObserveAllEngines(Calls(duplicated)), StringComparison.Ordinal);
        }
    }

    // ── The duplicate-property scan ─────────────────────────────────────────────────────────────────

    // The former implementation, kept here as the reference: a set over the names in order.
    private static string? ReferenceFirstDuplicate(IReadOnlyList<Property> properties)
    {
        var seen = new HashSet<string>();
        foreach (var property in properties)
        {
            if (!seen.Add(property.Name))
                return property.Name;
        }
        return null;
    }

    [Fact]
    public void FindDuplicatePropName_AnswersAsTheFormerSetScan_AtEveryLengthAndDuplicatePosition()
    {
        static Property Named(string name) => new(name, new Algorithm.User(null, [], [], [], [new Expr.Num(1)]));
        var limit = AlgorithmAccessors.LinearDuplicatePropertyScanLimit;
        var checkedLists = 0;
        for (var length = 0; length <= limit + 6; length++)
        {
            var unique = Enumerable.Range(0, length).Select(static i => i % 2 == 0 ? "n" + i : "N" + i).ToArray();
            Check(unique);
            // Names differing only in case are distinct.
            if (length >= 2) Check([.. unique[..^1], unique[0].ToUpperInvariant() == unique[0] ? unique[0].ToLowerInvariant() : unique[0].ToUpperInvariant()]);
            // One duplicated pair at every pair of positions; the answer is the LATER occurrence's name.
            for (var later = 1; later < length; later++)
            {
                for (var earlier = 0; earlier < later; earlier++)
                {
                    var names = (string[])unique.Clone();
                    names[later] = names[earlier];
                    Check(names);
                }
            }
            // Two duplicated pairs: the first one met in declaration order wins.
            if (length >= 4)
            {
                var names = (string[])unique.Clone();
                names[length - 1] = names[0];
                names[2] = names[1];
                Check(names);
            }
        }

        Assert.True(checkedLists > 1000, checkedLists.ToString(System.Globalization.CultureInfo.InvariantCulture));

        void Check(string[] names)
        {
            checkedLists++;
            var properties = names.Select(Named).ToList();
            var expected = ReferenceFirstDuplicate(properties);
            var user = new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]);
            Assert.Equal(expected, user.FindDuplicatePropName());
            Assert.Equal(expected, ((Algorithm)user).FindDuplicatePropName());
            Assert.Equal(expected, AlgorithmAccessors.FirstDuplicatePropertyName(properties));
        }
    }

    // ── Strict allocation counts (isolated child process) ───────────────────────────────────────────

    private static long Bytes(Action action)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        action();
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    [Fact]
    public void FlatCaptureHead_AllocatesExactlyItsEnvironment_AndARefusalNothing_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        static NeedCell Ready(int value) => NeedCell.Ready(new(new Result.Atom(value), 1));
        foreach (var width in new[] { 0, 1, 2, 3, 8, Evaluator.FlatUniqueNameBindingWidth })
        {
            IReadOnlyList<ParameterPattern> head = Head(width == 0 ? "" : Wide(width)).ToArray();
            var supply = Enumerable.Range(0, width).Select(Ready).ToArray();
            IReadOnlyList<(string Name, NeedCell Cell)>? bound = Direct(head, supply); // warm-up
            // The environment a head of this width binds, built here the way the binder builds it.
            Action environment = width switch
            {
                0 => () => bound = [],
                1 => () => bound = [("p1", supply[0])],
                _ => () => bound = new (string Name, NeedCell Cell)[width],
            };
            environment(); // warm-up
            var expected = Bytes(environment);
            Assert.Equal(width == 0, expected == 0);
            var allocated = Bytes(() => bound = Direct(head, supply));
            Assert.Equal(width, bound!.Count);
            Assert.Equal(expected, allocated);
        }

        // Every refusal is decided without allocating: the translated path then pays as before.
        var two = new[] { Ready(1), Ready(2) };
        foreach (var spec in new[] { "a|*rest", "a|a", "meta:op|k", "(a,b)|c", "a", "a|b|c" })
        {
            IReadOnlyList<ParameterPattern> head = Head(spec).ToArray();
            Assert.Null(Direct(head, two));
            Assert.Equal(0, Bytes(() => _ = Direct(head, two)));
        }
        IReadOnlyList<ParameterPattern> wide = Head(Wide(Evaluator.FlatUniqueNameBindingWidth + 1)).ToArray();
        var wideSupply = Enumerable.Range(0, Evaluator.FlatUniqueNameBindingWidth + 1).Select(Ready).ToArray();
        Assert.Null(Direct(wide, wideSupply));
        Assert.Equal(0, Bytes(() => _ = Direct(wide, wideSupply)));
        GcIsolatedAllocation.Complete();
    }

    [Fact]
    public void FindDuplicatePropName_OfAShortPropertyList_AllocatesNothing_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        static Property Named(string name) => new(name, new Algorithm.User(null, [], [], [], [new Expr.Num(1)]));
        var limit = AlgorithmAccessors.LinearDuplicatePropertyScanLimit;
        foreach (var count in new[] { 0, 1, 2, 5, limit })
        {
            var unique = new Algorithm.User(null, [], [], Enumerable.Range(0, count).Select(static i => Named("P" + i)).ToArray(), [new Expr.Num(1)]);
            Algorithm total = unique;
            Assert.Null(unique.FindDuplicatePropName()); // warm-up
            Assert.Null(total.FindDuplicatePropName());
            string? found = "unset";
            Assert.Equal(0, Bytes(() => found = unique.FindDuplicatePropName()));
            Assert.Null(found);
            Assert.Equal(0, Bytes(() => found = total.FindDuplicatePropName()));
            Assert.Null(found);
        }

        var duplicated = new Algorithm.User(null, [], [], Enumerable.Range(0, limit).Select(i => Named(i == limit - 1 ? "P0" : "P" + i)).ToArray(), [new Expr.Num(1)]);
        Assert.Equal("P0", duplicated.FindDuplicatePropName());
        string? name = null;
        Assert.Equal(0, Bytes(() => name = duplicated.FindDuplicatePropName()));
        Assert.Equal("P0", name);
        GcIsolatedAllocation.Complete();
    }

    [Fact]
    public void BoundBodyEntry_ProjectsTheParameterNamesOncePerCall_GcIsolatedChild()
    {
        // The shared core enters a body with a FRESH Params projection; the bound entry enters with the
        // names its binding boundary already projected. Everything else the two do is the same, so
        // the shared core allocates exactly one names array more.
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var bound = Private<BoundBody>("EvalBoundUserBodyCounted");
        var shared = Private<SharedBody>("EvalAlgOutputCountedCore");
        var ctx = Evaluator.EvalCtx.Empty;
        IReadOnlyList<(string Name, Result Value)> values = [];
        foreach (var width in new[] { 1, 2, 5 })
        {
            var callee = new Algorithm.User(null, Head(Wide(width)).ToArray(), [], [], [new Expr.Num(7)]);
            IReadOnlyList<string> names = callee.Params;
            for (var warm = 0; warm < 3; warm++)
            {
                Assert.True(bound(callee, ctx, values, names).IsOk);
                Assert.True(shared(callee, ctx, values).IsOk);
            }

            var projection = Bytes(() => names = callee.Params);
            Assert.True(projection > 0);
            var boundBytes = Bytes(() => _ = bound(callee, ctx, values, names));
            var sharedBytes = Bytes(() => _ = shared(callee, ctx, values));
            Assert.Equal(sharedBytes, boundBytes + projection);
        }
        GcIsolatedAllocation.Complete();
    }
}
