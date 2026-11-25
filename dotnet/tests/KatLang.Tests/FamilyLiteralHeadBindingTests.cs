using System.Reflection;
using KatLang.Evaluation;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// 2026-11 allocation attribution: a clause head that is a FLAT LITERAL LEVEL — literals and unique plain
/// names, at least one literal (<c>Fib(0)</c>, <c>G(0, y)</c>, <c>T(0, b, c)</c>) — binds through the
/// family drivers' direct path (<c>BindFlatLiteralHead</c> and its async mirror) instead of the general
/// inspecting binder's dictionaries and work stacks. This is an implementation-only optimization: on every
/// such head the direct path returns exactly what the general path (<c>BindAcceptedNeedPatterns</c> in
/// family mode) returns — the same error, the same non-match, the same environment in written order — and
/// demands exactly the same cells in the same order; every other head keeps the general path. Source
/// programs keep their value, error and resource profile on the three engines.
/// </summary>
public class FamilyLiteralHeadBindingTests
{
    private delegate ValueTask<EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?>> BindAccepted(
        IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply, Evaluator.EvalCtx ctx,
        bool asynchronous, bool family, IReadOnlyList<Expr?>? occurrences);

    private delegate EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?> BindLiteral(
        IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply, in Evaluator.EvalCtx ctx);

    private delegate ValueTask<EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?>> BindLiteralAsync(
        IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply, Evaluator.EvalCtx ctx);

    private delegate bool IsLiteralHead(IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply);

    private static T Private<T>(string name) where T : Delegate
        => typeof(Evaluator).GetMethod(name, BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<T>();

    private static readonly BindAccepted General = Private<BindAccepted>("BindAcceptedNeedPatterns");
    private static readonly BindLiteral Direct = Private<BindLiteral>("BindFlatLiteralHead");
    private static readonly BindLiteralAsync DirectAsync = Private<BindLiteralAsync>("BindFlatLiteralHeadAsync");
    private static readonly IsLiteralHead Recognizes = Private<IsLiteralHead>("IsFlatLiteralHead");

    private static Evaluator.NeedPattern Lit(int value) => new(Literal: new Pattern.LitInt(value));

    private static Evaluator.NeedPattern LitS(string value) => new(Literal: new Pattern.LitString(value));

    private static Evaluator.NeedPattern LitB(bool value) => new(Literal: new Pattern.LitBool(value));

    private static Evaluator.NeedPattern Name(string name) => new(name);

    // A cell that records its VALUE demand (both channels) in `log` and then yields `value`.
    private static NeedCell Logged(List<int> log, int id, EvalResult<Evaluator.CountedResult> value)
        => new(() => { log.Add(id); return value; }, () => { log.Add(id); return new(value); });

    private static EvalResult<Evaluator.CountedResult> Value(Result value) => EvalResult<Evaluator.CountedResult>.Ok(new(value, 1));

    private static T Complete<T>(ValueTask<T> operation)
    {
        Assert.True(operation.IsCompleted, "Ready and logged cells never suspend.");
        return operation.GetAwaiter().GetResult();
    }

    // The binding as observable data: the error, the non-match, or each name with its cell's slot.
    private static string Describe(EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?> bound, IReadOnlyList<NeedCell> supply)
        => bound.IsError
            ? "err " + KatLangError.FromEvalError(bound.Error).Message
            : bound.Value is not { } env
                ? "non-match"
                : "env [" + string.Join(", ", env.Select(b => b.Name + "=#" + supply.ToList().IndexOf(b.Cell))) + "]";

    private static readonly string LongText = new('a', 100);

    public static TheoryData<string> HeadCases => new()
    {
        "0", "0|x", "x|0", "x|0|y", "0|1|2", "0|y|z", "x|y|0", "s'a", "s'long", "b+", "0|b-|s'a",
    };

    private static Evaluator.NeedPattern[] Head(string spec)
        => spec.Split('|').Select(part => part switch
        {
            "s'a" => LitS("a"),
            "s'long" => LitS(LongText),
            "b+" => LitB(true),
            "b-" => LitB(false),
            _ when int.TryParse(part, out var n) => Lit(n),
            _ => Name(part),
        }).ToArray();

    // Supplies for a head: each slot a matching value, a mismatching value of each kind, or a failure.
    private static IEnumerable<(string Label, Func<List<int>, NeedCell[]> Build)> Supplies(Evaluator.NeedPattern[] head)
    {
        Result Match(Evaluator.NeedPattern p) => p.Literal switch
        {
            Pattern.LitInt(var n) => new Result.Atom(n),
            Pattern.LitString(var s) => new Result.Str(s),
            Pattern.LitBool(var b) => new Result.Bool(b),
            _ => new Result.Atom(7),
        };
        Result Miss(Evaluator.NeedPattern p) => p.Literal switch
        {
            Pattern.LitInt(var n) => new Result.Atom(n + 1),
            Pattern.LitString(var s) => new Result.Str(s[..^1] + "b"),
            Pattern.LitBool(var b) => new Result.Bool(!b),
            _ => new Result.Atom(7),
        };
        NeedCell[] Build(List<int> log, Func<int, EvalResult<Evaluator.CountedResult>> slot)
            => head.Select((_, i) => Logged(log, i, slot(i))).ToArray();

        yield return ("all match", log => Build(log, i => Value(Match(head[i]))));
        for (var k = 0; k < head.Length; k++)
        {
            if (head[k].Literal is null) continue;
            var at = k;
            yield return ($"miss at {at}", log => Build(log, i => Value(i == at ? Miss(head[i]) : Match(head[i]))));
            yield return ($"kind miss at {at}", log => Build(log, i => Value(i == at ? new Result.SequenceValue([]) : Match(head[i]))));
            yield return ($"failure at {at}", log => Build(log, i => i == at ? new EvalError.BadIndex() : Value(Match(head[i]))));
        }
    }

    [Theory]
    [MemberData(nameof(HeadCases))]
    public void FlatLiteralHead_BindsExactlyAsTheGeneralPath_DemandingTheSameCellsInTheSameOrder(string spec)
    {
        var head = Head(spec);
        var ctx = Evaluator.EvalCtx.Empty;
        foreach (var (label, build) in Supplies(head))
        {
            var generalLog = new List<int>();
            var generalSupply = build(generalLog);
            Assert.True(Recognizes(head, generalSupply), spec);
            var general = Describe(Complete(General(head, generalSupply, ctx, false, true, null)), generalSupply);

            var directLog = new List<int>();
            var directSupply = build(directLog);
            var direct = Describe(Direct(head, directSupply, in ctx), directSupply);

            var asyncLog = new List<int>();
            var asyncSupply = build(asyncLog);
            var twin = Describe(Complete(DirectAsync(head, asyncSupply, ctx)), asyncSupply);

            Assert.Equal(general, direct);
            Assert.Equal(general, twin);
            Assert.Equal(generalLog, directLog);
            Assert.Equal(generalLog, asyncLog);
            Assert.True(label != "all match" || general.StartsWith("env", StringComparison.Ordinal), $"{spec} {label}: {general}");
        }
    }

    [Fact]
    public void OnlyFlatLiteralLevels_TakeTheDirectPath()
    {
        NeedCell[] Cells(int n) => Enumerable.Range(0, n).Select(i => NeedCell.Ready(new(new Result.Atom(i), 1))).ToArray();
        Assert.True(Recognizes([Lit(0)], Cells(1)));
        Assert.True(Recognizes([Lit(0), Name("x")], Cells(2)));
        // No literal: the name-only rules own it (a single name, FlatUniqueNameBindings, or the general path).
        Assert.False(Recognizes([Name("x")], Cells(1)));
        Assert.False(Recognizes([Name("x"), Name("y")], Cells(2)));
        Assert.False(Recognizes([], Cells(0)));
        // A repeated name keeps NEED-04's group-aware agreement; a collector, META and structure keep theirs.
        Assert.False(Recognizes([Lit(0), Name("x"), Name("x")], Cells(3)));
        Assert.False(Recognizes([Lit(0), new Evaluator.NeedPattern("rest", Collecting: true)], Cells(3)));
        Assert.False(Recognizes([Lit(0), new Evaluator.NeedPattern("m", Meta: true)], Cells(2)));
        Assert.False(Recognizes([Lit(0), new Evaluator.NeedPattern(Children: [Name("a"), Name("b")])], Cells(2)));
        // The supply count must equal the pattern count, and the width is the flat-name bound.
        Assert.False(Recognizes([Lit(0), Name("x")], Cells(1)));
        Assert.True(Recognizes([Lit(0), .. Enumerable.Range(1, Evaluator.FlatUniqueNameBindingWidth - 1).Select(i => Name("p" + i))], Cells(Evaluator.FlatUniqueNameBindingWidth)));
        Assert.False(Recognizes([Lit(0), .. Enumerable.Range(1, Evaluator.FlatUniqueNameBindingWidth).Select(i => Name("p" + i))], Cells(Evaluator.FlatUniqueNameBindingWidth + 1)));
    }

    public static TheoryData<string, string> Programs => new()
    {
        { "Fib(0) = 0\nFib(1) = 1\nFib(n) = Fib(n - 1) + Fib(n - 2)\nFib(15)", "ok 610" },
        { "G(0, y) = y\nG(x, y) = x + y\nG(0, 5), G(2, 3)", "ok (5, 5)" },
        { "H(x, 1) = x\nH(x, y) = x * y\nH(4, 1), H(4, 2)", "ok (4, 8)" },
        { "S('a') = 1\nS(s) = 2\nS('a'), S('b'), S(1)", "ok (1, 2, 2)" },
        { $"L('{LongText}') = 1\nL(s) = 2\nL('{LongText}'), L('{LongText[..^1]}b')", "ok (1, 2)" },
        { "B(true) = 1\nB(false) = 0\nB(1 < 2), B(2 < 1)", "ok (1, 0)" },
        { "F(0) = 1\nF(x) = 2\nF('a'), F(0), F(())", "ok (2, 1, 2)" },
        // A literal demands a recursive argument: the inner call runs inside the outer clause decision.
        { "F(0) = 0\nF(n) = F(F(n - 1))\nF(5)", "ok 0" },
        // A structural head beside a literal stays on the general path.
        { "P(0, (a, b)) = a\nP(n, x) = n\nP(0, (1, 2)), P(3, 4)", "ok (1, 3)" },
        { "T(0, 1, 2) = 'a'\nT(0, b, c) = b + c\nT(a, b, c) = a\nT(0, 1, 2), T(0, 5, 6), T(7, 1, 2)", "ok ('a', 11, 7)" },
        { "K(0, k) = k\nK(n, k) = K(n - 1, k + n)\nK(30, 0)", "ok 465" },
        { "F(0) = 1\nF(x) = 2\nF([1][5])", "err BadIndex | while evaluating call to F: Bad index @[25:7, 25:8)" },
        { "F(0) = 1\nF(1) = 2\nF(2)", "err NoMatchingBranch | while evaluating call to F: No matching branch for 'F' @[25:1, 25:5)" },
        { "F(0) = 1\nF(x) = 2\nF(1 / 0)", "err DivisionByZero | while evaluating call to F: Division by zero @[25:3, 25:8)" },
    };

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task Program_HasThePinnedOutcome_AndOneResourceProfile_OnAllEngines(string source, string expected)
    {
        foreach (var plain in new[] { true, false })
        {
            var c = new InvocationRouteCorpus.Case("FAMILY-LITERAL", source, Plain: plain);
            var generic = await InvocationRouteCorpus.Observe(c, 0);
            var optimized = await InvocationRouteCorpus.Observe(c, 1);
            var asynchronous = await InvocationRouteCorpus.Observe(c, 2);
            if (plain) Assert.Equal(expected, generic.Outcome);
            Assert.Equal(generic.Semantic, optimized.Semantic);
            Assert.Equal(generic.Semantic, asynchronous.Semantic);
            Assert.Equal(generic.Plans, optimized.Plans);
            Assert.Equal(generic.Plans, asynchronous.Plans);
            Assert.Equal(generic.Formations, optimized.Formations);
            Assert.Equal(generic.Formations, asynchronous.Formations);
        }
    }

    [Fact]
    public void FlatLiteralHead_AllocatesOnlyItsEnvironment_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        static long Bytes(Action action)
        {
            var before = GC.GetAllocatedBytesForCurrentThread();
            action();
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        var ctx = Evaluator.EvalCtx.Empty;
        NeedCell Ready(int value) => NeedCell.Ready(new(new Result.Atom(value), 1));
        var literalOnly = new[] { Lit(0) };
        var mixed = new[] { Lit(0), Name("y"), Name("z") };
        NeedCell[] zero = [Ready(0)], one = [Ready(1)], mixedSupply = [Ready(0), Ready(5), Ready(6)];
        foreach (var (head, supply) in new[] { (literalOnly, zero), (literalOnly, one), (mixed, mixedSupply) })
            _ = Direct(head, supply, in ctx);

        // An all-literal head: nothing, matched or not.
        Assert.Equal(0, Bytes(() => _ = Direct(literalOnly, zero, in ctx)));
        Assert.Equal(0, Bytes(() => _ = Direct(literalOnly, one, in ctx)));
        // Literals and names: exactly the environment array.
        var environment = Bytes(() => _ = new (string Name, NeedCell Cell)[2]);
        Assert.Equal(environment, Bytes(() => _ = Direct(mixed, mixedSupply, in ctx)));
        GcIsolatedAllocation.Complete();
    }
}
