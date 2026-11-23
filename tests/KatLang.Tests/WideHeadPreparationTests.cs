using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.TestInfrastructure;
using KatLang.Tests.AsyncEvaluation;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// WIDE HEAD PREPARATION (2026-11-23, follow-up of the wide parameter frame audit of 2026-11-22). A head of more
/// than <see cref="Evaluator.FlatUniqueNameBindingWidth"/> patterns missed every direct binding path: each ordinary
/// call translated its stored head again (<c>NeedParameterPatterns</c>, about 64 B per pattern) and every binding
/// of a wide level — call, loop round, clause attempt — ran the general binder, whose multiplicity count, visit
/// table, work stacks and binding dictionary cost about 380 KB at 1,024 names. And a head pushed without a head
/// scope projected its whole <c>Params</c> list on every captured-parameter read (<c>CapturedParameterActivation</c>),
/// which the loop planner does once per captured reference it classifies. Now a wide FLAT translated level keeps its
/// binding shape (<see cref="Evaluator.WideNeedLevel"/>); a level of distinct names binds directly, a wide literal
/// clause head through the literal head's direct path, every other level through the general binder; an ordinary
/// call's wide stored head is translated once per run and validated against the caller-owned list before each use
/// (<see cref="Evaluator.NeedHeadPreparationCache"/>); and a scopeless head answers membership from its stored
/// patterns (<see cref="ParameterPattern.HasCaptureNamed"/>). Implementation-only: these tests pin the direct paths
/// against the general binder on random levels, the membership against the projection, the cache's validation, and
/// whole programs — plain, collecting, structural, repeated-name, clause, callback, recursive and loop heads, arity
/// and NEED-04 precedence, demand order, cancellation, host edits within and between runs, activation identity —
/// on the plain, counted generic, optimized, plan-retaining and async routes.
/// </summary>
public class WideHeadPreparationTests
{
    private const int Flat = Evaluator.FlatUniqueNameBindingWidth;
    private const int Indexed = Evaluator.MinimumIndexedParameterCount;

    private delegate ValueTask<EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?>> BindAccepted(
        IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply, Evaluator.EvalCtx ctx,
        bool asynchronous, bool family, IReadOnlyList<Expr?>? occurrences);

    private delegate EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?> BindLiteral(
        IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply, in Evaluator.EvalCtx ctx);

    private delegate ValueTask<EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?>> BindLiteralAsync(
        IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply, Evaluator.EvalCtx ctx);

    private delegate bool IsLiteralHead(IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply);

    private delegate IReadOnlyList<Evaluator.NeedPattern> TranslateParameters(IReadOnlyList<ParameterPattern> patterns);

    private delegate IReadOnlyList<Evaluator.NeedPattern> TranslateClause(Pattern pattern);

    private delegate ParameterActivation? Captured(string name, Evaluator.EvalCtx ctx);

    private delegate NeedCell Collector(IReadOnlyList<NeedCell> slice, Evaluator.EvalCtx ctx);

    private static T Private<T>(string name) where T : Delegate
        => typeof(Evaluator).GetMethod(name, BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<T>();

    private static readonly BindAccepted Bind = Private<BindAccepted>("BindAcceptedNeedPatterns");
    private static readonly BindLiteral LiteralHead = Private<BindLiteral>("BindFlatLiteralHead");
    private static readonly BindLiteralAsync LiteralHeadAsync = Private<BindLiteralAsync>("BindFlatLiteralHeadAsync");
    private static readonly IsLiteralHead RecognizesLiteralHead = Private<IsLiteralHead>("IsFlatLiteralHead");
    private static readonly TranslateParameters NeedParameterPatterns = Private<TranslateParameters>("NeedParameterPatterns");
    private static readonly TranslateClause NeedClauseHead = Private<TranslateClause>("NeedClauseHead");
    private static readonly Captured CapturedParameterActivation = Private<Captured>("CapturedParameterActivation");
    private static readonly Collector CollectorCell = Private<Collector>("CollectorCell");

    private static NeedCell Ready(int value) => NeedCell.Ready(new(new Result.Atom(value), 1));

    private static ParameterPattern[] Captures(IEnumerable<string> names)
        => names.Select(static name => (ParameterPattern)new CaptureParameterPattern(name)).ToArray();

    private static string[] Names(string prefix, int count) => Enumerable.Range(0, count).Select(i => prefix + i).ToArray();

    private static T Complete<T>(ValueTask<T> operation)
    {
        Assert.True(operation.IsCompleted, "Ready and logged cells never suspend.");
        return operation.GetAwaiter().GetResult();
    }

    // ── The translated level ────────────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(Flat)]
    [InlineData(Flat + 1)]
    [InlineData(Indexed)]
    [InlineData(300)]
    public void AFlatLevelWiderThanTheDirectPath_IsTranslatedIntoAWideLevel_HoldingTheSameRecords(int width)
    {
        var head = Enumerable.Range(0, width)
            .Select(static i => (ParameterPattern)new CaptureParameterPattern("p" + i, Kind: i == 3 ? ParameterKind.Collecting : ParameterKind.Normal))
            .ToArray();
        var translated = NeedParameterPatterns(head);
        Assert.Equal(width > Flat, translated is Evaluator.WideNeedLevel);
        Assert.Equal(width, translated.Count);
        for (var i = 0; i < width; i++)
        {
            Assert.Same(head[i], translated[i].Original);
            Assert.Equal(((CaptureParameterPattern)head[i]).Name, translated[i].Name);
            Assert.Equal(i == 3, translated[i].Collecting);
            Assert.Null(translated[i].Children);
        }

        if (translated is Evaluator.WideNeedLevel wide)
        {
            // A read-only collection like the array it wraps: copies are sized from Count and mutations refused.
            ICollection<Evaluator.NeedPattern> collection = wide;
            Assert.True(collection.IsReadOnly);
            var copy = new Evaluator.NeedPattern[width + 2];
            collection.CopyTo(copy, 1);
            Assert.Equal(translated, copy[1..^1]);
            Assert.Equal(translated, wide.ToArray());
            Assert.Equal(translated, new Stack<Evaluator.NeedPattern>(wide).Reverse());
            Assert.True(collection.Contains(translated[width - 1]));
            Assert.False(collection.Contains(new Evaluator.NeedPattern("missing")));
            Assert.Throws<NotSupportedException>(() => collection.Add(new Evaluator.NeedPattern("x")));
            Assert.Throws<NotSupportedException>(() => collection.Remove(translated[0]));
            Assert.Throws<NotSupportedException>(collection.Clear);
            Assert.Equal(Evaluator.WideLevelShape.DistinctNames, wide.Shape);
            Assert.Equal(3, wide.Collector);
        }

        // A structural pattern anywhere keeps the structural translation, whatever the width.
        ParameterPattern[] structural = [.. head, new SequenceValueParameterPattern(Captures(["a", "b"]))];
        Assert.IsNotType<Evaluator.WideNeedLevel>(NeedParameterPatterns(structural));

        // A clause head follows the same rule: literals and binders.
        var clause = new Pattern.SequenceValue([new Pattern.LitInt(0), .. Enumerable.Range(1, width).Select(static i => (Pattern)new Pattern.Bind("q" + i))]);
        var clauseHead = NeedClauseHead(clause);
        Assert.Equal(width + 1 > Flat, clauseHead is Evaluator.WideNeedLevel);
        if (clauseHead is Evaluator.WideNeedLevel wideClause)
            Assert.Equal(Evaluator.WideLevelShape.DistinctNamesWithLiterals, wideClause.Shape);
    }

    // The binding shape, decided here independently of the production decision.
    private static Evaluator.WideLevelShape ExpectedShape(IReadOnlyList<Evaluator.NeedPattern> level)
    {
        if (level.Any(static p => p.Meta || p.Children is not null || (p.Literal is not null && p.Name is not null)))
            return Evaluator.WideLevelShape.General;
        var named = level.Where(static p => p.Literal is null).ToArray();
        if (named.Any(static p => p.Name is null) || named.Select(static p => p.Name).Distinct(StringComparer.Ordinal).Count() != named.Length)
            return Evaluator.WideLevelShape.General;
        var collectors = named.Count(static p => p.Collecting);
        var literals = level.Count(static p => p.Literal is not null);
        if (collectors > 1 || (collectors == 1 && literals > 0))
            return Evaluator.WideLevelShape.General;
        return literals > 0 ? Evaluator.WideLevelShape.DistinctNamesWithLiterals : Evaluator.WideLevelShape.DistinctNames;
    }

    // A random wide flat level: names (sometimes repeated or null), collectors, META captures and literals.
    private static Evaluator.NeedPattern[] RandomLevel(Random random, int width, bool meta)
    {
        var level = new Evaluator.NeedPattern[width];
        var repeats = random.Next(4) == 0;
        var literals = random.Next(3) == 0;
        // A literal head mostly has no collector (a collector beside a literal keeps the general binder).
        var collectors = literals ? (random.Next(4) == 0 ? 1 : 0) : random.Next(3);
        for (var i = 0; i < width; i++)
        {
            var roll = random.Next(100);
            level[i] = literals && roll < 25 ? new Evaluator.NeedPattern(Literal: new Pattern.LitInt(random.Next(3)))
                // A host-built capture of no name, translated as the translation records it (with its pattern).
                : roll == 99 && random.Next(4) == 0 ? new Evaluator.NeedPattern(null, Original: new CaptureParameterPattern(new ParameterDeclaration(null!)))
                : meta && roll == 98 ? new Evaluator.NeedPattern("m" + i, Meta: true)
                : new Evaluator.NeedPattern(repeats ? "n" + random.Next(width) : "p" + i);
        }
        for (var c = 0; c < collectors; c++)
        {
            var at = random.Next(width);
            if (level[at] is { Literal: null, Name: { } name, Meta: false })
                level[at] = level[at] with { Collecting = true };
        }
        return level;
    }

    // A cell that records its VALUE demand and its CALLABLE projection in `log`, holding `value`.
    private static NeedCell Logged(List<string> log, int id, int value)
    {
        var outcome = EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom(value), 1));
        return new NeedCell(
            () => { log.Add("value " + id); return outcome; },
            () => { log.Add("value " + id); return new(outcome); },
            project: () => { log.Add("callable " + id); return EvalResult<Algorithm?>.Ok(null); });
    }

    // A binding as observable data: the error, the non-match, or each name with its supplied slot (a collector's
    // slice as the slots it holds).
    private static string Describe(EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?> bound, IReadOnlyList<NeedCell> supply)
    {
        if (bound.IsError)
            return "err " + KatLangError.FromEvalError(bound.Error).Message;
        if (bound.Value is not { } env)
            return "non-match";
        string Slot(NeedCell cell)
        {
            var index = supply.ToList().IndexOf(cell);
            return index >= 0 ? "#" + index : cell.Slice is { } slice ? "*[" + string.Join(",", slice.Select(c => supply.ToList().IndexOf(c))) + "]" : "?";
        }
        return "env [" + string.Join(", ", env.Select(b => (b.Name ?? "<null>") + "=" + Slot(b.Cell))) + "]";
    }

    public static TheoryData<int> Seeds
    {
        get
        {
            var data = new TheoryData<int>();
            for (var seed = 1; seed <= 48; seed++) data.Add(seed);
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(Seeds))]
    public void AWideLevel_BindsExactlyAsTheGeneralBinder_OnRandomLevelsAndSupplies(int seed)
    {
        var random = new Random(7919 * seed);
        var width = Flat + 1 + random.Next(seed % 4 == 0 ? 300 : 40);
        var records = RandomLevel(random, width, meta: false);
        var wide = new Evaluator.WideNeedLevel(records);
        // The same records as a plain array: wider than the pairwise direct path, so the general binder binds it.
        var general = records.ToArray();
        Assert.Equal(ExpectedShape(records), wide.Shape);

        var collector = Array.FindIndex(records, static p => p.Collecting);
        var counts = collector >= 0 && records.Count(static p => p.Collecting) == 1 ? new[] { width - 1, width, width + 3 } : [width];
        foreach (var count in counts)
        {
            // Values 0..2 for literal positions sometimes match, sometimes not; repeated names sometimes agree.
            var values = Enumerable.Range(0, count).Select(_ => random.Next(3)).ToArray();
            foreach (var family in new[] { false, true })
            {
                foreach (var asynchronous in new[] { false, true })
                {
                    var expectedLog = new List<string>();
                    var expectedSupply = values.Select((v, i) => Logged(expectedLog, i, v)).ToArray();
                    var expected = Describe(Complete(Bind(general, expectedSupply, Evaluator.EvalCtx.Empty, asynchronous, family, null)), expectedSupply);

                    var actualLog = new List<string>();
                    var actualSupply = values.Select((v, i) => Logged(actualLog, i, v)).ToArray();
                    var direct = RecognizesLiteralHead(wide, actualSupply);
                    Assert.Equal(wide.Shape == Evaluator.WideLevelShape.DistinctNamesWithLiterals, direct);
                    // The family drivers' choice: the literal head's direct path where it applies, the binder otherwise.
                    var actual = Describe(direct
                        ? asynchronous ? Complete(LiteralHeadAsync(wide, actualSupply, Evaluator.EvalCtx.Empty)) : LiteralHead(wide, actualSupply, Evaluator.EvalCtx.Empty)
                        : Complete(Bind(wide, actualSupply, Evaluator.EvalCtx.Empty, asynchronous, family, null)), actualSupply);
                    Assert.Equal(expected, actual);
                    Assert.Equal(expectedLog, actualLog);
                }
            }
        }
    }

    [Fact]
    public void TheRandomLevels_CoverEveryBindingShape()
    {
        // The equivalence theory above means something only if its levels reach both direct paths and the binder.
        var shapes = Enumerable.Range(1, 48).Select(seed =>
        {
            var random = new Random(7919 * seed);
            var width = Flat + 1 + random.Next(seed % 4 == 0 ? 300 : 40);
            return new Evaluator.WideNeedLevel(RandomLevel(random, width, meta: false)).Shape;
        }).ToArray();
        foreach (var shape in Enum.GetValues<Evaluator.WideLevelShape>())
            Assert.True(shapes.Count(s => s == shape) >= 5, $"only {shapes.Count(s => s == shape)} random levels of shape {shape}");
        Assert.Contains(Enumerable.Range(1, 48), seed => new Random(7919 * seed) is var random
            && RandomLevel(random, Flat + 1 + random.Next(seed % 4 == 0 ? 300 : 40), meta: false) is var level
            && new Evaluator.WideNeedLevel(level).Shape == Evaluator.WideLevelShape.DistinctNames && level.Any(static p => p.Collecting));
    }

    [Fact]
    public void AWideLevel_WithOtherPatterns_KeepsTheGeneralBinder()
    {
        string[] names = [.. Names("p", Flat + 4)];
        Evaluator.NeedPattern Plain(int i) => new(names[i]);
        Evaluator.WideNeedLevel Level(Func<int, Evaluator.NeedPattern> at) => new(Enumerable.Range(0, names.Length).Select(at).ToArray());
        Assert.Equal(Evaluator.WideLevelShape.DistinctNames, Level(Plain).Shape);
        Assert.Equal(-1, Level(Plain).Collector);
        // A repeated name (NEED-04), a null name, META, a second collector, a literal beside a collector, structure.
        Assert.Equal(Evaluator.WideLevelShape.General, Level(i => i == 9 ? new("p0") : Plain(i)).Shape);
        Assert.Equal(Evaluator.WideLevelShape.General, Level(i => i == 9 ? new(null) : Plain(i)).Shape);
        Assert.Equal(Evaluator.WideLevelShape.General, Level(i => i == 9 ? new("m", Meta: true) : Plain(i)).Shape);
        Assert.Equal(Evaluator.WideLevelShape.General, Level(i => i is 2 or 9 ? Plain(i) with { Collecting = true } : Plain(i)).Shape);
        Assert.Equal(Evaluator.WideLevelShape.General,
            Level(i => i == 2 ? Plain(i) with { Collecting = true } : i == 9 ? new(Literal: new Pattern.LitInt(1)) : Plain(i)).Shape);
        Assert.Equal(Evaluator.WideLevelShape.General, Level(i => i == 9 ? new(Children: [new("a"), new("b")]) : Plain(i)).Shape);
        Assert.Equal(Evaluator.WideLevelShape.General, Level(i => i == 9 ? new("x", Literal: new Pattern.LitInt(1)) : Plain(i)).Shape);
        var collecting = Level(i => i == 5 ? Plain(i) with { Collecting = true } : Plain(i));
        Assert.Equal(Evaluator.WideLevelShape.DistinctNames, collecting.Shape);
        Assert.Equal(5, collecting.Collector);
        var literal = Level(i => i == 0 ? new(Literal: new Pattern.LitInt(0)) : Plain(i));
        Assert.Equal(Evaluator.WideLevelShape.DistinctNamesWithLiterals, literal.Shape);
        Assert.Equal(-1, literal.Collector);
        // Names that differ only in case are distinct, as everywhere in binding.
        Assert.Equal(Evaluator.WideLevelShape.DistinctNames, Level(i => i == 9 ? new("P0") : Plain(i)).Shape);
    }

    [Fact]
    public void AWideCollector_CollectsTheSameSlice_AsTheGeneralBinder()
    {
        var names = Names("p", Flat + 7);
        var records = names.Select((n, i) => new Evaluator.NeedPattern(n, Collecting: i == 4)).ToArray();
        var wide = new Evaluator.WideNeedLevel(records);
        foreach (var count in new[] { names.Length - 1, names.Length, names.Length + 9 })
        {
            var supply = Enumerable.Range(0, count).Select(Ready).ToArray();
            var direct = Complete(Bind(wide, supply, Evaluator.EvalCtx.Empty, false, false, null)).Value!;
            var general = Complete(Bind(records.ToArray(), supply, Evaluator.EvalCtx.Empty, false, false, null)).Value!;
            Assert.Equal(general.Select(static b => b.Name), direct.Select(static b => b.Name));
            for (var i = 0; i < names.Length; i++)
            {
                if (i == 4)
                {
                    Assert.Equal(general[i].Cell.Slice, direct[i].Cell.Slice);
                    Assert.Equal(count - names.Length + 1, direct[i].Cell.Slice!.Count);
                    Assert.Equal(InvocationRouteCorpus.Value(general[i].Cell.Demand().Value.Value), InvocationRouteCorpus.Value(direct[i].Cell.Demand().Value.Value));
                }
                else
                {
                    Assert.Same(general[i].Cell, direct[i].Cell);
                }
            }
            // A fresh environment per binding, as the general binder's.
            Assert.NotSame(direct, Complete(Bind(wide, supply, Evaluator.EvalCtx.Empty, false, false, null)).Value);
        }
    }

    // ── A head pushed without a head scope ──────────────────────────────────────────────────────────

    // A random parameter pattern list: captures (sometimes repeated, sometimes null), nested sequence, list and
    // unpacking groups, and group nodes shared across positions (a host DAG).
    private static List<ParameterPattern> RandomHead(Random random, int width)
    {
        var shared = new List<ParameterPattern>();
        ParameterPattern Item(int depth)
        {
            var roll = random.Next(10);
            if (depth < 3 && roll < 2)
            {
                var items = Enumerable.Range(0, 2 + random.Next(3)).Select(_ => Item(depth + 1)).ToArray();
                ParameterPattern group = random.Next(3) switch
                {
                    0 => new SequenceValueParameterPattern(items),
                    1 => new ListValueParameterPattern(items),
                    _ => new UnpackingParameterPattern(items),
                };
                shared.Add(group);
                return group;
            }
            if (roll == 2 && shared.Count > 0)
                return shared[random.Next(shared.Count)];
            if (roll == 3 && random.Next(3) == 0)
                return new CaptureParameterPattern(new ParameterDeclaration(null!));
            return new CaptureParameterPattern("n" + random.Next(width + 4));
        }
        return Enumerable.Range(0, width).Select(_ => Item(0)).ToList();
    }

    [Theory]
    [MemberData(nameof(Seeds))]
    public void HasCaptureNamed_IsMembershipInTheParamsProjection(int seed)
    {
        var random = new Random(104729 * seed);
        var head = RandomHead(random, 1 + random.Next(seed % 3 == 0 ? 200 : 30));
        var user = new Algorithm.User(null, head, [], [], [new Expr.Num(0)]);
        var projected = user.Params;
        foreach (var probe in projected.Concat(Names("n", head.Count + 6)).Concat(["", "missing", "N1", null!]).Distinct())
            Assert.Equal(Evaluator.ContainsOrdinal(projected, probe), ParameterPattern.HasCaptureNamed(head, probe));
    }

    public static TheoryData<int> ScopelessWidths => new() { 1, 8, Flat, Flat + 1, Indexed, 200 };

    [Theory]
    [MemberData(nameof(ScopelessWidths))]
    public void AHeadPushedWithoutAHeadScope_BindsItsOwnNames_AndReachesItsOwnersActivation(int width)
    {
        // G(c, d, g0, …) is activated; its step S(p0, …, d) is pushed without a head scope, as the loop planner
        // pushes a step whose body it classifies. S's own names are read from its context, G's other names from
        // G's activation, and an unknown name from the context — exactly the projection's answers.
        string[] ownerNames = ["c", "d", .. Names("g", Indexed)];
        var owner = new Algorithm.User(null, Captures(ownerNames), [], [], [new Expr.Num(1)]);
        var minted = Evaluator.Concat(ownerNames.Select((n, i) => (n, Ready(i))).ToArray(), []);
        var entered = Evaluator.EnterAlgorithmBody(owner, Evaluator.EvalCtx.Empty.WithNeedEnv(minted), [], parameterNames: ownerNames, invoked: true);
        var activation = entered.HeadScope!.Activation!;
        string[] stepNames = [.. Names("p", width), "d"];
        foreach (var head in new IReadOnlyList<ParameterPattern>[]
        {
            Captures(stepNames),
            // The same names under structure: the read walks the groups.
            [.. Captures(stepNames.Skip(2)), new SequenceValueParameterPattern(Captures(stepNames.Take(2)))],
        })
        {
            var step = new Algorithm.User(entered.HeadScope, head, [], [], [new Expr.Num(2)]);
            var scopeless = entered.Push(step);
            Assert.Null(scopeless.HeadScope);
            foreach (var probe in stepNames.Concat(ownerNames).Concat(["missing", "C", null!]))
            {
                ParameterActivation? expected = Evaluator.ContainsOrdinal(step.Params, probe) ? null
                    : Evaluator.ContainsOrdinal(ownerNames, probe) ? activation : null;
                Assert.Same(expected, CapturedParameterActivation(probe, scopeless));
            }
        }

        // A clause family and a builtin pushed without a head scope declare no name.
        var family = new Algorithm.Conditional(entered.HeadScope, [], [new CondBranch(new Pattern.Bind("c"), new Algorithm.User(null, [], [], [], [new Expr.Num(0)]))]);
        Assert.Same(activation, CapturedParameterActivation("c", entered.Push(family)));
        Assert.Null(CapturedParameterActivation("c", entered.Push(new Algorithm.Builtin(BuiltinId.sum))));
    }

    // ── The run's prepared heads ────────────────────────────────────────────────────────────────────

    [Fact]
    public void AWideStoredHead_IsPreparedOncePerList_ServedOnlyWhileUnchanged_AndPreparedAgainWhenEdited()
    {
        var cache = new Evaluator.NeedHeadPreparationCache();
        var stored = Captures(Names("p", 40)).ToList();
        var first = cache.Translate(stored);
        Assert.IsType<Evaluator.WideNeedLevel>(first);
        Assert.Equal(1, cache.Preparations);
        for (var i = 0; i < 50; i++)
            Assert.Same(first, cache.Translate(stored));
        Assert.Equal(1, cache.Preparations);

        // Another list of equal content is another head; the first stays valid.
        var copy = stored.ToList();
        var other = cache.Translate(copy);
        Assert.NotSame(first, other);
        Assert.Equal(first, other);
        Assert.Same(first, cache.Translate(stored));
        Assert.Equal(2, cache.Preparations);

        // Edits in place: each is observed, and the entry is replaced.
        (stored[0], stored[1]) = (stored[1], stored[0]);
        var swapped = cache.Translate(stored);
        Assert.Equal(["p1", "p0", "p2"], swapped.Take(3).Select(static p => p.Name));
        Assert.Same(swapped, cache.Translate(stored));
        (stored[0], stored[1]) = (stored[1], stored[0]);
        var restored = cache.Translate(stored);
        Assert.NotSame(first, restored);
        Assert.Equal(first, restored);
        // A replacement by an equal record is a new pattern: references decide.
        stored[5] = new CaptureParameterPattern("p5");
        var replaced = cache.Translate(stored);
        Assert.NotSame(restored, replaced);
        Assert.Same(stored[5], replaced[5].Original);
        // A kind change, an added and a removed pattern.
        stored[7] = new CaptureParameterPattern("p7", Kind: ParameterKind.Collecting);
        Assert.True(cache.Translate(stored)[7].Collecting);
        stored.Add(new CaptureParameterPattern("extra"));
        Assert.Equal(41, cache.Translate(stored).Count);
        stored.RemoveAt(0);
        Assert.Equal("p1", cache.Translate(stored)[0].Name);
        Assert.Equal(8, cache.Preparations);
        // Every edit replaced the list's entry: one entry per list, however often it was prepared.
        Assert.Equal(2, cache.EntryCount);

        // A structural pattern is never prepared: translated on every call, as before, and the list's stale entry is dropped.
        stored[3] = new SequenceValueParameterPattern(Captures(["a", "b"]));
        var structural = cache.Translate(stored);
        Assert.IsNotType<Evaluator.WideNeedLevel>(structural);
        Assert.NotSame(structural, cache.Translate(stored));
        Assert.Equal(8, cache.Preparations);
        Assert.Equal(1, cache.EntryCount);
        stored[3] = new CaptureParameterPattern("q3");
        Assert.Equal("q3", cache.Translate(stored)[3].Name);
        Assert.Equal(9, cache.Preparations);
        Assert.Equal(2, cache.EntryCount);
        // The other list was never edited: still served from its first preparation.
        Assert.Same(other, cache.Translate(copy));
        Assert.Equal(9, cache.Preparations);
        GC.KeepAlive(stored);
    }

    [Fact]
    public void ARunCacheReleasesTemporaryFlatBinderHeadsWhileTheHostFamilyIsAlive()
    {
        const int width = 40;
        var head = new Pattern.SequenceValue(Names("p", width).Select(static n => (Pattern)new Pattern.Bind(n)).ToArray());
        var body = new Algorithm.User(null, [], [], [], [new Expr.Param("p39")]);
        var family = new Algorithm.Conditional(null, [], [new CondBranch(head, body)]);
        var collect = HostOperation.Create("CollectHeads", (_, _) =>
        {
            GC.Collect();
            return new Result.Atom(0);
        });
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", family)],
            [.. Enumerable.Range(0, 25).Select(_ => WideCall(width)), new Expr.NativeCall(collect.NativeName, [])]));
        var (result, budget) = Evaluator.RunCountedObserved(program, hostOperations: HostOperations.Create(collect));
        Assert.True(result.IsOk);
        // Each host-family invocation synthesizes a temporary user-equivalent parameter list.
        // Keep the original AST and the run cache alive while collecting those lists.
        Assert.Equal(25, budget.HeadPreparations.Preparations);
        Assert.Equal(0, budget.HeadPreparations.EntryCount);
        GC.KeepAlive(program);
    }

    [Theory]
    [InlineData(Flat + 1)]
    [InlineData(Indexed)]
    [InlineData(130)]
    public void AWideCall_ReadsItsStoredHeadTwicePerCall_AndPreparesItOncePerRun(int width)
    {
        // Per call, the stored head is read once to validate the run's preparation and once for the Params projection
        // the body is entered with; the translation itself runs once per run. Before, each call also translated it,
        // reading every pattern twice more.
        (long Reads, int Preparations) Run(int calls, bool optimize)
        {
            var head = new FrameReadCountingList<ParameterPattern>(Captures(Names("p", width)));
            var callee = new Algorithm.User(null, head, [], [], [new Expr.Binary(BinaryOp.Add, new Expr.Param("p0"), new Expr.Param("p" + (width - 1)))]);
            Expr Call() => new Expr.Call(new Expr.Resolve("F"), OutputBundle.TakeOwnership(Enumerable.Range(1, width).Select(static i => (Expr)new Expr.Num(i)).ToArray()));
            var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", callee)], Enumerable.Range(0, calls).Select(_ => Call()).ToArray()));
            var (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: optimize);
            Assert.True(result.IsOk, result.IsOk ? "" : KatLangError.FromEvalError(result.Error).Message);
            return (head.Reads, budget.HeadPreparations.Preparations);
        }

        foreach (var optimize in new[] { false, true })
        {
            var (ten, tenPreparations) = Run(10, optimize);
            var (twenty, twentyPreparations) = Run(20, optimize);
            Assert.Equal(1, tenPreparations);
            Assert.Equal(1, twentyPreparations);
            Assert.Equal(2L * width, (twenty - ten) / 10);
            Assert.Equal(0, (twenty - ten) % 10);
        }
    }

    // ── Programs on every route ─────────────────────────────────────────────────────────────────────

    private static string Describe((EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) run)
    {
        var (result, budget) = run;
        var outcome = result.IsOk
            ? $"ok {InvocationRouteCorpus.Value(result.Value.Value)} n={result.Value.EmittedCount}"
            : $"err {result.Error.Code} | {KatLangError.FromEvalError(result.Error).Message.Replace("\n", " / ", StringComparison.Ordinal)} @{result.Error.Span}";
        return $"{outcome}\tsteps={budget.ConsumedSteps}\tcheckpoints={budget.ConsumedExpressionCheckpoints}\titems={budget.MaterializedItems}";
    }

    /// <summary>
    /// The plain value entry, the counted generic and optimized routes, the optimized route of a run that retains
    /// invocation plans, and the async twin: they agree on the outcome, steps, checkpoints and materialized items.
    /// Returns the counted outcome and the head preparations of the generic run.
    /// </summary>
    private static async Task<(string Outcome, int Preparations)> ObserveAllRoutes(Func<(Expr Program, HostOperations? Operations)> build)
    {
        var (plainProgram, plainOperations) = build();
        var plain = Evaluator.Run(plainProgram, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(), enableLoopOptimization: true, loopDiagnostics: null,
            enableSequencePipelineOptimization: true, sequenceDiagnostics: null, hostOperations: plainOperations);
        var (genericProgram, genericOperations) = build();
        var genericRun = Evaluator.RunCountedObserved(genericProgram, enableOptimizations: false, hostOperations: genericOperations);
        var generic = Describe(genericRun);
        var (optimizedProgram, optimizedOperations) = build();
        var optimized = Describe(Evaluator.RunCountedObserved(optimizedProgram, enableOptimizations: true, hostOperations: optimizedOperations));
        var (plannedProgram, plannedOperations) = build();
        string planned;
        using (InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()))
            planned = Describe(Evaluator.RunCountedObserved(plannedProgram, enableOptimizations: true, hostOperations: plannedOperations));
        var (twinProgram, twinOperations) = build();
        var twin = Describe(await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            twinProgram, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache(), hostOperations: twinOperations)));
        Assert.Equal(generic, optimized);
        Assert.Equal(generic, planned);
        Assert.Equal(generic, twin);
        Assert.Equal(generic.StartsWith("ok ", StringComparison.Ordinal), plain.IsOk);
        if (plain.IsOk)
            Assert.StartsWith($"ok {InvocationRouteCorpus.Value(plain.Value)} n=", generic, StringComparison.Ordinal);
        else
            Assert.StartsWith($"err {plain.Error.Code} ", generic, StringComparison.Ordinal);
        var preparations = genericRun.Budget.HeadPreparations.Preparations;
        return (generic, preparations);
    }

    private static async Task<(string Outcome, int Preparations)> ObserveSource(string source, HostOperations? operations = null)
    {
        var root = (await Parse(source, operations)).Root;
        return await ObserveAllRoutes(() => (new Expr.AlgorithmExpr(root), operations));
    }

    // A clean front end, with the host operations the source calls registered.
    private static Task<SourceProvenance> Parse(string source, HostOperations? operations)
        => SourceProvenance.ParseValidAsync(source, operations is null ? null : new RunOptions { HostOperations = operations });

    private static string List(string prefix, int from, int to) => string.Join(", ", Enumerable.Range(from, to - from + 1).Select(i => prefix + i));

    private static string Weighted(string prefix, int width) => "sum([" + string.Join(", ", Enumerable.Range(1, width).Select(i => $"{i} * {prefix}{i}")) + "])";

    private static long Sum(int width, Func<int, long> term) => Enumerable.Range(1, width).Sum(term);

    public static TheoryData<int> ProgramWidths => new() { 2, 8, Flat - 1, Flat, Flat + 1, Indexed - 1, Indexed, Indexed + 1, 64, 130 };

    [Theory]
    [MemberData(nameof(ProgramWidths))]
    public async Task PlainCollectingStructuralClauseAndCallbackHeads_BindByPosition_OnAllRoutes(int width)
    {
        var source = $"F({List("p", 1, width)}) = {Weighted("p", width)}\n"
            + $"C({List("p", 1, width)}, *rest) = {Weighted("p", width)} + 1000 * count(rest) + 1000000 * sum(rest)\n"
            + $"M({List("p", 1, width - 1)}, *rest, p{width}) = {Weighted("p", width)} + 1000 * count(rest)\n"
            + $"S(({List("p", 1, width)})) = {Weighted("p", width)}\n"
            + $"Q(0, {List("q", 1, width)}) = 0\n"
            + $"Q(k, {List("q", 1, width)}) = k + {Weighted("q", width)}\n"
            + $"F({List("", 1, width)})\n"
            + $"C({List("", 1, width)})\n"
            + $"C({List("", 1, width)}, 5, 6)\n"
            + $"M({List("", 1, width)})\n"
            + $"M({List("", 1, width - 1)}, 7, 8, 9, {width})\n"
            + $"S(({List("", 1, width)}))\n"
            + $"Q(0, {List("", 1, width)})\n"
            + $"Q(3, {List("", 1, width)})\n"
            + $"range(1, 3).map{{F({string.Join(", ", Enumerable.Repeat("n", width))})}}.sum\n";
        var (outcome, preparations) = await ObserveSource(source);
        var squares = Sum(width, i => (long)i * i);
        var triangle = (long)width * (width + 1) / 2;
        Assert.StartsWith($"ok ({squares}, {squares}, {squares + 2000 + 11_000_000}, {squares}, {squares + 3000}, {squares}, 0, {3 + squares}, {6 * triangle}) n=",
            outcome, StringComparison.Ordinal);
        // Every wide stored head an ordinary call bound was prepared once in the run: F (width patterns), C and M
        // (width + 1). S has one structural pattern, and a family's clause heads are prepared with the family.
        Assert.Equal((width > Flat ? 1 : 0) + (width + 1 > Flat ? 2 : 0), preparations);
    }

    [Theory]
    [MemberData(nameof(ProgramWidths))]
    public async Task RecursiveForwardingAndLoopSteps_RebindEveryRound_OnAllRoutes(int width)
    {
        // R recurses five times, rotating its head; G forwards it; L rotates its state four times as a loop step (planned
        // when optimized), and T's rows read the captured c through the planner's classification of its references.
        const int rounds = 5;
        var rotated = string.Join(", ", Enumerable.Range(2, width - 1).Select(i => "p" + i).Append("p1"));
        var source = $"R(k, {List("p", 1, width)}) = if(k == 0, {Weighted("p", width)}, R(k - 1, {rotated}))\n"
            + $"G({List("p", 1, width)}) = R({rounds}, {List("p", 1, width)})\n"
            + $"L({List("p", 1, width)}) = {rotated}\n"
            + "H(c) = {\n"
            + $"  T({List("p", 1, width)}) = {string.Join(", ", Enumerable.Range(1, width).Select(i => $"p{(i % width) + 1} + c"))}\n"
            + $"  first([T({List("", 1, width)}).repeat(2)*])\n"
            + "}\n"
            + $"G({List("", 1, width)})\n"
            + $"sum([L({List("", 1, width)}).repeat(4)*])\n"
            + $"L({List("", 1, width)}).repeat(4)\n"
            + "H(100)\n";
        var (outcome, _) = await ObserveSource(source);
        var recursive = Sum(width, i => i * (long)((i - 1 + rounds) % width + 1));
        var loop = string.Join(", ", Enumerable.Range(0, width).Select(i => (i + 4) % width + 1));
        // After two rounds T's first slot holds the original p((2 mod width) + 1), plus 2 * c.
        Assert.StartsWith($"ok ({recursive}, {(long)width * (width + 1) / 2}, ({loop}), {2 % width + 1 + 200}) n=", outcome, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(Flat)]
    [InlineData(Flat + 1)]
    [InlineData(Indexed)]
    [InlineData(64)]
    public async Task ArityPrecedesBinding_AndARepeatedNameKeepsNeed04_InAWideHead_OnAllRoutes(int width)
    {
        string Observed((string Outcome, int Preparations) observation) => observation.Outcome;
        var plain = $"F({List("p", 1, width)}) = p1 + p{width}\n";
        var tooFew = Observed(await ObserveSource(plain + $"F({List("", 1, width - 1)})\n"));
        Assert.StartsWith($"err ArityMismatch | Callable `F({List("p", 1, width)})` expects {width} arguments, but was called with {width - 1} arguments.", tooFew, StringComparison.Ordinal);
        var tooMany = Observed(await ObserveSource(plain + $"F({List("", 1, width + 1)})\n"));
        Assert.StartsWith($"err ArityMismatch | Callable `F({List("p", 1, width)})` expects {width} arguments, but was called with {width + 1} arguments.", tooMany, StringComparison.Ordinal);

        var collecting = $"C({List("p", 1, width)}, *rest) = p1 + count(rest)\n";
        var variadic = Observed(await ObserveSource(collecting + $"C({List("", 1, width - 1)})\n"));
        Assert.StartsWith("err ArityMismatch | ", variadic, StringComparison.Ordinal);
        Assert.Contains($"*rest)` expects at least {width} items, but received {width - 1} items.", variadic, StringComparison.Ordinal);

        // A callback keeps the plain arity shape, named by its role.
        var callback = Observed(await ObserveSource(plain + "range(1, 2).map(F).sum\n"));
        Assert.StartsWith("err ArityMismatch | ", callback, StringComparison.Ordinal);

        // The repeated name: the arity decision first, then NEED-04's value agreement.
        var repeated = $"P({List("p", 1, width)}, p1) = p1 + 1000 * p{width}\n";
        Assert.StartsWith($"ok {1 + 1000L * width} n=", Observed(await ObserveSource(repeated + $"P({List("", 1, width)}, 1)\n")), StringComparison.Ordinal);
        var refusedCount = Observed(await ObserveSource(repeated + $"P({List("", 1, width)})\n"));
        Assert.StartsWith($"err ArityMismatch | Callable `P({List("p", 1, width)}, p1)` expects {width + 1} arguments", refusedCount, StringComparison.Ordinal);
        var refusedValue = Observed(await ObserveSource(repeated + $"P({List("", 1, width)}, 2)\n"));
        Assert.StartsWith("err ArityMismatch", refusedValue, StringComparison.Ordinal);
        Assert.Contains("repeated parameter 'p1' requires equal arguments", refusedValue, StringComparison.Ordinal);

        // A family: no clause accepts the count, then a literal non-match falls through to the general clause.
        var family = $"Q(0, {List("q", 1, width)}) = 0\nQ(k, {List("q", 1, width)}) = k\n";
        var familyArity = Observed(await ObserveSource(family + $"Q({List("", 1, width)})\n"));
        Assert.StartsWith($"err ArityMismatch | ", familyArity, StringComparison.Ordinal);
        Assert.StartsWith("ok 7 n=", Observed(await ObserveSource(family + $"Q(7, {List("", 1, width)})\n")), StringComparison.Ordinal);
        var literalOnly = $"Z(0, {List("q", 1, width)}) = 0\n";
        var unmatched = Observed(await ObserveSource(literalOnly + $"Z(7, {List("", 1, width)})\n"));
        Assert.StartsWith("err NoMatchingBranch", unmatched, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(3)]
    [InlineData(Flat + 1)]
    [InlineData(Indexed + 1)]
    public async Task AWideHead_DemandsItsArgumentsInTheBodysOrder_AndACollectorInSliceOrder_OnAllRoutes(int width)
    {
        // Every argument is a host operation that records its demand: binding a distinct-name level demands
        // nothing, so the record is the body's read order — p3, p1, p2, then the collected slice in order.
        var log = new List<string>();
        HostOperation Mark(int i) => HostOperation.Create("Mark" + i, (_, _) => { log.Add("m" + i); return new Result.Atom(i); });
        var marks = Enumerable.Range(1, width + 2).Select(Mark).ToArray();
        var operations = HostOperations.Create(marks);
        var arguments = string.Join(", ", Enumerable.Range(1, width + 2).Select(static i => $"Mark{i}()"));
        var source = $"F({List("p", 1, width)}, *rest) = p3 * 100 + p1 * 10 + p2 + 1000 * sum(rest)\n"
            + $"Q(0, {List("q", 1, width)}, x) = 0\n"
            + $"Q(k, {List("q", 1, width)}, x) = q2 + k\n"
            + $"F({arguments})\n"
            + $"Q(Mark1(), {string.Join(", ", Enumerable.Range(1, width + 1).Select(static i => $"Mark{i}()"))})\n";
        var root = (await Parse(source, operations)).Root;
        var routes = new List<string[]>();
        foreach (var run in new Func<Task<EvalResult<Evaluator.CountedResult>>>[]
        {
            () => Task.FromResult(Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(root), enableOptimizations: false, hostOperations: operations).Result),
            () => Task.FromResult(Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(root), enableOptimizations: true, hostOperations: operations).Result),
            () =>
            {
                using (InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()))
                    return Task.FromResult(Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(root), enableOptimizations: true, hostOperations: operations).Result);
            },
            async () => (await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(root),
                zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache(), hostOperations: operations))).Result,
        })
        {
            log.Clear();
            var result = await run();
            Assert.True(result.IsOk, result.IsOk ? "" : KatLangError.FromEvalError(result.Error).Message);
            Assert.Equal($"({312 + 1000L * ((width + 1) + (width + 2))}, {2 + 1})", InvocationRouteCorpus.Value(result.Value.Value));
            routes.Add([.. log]);
        }
        // F: p3, p1, p2, then rest's two cells; Q: the literal clause demands its first cell, the general clause reads q2.
        string[] expected = ["m3", "m1", "m2", "m" + (width + 1), "m" + (width + 2), "m1", "m2"];
        Assert.All(routes, route => Assert.Equal(expected, route));
    }

    [Theory]
    [InlineData("plain")]
    [InlineData("counted")]
    [InlineData("async")]
    public async Task ACancellationDuringAWideCall_StopsAtTheDemandingRead_OnAllRoutes(string route)
    {
        using var cancellation = new CancellationTokenSource();
        var seen = new List<string>();
        var operations = HostOperations.Create(
            HostOperation.Create("Unused", (_, _) => { seen.Add("unused"); return new Result.Atom(1); }),
            HostOperation.Create("Stop", (_, _) => { seen.Add("stop"); cancellation.Cancel(); return new Result.Atom(2); }));
        const int width = Indexed + 3;
        var names = List("p", 1, width);
        var arguments = string.Join(", ", Enumerable.Repeat("Unused()", width - 1).Append("Stop()"));
        var source = $"F({names}, *rest) = p{width} + p1\nQ(0, {names}) = 0\nQ(k, {names}) = p{width}\nF({arguments})\nQ(1, {arguments})\n";
        var program = new Expr.AlgorithmExpr((await Parse(source, operations)).Root);
        var token = cancellation.Token;
        var error = route switch
        {
            "plain" => Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.Run(program, operations, null, null, token)),
            "counted" => Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(program, hostOperations: operations, cancellationToken: token)),
            "async" => await Assert.ThrowsAnyAsync<OperationCanceledException>(() => AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache(),
                    hostOperations: operations, cancellationToken: token))),
            _ => throw new ArgumentOutOfRangeException(nameof(route)),
        };
        Assert.Equal(token, error.CancellationToken);
        // The body's first read demands the last argument, whose host operation cancels: nothing else ran.
        Assert.Equal(["stop"], seen);
    }

    public static TheoryData<string, string> WideHeadEdits => new()
    {
        // The edit F's caller-owned head receives between two calls of one run, and the run's outcome.
        { "swap", "ok (" },
        { "rename", "err UnknownName | " },
        { "collect", "err TypeMismatch | " },
        { "add", "err ArityMismatch | " },
        { "remove", "err ArityMismatch | " },
        { "repeat", "err ArityMismatch | " },
        { "structure", "err TypeMismatch | " },
    };

    private static void Edit(List<ParameterPattern> head, string edit)
    {
        switch (edit)
        {
            case "swap": (head[0], head[1]) = (head[1], head[0]); break;
            case "rename": head[0] = new CaptureParameterPattern("renamed"); break;
            case "collect": head[^1] = new CaptureParameterPattern(((CaptureParameterPattern)head[^1]).Name, Kind: ParameterKind.Collecting); break;
            case "add": head.Add(new CaptureParameterPattern("extra")); break;
            case "remove": head.RemoveAt(head.Count - 1); break;
            case "repeat": head[1] = new CaptureParameterPattern("p0"); break;
            case "structure": head[2] = new SequenceValueParameterPattern(Captures(["s", "t"])); break;
            default: throw new ArgumentOutOfRangeException(nameof(edit));
        }
    }

    // F(p0, …) = p0 * 10 + p1 + 1000 * p_last over a caller-owned list, called with 1, 2, …, width.
    private static (Algorithm.User Callee, List<ParameterPattern> Head) EditableCallee(int width)
    {
        var head = Captures(Names("p", width)).ToList();
        Expr body = new Expr.Binary(BinaryOp.Add,
            new Expr.Binary(BinaryOp.Add, new Expr.Binary(BinaryOp.Mul, new Expr.Param("p0"), new Expr.Num(10)), new Expr.Param("p1")),
            new Expr.Binary(BinaryOp.Mul, new Expr.Param("p" + (width - 1)), new Expr.Num(1000)));
        return (new Algorithm.User(null, head, [], [], [body]), head);
    }

    private static Expr WideCall(int width)
        => new Expr.Call(new Expr.Resolve("F"), OutputBundle.TakeOwnership(Enumerable.Range(1, width).Select(static i => (Expr)new Expr.Num(i)).ToArray()));

    [Theory]
    [MemberData(nameof(WideHeadEdits))]
    public async Task AHostEditOfAWideStoredHead_BetweenTwoCallsOfOneRun_IsObservedByTheSecondCall(string edit, string expected)
    {
        const int width = Indexed + 8;
        (Expr Program, HostOperations? Operations) Build()
        {
            var (callee, head) = EditableCallee(width);
            var operation = HostOperation.Create("EditHead", (_, _) => { Edit(head, edit); return new Result.Atom(0); });
            var program = new Expr.AlgorithmExpr(new Algorithm.User(
                null, [], [], [new Property("F", callee)], [WideCall(width), new Expr.NativeCall(operation.NativeName, []), WideCall(width)]));
            return (program, HostOperations.Create(operation));
        }

        var (outcome, preparations) = await ObserveAllRoutes(Build);
        Assert.StartsWith(expected, outcome, StringComparison.Ordinal);
        if (edit == "swap")
            Assert.StartsWith($"ok ({12 + 1000L * width}, 0, {21 + 1000L * width}) n=", outcome, StringComparison.Ordinal);
        // The first call prepared the head; an edited list is prepared again unless it no longer is a capture list.
        Assert.Equal(edit == "structure" ? 1 : 2, preparations);
    }

    [Theory]
    [MemberData(nameof(WideHeadEdits))]
    public async Task AHostEditOfAWideStoredHead_BetweenRuns_IsObservedByTheNextRun(string edit, string expected)
    {
        // ONE program over ONE caller-owned list, run, edited, run again: each run equals a program built in that state.
        const int width = Indexed + 8;
        var (callee, head) = EditableCallee(width);
        Expr Program(Algorithm.User f) => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", f)], [WideCall(width), WideCall(width)]));
        var program = Program(callee);
        var before = await ObserveAllRoutes(() => (program, null));
        Assert.StartsWith($"ok ({12 + 1000L * width}, {12 + 1000L * width}) n=", before.Outcome, StringComparison.Ordinal);
        Assert.Equal(1, before.Preparations);

        Edit(head, edit);
        var after = await ObserveAllRoutes(() => (program, null));
        var (control, controlHead) = EditableCallee(width);
        Edit(controlHead, edit);
        Assert.Equal((await ObserveAllRoutes(() => (Program(control), null))).Outcome, after.Outcome);
        Assert.StartsWith(expected, after.Outcome, StringComparison.Ordinal);
        Assert.Equal(edit == "structure" ? 0 : 1, after.Preparations);
    }

    [Theory]
    [InlineData(Flat)]
    [InlineData(Flat + 1)]
    [InlineData(64)]
    public async Task EveryCallOfAWideHead_IsItsOwnActivation_ForItsInnerProperties_OnAllRoutes(int width)
    {
        // V is an inner property of F: each call owns its binding (INNER-PROPERTY LIFETIME), whether F binds directly,
        // through the prepared translation or as a callback; a wide loop step's rounds and a clause's calls likewise.
        var ticks = 0;
        var operations = HostOperations.Create(HostOperation.Create("Tick", (_, _) => new Result.Atom(++ticks)));
        var source = $"F({List("p", 1, width)}) = {{\n  V = Tick()\n  V * 1000 + p1 + p{width}\n}}\n"
            + $"Q(0, {List("q", 1, width)}) = 0\nQ(k, {List("q", 1, width)}) = {{\n  W = Tick()\n  W * 1000\n}}\n"
            + $"F({List("", 1, width)})\nF({List("", 1, width)})\n"
            + $"range(1, 2).map{{F({string.Join(", ", Enumerable.Repeat("n", width))})}}\n"
            + $"Q(1, {List("", 1, width)})\nQ(1, {List("", 1, width)})\n";
        var root = (await Parse(source, operations)).Root;
        var (outcome, _) = await ObserveAllRoutes(() =>
        {
            ticks = 0;
            return (new Expr.AlgorithmExpr(root), operations);
        });
        Assert.StartsWith($"ok ({1000 + 1 + width}, {2000 + 1 + width}, [{3000 + 2}, {4000 + 4}], 5000, 6000) n=", outcome, StringComparison.Ordinal);
    }

    [Fact]
    public void TheRunsPreparation_DiesWithTheRun_AndRetainsNoHead()
    {
        // The preparation is the run's: nothing static keeps the stored head, its translation or the cache.
        [MethodImpl(MethodImplOptions.NoInlining)]
        static (WeakReference Head, WeakReference Cache, int Preparations) RunOnce()
        {
            var (callee, head) = EditableCallee(Indexed + 8);
            var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", callee)], [WideCall(Indexed + 8), WideCall(Indexed + 8)]));
            var (result, budget) = Evaluator.RunCountedObserved(program);
            Assert.True(result.IsOk);
            return (new WeakReference(head), new WeakReference(budget.HeadPreparations), budget.HeadPreparations.Preparations);
        }

        var (head, cache, preparations) = RunOnce();
        Assert.Equal(1, preparations);
        for (var attempt = 0; attempt < 10 && (head.IsAlive || cache.IsAlive); attempt++)
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();
        }
        Assert.False(head.IsAlive, "the stored head outlived its program");
        Assert.False(cache.IsAlive, "the run's head preparations outlived the run");
    }

    // ── Allocation (isolated child process) ─────────────────────────────────────────────────────────

    private static long Bytes(Action action)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        action();
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    // An async method's state machine is a class in a Debug build (allocated on every call) and a struct in Release.
    private static long StateMachineBytes(string method)
    {
        var type = typeof(Evaluator).GetMethod(method, BindingFlags.NonPublic | BindingFlags.Static)!
            .GetCustomAttribute<AsyncStateMachineAttribute>()!.StateMachineType;
        return type.IsValueType ? 0 : InstanceSize.Of(type);
    }

    [Fact]
    public void WideBindingsAllocateOnlyTheirEnvironment_PreparedHeadsAndScopelessReadsNothing_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var binder = StateMachineBytes("BindAcceptedNeedPatterns");
        foreach (var width in new[] { Flat + 1, Indexed, 300 })
        {
            var names = Names("p", width);
            var supply = Enumerable.Range(0, width).Select(Ready).ToArray();
            var ctx = Evaluator.EvalCtx.Empty;
            IReadOnlyList<(string Name, NeedCell Cell)>? bound = null;
            void AllocateEnvironment() => bound = new (string Name, NeedCell Cell)[width];
            AllocateEnvironment();
            var environment = Bytes(AllocateEnvironment);

            // A distinct-name level: exactly its environment (beside a Debug build's binder state machine), on both
            // binder routes and in both modes, once its shape is decided.
            var level = new Evaluator.WideNeedLevel(names.Select(static n => new Evaluator.NeedPattern(n)).ToArray());
            _ = Complete(Bind(level, supply, ctx, false, false, null));
            Assert.Equal(binder + environment, Bytes(() => bound = Complete(Bind(level, supply, ctx, false, false, null)).Value));
            Assert.Equal(binder + environment, Bytes(() => bound = Complete(Bind(level, supply, ctx, true, true, null)).Value));
            Assert.Equal(width, bound!.Count);

            // A collecting one: its environment, the slice and the collector's cell.
            var collecting = new Evaluator.WideNeedLevel(names.Select(static (n, i) => new Evaluator.NeedPattern(n, Collecting: i == 2)).ToArray());
            var longer = Enumerable.Range(0, width + 3).Select(Ready).ToArray();
            _ = Complete(Bind(collecting, longer, ctx, false, false, null));
            var slice = longer[2..6];
            _ = CollectorCell(slice, ctx);
            var collector = Bytes(() => _ = new NeedCell[slice.Length]) + Bytes(() => _ = CollectorCell(slice, ctx));
            Assert.Equal(binder + environment + collector, Bytes(() => bound = Complete(Bind(collecting, longer, ctx, false, false, null)).Value));

            // A wide literal clause head: its environment of names only.
            var literal = new Evaluator.WideNeedLevel([new(Literal: new Pattern.LitInt(0)), .. names.Skip(1).Select(static n => new Evaluator.NeedPattern(n))]);
            var zero = new[] { Ready(0) }.Concat(supply.Skip(1)).ToArray();
            Assert.True(RecognizesLiteralHead(literal, zero));
            _ = LiteralHead(literal, zero, ctx);
            void AllocateNameEnvironment() => bound = new (string Name, NeedCell Cell)[width - 1];
            AllocateNameEnvironment();
            var namesOnly = Bytes(AllocateNameEnvironment);
            Assert.Equal(namesOnly, Bytes(() => bound = LiteralHead(literal, zero, ctx).Value));
            Assert.Equal(0, Bytes(() => _ = RecognizesLiteralHead(literal, zero)));

            // A prepared stored head served again: validated without allocating.
            var cache = new Evaluator.NeedHeadPreparationCache();
            IReadOnlyList<ParameterPattern> stored = Captures(names);
            var prepared = cache.Translate(stored);
            IReadOnlyList<Evaluator.NeedPattern>? served = null;
            Assert.Equal(0, Bytes(() => served = cache.Translate(stored)));
            Assert.Same(prepared, served);

            // A structural pattern at the end of a wide top-level head goes directly to the
            // general translation, without allocating an unused flat snapshot on each call.
            ParameterPattern[] structural = [.. stored, new ListValueParameterPattern(Captures(["item"]))];
            _ = NeedParameterPatterns(structural);
            _ = cache.Translate(structural);
            Assert.Equal(Bytes(() => served = NeedParameterPatterns(structural)), Bytes(() => served = cache.Translate(structural)));

            // A scopeless user head's read of its own name, and of a name it does not declare.
            var step = new Algorithm.User(null, stored, [], [], [new Expr.Num(0)]);
            var scopeless = ctx.Push(step);
            var last = "p" + (width - 1);
            _ = CapturedParameterActivation(last, scopeless);
            Assert.Equal(0, Bytes(() => _ = CapturedParameterActivation(last, scopeless)));
            Assert.Equal(0, Bytes(() => _ = CapturedParameterActivation("missing", scopeless)));
        }

        GcIsolatedAllocation.Complete();
    }
}
