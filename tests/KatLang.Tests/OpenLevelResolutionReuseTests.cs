using System.Reflection;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// A level's <c>open</c> list is resolved ONCE PER LEVEL STATE, not once per read
/// (<c>Evaluator.ResolvedOpenLevel</c>, implementation-only, November 2026). Every lexical read that misses
/// structurally consults the open levels of its chain; it formerly resolved every target of each consulted
/// level again, so <c>R</c> reads of a level of <c>K</c> targets resolved <c>R·K</c> targets. A level's
/// providers are a pure function of the level object and the run, so they are memoized on the level's
/// runtime state — an activation, the static head level of a body entry, or a static wiring of a declaring
/// scope — and reused by every later read of that state, while a failed resolution is memoized nowhere and a
/// host-constructed level is never written. Counts come from the run's <see cref="EvaluationObservations"/>
/// on a prepared root, on the synchronous route and the forced async twin alike
/// (<see cref="OpenProviderIndexing.OnBothRoutesAsync(string)"/>): <c>Levels</c> counts resolutions,
/// <c>Consultations</c> reads of a nonempty level, <c>Reuses</c> reads a memo served.
/// </summary>
public class OpenLevelResolutionReuseTests
{
    // ── Programs ────────────────────────────────────────────────────────────────────────────────

    /// <summary><c>open M0, …, M{K−1}</c> with <c>Mi = { public Vi = i }</c> (or <c>public Fi(x) = x + i</c>).</summary>
    private static string Opening(int width, bool callable)
        => $"open {string.Join(", ", Enumerable.Range(0, width).Select(static i => $"M{i}"))}\n"
            + string.Concat(Enumerable.Range(0, width).Select(i => callable
                ? $"M{i} = {{ public F{i}(x) = x + {i} }}\n"
                : $"M{i} = {{ public V{i} = {i} }}\n"));

    /// <summary>The <paramref name="reads"/> opened names read in turn, cycling through the <paramref name="width"/> providers.</summary>
    private static IEnumerable<int> Cycle(int width, int reads) => Enumerable.Range(0, reads).Select(read => read % width);

    private static string Read(int provider, bool callable) => callable ? $"F{provider}(0)" : $"V{provider}";

    /// <summary>One row of <paramref name="reads"/> opened reads at the root, which consult the root's level.</summary>
    private static string RootReads(int width, int reads, bool callable)
        => Opening(width, callable) + $"[{string.Join(", ", Cycle(width, reads).Select(i => Read(i, callable)))}]";

    private static string Values(int width, int reads) => $"ok L[{string.Join(", ", Cycle(width, reads))}]";

    // Index work of ONE resolution of a level of K distinct declarations (OpenProviderIdentityTests).
    private static long KeyComparisons(int width) => width <= Evaluator.OpenProviderLinearIndexLimit ? width * (width - 1) / 2 : 0;

    // ── R reads of one level state resolve it once ──────────────────────────────────────────────

    [Theory]
    [InlineData(1, 1)]
    [InlineData(1, 5)]
    [InlineData(2, 7)]
    [InlineData(8, 3)]
    [InlineData(8, 24)]
    [InlineData(9, 1)]
    [InlineData(9, 40)]
    [InlineData(33, 100)]
    public async Task ReadsOfOneLevelState_ResolveItsTargetsOnce_HoweverManyReads(int width, int reads)
    {
        foreach (var callable in new[] { false, true })
        {
            // Formerly `reads` resolutions of `width` targets each (Levels = reads, Entries = reads·width).
            var observed = await OpenProviderIndexing.OnBothRoutesAsync(RootReads(width, reads, callable));
            Assert.Equal(
                new OpenProviderIndexing.Observation(Values(width, reads), 1, width, KeyComparisons(width), 0, 0, reads, reads - 1),
                observed);
        }
    }

    /// <summary>
    /// The width series of the brief (<c>R = K</c> reads of a level of <c>K</c> targets): the work — targets
    /// resolved and indexed, index probes, identity comparisons, and level consultations — is exactly
    /// <c>K + R</c>, so it doubles with the width, where per-read re-resolution made it <c>R·K + R</c>.
    /// </summary>
    [Fact]
    public async Task WidthSeries_ResolutionWorkIsLinearInReadsPlusTargets()
    {
        long? previous = null;
        foreach (var width in new[] { 16, 32, 64, 128, 256, 512 })
        {
            foreach (var callable in new[] { false, true })
            {
                var observed = await OpenProviderIndexing.OnBothRoutesAsync(RootReads(width, width, callable));
                Assert.Equal(1, observed.Levels);
                var work = observed.Entries + observed.KeyComparisons + observed.IdentityComparisons + observed.Consultations;
                Assert.Equal(2L * width, work);
                if (!callable && previous is { } half)
                    Assert.Equal(2 * half, work);
                if (!callable)
                    previous = work;
            }
        }
    }

    // ── Which state a read belongs to ───────────────────────────────────────────────────────────

    [Fact]
    public async Task AnActivatedLevel_IsResolvedOncePerActivation_NeverAcrossActivations()
    {
        // `F(z)`'s own body opens the providers: each call is a fresh activation whose K reads resolve
        // its level once. Three calls are three resolutions — the memo is never shared between them.
        const int width = 5, calls = 3;
        var body = string.Join(" + ", Enumerable.Range(0, width).Select(static i => $"V{i}"));
        var source = string.Concat(Enumerable.Range(0, width).Select(static i => $"M{i} = {{ public V{i} = {i} }}\n"))
            + $"F(z) = {{\n    open {string.Join(", ", Enumerable.Range(0, width).Select(static i => $"M{i}"))}\n    {body} + z\n}}\n"
            + $"[{string.Join(", ", Enumerable.Range(1, calls).Select(static c => $"F({c})"))}]";
        var observed = await OpenProviderIndexing.OnBothRoutesAsync(source);
        Assert.Equal(
            new OpenProviderIndexing.Observation("ok L[11, 12, 13]", calls, calls * width, calls * KeyComparisons(width), 0, 0, calls * width, calls * (width - 1)),
            observed);
    }

    [Fact]
    public async Task TheEntrysLevel_IsSharedByTheBodiesWiredUnderIt()
    {
        // The root entry's static head level is the parent of every `G` the root's rows wire, so the
        // reads inside each call of `G` consult that ONE level state: one resolution for the whole run,
        // however many calls and reads.
        const int width = 4, calls = 6;
        var source = Opening(width, callable: false)
            + "G(x) = V0 + V3 + x\n"
            + $"[{string.Join(", ", Enumerable.Range(1, calls).Select(static c => $"G({c})"))}]";
        var observed = await OpenProviderIndexing.OnBothRoutesAsync(source);
        Assert.Equal(
            new OpenProviderIndexing.Observation("ok L[4, 5, 6, 7, 8, 9]", 1, width, KeyComparisons(width), 0, 0, 2 * calls, 2 * calls - 1),
            observed);
    }

    [Fact]
    public async Task BothFormsOfOneLevel_ShareItsState_InEitherOrder()
    {
        // The head's own rows read the level as the HEAD's level, the bodies wired under it read it as an
        // ENCLOSING level; whichever reads first resolves it and the other form reuses the same providers.
        const int width = 4;
        var headFirst = await OpenProviderIndexing.OnBothRoutesAsync(Opening(width, callable: false) + "G(x) = V0 + V3 + x\n[V1, G(1), V2, G(2)]");
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[1, 4, 2, 5]", 1, width, KeyComparisons(width), 0, 0, 6, 5), headFirst);
        var enclosingFirst = await OpenProviderIndexing.OnBothRoutesAsync(Opening(width, callable: false) + "G(x) = V0 + V3 + x\n[G(1), V1]");
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[4, 1]", 1, width, KeyComparisons(width), 0, 0, 3, 2), enclosingFirst);

        // An ACTIVATED level whose dotted target's members capture the activation's parameter: the
        // resolution's access checks are judged inside the activation, and the nested `G` reuses the
        // providers the head's first read resolved — once per call of `F`.
        const string captured = "F(p) = {\n    open Lib.Sub\n    Lib = {\n        public Sub = {\n            public X = p\n        }\n    }\n"
            + "    G(q) = X + q\n    [X, G(1), X]\n}\n[F(10), F(20)]";
        var activated = await OpenProviderIndexing.OnBothRoutesAsync(captured);
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[L[10, 11, 10], L[20, 21, 20]]", 2, 2, 0, 0, 0, 6, 4), activated);
        Assert.Equal("ok", (await SixRouteAgreement.OnEveryRouteAsync(captured)).Kind);
    }

    [Fact]
    public async Task AFallbackThroughAnEnclosingLevel_ReusesItsState_AcrossCalls()
    {
        // A dotted route: `q.X` misses on the number and falls back to the lexical `X(q)`, which consults
        // `A`'s level from inside each `K` call; `A`'s entry resolves it once (a transparent reference
        // and the dotted path to the same declaration stay one provider).
        const string source = "Lib = {\n    public Sub = {\n        public X(v) = v + 10\n    }\n}\nRef = Lib.Sub\n"
            + "A = {\n    open Ref, Lib.Sub\n    K(q) = q.X\n    [K(1), K(2), K(3)]\n}\nA";
        var observed = await OpenProviderIndexing.OnBothRoutesAsync(source);
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[11, 12, 13]", 1, 2, 1, 1, 0, 3, 2), observed);
        Assert.Equal("ok", (await SixRouteAgreement.OnEveryRouteAsync(source)).Kind);
    }

    [Fact]
    public async Task TransparentReferencesAndDottedTargets_KeepTheirProvidersAndOrder_WhenReused()
    {
        // `A = Lib` opens Lib's namespace, `Ref = Lib.Sub` and `Lib.Sub` are ONE provider named by its
        // first target; every read after the first is served by the root entry's memo with the same
        // selection, and the ambiguity of a name two providers offer still names both in order.
        const string declarations = "Lib = {\n    public Sub = {\n        public X = 1\n        public Y = 2\n    }\n    public Z = 3\n    public Y = 4\n}\n"
            + "Ref = Lib.Sub\nA = Lib\n";
        var ok = await OpenProviderIndexing.OnBothRoutesAsync("open Ref, A, Lib.Sub\n" + declarations + "[X, Z, X, Z, X]");
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[1, 3, 1, 3, 1]", 1, 3, 2, 1, 0, 5, 4), ok);

        // The same level read through K's fallback: `q.Y` is offered by both Ref (Sub) and A (Lib).
        var ambiguous = await OpenProviderIndexing.OnBothRoutesAsync(
            declarations + "B = {\n    open Ref, A, Lib.Sub\n    K(q) = q.Y\n    [X, Z, K(0)]\n}\nB");
        Assert.Contains("AmbiguousOpen(Y: Ref, A) @ ", ambiguous.Outcome, StringComparison.Ordinal);
        Assert.Equal((1, 3, 3, 2), (ambiguous.Levels, ambiguous.Entries, ambiguous.Consultations, ambiguous.Reuses));
    }

    /// <summary>
    /// A host-built root opening <paramref name="width"/> inline blocks (<c>(inline#i)</c>): block 2 and
    /// block 7 publicly offer <c>Z</c>, block 5 offers a PRIVATE <c>Z</c> before two public ones and two
    /// public <c>Y</c>s, and every block offers its own <c>Wi</c>.
    /// </summary>
    private static Expr ManyBlocks(int width, params Expr[] rows)
    {
        static Property Member(string name, decimal value, bool isPublic = true) => new(name, Value(value), isPublic);
        var opens = Enumerable.Range(0, width).Select(i =>
        {
            List<Property> members = i switch
            {
                2 or 7 => [Member("Z", i)],
                5 => [Member("Z", 50, isPublic: false), Member("Z", 5), Member("Z", 55), Member("Y", 1), Member("Y", 2)],
                _ => [],
            };
            members.Add(Member($"W{i}", i));
            return (Expr)new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], members, OutputBundle.Empty));
        }).ToArray();
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], opens, [], new OutputBundle(rows)));
    }

    [Theory]
    [InlineData(8)]
    [InlineData(12)]
    public async Task TheMemberIndexOfAWideLevel_SelectsExactlyWhatTheScanSelects(int width)
    {
        // 8 providers scan on every read; 12 index their public members once. Either way a provider
        // offers its FIRST public member of a name, and an ambiguity names every offering provider in
        // written order.
        var last = width - 1;
        var reads = await OpenProviderIndexing.OnBothRoutesAsync(
            ManyBlocks(width, new Expr.Resolve("Y"), new Expr.Resolve("W0"), new Expr.Resolve($"W{last}"), new Expr.Resolve("Y")));
        Assert.Equal($"ok S[1, 0, {last}, 1]", reads.Outcome);
        Assert.Equal((1, width, 4, 3), (reads.Levels, reads.Entries, reads.Consultations, reads.Reuses));

        var ambiguous = await OpenProviderIndexing.OnBothRoutesAsync(ManyBlocks(width, new Expr.Resolve("W3"), new Expr.Resolve("Z")));
        Assert.Contains("AmbiguousOpen(Z: (inline#2), (inline#5), (inline#7)) @ ", ambiguous.Outcome, StringComparison.Ordinal);
        Assert.Equal((1, 2, 1), (ambiguous.Levels, ambiguous.Consultations, ambiguous.Reuses));
    }

    // ── Failures, host levels and copies ────────────────────────────────────────────────────────

    private static readonly Property[] Libraries =
    [
        new("Lib", new Algorithm.User(null, [], [], [new Property("V", Value(1), IsPublic: true)], OutputBundle.Empty)),
        new("Other", new Algorithm.User(null, [], [], [new Property("W", Value(2), IsPublic: true)], OutputBundle.Empty)),
    ];

    private static Algorithm.User Value(decimal n) => new(null, [], [], [], [new Expr.Num(n)]);

    private static Expr Named(string name, int column) => new Expr.Resolve(name) { Span = new(1, column, 1, column + name.Length) };

    private delegate EvalResult<Algorithm> ResolveNamed(string name, SourceSpan? span, Evaluator.EvalCtx ctx);

    /// <summary>The evaluator's callee resolution of a bare name in a context (<c>Evaluator.ResolveNamedAlgorithm</c>).</summary>
    private static readonly ResolveNamed Resolve = typeof(Evaluator)
        .GetMethod("ResolveNamedAlgorithm", BindingFlags.NonPublic | BindingFlags.Static)!
        .CreateDelegate<ResolveNamed>();

    /// <summary>A run context observed by <paramref name="observations"/>, below a stand-in prelude level.</summary>
    private static Evaluator.EvalCtx ObservedRun(EvaluationObservations observations)
        => new(
            [new Algorithm.User(null, [], [], [], OutputBundle.Empty)],
            null,
            new Evaluator.RunServices(
                UncachedZeroArgPropertyResultCache.Instance, UncachedDeconstructionBindingCache.Instance,
                EnableLoopOptimization: true, LoopDiagnostics: null,
                EnableSequencePipelineOptimization: true, SequenceDiagnostics: null,
                observations),
            EvaluationBudget.Create(null));

    [Fact]
    public void AFailedResolution_IsMemoizedNowhere_SoALaterReadReportsTheSameError()
    {
        // Two reads in ONE entry of a body whose later target fails: each read resolves the level again
        // and reports the same first failure in its open frame at its span; nothing is indexed or reused.
        var observations = new EvaluationObservations();
        var failing = new Algorithm.User(null, [], [Named("Lib", 6), Named("Gone", 11), Named("Other", 17)], Libraries, OutputBundle.Empty);
        var entry = Evaluator.EnterAlgorithmBody(failing, ObservedRun(observations), []);
        var first = Resolve("V", null, entry);
        var second = Resolve("V", null, entry);
        Assert.True(first.IsError && second.IsError);
        var report = OpenProviderIndexing.Describe(first.Error);
        Assert.Equal(
            "[while resolving open: Gone @ [1:11, 1:15)] UnknownName { Span = [1:11, 1:15), IsResourceLimit = False, Code = UnknownName, Name = Gone } @ [1:11, 1:15)"
                + " | UnknownName: while resolving open: Gone: Unknown name: Gone @ [1:11, 1:15)",
            report);
        Assert.Equal(report, OpenProviderIndexing.Describe(second.Error));
        Assert.Equal((0L, 2L, 0L), (observations.OpenProviderLevelCount, observations.OpenLevelConsultationCount, observations.OpenLevelReuseCount));
        Assert.Null(entry.HeadScope!.StaticOpenLevel);

        // Control: the same two reads of a level that resolves: one resolution, one reuse, one selection.
        var resolving = new Algorithm.User(null, [], [Named("Lib", 6), Named("Other", 11)], Libraries, OutputBundle.Empty);
        observations = new EvaluationObservations();
        entry = Evaluator.EnterAlgorithmBody(resolving, ObservedRun(observations), []);
        var once = Resolve("V", null, entry);
        var again = Resolve("V", null, entry);
        Assert.True(once.IsOk && again.IsOk);
        Assert.Equal(once.Value, again.Value);
        Assert.Equal((1L, 2L, 1L), (observations.OpenProviderLevelCount, observations.OpenLevelConsultationCount, observations.OpenLevelReuseCount));
        Assert.Same(entry.HeadScope, entry.HeadScope!.StaticOpenLevel!.Level);
    }

    [Fact]
    public void AnotherRun_OrAWithCopyOfTheLevel_ResolvesAfresh()
    {
        var resolving = new Algorithm.User(null, [], [Named("Lib", 6), Named("Other", 11)], Libraries, OutputBundle.Empty);
        var observations = new EvaluationObservations();
        var entry = Evaluator.EnterAlgorithmBody(resolving, ObservedRun(observations), []);
        Assert.True(Resolve("V", null, entry).IsOk);
        var level = entry.HeadScope!;
        var memo = level.StaticOpenLevel!;

        // The same level object read in ANOTHER run (another budget) is resolved for that run.
        var otherRun = ObservedRun(new EvaluationObservations()) with { CallStack = entry.CallStack, HeadScope = level };
        Assert.True(Resolve("V", null, otherRun).IsOk);
        Assert.Equal(1, otherRun.Observations!.OpenProviderLevelCount);
        Assert.NotSame(memo, level.StaticOpenLevel);

        // A `with` copy carries the slot, but the memo names the level it was resolved for, so a body
        // wired under the copy resolves the copy's level again and memoizes it on the copy.
        var copy = level with { };
        Assert.Same(level.StaticOpenLevel, copy.StaticOpenLevel);
        var reader = new Algorithm.User(copy, [], [], [], OutputBundle.Empty);
        observations = new EvaluationObservations();
        var readerEntry = Evaluator.EnterAlgorithmBody(reader, ObservedRun(observations) with { CallStack = entry.CallStack }, []);
        Assert.True(Resolve("W", null, readerEntry).IsOk);
        Assert.True(Resolve("V", null, readerEntry).IsOk);
        Assert.Equal((1L, 2L, 1L), (observations.OpenProviderLevelCount, observations.OpenLevelConsultationCount, observations.OpenLevelReuseCount));
        Assert.Same(copy, copy.StaticOpenLevel!.Level);
    }

    [Fact]
    public async Task AHostConstructedLevel_IsResolvedOnEveryRead_AndNeverWritten()
    {
        // `Run`'s rows read `V` through the opens of the HOST level the opened block is pre-wired under. A
        // host level may be shared across runs and threads, so it holds no memo: each of the three reads
        // resolves it (the root's own level, read once for `Run`, is the fourth resolution).
        var host = new ScopeCtx(null, [new Expr.Resolve("M")],
            [new Property("M", new Algorithm.User(null, [], [], [new Property("V", Value(7), IsPublic: true)], OutputBundle.Empty))]);
        var block = new Algorithm.User(host, [], [], [new Property("Run", new Algorithm.User(null, [], [], [],
            [new Expr.Resolve("V"), new Expr.Resolve("V"), new Expr.Resolve("V")]), IsPublic: true)], OutputBundle.Empty);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.AlgorithmExpr(block)], [], [new Expr.Resolve("Run")]));

        var observed = await OpenProviderIndexing.OnBothRoutesAsync(program);
        Assert.Equal(new OpenProviderIndexing.Observation("ok S[7, 7, 7]", 4, 4, 0, 0, 0, 4, 0), observed);
        Assert.Null(host.StaticOpenLevel);
    }
}
