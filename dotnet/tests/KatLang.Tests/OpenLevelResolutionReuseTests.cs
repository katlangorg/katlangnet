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
/// on a prepared root: <c>Levels</c> counts resolutions, <c>Consultations</c> reads of a nonempty level,
/// <c>Reuses</c> reads a memo served. Where the synchronous route and the forced async twin do the same lookup
/// work, both must give the same counts (<see cref="OpenProviderIndexing.OnBothRoutesAsync(string)"/>). Two tests
/// pin work that differs by route and observe each route on its own: loop planning, and an asynchronous
/// resolution's retry (<see cref="AFailingLinkCarrierThroughAParameter_AgreesOnBothRoutes_ButTheAsyncRetryReadsItsLevelOnceMore"/>).
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
        // Each call of `F` consults its level five times: the two written `X` elements when the list is
        // built (a list element is supplied like an argument and read later: lazy collections, issue #204),
        // then the three reads — the two elements and `G`'s — when the result is read. One resolution per call.
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[L[10, 11, 10], L[20, 21, 20]]", 2, 2, 0, 0, 0, 10, 8), activated);
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
        // 8 providers scan on every read; 12 index their public members once, on the second read, visiting
        // all 19 members of the 12 blocks. Either way a provider offers its FIRST public member of a name,
        // and an ambiguity names every offering provider in written order.
        var last = width - 1;
        var indexWork = width > Evaluator.OpenProviderLinearIndexLimit ? new OpenProviderIndexing.MemberIndexWork(1, 19, 0) : OpenProviderIndexing.MemberIndexWork.None;
        var (reads, readsIndex) = await OpenProviderIndexing.OnBothRoutesWithIndexWorkAsync(
            ManyBlocks(width, new Expr.Resolve("Y"), new Expr.Resolve("W0"), new Expr.Resolve($"W{last}"), new Expr.Resolve("Y")));
        Assert.Equal($"ok S[1, 0, {last}, 1]", reads.Outcome);
        Assert.Equal((1, width, 4, 3), (reads.Levels, reads.Entries, reads.Consultations, reads.Reuses));
        Assert.Equal(indexWork, readsIndex);

        var (ambiguous, ambiguousIndex) = await OpenProviderIndexing.OnBothRoutesWithIndexWorkAsync(ManyBlocks(width, new Expr.Resolve("W3"), new Expr.Resolve("Z")));
        Assert.Contains("AmbiguousOpen(Z: (inline#2), (inline#5), (inline#7)) @ ", ambiguous.Outcome, StringComparison.Ordinal);
        Assert.Equal((1, 2, 1), (ambiguous.Levels, ambiguous.Consultations, ambiguous.Reuses));
        Assert.Equal(indexWork, ambiguousIndex);
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

    // ── Heads pushed without a head scope (November 2026 follow-up) ─────────────────────────────
    // Each alias chase that no binding memo serves (for example, a carrier invoked through a parameter)
    // reads the head level of its wiring. Loop planning can also consult a head's opens when recognizing
    // `if` through a host parent. Executing loop steps and selected clauses have per-activation levels.

    /// <summary><c>M0 … M{K−1}</c> with <c>Mi = { public Fi(x) = x + i }</c>, and the carrier <c>A</c> opening them all.</summary>
    private static string Carrier(int width)
        => string.Concat(Enumerable.Range(0, width).Select(static i => $"M{i} = {{ public F{i}(x) = x + {i} }}\n"))
            + $"A = {{\n    open {string.Join(", ", Enumerable.Range(0, width).Select(static i => $"M{i}"))}\n    F{width - 1}\n}}\n";

    [Theory]
    [InlineData(1, 2)]
    [InlineData(4, 16)]
    [InlineData(9, 12)]
    public async Task AnAliasInvokedAgain_ResolvesItsOpensOncePerAliasObject(int width, int calls)
    {
        // `Run`'s parameter projects ONE alias object, invoked `calls` times; each invocation chases it, and
        // each chase reads `F{K−1}` through the carrier's own level. Formerly `calls` resolutions of K targets.
        var source = Carrier(width) + $"Run(f) = [{string.Join(", ", Enumerable.Range(0, calls).Select(static i => $"f({i})"))}]\nRun(A)";
        var values = $"ok L[{string.Join(", ", Enumerable.Range(0, calls).Select(i => i + width - 1))}]";
        var observed = await OpenProviderIndexing.OnBothRoutesAsync(source);
        Assert.Equal(new OpenProviderIndexing.Observation(values, 1, width, KeyComparisons(width), 0, 0, calls, calls - 1), observed);
        Assert.Equal("ok", (await SixRouteAgreement.OnEveryRouteAsync(source)).Kind);
    }

    [Fact]
    public async Task AnAliasHeadLevel_IsOwnedByTheActivationTheAliasIsDeclaredUnder()
    {
        // `A` is declared inside `G`'s body, so each call wires its own alias under its own activation: one
        // resolution per call, shared by the call's two invocations (formerly one per invocation).
        const string source = "M0 = { public F0(x) = x + 0 }\nM1 = { public F1(x) = x + 1 }\nTwice(f, z) = [f(z), f(z + 1)]\n"
            + "G(z) = {\n    A = {\n        open M0, M1\n        F1\n    }\n    Twice(A, z)\n}\n[G(1), G(2), G(3)]";
        var observed = await OpenProviderIndexing.OnBothRoutesAsync(source);
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[L[2, 3], L[3, 4], L[4, 5]]", 3, 6, 3, 0, 0, 6, 3), observed);

        // An inline carrier passed as the argument is the same: one alias per call of `G`.
        const string inline = "M0 = { public F0(x) = x + 0 }\nM1 = { public F1(x) = x + 1 }\nTwice(f, z) = [f(z), f(z + 1)]\n"
            + "G(z) = Twice({\n    open M0, M1\n    F1\n}, z)\n[G(1), G(2)]";
        var inlineObserved = await OpenProviderIndexing.OnBothRoutesAsync(inline);
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[L[2, 3], L[3, 4]]", 2, 4, 2, 0, 0, 4, 2), inlineObserved);
        Assert.Equal("ok", (await SixRouteAgreement.OnEveryRouteAsync(inline)).Kind);
    }

    [Fact]
    public async Task AliasWiringsKeepTheirOwnHeadLevelsForDottedAndAlternatingCalls()
    {
        // A member-path target whose head `Sub` the carrier's own open supplies: one resolution for three
        // invocations, the same selection.
        const string dotted = "Lib = {\n    public Sub = {\n        public F(x) = x * 10\n    }\n}\nA = {\n    open Lib\n    Sub.F\n}\n"
            + "Run(f) = [f(1), f(2), f(3)]\nRun(A)";
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[10, 20, 30]", 1, 1, 0, 0, 0, 3, 2), await OpenProviderIndexing.OnBothRoutesAsync(dotted));
        Assert.Equal("ok", (await SixRouteAgreement.OnEveryRouteAsync(dotted)).Kind);

        // Both parameter cells retain their own wiring. Alternating the calls reuses both scopes.
        const string alternating = "M0 = { public F0(x) = x + 0 }\nM1 = { public F1(x) = x + 1 }\nA = {\n    open M0\n    F0\n}\n"
            + "B = {\n    open M1\n    F1\n}\nRun(f, g) = [f(1), g(1), f(2), g(2)]\nRun(A, B)";
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[1, 2, 2, 3]", 2, 2, 0, 0, 0, 4, 2), await OpenProviderIndexing.OnBothRoutesAsync(alternating));
    }

    /// <summary>
    /// One route of a prepared program beside its open-level counts: the zero-argument entries the run
    /// published, its semantic charges (steps, peak depth, materialized items and string characters,
    /// <c>tick()</c>s), and the retries of its asynchronous resolutions (none on the synchronous route).
    /// </summary>
    private sealed record RouteRun(OpenProviderIndexing.Observation Lookup, int Publications, string Charges, long Retries)
    {
        /// <summary>What both routes must agree on: the complete outcome, the publications and the charges.</summary>
        public (string Outcome, int Publications, string Charges) Agreed => (Lookup.Outcome, Publications, Charges);
    }

    /// <summary>The run <see cref="OpenProviderIndexing.ObserveAsync"/> makes of <paramref name="program"/>, with its caches and budget read too.</summary>
    private static async Task<RouteRun> ObserveRouteAsync(Expr program, bool forcedAsync, EvaluationLimits? limits = null)
    {
        var observations = new EvaluationObservations();
        if (forcedAsync)
        {
            var cache = new RunScopedAsyncZeroArgPropertyResultCache();
            var (result, budget) = await Evaluator.RunCountedObservedAsync(program, limits, cache, observations: observations);
            return Observed(result, budget, cache.PublishedCount);
        }
        else
        {
            var cache = new RunScopedZeroArgPropertyResultCache(collectStatistics: false);
            var (result, budget) = Evaluator.RunCountedObserved(program, limits, zeroArgPropertyResultCache: cache, observations: observations);
            return Observed(result, budget, cache.PublishedCount);
        }

        RouteRun Observed(EvalResult<Evaluator.CountedResult> result, EvaluationBudget budget, int publications)
            => new(OpenProviderIndexing.Of(result, observations), publications,
                $"steps {budget.ConsumedSteps}, depth {budget.PeakDepth}, items {budget.MaterializedItems}, "
                    + $"chars {budget.MaterializedStringChars}, ticks {budget.TickCount}",
                budget.ResolutionRetries);
    }

    [Fact]
    public async Task AFailingLinkCarrierThroughAParameter_AgreesOnBothRoutes_ButTheAsyncRetryReadsItsLevelOnceMore()
    {
        // NEGATIVE CONTROL of OnBothRoutesAsync's count parity, recovered from the 2026-11-18 open-lookup review. The
        // carrier `A` reaches `Sub.Algorithm` through its own `open Lib`. `Run` reserves three list positions
        // and returns. Reading the first position then invokes `A` through the parameter `f`, so no binding
        // memo serves the chase. The link's receiver `Sub` has no output, so `f(1)` fails before demanding 1.
        const string failingCarrier = "Lib = {\n    public Sub = {\n        public F(x) = x * 10\n    }\n}\n"
            + "A = {\n    open Lib\n    Sub.Algorithm\n}\n";
        const string source = failingCarrier + "Run(f) = [f(1), f(2), f(3)]\nRun(A)";
        const string publicError = "MissingOutput: while evaluating call to f: Property 'Sub' has no defined output.\n"
            + "Add an output expression to 'Sub', or use `()` if the empty sequence value was intended. "
            + "To use one of its properties, write `Sub.X`. @ [8:5, 8:8)";
        // Every frame carries the position of `Sub` in the carrier's row; the innermost error has none.
        const string missingOutput = "err [while evaluating call to f @ [8:5, 8:8)] "
            + "[while evaluating property Sub @ [8:5, 8:8)] MissingOutput { Span = , IsResourceLimit = False, Code = MissingOutput } @  | "
            + publicError;
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var synchronous = await ObserveRouteAsync(program, forcedAsync: false);
        var asynchronous = await ObserveRouteAsync(program, forcedAsync: true);

        // Both routes report the same structured error, publish nothing and charge the same two steps.
        Assert.Equal((missingOutput, 0, "steps 2, depth 1, items 3, chars 0, ticks 0"), synchronous.Agreed);
        Assert.Equal(synchronous.Agreed, asynchronous.Agreed);

        // Both routes resolve the same two level states of the carrier's `open Lib`, the head level the chase
        // navigates and the level the link cell's projection reads, and index the same two providers. Their reads
        // differ. The synchronous route consults those levels four times: the chase's route navigation, the link's
        // route check, the receiver's classification and its VALUE demand. The twin's resolutions retry twice, after
        // the link's CALLABLE projection and after its receiver's VALUE. After the VALUE failure the projection's
        // resolver runs again and checks the link's route once more: a fifth read, which the memo serves.
        Assert.Equal(new OpenProviderIndexing.Observation(missingOutput, 2, 2, 0, 0, 0, 4, 2), synchronous.Lookup);
        Assert.Equal(new OpenProviderIndexing.Observation(missingOutput, 2, 2, 0, 0, 0, 5, 3), asynchronous.Lookup);
        Assert.Equal((0L, 2L), (synchronous.Retries, asynchronous.Retries));

        // These are the helper's own observations, so its parity assertion rejects this program.
        Assert.Equal(synchronous.Lookup, await OpenProviderIndexing.ObserveAsync(program, forcedAsync: false));
        Assert.Equal(asynchronous.Lookup, await OpenProviderIndexing.ObserveAsync(program, forcedAsync: true));
        await Assert.ThrowsAsync<Xunit.Sdk.EqualException>(() => OpenProviderIndexing.OnBothRoutesAsync(program));

        // The charges also agree at the step limit. One step stops both routes at `Sub`'s declaration; two and
        // three give the original error again.
        foreach (var maxSteps in new[] { 1, 2, 3 })
        {
            var limits = new EvaluationLimits { MaxSteps = maxSteps };
            var limited = await ObserveRouteAsync(program, forcedAsync: false, limits);
            Assert.Equal(limited.Agreed, (await ObserveRouteAsync(program, forcedAsync: true, limits)).Agreed);
            Assert.Equal(
                maxSteps == 1
                    ? ("err EvaluationStepLimitExceeded { Span = [2:12, 2:15), IsResourceLimit = True, Code = EvaluationStepLimitExceeded, Limit = 1 } @ [2:12, 2:15)"
                        + " | EvaluationStepLimitExceeded: Evaluation step limit of 1 was exceeded @ [2:12, 2:15)", 0, "steps 1, depth 1, items 3, chars 0, ticks 0")
                    : synchronous.Agreed,
                limited.Agreed);
        }

        // A trace in the first argument makes premature demand observable. Even the route that retries
        // the projection must report the same error before invoking the host.
        var failing = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal(("err", publicError), (failing.Kind, Assert.Single(failing.Errors)));
        Assert.Empty(failing.HostCalls);
        var withTrace = await SixRouteAgreement.OnEveryRouteAsync(
            failingCarrier + "Run(f) = [f(trace(1)), f(2), f(3)]\nRun(A)");
        Assert.True(failing.AgreesWith(withTrace), withTrace.ToString());

        // A retained carrier whose target traces runs that target once per invocation, in order.
        const string traced = "Lib = {\n    public Sub = {\n        public F(x) = trace(x)\n    }\n}\n"
            + "A = {\n    open Lib\n    Sub.F\n}\nRun(f) = [f(1), f(2), f(3)]\nRun(A)";
        var effects = await SixRouteAgreement.OnEveryRouteAsync(traced);
        Assert.Equal(("ok", "L[1, 2, 3]"), (effects.Kind, effects.Value));
        Assert.Equal(["trace(1)", "trace(2)", "trace(3)"], effects.HostCalls);
    }

    private delegate EvalResult<Algorithm> ResolveAlias(Algorithm.Alias alias, Evaluator.EvalCtx ctx, Property? binding);

    /// <summary>The evaluator's invocation chase of an alias, with no binding memo (<c>Evaluator.ResolveAliasTarget</c>).</summary>
    private static readonly ResolveAlias ChaseAlias = typeof(Evaluator)
        .GetMethod("ResolveAliasTarget", BindingFlags.NonPublic | BindingFlags.Static)!
        .CreateDelegate<ResolveAlias>();

    [Fact]
    public void CopiedAliasWiringsAndOtherRunsResolveTheirOwnProviders()
    {
        var source = new Algorithm.Alias(null, [new Expr.Resolve("Lib")], Libraries, new Expr.Resolve("V"));
        var wired = Evaluator.WireAlias(source, null);
        var scope = Assert.IsType<ScopeCtx>(wired.WiredOpenScope);
        Assert.Same(wired, scope.Owner);
        Assert.Null(source.WiredOpenScope);
        Assert.Equal(source, wired);
        Assert.Equal(source.GetHashCode(), wired.GetHashCode());

        var run = ObservedRun(new EvaluationObservations());
        Assert.True(ChaseAlias(wired, run, null).IsOk);
        Assert.Same(run.Budget, scope.StaticOpenLevel!.Run);

        var copy = wired with { Opens = [new Expr.Resolve("Other")] };
        Assert.Null(copy.WiredOpenScope);
        Assert.True(ChaseAlias(copy, run, null).IsError); // Other does not offer V.
        Assert.True(ChaseAlias(wired, run, null).IsOk);
        Assert.Equal(1, run.Observations!.OpenLevelReuseCount);

        var nextRun = ObservedRun(new EvaluationObservations());
        Assert.True(ChaseAlias(wired, nextRun, null).IsOk);
        Assert.Equal(1, nextRun.Observations!.OpenProviderLevelCount);
        Assert.Equal(0, nextRun.Observations.OpenLevelReuseCount);
    }

    [Fact]
    public void AnAliasHeadLevel_NeverMemoizesAFailure_AndAnotherAliasObjectBuildsItsOwn()
    {
        // A host-built carrier whose later open target fails: two chases resolve its level twice and report
        // the same first error; the run's slot keeps the alias's head level, which holds no memo.
        var observations = new EvaluationObservations();
        var run = ObservedRun(observations);
        var failing = new Algorithm.Alias(null, [Named("Lib", 6), Named("Gone", 11), Named("Other", 17)], Libraries, new Expr.Resolve("V"));
        var first = ChaseAlias(failing, run, null);
        var second = ChaseAlias(failing, run, null);
        Assert.True(first.IsError && second.IsError);
        Assert.Equal(OpenProviderIndexing.Describe(first.Error), OpenProviderIndexing.Describe(second.Error));
        Assert.Contains("while resolving open: Gone", OpenProviderIndexing.Describe(first.Error), StringComparison.Ordinal);
        Assert.Equal((0L, 2L, 0L), (observations.OpenProviderLevelCount, observations.OpenLevelConsultationCount, observations.OpenLevelReuseCount));
        var level = run.Budget.AliasHeadLevel!;
        Assert.Same(failing, level.Owner);
        Assert.Null(level.Activation);
        Assert.Null(level.StaticOpenLevel);

        // A resolving carrier: the second chase reuses the first's providers on the same head level.
        var resolving = new Algorithm.Alias(null, [Named("Lib", 6), Named("Other", 11)], Libraries, new Expr.Resolve("V"));
        observations = new EvaluationObservations();
        run = ObservedRun(observations);
        var once = ChaseAlias(resolving, run, null);
        var again = ChaseAlias(resolving, run, null);
        Assert.True(once.IsOk && again.IsOk);
        Assert.Equal(once.Value, again.Value);
        Assert.Equal((1L, 2L, 1L), (observations.OpenProviderLevelCount, observations.OpenLevelConsultationCount, observations.OpenLevelReuseCount));
        level = run.Budget.AliasHeadLevel!;
        Assert.Same(resolving, level.Owner);
        Assert.Same(level, level.StaticOpenLevel!.Level);
        Assert.Equal(new ScopeCtx(null, resolving.Opens, resolving.Properties, []), level);

        // A `with` copy is another alias object: it builds its own head level and resolves it afresh, and the
        // original alias is never written (it has no state to write; the memo lives on the run's scope).
        var copy = resolving with { };
        Assert.True(ChaseAlias(copy, run, null).IsOk);
        Assert.Equal((2L, 3L, 1L), (observations.OpenProviderLevelCount, observations.OpenLevelConsultationCount, observations.OpenLevelReuseCount));
        Assert.Same(copy, run.Budget.AliasHeadLevel!.Owner);
        Assert.NotSame(level, run.Budget.AliasHeadLevel);

        // Another run starts with an empty slot and resolves the same alias object for itself.
        var otherRun = ObservedRun(new EvaluationObservations());
        Assert.Null(otherRun.Budget.AliasHeadLevel);
        Assert.True(ChaseAlias(resolving, otherRun, null).IsOk);
        Assert.Equal(1, otherRun.Observations!.OpenProviderLevelCount);
        Assert.NotSame(level, otherRun.Budget.AliasHeadLevel);
    }

    [Fact]
    public async Task AHostBuiltAliasUnderAHostLevel_GetsAHeadLevelPerRun_AndTheHostLevelIsNeverWritten()
    {
        // A host-built tree reused by two runs: the carrier `A` (opening `Lib` for its target `F`) and `Apply`
        // live on a HOST level, under which the root's opened inline block declares `Run`. `Run` passes `A` to
        // `Apply`, so `A` is wired under the host level; the parameter's cell
        // projects the carrier once for the three calls. Each run resolves the root's level and the carrier's
        // own level once each, on its own head level, the two runs agree exactly, and the host level is never
        // written. (Repeated chases of one alias object are pinned above, from source and directly.)
        var identity = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);
        var lib = new Algorithm.User(null, [], [], [new Property("F", identity, IsPublic: true)], OutputBundle.Empty);
        var carrier = new Algorithm.Alias(null, [new Expr.Resolve("Lib")], [], new Expr.Resolve("F")) { IsReference = false };
        Expr Call(int i) => new Expr.Call(new Expr.Param("f"), [new Expr.Num(i)]);
        var apply = new Algorithm.User(null, [new CaptureParameterPattern("f")], [], [], [Call(1), Call(2), Call(3)]);
        var host = new ScopeCtx(null, [], [new Property("Lib", lib), new Property("A", carrier), new Property("Apply", apply)]);
        var run = new Algorithm.User(null, [], [], [], [new Expr.Call(new Expr.Resolve("Apply"), [new Expr.Resolve("A")])]);
        var block = new Algorithm.User(host, [], [], [new Property("Run", run, IsPublic: true)], OutputBundle.Empty);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.AlgorithmExpr(block)], [], [new Expr.Resolve("Run")]));

        var runs = await Task.WhenAll(Task.Run(() => OpenProviderIndexing.OnBothRoutesAsync(program)),
            Task.Run(() => OpenProviderIndexing.OnBothRoutesAsync(program)));
        var expected = new OpenProviderIndexing.Observation("ok S[1, 2, 3]", 2, 2, 0, 0, 0, 4, 2);
        Assert.All(runs, observed => Assert.Equal(expected, observed));
        Assert.Null(carrier.WiredOpenScope);
        Assert.Null(host.StaticOpenLevel);
    }

    [Fact]
    public async Task AliasRouteAndStaticStepShareTheSameOpenedReceiver()
    {
        var identity = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);
        var sub = new Algorithm.User(null, [], [], [new Property("Algorithm", identity, IsPublic: true)], OutputBundle.Empty);
        var lib = new Algorithm.User(null, [], [], [new Property("Sub", sub, IsPublic: true)], OutputBundle.Empty);
        var carrier = new Algorithm.Alias(null, [new Expr.Resolve("Lib")], [],
            new Expr.DotCall(new Expr.Resolve("Sub"), "Algorithm", null)) { IsReference = false };
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [new Property("Lib", lib), new Property("A", carrier)], [new Expr.Call(new Expr.Resolve("A"), [new Expr.Num(7)])]));

        Assert.Equal(new OpenProviderIndexing.Observation("ok 7", 1, 1, 0, 0, 0, 2, 1),
            await OpenProviderIndexing.OnBothRoutesAsync(program));
    }

    [Fact]
    public async Task LoopPlanningSharesTheStepsOpenLevelForBuiltinRecognition()
    {
        const int calls = 8, rounds = 8;
        var builtins = new Algorithm.User(null, [], [],
            [new Property("if", new Algorithm.Builtin(BuiltinId.@if), IsPublic: true)], OutputBundle.Empty);
        var host = new ScopeCtx(null, [], [new Property("Ops", builtins)]);
        Expr row = new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1));
        for (var i = 0; i < calls; i++)
            row = new Expr.Call(new Expr.Resolve("if"), [new Expr.BoolLiteral(true), row, new Expr.Num(-1)]);
        var step = new Algorithm.User(null, [new CaptureParameterPattern("x")], [new Expr.Resolve("Ops")], [], [row]);
        var exports = new Algorithm.User(host, [], [], [new Property("Step", step, IsPublic: true)], OutputBundle.Empty);
        var repeat = new Expr.Call(new Expr.Resolve("repeat"),
            [new Expr.Call(new Expr.Resolve("Step"), [new Expr.Num(0)]), new Expr.Num(rounds)]);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.AlgorithmExpr(exports)], [], [repeat]));

        // Both routes resolve the root's export once. Sync recognizes the eight calls while building
        // one plan. The async evaluator runs the written calls and shares a fresh level in each round.
        Assert.Equal(new OpenProviderIndexing.Observation("ok 8", 2, 2, 0, 0, 0, 1 + calls, calls - 1),
            await OpenProviderIndexing.ObserveAsync(program, forcedAsync: false));
        Assert.Equal(new OpenProviderIndexing.Observation("ok 8", 1 + rounds, 1 + rounds, 0, 0, 0,
                1 + rounds * calls, rounds * (calls - 1)),
            await OpenProviderIndexing.ObserveAsync(program, forcedAsync: true));
        Assert.Null(host.StaticOpenLevel);
    }

    [Theory]
    [InlineData(4, 16)]
    [InlineData(9, 6)]
    public async Task ALoopStepsOwnLevel_IsResolvedOncePerRound_AndSharedByTheRoundsReads(int width, int rounds)
    {
        // The step body opens the providers and reads all K names each round. Every round enters the step
        // with its own activation (the generic rounds, and the planned loop's per-iteration rebinding), so
        // the level is resolved once per round and reused by the round's other K − 1 reads — never per read.
        // Resolving it once per LOOP would be wrong in general: a step's own member opened as a provider is
        // wired under the round's activation and reads that round's state.
        var source = string.Concat(Enumerable.Range(0, width).Select(static i => $"M{i} = {{ public V{i} = {i} }}\n"))
            + $"Step(x) = {{\n    open {string.Join(", ", Enumerable.Range(0, width).Select(static i => $"M{i}"))}\n    x + {string.Join(" + ", Enumerable.Range(0, width).Select(static i => $"V{i}"))}\n}}\n"
            + $"Step(0).repeat({rounds})";
        var observed = await OpenProviderIndexing.OnBothRoutesAsync(source);
        var perRound = width * (width - 1) / 2;
        Assert.Equal(
            new OpenProviderIndexing.Observation($"ok {rounds * perRound}", rounds, rounds * width, rounds * KeyComparisons(width), 0, 0, rounds * width, rounds * (width - 1)),
            observed);

        // The exception that rules out sharing across rounds: the step's own member is the provider, and
        // it reads the round's parameter.
        const string ownMember = "Step(x) = {\n    open Sub\n    Sub = {\n        public V = x + 1\n    }\n    V\n}\nStep(0).repeat(4)";
        Assert.Equal(new OpenProviderIndexing.Observation("ok 4", 4, 4, 0, 0, 0, 4, 0), await OpenProviderIndexing.OnBothRoutesAsync(ownMember));
        Assert.Equal("ok", (await SixRouteAgreement.OnEveryRouteAsync(ownMember)).Kind);
    }

    [Fact]
    public async Task AClauseFamilysBodyLevel_IsResolvedOncePerCall_AndSharedByTheCallsReads()
    {
        // The recursive clause's body opens two providers and reads both. The pushed family is never the head of
        // a read: each call enters the selected body above it — the body's static head level, one per entry,
        // wired under the call's family activation — so 8 calls resolve 8 levels and reuse each once.
        const string source = "M0 = { public V0 = 1 }\nM1 = { public V1 = 2 }\nF(0) = 0\nF(n) = {\n    open M0, M1\n    V0 + V1 + F(n - 1)\n}\nF(8)";
        Assert.Equal(new OpenProviderIndexing.Observation("ok 24", 8, 16, 8, 0, 0, 16, 8), await OpenProviderIndexing.OnBothRoutesAsync(source));

        // A family declared inside a body that opens reads the enclosing level, which its entry resolves once.
        const string enclosing = "M0 = { public V0 = 1 }\nOuter = {\n    open M0\n    F(0) = 0\n    F(n) = V0 + F(n - 1)\n    F(8)\n}\nOuter";
        Assert.Equal(new OpenProviderIndexing.Observation("ok 8", 1, 1, 0, 0, 0, 8, 7), await OpenProviderIndexing.OnBothRoutesAsync(enclosing));
    }

    [Fact]
    public async Task OpensOnAHostBuiltFamilyAreSharedWithinEachMatch()
    {
        var branch = new Algorithm.User(null, [], [], [],
            [new Expr.Binary(BinaryOp.Add, new Expr.Resolve("V"), new Expr.Resolve("V"))]);
        var family = new Algorithm.Conditional(null, [new Expr.Resolve("Lib")], [new CondBranch(new Pattern.Bind("n"), branch)]);
        Expr Call(int value) => new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(value)]);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [.. Libraries, new Property("F", family)], [Call(1), Call(2)]));
        Assert.Equal(new OpenProviderIndexing.Observation("ok S[2, 2]", 2, 2, 0, 0, 0, 4, 2),
            await OpenProviderIndexing.OnBothRoutesAsync(program));
    }

    [Fact]
    public async Task MemberCallsReuseAnOpenLevelWithinTheirOwnWiring()
    {
        const string source = """
            Mod = {
                open Lib
                public X(q) = V + V + q
            }
            Lib = { public V = 10 }
            [Mod.X(1), Mod.X(2), Mod.X(3)]
            """;
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[21, 22, 23]", 3, 3, 0, 0, 0, 6, 3),
            await OpenProviderIndexing.OnBothRoutesAsync(source));
    }

    // ── Large providers (November 2026 follow-up) ─────────────────────────────────────────────────
    // A narrow level asks each provider for its first public member of the name. A provider of P members
    // was scanned on every read (R reads cost R·P); a member list of at least
    // `PropertyBindingIndexCache.MinimumIndexedPublicPropertyCount` is now indexed once per run
    // (PropertyBindingIndexTests pins the member reads), and every selection stays the scan's.

    /// <summary><see cref="ManyBlocks"/> with every block padded by <paramref name="padding"/> extra public members first.</summary>
    private static Expr PaddedBlocks(int width, int padding, params Expr[] rows)
    {
        static Property Member(string name, decimal value, bool isPublic = true) => new(name, Value(value), isPublic);
        var opens = Enumerable.Range(0, width).Select(i =>
        {
            var members = Enumerable.Range(0, padding).Select(p => Member($"Pad{i}_{p}", p)).ToList();
            members.AddRange(i switch
            {
                2 or 7 => [Member("Z", i)],
                5 => [Member("Z", 50, isPublic: false), Member("Z", 5), Member("Z", 55), Member("Y", 1), Member("Y", 2), Member("Hidden", 9, isPublic: false)],
                _ => [],
            });
            members.Add(Member($"W{i}", i));
            return (Expr)new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], members, OutputBundle.Empty));
        }).ToArray();
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], opens, [], new OutputBundle(rows)));
    }

    [Theory]
    [InlineData(3)]
    [InlineData(8)]
    [InlineData(12)]
    public async Task ALargeProvidersIndex_SelectsExactlyWhatTheScanSelects(int width)
    {
        // The same reads over unpadded providers (each scanned) and providers padded past the index threshold
        // (each indexed): the same values, the same first public member (a private `Z` never selected, the
        // first of two public ones kept), the same ambiguity naming the offering providers in written order,
        // and the same miss for a name only a private member carries.
        var padding = Evaluation.PropertyBindingIndexCache.MinimumIndexedPublicPropertyCount;
        var last = width - 1;
        Expr[] reads = width > 5
            ? [new Expr.Resolve("Y"), new Expr.Resolve("W0"), new Expr.Resolve($"W{last}"), new Expr.Resolve("Y")]
            : [new Expr.Resolve("W0"), new Expr.Resolve($"W{last}"), new Expr.Resolve("W0")];
        foreach (var rows in new[] { reads, [new Expr.Resolve("W1"), new Expr.Resolve("Z")], [new Expr.Resolve("Hidden")] })
        {
            var scanned = await OpenProviderIndexing.OnBothRoutesAsync(PaddedBlocks(width, 0, rows));
            var indexed = await OpenProviderIndexing.OnBothRoutesAsync(PaddedBlocks(width, padding, rows));
            Assert.Equal(scanned, indexed);
        }

        var values = await OpenProviderIndexing.OnBothRoutesAsync(PaddedBlocks(width, padding, reads));
        Assert.Equal(width > 5 ? $"ok S[1, 0, {last}, 1]" : $"ok S[0, {last}, 0]", values.Outcome);
        // Three blocks hold one public `Z` (block 2's); wider levels offer it from blocks 2, 5 and 7.
        var zRead = (await OpenProviderIndexing.OnBothRoutesAsync(PaddedBlocks(width, padding, new Expr.Resolve("W1"), new Expr.Resolve("Z")))).Outcome;
        if (width == 3)
            Assert.Equal("ok S[1, 2]", zRead);
        else
            Assert.Contains("AmbiguousOpen(Z: (inline#2), (inline#5), (inline#7)) @ ", zRead, StringComparison.Ordinal);
        Assert.Contains("UnknownName", (await OpenProviderIndexing.OnBothRoutesAsync(PaddedBlocks(width, padding, new Expr.Resolve("Hidden")))).Outcome, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(64)]
    public async Task ALargeProvidersSelectedMember_KeepsItsAccessCheck(int padding)
    {
        // `Q` captures `F`'s parameter, so it is local-only, and the root reads it outside any activation of
        // `F`: the refusal is the same whether `Sub`'s members are scanned or indexed. Read from inside the
        // activation, a captured member padded past the threshold selects and reads as before.
        var pads = string.Concat(Enumerable.Range(0, padding).Select(static i => $"        public Pad{i} = {i}\n"));
        var refused = await OpenProviderIndexing.OnBothRoutesAsync($"open A\nF(v) = {{\n    Sub = {{\n        public Q = v\n{pads}        0\n    }}\n    1\n}}\nA = F.Sub\nQ");
        Assert.StartsWith("err ", refused.Outcome, StringComparison.Ordinal);
        Assert.Contains("LocalOnlyProperty", refused.Outcome, StringComparison.Ordinal);

        var innerPads = string.Concat(Enumerable.Range(0, padding).Select(static i => $"            public Pad{i} = {i}\n"));
        var captured = $"F(p) = {{\n    open Lib.Sub\n    Lib = {{\n        public Sub = {{\n            public X = p\n{innerPads}        }}\n    }}\n    G(q) = X + q\n    [X, G(1), X]\n}}\n[F(10), F(20)]";
        // Each call's list is read when the run reads its result (lazy collections, issue #204): its
        // deferred elements consult the level's entry in their own evaluations — five consultations
        // per call, four of them reuses — where the eager literal consulted it three times.
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[L[10, 11, 10], L[20, 21, 20]]", 2, 2, 0, 0, 0, 10, 8), await OpenProviderIndexing.OnBothRoutesAsync(captured));
        Assert.Equal("ok", (await SixRouteAgreement.OnEveryRouteAsync(captured)).Kind);
    }

    // ── Repeated level states of one wide level (November 2026 follow-up) ─────────────────────────
    // A level's providers are resolved once per level STATE: per call, clause-body entry, loop round or member
    // call. A wide level's member index was built per state as well, so C calls through one level of providers
    // holding M members visited C·M members, and every call allocated an index. The index depends on the
    // providers' member lists alone, so the run builds it once per distinct sequence of lists
    // (`Evaluator.OpenLevelMemberIndexCache`) and every later state takes it; the providers, their wiring, the
    // access check and the selected member's wiring stay the state's and the read's.

    /// <summary><c>M0 … M{K−1}</c>, each <c>Mi</c> holding <paramref name="padding"/> public <c>Pixj</c> members before its <c>public Wi = i</c>.</summary>
    private static string PaddedProviders(int width, int padding)
        => string.Concat(Enumerable.Range(0, width).Select(i =>
            $"M{i} = {{\n{string.Concat(Enumerable.Range(0, padding).Select(j => $"    public P{i}x{j} = {j}\n"))}    public W{i} = {i}\n}}\n"));

    private static string OpensOf(IEnumerable<int> providers) => $"open {string.Join(", ", providers.Select(static i => $"M{i}"))}";

    private static string Calls(string callee, int calls)
        => $"[{string.Join(", ", Enumerable.Range(1, calls).Select(c => $"{callee}({c})"))}]";

    /// <summary>
    /// <paramref name="calls"/> level states of ONE written level of <paramref name="width"/> providers, each
    /// reading <c>W0</c> and <c>W{K−1}</c>: a parameterized body's own level (an activation per call), a clause
    /// body's static head level (one per entry), a loop step's level (one per round), or the level of a module
    /// owner its member calls read (a static wiring per call).
    /// </summary>
    private static string RepeatedStates(string shape, int width, int padding, int calls)
    {
        var opens = OpensOf(Enumerable.Range(0, width));
        var reads = $"W0 + W{width - 1}";
        return PaddedProviders(width, padding) + shape switch
        {
            "call" => $"F(x) = {{\n    {opens}\n    x + {reads}\n}}\n" + Calls("F", calls),
            "entry" => $"H(0) = 0\nH(n) = {{\n    {opens}\n    n + {reads}\n}}\n" + Calls("H", calls),
            "round" => $"Step(x) = {{\n    {opens}\n    x + {reads}\n}}\nStep(0).repeat({calls})",
            "member" => $"Mod = {{\n    {opens}\n    public X(q) = q + {reads}\n}}\n" + Calls("Mod.X", calls),
            _ => throw new ArgumentOutOfRangeException(nameof(shape), shape, null),
        };
    }

    [Theory]
    [InlineData("call", 8, 16, 5)]
    [InlineData("call", 9, 0, 5)]
    [InlineData("call", 9, 16, 5)]
    [InlineData("call", 16, 3, 3)]
    [InlineData("entry", 8, 16, 4)]
    [InlineData("entry", 9, 16, 4)]
    [InlineData("round", 8, 16, 4)]
    [InlineData("round", 9, 16, 6)]
    [InlineData("member", 8, 16, 4)]
    [InlineData("member", 9, 16, 4)]
    public async Task RepeatedStatesOfOneWideLevel_ShareOneMemberIndexPerRun(string shape, int width, int padding, int calls)
    {
        // Every state still resolves its own level once and reads it twice. At most 8 providers scan on every
        // read and index nothing; a wider level's FIRST state builds the run's index on its second read, visiting
        // every member of every provider once, and each later state takes it — formerly one build per state.
        var source = RepeatedStates(shape, width, padding, calls);
        var values = shape == "round"
            ? $"ok {calls * (width - 1)}"
            : $"ok L[{string.Join(", ", Enumerable.Range(1, calls).Select(c => c + width - 1))}]";
        var index = width > Evaluator.OpenProviderLinearIndexLimit
            ? new OpenProviderIndexing.MemberIndexWork(1, width * (padding + 1L), calls - 1)
            : OpenProviderIndexing.MemberIndexWork.None;
        var (observed, indexWork) = await OpenProviderIndexing.OnBothRoutesWithIndexWorkAsync(source);
        Assert.Equal(
            new OpenProviderIndexing.Observation(values, calls, calls * width, calls * KeyComparisons(width), 0, 0, 2 * calls, calls),
            observed);
        Assert.Equal(index, indexWork);

        // The plain (uncounted) and the generic (unoptimized) evaluator routes read through the same selection.
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var plain = new EvaluationObservations();
        var plainResult = Evaluator.RunObserved(program, plain);
        Assert.Equal(values, "ok " + SixRouteAgreement.Neutral(plainResult.Value));
        Assert.Equal(index, OpenProviderIndexing.MemberIndexWork.Of(plain));
        var generic = new EvaluationObservations();
        var (genericResult, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false, observations: generic);
        Assert.Equal(values, "ok " + SixRouteAgreement.Neutral(genericResult.Value.Value));
        Assert.Equal(index, OpenProviderIndexing.MemberIndexWork.Of(generic));
        Assert.Equal("ok", (await SixRouteAgreement.OnEveryRouteAsync(source)).Kind);
    }

    [Fact]
    public async Task ASharedMemberIndex_SelectsInEachRoundItsOwnProvider()
    {
        // The step's own `Sub` is one of nine providers and reads the round's `x`: the index the first round
        // built selects `V` for every later round, and each round still wires it under ITS OWN `Sub`, so
        // the rounds read 1, 9, 17 and 25 (one index shared by rounds 2–4; a stale wiring would read 1 forever).
        var source = string.Concat(Enumerable.Range(0, 8).Select(static i => $"M{i} = {{ public W{i} = {i} }}\n"))
            + $"Step(x) = {{\n    open Sub, {string.Join(", ", Enumerable.Range(0, 8).Select(static i => $"M{i}"))}\n"
            + "    Sub = {\n        public V = x + 1\n    }\n    W7 + V\n}\nStep(0).repeat(4)";
        var (observed, index) = await OpenProviderIndexing.OnBothRoutesWithIndexWorkAsync(source);
        Assert.Equal(new OpenProviderIndexing.Observation("ok 32", 4, 36, 0, 0, 0, 8, 4), observed);
        Assert.Equal(new OpenProviderIndexing.MemberIndexWork(1, 9, 3), index);
        Assert.Equal("ok", (await SixRouteAgreement.OnEveryRouteAsync(source)).Kind);
    }

    [Fact]
    public async Task EachOrderOfProviderLists_HasItsOwnIndex_SharedByEveryLevelWithThatOrder()
    {
        // F and H open the same nine providers in the same order, G in the reverse order: two indexes for the
        // run, each state of a known order taking its index (also after another order was served), and each
        // read selecting through its own level's order.
        var forward = OpensOf(Enumerable.Range(0, 9));
        var backward = OpensOf(Enumerable.Range(0, 9).Reverse());
        var source = PaddedProviders(9, 0)
            + $"F(x) = {{\n    {forward}\n    x + W0 + W8\n}}\nG(x) = {{\n    {backward}\n    x + W0 + W8\n}}\nH(x) = {{\n    {forward}\n    x + W1 + W7\n}}\n"
            + "[F(1), G(2), H(3), F(4), G(5), H(6)]";
        var (observed, index) = await OpenProviderIndexing.OnBothRoutesWithIndexWorkAsync(source);
        Assert.Equal(new OpenProviderIndexing.Observation("ok L[9, 10, 11, 12, 13, 14]", 6, 54, 0, 0, 0, 12, 6), observed);
        Assert.Equal(new OpenProviderIndexing.MemberIndexWork(2, 18, 4), index);
    }

    [Fact]
    public async Task AnAmbiguityThroughASharedIndex_IsTheScansAmbiguity()
    {
        // `K(q) = q.Z` falls back to the lexical `Z(q)` at run time (a receiver-decided fallback, so the front
        // end leaves the ambiguity to the evaluator), which reads `G`'s level: M2 and M7 both offer `Z`. Read
        // first, `Z` is selected by the scan; read second, by the index `G`'s state built, or by the index
        // `F`'s state built and `G`'s state took. All three name the same providers in written order. `Back`
        // opens them in the reverse order, so it builds its own index and names them in its order; F's index
        // read through Back's providers would name the providers at F's positions, M6 and M1.
        var providers = string.Concat(Enumerable.Range(0, 9).Select(static i => i is 2 or 7
            ? $"M{i} = {{\n    public W{i} = {i}\n    public Z = {i}\n}}\n"
            : $"M{i} = {{ public W{i} = {i} }}\n"));
        var opens = OpensOf(Enumerable.Range(0, 9));
        var declarations = providers + $"F(x) = {{\n    {opens}\n    x + W0 + W8\n}}\n"
            + $"G(x) = {{\n    {opens}\n    K(q) = q.Z\n    x + W1 + K(0)\n}}\n"
            + $"Early(x) = {{\n    {opens}\n    K(q) = q.Z\n    K(0) + x + W1\n}}\n"
            + $"Back(x) = {{\n    {OpensOf(Enumerable.Range(0, 9).Reverse())}\n    K(q) = q.Z\n    x + W1 + K(0)\n}}\n";
        foreach (var (row, providerOrder, index) in new[]
        {
            ("Early(2)", "M2, M7", OpenProviderIndexing.MemberIndexWork.None),
            ("G(2)", "M2, M7", new OpenProviderIndexing.MemberIndexWork(1, 11, 0)),
            ("[F(1), G(2)]", "M2, M7", new OpenProviderIndexing.MemberIndexWork(1, 11, 1)),
            ("[F(1), Back(2)]", "M7, M2", new OpenProviderIndexing.MemberIndexWork(2, 22, 0)),
        })
        {
            var (observed, indexWork) = await OpenProviderIndexing.OnBothRoutesWithIndexWorkAsync(declarations + row);
            Assert.StartsWith("err ", observed.Outcome, StringComparison.Ordinal);
            Assert.Contains($"AmbiguousOpen(Z: {providerOrder}) @ ", observed.Outcome, StringComparison.Ordinal);
            Assert.Equal(index, indexWork);
        }
    }

    [Fact]
    public void TheLevelMemberIndex_OffersExactlyWhatTheOrderedScanOffers_ForEveryName()
    {
        // The index against the selection it replaces — each provider's first public member of the name, in
        // provider order (PropertyBindingIndexCache.LookupPublic: a scan below 16 members, the list's index
        // from 16) — for shared, repeated, private-only, absent and UNNAMED names. A host-built list may hold
        // public members with a null name, which the scan compares like any other name; building the index of
        // a wide level holding one used to throw.
        static Property Member(string? name, decimal value, bool isPublic = true) => new(name!, Value(value), isPublic);
        static Property[] Padded(int padding, params Property[] members)
            => [.. Enumerable.Range(0, padding).Select(i => Member($"Pad{i}", i)), .. members];
        Property[][] lists =
        [
            [Member("A", 0), Member("A", 1), Member("Hidden", 2, isPublic: false)],
            Padded(16, Member("A", 3, isPublic: false), Member("B", 4), Member(null, 5), Member(null, 6)),
            [],
            [Member(null, 7, isPublic: false), Member("C", 8)],
            Padded(20, Member("A", 9), Member("B", 10)),
            [Member("B", 11, isPublic: false), Member("B", 12)],
            [Member(null, 13), Member("A", 14)],
            Padded(3, Member("Hidden", 15, isPublic: false)),
            [Member("C", 16), Member("C", 17)],
            Padded(16, Member(null, 18)),
        ];
        var providers = lists.Select((members, position) => new Evaluator.ResolvedOpen(
            $"P{position}", new Expr.Resolve($"P{position}"), new Algorithm.User(null, [], [], members, OutputBundle.Empty))).ToList();
        var index = new Evaluator.ResolvedOpenLevel.MemberIndex(providers);
        Assert.Equal(lists.Sum(static members => (long)members.Length), index.MemberCount);
        Assert.True(index.IndexesListsOf(providers));

        var scan = new PropertyBindingIndexCache();
        foreach (var name in new[] { "A", "B", "C", "Hidden", "Pad0", "Pad19", "Absent", null })
        {
            var expected = providers
                .Select((provider, position) => (Position: position, Member: scan.LookupPublic(provider.Lib.Properties, name!)))
                .Where(static offer => offer.Member is not null)
                .ToList();
            var offered = new List<(int Position, Property? Member)>();
            var cursor = index.FirstOffer(name!);
            for (var position = index.Offer(ref cursor, out var member); position >= 0; position = index.Offer(ref cursor, out member))
                offered.Add((position, member));
            Assert.Equal(expected.Select(static offer => offer.Position), offered.Select(static offer => offer.Position));
            Assert.All(expected.Zip(offered), pair => Assert.Same(pair.First.Member, pair.Second.Member));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MemberIndexStorage_GrowsWithOffers(bool publicDuplicates)
    {
        static Evaluator.ResolvedOpen[] Providers(int padding, bool publicDuplicates)
            => Enumerable.Range(0, 9).Select(i =>
            {
                var name = $"W{i}";
                var offer = new Property(name, Value(i), IsPublic: true);
                var filler = publicDuplicates ? offer : new Property("Private", Value(i));
                Property[] members = [offer, .. Enumerable.Repeat(filler, padding)];
                var block = new Algorithm.User(null, [], [], members, OutputBundle.Empty);
                return new Evaluator.ResolvedOpen(name, new Expr.AlgorithmExpr(block), block);
            }).ToArray();

        static long BuildBytes(Evaluator.ResolvedOpen[] providers)
        {
            var start = GC.GetAllocatedBytesForCurrentThread();
            var index = new Evaluator.ResolvedOpenLevel.MemberIndex(providers);
            var bytes = GC.GetAllocatedBytesForCurrentThread() - start;
            GC.KeepAlive(index);
            return bytes;
        }

        var small = Providers(0, publicDuplicates);
        var padded = Providers(4096, publicDuplicates);
        _ = BuildBytes(small);
        var smallBytes = BuildBytes(small);
        var paddedBytes = BuildBytes(padded);
        // Both levels offer nine members. Reserving an entry for each visited member adds over 500 KiB.
        Assert.InRange(paddedBytes, 0, smallBytes + 4096);
    }

    [Fact]
    public async Task AWideLevelHoldingAnUnnamedHostMember_ReadsItsNamedMembersAsANarrowOneDoes()
    {
        // The evaluator-level regression of the unnamed host member: the second read of a wide memoized level
        // builds its index, which threw `ArgumentNullException` for a public member with a null name.
        foreach (var width in new[] { 8, 9 })
        {
            var opens = Enumerable.Range(0, width).Select(i => (Expr)new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
                i == 0
                    ? [new Property(null!, Value(99), IsPublic: true), new Property("W0", Value(0), IsPublic: true)]
                    : [new Property($"W{i}", Value(i), IsPublic: true)],
                OutputBundle.Empty))).ToArray();
            var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], opens, [],
                [new Expr.Resolve("W0"), new Expr.Resolve($"W{width - 1}"), new Expr.Resolve("W0")]));
            var (observed, index) = await OpenProviderIndexing.OnBothRoutesWithIndexWorkAsync(program);
            Assert.Equal($"ok S[0, {width - 1}, 0]", observed.Outcome);
            Assert.Equal(width > Evaluator.OpenProviderLinearIndexLimit
                ? new OpenProviderIndexing.MemberIndexWork(1, width + 1, 0)
                : OpenProviderIndexing.MemberIndexWork.None, index);
        }
    }

    [Fact]
    public void TheRunsMemberIndexes_AreKeyedByMemberLists_NeverByTheProvidersTheyWereBuiltFor()
    {
        // Two states of one level differ in their providers' wiring, never in their lists: a rewired view of each
        // declaration (another parent) takes the same index, and so does a later state after another order was
        // served. The same lists in another order are another index. An index keeps the declarations' lists.
        var blocks = Enumerable.Range(0, 9)
            .Select(static i => new Algorithm.User(null, [], [], [new Property($"W{i}", Value(i), IsPublic: true)], OutputBundle.Empty))
            .ToArray();
        static IReadOnlyList<Evaluator.ResolvedOpen> Level(IEnumerable<Algorithm> providers)
            => providers.Select(static (provider, position) => new Evaluator.ResolvedOpen($"(inline#{position})", new Expr.AlgorithmExpr(provider), provider)).ToList();
        var rewired = blocks.Select(static block => (Algorithm)(block with { Parent = new ScopeCtx(null, [], []) })).ToArray();
        Assert.All(rewired.Zip(blocks), pair => Assert.Same(pair.Second.Properties, pair.First.Properties));

        var observations = new EvaluationObservations();
        var cache = new Evaluator.OpenLevelMemberIndexCache();
        var first = cache.IndexOf(Level(blocks), observations);
        Assert.Same(first, cache.IndexOf(Level(rewired), observations));
        var reversed = cache.IndexOf(Level(Enumerable.Reverse(blocks)), observations);
        Assert.NotSame(first, reversed);
        Assert.Same(first, cache.IndexOf(Level(rewired), observations));
        Assert.Same(reversed, cache.IndexOf(Level(Enumerable.Reverse(rewired)), observations));
        Assert.Equal(2, cache.Count);
        Assert.Equal(new OpenProviderIndexing.MemberIndexWork(2, 18, 3), OpenProviderIndexing.MemberIndexWork.Of(observations));
        Assert.All(first.Lists.Zip(blocks), pair => Assert.Same(pair.Second.Properties, pair.First));

        // One cache per run: a run reuses its own, another run never sees it.
        var run = EvaluationBudget.Create(null);
        Assert.Same(run.OpenLevelMemberIndexes, run.OpenLevelMemberIndexes);
        Assert.NotSame(run.OpenLevelMemberIndexes, EvaluationBudget.Create(null).OpenLevelMemberIndexes);
    }

    [Fact]
    public async Task AHostConstructedWideLevel_IsResolvedOnEveryRead_AndNeverIndexed()
    {
        // The host level of AHostConstructedLevel_IsResolvedOnEveryRead_AndNeverWritten, widened past the index
        // threshold: it has no level state, so each read resolves and scans it again and nothing is indexed (the
        // root's own level, read once for `Run`, is the fourth resolution).
        const int width = 9;
        var host = new ScopeCtx(null,
            Enumerable.Range(0, width).Select(static i => (Expr)new Expr.Resolve($"M{i}")).ToArray(),
            Enumerable.Range(0, width).Select(static i => new Property($"M{i}",
                new Algorithm.User(null, [], [], [new Property($"V{i}", Value(i), IsPublic: true)], OutputBundle.Empty))).ToArray());
        var block = new Algorithm.User(host, [], [], [new Property("Run", new Algorithm.User(null, [], [], [],
            [new Expr.Resolve("V0"), new Expr.Resolve("V8"), new Expr.Resolve("V0")]), IsPublic: true)], OutputBundle.Empty);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.AlgorithmExpr(block)], [], [new Expr.Resolve("Run")]));

        var (observed, index) = await OpenProviderIndexing.OnBothRoutesWithIndexWorkAsync(program);
        Assert.Equal(new OpenProviderIndexing.Observation("ok S[0, 8, 0]", 4, 3 * width + 1, 0, 0, 0, 4, 0), observed);
        Assert.Equal(OpenProviderIndexing.MemberIndexWork.None, index);
        Assert.Null(host.StaticOpenLevel);
    }
}
