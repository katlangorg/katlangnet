using System.Globalization;
using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using static KatLang.Tests.Randomness.SeededRun;

namespace KatLang.Tests.Randomness;

/// <summary>
/// The public reproducibility contract of <see cref="RunOptions.RandomSeed"/> and the
/// direct <c>Evaluator.Run*</c> seed overloads: a seed selects ONE run-scoped stream
/// consumed in evaluation order by both random operations in every spelling;
/// separate runs, entry points, and sync/async routing replay it identically; the
/// stream is never continued across runs or shared between them; unseeded runs stay
/// nondeterministic. Expected VALUES come from the test-side
/// <see cref="ReferenceRandomOracle"/>, never from the implementation.
/// </summary>
public class SeededRandomnessTests
{
    private const long Seed = 20260914;

    private const string MixedSpellings =
        "Math.Random(0, 1)\n" +
        "Math.RandomInt(0, 100)\n" +
        "random(2, 6)\n" +
        "randomInt(-3, 3)\n" +
        "Math.RandomInt(1e34 - 1, 1e34)\n" +
        "Math.Random(-7, 5)";

    /// <summary>The oracle's expectation for <see cref="MixedSpellings"/> under a seed, in evaluation order.</summary>
    private static IReadOnlyList<Decimal128> ExpectedMixedSpellings(long seed)
    {
        var words = Words(seed);
        return
        [
            ReferenceRandomOracle.Random(words, D(0), D(1)),
            ReferenceRandomOracle.RandomInt(words, 0, 100),
            ReferenceRandomOracle.Random(words, D(2), D(6)),
            ReferenceRandomOracle.RandomInt(words, -3, 3),
            ReferenceRandomOracle.RandomInt(words, BigInteger.Pow(10, 34) - 1, BigInteger.Pow(10, 34)),
            ReferenceRandomOracle.Random(words, D(-7), D(5)),
        ];
    }

    // ── §20.3 Independent end-to-end golden ──────────────────────────────────

    [Theory]
    [InlineData(0L)]
    [InlineData(1L)]
    [InlineData(-1L)]
    [InlineData(long.MinValue)]
    [InlineData(long.MaxValue)]
    [InlineData(Seed)]
    public void SeededProgram_MatchesTheIndependentOracle_EndToEnd(long seed)
    {
        // Pinned SplitMix64 words → 64-bit bounded rejection → high * 1e17 + low →
        // * 1e-34 → Decimal128 scaling → 128-bit rejection for RandomInt, all derived
        // by the test-side oracle; the evaluator must agree value for value, in order.
        AssertSameAtoms(ExpectedMixedSpellings(seed), Atoms(MixedSpellings, seed));
    }

    [Fact]
    public void SeededUnitFraction_RendersTheFull34DigitLattice()
    {
        // The unit fraction's display carries the exact 34-digit lattice text: the
        // expected string is formed from the oracle's lattice integer, not captured.
        var words = Words(Seed);
        var high = new BigInteger(ReferenceRandomOracle.BoundedInt64(words, 100_000_000_000_000_000));
        var low = new BigInteger(ReferenceRandomOracle.BoundedInt64(words, 100_000_000_000_000_000));
        var lattice = ((high * BigInteger.Pow(10, 17)) + low).ToString(CultureInfo.InvariantCulture).PadLeft(34, '0');

        Assert.Equal("0." + lattice, Display(Success("Math.Random(0, 1)", Seed)));
    }

    // ── §22.1 Basic reproducibility ───────────────────────────────────────────

    [Fact]
    public void SameSeed_SeparateEngineRuns_ProduceIdenticalStructuredResults()
    {
        var first = Success(MixedSpellings, Seed);
        var second = Success(MixedSpellings, Seed);

        AssertSameValue(first.Value, second.Value);
        Assert.Equal(first.EmittedCount, second.EmittedCount);
        Assert.Equal(Display(first), Display(second));
    }

    [Fact]
    public async Task SameSeed_SyncAndAsyncEntryPoints_AreIdentical()
    {
        var sync = Success(MixedSpellings, Seed);
        var asyncFastPath = await SuccessAsync(MixedSpellings, Seed);

        // An unused ASYNC host operation forces the async twin family; the stream
        // must be the same there too.
        var twinOptions = new RunOptions
        {
            RandomSeed = Seed,
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("SeedProbeUnusedAsyncZz", (_, _) => ValueTask.FromResult<Result>(new Result.Atom(1)))),
        };
        var twin = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(MixedSpellings, twinOptions));

        AssertSameValue(sync.Value, asyncFastPath.Value);
        AssertSameValue(sync.Value, twin.Value);
        AssertSameAtoms(ExpectedMixedSpellings(Seed), twin.Atoms);
    }

    [Fact]
    public void ReusedRunOptionsObject_RestartsTheStreamForEveryRun()
    {
        var options = Options(Seed);
        var expected = ExpectedMixedSpellings(Seed);

        for (var run = 0; run < 3; run++)
        {
            var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(MixedSpellings, options));
            AssertSameAtoms(expected, success.Atoms);
        }
    }

    [Fact]
    public void DifferentSeeds_SelectDifferentStreams()
    {
        Assert.NotEqual(Display(Success(MixedSpellings, 1)), Display(Success(MixedSpellings, 2)));
        Assert.NotEqual(Display(Success(MixedSpellings, 5)), Display(Success(MixedSpellings, -5)));
        Assert.NotEqual(Display(Success(MixedSpellings, 0)), Display(Success(MixedSpellings, long.MinValue)));
    }

    [Fact]
    public void UnseededRuns_RemainNondeterministic()
    {
        // A coarse unseeded wiring check: a fixed default state would make these
        // draws all equal. The factory and reference tests provide deterministic pins.
        var draws = Enumerable.Range(0, 8)
            .Select(_ => Display(Success("Math.RandomInt(0, 1e30)", null)))
            .Distinct()
            .Count();

        Assert.True(draws > 1, "unseeded evaluation produced one constant value");
    }

    [Fact]
    public void FreshContextsAndBudgets_OwnDistinctUnseededSources()
    {
        var first = Evaluator.EvalCtx.Empty;
        var second = Evaluator.EvalCtx.Empty;
        Assert.NotSame(first.Budget, second.Budget);
        Assert.NotSame(first.Budget.RandomSource, second.Budget.RandomSource);

        // Direct budget creation without a seed is unseeded: sixteen fresh budgets
        // cannot all start their streams on the same word unless entropy is fixed.
        var firstWords = Enumerable.Range(0, 16)
            .Select(_ => EvaluationBudget.Create(null).RandomSource.NextUInt64())
            .Distinct()
            .Count();
        Assert.True(firstWords > 1, "EvaluationBudget.Create(null) produced one constant stream");

        // And a seeded budget starts exactly the seed's stream.
        Assert.Equal(Words(Seed).Next(), EvaluationBudget.Create(null, randomSeed: Seed).RandomSource.NextUInt64());
    }

    // ── §22.2 Stream behavior ─────────────────────────────────────────────────

    [Fact]
    public void ConsecutiveCalls_ConsumeSuccessiveStreamWords()
    {
        // A 2^32 span divides 2^128, so each RandomInt is one un-rejected 128-bit
        // draw (two words) and its value is the LOW word modulo 2^32: call k returns
        // word 2k of the pinned stream, which pins successive consumption directly.
        const string source = "Math.RandomInt(0, 4294967296)\nMath.RandomInt(0, 4294967296)\nMath.RandomInt(0, 4294967296)\nMath.RandomInt(0, 4294967296)";
        var words = Words(Seed);
        var expected = Enumerable.Range(0, 4).Select(_ => LowWordMod2Pow32(words)).ToArray();

        AssertSameAtoms(expected, Atoms(source, Seed));
    }

    [Fact]
    public void RemovingAnEarlierRandomCall_ChangesTheLaterValues()
    {
        const string two = "Math.RandomInt(0, 4294967296)\nMath.RandomInt(0, 4294967296)";
        const string one = "Math.RandomInt(0, 4294967296)";

        var twoAtoms = Atoms(two, Seed);
        var oneAtoms = Atoms(one, Seed);

        // The remaining call now consumes the stream from its beginning: it equals the
        // removed call's value, not its own former value.
        Assert.Equal(twoAtoms[0], Assert.Single(oneAtoms));
        Assert.NotEqual(twoAtoms[1], oneAtoms[0]);
    }

    [Fact]
    public void RandomAndRandomInt_InEverySpelling_ConsumeOneSharedStreamInEvaluationOrder()
    {
        // Reordering the same calls changes which stream positions each consumes, so
        // the values are the oracle's values for THAT order — only one shared stream
        // consumed in evaluation order produces both sequences.
        const string reordered =
            "randomInt(-3, 3)\n" +
            "Math.Random(0, 1)\n" +
            "random(2, 6)\n" +
            "Math.RandomInt(0, 100)";
        var words = Words(Seed);
        IReadOnlyList<Decimal128> expected =
        [
            ReferenceRandomOracle.RandomInt(words, -3, 3),
            ReferenceRandomOracle.Random(words, D(0), D(1)),
            ReferenceRandomOracle.Random(words, D(2), D(6)),
            ReferenceRandomOracle.RandomInt(words, 0, 100),
        ];

        AssertSameAtoms(expected, Atoms(reordered, Seed));
        AssertSameAtoms(ExpectedMixedSpellings(Seed), Atoms(MixedSpellings, Seed));
    }

    [Fact]
    public void AliasAndCanonicalSpellings_AreTheSameOperationOnTheStream()
    {
        var canonical = Atoms("Math.Random(0, 1), Math.RandomInt(0, 100)", Seed);
        var aliased = Atoms("random(0, 1), randomInt(0, 100)", Seed);

        AssertSameAtoms(canonical, aliased);
    }

    // ── §22.3 Validation consumes nothing ─────────────────────────────────────

    public static TheoryData<string, string, string> InvalidCalls => new()
    {
        { "Random", "1", "0" },                       // start >= end
        { "Random", "1", "1" },
        { "Random", "Infinity", "1" },                // non-finite bound
        { "Random", "-9e6144", "9e6144" },            // range too large (the difference overflows to infinity)
        { "RandomInt", "0.5", "10" },                 // non-integer bound
        { "RandomInt", "0", "2e34" },                 // beyond the exact-integer domain
        { "RandomInt", "5", "5" },                    // start >= end
        { "RandomInt", "NaN", "1" },
    };

    [Theory]
    [MemberData(nameof(InvalidCalls))]
    public void InvalidRandomCall_FailsWithoutConsumingAWord_SoTheNextDrawIsTheBaseline(
        string member, string start, string end)
    {
        // Validation runs before any draw at the ONE Math-native dispatch both engines
        // share: the same scripted words yield the same value whether or not an
        // invalid call preceded the valid one.
        var withInvalid = new ScriptedWordSource(SampleWords);
        var invalid = Evaluator.ApplyMathNative(member, [D(start), D(end)], withInvalid);
        Assert.True(invalid.IsError);
        Assert.IsType<EvalError.IllegalInEval>(invalid.Error);
        Assert.Equal(SampleWords.Length, withInvalid.Remaining);

        var afterInvalid = Evaluator.ApplyMathNative(member, [D(0), D(10)], withInvalid);
        var baseline = Evaluator.ApplyMathNative(member, [D(0), D(10)], new ScriptedWordSource(SampleWords));
        Assert.True(afterInvalid.IsOk && baseline.IsOk);
        AssertSameValue(baseline.Value, afterInvalid.Value);
    }

    private static readonly ulong[] SampleWords =
        [0x1234_5678_9ABC_DEF0UL, 0x0FED_CBA9_8765_4321UL, 0x0000_0000_0000_002AUL, 0x7777_7777_7777_7777UL];

    // ── §22.4 An unused seed changes nothing ──────────────────────────────────

    public static TheoryData<string> DeterministicSpecCaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var specCase in LanguageSpec.LanguageSpecCorpus.AllCases().OrderBy(static c => c.Id, StringComparer.Ordinal))
        {
            // The canonical corpus carries no random native (its expectations are
            // exact); the guard keeps this differential honest should one ever appear.
            if (!specCase.Source.Contains("andom", StringComparison.Ordinal))
                data.Add(specCase.Id);
        }

        return data;
    }

    private static readonly IReadOnlyDictionary<string, LanguageSpec.SpecCase> SpecById =
        LanguageSpec.LanguageSpecCorpus.AllCases().ToDictionary(static c => c.Id, StringComparer.Ordinal);

    [Theory]
    [MemberData(nameof(DeterministicSpecCaseIds))]
    public void UnusedSeed_ChangesNoDeterministicProgramOutcome(string caseId)
    {
        var source = SpecById[caseId].Source;

        var baseline = KatLangEngine.Run(source);
        var seeded = KatLangEngine.Run(source, Options(Seed));

        Assert.Equal(baseline.GetType(), seeded.GetType());
        Assert.Equal(baseline.ToDisplayString(), seeded.ToDisplayString());
    }

    // ── §22.5 Convenience APIs and direct evaluator overloads ─────────────────

    [Fact]
    public async Task EngineConveniences_HonorTheSeed()
    {
        var expected = ExpectedMixedSpellings(Seed);
        var options = Options(Seed);

        AssertSameAtoms(expected, KatLangEngine.EvaluateToAtoms(MixedSpellings, options));
        AssertSameAtoms(expected, await KatLangEngine.EvaluateToAtomsAsync(MixedSpellings, options));

        var expectedText = string.Join(" ", expected.Select(static atom => atom.ToString(CultureInfo.InvariantCulture)));
        var syncText = KatLangEngine.EvaluateToString(MixedSpellings, options);
        var asyncText = await KatLangEngine.EvaluateToStringAsync(MixedSpellings, options);
        Assert.Equal(syncText, asyncText);
        Assert.Equal(expectedText.Split(' ').Length, syncText.Split(' ').Length);
        AssertSameAtoms(expected, syncText.Split(' ').Select(D).ToArray());
    }

    [Fact]
    public async Task DirectEvaluatorSeedOverloads_InitializeTheSameStreamAsTheEngine()
    {
        var expected = ExpectedMixedSpellings(Seed);
        var program = Program(MixedSpellings);
        var hostOperations = HostOperations.Create(
            HostOperation.Create("SeedProbeUnusedSyncZz", static (_, _) => new Result.Atom(1)));

        AssertSameAtoms(expected, Unwrap(Evaluator.Run(program, null, Seed, CancellationToken.None)).ToHostAtoms());
        AssertSameAtoms(expected, Unwrap(Evaluator.Run(program, hostOperations, null, Seed, CancellationToken.None)).ToHostAtoms());
        AssertSameAtoms(expected, Unwrap(await Evaluator.RunAsync(program, null, Seed, CancellationToken.None)).ToHostAtoms());
        AssertSameAtoms(expected, Unwrap(await Evaluator.RunAsync(program, hostOperations, null, Seed, CancellationToken.None)).ToHostAtoms());
        AssertSameAtoms(expected, Unwrap(Evaluator.RunFlat(program, null, Seed, CancellationToken.None)));
        AssertSameAtoms(expected, Unwrap(await Evaluator.RunFlatAsync(program, null, Seed, CancellationToken.None)));

        // The seedless overloads stay unseeded: two calls do not agree by construction.
        var unseeded = Enumerable.Range(0, 8)
            .Select(_ => Unwrap(Evaluator.RunFlat(program, null, CancellationToken.None))[1])
            .Distinct()
            .Count();
        Assert.True(unseeded > 1);
    }

    [Fact]
    public void InternalRunFunnels_HonorTheSeed()
    {
        var expected = ExpectedMixedSpellings(Seed);
        var program = Program(MixedSpellings);

        AssertSameAtoms(expected, Unwrap(Evaluator.RunCounted(program, new RunScopedZeroArgPropertyResultCache(), randomSeed: Seed)).Value.ToHostAtoms());
        AssertSameAtoms(expected, Unwrap(Evaluator.RunCountedObserved(program, randomSeed: Seed).Result).Value.ToHostAtoms());
        AssertSameAtoms(expected, Unwrap(Evaluator.RunObserved(program, new EvaluationObservations(), randomSeed: Seed)).ToHostAtoms());
        AssertSameAtoms(
            expected,
            Unwrap(Evaluator.RunCountedWithTopLevelProperty(
                program, "DisplayDecimals", new RunScopedZeroArgPropertyResultCache(), randomSeed: Seed)).Output.Value.ToHostAtoms());
    }

    [Fact]
    public async Task ParserEntryPoints_IgnoreTheSeed()
    {
        var seeded = Parser.Parse(MixedSpellings, Options(Seed));
        var seededAsync = await Parser.ParseAsync(MixedSpellings, Options(Seed));
        var plain = Parser.Parse(MixedSpellings);

        Assert.False(seeded.HasErrors);
        Assert.False(seededAsync.HasErrors);
        Assert.Equal(plain.Diagnostics.Count, seeded.Diagnostics.Count);
        Assert.Equal(plain.Diagnostics.Count, seededAsync.Diagnostics.Count);

        // A tree parsed with a seeded options object is an ordinary program: only the
        // RUN decides the stream.
        var unseededRun = Unwrap(Evaluator.RunFlat(new Expr.AlgorithmExpr(seeded.Root)));
        var seededRun = Unwrap(Evaluator.RunFlat(new Expr.AlgorithmExpr(seeded.Root), null, Seed, CancellationToken.None));
        AssertSameAtoms(ExpectedMixedSpellings(Seed), seededRun);
        Assert.Equal(seededRun.Count, unseededRun.Count);
    }

    [Fact]
    public async Task AdditionalErrorEvaluation_AfterLoadFailure_RunsUnderTheSeed()
    {
        // A load failure the front end can still evaluate past selects the separate
        // additional-error evaluation route; the primary route never starts. It
        // receives the seed and starts a FRESH
        // stream from it: the draw is the oracle's FIRST value for the seed, so dividing
        // by (draw - thatValue) is deterministically the division-by-zero additional
        // error, while any other pivot yields none. Unseeded, the first outcome would
        // occur with probability 1e-6.
        var pivot = ReferenceRandomOracle.RandomInt(Words(Seed), 0, 1_000_000);
        static string Source(Decimal128 pivot)
            => "A = load('https://katlang.org/seed/not-katlang.kat')\n"
                + $"1 / (Math.RandomInt(0, 1000000) - {pivot.ToString(CultureInfo.InvariantCulture)})";
        var options = new RunOptions
        {
            RandomSeed = Seed,
            DownloadCode = static (_, _) => ValueTask.FromResult("<!doctype html><html><body>Not found</body></html>"),
        };

        // Advance a previous evaluator run under the SAME options before entering
        // the error route. Retaining its partially consumed stream would miss pivot.
        var prior = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync("Math.RandomInt(0, 1000000)", options));
        Assert.Equal(pivot, Assert.Single(prior.Atoms));

        var dividing = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(Source(pivot), options));
        Assert.Contains(dividing.Errors, static error => error.Message.Contains("Division by zero", StringComparison.Ordinal));
        Assert.Equal(dividing.ToDisplayString(), (await KatLangEngine.RunAsync(Source(pivot), options)).ToDisplayString());

        var clean = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(Source(pivot + Decimal128.One), options));
        Assert.DoesNotContain(clean.Errors, static error => error.Message.Contains("Division by zero", StringComparison.Ordinal));
    }

    private static T Unwrap<T>(EvalResult<T> result)
    {
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        return result.Value;
    }

    /// <summary>Scripts the RAW seam so the shared Math-native dispatch is exercised over known words.</summary>
    internal sealed class ScriptedWordSource(IEnumerable<ulong> words) : RandomSource
    {
        private readonly Queue<ulong> _words = new(words);

        public int Remaining => _words.Count;

        public override ulong NextUInt64() => _words.Dequeue();
    }
}
