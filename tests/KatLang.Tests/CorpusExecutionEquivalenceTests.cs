using KatLang.Evaluation.Caching;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// Execution-policy equivalence over the two shared corpora (the canonical
/// language spec and the semantic-explorer corpus, ~1,700 programs together).
///
/// <para>The corpora pin what each program MEANS. These tests pin that the
/// meaning does not depend on which internal execution policy runs it: the
/// optimizers, the per-run zero-argument property cache, and the flattening
/// host entry point must all observe the same value, emitted count, and error
/// category as the plain generic execution. Every relation here is a documented
/// invariant, so a failure is a production defect rather than a corpus edit.</para>
///
/// <para>The plain-versus-counted evaluator comparison is not repeated here:
/// <see cref="SemanticExplorerHarness.Observe"/> applies it to every case of
/// both corpora already (mirroring the generated Lean artifact's <c>obs</c>).</para>
/// </summary>
public class CorpusExecutionEquivalenceTests
{
    /// <summary>
    /// Every corpus program that parses: language-spec cases and their probes,
    /// plus every semantic-explorer surface case.
    /// </summary>
    public static IReadOnlyList<(string Id, Expr Program)> Corpus { get; } = BuildCorpus();

    private static IReadOnlyList<(string, Expr)> BuildCorpus()
    {
        var sources = new List<(string Id, string Source)>();
        foreach (var specCase in LanguageSpecCorpus.AllCases())
        {
            if (specCase.Outcome != SpecOutcome.ParseError)
                sources.Add(("spec:" + specCase.Id, specCase.Source));

            for (var i = 0; i < specCase.Probes.Count; i++)
                sources.Add(($"spec:{specCase.Id}#probe{i}", specCase.Probes[i].Probe));
        }

        foreach (var explorerCase in SemanticExplorerCorpus.AllCases())
            sources.Add(("explorer:" + explorerCase.Id, explorerCase.Source));

        var programs = new List<(string, Expr)>(sources.Count);
        foreach (var (id, source) in sources)
        {
            var parsed = Parser.Parse(source);
            if (!parsed.HasErrors)
                programs.Add((id, new Expr.Block(parsed.Root)));
        }

        return programs;
    }

    private static string Neutral(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? "err " + SemanticExplorerHarness.ErrorCategory(result.Error)
            : $"ok raw={SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount}";

    private static void AssertNoMismatches(List<string> mismatches, int compared)
        => Assert.True(
            mismatches.Count == 0,
            $"{mismatches.Count} of {compared} corpus programs disagreed:\n"
            + string.Join("\n", mismatches.Take(25)));

    /// <summary>
    /// The loop and sequence-pipeline optimizers are documented as
    /// meaning-preserving. <see cref="OptimizerEquivalenceSweepTests"/> crosses
    /// their eligible shapes exhaustively; this runs the same relation over the
    /// corpora, whose programs exercise spread, deconstruction, patterned and
    /// clause-family calls, and list values instead.
    /// </summary>
    [Fact]
    public void Optimized_MatchesGeneric()
    {
        var mismatches = new List<string>();
        foreach (var (id, program) in Corpus)
        {
            var optimized = Neutral(Evaluator.RunCountedObserved(program, enableOptimizations: true).Result);
            var generic = Neutral(Evaluator.RunCountedObserved(program, enableOptimizations: false).Result);
            if (optimized != generic)
                mismatches.Add($"{id}: optimized={optimized} generic={generic}");
        }

        AssertNoMismatches(mismatches, Corpus.Count);
    }

    /// <summary>
    /// The zero-argument property cache is a per-run reuse optimization: `A`
    /// may serve a cached result where `A()` bypasses that entry, but neither
    /// the cached value nor its re-counted boundary may differ from recomputing
    /// the property every time.
    /// </summary>
    [Fact]
    public void CachedZeroArgProperties_MatchUncachedRecomputation()
    {
        var mismatches = new List<string>();
        foreach (var (id, program) in Corpus)
        {
            var cached = Neutral(Evaluator.RunCounted(program, new RunScopedZeroArgPropertyResultCache()));
            var uncached = Neutral(Evaluator.RunCounted(program, UncachedZeroArgPropertyResultCache.CreateForRun()));
            if (cached != uncached)
                mismatches.Add($"{id}: cached={cached} uncached={uncached}");
        }

        AssertNoMismatches(mismatches, Corpus.Count);
    }

    /// <summary>
    /// <c>RunFlat</c> is the host-boundary flattening entry point. It must be
    /// exactly <c>ToHostAtoms</c> of the ordinary run — same success/failure
    /// decision, same atoms — never a second evaluation strategy.
    /// </summary>
    [Fact]
    public void RunFlat_MatchesHostAtomsOfRun()
    {
        var mismatches = new List<string>();
        foreach (var (id, program) in Corpus)
        {
            var flat = Evaluator.RunFlat(program);
            var run = Evaluator.Run(program);
            if (flat.IsError != run.IsError)
            {
                mismatches.Add($"{id}: RunFlat.IsError={flat.IsError} Run.IsError={run.IsError}");
                continue;
            }

            if (flat.IsError)
                continue;

            var flatAtoms = string.Join(",", flat.Value);
            var runAtoms = string.Join(",", run.Value.ToHostAtoms());
            if (flatAtoms != runAtoms)
                mismatches.Add($"{id}: RunFlat=[{flatAtoms}] Run.ToHostAtoms=[{runAtoms}]");
        }

        AssertNoMismatches(mismatches, Corpus.Count);
    }

    public static TheoryData<string, string> BuiltinDotSpellings()
    {
        var values = new[]
        {
            "(1, 2, 3)", "[1, 2, 3]", "7", "()", "[]", "((1, 2), 3)", "[[1, 2], 3]", "('a', 'b')", "'ab'",
        };
        var calls = new (string Name, string Args)[]
        {
            ("count", ""), ("sum", ""), ("first", ""), ("last", ""), ("min", ""), ("max", ""), ("avg", ""),
            ("order", ""), ("orderDesc", ""), ("distinct", ""), ("atoms", ""),
            ("take", "2"), ("skip", "1"), ("contains", "1"),
            ("map", "Mapper"), ("filter", "Predicate"), ("reduce", "Reducer, 0"),
        };

        var data = new TheoryData<string, string>();
        foreach (var value in values)
        {
            foreach (var (name, args) in calls)
                data.Add(value, name + (args.Length == 0 ? "" : "(" + args + ")"));
        }

        return data;
    }

    /// <summary>
    /// Dotted-call equivalence for the collection builtins: `A.B(args)` means
    /// exactly `B(A, args)` — the receiver fills the fixed `collection`
    /// parameter with no builtin-specific placement. The two spellings take
    /// different evaluator paths (dot dispatch with receiver injection versus
    /// plain call assembly), so agreement on every builtin and every collection
    /// KIND is the pin. Only `count` and `take` had a dotted differential case
    /// before.
    /// </summary>
    [Theory]
    [MemberData(nameof(BuiltinDotSpellings))]
    public void DottedBuiltinCall_MatchesPlainCallWithReceiverAsFirstArgument(string value, string dotCall)
    {
        const string prelude = "Mapper(a) = 1\nPredicate(a) = 1\nReducer(a, b) = 0\n";

        var open = dotCall.IndexOf('(', StringComparison.Ordinal);
        var name = open < 0 ? dotCall : dotCall[..open];
        var args = open < 0 ? "" : ", " + dotCall[(open + 1)..^1];

        var plainSource = $"{prelude}V = {value}\n{name}(V{args})";
        var dotSource = $"{prelude}V = {value}\nV.{dotCall}";

        var plainParsed = Parser.Parse(plainSource);
        var dotParsed = Parser.Parse(dotSource);
        Assert.False(plainParsed.HasErrors, plainSource);
        Assert.False(dotParsed.HasErrors, dotSource);

        var plain = Neutral(Evaluator.RunCounted(new Expr.Block(plainParsed.Root)));
        var dotted = Neutral(Evaluator.RunCounted(new Expr.Block(dotParsed.Root)));

        Assert.Equal(plain, dotted);
    }
}
