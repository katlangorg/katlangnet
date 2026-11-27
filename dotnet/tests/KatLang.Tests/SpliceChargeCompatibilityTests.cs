using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Compatibility pins for the aggregate's splice charge (`evaluator-and-hosting.md` § SPLICES
/// CHARGE THE AGGREGATE). The owner decision on that rule is pending; the options and the values
/// each one gives for these programs are in
/// `docs/design/splice-charge-owner-decision-brief-2026-11.md`. C#-only host source-processing
/// policy: Lean has no module loading and no source budget.
///
/// <para><b>Current-rule pins.</b> A cache-hit splice charges the module's elaborated weight — its
/// text plus everything its own walk charged, nested splices included — so the aggregate counts
/// the import graph UNFOLDED INTO A TREE: a module's text is charged once per import path that
/// reaches it, exponentially many in the depth of a shared import DAG. Each pin states the
/// smallest admitting <see cref="SourceProcessingLimits.MaxAggregateSourceLength"/>: admitted at
/// that total, refused one code unit below it. An adopted rule changes these totals deliberately.</para>
///
/// <para><b>Compatibility requirements.</b> One download per successfully cached canonical URL; distinct URLs are
/// distinct modules whatever their bytes; a refusal is a structured
/// <see cref="DiagnosticCode.AggregateSourceLengthExceeded"/> (a parse failure eagerly, an
/// evaluation failure at a deferred selection); an unselected deferred branch does no source work;
/// and the aggregate continues to charge distinct materializations that splice a completed module.</para>
///
/// <para>Every downloader is deterministic and in memory — no network.</para>
/// </summary>
public class SpliceChargeCompatibilityTests
{
    private const string Base = "https://katlang.org/splice-charge/";

    private static string Url(string name) => Base + name + ".kat";

    private sealed class Server(IReadOnlyDictionary<string, string> files)
    {
        public List<string> Requests { get; } = [];

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            lock (Requests)
                Requests.Add(url);
            return ValueTask.FromResult(files[url]);
        }

        public RunOptions Options(long aggregateLimit) => new()
        {
            DownloadCode = Download,
            SourceProcessingLimits = new SourceProcessingLimits { MaxAggregateSourceLength = aggregateLimit },
        };
    }

    private static async Task<(ParseResult Parsed, Server Downloads)> Parse(
        string source, IReadOnlyDictionary<string, string> files, long aggregateLimit)
    {
        var server = new Server(files);
        return (await Parser.ParseAsync(source, server.Options(aggregateLimit)), server);
    }

    private static async Task<(RunResult Result, Server Downloads)> Run(
        string source, IReadOnlyDictionary<string, string> files, long aggregateLimit)
    {
        var server = new Server(files);
        return (await KatLangEngine.RunAsync(source, server.Options(aggregateLimit)), server);
    }

    /// <summary>Admitted at <paramref name="total"/>, refused by the aggregate one code unit below it.</summary>
    private static async Task<Server> AssertParseAdmitsExactly(string source, IReadOnlyDictionary<string, string> files, long total)
    {
        var (fits, downloads) = await Parse(source, files, total);
        Assert.Empty(fits.Diagnostics);

        var (over, _) = await Parse(source, files, total - 1);
        Assert.Contains(over.Diagnostics, d => d.Code == DiagnosticCode.AggregateSourceLengthExceeded);
        return downloads;
    }

    /// <summary>
    /// A diamond ladder: the shared leaf <c>t0</c>; at level i the modules <c>ai</c> and
    /// <c>bi</c> each open <c>t(i-1)</c>, and <c>ti</c> opens both. <paramref name="depth"/>
    /// levels give 3·depth + 1 modules, 4·depth written load sites and 2^depth import paths from
    /// the top module to the leaf.
    /// </summary>
    private static (Dictionary<string, string> Files, Dictionary<string, string[]> Loads) Ladder(int depth, string leafPadding = "")
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal) { [Url("t0")] = "public T0 = 3" + leafPadding };
        var loads = new Dictionary<string, string[]>(StringComparer.Ordinal) { [Url("t0")] = [] };
        for (var i = 1; i <= depth; i++)
        {
            var below = Url($"t{i - 1}");
            files[Url($"a{i}")] = $"open '{below}'\npublic A{i} = T{i - 1} + 1";
            loads[Url($"a{i}")] = [below];
            files[Url($"b{i}")] = $"open '{below}'\npublic B{i} = T{i - 1} + 2";
            loads[Url($"b{i}")] = [below];
            files[Url($"t{i}")] = $"open '{Url($"a{i}")}', '{Url($"b{i}")}'\npublic T{i} = A{i} + B{i}";
            loads[Url($"t{i}")] = [Url($"a{i}"), Url($"b{i}")];
        }

        return (files, loads);
    }

    /// <summary>
    /// THE CURRENT RULE as a model: a module's elaborated weight is its own text plus the weight
    /// of every load its text writes, whether that load downloads or splices a cached view.
    /// </summary>
    private static long UnfoldedWeight(string url, IReadOnlyDictionary<string, string> files, IReadOnlyDictionary<string, string[]> loads)
        => files[url].Length + loads[url].Sum(target => UnfoldedWeight(target, files, loads));

    // ── Current-rule pins ────────────────────────────────────────────────────

    [Fact]
    public async Task ImportDag_ChargesTheGraphUnfoldedIntoATree()
    {
        var (files, loads) = Ladder(3);
        var source = $"open '{Url("t3")}'\nT3";
        var total = source.Length + UnfoldedWeight(Url("t3"), files, loads);

        var (fits, downloads) = await Parse(source, files, total);
        Assert.Empty(fits.Diagnostics);
        Assert.Equal(files.Keys.Order(StringComparer.Ordinal), downloads.Requests.Order(StringComparer.Ordinal));

        // The last charge in walk order is b3's re-splice of t2, which charges t2's whole
        // unfolded weight (t2's own walk re-spliced t1, and t1's re-spliced t0).
        var (over, overDownloads) = await Parse(source, files, total - 1);
        var refused = Assert.Single(over.Diagnostics, d => d.Code == DiagnosticCode.AggregateSourceLengthExceeded);
        Assert.Contains(
            $"splicing the already loaded '{Url("t2")}' again ({UnfoldedWeight(Url("t2"), files, loads)} UTF-16 code units of elaborated module source)",
            refused.Message);
        Assert.Equal(files.Count, overDownloads.Requests.Count);
    }

    [Theory]
    [InlineData(1, 2)]
    [InlineData(2, 4)]
    [InlineData(3, 8)]
    [InlineData(4, 16)]
    public async Task SharedLeaf_IsChargedOncePerImportPath(int depth, int chargedCopies)
    {
        // One more code unit in the shared leaf raises the smallest admitting aggregate by the
        // number of times the rule counts the leaf's text: once per import path (2^depth), while
        // the leaf is downloaded once and named by two written load sites.
        var (files, loads) = Ladder(depth);
        var (padded, _) = Ladder(depth, leafPadding: " ");
        var source = $"open '{Url($"t{depth}")}'\nT{depth}";
        var total = source.Length + UnfoldedWeight(Url($"t{depth}"), files, loads);

        await AssertParseAdmitsExactly(source, files, total);
        var downloads = await AssertParseAdmitsExactly(source, padded, total + chargedCopies);
        Assert.Single(downloads.Requests, url => url == Url("t0"));
    }

    [Fact]
    public async Task DeferredSelection_ReSplicingTheEagerImportDag_ChargesItsUnfoldedWeightAgain()
    {
        // The parse charges the DAG once; the selected branch's re-splice of the top module
        // charges its whole unfolded weight again, so a limit that admits the parse can still
        // refuse the run at the selection (an evaluation failure, after a clean parse).
        var (files, loads) = Ladder(2);
        var top = Url("t2");
        var source = $"open '{top}'\nG(0) = 0\nG(n) = {{\n    open '{top}'\n    T2 + n\n}}\nG(1)\nT2";
        var weight = UnfoldedWeight(top, files, loads);
        var total = source.Length + 2 * weight;

        var (fits, downloads) = await Run(source, files, total);
        var success = Assert.IsType<RunResult.Success>(fits);
        Assert.Equal(new Decimal128[] { 22m, 21m }, success.Atoms);
        Assert.Equal(files.Count, downloads.Requests.Count);

        var (over, _) = await Run(source, files, total - 1);
        var failure = Assert.IsType<RunResult.EvalFailure>(over);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.AggregateSourceLengthExceeded, error.Code);
        Assert.Equal(new SourcePosition(4, 10), error.Span?.Start);
        Assert.Contains($"splicing the already loaded '{top}' again ({weight} UTF-16 code units of elaborated module source)", error.Message);

        var (parseOnly, _) = await Parse(source, files, total - 1);
        Assert.Empty(parseOnly.Diagnostics);
    }

    [Fact]
    public async Task ReSplice_ExcludesAnUnselectedDependencyAlreadyCachedElsewhere()
    {
        var hidden = Url("hidden");
        var top = Url("top");
        const string hiddenText = "public V = 'é😀'";
        var topText = $"public G(0) = 0\npublic G(n) = {{\n    open '{hidden}'\n    n\n}}";
        var files = new Dictionary<string, string> { [hidden] = hiddenText, [top] = topText };
        var source = $"Known = load('{hidden}')\nA = load('{top}')\nB = load('{top}')\n0";
        // The root preloads hidden. The module names it only in a deferred branch. Its
        // first walk never splices hidden, so its cached weight includes only its own text.
        // String.Length is the UTF-16 charge, including the non-BMP character in hidden.
        var total = source.Length + hiddenText.Length + 2 * topText.Length;

        var (fits, downloads) = await Parse(source, files, total);
        Assert.Empty(fits.Diagnostics);
        Assert.Equal([hidden, top], downloads.Requests);

        var (over, _) = await Parse(source, files, total - 1);
        var refused = Assert.Single(over.Diagnostics, d => d.Code == DiagnosticCode.AggregateSourceLengthExceeded);
        Assert.Equal(new SourcePosition(3, 5), refused.Span?.Start);
        Assert.Contains($"splicing the already loaded '{top}' again ({topText.Length} UTF-16 code units", refused.Message);
    }

    // ── Module identity and deferred source protection ───────────────────────

    [Fact]
    public async Task DistinctUrlsWithIdenticalText_AreTwoDownloads_AndNoSplice()
    {
        // Identity is the canonical URL, never the bytes (ModuleIdentityTests): each module is
        // charged once, as downloaded source, and nothing is a splice.
        const string text = "public V = 1";
        var files = new Dictionary<string, string> { [Url("m1")] = text, [Url("m2")] = text };
        var source = $"A = load('{Url("m1")}')\nB = load('{Url("m2")}')\nA.V + B.V";
        var total = source.Length + 2 * text.Length;

        var (fits, downloads) = await Parse(source, files, total);
        Assert.Empty(fits.Diagnostics);
        Assert.Equal([Url("m1"), Url("m2")], downloads.Requests);

        var (over, _) = await Parse(source, files, total - 1);
        var refused = Assert.Single(over.Diagnostics, d => d.Code == DiagnosticCode.AggregateSourceLengthExceeded);
        Assert.DoesNotContain("splicing the already loaded", refused.Message);
        Assert.Contains(Url("m2"), refused.Message);
    }

    [Fact]
    public async Task SelectedBranches_EachChargeTheModuleAgain_SoRepeatedMaterializationStaysBounded()
    {
        // Three load-bearing branches open one leaf module. The first selection downloads it and
        // each later selection re-splices it, charging its text again: the aggregate bounds how
        // many materializations may re-process a completed module.
        const string module = "public V = 1";
        var files = new Dictionary<string, string> { [Url("m")] = module };
        var source = string.Concat(Enumerable.Range(0, 3).Select(i => $"G{i}(0) = 0\nG{i}(n) = {{\n    open '{Url("m")}'\n    V + n\n}}\n"))
            + "G0(1)\nG1(2)\nG2(3)";
        var total = source.Length + 3 * module.Length;

        var (fits, downloads) = await Run(source, files, total);
        var success = Assert.IsType<RunResult.Success>(fits);
        Assert.Equal(new Decimal128[] { 2m, 3m, 4m }, success.Atoms);
        Assert.Equal([Url("m")], downloads.Requests);

        var (over, overDownloads) = await Run(source, files, total - 1);
        var failure = Assert.IsType<RunResult.EvalFailure>(over);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.AggregateSourceLengthExceeded, error.Code);
        Assert.Contains($"splicing the already loaded '{Url("m")}' again", error.Message);
        Assert.Equal([Url("m")], overDownloads.Requests);
    }

    [Fact]
    public async Task UnselectedBranch_DoesNoSourceWork()
    {
        var files = new Dictionary<string, string> { [Url("m")] = "public V = 1" };
        var source = $"G(0) = 0\nG(n) = {{\n    open '{Url("m")}'\n    V + n\n}}\nG(0)";

        var (result, downloads) = await Run(source, files, source.Length);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(new Decimal128[] { 0m }, success.Atoms);
        Assert.Empty(downloads.Requests);
    }
}
