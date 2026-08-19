using System.Collections.Concurrent;

namespace KatLang.Tests;

/// <summary>
/// Host-runtime source/module input-size policy (<see cref="SourceProcessingLimits"/>): per-source
/// length, import depth, aggregate source, and distinct-module count. Boundary assertions configure
/// explicit small limits so every assertion is exact and platform-independent; nothing here measures
/// elapsed time. These are parse/front-end diagnostics, never <see cref="EvalError"/>.
/// </summary>
public class SourceProcessingLimitsTests
{
    // ── generative in-memory downloaders (no network) ──────────────────────────

    private const string Host = "https://katlang.org/gen/";

    /// <summary>chain/K loads chain/(K-1); chain/0 is a leaf. Import depth of `main loads chain/N` is N+1.</summary>
    private static (Func<string, string> Download, Func<int> Fetches) ChainDownloader()
    {
        var fetches = 0;
        string Download(string url)
        {
            fetches++;
            var k = int.Parse(url[(Host.Length + "chain/".Length)..]);
            return k <= 0 ? "public V = 0" : $"public Inner = load('{Host}chain/{k - 1}')\npublic V = {k}";
        }
        return (Download, () => fetches);
    }

    /// <summary>leaf/K is an independent tiny module. Optional pad grows each body to ~pad code units.</summary>
    private static (Func<string, string> Download, Func<int> Fetches) LeafDownloader(int pad = 0)
    {
        var fetches = 0;
        string Download(string url)
        {
            fetches++;
            var k = url[(Host.Length + "leaf/".Length)..];
            var body = $"public V{k} = {k}";
            return pad > 0 ? $"# {new string('x', pad)}\n{body}" : body;
        }
        return (Download, () => fetches);
    }

    /// <summary>
    /// Adapts a test's in-memory synchronous fetch to the async downloader contract:
    /// the ValueTasks complete synchronously (throwing fetches throw synchronously),
    /// so downloader-configured runs below complete synchronously and GetResult is
    /// plain result extraction on a completed task.
    /// </summary>
    private static Func<string, CancellationToken, ValueTask<string>>? Adapt(Func<string, string>? downloader)
        => downloader is null ? null : (url, _) => ValueTask.FromResult(downloader(url));

    private static RunResult Run(string source, SourceProcessingLimits limits, Func<string, string>? downloader = null)
    {
        var options = new RunOptions { DownloadCode = Adapt(downloader), SourceProcessingLimits = limits };
        if (downloader is null)
            return KatLangEngine.Run(source, options);

        var task = KatLangEngine.RunAsync(source, options);
        Assert.True(task.IsCompleted);
        return task.GetAwaiter().GetResult();
    }

    private static ParseResult Parse(string source, SourceProcessingLimits limits, Func<string, string>? downloader = null)
    {
        var options = new RunOptions { DownloadCode = Adapt(downloader), SourceProcessingLimits = limits };
        if (downloader is null)
            return Parser.Parse(source, options);

        var task = Parser.ParseAsync(source, options);
        Assert.True(task.IsCompleted);
        return task.GetAwaiter().GetResult();
    }

    private static string FirstError(RunResult result)
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        return failure.Errors[0].Message;
    }

    // ── configuration and validation ──────────────────────────────────────────

    [Theory]
    [InlineData(0)]
    [InlineData(-1)]
    [InlineData(int.MinValue)]
    public void MaxSourceLength_ZeroOrNegative_Throws(int value)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new SourceProcessingLimits { MaxSourceLength = value });

    [Theory]
    [InlineData(0)]
    [InlineData(-1)]
    [InlineData(int.MinValue)]
    public void MaxModuleDepth_ZeroOrNegative_Throws(int value)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new SourceProcessingLimits { MaxModuleDepth = value });

    [Theory]
    [InlineData(0L)]
    [InlineData(-1L)]
    [InlineData(long.MinValue)]
    public void MaxAggregateSourceLength_ZeroOrNegative_Throws(long value)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new SourceProcessingLimits { MaxAggregateSourceLength = value });

    [Theory]
    [InlineData(0)]
    [InlineData(-1)]
    [InlineData(int.MinValue)]
    public void MaxModuleCount_ZeroOrNegative_Throws(int value)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new SourceProcessingLimits { MaxModuleCount = value });

    [Fact]
    public void ValuesAboveCeiling_AreClampedToCeiling()
    {
        var limits = new SourceProcessingLimits
        {
            MaxSourceLength = int.MaxValue,
            MaxModuleDepth = int.MaxValue,
            MaxAggregateSourceLength = long.MaxValue,
            MaxModuleCount = int.MaxValue,
        };
        Assert.Equal(SourceProcessingLimits.MaxSupportedSourceLength, limits.EffectiveMaxSourceLength);
        Assert.Equal(SourceProcessingLimits.MaxSupportedModuleDepth, limits.EffectiveMaxModuleDepth);
        Assert.Equal(SourceProcessingLimits.MaxSupportedAggregateSourceLength, limits.EffectiveMaxAggregateSourceLength);
        Assert.Equal(SourceProcessingLimits.MaxSupportedModuleCount, limits.EffectiveMaxModuleCount);
    }

    [Fact]
    public void Defaults_AreTheSupportedCeilings()
    {
        Assert.Null(SourceProcessingLimits.Default.MaxSourceLength);
        Assert.Equal(SourceProcessingLimits.MaxSupportedSourceLength, SourceProcessingLimits.Default.EffectiveMaxSourceLength);
        Assert.Equal(SourceProcessingLimits.MaxSupportedModuleDepth, SourceProcessingLimits.Default.EffectiveMaxModuleDepth);
        Assert.Equal(SourceProcessingLimits.MaxSupportedAggregateSourceLength, SourceProcessingLimits.Default.EffectiveMaxAggregateSourceLength);
        Assert.Equal(SourceProcessingLimits.MaxSupportedModuleCount, SourceProcessingLimits.Default.EffectiveMaxModuleCount);
    }

    [Fact]
    public void LowerConfiguredValues_AreEnforced()
    {
        var limits = new SourceProcessingLimits
        {
            MaxSourceLength = 10,
            MaxModuleDepth = 3,
            MaxAggregateSourceLength = 20,
            MaxModuleCount = 2,
        };
        Assert.Equal(10, limits.EffectiveMaxSourceLength);
        Assert.Equal(3, limits.EffectiveMaxModuleDepth);
        Assert.Equal(20L, limits.EffectiveMaxAggregateSourceLength);
        Assert.Equal(2, limits.EffectiveMaxModuleCount);
    }

    // ── main source length: below / at / above ─────────────────────────────────

    [Fact]
    public void MainSource_BelowLimit_Succeeds()
        => Assert.IsType<RunResult.Success>(Run("1", new SourceProcessingLimits { MaxSourceLength = 10 }));

    [Fact]
    public void MainSource_ExactlyAtLimit_Succeeds()
    {
        // "7 + 3 * 21" is 10 code units.
        var source = "7 + 3 * 21";
        Assert.Equal(10, source.Length);
        Assert.IsType<RunResult.Success>(Run(source, new SourceProcessingLimits { MaxSourceLength = 10 }));
    }

    [Fact]
    public void MainSource_OneOverLimit_IsRejectedWithStructuredError()
    {
        var source = "7 + 3 * 211";  // 11 code units
        var result = Run(source, new SourceProcessingLimits { MaxSourceLength = 10 });
        var message = FirstError(result);
        Assert.Contains("Source length 11", message);
        Assert.Contains("maximum of 10 UTF-16 code units", message);
    }

    [Fact]
    public void MainSource_OverSupportedCeiling_IsRejectedByDefault()
    {
        // Always-active: a run that configures nothing still rejects an oversized source. Whitespace
        // reaches the length cheaply and is rejected before tokenization.
        var source = new string(' ', SourceProcessingLimits.MaxSupportedSourceLength + 1);
        var result = KatLangEngine.Run(source);
        var message = FirstError(result);
        Assert.Contains($"maximum of {SourceProcessingLimits.MaxSupportedSourceLength}", message);
    }

    [Fact]
    public void RawSyntaxBoundary_EnforcesTheSupportedCeiling()
    {
        // The raw parser boundary (used by raw-parser fuzzing) enforces the hard ceiling itself.
        var syntax = Parser.ParseSyntax(new string(' ', SourceProcessingLimits.MaxSupportedSourceLength + 1));
        Assert.True(syntax.HasErrors);
        Assert.Contains(syntax.Diagnostics, d => d.Message.Contains("UTF-16 code units"));
    }

    // ── import depth (chain) ───────────────────────────────────────────────────

    [Fact]
    public void ImportDepth_AtLimit_Succeeds()
    {
        var (download, _) = ChainDownloader();
        // main loads chain/2 -> depths 1,2,3. Limit 3 admits it.
        var result = Run($"open Lib\npublic Lib = load('{Host}chain/2')\nLib.V",
            new SourceProcessingLimits { MaxModuleDepth = 3 }, download);
        Assert.IsType<RunResult.Success>(result);
    }

    [Fact]
    public void ImportDepth_OneOver_IsRejectedWithStructuredError()
    {
        var (download, _) = ChainDownloader();
        // main loads chain/3 -> deepest module chain/0 at depth 4, over limit 3.
        var result = Run($"public Lib = load('{Host}chain/3')\nLib.V",
            new SourceProcessingLimits { MaxModuleDepth = 3 }, download);
        Assert.Contains("would reach depth 4, over the maximum of 3 nested module levels", FirstError(result));
    }

    [Fact]
    public void DeepChain_UnderDefaultLimit_ReturnsStructuredErrorNotStackOverflow()
    {
        // The import-depth crash boundary was ~562 levels; the default ceiling of 64 turns a deep
        // chain into a structured diagnostic long before the process can overflow.
        var (download, _) = ChainDownloader();
        var result = Run(
            $"public Lib = load('{Host}chain/500')\nLib.V",
            SourceProcessingLimits.Default,
            download);
        Assert.Contains("over the maximum of 64 nested module levels", FirstError(result));
    }

    // ── distinct module count ──────────────────────────────────────────────────

    [Fact]
    public void ModuleCount_AtLimit_Succeeds()
    {
        var (download, fetches) = LeafDownloader();
        var source = $"public A = load('{Host}leaf/0')\npublic B = load('{Host}leaf/1')\nA.V0";
        var result = Run(source, new SourceProcessingLimits { MaxModuleCount = 2 }, download);
        Assert.IsType<RunResult.Success>(result);
        Assert.Equal(2, fetches());
    }

    [Fact]
    public void ModuleCount_OneOver_IsRejectedWithStructuredError()
    {
        var (download, _) = LeafDownloader();
        var source = $"public A = load('{Host}leaf/0')\npublic B = load('{Host}leaf/1')\npublic C = load('{Host}leaf/2')\nA.V0";
        var result = Run(source, new SourceProcessingLimits { MaxModuleCount = 2 }, download);
        Assert.Contains("would request distinct module 3, over the maximum of 2 modules", FirstError(result));
    }

    [Fact]
    public void RepeatedLoadOfSameModule_ConsumesOneSlot()
    {
        // Loading the SAME url many times is one distinct module (cache hit), so a module-count
        // ceiling of 1 still permits any number of repeated references.
        var (download, fetches) = LeafDownloader();
        var source = $"public A = load('{Host}leaf/7')\npublic B = load('{Host}leaf/7')\npublic C = load('{Host}leaf/7')\nA.V7";
        var result = Run(source, new SourceProcessingLimits { MaxModuleCount = 1 }, download);
        Assert.IsType<RunResult.Success>(result);
        Assert.Equal(1, fetches());
    }

    // ── aggregate source ───────────────────────────────────────────────────────

    [Fact]
    public void Aggregate_MainPlusModulesUnderLimit_Succeeds()
    {
        var (download, _) = LeafDownloader();
        var result = Run($"public A = load('{Host}leaf/0')\nA.V0",
            new SourceProcessingLimits { MaxAggregateSourceLength = 10_000 }, download);
        Assert.IsType<RunResult.Success>(result);
    }

    [Fact]
    public void Aggregate_OverLimit_IsRejectedWithStructuredError()
    {
        // Each padded module is ~2000 code units; a small aggregate budget is crossed by the modules.
        var (download, _) = LeafDownloader(pad: 2000);
        var source = $"public A = load('{Host}leaf/0')\npublic B = load('{Host}leaf/1')\nA.V0";
        var result = Run(source, new SourceProcessingLimits { MaxAggregateSourceLength = 2500 }, download);
        Assert.Contains("would bring total source", FirstError(result));
    }

    [Fact]
    public void Aggregate_ChargesMainProgramFirst()
    {
        // Configuring the aggregate below the main program's own length rejects it directly.
        var result = KatLangEngine.Run(
            "12345",
            new RunOptions { SourceProcessingLimits = new SourceProcessingLimits { MaxAggregateSourceLength = 3 } });
        Assert.Contains("exceeds the maximum total source", FirstError(result));
    }

    // ── run-scoped budget: reservation stability ───────────────────────────────

    [Fact]
    public void Budget_FailedAggregateReservation_LeavesTotalUnchanged()
    {
        var budget = new SourceProcessingBudget(new SourceProcessingLimits { MaxAggregateSourceLength = 100 });
        Assert.True(budget.TryReserveAggregate(60));
        Assert.Equal(60, budget.AggregateSource);
        Assert.False(budget.TryReserveAggregate(50));  // would reach 110 > 100
        Assert.Equal(60, budget.AggregateSource);       // unchanged
        Assert.True(budget.TryReserveAggregate(40));    // 60 + 40 = 100, exactly fits
        Assert.Equal(100, budget.AggregateSource);
    }

    [Fact]
    public void Budget_FailedModuleReservation_LeavesCountUnchanged()
    {
        var budget = new SourceProcessingBudget(new SourceProcessingLimits { MaxModuleCount = 1 });
        Assert.True(budget.TryReserveModule());
        Assert.Equal(1, budget.ModuleCount);
        Assert.False(budget.TryReserveModule());
        Assert.Equal(1, budget.ModuleCount);
    }

    [Fact]
    public void Budget_DepthEnterExit_IsBalancedAndTracksPeak()
    {
        var budget = new SourceProcessingBudget(new SourceProcessingLimits { MaxModuleDepth = 2 });
        Assert.True(budget.TryEnterModule());   // depth 1
        Assert.True(budget.TryEnterModule());   // depth 2
        Assert.False(budget.TryEnterModule());  // would be depth 3 > 2
        Assert.Equal(2, budget.PeakDepth);
        budget.ExitModule();
        budget.ExitModule();
        Assert.True(budget.TryEnterModule());   // depth budget restored after exits
    }

    // ── isolation across runs ──────────────────────────────────────────────────

    [Fact]
    public void IndependentRuns_AFailedRunDoesNotContaminateALaterRun()
    {
        var limits = new SourceProcessingLimits { MaxModuleCount = 1 };
        var (download, _) = LeafDownloader();

        // First run exceeds the module-count ceiling.
        var failed = Run($"public A = load('{Host}leaf/0')\npublic B = load('{Host}leaf/1')\nA.V0", limits, download);
        Assert.IsType<RunResult.ParseFailure>(failed);

        // Second run reuses the SAME immutable limits and starts from a fresh budget.
        var ok = Run($"public A = load('{Host}leaf/0')\nA.V0", limits, download);
        Assert.IsType<RunResult.Success>(ok);
    }

    [Fact]
    public void Concurrency_SharedImmutableLimits_MatchSequentialControls()
    {
        var limits = new SourceProcessingLimits { MaxModuleCount = 2 };

        string ProgramFor(int i) => i % 2 == 0
            ? $"public A = load('{Host}leaf/{i}')\nA.V{i}"                                  // 1 module -> ok
            : $"public A = load('{Host}leaf/{i}')\npublic B = load('{Host}leaf/{i}0')\npublic C = load('{Host}leaf/{i}1')\nA.V{i}"; // 3 modules -> fail

        bool RunOne(int i)
        {
            var (download, _) = LeafDownloader();  // independent downloader per run
            return Run(ProgramFor(i), limits, download) is RunResult.Success;
        }

        var sequential = Enumerable.Range(0, 40).Select(RunOne).ToArray();

        var parallel = new ConcurrentDictionary<int, bool>();
        Parallel.For(0, 40, i => parallel[i] = RunOne(i));

        for (var i = 0; i < 40; i++)
            Assert.Equal(sequential[i], parallel[i]);
        // Even indices (1 module) succeed; odd indices (3 modules) fail under the count-of-2 ceiling.
        Assert.True(sequential[0]);
        Assert.False(sequential[1]);
    }

    // ── compatibility: in-budget programs are unchanged ────────────────────────

    [Fact]
    public void InBudgetProgram_WithAndWithoutExplicitDefaultLimits_ProduceSameResult()
    {
        const string source = "A = 1 + 1\nF(x) = x * 2\nF(A)";
        var withoutLimits = KatLangEngine.Run(source);
        var withDefault = KatLangEngine.Run(source, new RunOptions { SourceProcessingLimits = SourceProcessingLimits.Default });
        Assert.Equal(withoutLimits.ToDisplayString(), withDefault.ToDisplayString());
        Assert.Equal("4", withDefault.ToDisplayString());
    }

    [Fact]
    public void InBudgetModuleProgram_LoadsAndEvaluatesNormally()
    {
        var (download, fetches) = LeafDownloader();
        var result = Run($"open Lib\npublic Lib = load('{Host}leaf/5')\nV5",
            SourceProcessingLimits.Default, download);
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal("5", success.ToDisplayString());
        Assert.Equal(1, fetches());
    }

    [Fact]
    public void RecordCopy_RevalidatesAndDoesNotMutateOriginal()
    {
        var original = new SourceProcessingLimits { MaxSourceLength = 10 };
        var copy = original with { MaxSourceLength = 20 };

        Assert.Equal(10, original.EffectiveMaxSourceLength);
        Assert.Equal(20, copy.EffectiveMaxSourceLength);
        Assert.Throws<ArgumentOutOfRangeException>(() => original with { MaxSourceLength = 0 });
    }

    [Fact]
    public void RawSyntaxBoundary_ExactlyAtSupportedCeiling_IsAccepted()
    {
        var syntax = Parser.ParseSyntax(new string(' ', SourceProcessingLimits.MaxSupportedSourceLength));
        Assert.False(syntax.HasErrors, string.Join(Environment.NewLine, syntax.Diagnostics.Select(d => d.Message)));
    }

    [Fact]
    public void AboveSupportedRequest_CannotRaiseTheHardSourceCeiling()
    {
        var source = new string(' ', SourceProcessingLimits.MaxSupportedSourceLength + 1);
        var result = Run(source, new SourceProcessingLimits { MaxSourceLength = int.MaxValue });
        var message = FirstError(result);

        Assert.Contains($"Source length {source.Length}", message);
        Assert.Contains($"maximum of {SourceProcessingLimits.MaxSupportedSourceLength}", message);
    }

    [Fact]
    public void PublicExecutionSurfaces_PropagateConfiguredSourceLimit()
    {
        const string source = "77";
        var options = new RunOptions
        {
            SourceProcessingLimits = new SourceProcessingLimits { MaxSourceLength = source.Length - 1 },
        };

        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
        Assert.Throws<KatLangException>(() => KatLangEngine.EvaluateToAtoms(source, options));
        Assert.Contains("UTF-16 code units", KatLangEngine.EvaluateToString(source, options));
    }

    [Fact]
    public void SourceLength_UsesUtf16CodeUnits()
    {
        const string source = "# \U0001F600\n1";
        Assert.Equal(6, source.Length);
        Assert.IsType<RunResult.Success>(Run(
            source,
            new SourceProcessingLimits { MaxSourceLength = source.Length }));

        var rejected = Run(
            source,
            new SourceProcessingLimits { MaxSourceLength = source.Length - 1 });
        Assert.Contains("Source length 6", FirstError(rejected));
    }

    [Fact]
    public void ModuleSource_ExactAndOneOverConfiguredBoundary()
    {
        var url = $"{Host}module-source";
        var main = $"public Lib = load('{url}')\n1";
        var exact = PadToLength("# \U0001F600\npublic V = 1", 100);
        Assert.Equal(100, exact.Length);
        var limits = new SourceProcessingLimits
        {
            MaxSourceLength = 100,
            MaxAggregateSourceLength = 10_000,
        };

        Assert.IsType<RunResult.Success>(Run(main, limits, _ => exact));

        var failure = Assert.IsType<RunResult.ParseFailure>(Run(main, limits, _ => exact + " "));
        var error = Assert.Single(failure.Errors);
        Assert.Contains(url, error.Message);
        Assert.Contains("101 UTF-16 code units", error.Message);
        Assert.Contains("maximum of 100", error.Message);
    }

    [Fact]
    public void AggregateSource_ExactAndOneOverBoundary_IncludesMainSource()
    {
        var url = $"{Host}aggregate-exact";
        var main = $"public Lib = load('{url}')\n1";
        var module = PadToLength("public V = 1", 100);
        var exactTotal = main.Length + module.Length;

        var exact = Parse(
            main,
            new SourceProcessingLimits { MaxAggregateSourceLength = exactTotal },
            _ => module);
        Assert.False(exact.HasErrors, string.Join(Environment.NewLine, exact.Diagnostics.Select(d => d.Message)));

        var over = Parse(
            main,
            new SourceProcessingLimits { MaxAggregateSourceLength = exactTotal - 1 },
            _ => module);
        var error = Assert.Single(over.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Contains($"total source to {exactTotal} UTF-16 code units", error.Message);
        Assert.Contains($"maximum of {exactTotal - 1}", error.Message);
    }

    [Fact]
    public void CachedRepeatedModule_IsChargedOnceAtAggregateBoundary()
    {
        var url = $"{Host}cached-aggregate";
        var source = $"public A = load('{url}')\npublic B = load('{url}')\n1";
        const string module = "public V = 1";
        var fetches = 0;

        var parsed = Parse(
            source,
            new SourceProcessingLimits { MaxAggregateSourceLength = source.Length + module.Length },
            _ => { fetches++; return module; });

        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));
        Assert.Equal(1, fetches);
    }

    [Fact]
    public void SupportedDepthBoundary_Admits64ImportedModulesAndRejects65()
    {
        var (atDownload, atFetches) = ChainDownloader();
        var at = Parse(
            $"public Lib = load('{Host}chain/63')\n1",
            SourceProcessingLimits.Default,
            atDownload);
        Assert.False(at.HasErrors, string.Join(Environment.NewLine, at.Diagnostics.Select(d => d.Message)));
        Assert.Equal(64, atFetches());

        var (overDownload, overFetches) = ChainDownloader();
        var over = Parse(
            $"public Lib = load('{Host}chain/64')\n1",
            SourceProcessingLimits.Default,
            overDownload);
        var error = Assert.Single(over.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Contains("would reach depth 65", error.Message);
        Assert.Contains("maximum of 64", error.Message);
        Assert.Equal(64, overFetches());
    }

    [Fact]
    public void SupportedModuleCountBoundary_Admits256AndRejects257BeforeFetch()
    {
        static string Program(int count) =>
            string.Concat(Enumerable.Range(0, count).Select(i =>
                $"public L{i} = load('{Host}count/{i}')\n")) + "1";

        var atFetches = 0;
        var at = Parse(Program(256), SourceProcessingLimits.Default, _ =>
        {
            atFetches++;
            return "public V = 1";
        });
        Assert.False(at.HasErrors, string.Join(Environment.NewLine, at.Diagnostics.Select(d => d.Message)));
        Assert.Equal(256, atFetches);

        var overFetches = 0;
        var over = Parse(Program(257), SourceProcessingLimits.Default, _ =>
        {
            overFetches++;
            return "public V = 1";
        });
        var error = Assert.Single(over.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Contains("distinct module 257", error.Message);
        Assert.Contains("maximum of 256 modules", error.Message);
        Assert.Equal(256, overFetches);
    }

    [Fact]
    public void DiamondDependency_FetchesAndChargesSharedModuleOnce()
    {
        var a = $"{Host}diamond/a";
        var b = $"{Host}diamond/b";
        var c = $"{Host}diamond/c";
        var d = $"{Host}diamond/d";
        var files = new Dictionary<string, string>
        {
            [a] = $"public B = load('{b}')\npublic C = load('{c}')",
            [b] = $"public D = load('{d}')",
            [c] = $"public D = load('{d}')",
            [d] = "public V = 1",
        };
        var calls = new Dictionary<string, int>(StringComparer.Ordinal);

        var parsed = Parse(
            $"public A = load('{a}')\n1",
            new SourceProcessingLimits { MaxModuleCount = 4 },
            url =>
            {
                calls[url] = calls.GetValueOrDefault(url) + 1;
                return files[url];
            });

        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(diagnostic => diagnostic.Message)));
        Assert.Equal(4, calls.Count);
        Assert.All(calls.Values, count => Assert.Equal(1, count));
    }

    [Fact]
    public void EquivalentNormalizedUrls_ShareOneCacheEntry()
    {
        var fetches = 0;
        var source =
            "public A = load('HTTPS://KATLANG.ORG:443/gen/dir/../same')\n" +
            "public B = load('https://katlang.org/gen/same')\n1";

        var parsed = Parse(source, new SourceProcessingLimits { MaxModuleCount = 1 }, _ =>
        {
            fetches++;
            return "public V = 1";
        });

        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));
        Assert.Equal(1, fetches);
    }

    [Fact]
    public void CycleAtWouldBeOverDepth_IsReportedAsCycle()
    {
        var a = $"{Host}cycle/a";
        var b = $"{Host}cycle/b";
        var files = new Dictionary<string, string>
        {
            [a] = $"public B = load('{b}')",
            [b] = $"public A = load('{a}')",
        };

        var parsed = Parse(
            $"public A = load('{a}')\n1",
            new SourceProcessingLimits { MaxModuleDepth = 2 },
            url => files[url]);

        var error = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Contains("load cycle detected", error.Message);
        Assert.DoesNotContain("maximum", error.Message);
    }

    [Fact]
    public void ModulePolicyFailure_DoesNotAppendEvaluatorContext()
    {
        var url = $"{Host}too-large";
        var source = $"A = load('{url}')\nA.X";
        var limits = new SourceProcessingLimits { MaxSourceLength = 100 };

        var failure = Assert.IsType<RunResult.ParseFailure>(Run(source, limits, _ => new string('x', 101)));
        var error = Assert.Single(failure.Errors);
        Assert.Contains(url, error.Message);
        Assert.Contains("101 UTF-16 code units", error.Message);
        Assert.DoesNotContain("Property 'X'", error.Message);
    }

    [Fact]
    public void Budget_ModuleSourceReservation_IsAtomicInBothFailureDirections()
    {
        var aggregateFirst = new SourceProcessingBudget(new SourceProcessingLimits
        {
            MaxAggregateSourceLength = 10,
            MaxModuleCount = 1,
        });
        Assert.False(aggregateFirst.TryReserveModuleSource(11));
        Assert.Equal(0, aggregateFirst.AggregateSource);
        Assert.Equal(0, aggregateFirst.ModuleCount);

        var countFirst = new SourceProcessingBudget(new SourceProcessingLimits
        {
            MaxAggregateSourceLength = 10,
            MaxModuleCount = 1,
        });
        Assert.True(countFirst.TryReserveModule());
        Assert.False(countFirst.TryReserveModuleSource(5));
        Assert.Equal(0, countFirst.AggregateSource);
        Assert.Equal(1, countFirst.ModuleCount);
    }

    [Fact]
    public void Budget_DepthCannotUnderflow()
    {
        var budget = new SourceProcessingBudget(new SourceProcessingLimits { MaxModuleDepth = 1 });
        Assert.Throws<InvalidOperationException>(budget.ExitModule);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.True(budget.TryEnterModule());
        Assert.Equal(1, budget.CurrentDepth);
        budget.ExitModule();
        Assert.Equal(0, budget.CurrentDepth);
    }

    [Fact]
    public void AggregateRejection_DoesNotConsumeTheModuleSlotNeededByALaterModule()
    {
        var largeUrl = $"{Host}rollback/large";
        var smallUrl = $"{Host}rollback/small";
        var source = $"public Large = load('{largeUrl}')\npublic Small = load('{smallUrl}')\n1";
        var small = "public V = 1";
        var large = PadToLength("public V = 1", 100);
        var fetches = 0;

        var parsed = Parse(
            source,
            new SourceProcessingLimits
            {
                MaxSourceLength = 200,
                MaxAggregateSourceLength = source.Length + small.Length,
                MaxModuleCount = 1,
            },
            url =>
            {
                fetches++;
                return url == largeUrl ? large : small;
            });

        Assert.Equal(2, fetches);
        Assert.Single(parsed.Diagnostics, d => d.Message.Contains("would bring total source", StringComparison.Ordinal));
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Message.Contains("distinct module", StringComparison.Ordinal));
    }

    [Fact]
    public void FailedDownloads_AreRefetchedAndDoNotConsumeAModuleSlot()
    {
        var missing = $"{Host}missing/same";
        var ok = $"{Host}missing/ok";
        var source =
            $"public A = load('{missing}')\n" +
            $"public B = load('{missing}')\n" +
            $"public C = load('{ok}')\n1";
        var missingFetches = 0;
        var okFetches = 0;

        var parsed = Parse(
            source,
            new SourceProcessingLimits { MaxModuleCount = 1 },
            url =>
            {
                if (url == missing)
                {
                    missingFetches++;
                    throw new InvalidOperationException("expected test failure");
                }

                okFetches++;
                return "public V = 1";
            });

        Assert.Equal(2, missingFetches);
        Assert.Equal(1, okFetches);
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Message.Contains("distinct module", StringComparison.Ordinal));
    }

    [Fact]
    public void ExceptionalDownload_RestoresDepthForTheNextSibling()
    {
        var failed = $"{Host}depth/failed";
        var ok = $"{Host}depth/ok";
        var source = $"public A = load('{failed}')\npublic B = load('{ok}')\n1";

        var parsed = Parse(
            source,
            new SourceProcessingLimits { MaxModuleDepth = 1 },
            url => url == failed
                ? throw new InvalidOperationException("expected test failure")
                : "public V = 1");

        Assert.DoesNotContain(parsed.Diagnostics, d => d.Message.Contains("nested module levels", StringComparison.Ordinal));
    }

    [Fact]
    public void NullDownloaderResult_IsAStructuredLoadDiagnostic()
    {
        var parsed = Parse(
            $"public A = load('{Host}null')\n1",
            SourceProcessingLimits.Default,
            _ => null!);

        var error = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Contains("returned no source text", error.Message);
    }

    [Fact]
    public void EmptyModule_IsCachedAndCountsAsOneDistinctModule()
    {
        var url = $"{Host}empty";
        var source = $"public A = load('{url}')\npublic B = load('{url}')\n1";
        var fetches = 0;

        var parsed = Parse(source, new SourceProcessingLimits { MaxModuleCount = 1 }, _ =>
        {
            fetches++;
            return string.Empty;
        });

        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));
        Assert.Equal(1, fetches);
    }

    [Fact]
    public async Task ConcurrentRuns_WithSharedLimitsActuallyOverlapAndRemainIsolated()
    {
        const int runCount = 8;
        var limits = new SourceProcessingLimits { MaxModuleCount = 1 };
        using var enteredDownloaders = new CountdownEvent(runCount);
        using var releaseDownloaders = new ManualResetEventSlim(false);

        var tasks = Enumerable.Range(0, runCount)
            .Select(i => Task.Factory.StartNew(
                () => Run(
                    $"public A = load('{Host}overlap/{i}')\n1",
                    limits,
                    _ =>
                    {
                        enteredDownloaders.Signal();
                        Assert.True(releaseDownloaders.Wait(TimeSpan.FromSeconds(10)));
                        return "public V = 1";
                    }),
                CancellationToken.None,
                TaskCreationOptions.LongRunning,
                TaskScheduler.Default))
            .ToArray();

        try
        {
            Assert.True(enteredDownloaders.Wait(TimeSpan.FromSeconds(10)), "Runs did not overlap inside their downloaders.");
        }
        finally
        {
            releaseDownloaders.Set();
        }

        var results = await Task.WhenAll(tasks);
        Assert.All(results, result => Assert.IsType<RunResult.Success>(result));
    }

    [Fact]
    public void OversizedModule_DoesNotConsumeAggregateOrModuleCount()
    {
        var oversizedUrl = $"{Host}rollback/oversized";
        var smallUrl = $"{Host}rollback/after-oversized";
        var source = $"public Oversized = load('{oversizedUrl}')\npublic Small = load('{smallUrl}')\n1";
        var sourceLimit = Math.Max(source.Length, 120);
        var small = "public V = 1";
        var fetches = 0;

        var parsed = Parse(
            source,
            new SourceProcessingLimits
            {
                MaxSourceLength = sourceLimit,
                MaxAggregateSourceLength = source.Length + small.Length,
                MaxModuleCount = 1,
            },
            url =>
            {
                fetches++;
                return url == oversizedUrl ? new string('x', sourceLimit + 1) : small;
            });

        Assert.Equal(2, fetches);
        Assert.Single(parsed.Diagnostics, d => d.Message.Contains("source from", StringComparison.Ordinal));
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Message.Contains("total source", StringComparison.Ordinal));
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Message.Contains("distinct module", StringComparison.Ordinal));
    }

    [Fact]
    public void RepeatedAggregateRejection_IsRefetchedWithoutMutatingCounters()
    {
        var rejectedUrl = $"{Host}rollback/repeated-aggregate";
        var smallUrl = $"{Host}rollback/after-repeated-aggregate";
        var source =
            $"public A = load('{rejectedUrl}')\n" +
            $"public B = load('{rejectedUrl}')\n" +
            $"public Small = load('{smallUrl}')\n1";
        var small = "public V = 1";
        var rejected = PadToLength("public V = 1", 100);
        var rejectedFetches = 0;
        var smallFetches = 0;

        var parsed = Parse(
            source,
            new SourceProcessingLimits
            {
                MaxSourceLength = 1_000,
                MaxAggregateSourceLength = source.Length + small.Length,
                MaxModuleCount = 1,
            },
            url =>
            {
                if (url == rejectedUrl)
                {
                    rejectedFetches++;
                    return rejected;
                }

                smallFetches++;
                return small;
            });

        Assert.Equal(2, rejectedFetches);
        Assert.Equal(1, smallFetches);
        Assert.Equal(2, parsed.Diagnostics.Count(d => d.Message.Contains("would bring total source", StringComparison.Ordinal)));
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Message.Contains("distinct module", StringComparison.Ordinal));
    }
    [Fact]
    public void ResourceDiagnostics_PluralizeSingularUnits()
    {
        Assert.Contains("maximum of 1 UTF-16 code unit.",
            SourceProcessingDiagnostics.SourceLengthExceeded(2, 1).Message);
        Assert.Contains("maximum of 1 UTF-16 code unit.",
            SourceProcessingDiagnostics.ModuleSourceLengthExceeded("https://katlang.org/m", 2, 1, null).Message);
        Assert.Contains("maximum of 1 nested module level.",
            SourceProcessingDiagnostics.ModuleImportDepthExceeded("https://katlang.org/m", 2, 1, null).Message);

        var aggregate = SourceProcessingDiagnostics.AggregateSourceLengthExceeded(
            "https://katlang.org/m", 1, 2, 1, null).Message;
        Assert.Contains("(1 UTF-16 code unit)", aggregate);
        Assert.Contains("maximum of 1 UTF-16 code unit.", aggregate);
        Assert.Contains("maximum total source of 1 UTF-16 code unit.",
            SourceProcessingDiagnostics.AggregateSourceLengthExceededByProgram(2, 1).Message);
        Assert.Contains("maximum of 1 module.",
            SourceProcessingDiagnostics.ModuleCountExceeded("https://katlang.org/m", 2, 1, null).Message);
    }

    private static string PadToLength(string source, int length)
        => source + new string(' ', length - source.Length);
}
