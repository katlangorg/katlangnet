using KatLang.Tests.LanguageSpec;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// THE EMPTY-MODULE SWEEP (owner follow-up of 2026-11-17 to the decision "resolve the provisional body"). A
/// clause branch that loads a module is classified from its PROVISIONAL body, which implicit-argument
/// resolution resolves at parse as if the modules the branch loads on demand were EMPTY
/// (<c>ImplicitArgumentResolver.ResolveProvisionalBranch</c>). When the module really provides nothing the
/// branch names, that assumption is exactly true, so the deferred program must behave exactly like the same
/// text without the load: neither known limitation of <see cref="DeferredBranchForwardingRefusalTests"/> can
/// produce a difference here. Every program of the language-specification and semantic-explorer corpora is
/// swept through that oracle, so every body shape the corpora hold reaches the resolver's provisional path
/// (a gap in its reach or selection invariants throws from the parse).
///
/// <para><b>Construction.</b> A corpus program <c>P</c> becomes the body of a load-bearing clause:</para>
/// <code>
/// ZzHost(host parameters) = {
///   ZzFam(0) = 0
///   ZzFam(ZzN) = {
/// P, unchanged
///     ZzHold = load('https://modules.example/unused.kat')
///   }
///   ZzRead = ZzFam(1)
///   ZzRead
/// }
/// ZzHost(1, 2, 3, …)
/// </code>
/// <para>The DEFERRED twin is that text. The PLAIN twin is the same text without the load: its holder line is
/// <c>ZzHold = 0</c>, so no branch is deferred. The module is <c>public ZzUnused = 0</c> and nothing reads
/// <c>ZzHold</c>: the module supplies no name. <c>P</c> comes first, so its lines, and a leading
/// <c>open</c>, are where they are in both twins; and the two twins are the same tokens up to the holder's
/// right-hand side, so a program that ENDS INCOMPLETE (an unterminated list, a line-final <c>*</c>) meets
/// the same next token in both and has the same syntax error. The OPEN variant writes
/// <c>open 'https://modules.example/unused.kat'</c> as the body's first line instead, which the plain twin
/// leaves empty (programs with no root <c>open</c> of their own). Every introduced name starts with
/// <c>Zz</c>, the clause binder included, and no corpus program mentions such a name, so the frame rebinds
/// nothing of <c>P</c>.</para>
///
/// <para><b>Host parameters.</b> Shape S1: the root parameter names of <c>P</c>'s standalone parse. Shape S2:
/// S1 plus every parameter name of <c>P</c>'s root-level callables (the binders of a clause family
/// included), minus <c>P</c>'s root property names. Under S2 the formulas of the branch forward ENCLOSING
/// bindings, which is the forwarding the provisional resolution exists to charge.</para>
///
/// <para>Both twins are parsed with <see cref="Parser.ParseAsync"/> and run through
/// <see cref="KatLangEngine.RunAsync"/> with the same in-memory downloader,
/// <c>AllowedHosts = ["modules.example"]</c> and the same fixed <see cref="RunOptions.RandomSeed"/>. One fact
/// per corpus, variant and shape collects every failing case and asserts the list empty; minimum counts keep
/// the sweep from going empty. No program is excluded: a program whose standalone parse needs a downloader
/// is skipped by the construction (it cannot be written without a load), and counted.</para>
/// </summary>
public class DeferredProvisionalParitySweepTests(ITestOutputHelper output)
{
    private const string Host = "modules.example";
    private const string UnusedUrl = "https://modules.example/unused.kat";
    private const string UnusedModule = "public ZzUnused = 0\n";
    private const string HolderLine = "    ZzHold = load('" + UnusedUrl + "')\n";
    private const string PlainHolderLine = "    ZzHold = 0\n";
    private const string OpenLine = "    open '" + UnusedUrl + "'\n";
    private const long Seed = 20261117;

    public enum Variant
    {
        /// <summary>A holder nothing reads, written after the program.</summary>
        Holder,

        /// <summary>An <c>open</c> of the module as the body's first line (programs without a root <c>open</c>).</summary>
        Open,
    }

    public enum Shape
    {
        /// <summary>S1: the program's own root parameters.</summary>
        RootParameters,

        /// <summary>S2: S1 plus the parameter names of the program's root-level callables, minus its root property names.</summary>
        RootAndCallableParameters,
    }

    private sealed record CorpusProgram(string Id, string Source);

    private static IReadOnlyList<CorpusProgram> SpecPrograms()
        => [.. LanguageSpecCorpus.AllCases().Select(static c => new CorpusProgram("spec:" + c.Id, c.Source))];

    private static IReadOnlyList<CorpusProgram> ExplorerPrograms()
        => [.. SemanticExplorerCorpus.AllCases().Select(static c => new CorpusProgram("explorer:" + c.Id, c.Source))];

    // ── The frame ───────────────────────────────────────────────────────────

    /// <summary>What a program's standalone parse says about it: whether it can be swept, and its names.</summary>
    private sealed record Standalone(bool NeedsDownloader, bool HasRootOpen, IReadOnlyList<string> RootParameters,
        IReadOnlyList<string> CallableParameters, IReadOnlySet<string> RootProperties);

    private static Standalone Inspect(string program)
    {
        var parsed = Parser.Parse(program);
        var root = parsed.Root;
        var needsDownloader = parsed.Diagnostics.Any(static diagnostic => diagnostic.Code == DiagnosticCode.LoadElaborationUnavailable)
            || LoadElaborationGuard.TryFindFirstUnresolvedLoad(root, out _);
        var rootParameters = ParameterPattern.CapturesExpandingSharedNodesOnce(root.ParameterPatterns)
            .Select(static capture => capture.Name).Distinct(StringComparer.Ordinal).ToArray();
        var callableParameters = new List<string>();
        foreach (var property in root.Properties)
        {
            switch (property.Value)
            {
                case Algorithm.Conditional family:
                    foreach (var branch in family.Branches)
                        callableParameters.AddRange(branch.Pattern.BoundNames());
                    break;
                case Algorithm.User callable:
                    callableParameters.AddRange(
                        ParameterPattern.CapturesExpandingSharedNodesOnce(callable.ParameterPatterns).Select(static capture => capture.Name));
                    break;
            }
        }

        return new Standalone(needsDownloader, root.Opens.Count != 0, rootParameters,
            [.. callableParameters.Distinct(StringComparer.Ordinal)],
            new HashSet<string>(root.Properties.Select(static property => property.Name), StringComparer.Ordinal));
    }

    private static IReadOnlyList<string> HostParameters(Standalone standalone, Shape shape)
    {
        var names = new List<string>(standalone.RootParameters);
        if (shape == Shape.RootAndCallableParameters)
        {
            foreach (var name in standalone.CallableParameters)
            {
                if (!standalone.RootProperties.Contains(name) && !names.Contains(name, StringComparer.Ordinal))
                    names.Add(name);
            }
        }

        return names;
    }

    /// <summary>
    /// The two twins of one program. They differ in ONE line and nowhere else: the load directive, where the
    /// plain twin holds <c>0</c> (holder variant) or nothing (open variant), so every other token of both has
    /// the same position.
    /// </summary>
    private static (string Deferred, string Plain) Twins(string program, Variant variant, IReadOnlyList<string> hostParameters)
    {
        var body = program.EndsWith('\n') ? program : program + "\n";
        var header = hostParameters.Count == 0 ? "ZzHost" : $"ZzHost({string.Join(", ", hostParameters)})";
        var call = hostParameters.Count == 0 ? "ZzHost" : $"ZzHost({string.Join(", ", Enumerable.Range(1, hostParameters.Count))})";
        string Frame(string first, string last)
            => header + " = {\n" +
               "  ZzFam(0) = 0\n" +
               "  ZzFam(ZzN) = {\n" +
               first +
               body +
               last +
               "  }\n" +
               "  ZzRead = ZzFam(1)\n" +
               "  ZzRead\n" +
               "}\n" +
               call + "\n";
        return variant == Variant.Holder
            ? (Frame("", HolderLine), Frame("", PlainHolderLine))
            : (Frame(OpenLine, ""), Frame("\n", ""));
    }

    private static RunOptions Options() => new()
    {
        AllowedHosts = [Host],
        DownloadCode = static (url, _) => url == UnusedUrl
            ? ValueTask.FromResult(UnusedModule)
            : throw new InvalidOperationException($"404: {url}"),
        RandomSeed = Seed,
    };

    // ── One twin, observed ──────────────────────────────────────────────────

    private sealed record Observed(ParseResult? Parsed, RunResult? Result, string? Thrown)
    {
        public IReadOnlyList<Diagnostic> ParseErrors
            => Parsed is null ? [] : [.. Parsed.Diagnostics.Where(static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error)];

        public IReadOnlyList<KatLangErrorCode> ErrorCodes => Result switch
        {
            RunResult.ParseFailure failure => [.. failure.Errors.Select(static error => error.Code)],
            RunResult.EvalFailure failure => [.. failure.Errors.Select(static error => error.Code)],
            _ => [],
        };

        public bool HasDeferredRegion => Parsed is not null && DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(Parsed.Root));

        public string Kind => Thrown is not null ? "threw" : Result switch
        {
            RunResult.Success => "Success",
            RunResult.EvalFailure => "EvalFailure",
            RunResult.ParseFailure => "ParseFailure",
            RunResult.NoProgramOutput => "NoProgramOutput",
            _ => "none",
        };
    }

    private static async Task<Observed> Observe(string source)
    {
        ParseResult? parsed = null;
        try
        {
            parsed = await Parser.ParseAsync(source, Options());
            return new Observed(parsed, await KatLangEngine.RunAsync(source, Options()), null);
        }
        catch (Exception error)
        {
            return new Observed(parsed, null,
                $"{(parsed is null ? "Parser.ParseAsync" : "KatLangEngine.RunAsync")} threw {error.GetType().Name}: {error.Message}");
        }
    }

    private static (PropertyExposure Family, PropertyExposure Reader)? Exposures(ParseResult parsed)
    {
        if (parsed.Root.Properties.FirstOrDefault(static property => property.Name == "ZzHost")?.Value is not { } host)
            return null;
        var family = host.Properties.FirstOrDefault(static property => property.Name == "ZzFam");
        var reader = host.Properties.FirstOrDefault(static property => property.Name == "ZzRead");
        return family is null || reader is null ? null : (family.Exposure, reader.Exposure);
    }

    // ── The sweep ───────────────────────────────────────────────────────────

    /// <summary>What one sweep saw: how many pairs fell in each class, the skips by reason, and every failing case.</summary>
    private sealed class Census
    {
        public int Programs;
        public int Swept;
        public int WithHostParameters;
        public int ComparedValues;
        public int ComparedEvaluationFailures;
        public int ComparedFrontEndErrorsOfTheBranch;
        public int ComparedSyntaxErrors;
        public int CleanParses;
        public int ReaderLocalOnly;
        public int DeferredRegions;

        public SortedDictionary<string, int> Skips { get; } = new(StringComparer.Ordinal);

        public List<string> Failures { get; } = [];

        public void Skip(string reason) => Skips[reason] = Skips.GetValueOrDefault(reason) + 1;
    }

    private static string Codes(IReadOnlyList<KatLangErrorCode> codes) => "[" + string.Join(", ", codes) + "]";

    private static async Task<Census> Sweep(IReadOnlyList<CorpusProgram> programs, Variant variant, Shape shape)
    {
        var census = new Census { Programs = programs.Count };
        foreach (var program in programs)
        {
            void Fail(string what) => census.Failures.Add($"{program.Id}: {what}");

            // Hygiene: the frame's names are its own.
            if (program.Source.Contains("Zz", StringComparison.Ordinal))
            {
                Fail("the corpus program mentions a Zz name");
                continue;
            }

            var standalone = Inspect(program.Source);
            if (standalone.NeedsDownloader)
            {
                census.Skip("the standalone parse needs a downloader");
                continue;
            }

            if (variant == Variant.Open && standalone.HasRootOpen)
            {
                census.Skip("the program has a root open of its own (open variant)");
                continue;
            }

            var hostParameters = HostParameters(standalone, shape);
            var (deferredSource, plainSource) = Twins(program.Source, variant, hostParameters);
            var plain = await Observe(plainSource);
            var deferred = await Observe(deferredSource);
            census.Swept++;
            if (hostParameters.Count != 0)
                census.WithHostParameters++;

            // 1. Neither twin throws, from the parse or from the run.
            if (plain.Thrown is not null || deferred.Thrown is not null)
            {
                if (plain.Thrown is not null) Fail("plain twin: " + plain.Thrown);
                if (deferred.Thrown is not null) Fail("deferred twin: " + deferred.Thrown);
                continue;
            }

            // The twins are what they are meant to be: the plain one defers nothing, and a deferred one that parses
            // cleanly holds its region.
            if (plain.HasDeferredRegion)
                Fail("the plain twin holds a deferred region");
            if (deferred.HasDeferredRegion)
                census.DeferredRegions++;
            else if (deferred.ParseErrors.Count == 0)
                Fail("the deferred twin parses cleanly without a deferred region");

            // 2. Every parse error of the deferred twin is a parse error of the plain twin: a deferred unit is parsed
            // eagerly and judged when selected.
            var plainParseErrors = plain.ParseErrors.Select(static diagnostic => (diagnostic.Code, diagnostic.Span, diagnostic.Message)).ToHashSet();
            foreach (var diagnostic in deferred.ParseErrors)
            {
                if (!plainParseErrors.Contains((diagnostic.Code, diagnostic.Span, diagnostic.Message)))
                    Fail($"the deferred parse reports {diagnostic.Code} at {diagnostic.Span}, which the plain parse does not: {diagnostic.Message}");
            }

            var plainCodes = plain.ErrorCodes;
            var deferredCodes = deferred.ErrorCodes;
            switch (plain.Result)
            {
                // 3. A value is the same value.
                case RunResult.Success plainSuccess:
                    census.ComparedValues++;
                    if (deferred.Result is not RunResult.Success deferredSuccess)
                        Fail($"plain Success ({plainSuccess.ToDisplayString()}), deferred {deferred.Kind} {Codes(deferredCodes)}");
                    else if (!string.Equals(plainSuccess.ToDisplayString(), deferredSuccess.ToDisplayString(), StringComparison.Ordinal))
                        Fail($"plain displays '{plainSuccess.ToDisplayString()}', deferred '{deferredSuccess.ToDisplayString()}'");
                    break;

                // 4. An evaluation failure is the same failure.
                case RunResult.EvalFailure:
                    census.ComparedEvaluationFailures++;
                    if (deferred.Result is not RunResult.EvalFailure || !plainCodes.SequenceEqual(deferredCodes))
                        Fail($"plain EvalFailure {Codes(plainCodes)}, deferred {deferred.Kind} {Codes(deferredCodes)}");
                    break;

                // 5. A front-end error of the branch is the deferred unit's when it is selected. The engine reports a
                // refused materialization as ONE error, its primary diagnostic (the first error of the unit's
                // elaboration: EvalError.ModuleRegionMaterializationFailed.Primary), where the eager parse lists
                // every error: the deferred twin's code is the plain twin's first.
                case RunResult.ParseFailure when deferred.ParseErrors.Count == 0:
                    census.ComparedFrontEndErrorsOfTheBranch++;
                    if (deferred.Result is not RunResult.EvalFailure)
                        Fail($"plain ParseFailure {Codes(plainCodes)}, deferred parses cleanly and is {deferred.Kind}"
                            + (deferred.Result is RunResult.Success value ? $" ({value.ToDisplayString()})" : ""));
                    else if (deferredCodes.Count != 1 || deferredCodes[0] != plainCodes[0])
                        Fail($"plain ParseFailure {Codes(plainCodes)}, deferred EvalFailure {Codes(deferredCodes)}");
                    break;

                // A syntax error is both twins' (assertion 2 compared the errors themselves).
                case RunResult.ParseFailure:
                    census.ComparedSyntaxErrors++;
                    if (deferred.Result is not RunResult.ParseFailure)
                        Fail($"plain ParseFailure, the deferred parse has errors but its run is {deferred.Kind}");
                    break;

                default:
                    if (plain.Kind != deferred.Kind)
                        Fail($"plain {plain.Kind}, deferred {deferred.Kind}");
                    break;
            }

            // 6. The deferred twin is never refused for forwarding, and never reaches UnknownName on its own.
            if (deferredCodes.Contains(KatLangErrorCode.DeferredBranchForwardsEnclosingParameter)
                || deferred.ParseErrors.Any(static diagnostic => diagnostic.Code == DiagnosticCode.DeferredBranchForwardsEnclosingParameter))
                Fail("the deferred twin reports DeferredBranchForwardsEnclosingParameter");
            if (deferredCodes.Contains(KatLangErrorCode.UnknownName) && !plainCodes.Contains(KatLangErrorCode.UnknownName))
                Fail("the deferred twin reports UnknownName and the plain twin does not");

            // 7. The classification of the frame's family and of its reader is the same.
            if (plain.ParseErrors.Count == 0)
            {
                census.CleanParses++;
                var plainExposures = Exposures(plain.Parsed!);
                var deferredExposures = Exposures(deferred.Parsed!);
                if (plainExposures is null || deferredExposures is null)
                    Fail("the frame's family or reader is missing from a clean parse");
                else
                {
                    if (plainExposures != deferredExposures)
                        Fail($"exposure (ZzFam, ZzRead): plain {plainExposures}, deferred {deferredExposures}");
                    if (plainExposures.Value.Reader != PropertyExposure.Exported)
                        census.ReaderLocalOnly++;
                }
            }
        }

        return census;
    }

    /// <summary>
    /// One sweep: no failing case, and the minimum counts that keep it from going empty (programs swept, pairs
    /// compared by value, pairs with at least one host parameter, pairs whose reader is local-only).
    /// </summary>
    private async Task AssertSweep(string corpus, IReadOnlyList<CorpusProgram> programs, Variant variant, Shape shape,
        int minimumSwept, int minimumValues, int minimumWithHostParameters, int minimumReaderLocalOnly)
    {
        var census = await Sweep(programs, variant, shape);
        output.WriteLine($"{corpus} / {variant} / {shape}: programs {census.Programs}, swept {census.Swept}, "
            + $"with host parameters {census.WithHostParameters}, deferred regions {census.DeferredRegions}, "
            + $"clean plain parses {census.CleanParses}, reader local-only {census.ReaderLocalOnly}");
        output.WriteLine($"  compared: values {census.ComparedValues}, evaluation failures {census.ComparedEvaluationFailures}, "
            + $"front-end errors of the branch {census.ComparedFrontEndErrorsOfTheBranch}, syntax errors {census.ComparedSyntaxErrors}");
        foreach (var (reason, count) in census.Skips)
            output.WriteLine($"  skipped {count}: {reason}");
        foreach (var failure in census.Failures)
            output.WriteLine("  FAILURE " + failure);

        Assert.True(census.Failures.Count == 0,
            $"{census.Failures.Count} failing case(s) of {corpus} / {variant} / {shape}:\n" + string.Join("\n", census.Failures.Take(40)));
        Assert.True(census.Swept >= minimumSwept, $"swept {census.Swept} programs, expected at least {minimumSwept}");
        Assert.True(census.ComparedValues >= minimumValues, $"compared {census.ComparedValues} values, expected at least {minimumValues}");
        Assert.True(census.WithHostParameters >= minimumWithHostParameters,
            $"{census.WithHostParameters} pairs have a host parameter, expected at least {minimumWithHostParameters}");
        Assert.True(census.ReaderLocalOnly >= minimumReaderLocalOnly,
            $"{census.ReaderLocalOnly} pairs have a local-only reader, expected at least {minimumReaderLocalOnly}");
    }

    // Measured 2026-11-17 (language-spec corpus, 581 programs): holder S1 581 swept / 233 values / 4 with host
    // parameters / 1 local-only reader; holder S2 581 / 230 / 346 / 33; open S1 567 / 228 / 2 / 1; open S2
    // 567 / 225 / 340 / 33 (14 programs have a root open of their own).

    [Fact]
    public async Task LanguageSpecCorpus_HolderVariant_RootParameters()
        => await AssertSweep("spec", SpecPrograms(), Variant.Holder, Shape.RootParameters, 500, 200, 1, 1);

    [Fact]
    public async Task LanguageSpecCorpus_HolderVariant_RootAndCallableParameters()
        => await AssertSweep("spec", SpecPrograms(), Variant.Holder, Shape.RootAndCallableParameters, 500, 200, 300, 25);

    [Fact]
    public async Task LanguageSpecCorpus_OpenVariant_RootParameters()
        => await AssertSweep("spec", SpecPrograms(), Variant.Open, Shape.RootParameters, 500, 200, 1, 1);

    [Fact]
    public async Task LanguageSpecCorpus_OpenVariant_RootAndCallableParameters()
        => await AssertSweep("spec", SpecPrograms(), Variant.Open, Shape.RootAndCallableParameters, 500, 200, 300, 25);

    // Measured 2026-11-17 (semantic-explorer corpus, 2,564 programs, none with a root open): S1 2,564 swept /
    // 1,934 values / 2 with host parameters / 1 local-only reader; S2 2,564 / 1,920 / 1,117 / 41, in both variants.

    [Fact]
    public async Task SemanticExplorerCorpus_HolderVariant_RootParameters()
        => await AssertSweep("explorer", ExplorerPrograms(), Variant.Holder, Shape.RootParameters, 2400, 1800, 1, 1);

    [Fact]
    public async Task SemanticExplorerCorpus_HolderVariant_RootAndCallableParameters()
        => await AssertSweep("explorer", ExplorerPrograms(), Variant.Holder, Shape.RootAndCallableParameters, 2400, 1800, 1000, 30);

    [Fact]
    public async Task SemanticExplorerCorpus_OpenVariant_RootParameters()
        => await AssertSweep("explorer", ExplorerPrograms(), Variant.Open, Shape.RootParameters, 2400, 1800, 1, 1);

    [Fact]
    public async Task SemanticExplorerCorpus_OpenVariant_RootAndCallableParameters()
        => await AssertSweep("explorer", ExplorerPrograms(), Variant.Open, Shape.RootAndCallableParameters, 2400, 1800, 1000, 30);

    // ── The frame itself ────────────────────────────────────────────────────

    [Fact]
    public void NoCorpusProgram_MentionsAFrameName()
    {
        Assert.NotEmpty(SpecPrograms());
        Assert.NotEmpty(ExplorerPrograms());
        Assert.DoesNotContain(SpecPrograms().Concat(ExplorerPrograms()), static program => program.Source.Contains("Zz", StringComparison.Ordinal));
    }

    [Fact]
    public async Task Twins_DifferOnlyInTheLoadDirective_AndOnlyTheDeferredOneDefers()
    {
        // A program whose callable takes `y`: under S2 it is a host parameter, and the formula forwards it.
        const string program = "W = y + 1\nW * 2";
        var standalone = Inspect(program);
        Assert.False(standalone.NeedsDownloader);
        Assert.Equal(["y"], standalone.RootParameters);
        Assert.Equal(["y"], HostParameters(standalone, Shape.RootParameters));

        var (deferred, plain) = Twins(program, Variant.Holder, ["y"]);
        Assert.Equal(
            "ZzHost(y) = {\n" +
            "  ZzFam(0) = 0\n" +
            "  ZzFam(ZzN) = {\n" +
            "W = y + 1\n" +
            "W * 2\n" +
            "    ZzHold = load('https://modules.example/unused.kat')\n" +
            "  }\n" +
            "  ZzRead = ZzFam(1)\n" +
            "  ZzRead\n" +
            "}\n" +
            "ZzHost(1)\n",
            deferred);
        Assert.Equal(deferred.Replace("load('" + UnusedUrl + "')", "0", StringComparison.Ordinal), plain);

        var (deferredOpen, plainOpen) = Twins(program, Variant.Open, []);
        Assert.StartsWith("ZzHost = {\n  ZzFam(0) = 0\n  ZzFam(ZzN) = {\n    open '" + UnusedUrl + "'\nW = y + 1\n", deferredOpen, StringComparison.Ordinal);
        Assert.Equal(deferredOpen.Replace(OpenLine, "\n", StringComparison.Ordinal), plainOpen);
        Assert.EndsWith("}\nZzHost\n", deferredOpen, StringComparison.Ordinal);

        // The deferred twin holds one region and downloads nothing at parse; the plain twin defers nothing.
        var observedDeferred = await Observe(deferred);
        var observedPlain = await Observe(plain);
        Assert.True(observedDeferred.HasDeferredRegion);
        Assert.False(observedPlain.HasDeferredRegion);
        // W forwards the host's y: the reader is local-only in both, and the value is the same.
        Assert.Equal("4", Assert.IsType<RunResult.Success>(observedPlain.Result).ToDisplayString());
        Assert.Equal("4", Assert.IsType<RunResult.Success>(observedDeferred.Result).ToDisplayString());
        Assert.Equal(Exposures(observedPlain.Parsed!), Exposures(observedDeferred.Parsed!));
        Assert.NotEqual(PropertyExposure.Exported, Exposures(observedDeferred.Parsed!)!.Value.Reader);
    }
}
