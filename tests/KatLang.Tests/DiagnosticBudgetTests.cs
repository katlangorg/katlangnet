using System.Collections.Concurrent;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// The per-list diagnostic budget (<see cref="SourceProcessingLimits.MaxDiagnosticCount"/>,
/// <see cref="DiagnosticBag"/>) and the source-processing amplifications it closes:
/// <list type="bullet">
/// <item>THE PREFIX LAW — a list keeps exactly the first N diagnostics an unbounded operation would
/// report, in order, then one unpositioned <see cref="DiagnosticCode.DiagnosticCountExceeded"/>
/// marker; lexer, parser, module loading, nested modules, and every elaboration pass share one
/// list per operation (a parse, or one demand-time materialization).</item>
/// <item>OBSERVATIONAL IRRELEVANCE — trees, downloads, caching, classification, and evaluation
/// gating are identical at any budget; only what is stored differs.</item>
/// <item>SPLICE CHARGING — every splice of a cached module charges its elaborated weight against the
/// aggregate, so module content multiplied across scopes stays bounded by the aggregate.</item>
/// <item>BOUNDED ECHOES — text a diagnostic repeats per reference is bounded, so neither the stored
/// list nor the work of formatting it grows with the product of two source sizes.</item>
/// </list>
/// Boundaries use small configured limits so every assertion is exact; nothing here measures
/// elapsed time.
/// </summary>
public class DiagnosticBudgetTests
{
    private const string Host = "https://katlang.org/budget/";
    private const int Limit = SourceProcessingLimits.MaxSupportedDiagnosticCount;

    private static SourceProcessingLimits Limits(int? maxDiagnosticCount)
        => new() { MaxDiagnosticCount = maxDiagnosticCount };

    private static ParseResult Parse(string source, int? limit = null)
        => Parser.Parse(source, new RunOptions { SourceProcessingLimits = Limits(limit) });

    private static string Tree(Algorithm root) => FrontEndFingerprint.ComputeParseResult(root, []);

    private sealed class Modules(IReadOnlyDictionary<string, string> files)
    {
        public ConcurrentQueue<string> Requests { get; } = new();

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            Requests.Enqueue(url);
            return files.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : ValueTask.FromException<string>(new InvalidOperationException($"no module '{url}'"));
        }
    }

    private static async Task<(ParseResult Parsed, Modules Downloads)> ParseLoading(
        string source,
        IReadOnlyDictionary<string, string> files,
        SourceProcessingLimits? limits)
    {
        var modules = new Modules(files);
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            DownloadCode = modules.Download,
            SourceProcessingLimits = limits,
        });
        return (parsed, modules);
    }

    private static void AssertMarker(Diagnostic marker, int limit)
    {
        Assert.Equal(DiagnosticCode.DiagnosticCountExceeded, marker.Code);
        Assert.Equal(DiagnosticSeverity.Error, marker.Severity);
        Assert.Null(marker.Span);
        Assert.Contains($"Diagnostic limit of {limit} diagnostic", marker.Message);
    }

    private static string Refused(int count) => string.Join(", ", Enumerable.Repeat("''", count));

    // ── A. The bag's own laws ───────────────────────────────────────────────

    [Fact]
    public void Bag_WithinCapacity_StoresEveryReport_WithoutMarker()
    {
        var bag = new DiagnosticBag(3);
        for (var i = 0; i < 3; i++)
            bag.Report(DiagnosticCode.UnexpectedToken, $"m{i}", null);

        Assert.Equal(["m0", "m1", "m2"], bag.Select(d => d.Message));
        Assert.Equal(3, bag.ReportedCount);
        Assert.False(bag.IsTruncated);
    }

    [Fact]
    public void Bag_PastCapacity_KeepsTheFirstReports_ThenOneUnpositionedMarker()
    {
        var bag = new DiagnosticBag(3);
        for (var i = 0; i < 10; i++)
        {
            bag.Report(
                i < 5 ? DiagnosticCode.UnexpectedToken : DiagnosticCode.UnexpectedCharacter,
                $"m{i}",
                new SourceSpan(i + 1, 1, i + 1, 2));
        }

        Assert.Equal(["m0", "m1", "m2"], bag.Take(3).Select(d => d.Message));
        Assert.Equal(4, bag.Count);
        AssertMarker(bag[3], 3);
        Assert.Equal("Diagnostic limit of 3 diagnostics reached: later diagnostics were omitted.", bag[3].Message);
        Assert.True(bag.IsTruncated);
        // Counters observe every report, dropped ones included.
        Assert.Equal(10, bag.ReportedCount);
        Assert.Equal(10, bag.ReportedErrorCount);
        Assert.True(bag.HasReported(DiagnosticCode.UnexpectedCharacter));
        Assert.False(bag.HasReported(DiagnosticCode.LoadCycle));

        var single = new DiagnosticBag(1);
        single.Report(DiagnosticCode.UnexpectedToken, "a", null);
        single.Report(DiagnosticCode.UnexpectedToken, "b", null);
        Assert.Equal("Diagnostic limit of 1 diagnostic reached: later diagnostics were omitted.", single[^1].Message);
    }

    [Fact]
    public void Bag_FormatsOnlyTheMessagesItStores()
    {
        var bag = new DiagnosticBag(2);
        var formatted = 0;
        for (var i = 0; i < 100; i++)
        {
            bag.Report(DiagnosticCode.UnexpectedCharacter, null, i, n =>
            {
                formatted++;
                return $"m{n}";
            });
        }

        Assert.Equal(2, formatted);
        Assert.Equal(100, bag.ReportedCount);
        Assert.Equal(3, bag.Count);
    }

    [Theory]
    [InlineData(3, 0, 2)]
    [InlineData(3, 0, 5)]
    [InlineData(3, 2, 2)]
    [InlineData(3, 3, 1)]
    [InlineData(3, 5, 5)]
    [InlineData(1, 0, 1)]
    [InlineData(1, 1, 3)]
    [InlineData(5, 2, 3)]
    public void Bag_CommittedStage_IsIndistinguishableFromDirectReports(int capacity, int before, int staged)
    {
        var reports = Enumerable.Range(0, before + staged)
            .Select(i => new Diagnostic($"d{i}", DiagnosticSeverity.Error, new SourceSpan(i + 1, 1, i + 1, 2))
            {
                Code = i % 2 == 0 ? DiagnosticCode.UnexpectedToken : DiagnosticCode.DuplicateProperty,
            })
            .ToArray();

        var direct = new DiagnosticBag(capacity);
        direct.AddRange(reports);

        var parent = new DiagnosticBag(capacity);
        parent.AddRange(reports.Take(before));
        var stage = parent.CreateStage();
        stage.AddRange(reports.Skip(before));
        parent.AddRange(stage);

        Assert.Equal(direct.ToArray(), parent.ToArray());
        Assert.Equal(direct.ReportedCount, parent.ReportedCount);
        Assert.Equal(direct.ReportedErrorCount, parent.ReportedErrorCount);
        Assert.Equal(direct.IsTruncated, parent.IsTruncated);
        Assert.Equal(direct.HasReported(DiagnosticCode.DuplicateProperty), parent.HasReported(DiagnosticCode.DuplicateProperty));
    }

    [Fact]
    public void Bag_Marker_CarriesTheMostSevereDroppedSeverity()
    {
        // Truncation never makes a list block evaluation that would not, and never hides that one would.
        var bag = new DiagnosticBag(1);
        bag.Add(new Diagnostic("w0", DiagnosticSeverity.Warning, null));
        bag.Add(new Diagnostic("w1", DiagnosticSeverity.Warning, null));
        Assert.Equal(DiagnosticSeverity.Warning, bag[^1].Severity);
        Assert.DoesNotContain(bag, d => d.Severity == DiagnosticSeverity.Error);

        bag.Add(new Diagnostic("e", DiagnosticSeverity.Error, null));
        Assert.Equal(2, bag.Count);
        Assert.Equal(DiagnosticSeverity.Error, bag[^1].Severity);
        Assert.Equal(DiagnosticCode.DiagnosticCountExceeded, bag[^1].Code);
        Assert.Equal(1, bag.ReportedErrorCount);
    }

    [Fact]
    public void Bag_BoundsEveryStoredMessage_WithoutSplittingASurrogatePair()
    {
        const int max = DiagnosticBag.MaxRetainedMessageLength;
        var bag = new DiagnosticBag(5);

        var exact = new string('a', max);
        bag.Report(DiagnosticCode.UnexpectedToken, exact, null);
        Assert.Same(exact, bag[0].Message);

        bag.Report(DiagnosticCode.UnexpectedToken, new string('b', max + 10), null);
        Assert.Equal(new string('b', max) + ExprNameRenderer.TruncationMarker, bag[1].Message);

        var straddling = new string('c', max - 1) + char.ConvertFromUtf32(0x1F600) + "tail";
        bag.Add(new Diagnostic(straddling, DiagnosticSeverity.Error, null) { Code = DiagnosticCode.DuplicateProperty });
        Assert.Equal(new string('c', max - 1) + ExprNameRenderer.TruncationMarker, bag[2].Message);
        Assert.Equal(DiagnosticCode.DuplicateProperty, bag[2].Code);
    }

    [Fact]
    public void Bag_RejectsANonPositiveCapacity_AndCommittingItself()
    {
        Assert.Throws<ArgumentOutOfRangeException>(() => new DiagnosticBag(0));
        var bag = new DiagnosticBag(1);
        Assert.Throws<InvalidOperationException>(() => bag.AddRange(bag));
    }

    // ── B. The law through the front end ────────────────────────────────────

    [Fact]
    public void ExactLimit_KeepsEveryDiagnostic_OneMoreEndsTheListWithTheMarker()
    {
        var atLimit = Parse("@@@", limit: 3);
        Assert.Equal(3, atLimit.Diagnostics.Count);
        Assert.All(atLimit.Diagnostics, d => Assert.Equal(DiagnosticCode.UnexpectedCharacter, d.Code));

        var overLimit = Parse("@@@@", limit: 3);
        Assert.Equal(4, overLimit.Diagnostics.Count);
        Assert.Equal(atLimit.Diagnostics, overLimit.Diagnostics.Take(3));
        AssertMarker(overLimit.Diagnostics[3], 3);
        Assert.True(overLimit.HasErrors);
    }

    public static TheoryData<string, string> FloodSources => new()
    {
        { "lexer", new string('@', 40) },
        { "parser", new string(')', 40) },
        { "semantic", "F(x) = " + string.Join(", ", Enumerable.Range(0, 40).Select(i => $"u{i}")) },
        { "open-provider", "open " + string.Join(", ", Enumerable.Repeat("F", 40)) + "\nF(p) = p\n1" },
        { "load-unavailable", "open " + Refused(40) },
        { "mixed", "@ @ @\n) ] }\nF(x) = u0, u1, u2\nA = 1\nA = 2\nG(0) = 1\nG(0) = 2\nG(9)" },
    };

    [Theory]
    [MemberData(nameof(FloodSources))]
    public void TruncatedList_IsExactlyThePrefixOfTheUnboundedList_AndTheTreeIsUnchanged(string name, string source)
    {
        var full = Parse(source);
        Assert.True(full.Diagnostics.Count > 5, $"{name}: the source must report more than the small limits");
        Assert.DoesNotContain(full.Diagnostics, d => d.Code == DiagnosticCode.DiagnosticCountExceeded);

        foreach (var limit in new[] { 1, 2, 5, full.Diagnostics.Count - 1, full.Diagnostics.Count })
        {
            var bounded = Parse(source, limit);
            if (limit >= full.Diagnostics.Count)
            {
                Assert.Equal(full.Diagnostics, bounded.Diagnostics);
            }
            else
            {
                Assert.Equal(limit + 1, bounded.Diagnostics.Count);
                Assert.Equal(full.Diagnostics.Take(limit), bounded.Diagnostics.Take(limit));
                AssertMarker(bounded.Diagnostics[limit], limit);
            }

            Assert.Equal(Tree(full.Root), Tree(bounded.Root));
        }
    }

    [Fact]
    public void EditorSemanticModel_IsTheSameWhateverTheListKept()
    {
        // The editor API reads the recovered tree, never the diagnostic list, so a parse whose
        // list was truncated yields the same occurrences, declarations, and resolutions.
        const string source = "F(x) = x + 1\n@ @ @ @ @ @ @ @\nG = F(2)\nH(y) = G + y + u\nH(3)";
        var full = Parse(source);
        var tiny = Parse(source, 1);
        Assert.True(full.Diagnostics.Count > 2);
        Assert.Equal(2, tiny.Diagnostics.Count);
        AssertMarker(tiny.Diagnostics[1], 1);

        var fullModel = Semantics.SemanticModelBuilder.Build(full);
        var tinyModel = Semantics.SemanticModelBuilder.Build(tiny);

        Assert.NotEmpty(fullModel.IdentifierResolutions);
        Assert.Equal(fullModel.IdentifierOccurrences, tinyModel.IdentifierOccurrences);
        Assert.Equal(fullModel.Declarations, tinyModel.Declarations);
        Assert.Equal(
            fullModel.IdentifierResolutions.Select(r => (r.Occurrence, r.Classification, r.ResolvedDeclaration)),
            tinyModel.IdentifierResolutions.Select(r => (r.Occurrence, r.Classification, r.ResolvedDeclaration)));
        var gReference = new SourcePosition(4, 8); // `G` in `H(y) = G + y + u`
        var resolved = Assert.IsType<Semantics.DeclarationOccurrence>(tinyModel.FindResolutionAt(gReference)?.ResolvedDeclaration);
        Assert.Equal(("G", 3), (resolved.Name, resolved.Span.Start.Line));
        Assert.Equal(fullModel.FindResolutionAt(gReference)?.ResolvedDeclaration, resolved);
    }

    [Fact]
    public void LexerParserAndElaborationDiagnostics_ShareOneList()
    {
        // Four lexical, then four syntax, then four elaboration diagnostics: wherever the limit
        // falls, the list is the one ordered prefix — no stage keeps a list of its own.
        const string source = "@@@@\n))))\nF(x) = u0, u1, u2, u3";
        var codes = Parse(source).Diagnostics.Select(d => d.Code).ToArray();
        Assert.Equal(
            [.. Enumerable.Repeat(DiagnosticCode.UnexpectedCharacter, 4),
             .. Enumerable.Repeat(DiagnosticCode.UnexpectedToken, 4),
             .. Enumerable.Repeat(DiagnosticCode.UndeclaredIdentifier, 4)],
            codes);

        foreach (var limit in new[] { 3, 6, 10 })
        {
            var bounded = Parse(source, limit).Diagnostics;
            Assert.Equal([.. codes.Take(limit), DiagnosticCode.DiagnosticCountExceeded], bounded.Select(d => d.Code));
        }
    }

    [Fact]
    public void ParserDecisions_ReadWhatWasReported_NotWhatWasKept()
    {
        // `F(0@)` has a lexical error in its head, so clause-head recovery keeps it out of the
        // family's duplicate check; `G(1)` is a genuine duplicate. With a one-diagnostic bag the
        // head's lexical error is dropped, yet the decision — and so the reports, the tree, and
        // the kept prefix — must be exactly those of a bag that keeps everything.
        // `H(1 2)` needed syntax recovery inside its head, so it is kept out of `H(1, 2)`'s check.
        const string source = "@ @ @ @ @\nF(0) = 1\nF(0@) = 2\nG(1) = 3\nG(1) = 4\nH(1 2) = 5\nH(1, 2) = 6\nF(1)";
        var roomy = Parser.ParseSyntax(source, new DiagnosticBag(10_000));
        Assert.Single(roomy.Diagnostics, d => d.Code == DiagnosticCode.DuplicateBranchPattern);
        Assert.Single(roomy.Diagnostics, d => d.Code == DiagnosticCode.UnseparatedSameLineItem);

        var tiny = Parser.ParseSyntax(source, new DiagnosticBag(1));
        Assert.Equal(roomy.Diagnostics.ReportedCount, tiny.Diagnostics.ReportedCount);
        Assert.Equal(roomy.Diagnostics.ReportedErrorCount, tiny.Diagnostics.ReportedErrorCount);
        Assert.Equal(Tree(roomy.Root), Tree(tiny.Root));
        Assert.Equal(roomy.Diagnostics[0], tiny.Diagnostics[0]);
        AssertMarker(tiny.Diagnostics[1], 1);
    }

    [Theory]
    [InlineData("1 + 2")]
    [InlineData("Square(x) = x * x\nSquare(7)")]
    [InlineData("F(0) = 1\nF(n) = n * F(n - 1)\nF(5)")]
    [InlineData("A = [1, 2, 3]\nB = A.sum\nB, A.count")]
    [InlineData("open Lib\nLib = { public Twice(x) = x * 2 }\nTwice(21)")]
    public void ValidPrograms_AreUnaffectedByTheBudget(string source)
    {
        var roomy = KatLangEngine.Run(source);
        var tiny = KatLangEngine.Run(source, new RunOptions { SourceProcessingLimits = Limits(1) });

        Assert.IsType<RunResult.Success>(roomy);
        Assert.Equal(roomy.ToDisplayString(), tiny.ToDisplayString());
        var tinyParse = Parse(source, 1);
        Assert.Empty(tinyParse.Diagnostics);
        Assert.Equal(Tree(SourceProvenance.ParseValid(source).Root), Tree(tinyParse.Root));
    }

    [Fact]
    public async Task ValidModuleProgram_IsUnaffectedByTheBudget()
    {
        var files = new Dictionary<string, string>
        {
            [$"{Host}lib"] = $"public Inner = load('{Host}inner')\npublic Twice(x) = x * 2",
            [$"{Host}inner"] = "public V = 21",
        };
        var source = $"open L\nL = load('{Host}lib')\nM = load('{Host}lib')\nTwice(Inner.V)";

        var (roomy, roomyDownloads) = await ParseLoading(source, files, limits: null);
        var (tiny, tinyDownloads) = await ParseLoading(source, files, Limits(1));

        Assert.Empty(roomy.Diagnostics);
        Assert.Empty(tiny.Diagnostics);
        Assert.Equal(Tree(roomy.Root), Tree(tiny.Root));
        Assert.Equal(roomyDownloads.Requests, tinyDownloads.Requests);
        var run = await KatLangEngine.RunAsync(source, new RunOptions
        {
            DownloadCode = new Modules(files).Download,
            SourceProcessingLimits = Limits(1),
        });
        Assert.Equal("42", run.ToDisplayString());
    }

    [Fact]
    public async Task TruncatedList_NeverReachesEvaluation_AndIsRecognizableByCode()
    {
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Probe", (_, _) =>
            {
                calls++;
                return new Result.Atom(1);
            })),
            SourceProcessingLimits = Limits(2),
        };
        const string source = "@@@@@\nProbe";

        var sync = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
        Assert.Equal(3, sync.Errors.Count);
        var marker = sync.Errors[^1];
        Assert.Equal(KatLangErrorCode.DiagnosticCountExceeded, marker.Code);
        Assert.Null(marker.Span);
        Assert.Null(marker.Source);
        Assert.False(marker.IsResourceLimit);
        Assert.Contains("Diagnostic limit of 2 diagnostics reached", sync.ToDisplayString());

        var asynchronous = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));
        Assert.Equal(sync.Errors.Select(e => (e.Code, e.Message, e.Span)), asynchronous.Errors.Select(e => (e.Code, e.Message, e.Span)));
        Assert.Equal(0, calls);
    }

    [Fact]
    public void LexerTokenize_BoundsItsDiagnostics_ButKeepsEveryToken()
    {
        var (tokens, diagnostics) = Lexer.Tokenize(new string('@', 1500));

        Assert.Equal(1501, tokens.Count);
        Assert.All(tokens.Take(1500), token => Assert.Equal(TokenKind.Bad, token.Kind));
        Assert.Equal(Limit + 1, diagnostics.Count);
        Assert.Equal(Enumerable.Range(1, Limit), diagnostics.Take(Limit).Select(d => d.Span!.Value.Start.Column));
        AssertMarker(diagnostics[^1], Limit);
    }

    [Fact]
    public void ThrowingConvenienceEntry_RendersABoundedMessage()
    {
        var exception = Assert.Throws<KatLangException>(() => KatLangEngine.EvaluateToAtoms(new string(';', 5000)));

        Assert.Equal(Limit + 1, exception.Errors.Count);
        Assert.Equal(Limit + 1, exception.Message.Split(Environment.NewLine).Length);
        Assert.Equal(KatLangErrorCode.DiagnosticCountExceeded, exception.Errors[^1].Code);
    }

    // ── C. Modules, nested modules, and deferred regions ─────────────────────

    [Fact]
    public async Task NestedModules_ReportIntoTheParseList_AndNeverGetAFreshBudget()
    {
        // root -> m0 -> m1 -> m2 -> m3: every module also writes ten refused targets, reported at
        // the root's import site into the one list of the parse.
        var files = new Dictionary<string, string>();
        for (var i = 0; i < 4; i++)
        {
            files[$"{Host}m{i}"] = i < 3
                ? $"open '{Host}m{i + 1}', {Refused(10)}\npublic V{i} = {i}"
                : $"open {Refused(10)}\npublic V3 = 3";
        }

        var source = $"M = load('{Host}m0')\n1";
        var (full, fullDownloads) = await ParseLoading(source, files, limits: null);
        var (bounded, boundedDownloads) = await ParseLoading(source, files, Limits(5));

        Assert.Equal(40, full.Diagnostics.Count);
        Assert.All(full.Diagnostics, d => Assert.Equal(DiagnosticCode.InvalidLoadUrl, d.Code));
        Assert.All(full.Diagnostics, d => Assert.Equal(1, d.Span!.Value.Start.Line));
        Assert.Equal(6, bounded.Diagnostics.Count);
        Assert.Equal(full.Diagnostics.Take(5), bounded.Diagnostics.Take(5));
        AssertMarker(bounded.Diagnostics[5], 5);
        Assert.Equal(4, boundedDownloads.Requests.Count);
        Assert.Equal(fullDownloads.Requests, boundedDownloads.Requests);
        Assert.Equal(Tree(full.Root), Tree(bounded.Root));
    }

    [Fact]
    public async Task FailedModuleParse_IsClassifiedByWhatItReported_NotByWhatWasKept()
    {
        // Twenty lexical errors fill a one-diagnostic list before the module's nesting failure is
        // reported; the load site must still name the nesting failure, as it does with room.
        var module = new string('@', 20) + "\npublic X = " + new string('(', 600) + "1" + new string(')', 600);
        var files = new Dictionary<string, string> { [$"{Host}deep"] = module };

        foreach (var limits in new[] { null, Limits(1) })
        {
            var (parsed, downloads) = await ParseLoading($"M = load('{Host}deep')\n1", files, limits);
            var error = Assert.Single(parsed.Diagnostics);
            Assert.Equal(DiagnosticCode.ModuleNestingTooDeep, error.Code);
            Assert.Single(downloads.Requests);
        }
    }

    [Fact]
    public async Task ModuleCaching_DoesNotDependOnTheBudget()
    {
        // A module whose own load fails is never cached, so each site downloads it again — also
        // when the list was already full by the time the module's failure was reported.
        var files = new Dictionary<string, string> { [$"{Host}failing"] = "open ''\npublic V = 1" };
        var source = $"@@@\nA = load('{Host}failing')\nB = load('{Host}failing')\n1";

        var (full, fullDownloads) = await ParseLoading(source, files, limits: null);
        var (bounded, boundedDownloads) = await ParseLoading(source, files, Limits(1));

        Assert.Equal(2, fullDownloads.Requests.Count);
        Assert.Equal(2, boundedDownloads.Requests.Count);
        Assert.Equal(Tree(full.Root), Tree(bounded.Root));
    }

    private static EvalError.ModuleRegionMaterializationFailed MaterializationFailure(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
    }

    private static DeferredModuleRegion Region(Algorithm root, string family, int branch)
    {
        var conditional = Assert.IsType<Algorithm.Conditional>(root.Properties.Single(property => property.Name == family).Value);
        return Assert.IsType<DeferredModuleRegion>(conditional.Branches[branch].Body.DeferredRegion);
    }

    [Fact]
    public async Task DeferredMaterialization_ReportsIntoItsOwnBoundedList_OnEveryAttempt()
    {
        var source = $"F(0) = 0\nF(1) = {{\n    open {Refused(20)}\n    1\n}}\nF(1)";
        var modules = new Modules(new Dictionary<string, string>());
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            DownloadCode = modules.Download,
            SourceProcessingLimits = Limits(4),
        });
        Assert.Empty(parsed.Diagnostics);
        var region = Region(parsed.Root, "F", 1);

        for (var attempt = 1; attempt <= 3; attempt++)
        {
            var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
            Assert.True(result.IsError);
            var failure = MaterializationFailure(result.Error);
            Assert.Equal(5, failure.Diagnostics.Count);
            Assert.All(failure.Diagnostics.Take(4), d => Assert.Equal(DiagnosticCode.InvalidLoadUrl, d.Code));
            AssertMarker(failure.Diagnostics[4], 4);
            Assert.Equal(attempt, region.MaterializationAttempts);
        }

        // Nothing was downloaded, the published parse result never changed, and the loader holds
        // no diagnostics of its attempts: each belongs to its own evaluation's error.
        Assert.Empty(modules.Requests);
        Assert.Empty(parsed.Diagnostics);
        Assert.Empty(Assert.IsAssignableFrom<IReadOnlyList<Diagnostic>>(region.Loader.WalkContext.Sink));
    }

    [Fact]
    public async Task RepeatedFailingMaterialization_KeepsDownloadsCharged_AndEveryListBounded()
    {
        // Each attempt refuses six targets (three kept, then the marker) and then downloads a
        // missing module; the download budget admits two attempts' downloads in all, whatever
        // the lists kept — the dropped fetch failure and module-count refusal are still counted.
        var source = $"F(0) = 0\nF(1) = {{\n    open {Refused(6)}, '{Host}missing'\n    1\n}}\nF(1)";
        var modules = new Modules(new Dictionary<string, string>());
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            DownloadCode = modules.Download,
            SourceProcessingLimits = new SourceProcessingLimits { MaxDiagnosticCount = 3, MaxModuleCount = 2 },
        });
        Assert.Empty(parsed.Diagnostics);
        var region = Region(parsed.Root, "F", 1);

        for (var attempt = 1; attempt <= 4; attempt++)
        {
            var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
            var failure = MaterializationFailure(result.Error);
            Assert.Equal(4, failure.Diagnostics.Count);
            Assert.All(failure.Diagnostics.Take(3), d => Assert.Equal(DiagnosticCode.InvalidLoadUrl, d.Code));
            AssertMarker(failure.Diagnostics[3], 3);
            Assert.False(region.IsMaterialized);
        }

        Assert.Equal([$"{Host}missing", $"{Host}missing"], modules.Requests);
        Assert.Equal(4, region.MaterializationAttempts);
    }

    [Fact]
    public async Task DeferredMaterialization_NestedModulesShareTheAttemptList()
    {
        var files = new Dictionary<string, string>
        {
            [$"{Host}d0"] = $"open '{Host}d1', {Refused(4)}\npublic V0 = 0",
            [$"{Host}d1"] = $"open {Refused(4)}\npublic V1 = 1",
        };
        var source = $"F(0) = 0\nF(1) = {{\n    open '{Host}d0'\n    V0\n}}\nF(1)";
        var modules = new Modules(files);
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            DownloadCode = modules.Download,
            SourceProcessingLimits = Limits(3),
        });
        Assert.Empty(parsed.Diagnostics);

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));

        var failure = MaterializationFailure(result.Error);
        Assert.Equal(4, failure.Diagnostics.Count);
        Assert.All(failure.Diagnostics.Take(3), d => Assert.Equal(DiagnosticCode.InvalidLoadUrl, d.Code));
        AssertMarker(failure.Diagnostics[3], 3);
        Assert.Equal([$"{Host}d0", $"{Host}d1"], modules.Requests);
    }

    // ── D. Splice charging ──────────────────────────────────────────────────

    [Fact]
    public async Task DistinctScopeSplices_EachChargeTheAggregate_AndStopAtItsLimit()
    {
        // One module spliced into ten distinct scopes: the front end elaborates each splice, so
        // each charges the module's weight; the aggregate admits the download and three splices.
        const string module = "public V = 1";
        var url = $"{Host}shared";
        const int sites = 10;
        var source = string.Concat(Enumerable.Range(0, sites).Select(i => $"P{i} = {{ a = load('{url}')\n1 }}\n")) + "1";

        var (parsed, downloads) = await ParseLoading(
            source,
            new Dictionary<string, string> { [url] = module },
            new SourceProcessingLimits { MaxAggregateSourceLength = source.Length + 4 * module.Length });

        Assert.Single(downloads.Requests);
        var rejected = parsed.Diagnostics.Where(d => d.Code == DiagnosticCode.AggregateSourceLengthExceeded).ToArray();
        Assert.Equal(parsed.Diagnostics, rejected);
        // Site i spans lines 2i+1 and 2i+2; sites 4..9 are over the limit.
        Assert.Equal(Enumerable.Range(4, sites - 4).Select(i => 2 * i + 1), rejected.Select(d => d.Span!.Value.Start.Line));
        Assert.All(rejected, d => Assert.Contains($"splicing the already loaded '{url}' again", d.Message));
    }

    [Fact]
    public async Task SpliceWeight_IncludesEverythingTheModulesOwnLoadsCharged()
    {
        var inner = $"{Host}inner";
        var outer = $"{Host}outer";
        const string innerSource = "public V = 2";
        var outerSource = $"public A = load('{inner}')\npublic B = load('{inner}')";
        var files = new Dictionary<string, string> { [inner] = innerSource, [outer] = outerSource };
        var source = $"X = load('{outer}')\nY = load('{outer}')\n1";

        // outer's elaborated weight: its own source, the inner download, and the inner re-splice.
        var outerWeight = outerSource.Length + 2 * innerSource.Length;
        var total = source.Length + 2 * outerWeight;

        var (fits, fitsDownloads) = await ParseLoading(source, files, new SourceProcessingLimits { MaxAggregateSourceLength = total });
        Assert.Empty(fits.Diagnostics);
        Assert.Equal(2, fitsDownloads.Requests.Count);

        var (over, overDownloads) = await ParseLoading(source, files, new SourceProcessingLimits { MaxAggregateSourceLength = total - 1 });
        var error = Assert.Single(over.Diagnostics);
        Assert.Equal(DiagnosticCode.AggregateSourceLengthExceeded, error.Code);
        Assert.Equal(2, error.Span!.Value.Start.Line);
        Assert.Contains($"({outerWeight} UTF-16 code units of elaborated module source)", error.Message);
        Assert.Equal(2, overDownloads.Requests.Count);
    }

    [Fact]
    public async Task CancelledMaterialization_ReleasesItsSpliceCharges()
    {
        // The aggregate admits exactly one successful materialization: the eager download of
        // `shared`, the branch's re-splice of it, and the branch's download of `slow`. A cancelled
        // attempt that kept its splice charge would leave the retry no room.
        var shared = $"{Host}shared";
        var slow = $"{Host}slow";
        const string sharedSource = "public V = 40";
        const string slowSource = "public W = 2";
        var source = $"S = load('{shared}')\nF(0) = 0\nF(1) = {{\n    open '{shared}', '{slow}'\n    V + W\n}}\nF(1)";

        var slowStarted = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var slowRelease = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        async ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            if (url == shared)
                return sharedSource;

            slowStarted.TrySetResult();
            return await slowRelease.Task.WaitAsync(cancellationToken);
        }

        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            DownloadCode = Download,
            SourceProcessingLimits = new SourceProcessingLimits
            {
                MaxAggregateSourceLength = source.Length + 2 * sharedSource.Length + slowSource.Length,
            },
        });
        Assert.Empty(parsed.Diagnostics);
        var root = new Expr.AlgorithmExpr(parsed.Root);

        using (var cancellation = new CancellationTokenSource())
        {
            var run = Evaluator.RunFlatAsync(root, limits: null, cancellation.Token);
            await slowStarted.Task.WaitAsync(TimeSpan.FromSeconds(10));
            cancellation.Cancel();
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(TimeSpan.FromSeconds(10)));
        }

        // Wait for the abandoned walk to unwind (it releases the materialization gate last).
        var region = Region(parsed.Root, "F", 1);
        using (var gateTimeout = new CancellationTokenSource(TimeSpan.FromSeconds(10)))
        {
            await region.Loader.MaterializationGate.WaitAsync(gateTimeout.Token);
            region.Loader.MaterializationGate.Release();
        }

        slowRelease.SetResult(slowSource);
        var retry = await Evaluator.RunFlatAsync(root).WaitAsync(TimeSpan.FromSeconds(10));
        Assert.False(retry.IsError, retry.IsError ? retry.Error.ToString() : "");
        Assert.Equal([42m], retry.Value);
    }

    // ── E. Bounded echoes ───────────────────────────────────────────────────

    [Fact]
    public void OpenTargetRequiringArguments_EchoesABoundedParameterList()
    {
        var small = Assert.Single(Parse("open F\nF(a, b, c) = a\n1").Diagnostics);
        Assert.Equal(
            "'F' cannot be opened because it requires arguments (a, b, c); open imports only an algorithm that needs no call.",
            small.Message);

        var parameters = string.Join(", ", Enumerable.Range(0, 2000).Select(i => $"p{i}"));
        var large = Parse($"open F, F\nF({parameters}) = p0\n1").Diagnostics;
        Assert.Equal(2, large.Count);
        Assert.All(large, d =>
        {
            Assert.Equal(DiagnosticCode.IllegalInOpen, d.Code);
            Assert.StartsWith("'F' cannot be opened because it requires arguments (p0, p1, p2, ", d.Message);
            Assert.Contains(ExprNameRenderer.TruncationMarker + ");", d.Message);
            Assert.True(d.Message.Length < 700, $"{d.Message.Length} code units");
        });
    }

    [Fact]
    public void ConditionalBranchDiagnostic_EchoesABoundedFamilyName()
    {
        var family = "F" + new string('x', 5000);
        var diagnostics = Parse($"{family}(0) = y, z\n1").Diagnostics;

        Assert.Equal(2, diagnostics.Count);
        Assert.All(diagnostics, d =>
        {
            Assert.Equal(DiagnosticCode.UndeclaredIdentifier, d.Code);
            Assert.Contains($"conditional branch '{family[..ExprNameRenderer.MaxRenderedNameLength]}{ExprNameRenderer.TruncationMarker}'", d.Message);
            Assert.True(d.Message.Length < 900, $"{d.Message.Length} code units");
        });
    }

    [Fact]
    public void BlockedForwardingDiagnostic_EchoesABoundedNameList()
    {
        var names = string.Join(", ", Enumerable.Range(0, 1000).Select(i => $"x{i}"));
        var error = Assert.Single(Parse($"G = {names}\nH(q) = abs(G)\n1").Diagnostics);

        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, error.Code);
        Assert.Contains("'G' is required as a value here, but producing that value needs the implicit parameters 'x0', 'x1', ", error.Message);
        Assert.Contains(ExprNameRenderer.TruncationMarker, error.Message);
        Assert.True(error.Message.Length < 3000, $"{error.Message.Length} code units");
    }

    [Fact]
    public void StoredMessage_IsBounded_WhateverTheSourceEchoed()
    {
        var name = "L" + new string('o', 10_000);
        var error = Assert.Single(Parse($"{name} = 1\n{name} = 2\n1").Diagnostics);

        Assert.Equal(DiagnosticCode.DuplicateProperty, error.Code);
        Assert.Equal(DiagnosticBag.MaxRetainedMessageLength + 1, error.Message.Length);
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, error.Message);
    }

    [Fact]
    public void RepeatedDeclarationEchoes_CostBoundedWorkPerReport()
    {
        // Each report formats a bounded echo of the provider's parameter list, reading only the
        // names it shows, so doubling the reports adds a bounded amount per report however long
        // the list is (the unbounded echo materialized and joined all 4000 names per report).
        static long Allocated(int targets)
        {
            var parameters = string.Join(", ", Enumerable.Range(0, 4000).Select(i => $"p{i}"));
            var source = "open " + string.Join(", ", Enumerable.Repeat("F", targets)) + $"\nF({parameters}) = p0\n1";
            _ = Parse(source);
            var before = GC.GetAllocatedBytesForCurrentThread();
            var parsed = Parse(source);
            var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.Equal(targets, parsed.Diagnostics.Count);
            return allocated;
        }

        var perReport = (Allocated(800) - Allocated(400)) / 400;
        Assert.True(perReport < 16 * 1024, $"{perReport} bytes per additional report");
    }

    [Fact]
    public void ReportsPastTheLimit_AllocateNoDiagnostics()
    {
        // Past the limit a report is counted and dropped: no diagnostic and no message is built,
        // so the marginal cost of a bad character is the token the lexer must produce anyway.
        static long Allocated(int characters)
        {
            var source = new string('@', characters);
            _ = Parse(source, 1);
            var before = GC.GetAllocatedBytesForCurrentThread();
            var parsed = Parse(source, 1);
            var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.Equal(2, parsed.Diagnostics.Count);
            return allocated;
        }

        // Measured about 116 bytes (the Bad token and its lexical-error start); a diagnostic built
        // per dropped report adds about 70 more, a formatted message more still.
        var perCharacter = (Allocated(40_000) - Allocated(20_000)) / 20_000;
        Assert.True(perCharacter < 150, $"{perCharacter} bytes per additional bad character");
    }

    [Fact]
    public void ParserReportsPastTheLimit_AllocateNoDiagnostics()
    {
        // The parser's densest flood — one stray closer per code unit — costs its tokens past the
        // limit, never a diagnostic or a message per closer.
        static long Allocated(int closers)
        {
            var source = new string(')', closers);
            _ = Parse(source, 1);
            var before = GC.GetAllocatedBytesForCurrentThread();
            var parsed = Parse(source, 1);
            var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.Equal(2, parsed.Diagnostics.Count);
            return allocated;
        }

        // Measured about 90 bytes (the token); a diagnostic built per dropped report adds about 70.
        var perCloser = (Allocated(40_000) - Allocated(20_000)) / 20_000;
        Assert.True(perCloser < 125, $"{perCloser} bytes per additional stray closer");
    }

    // ── F. Isolation ────────────────────────────────────────────────────────

    [Fact]
    public async Task ConcurrentRuns_SharingOptions_KeepTheirOwnLists()
    {
        // Both runs are suspended in the downloader at the same time, then report their modules'
        // refused targets into their own lists; each list equals the one the run produces alone.
        var arrived = 0;
        var both = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var options = new RunOptions
        {
            DownloadCode = async (url, _) =>
            {
                if (Interlocked.Increment(ref arrived) == 2)
                    both.SetResult();
                await both.Task.WaitAsync(TimeSpan.FromSeconds(10));
                return $"open {Refused(3)}\npublic V = 1";
            },
            SourceProcessingLimits = Limits(6),
        };
        var first = $"@@@@\nM = load('{Host}one')\n1";
        var second = $"$$$$$\nM = load('{Host}two')\n1";

        var results = await Task.WhenAll(
            Task.Run(() => KatLangEngine.RunAsync(first, options)),
            Task.Run(() => KatLangEngine.RunAsync(second, options)));

        static IEnumerable<(KatLangErrorCode, string, SourceSpan?)> Shape(RunResult result)
            => Assert.IsType<RunResult.ParseFailure>(result).Errors.Select(e => (e.Code, e.Message, e.Span));

        var alone = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult($"open {Refused(3)}\npublic V = 1"),
            SourceProcessingLimits = Limits(6),
        };
        Assert.Equal(Shape(await KatLangEngine.RunAsync(first, alone)), Shape(results[0]));
        Assert.Equal(Shape(await KatLangEngine.RunAsync(second, alone)), Shape(results[1]));
        Assert.Equal(7, Shape(results[0]).Count());
        Assert.Equal(7, Shape(results[1]).Count());
    }

    [Fact]
    public async Task ReentrantRunFromTheDownloader_KeepsItsOwnList()
    {
        RunResult? inner = null;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                inner = KatLangEngine.Run(new string(')', 50), new RunOptions { SourceProcessingLimits = Limits(2) });
                return ValueTask.FromResult("public V = 1");
            },
            SourceProcessingLimits = Limits(3),
        };

        var outer = Assert.IsType<RunResult.ParseFailure>(
            await KatLangEngine.RunAsync($"@@\nM = load('{Host}reentrant')\n1", options));

        var innerFailure = Assert.IsType<RunResult.ParseFailure>(inner);
        Assert.Equal(3, innerFailure.Errors.Count);
        Assert.All(innerFailure.Errors.Take(2), e => Assert.Equal(KatLangErrorCode.UnexpectedToken, e.Code));
        Assert.Equal(KatLangErrorCode.DiagnosticCountExceeded, innerFailure.Errors[^1].Code);
        Assert.Equal([KatLangErrorCode.UnexpectedCharacter, KatLangErrorCode.UnexpectedCharacter], outer.Errors.Select(e => e.Code));
    }

    [Fact]
    public async Task Cancellation_IsObserved_AfterTheListWasTruncated()
    {
        using var cancellation = new CancellationTokenSource();
        var options = new RunOptions
        {
            DownloadCode = (_, token) =>
            {
                cancellation.Cancel();
                token.ThrowIfCancellationRequested();
                return ValueTask.FromResult("public V = 1");
            },
            SourceProcessingCancellationToken = cancellation.Token,
            SourceProcessingLimits = Limits(1),
        };

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => Parser.ParseAsync(new string('@', 5000) + $"\nM = load('{Host}cancel')\n1", options));
        Assert.Equal(cancellation.Token, exception.CancellationToken);
    }
}
