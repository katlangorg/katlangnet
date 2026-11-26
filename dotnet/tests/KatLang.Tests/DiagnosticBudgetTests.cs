using System.Collections.Concurrent;
using System.Diagnostics.Tracing;
using KatLang.ParserFuzz;
using KatLang.TestInfrastructure;

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
/// <item>NO PAYLOAD PAST THE LIMIT — a producer whose message grows with the source (bare forwarding's
/// per-parameter reports, a marker refused on an alias or a module holder) makes and counts every
/// report but builds a message, and reads what only a message needs, for a stored report alone.</item>
/// <item>NO TEXT PAST THE RETAINED PREFIX — a stored report whose text grows with the source (a marked-wrapper
/// suggestion, a structural parameter's written form) is built only to the prefix its bound reads, and stores exactly
/// the whole message's text.</item>
/// </list>
/// Boundaries use small configured limits so every assertion is exact; nothing here measures
/// elapsed time.
/// </summary>
public class DiagnosticBudgetTests(Xunit.Abstractions.ITestOutputHelper output)
{
    // Every bounded wait in this file is a hang guard, never a latency claim: what it waits for
    // runs as thread-pool work, which a loaded CI runner can delay well past a tight bound (a
    // 10 s guard timed out in CI in October 2026).
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

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

    [Fact]
    public void Bag_Stage_HasTheParentCapacity_AndNeverReachesTheParent()
    {
        // A stage holds a WITHHELD list (a provisional elaboration's passes): bounded exactly like
        // the operation's own list, and never committed into it.
        var parent = new DiagnosticBag(2);
        parent.Report(DiagnosticCode.UnexpectedToken, "p0", null);
        var stage = parent.CreateStage();
        for (var i = 0; i < 5; i++)
            stage.Report(DiagnosticCode.UndeclaredIdentifier, $"s{i}", null);

        Assert.Equal(parent.Capacity, stage.Capacity);
        Assert.Equal(["s0", "s1"], stage.Take(2).Select(d => d.Message));
        AssertMarker(stage[^1], 2);
        Assert.Equal(5, stage.ReportedCount);

        Assert.Equal(["p0"], parent.Select(d => d.Message));
        Assert.Equal(1, parent.ReportedCount);
        Assert.False(parent.IsTruncated);
        Assert.False(parent.HasReported(DiagnosticCode.UndeclaredIdentifier));
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
    public void Bag_AnchoredReports_TakeThePlaceTheirAnchorReserved()
    {
        // A report decided later (M4★: a check implicit-argument resolution decides) stands where its anchor was
        // reserved: after every report made before, before every report made after; anchors reserved at one point keep
        // their reservation order, and the reports of one anchor their own.
        var bag = new DiagnosticBag(10);
        bag.Report(DiagnosticCode.UnexpectedToken, "a", null);
        var first = bag.ReserveAnchor();
        var second = bag.ReserveAnchor();
        bag.Report(DiagnosticCode.UnexpectedToken, "b", null);
        var third = bag.ReserveAnchor();
        bag.Report(DiagnosticCode.UnexpectedToken, "c", null);
        Assert.Equal(3, bag.ReportedCount);

        using (bag.InsertingAt(third))
            bag.Report(DiagnosticCode.UndeclaredIdentifier, "t", null);
        using (bag.InsertingAt(second))
        {
            bag.Report(DiagnosticCode.UndeclaredIdentifier, "s1", null);
            bag.Report(DiagnosticCode.UndeclaredIdentifier, "s2", null);
        }

        using (bag.InsertingAt(first))
            bag.Report(DiagnosticCode.AmbiguousOpen, "f", null);
        bag.Report(DiagnosticCode.UnexpectedToken, "d", null);

        Assert.Equal(["a", "f", "s1", "s2", "b", "t", "c", "d"], bag.Select(d => d.Message));
        Assert.Equal(8, bag.ReportedCount);
        Assert.True(bag.HasReported(DiagnosticCode.AmbiguousOpen));
        Assert.False(bag.IsTruncated);
        // An unused anchor reserves nothing.
        _ = bag.ReserveAnchor();
        Assert.Equal(8, bag.Count);
    }

    [Fact]
    public void Bag_AnchoredReports_KeepThePrefixLaw()
    {
        // The stored list is the first N of the list the anchored reports would have made at their anchors: an anchored
        // report moves the last stored one past the capacity (the marker takes its severity), and one whose place is past
        // the capacity is dropped and never formatted.
        var bag = new DiagnosticBag(3);
        var early = bag.ReserveAnchor();
        bag.Add(new Diagnostic("w0", DiagnosticSeverity.Warning, null));
        bag.Add(new Diagnostic("w1", DiagnosticSeverity.Warning, null));
        bag.Add(new Diagnostic("w2", DiagnosticSeverity.Warning, null));
        var late = bag.ReserveAnchor();
        Assert.False(bag.IsTruncated);

        using (bag.InsertingAt(early))
            bag.Report(DiagnosticCode.UndeclaredIdentifier, "e", null);
        Assert.Equal(["e", "w0", "w1"], bag.Take(3).Select(d => d.Message));
        Assert.Equal(4, bag.Count);
        Assert.Equal(DiagnosticCode.DiagnosticCountExceeded, bag[3].Code);
        Assert.Null(bag[3].Span);
        // The moved report was a warning: the marker carries its severity.
        Assert.Equal(DiagnosticSeverity.Warning, bag[3].Severity);

        var formatted = 0;
        using (bag.InsertingAt(late))
        {
            Assert.False(bag.StoresNext);
            bag.Report(DiagnosticCode.UndeclaredIdentifier, null, 0, _ =>
            {
                formatted++;
                return "never";
            });
        }

        Assert.Equal(0, formatted);
        Assert.Equal(["e", "w0", "w1"], bag.Take(3).Select(d => d.Message));
        Assert.Equal(4, bag.Count);
        // The dropped anchored error raises the marker to an error: truncation never hides a blocking list.
        Assert.Equal(DiagnosticSeverity.Error, bag[3].Severity);
        Assert.Equal(5, bag.ReportedCount);
        Assert.Equal(2, bag.ReportedErrorCount);

        // A later in-place report is past the capacity too.
        bag.Report(DiagnosticCode.UnexpectedToken, "x", null);
        Assert.Equal(["e", "w0", "w1"], bag.Take(3).Select(d => d.Message));
        Assert.Equal(4, bag.Count);
    }

    [Fact]
    public void Bag_BulkDroppedErrorsPreserveCountsSeverityAndAnchorOrder()
    {
        static DiagnosticBag Reports(bool bulk)
        {
            var bag = new DiagnosticBag(2);
            var early = bag.ReserveAnchor();
            bag.Report(DiagnosticCode.UnexpectedToken, "first", null);
            bag.Report(DiagnosticCode.UnexpectedToken, "second", null);
            var late = bag.ReserveAnchor();
            void Drop()
            {
                if (bulk)
                    bag.ReportDroppedErrors(DiagnosticCode.UnforwardableParameter, 7);
                else
                    for (var n = 0; n < 7; n++)
                        bag.Report(DiagnosticCode.UnforwardableParameter, "unused", null);
            }
            using (bag.InsertingAt(late))
                Drop();
            Drop();
            using (bag.InsertingAt(early))
                bag.Report(DiagnosticCode.UndeclaredIdentifier, "inserted", null);
            return bag;
        }

        var individual = Reports(bulk: false);
        var grouped = Reports(bulk: true);
        Assert.Equal(individual.Select(Stored), grouped.Select(Stored));
        Assert.Equal((17, 17, true), (grouped.ReportedCount, grouped.ReportedErrorCount, grouped.HasReported(DiagnosticCode.UnforwardableParameter)));
    }

    [Fact]
    public void Bag_AnchoredScopes_DoNotNest()
    {
        var bag = new DiagnosticBag(4);
        var anchor = bag.ReserveAnchor();
        using (bag.InsertingAt(anchor))
            Assert.Throws<InvalidOperationException>(() => bag.InsertingAt(anchor));
        bag.Report(DiagnosticCode.UnexpectedToken, "after", null);
        Assert.Equal(["after"], bag.Select(d => d.Message));
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
    public void Bag_RejectsANonPositiveCapacity()
    {
        Assert.Throws<ArgumentOutOfRangeException>(() => new DiagnosticBag(0));
        Assert.Throws<ArgumentOutOfRangeException>(() => new DiagnosticBag(-1));
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
            await slowStarted.Task.WaitAsync(WaitLimit);
            cancellation.Cancel();
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(WaitLimit));
        }

        // Wait for the abandoned walk to unwind (it releases the materialization gate last).
        var region = Region(parsed.Root, "F", 1);
        using (var gateTimeout = new CancellationTokenSource(WaitLimit))
        {
            await region.Loader.MaterializationGate.WaitAsync(gateTimeout.Token);
            region.Loader.MaterializationGate.Release();
        }

        slowRelease.SetResult(slowSource);
        var retry = await Evaluator.RunFlatAsync(root).WaitAsync(WaitLimit);
        Assert.False(retry.IsError, retry.IsError ? retry.Error.ToString() : "");
        Assert.Equal([42m], retry.Value);
    }

    // ── E. Bounded echoes ───────────────────────────────────────────────────

    [Fact]
    public void OpenTargetRequiringArguments_EchoesABoundedParameterList()
    {
        var small = Assert.Single(Parse("open F\nF(a, b, c) = a\n1").Diagnostics);
        Assert.Equal(
            "'F' cannot be opened because open providers must have an empty effective parameter list (found: a, b, c).",
            small.Message);

        var parameters = string.Join(", ", Enumerable.Range(0, 2000).Select(i => $"p{i}"));
        var large = Parse($"open F, F\nF({parameters}) = p0\n1").Diagnostics;
        Assert.Equal(2, large.Count);
        Assert.All(large, d =>
        {
            Assert.Equal(DiagnosticCode.IllegalInOpen, d.Code);
            Assert.StartsWith("'F' cannot be opened because open providers must have an empty effective parameter list (found: p0, p1, p2, ", d.Message);
            Assert.Contains(ExprNameRenderer.TruncationMarker + ").", d.Message);
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
    public void ClosedValueDemand_DoesNotProduceAStaticNameListDiagnostic()
    {
        var names = string.Join(", ", Enumerable.Range(0, 1000).Select(i => $"x{i}"));
        Assert.Empty(Parse($"G = {names}\nH(q) = abs(G)\n1").Diagnostics);
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
                await both.Task.WaitAsync(WaitLimit);
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

    // ── G. Report payloads past the limit ───────────────────────────────────
    //
    // A report past the limit is counted and dropped, so it must cost no payload. The producers whose payload grows with the
    // source — implicit-argument resolution's UnforwardableParameter (one report per callee parameter bare forwarding cannot
    // supply) and OutputSpreadMarkerOnAlias (whose alias wording lists every parameter of the target), and the parser's
    // module-holder report of the same code — make every report and build a message only for a report the list stores.
    // Each test counts the reports MADE, the messages BUILT and the checks only a message reads, below, at and above the
    // limit, and checks the stored list against the unbounded one: the same prefix, order, codes, spans, text and layout.

    private static (DiagnosticBag Diagnostics, FrontEndTraversalObservations Observations) Elaborate(string source, int? limit = null)
    {
        var observations = new FrontEndTraversalObservations();
        var result = FrontEndPipeline.Process(source, new RunOptions { SourceProcessingLimits = Limits(limit) }, comparisonObservations: null, observations);
        return (Assert.IsType<DiagnosticBag>(result.Diagnostics), observations);
    }

    private static string Lines(string first, string second) => first + Environment.NewLine + second;

    private static string Names(string prefix, int count) => string.Join(", ", Enumerable.Range(0, count).Select(i => $"{prefix}{i}"));

    /// <summary>Above, at and just below the number of reports, then far below it.</summary>
    private static int[] LimitsAround(int reports) => [reports + 1, reports, reports - 1, 5, 1];

    // Everything a host can read of a stored diagnostic, its line layout included.
    private static (DiagnosticCode, DiagnosticSeverity, SourceSpan?, string, string) Stored(Diagnostic diagnostic)
        => (diagnostic.Code, diagnostic.Severity, diagnostic.Span, diagnostic.Message, diagnostic.RenderMessage(static line => $"<{line}>"));

    private static void AssertPrefixOfUnbounded(DiagnosticBag full, DiagnosticBag bounded, int limit)
    {
        Assert.False(full.IsTruncated);
        if (limit >= full.Count)
        {
            Assert.False(bounded.IsTruncated);
            Assert.Equal(full.Select(Stored), bounded.Select(Stored));
            return;
        }

        Assert.Equal(limit + 1, bounded.Count);
        Assert.Equal(full.Take(limit).Select(Stored), bounded.Take(limit).Select(Stored));
        AssertMarker(bounded[limit], limit);
    }

    [Fact]
    public void UnforwardableParameterFlood_BuildsAMessageOnlyForEachReportTheListKeeps()
    {
        // `A(q) = G` forwards none of G's 40 parameters: 40 reports at the bare reference, in G's parameter order.
        const int parameters = 40;
        var source = $"G({Names("p", parameters)}) = 0\nA(q) = G\n1";
        var (full, unbounded) = Elaborate(source);
        Assert.Equal(parameters, full.Count);
        Assert.All(full, d => Assert.Equal((DiagnosticCode.UnforwardableParameter, (SourceSpan?)new SourceSpan(2, 8, 2, 9)), (d.Code, d.Span)));
        Assert.Equal(Lines(
                "'G' is forwarded by name here, but its parameter 'p39' is not a parameter of the enclosing explicit parameter list.",
                "Bare forwarding reuses an existing parameter only under its own name, and explicit parameter lists are closed, "
                    + "so 'p39' is neither renamed nor added. Declare 'p39' in the parameter list, or call 'G' with explicit arguments."),
            full[^1].Message);
        Assert.Equal(parameters, unbounded.UnforwardableParameterMessages);

        foreach (var limit in LimitsAround(parameters))
        {
            var (bounded, observed) = Elaborate(source, limit);
            AssertPrefixOfUnbounded(full, bounded, limit);
            var stored = Math.Min(limit, parameters);
            // Every report is made and counted, so the list's status is the unbounded run's …
            Assert.Equal((parameters, parameters, true), (bounded.ReportedCount, bounded.ReportedErrorCount, bounded.HasReported(DiagnosticCode.UnforwardableParameter)));
            Assert.Equal(parameters, observed.UnforwardableParameterReports);
            // … every callee parameter is judged once, since each one's verdict decides whether it is reported, and the row
            // that is left as written builds no argument …
            Assert.Equal(parameters, observed.BareForwardingVerdicts);
            Assert.Equal(0, observed.BareForwardingArgumentsBuilt);
            // … but only a stored report builds its message, with the one name its wording checks.
            Assert.Equal(stored, observed.UnforwardableParameterMessages);
            Assert.Equal(stored, observed.UnforwardableParameterWordingChecks);
        }
    }

    [Fact]
    public void ManyNarrowForwarders_CountDroppedReportsWithoutJudgingEveryPair()
    {
        const int width = 40, callers = 16;
        // The repeated p2 is one report. Each caller supplies a different name, and q is irrelevant.
        var source = $"G({Names("p", width)}, p2) = 0\n"
            + string.Concat(Enumerable.Range(0, callers).Select(i => $"A{i}(p{i + 1}, q) = G\n"))
            + "1";
        const int reports = callers * (width - 1);
        var (full, unbounded) = Elaborate(source);
        Assert.Equal(reports, full.Count);
        Assert.Equal(callers * (width + 1), unbounded.BareForwardingVerdicts);

        foreach (var limit in new[] { reports + 1, reports, reports - 1, 1 })
        {
            var (bounded, work) = Elaborate(source, limit);
            AssertPrefixOfUnbounded(full, bounded, limit);
            Assert.Equal((reports, reports, true), (bounded.ReportedCount, bounded.ReportedErrorCount,
                bounded.HasReported(DiagnosticCode.UnforwardableParameter)));
            Assert.Equal(reports, work.UnforwardableParameterReports);
            Assert.Equal(Math.Min(limit, reports), work.UnforwardableParameterMessages);
            if (limit == 1)
            {
                // One full ordered row plus one failed verdict per later row. The index visits the
                // callee once and probes only each later caller's two names.
                Assert.Equal(width + 1 + callers - 1, work.BareForwardingVerdicts);
                Assert.Equal(width + 1 + 2 * (callers - 1), work.BareForwardingIndexSteps);
            }
        }
    }

    [Fact]
    public void DroppedForwardingReports_RespectShadowingAndLeaveSuccessfulRowsIntact()
    {
        const string source = """
            G(a, b, c, d, e, e) = a
            First(q) = G
            Outer(a, b) = {
                Inner([a], b) = G
                Accepted(c, d, e) = G
                1
            }
            1
            """;
        // First misses five distinct names. Inner's nested a shadows the enclosing a, so only b
        // supplies G. Accepted can forward all six slots from its own and its enclosing bindings.
        var work = new FrontEndTraversalObservations();
        var roomy = FrontEndPipeline.Process(source, new RunOptions { SourceProcessingLimits = Limits(Limit) });
        var tiny = FrontEndPipeline.Process(source, new RunOptions { SourceProcessingLimits = Limits(1), TraversalObservations = work });
        var full = Assert.IsType<DiagnosticBag>(roomy.Diagnostics);
        var bounded = Assert.IsType<DiagnosticBag>(tiny.Diagnostics);
        Assert.Equal(9, full.ReportedCount);
        Assert.Equal(full.ReportedCount, bounded.ReportedCount);
        AssertPrefixOfUnbounded(full, bounded, 1);
        Assert.Equal(Tree(roomy.ElaboratedRoot), Tree(tiny.ElaboratedRoot));
        Assert.True(work.BareForwardingIndexSteps > 0);
        Assert.Equal(6, work.BareForwardingArgumentsBuilt);
    }

    public static TheoryData<string, string[], int, int> UnforwardableWordings => new()
    {
        // An explicit list: `u` is bound nowhere; `[a, b]` has a leaf the list binds as a whole parameter, so it is not
        // declared "in that form"; `v` is supplied, after the first unforwardable parameter, so no argument is built for it.
        {
            "G(u, [a, b], v) = 0\nA(v, a) = G\n1",
            [
                Lines(
                    "'G' is forwarded by name here, but its parameter 'u' is not a parameter of the enclosing explicit parameter list.",
                    "Bare forwarding reuses an existing parameter only under its own name, and explicit parameter lists are closed, "
                        + "so 'u' is neither renamed nor added. Declare 'u' in the parameter list, or call 'G' with explicit arguments."),
                Lines(
                    "'G' is forwarded by name here, but the enclosing explicit parameter list does not declare its parameter '[a, b]' in that form.",
                    "Bare forwarding reuses an existing parameter only with the same pattern and never reshapes an argument. "
                        + "Declare the parameter '[a, b]', or call 'G' with explicit arguments."),
            ],
            3,
            2
        },
        // A conditional branch: `x` is bound only inside the head's list pattern, `y` not at all.
        {
            "G(x, y) = 0\nF([x]) = G\nF([1]) = 0\n1",
            [
                Lines(
                    "'G' is forwarded by name here, but the pattern of conditional branch 'F' does not bind its parameter 'x' in that form.",
                    "Bare forwarding reuses an existing binding only with the same pattern and never reshapes an argument. "
                        + "Bind 'x' in the branch pattern, or call 'G' with explicit arguments."),
                Lines(
                    "'G' is forwarded by name here, but its parameter 'y' is not bound by the pattern of conditional branch 'F'.",
                    "Bare forwarding reuses an existing binding only under its own name, and conditional branch patterns are closed, "
                        + "so 'y' is neither renamed nor added. Bind 'y' in the branch pattern, or call 'G' with explicit arguments."),
            ],
            2,
            2
        },
    };

    [Theory]
    [MemberData(nameof(UnforwardableWordings))]
    public void UnforwardableParameterWording_IsReadOnlyForAStoredReport(string source, string[] messages, int verdicts, int wordingChecks)
    {
        var (full, unbounded) = Elaborate(source);
        Assert.Equal(messages, full.Select(d => d.Message));
        Assert.All(full, d => Assert.Equal(DiagnosticCode.UnforwardableParameter, d.Code));
        Assert.Equal((messages.Length, messages.Length, verdicts, 0, wordingChecks), (unbounded.UnforwardableParameterReports,
            unbounded.UnforwardableParameterMessages, unbounded.BareForwardingVerdicts, unbounded.BareForwardingArgumentsBuilt,
            unbounded.UnforwardableParameterWordingChecks));

        // A one-diagnostic list keeps the first report and words nothing else: the second report is made and counted, and
        // neither its message nor the check of its pattern happens.
        var (bounded, observed) = Elaborate(source, limit: 1);
        AssertPrefixOfUnbounded(full, bounded, limit: 1);
        Assert.Equal(messages.Length, bounded.ReportedCount);
        Assert.Equal((messages.Length, 1, verdicts, 0, 1), (observed.UnforwardableParameterReports,
            observed.UnforwardableParameterMessages, observed.BareForwardingVerdicts, observed.BareForwardingArgumentsBuilt,
            observed.UnforwardableParameterWordingChecks));
    }

    [Theory]
    // Arguments for the supplied parameters BEFORE the first unforwardable one are built (the verdict is not yet known),
    // none after it; every parameter is still judged, because each verdict decides whether it is reported.
    [InlineData("G(v, w, u) = 0\nA(v, w) = G\n1", 2)]
    [InlineData("G(v, u, w) = 0\nA(v, w) = G\n1", 1)]
    [InlineData("G(u, v, w) = 0\nA(v, w) = G\n1", 0)]
    public void BareForwarding_BuildsNoArgumentAfterTheFirstUnforwardableParameter(string source, int argumentsBuilt)
    {
        var (diagnostics, observations) = Elaborate(source);
        var diagnostic = Assert.Single(diagnostics);
        Assert.StartsWith("'G' is forwarded by name here, but its parameter 'u' is not a parameter", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal((3, argumentsBuilt, 1), (observations.BareForwardingVerdicts, observations.BareForwardingArgumentsBuilt, observations.UnforwardableParameterReports));
    }

    [Fact]
    public void BareForwarding_ThatSucceeds_BuildsEveryArgument_ByName()
    {
        // The accepted binding result is unchanged: `A(w, v) = G` is `G(v, w)` by name, so `A(10, 3)` is 3 - 10.
        const string source = "G(v, w) = v - w\nA(w, v) = G\nA(10, 3)";
        var (diagnostics, observations) = Elaborate(source);
        Assert.Empty(diagnostics);
        Assert.Equal((2, 2, 0), (observations.BareForwardingVerdicts, observations.BareForwardingArgumentsBuilt, observations.UnforwardableParameterReports));
        Assert.Equal([-7m], Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root)).Value);
    }

    [Fact]
    public void UnforwardableParameters_WithNoListToReportInto_AreJudgedOnlyUpToTheFirst()
    {
        // A resolution that reports nothing (a provisional branch, a rewrite-only entry) needs one unforwardable parameter to
        // leave the row as written: it judges no further parameter, and the row it leaves is the reporting run's.
        const int parameters = 40;
        var source = $"G({Names("p", parameters)}) = 0\nA(q) = G\n1";
        (Algorithm Resolved, FrontEndTraversalObservations Observations) Resolve(DiagnosticBag? diagnostics)
        {
            var program = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
            Assert.Equal(0, program.Diagnostics.ReportedCount);
            var observations = new FrontEndTraversalObservations();
            var resolved = ImplicitArgumentResolver.ResolvePrevalidated(
                program.Root, observations, diagnostics, program.HostOperations, program.Modules, program.Operation);
            return (resolved, observations);
        }

        var list = new DiagnosticBag(1);
        var (reported, reporting) = Resolve(list);
        var (silent, unreported) = Resolve(diagnostics: null);

        Assert.Equal(parameters, list.ReportedCount);
        Assert.Equal((parameters, parameters, 1), (reporting.BareForwardingVerdicts, reporting.UnforwardableParameterReports, reporting.UnforwardableParameterMessages));
        Assert.Equal((1, 0, 0), (unreported.BareForwardingVerdicts, unreported.UnforwardableParameterReports, unreported.UnforwardableParameterMessages));
        Assert.Equal(Tree(reported), Tree(silent));
    }

    [Fact]
    public void UnforwardableParameterReplays_ForFamiliesSharingABranchBody_BuildOnlyTheMessagesTheListKeeps()
    {
        // One branch body `G` shared by three families is rewritten once; the second and third family re-issue its reports
        // in their own names (M4). A re-issued report is made and counted like the first; its message is built only when
        // the list stores it, and the parameter's part of the wording is read once, at its first stored report.
        const int parameters = 6;
        string[] families = ["Left", "Middle", "Right"];
        var parsed = Parser.ParseSyntax($"G({Names("p", parameters)}) = 0\nF(0) = G\nF(1) = 0\n1");
        Assert.False(parsed.HasErrors);
        var sharedBody = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.SyntaxRoot.Properties, p => p.Name == "F").Value).Branches[0].Body;
        var g = Assert.Single(parsed.SyntaxRoot.Properties, p => p.Name == "G");

        (DiagnosticBag Diagnostics, FrontEndTraversalObservations Observations) Resolve(int limit)
        {
            var root = new Algorithm.User(null, [], [],
                [g, .. families.Select(family => new Property(family, new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), sharedBody)])))],
                new OutputBundle([new Expr.Num(1)]));
            var diagnostics = new DiagnosticBag(limit);
            var program = ParameterDetector.DetectPrevalidated(root, diagnostics: diagnostics);
            Assert.Equal(0, diagnostics.ReportedCount);
            var observations = new FrontEndTraversalObservations();
            _ = ImplicitArgumentResolver.ResolvePrevalidated(program, observations, diagnostics);
            return (diagnostics, observations);
        }

        const int reports = 3 * parameters;
        var (full, unbounded) = Resolve(Limit);
        Assert.Equal(1, unbounded.ResolverBranchBodyRegionExpansions);
        Assert.Equal(
            [.. families.SelectMany(family => Enumerable.Range(0, parameters).Select(i => $"'G' is forwarded by name here, but its parameter 'p{i}' is not bound by the pattern of conditional branch '{family}'."))],
            full.Select(d => d.Message.Split(Environment.NewLine)[0]));
        Assert.Equal((reports, reports, parameters), (unbounded.UnforwardableParameterReports, unbounded.UnforwardableParameterMessages, unbounded.UnforwardableParameterWordingChecks));

        foreach (var limit in new[] { reports + 1, reports, reports - 1, parameters + 2, parameters, parameters - 1, 1 })
        {
            var (bounded, observed) = Resolve(limit);
            AssertPrefixOfUnbounded(full, bounded, limit);
            Assert.Equal(reports, bounded.ReportedCount);
            Assert.Equal(reports, observed.UnforwardableParameterReports);
            Assert.Equal(parameters, observed.BareForwardingVerdicts);
            Assert.Equal(Math.Min(limit, reports), observed.UnforwardableParameterMessages);
            Assert.Equal(Math.Min(limit, parameters), observed.UnforwardableParameterWordingChecks);
        }
    }

    [Fact]
    public void OutputSpreadMarkerOnAliasFlood_BuildsAMessageOnlyForEachReportTheListKeeps()
    {
        // 30 marked aliases of a 50-parameter target: each report's wrapper suggestion lists all 50 parameters.
        const int aliases = 30;
        const int parameters = 50;
        var targetParameters = Names("p", parameters);
        var source = $"T({targetParameters}) = 0\n" + string.Concat(Enumerable.Range(0, aliases).Select(i => $"B{i}* = T\n")) + "1";
        var (full, unbounded) = Elaborate(source);
        Assert.Equal(aliases, full.Count);
        Assert.All(full, d => Assert.Equal(DiagnosticCode.OutputSpreadMarkerOnAlias, d.Code));
        Assert.Equal(Enumerable.Range(0, aliases).Select(i => (SourceSpan?)new SourceSpan(i + 2, i < 10 ? 3 : 4, i + 2, i < 10 ? 4 : 5)), full.Select(d => d.Span));
        Assert.Equal(Lines(
                "'B0' is an alias of 'T', so it cannot carry the output-spreading marker `*`: calls through an alias are calls of 'T', and they spread exactly when it is marked.",
                $"To spread the output of calls to 'B0' itself, declare a marked wrapper: `B0({targetParameters})* = T({targetParameters})`."),
            full[0].Message);
        Assert.Equal((aliases, aliases * parameters), (unbounded.OutputSpreadMarkerOnAliasMessages, unbounded.OutputSpreadMarkerWrapperParameterReads));

        foreach (var limit in LimitsAround(aliases))
        {
            var (bounded, observed) = Elaborate(source, limit);
            AssertPrefixOfUnbounded(full, bounded, limit);
            var stored = Math.Min(limit, aliases);
            Assert.Equal(aliases, bounded.ReportedCount);
            Assert.Equal(aliases, observed.OutputSpreadMarkerOnAliasReports);
            Assert.Equal(stored, observed.OutputSpreadMarkerOnAliasMessages);
            Assert.Equal(stored * parameters, observed.OutputSpreadMarkerWrapperParameterReads);
        }
    }

    [Theory]
    // Two markers on runtime-target aliases, and two on `.Algorithm` links that stay calculations.
    [InlineData("F(f) = {\nG* = f\nH* = f\nG(1)\n}\nF({ x + 1 })", "is a runtime-target alias, so it cannot carry the output-spreading marker `*`: the callable it calls is known only at run time")]
    [InlineData("Mk(meta op) = op\nG* = Mk.Algorithm\nH* = Mk.Algorithm\n1", "is an `.Algorithm` link, so it cannot carry the output-spreading marker `*`: the algorithm a link calls is known only at run time")]
    public void OutputSpreadMarkerOnRuntimeTargets_BuildAMessageOnlyForAStoredReport(string source, string reason)
    {
        var (full, unbounded) = Elaborate(source);
        Assert.Equal(
            new[] { "G", "H" }.Select(name => Lines(
                $"'{name}' {reason}, and only a call the front end resolves statically to a marked declaration is spread.",
                "Declare a marked algorithm with explicit parameters that calls it instead.")),
            full.Select(d => d.Message));
        Assert.All(full, d => Assert.Equal(DiagnosticCode.OutputSpreadMarkerOnAlias, d.Code));
        Assert.Equal((2, 2), (unbounded.OutputSpreadMarkerOnAliasReports, unbounded.OutputSpreadMarkerOnAliasMessages));

        foreach (var limit in new[] { 3, 2, 1 })
        {
            var (bounded, observed) = Elaborate(source, limit);
            AssertPrefixOfUnbounded(full, bounded, limit);
            Assert.Equal(2, bounded.ReportedCount);
            Assert.Equal((2, Math.Min(limit, 2), 0), (observed.OutputSpreadMarkerOnAliasReports, observed.OutputSpreadMarkerOnAliasMessages, observed.OutputSpreadMarkerWrapperParameterReads));
        }
    }

    [Fact]
    public void ModuleHolderMarkerFlood_BuildsAMessageOnlyForEachReportTheListKeeps()
    {
        // The parser refuses a marker on a module holder: one OutputSpreadMarkerOnAlias report per marked holder, at its `*`.
        static string Holders(int count, string marker)
            => string.Concat(Enumerable.Range(0, count).Select(i => $"M{i}{marker} = load('{Host}lib.kat')\n")) + "1";

        const int holders = 12;
        var source = Holders(holders, "*");
        var full = Parser.ParseSyntax(source, new DiagnosticBag()).Diagnostics;
        Assert.Equal(holders, full.Count);
        Assert.All(full, d => Assert.Equal(DiagnosticCode.OutputSpreadMarkerOnAlias, d.Code));
        Assert.Equal(Enumerable.Range(0, holders).Select(i => (SourceSpan?)new SourceSpan(i + 1, i < 10 ? 3 : 4, i + 1, i < 10 ? 4 : 5)), full.Select(d => d.Span));
        Assert.Equal(
            "'M0' holds a loaded module, so it cannot carry the output-spreading marker `*`: a module is one declaration, "
                + "shared by every holder of its URL. Mark the module's own declarations instead.",
            full[0].Message);
        foreach (var limit in LimitsAround(holders))
        {
            var observations = new ParserTraversalObservations();
            var bounded = Parser.ParseSyntaxObserved(source, observations, new DiagnosticBag(limit)).Diagnostics;
            AssertPrefixOfUnbounded(full, bounded, limit);
            Assert.Equal(holders, bounded.ReportedCount);
            Assert.Equal(Math.Min(holders, limit), observations.ModuleHolderMarkerMessages);
        }
    }

    // ── H. Stored payloads built to the retained prefix ─────────────────────
    //
    // A STORED report whose text grows with the source is built only as far as its bound reads. A list decides what it
    // stores of a message from the message's first DiagnosticBag.RetainedPrefixLength (4,097) units — whether to cut it,
    // and where the surrogate-safe cut falls — and a name echoed bounded is decided by its first 513 units. So the
    // marked-wrapper suggestion of OutputSpreadMarkerOnAlias is built to the list's prefix, and the written form of a
    // parameter that UnforwardableParameter and ExplicitParametersRequireOutput show to the name's: the stored text — its
    // cut, marker and line layout — is the whole message's, while the work and the text built stop at the prefix. The
    // oracles below rebuild each whole message as the former formatters built it; the counters show what was read, and
    // the allocation control fails if a whole text is built again.

    // A whole message as a list keeps it, cut independently of the bag: whole up to the bound, else its first 4,096 units
    // — one fewer when they would end inside a surrogate pair — and the marker.
    private static string RetainedText(string whole)
    {
        const int bound = DiagnosticBag.MaxRetainedMessageLength;
        if (whole.Length <= bound)
            return whole;
        var cut = char.IsHighSurrogate(whole[bound - 1]) && char.IsLowSurrogate(whole[bound]) ? bound - 1 : bound;
        return whole[..cut] + ExprNameRenderer.TruncationMarker;
    }

    // A name as a diagnostic echoes it bounded, cut independently of the renderer the same way at 512 units.
    private static string ShownName(string whole)
    {
        const int bound = ExprNameRenderer.MaxRenderedNameLength;
        if (whole.Length <= bound)
            return whole;
        var cut = char.IsHighSurrogate(whole[bound - 1]) && char.IsLowSurrogate(whole[bound]) ? bound - 1 : bound;
        return whole[..cut] + ExprNameRenderer.TruncationMarker;
    }

    // What a list stores for a whole message with one line break after its first line.
    private static Diagnostic StoredForm(string whole, int lineBreak, DiagnosticCode code, SourceSpan? span)
        => new Diagnostic(new DiagnosticMessage(whole, [lineBreak]), DiagnosticSeverity.Error, span) { Code = code }
            .WithBoundedMessage(DiagnosticBag.MaxRetainedMessageLength);

    /// <summary>
    /// The OutputSpreadMarkerOnAlias message about a transparent alias, as the former formatter built it WHOLE — the
    /// explanation, the line break, and the repair, whose wrapper lists every parameter of the target twice — with its
    /// first line and where each parameter's text starts in it (its first writing, in the wrapper's parameter list).
    /// </summary>
    private static (string First, string Text, IReadOnlyList<int> ParameterStarts) WholeAliasMarkerMessage(
        string alias, string target, IReadOnlyList<ParameterPattern> parameters)
    {
        var name = ExprNameRenderer.BoundName(alias);
        var shownTarget = ExprNameRenderer.BoundName(target);
        var first = $"'{name}' is an alias of '{shownTarget}', so it cannot carry the output-spreading marker `*`: "
            + $"calls through an alias are calls of '{shownTarget}', and they spread exactly when it is marked.";
        var repair = $"To spread the output of calls to '{name}' itself, declare a marked wrapper: `";
        var starts = new List<int>();
        string suggestion;
        if (parameters.Any(static parameter => parameter is not CaptureParameterPattern))
            suggestion = $"{name}(…)* = {shownTarget}(…)";
        else if (parameters.Count == 0)
            suggestion = $"{name}* = {shownTarget}()";
        else
        {
            var captures = parameters.Cast<CaptureParameterPattern>().ToList();
            var listed = captures.Select(static c => (c.Kind == ParameterKind.Collecting ? "*" : "") + ExprNameRenderer.BoundName(c.Name)).ToList();
            var forwarded = captures.Select(static c => ExprNameRenderer.BoundName(c.Name) + (c.Kind == ParameterKind.Collecting ? "*" : "")).ToList();
            var start = first.Length + Environment.NewLine.Length + repair.Length + name.Length + 1;
            foreach (var item in listed)
            {
                starts.Add(start);
                start += item.Length + 2;
            }

            suggestion = $"{name}({string.Join(", ", listed)})* = {shownTarget}({string.Join(", ", forwarded)})";
        }

        return (first, first + Environment.NewLine + repair + suggestion + "`.", starts);
    }

    private static int ShownParameters(IReadOnlyList<int> starts) => starts.Count(static start => start < DiagnosticBag.RetainedPrefixLength);

    /// <summary>
    /// A parsed program whose declaration <paramref name="name"/> a host gave other parameter patterns — the lexer admits
    /// no surrogate in a name, so only a host tree carries one — detected and resolved into a list of the given capacity.
    /// </summary>
    private static (DiagnosticBag Diagnostics, FrontEndTraversalObservations Observations) ResolveHostBuilt(
        string source, string name, IReadOnlyList<ParameterPattern> parameters, int limit = Limit)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.False(parsed.HasErrors);
        var root = parsed.SyntaxRoot;
        var host = root with
        {
            Properties = [.. root.Properties.Select(property => property.Name == name
                ? property with { Value = Assert.IsType<Algorithm.User>(property.Value) with { ParameterPatterns = parameters } }
                : property)],
        };
        var diagnostics = new DiagnosticBag(limit);
        var program = ParameterDetector.DetectPrevalidated(host, diagnostics: diagnostics);
        var observations = new FrontEndTraversalObservations();
        _ = ImplicitArgumentResolver.ResolvePrevalidated(program, observations, diagnostics);
        return (diagnostics, observations);
    }

    [Fact]
    public void RetainedPrefix_OfAMessage_IsStoredExactlyAsTheWholeMessage()
    {
        // The law the builders rely on, at the bag: a message's first RetainedPrefixLength units, kept by a RAW cut however
        // the message was split into fragments, store exactly what the whole message stores — at every length around the
        // bound, with a surrogate pair before, across and after the cut and across the prefix's end, and with lone halves.
        const int bound = DiagnosticBag.MaxRetainedMessageLength;
        Assert.Equal(bound + 1, DiagnosticBag.RetainedPrefixLength);
        const string pair = "😀";
        const string first = "The first line.";
        var head = first + Environment.NewLine;
        string Filler(int until) => head + new string('m', until - head.Length);
        var messages = new List<string>();
        foreach (var length in new[] { bound - 1, bound, bound + 1, bound + 2, bound + 3, 2 * bound })
            messages.Add(Filler(length));
        foreach (var start in new[] { bound - 2, bound - 1, bound, bound + 1 })
            messages.Add(Filler(start) + pair + "tail");
        messages.Add(Filler(bound - 1) + "\uD83D" + "tail");
        messages.Add(Filler(bound) + "\uDE00" + "tail");
        messages.Add(Filler(bound) + "\uD83D");

        foreach (var whole in messages)
        {
            var expected = StoreWhole(whole);
            Assert.Equal(RetainedText(whole), expected.Message);

            // One fragment, two around every unit near the cut and the prefix's end, and one-unit fragments.
            var splits = new List<string[]> { new[] { whole } };
            for (var at = bound - 3; at <= bound + 3 && at < whole.Length; at++)
                splits.Add([whole[..at], whole[at..]]);
            splits.Add([.. whole.Select(static unit => unit.ToString())]);
            foreach (var fragments in splits)
            {
                var prefix = new Rendering.TextPrefixBuilder(DiagnosticBag.RetainedPrefixLength);
                foreach (var fragment in fragments)
                {
                    if (!prefix.Append(fragment))
                        break;
                }

                Assert.Equal(whole[..Math.Min(whole.Length, DiagnosticBag.RetainedPrefixLength)], prefix.ToString());
                Assert.Equal(Stored(expected), Stored(StoreWhole(prefix.ToString())));
            }
        }

        // Why the cut is raw: a surrogate-safe cut at the prefix's end keeps `bound` units of a longer message, which the
        // list would then store whole, without its marker.
        var acrossTheEnd = new string('m', bound) + pair + "tail";
        var safe = acrossTheEnd[..ExprNameRenderer.SafePrefixLength(acrossTheEnd, DiagnosticBag.RetainedPrefixLength)];
        Assert.Equal(bound, safe.Length);
        Assert.Equal(acrossTheEnd[..bound] + ExprNameRenderer.TruncationMarker, StoreWhole(acrossTheEnd).Message);
        Assert.Equal(safe, StoreWhole(safe).Message);

        static Diagnostic StoreWhole(string message)
        {
            var bag = new DiagnosticBag(1);
            bag.Report(DiagnosticCode.UnexpectedToken, new SourceSpan(1, 1, 1, 2), message,
                static text => new DiagnosticMessage(text, [first.Length]));
            return Assert.Single(bag);
        }
    }

    [Fact]
    public void MarkedWrapperSuggestion_StoresTheWholeMessagesText_AcrossTheRetentionBound()
    {
        // T's last parameter grows unit by unit, so the whole message, whose repair lists T's parameters twice, passes the
        // 4,096-unit bound in steps of two units, and a one- or two-letter alias (its name is written three times) gives
        // both parities. Each stored message is the whole one's, cut by the list, and its wrapper read only the parameters
        // that begin inside the 4,097-unit prefix the list reads.
        const int bound = DiagnosticBag.MaxRetainedMessageLength;
        var lengths = new HashSet<int>();
        foreach (var alias in new[] { "B", "BB" })
        {
            for (var tail = 1; tail <= 400; tail++)
            {
                var names = Enumerable.Range(0, 300).Select(static i => $"p{i}").Append("z" + new string('t', tail - 1)).ToList();
                var (first, whole, starts) = WholeAliasMarkerMessage(alias, "T", [.. names.Select(static n => (ParameterPattern)new CaptureParameterPattern(n))]);
                if (whole.Length is < bound - 4 or > bound + 4)
                    continue;

                lengths.Add(whole.Length);
                var (diagnostics, observations) = Elaborate($"T({string.Join(", ", names)}) = 0\n{alias}* = T\n1");
                var stored = Assert.Single(diagnostics);
                var span = new SourceSpan(2, alias.Length + 1, 2, alias.Length + 2);
                Assert.Equal(Stored(StoredForm(whole, first.Length, DiagnosticCode.OutputSpreadMarkerOnAlias, span)), Stored(stored));
                Assert.Equal(RetainedText(whole), stored.Message);
                Assert.Equal((1, ShownParameters(starts)), (observations.OutputSpreadMarkerOnAliasMessages,
                    observations.OutputSpreadMarkerWrapperParameterReads));
            }
        }

        Assert.Superset(new HashSet<int> { bound - 1, bound, bound + 1, bound + 2 }, lengths);
    }

    public static TheoryData<string, string, int> OrdinaryWrapperForms => new()
    {
        // Plain parameters, a collector forwarded as `ys*`, a meta parameter (listed by its name), a target with none, and a
        // structural parameter anywhere, which makes the suggestion generic.
        { "A(x, y)* = x, y\nB* = A\nB(1, 2)", "B(x, y)* = A(x, y)", 2 },
        { "A(x, *ys)* = x, ys*\nB* = A\nB(1)", "B(x, *ys)* = A(x, ys*)", 2 },
        { "A(meta f) = f\nB* = A\n1", "B(f)* = A(f)", 1 },
        { "P* = 1\nB* = P\nB()", "B* = P()", 0 },
        { "A(x, [y], z) = x\nB* = A\n1", "B(…)* = A(…)", 0 },
        { "A((y, z)) = y\nB* = A\n1", "B(…)* = A(…)", 0 },
    };

    [Theory]
    [MemberData(nameof(OrdinaryWrapperForms))]
    public void MarkedWrapperSuggestion_OfAnOrdinaryTarget_IsStoredWhole(string source, string suggestion, int reads)
    {
        var (diagnostics, observations) = Elaborate(source);
        var stored = Assert.Single(diagnostics, static d => d.Code == DiagnosticCode.OutputSpreadMarkerOnAlias);
        var target = source[..1];
        var first = $"'B' is an alias of '{target}', so it cannot carry the output-spreading marker `*`: "
            + $"calls through an alias are calls of '{target}', and they spread exactly when it is marked.";
        var repair = $"To spread the output of calls to 'B' itself, declare a marked wrapper: `{suggestion}`.";
        Assert.Equal(Lines(first, repair), stored.Message);
        Assert.Equal($"<{first}>{Environment.NewLine}<{repair}>", stored.RenderMessage(static line => $"<{line}>"));
        Assert.Equal((1, reads), (observations.OutputSpreadMarkerOnAliasMessages, observations.OutputSpreadMarkerWrapperParameterReads));
    }

    [Theory]
    [InlineData("T")]
    [InlineData("Lifted")]
    public void StructuralParameterPastThePrefix_SelectsTheGenericWrapper(string target)
    {
        // The last structural slot would fall beyond the cut in a plain wrapper. It decides the
        // suggestion even through a lifted signature with an owner-local head and a shared tail.
        var source = $"T({Names("p", 1200)}, [lastSlot]) = 0\nLifted = own + T\nB* = {target}\nC* = {target}\n1";
        var (diagnostics, observations) = Elaborate(source, 1);
        Assert.Equal(2, diagnostics.ReportedCount);
        Assert.Equal(DiagnosticCode.OutputSpreadMarkerOnAlias, diagnostics[0].Code);
        Assert.EndsWith($"`B(…)* = {target}(…)`.", diagnostics[0].Message, StringComparison.Ordinal);
        Assert.Equal(DiagnosticCode.DiagnosticCountExceeded, diagnostics[1].Code);
        Assert.Equal((1, 0), (observations.OutputSpreadMarkerOnAliasMessages, observations.OutputSpreadMarkerWrapperParameterReads));
    }

    [Fact]
    public void WideAliasTargetFlood_BuildsEachStoredMessageOnlyToItsRetainedPrefix()
    {
        // 12 marked aliases of a 3,000-parameter target: each whole message is about 32,000 units, so every stored one is
        // cut, and its wrapper reads only the parameters that begin inside the retained prefix. Every alias's report is
        // made and counted at every limit; only a stored one is built.
        const int aliases = 12, parameters = 3000;
        ParameterPattern[] patterns = [.. Enumerable.Range(0, parameters).Select(static i => new CaptureParameterPattern($"p{i}"))];
        var source = $"T({Names("p", parameters)}) = 0\n" + string.Concat(Enumerable.Range(0, aliases).Select(i => $"B{i}* = T\n")) + "1";
        var wholes = Enumerable.Range(0, aliases).Select(i => WholeAliasMarkerMessage($"B{i}", "T", patterns)).ToList();
        var shown = wholes.Select(static whole => ShownParameters(whole.ParameterStarts)).ToList();
        Assert.All(shown, static count => Assert.InRange(count, 400, 800));

        var (full, _) = Elaborate(source);
        Assert.Equal(aliases, full.Count);
        for (var i = 0; i < aliases; i++)
        {
            var span = new SourceSpan(i + 2, i < 10 ? 3 : 4, i + 2, i < 10 ? 4 : 5);
            Assert.Equal(Stored(StoredForm(wholes[i].Text, wholes[i].First.Length, DiagnosticCode.OutputSpreadMarkerOnAlias, span)), Stored(full[i]));
            Assert.Equal(DiagnosticBag.MaxRetainedMessageLength + 1, full[i].Message.Length);
        }

        foreach (var limit in LimitsAround(aliases))
        {
            var (bounded, observed) = Elaborate(source, limit);
            AssertPrefixOfUnbounded(full, bounded, limit);
            var stored = Math.Min(limit, aliases);
            Assert.Equal((aliases, aliases, true), (bounded.ReportedCount, bounded.ReportedErrorCount, bounded.HasReported(DiagnosticCode.OutputSpreadMarkerOnAlias)));
            Assert.Equal((aliases, stored), (observed.OutputSpreadMarkerOnAliasReports, observed.OutputSpreadMarkerOnAliasMessages));
            // The signature supplies the wrapper shape. Formatting reads only the parameters in the prefix.
            Assert.Equal(shown.Take(stored).Sum(), observed.OutputSpreadMarkerWrapperParameterReads);
        }
    }

    [Fact]
    public void MarkedWrapperSuggestion_IsCutAroundSurrogatePairs_AsTheListCutsTheWholeMessage()
    {
        // A host-built target whose later parameter names are runs of astral scalars (two units each), shifted unit by
        // unit so that a pair lies across the 4,096-unit cut, or across the end of the 4,097-unit prefix the message is
        // built to — where the prefix ends in a lone high surrogate, and the list must still cut there and add its marker.
        const int bound = DiagnosticBag.MaxRetainedMessageLength;
        const string source = "T(a, b) = 0\nB* = T\n1";

        // The host route is the parse's route: with the written names it stores what the parse stores.
        ParameterPattern[] written = [new CaptureParameterPattern("a"), new CaptureParameterPattern("b")];
        Assert.Equal(Elaborate(source).Diagnostics.Select(Stored), ResolveHostBuilt(source, "T", written).Diagnostics.Select(Stored));

        var placements = new HashSet<string>();
        for (var shift = 0; shift < 8; shift++)
        {
            ParameterPattern[] parameters =
            [
                .. Enumerable.Range(0, 400).Select(static i => new CaptureParameterPattern($"p{i}")),
                new CaptureParameterPattern(new string('q', 1 + shift)),
                .. Enumerable.Range(0, 8).Select(static i => new CaptureParameterPattern(string.Concat(Enumerable.Repeat("😀", 250)))),
            ];
            var (first, whole, starts) = WholeAliasMarkerMessage("B", "T", parameters);
            var (diagnostics, observations) = ResolveHostBuilt(source, "T", parameters);
            var stored = Assert.Single(diagnostics);
            Assert.Equal(Stored(StoredForm(whole, first.Length, DiagnosticCode.OutputSpreadMarkerOnAlias, new SourceSpan(2, 2, 2, 3))), Stored(stored));
            Assert.Equal(RetainedText(whole), stored.Message);
            Assert.Equal(ShownParameters(starts), observations.OutputSpreadMarkerWrapperParameterReads);
            placements.Add(char.IsHighSurrogate(whole[bound - 1]) ? "across the cut" : char.IsHighSurrogate(whole[bound]) ? "across the prefix's end" : "elsewhere");
        }

        Assert.Superset(new HashSet<string> { "across the cut", "across the prefix's end" }, placements);
    }

    // The UnforwardableParameter message of `A(q) = G` for G's parameter shown as `shown`, which A binds in no form.
    private static (string First, string Text) UnforwardableMessage(string shown)
    {
        var first = $"'G' is forwarded by name here, but its parameter '{shown}' is not a parameter of the enclosing explicit parameter list.";
        return (first, Lines(first, "Bare forwarding reuses an existing parameter only under its own name, and explicit parameter lists are closed, "
            + $"so '{shown}' is neither renamed nor added. Declare '{shown}' in the parameter list, or call 'G' with explicit arguments."));
    }

    // The nodes the bounded written form writes of a group of leaves: its opener, then each leaf that begins inside the
    // 513-unit prefix after its separator.
    private static int ShownGroupNodes(IEnumerable<string> leaves)
    {
        var nodes = 1;
        var start = 1;
        foreach (var leaf in leaves)
        {
            if (start >= ExprNameRenderer.MaxRenderedNameLength + 1)
                break;
            nodes++;
            start += leaf.Length + 2;
        }

        return nodes;
    }

    [Fact]
    public void ForwardedStructuralParameter_IsShownBounded_FromItsShownPrefixOnly()
    {
        // G's one parameter, which `A0(q) = G` and `A1(q) = G` cannot forward, is shown by its written form, cut to the
        // name bound: wide (5,000 leaves), with a collector, deep (280 groups, near the source's 300-node structural depth
        // limit), a long name, the forms whose text is 511 to 514 units, and an ordinary nested one. Each stored message is
        // the whole one's; only the nodes the shown prefix holds are written. Every leaf's binding is still checked for the
        // wording (whether A binds the parameter in another form), once per stored message.
        static string Deep(int depth) => new string('[', depth) + "x" + new string(']', depth);
        var wide = Enumerable.Range(0, 5000).Select(static i => $"a{i}").ToList();
        var withCollector = Enumerable.Range(0, 3000).Select(static i => $"b{i}").Append("*rest").ToList();
        (string Pattern, int Nodes, int Leaves)[] cases =
        [
            ($"[{string.Join(", ", wide)}]", ShownGroupNodes(wide), wide.Count),
            ($"({string.Join(", ", withCollector)})", ShownGroupNodes(withCollector), withCollector.Count),
            (Deep(280), 281, 1),
            ($"[{new string('x', 5000)}]", 2, 1),
            .. new[] { 509, 510, 511, 512 }.Select(static length => ($"[{new string('y', length)}]", 2, 1)),
            ("[(a, b), [c, *d], e]", 8, 5),
        ];

        foreach (var (pattern, nodes, leaves) in cases)
        {
            var source = $"G({pattern}) = 0\nA0(q) = G\nA1(q) = G\n1";
            var (first, whole) = UnforwardableMessage(ShownName(pattern));
            var (full, unbounded) = Elaborate(source);
            Assert.Equal(2, full.Count);
            Assert.Equal(Stored(StoredForm(whole, first.Length, DiagnosticCode.UnforwardableParameter, new SourceSpan(2, 9, 2, 10))), Stored(full[0]));
            Assert.Equal(Stored(StoredForm(whole, first.Length, DiagnosticCode.UnforwardableParameter, new SourceSpan(3, 9, 3, 10))), Stored(full[1]));
            Assert.Equal((2, 2 * nodes, 2 * leaves), (unbounded.UnforwardableParameterMessages, unbounded.UnforwardableParameterDisplayNodes,
                unbounded.UnforwardableParameterWordingChecks));

            foreach (var limit in new[] { 3, 2, 1 })
            {
                var (bounded, observed) = Elaborate(source, limit);
                AssertPrefixOfUnbounded(full, bounded, limit);
                var stored = Math.Min(limit, 2);
                Assert.Equal((2, 2, 2), (bounded.ReportedCount, bounded.ReportedErrorCount, observed.UnforwardableParameterReports));
                Assert.Equal((stored, stored * nodes), (observed.UnforwardableParameterMessages, observed.UnforwardableParameterDisplayNodes));
            }
        }

        // The work control: the wide parameter's shown prefix holds about a hundred of its 5,001 nodes.
        Assert.InRange(ShownGroupNodes(wide), 60, 120);
    }

    [Fact]
    public void ForwardedStructuralParameter_IsCutAroundSurrogatePairs_AsBoundNameCutsItsWholeText()
    {
        // A host-built list parameter whose leaf ends in a run of astral scalars, shifted unit by unit so that a pair lies
        // across the 512-unit cut, or across the end of the 513-unit prefix its written form is built to.
        const int bound = ExprNameRenderer.MaxRenderedNameLength;
        const string source = "G(u) = 0\nA(q) = G\n1";
        var placements = new HashSet<string>();
        for (var shift = 0; shift < 4; shift++)
        {
            var leaf = new string('m', bound - 7 + shift) + string.Concat(Enumerable.Repeat("😀", 8));
            var display = "[" + leaf + "]";
            var (diagnostics, observations) = ResolveHostBuilt(source, "G", [new ListValueParameterPattern([new CaptureParameterPattern(leaf)])]);
            var stored = Assert.Single(diagnostics);
            var (first, whole) = UnforwardableMessage(ShownName(display));
            Assert.Equal(Stored(StoredForm(whole, first.Length, DiagnosticCode.UnforwardableParameter, new SourceSpan(2, 8, 2, 9))), Stored(stored));
            Assert.Equal(2, observations.UnforwardableParameterDisplayNodes);
            placements.Add(char.IsHighSurrogate(display[bound - 1]) ? "across the cut" : char.IsHighSurrogate(display[bound]) ? "across the prefix's end" : "elsewhere");
        }

        Assert.Superset(new HashSet<string> { "across the cut", "across the prefix's end" }, placements);
    }

    [Fact]
    public void InferredStructuralParameters_AreShownBounded_AsTheirWholeTextsCut()
    {
        // Formula lifting forwards G's parameters to F, which has no output: ExplicitParametersRequireOutput names up to
        // three of them, each by its written form cut to the name bound — wide, deep, long, and 511 to 514 units.
        const string canonicalStart = "This algorithm takes the implicit parameter 'x' but does not define an output. ";
        var canonical = Assert.Single(Parse("G(x) = 0\nF = { a, b = G + 0, 1 }\ntrace(5)").Diagnostics).Message;
        Assert.StartsWith(canonicalStart, canonical, StringComparison.Ordinal);
        var rest = canonical[canonicalStart.Length..];

        static string Message(string source)
            => Assert.Single(Parse(source).Diagnostics, static d => d.Code == DiagnosticCode.ExplicitParametersRequireOutput).Message;

        var wide = $"[{Names("q", 5000)}]";
        var deep = new string('[', 280) + "r, s" + new string(']', 280);
        var longName = $"[*{new string('l', 3000)}]";
        foreach (var pattern in new[] { wide, deep, longName, $"[{new string('y', 509)}]", $"[{new string('y', 510)}]", $"[{new string('y', 511)}]", $"[{new string('y', 512)}]" })
        {
            Assert.Equal(
                $"This algorithm takes the implicit parameter '{ShownName(pattern)}' but does not define an output. {rest}",
                Message($"G({pattern}) = 0\nF = {{ a, b = G + 0, 1 }}\ntrace(5)"));
        }

        Assert.Equal(
            $"This algorithm takes the implicit parameters '{ShownName(wide)}', '{ShownName(deep)}', and 'z' but does not define an output. {rest}",
            Message($"G({wide}, {deep}, z) = 0\nF = {{ a, b = G + 0, 1 }}\ntrace(5)"));
        Assert.Equal(
            $"This algorithm takes the implicit parameters '{ShownName(wide)}', '{ShownName(deep)}', '{ShownName(longName)}', and 1 more but does not define an output. {rest}",
            Message($"G({wide}, {deep}, {longName}, z) = 0\nF = {{ a, b = G + 0, 1 }}\ntrace(5)"));
    }

    // The front end's allocation for a source making two equal reports with a two-diagnostic list, minus that with a
    // one-diagnostic list, which stores only the first: the cost of building ONE stored message (both runs warmed first).
    //
    // FreezeParameters rents int[16384], int[32768] and int[1024] to freeze 10,000 names. SummaryReference.KeyParts
    // also rents char[131072] four times for the lifted pattern. Trimming the pool on just one side of a pair
    // reproduced the displacement seen before the depth gate (217208 bytes) and after it (217368, 12280, 218328).
    // Other recorded differences include -193224 bytes and 475 KB on the lifted pattern.
    //
    // A fresh thread gives each window an empty thread-local pool cache. The shared pool can still supply an array,
    // and a trim between rents can force another allocation. Compare the large (pool, length) allocations in full
    // before accepting a pair. Smaller refills stay in the measurement within the workloads' existing allowance.
    //
    // On the 10,000-leaf lifted-pattern workload, changing JIT tiers between the windows displaced one difference by
    // about 800 KB (7de84650). Three comparable adjacent pairs are recorded in execution order and their median decides,
    // so a single displaced pair in either direction cannot decide whether the message meets its allocation bound.
    private long OneStoredMessage(string source)
    {
        (long Bytes, long[] PoolAllocations) Allocated(int limit)
        {
            var allocated = 0L;
            long[]? poolAllocations = null;
            DiagnosticBag? diagnostics = null;
            System.Runtime.ExceptionServices.ExceptionDispatchInfo? failure = null;
            var window = new Thread(() =>
            {
                try
                {
                    PooledArrayAllocations.Begin();
                    var before = GC.GetAllocatedBytesForCurrentThread();
                    (diagnostics, _) = Elaborate(source, limit);
                    allocated = GC.GetAllocatedBytesForCurrentThread() - before;
                    poolAllocations = PooledArrayAllocations.End();
                }
                catch (Exception exception)
                {
                    failure = System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(exception);
                }
            });
            window.Start();
            window.Join();
            failure?.Throw();
            Assert.Equal((2, Math.Min(2, limit)), (diagnostics!.ReportedCount, diagnostics.Count - (diagnostics.IsTruncated ? 1 : 0)));
            return (allocated, poolAllocations!);
        }

        using var pool = new PooledArrayAllocations();
        _ = Elaborate(source, 2);
        _ = Elaborate(source, 1);
        const int MaxPairs = 9;
        var differences = new List<long>(3);
        var windows = new List<string>();
        for (var pair = 0; pair < MaxPairs && differences.Count < 3; pair++)
        {
            var two = Allocated(2);
            var one = Allocated(1);
            var comparable = two.PoolAllocations.AsSpan().SequenceEqual(one.PoolAllocations);
            if (comparable)
                differences.Add(two.Bytes - one.Bytes);
            windows.Add(comparable
                ? $"{two.Bytes} - {one.Bytes}"
                : $"{two.Bytes} - {one.Bytes} excluded, the pool allocated [{PooledArrayAllocations.Show(two.PoolAllocations)}] "
                    + $"against [{PooledArrayAllocations.Show(one.PoolAllocations)}]");
        }
        output.WriteLine($"Stored-message windows, two-diagnostic minus one-diagnostic in execution order (bytes): {string.Join("; ", windows)}");
        Assert.True(differences.Count == 3,
            $"the shared ArrayPool allocated different arrays in the two windows of {windows.Count - differences.Count} of {windows.Count} pairs: {string.Join("; ", windows)}");
        output.WriteLine($"Stored-message allocation differences (bytes): {differences[0]}, {differences[1]}, {differences[2]}");
        differences.Sort();
        return differences[1];
    }

    /// <summary>
    /// The large arrays (<see cref="LargeLength"/> elements or more) a shared ArrayPool had to allocate (its
    /// BufferAllocated event) on the window thread between <see cref="Begin"/> and <see cref="End"/>, recorded by pool
    /// and length without allocating. The event is raised synchronously on the renting thread; other threads record nothing.
    /// </summary>
    private sealed class PooledArrayAllocations : EventListener
    {
        private const int LargeLength = 4096;
        [ThreadStatic] private static long[]? t_allocations;
        [ThreadStatic] private static int t_count;

        internal static void Begin()
        {
            t_allocations = new long[256];
            t_count = 0;
        }

        /// <summary>The complete multiset of large (pool, length) allocations, sorted after the window closes.</summary>
        internal static long[] End()
        {
            var allocations = t_allocations!;
            t_allocations = null;
            Assert.True(t_count <= allocations.Length,
                $"Recorded {allocations.Length} of {t_count} large pool allocations. The measurement is incomplete.");
            var recorded = allocations[..t_count];
            Array.Sort(recorded);
            return recorded;
        }

        internal static string Show(long[] allocations)
            => string.Join(", ", allocations.Select(static key => $"pool {key >> 32}: {(int)key}"));

        protected override void OnEventSourceCreated(EventSource eventSource)
        {
            if (eventSource.Name == "System.Buffers.ArrayPoolEventSource")
                EnableEvents(eventSource, EventLevel.Informational);
        }

        protected override void OnEventWritten(EventWrittenEventArgs eventData)
        {
            if (t_allocations is not { } allocations || eventData.EventName != "BufferAllocated" || eventData.Payload is not { Count: > 2 } payload)
                return;
            var length = (int)payload[1]!;
            if (length < LargeLength)
                return;
            if (t_count < allocations.Length)
                allocations[t_count] = ((long)(int)payload[2]! << 32) | (uint)length;
            t_count++;
        }
    }

    [Fact]
    public void StoredReportsOverWideDeclarations_AllocateTheirRetainedPrefix_NotTheWholeText()
    {
        // The regression control for the three payloads. Each workload makes two equal reports, and a one-diagnostic list
        // stores only the first, so a two-diagnostic list's extra allocation is the cost of building ONE stored message.
        // Built to its retained prefix that is a few kilobytes (measured on 2026-11-23 in the Debug test build: 27 KB for
        // the wrapper — the 4,097-unit builder, its string and the list's cut copy — 13 KB and 10 KB for the written
        // forms). Building the whole text first, as the former formatters did, costs at least two UTF-16 copies of it:
        // measured 1.27 MB for the 10,000-parameter wrapper, 829 KB for the 200,000-unit name and 290 KB for the
        // 10,000-leaf lifted pattern. Each bound leaves room for an ArrayPool refill (32 KB) and the ~8 KB allocation
        // quantum of the in-process counter, and stays well below the whole text.
        (string Payload, long Bytes, long Bound)[] measured =
        [
            ("the wrapper over 10,000 parameters", OneStoredMessage($"T({Names("p", 10_000)}) = 0\nB0* = T\nB1* = T\n1"), 128 * 1024),
            ("the written form of a 200,000-unit name",
                OneStoredMessage($"G([{new string('x', 200_000)}]) = 0\nA0(q) = G\nA1(q) = G\n1"), 96 * 1024),
            ("the written form of a 10,000-leaf lifted pattern",
                OneStoredMessage($"G([{Names("q", 10_000)}]) = 0\nF0 = {{ a, b = G + 0, 1 }}\nF1 = {{ a, b = G + 0, 1 }}\ntrace(5)"), 96 * 1024),
        ];
        var over = measured.Where(static m => m.Bytes >= m.Bound).Select(static m => $"{m.Payload}: {m.Bytes} bytes (bound {m.Bound})").ToList();
        Assert.True(over.Count == 0, "one stored message built its whole text: " + string.Join("; ", over));
    }

    // ── The wording of a stored UnforwardableParameter report ────────────────
    //
    // Whether the body binds an unforwardable structural parameter in ANOTHER FORM ("in that form") is decided from the
    // parameter's leaves in CapturesExpandingSharedNodesOnce order, a shared node's once, read only until one is bound
    // (ParameterPattern.AnyCaptureExpandingSharedNodesOnce) — never from a list of every leaf. A host items list that
    // counts its reads shows what ONE stored report reads, as the difference between capacities: the written form's
    // shown prefix, then the leaves its wording checked. A report the list drops reads nothing.

    /// <summary>A host pattern's items list that counts every item read through it.</summary>
    private sealed class CountedPatternItems(IReadOnlyList<ParameterPattern> items) : IReadOnlyList<ParameterPattern>
    {
        public long Reads { get; private set; }

        public int Count => items.Count;

        public ParameterPattern this[int index]
        {
            get
            {
                Reads++;
                return items[index];
            }
        }

        public IEnumerator<ParameterPattern> GetEnumerator()
        {
            for (var index = 0; index < items.Count; index++)
                yield return this[index];
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    // The UnforwardableParameter message of `A(q) = G` for G's parameter shown as `shown`, one of whose leaves A binds.
    private static (string First, string Text) InThatFormMessage(string shown)
    {
        var first = $"'G' is forwarded by name here, but the enclosing explicit parameter list does not declare its parameter '{shown}' in that form.";
        return (first, Lines(first, "Bare forwarding reuses an existing parameter only with the same pattern and never reshapes an argument. "
            + $"Declare the parameter '{shown}', or call 'G' with explicit arguments."));
    }

    /// <summary>Where the leaf the callers bind stands among the parameter's 10,000 leaves: first, second, middle, last, none.</summary>
    public static TheoryData<int> DecidingLeafPositions => new() { 0, 1, 4_999, 9_999, -1 };

    [Theory]
    [MemberData(nameof(DecidingLeafPositions))]
    public void StoredUnforwardableReport_ReadsTheParameterLeavesOnlyUntilOneDecidesItsWording(int decidingLeaf)
    {
        // G's one list parameter holds 10,000 leaves, and three callers that bind `q` — the leaf at `decidingLeaf`, or no
        // leaf at all — cannot forward it, so each of their three reports says whether its caller binds the parameter in
        // that form. A stored report reads the items its written form shows, then the leaves its wording checks up to the
        // one that decides; only a parameter none of whose leaves decides is read to its end. A dropped report reads
        // nothing, and every capacity keeps the whole list's prefix.
        const int leaves = 10_000;
        const int reports = 3;
        const string source = "G(u) = 0\nA0(q) = G\nA1(q) = G\nA2(q) = G\n1";
        var names = Enumerable.Range(0, leaves).Select(i => i == decidingLeaf ? "q" : $"a{i}").ToArray();
        var shown = ShownName($"[{string.Join(", ", names)}]");
        var (first, whole) = decidingLeaf >= 0 ? InThatFormMessage(shown) : UnforwardableMessage(shown);
        var checks = decidingLeaf >= 0 ? decidingLeaf + 1 : leaves;
        var displayNodes = ShownGroupNodes(names);
        // The written form reads every node it shows but the group itself; the wording reads each leaf it checks once.
        var readsPerStoredReport = displayNodes - 1 + checks;

        (DiagnosticBag Diagnostics, FrontEndTraversalObservations Observations, long Reads) Resolve(int limit)
        {
            var items = new CountedPatternItems([.. names.Select(static name => new CaptureParameterPattern(name))]);
            var (diagnostics, observations) = ResolveHostBuilt(source, "G", [new ListValueParameterPattern(items)], limit);
            return (diagnostics, observations, items.Reads);
        }

        var (full, unbounded, _) = Resolve(Limit);
        Assert.Equal(
            Enumerable.Range(2, reports).Select(row
                => Stored(StoredForm(whole, first.Length, DiagnosticCode.UnforwardableParameter, new SourceSpan(row, 9, row, 10)))),
            full.Select(Stored));
        Assert.Equal((reports, reports * checks, reports * displayNodes), (unbounded.UnforwardableParameterMessages,
            unbounded.UnforwardableParameterWordingChecks, unbounded.UnforwardableParameterDisplayNodes));

        var oneStored = Resolve(1).Reads;
        foreach (var limit in new[] { reports + 1, reports, reports - 1, 1 })
        {
            var (bounded, observed, reads) = Resolve(limit);
            AssertPrefixOfUnbounded(full, bounded, limit);
            var stored = Math.Min(limit, reports);
            Assert.Equal((reports, reports, stored), (bounded.ReportedCount, observed.UnforwardableParameterReports,
                observed.UnforwardableParameterMessages));
            Assert.Equal((stored * checks, stored * displayNodes), (observed.UnforwardableParameterWordingChecks,
                observed.UnforwardableParameterDisplayNodes));
            Assert.Equal((stored - 1) * readsPerStoredReport, reads - oneStored);
        }
    }

    [Fact]
    public void StoredUnforwardableReport_ChecksTheLeavesOfASharedSubtreeOnce()
    {
        // A host-built parameter may hold one structural node along several paths. Its wording checks the leaves in
        // CapturesExpandingSharedNodesOnce order: a node met again was checked whole where it was first met, and is
        // skipped. In [[a, b], [a, b], c] with one shared [a, b], a caller binding c decides at the third check, not the
        // fifth, and a caller binding none of them is told so after three.
        var shared = new ListValueParameterPattern([new CaptureParameterPattern("a"), new CaptureParameterPattern("b")]);
        ParameterPattern parameter = new ListValueParameterPattern([shared, shared, new CaptureParameterPattern("c")]);
        foreach (var (caller, checks) in new[] { ("a", 1), ("b", 2), ("c", 3), ("q", 3) })
        {
            var source = $"G(u) = 0\nA0({caller}) = G\nA1({caller}) = G\n1";
            var (first, whole) = caller == "q" ? UnforwardableMessage("[[a, b], [a, b], c]") : InThatFormMessage("[[a, b], [a, b], c]");
            var (full, unbounded) = ResolveHostBuilt(source, "G", [parameter]);
            Assert.Equal(
                Enumerable.Range(2, 2).Select(row
                    => Stored(StoredForm(whole, first.Length, DiagnosticCode.UnforwardableParameter, new SourceSpan(row, 9, row, 10)))),
                full.Select(Stored));
            Assert.Equal((2, 2 * checks), (unbounded.UnforwardableParameterMessages, unbounded.UnforwardableParameterWordingChecks));

            var (bounded, observed) = ResolveHostBuilt(source, "G", [parameter], limit: 1);
            AssertPrefixOfUnbounded(full, bounded, 1);
            Assert.Equal((2, 1, checks), (observed.UnforwardableParameterReports, observed.UnforwardableParameterMessages,
                observed.UnforwardableParameterWordingChecks));
        }

        // A diamond of 45 levels holds one node twice per level — 2^45 paths to its bottom (x, y) — and its items count
        // their reads against a budget a per-path walk would exhaust. Its wording checks x and y whether the caller binds
        // y or neither; deciding at y reads one item per level on the way down, and finding no leaf also reads each
        // level's second, already checked, item on the way back: exactly 45 reads more, never a path twice.
        const int levels = 45;
        static ParameterPattern Diamond(PatternReadBudget budget)
        {
            ParameterPattern pattern = new SequenceValueParameterPattern([new CaptureParameterPattern("x"), new CaptureParameterPattern("y")]);
            for (var level = 0; level < levels; level++)
                pattern = new ListValueParameterPattern(new BudgetedPatternItems<ParameterPattern>(pattern, pattern, budget));
            return pattern;
        }

        var diamondShown = ExprNameRenderer.BoundDisplayName(Diamond(new PatternReadBudget(1_000_000)));
        var storedReads = new Dictionary<string, long>();
        foreach (var caller in new[] { "y", "q" })
        {
            var source = $"G(u) = 0\nA0({caller}) = G\nA1({caller}) = G\n1";
            var (first, whole) = caller == "q" ? UnforwardableMessage(diamondShown) : InThatFormMessage(diamondShown);
            long Reads(int limit, out DiagnosticBag diagnostics, out FrontEndTraversalObservations observations)
            {
                var budget = new PatternReadBudget(1_000_000);
                (diagnostics, observations) = ResolveHostBuilt(source, "G", [Diamond(budget)], limit);
                return budget.Reads;
            }

            var two = Reads(2, out var full, out var unbounded);
            var one = Reads(1, out var bounded, out var observed);
            Assert.Equal(
                Enumerable.Range(2, 2).Select(row
                    => Stored(StoredForm(whole, first.Length, DiagnosticCode.UnforwardableParameter, new SourceSpan(row, 9, row, 10)))),
                full.Select(Stored));
            AssertPrefixOfUnbounded(full, bounded, 1);
            Assert.Equal((4, 2), (unbounded.UnforwardableParameterWordingChecks, observed.UnforwardableParameterWordingChecks));
            storedReads[caller] = two - one;
        }

        Assert.Equal(levels, storedReads["q"] - storedReads["y"]);
    }

    [Fact]
    public void StructuralWordingReplays_ForFamiliesSharingABranchBody_ReadTheParameterOnlyForTheFirstReport()
    {
        // One branch body `G` shared by three families (M4) under the head [z] or [x], where x is the first of the 10,000
        // leaves of G's list parameter: the body's first stored report reads the parameter, its written form's prefix and
        // the leaves its wording checks — one under [x], all of them under [z] — and every report re-issued for a further
        // family reuses that wording and reads none of the parameter, at every capacity.
        const int leaves = 10_000;
        string[] families = ["Left", "Middle", "Right"];
        var names = new[] { "x" }.Concat(Enumerable.Range(1, leaves - 1).Select(static i => $"a{i}")).ToArray();
        var shown = ShownName($"[{string.Join(", ", names)}]");
        var readsByHead = new Dictionary<string, long>();
        foreach (var head in new[] { "x", "z" })
        {
            var parsed = Parser.ParseSyntax($"G(u) = 0\nF([{head}]) = G\nF([1]) = 0\n1");
            Assert.False(parsed.HasErrors);
            var branches = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.SyntaxRoot.Properties, p => p.Name == "F").Value).Branches;
            var g = Assert.Single(parsed.SyntaxRoot.Properties, p => p.Name == "G");

            (DiagnosticBag Diagnostics, FrontEndTraversalObservations Observations, long Reads) Resolve(int limit)
            {
                var items = new CountedPatternItems([.. names.Select(static name => new CaptureParameterPattern(name))]);
                var host = g with { Value = Assert.IsType<Algorithm.User>(g.Value) with { ParameterPatterns = [new ListValueParameterPattern(items)] } };
                var root = new Algorithm.User(null, [], [],
                    [host, .. families.Select(family => new Property(family, new Algorithm.Conditional(null, [], branches)))],
                    new OutputBundle([new Expr.Num(1)]));
                var diagnostics = new DiagnosticBag(limit);
                var program = ParameterDetector.DetectPrevalidated(root, diagnostics: diagnostics);
                Assert.Equal(0, diagnostics.ReportedCount);
                var observations = new FrontEndTraversalObservations();
                var before = items.Reads;
                _ = ImplicitArgumentResolver.ResolvePrevalidated(program, observations, diagnostics);
                return (diagnostics, observations, items.Reads - before);
            }

            var checks = head == "x" ? 1 : leaves;
            var (full, unbounded, reads) = Resolve(Limit);
            // Each of the two branch bodies is rewritten once for the three families that share it.
            Assert.Equal(branches.Count, unbounded.ResolverBranchBodyRegionExpansions);
            Assert.Equal(
                families.Select(family => head == "x"
                    ? $"'G' is forwarded by name here, but the pattern of conditional branch '{family}' does not bind its parameter '{shown}' in that form."
                    : $"'G' is forwarded by name here, but its parameter '{shown}' is not bound by the pattern of conditional branch '{family}'."),
                full.Select(d => d.Message.Split(Environment.NewLine)[0]));
            Assert.Equal((3, 3, checks), (unbounded.UnforwardableParameterReports, unbounded.UnforwardableParameterMessages,
                unbounded.UnforwardableParameterWordingChecks));

            foreach (var limit in new[] { 4, 3, 2, 1 })
            {
                var (bounded, observed, boundedReads) = Resolve(limit);
                AssertPrefixOfUnbounded(full, bounded, limit);
                Assert.Equal((3, Math.Min(limit, 3), checks), (observed.UnforwardableParameterReports,
                    observed.UnforwardableParameterMessages, observed.UnforwardableParameterWordingChecks));
                Assert.Equal(reads, boundedReads);
            }

            readsByHead[head] = reads;
        }

        // The same written form is read under both heads; the wording alone reads one leaf under [x] and every leaf under [z].
        Assert.Equal(leaves - 1, readsByHead["z"] - readsByHead["x"]);
    }

    [Fact]
    public void StoredUnforwardableReports_DecideTheirWordingWithoutListingEveryLeaf()
    {
        // The allocation control for the wording. Each workload makes two equal reports about a 10,000-leaf list parameter,
        // and a one-diagnostic list stores only the first, so a two-diagnostic list's extra allocation is the cost of ONE
        // stored message: its bounded written form and its text (measured on 2026-11-24 in the Debug build: 11–12 KB with
        // a leaf bound, 16 KB with none, whose wording is longer). Deciding the wording from a list of the parameter's
        // leaves, as the former check did, also cost the list and the stack that filled it, whichever leaf decided:
        // 536–543 KB per stored message in the Debug test build (the check alone 525 KB in Release, 4.2 MB at 100,000
        // leaves). A group of leaves is now walked in place. The bound leaves room for an ArrayPool refill (32 KB) and the
        // ~8 KB allocation quantum of the in-process counter, and stays far below the list.
        const int leaves = 10_000;
        (string Payload, long Bytes)[] measured =
        [
            ("the first leaf bound by the caller", OneStoredMessage($"G([q, {Names("a", leaves - 1)}]) = 0\nA0(q) = G\nA1(q) = G\n1")),
            ("the last leaf bound by the caller", OneStoredMessage($"G([{Names("a", leaves - 1)}, q]) = 0\nA0(q) = G\nA1(q) = G\n1")),
            ("no leaf bound", OneStoredMessage($"G([{Names("a", leaves)}]) = 0\nA0(q) = G\nA1(q) = G\n1")),
            ("the first leaf bound by an enclosing parameter",
                OneStoredMessage($"G([q, {Names("a", leaves - 1)}]) = 0\nOuter(q) = {{\n    A0(r) = G\n    A1(r) = G\n    1\n}}\n1")),
            ("the first leaf of a nested group bound by the caller",
                OneStoredMessage($"G([(q, {Names("a", leaves - 1)})]) = 0\nA0(q) = G\nA1(q) = G\n1")),
        ];
        const long bound = 96 * 1024;
        var over = measured.Where(static m => m.Bytes >= bound).Select(static m => $"{m.Payload}: {m.Bytes} bytes (bound {bound})").ToList();
        Assert.True(over.Count == 0, "one stored message listed the parameter's leaves: " + string.Join("; ", over));
    }
}
