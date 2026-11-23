using System.Text;
using KatLang.Semantics;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// Position lookup — <see cref="SemanticModel.FindResolutionAt"/>, and through it
/// <see cref="SemanticModel.FindPropertyAt"/>, the hover and go-to-definition query — reads the
/// model's resolution listing in place. The builder lists sites by start, then end; when the
/// sites' starts AND ends both never decrease (no site strictly contains another, as in parsed
/// documents), the query binary-searches that listing instead of scanning every site. These
/// tests pin that the answer is EXACTLY the former linear first-containing-site result at every
/// position: for parsed documents with Unicode text, nested scopes, shadowing, aliases, open
/// providers (deduplicated, ambiguous, dotted, module-backed, missing) and recovery trees; for
/// host-constructed listings with tied, adjacent, zero-width and multi-line sites; and for nested
/// or unordered listings, which keep the scan. They also pin that a query allocates nothing and
/// that the number of sites it inspects grows at most logarithmically.
/// </summary>
public class SemanticModelPositionLookupTests(ITestOutputHelper output)
{
    /// <summary>Unicode identifiers, and string literals with surrogate pairs that shift the UTF-16 columns of later names.</summary>
    private const string UnicodeDocument =
        "Größe = 2\n"
        + "Fläche(w, h) = w * h + Größe\n"
        + "Paar = ['😀😀', Größe, 'é𝐀']\n"
        + "Скорость(x) = x + λ + count(Paar)\n"
        + "λ = Größe + Fläche(Größe, 3)\n"
        + "Скорость(1)";

    /// <summary>
    /// Nested scopes with a shadowing local, an alias chain, a root open of one provider under two
    /// spellings (deduplicated), a dotted open through the alias chain, two providers whose shared
    /// member stays unwritten (ambiguous), a clause family and implicit parameters.
    /// </summary>
    private const string ScopesDocument =
        "open Lib, Alias\n"
        + "Lib = {\n"
        + "    public Größe = 1\n"
        + "    public Fläche(w, h) = w * h + Größe\n"
        + "    public Inner = {\n"
        + "        public Tief = Größe + 1\n"
        + "    }\n"
        + "}\n"
        + "Alias = Lib\n"
        + "Chain = Alias\n"
        + "P1 = {\n"
        + "    public Doppelt = 1\n"
        + "}\n"
        + "P2 = {\n"
        + "    public Doppelt = 2\n"
        + "}\n"
        + "Use = {\n"
        + "    open Chain.Inner, P1, P2\n"
        + "    Local = Tief + Fläche(2, 3)\n"
        + "    Nest = {\n"
        + "        Größe = 5\n"
        + "        Deep = {\n"
        + "            V = Local + Größe\n"
        + "            V\n"
        + "        }\n"
        + "        Deep + 1\n"
        + "    }\n"
        + "    Nest + Chain.Inner.Tief + Alias.Größe\n"
        + "}\n"
        + "Clause(0) = 1\n"
        + "Clause(n) = n * Clause(n - 1)\n"
        + "Imp = a + b\n"
        + "Use + Clause(3) + Imp(1, 2) + Größe";

    private const string LibUrl = "https://katlang.org/lib.kat";
    private const string OtherUrl = "https://katlang.org/other.kat";

    private static readonly IReadOnlyDictionary<string, string> Modules = new Dictionary<string, string>
    {
        [LibUrl] = "public Größe = 2\npublic Fläche(w, h) = w * h\n",
        [OtherUrl] = "public Λ = {\n    public Tief = 3\n}\npublic Wert = 4\n",
    };

    /// <summary>A root module open and a module property opened in a nested scope: module-provided targets are locationless.</summary>
    private const string ModuleDocument =
        "open 'https://katlang.org/lib.kat'\n"
        + "M = load('https://katlang.org/other.kat')\n"
        + "Use = {\n"
        + "    open M\n"
        + "    Fläche(2, 3) + Größe + Wert + Λ.Tief\n"
        + "}\n"
        + "Direct = M.Wert + Größe + M.Λ.Tief\n"
        + "Use + Direct";

    /// <summary>Recovery trees: unclosed groups and blocks, and an open of an undeclared name.</summary>
    private const string RecoveryDocument =
        "A = (1 +\n"
        + "B = A + Größe\n"
        + "C = { D = B +\n"
        + "Ω = { open Missing\n"
        + "  Ω + ";

    /// <summary>A module the parse could not load (no downloader): its names classify as deferred.</summary>
    private const string MissingModuleDocument =
        "open 'https://katlang.org/lib.kat'\n"
        + "X = Größe + Fläche(1, 2)\n"
        + "M = load('https://katlang.org/other.kat')\n"
        + "Y = M.Wert + Unklar\n"
        + "X + Y";

    public static TheoryData<string> ParsedDocuments => new()
    {
        "unicode",
        "scopes",
        "module",
        "recovery",
        "missing-module",
        "generated",
    };

    private static async Task<(string Source, SemanticModel Model)> ModelOf(string name)
    {
        switch (name)
        {
            case "unicode":
                return (UnicodeDocument, SemanticModelBuilder.Build(SourceProvenance.ParseValid(UnicodeDocument).Parsed));
            case "scopes":
                return (ScopesDocument, SemanticModelBuilder.Build(SourceProvenance.ParseValid(ScopesDocument).Parsed));
            case "module":
                var loaded = await SourceProvenance.ParseValidAsync(ModuleDocument, Downloading());
                return (ModuleDocument, SemanticModelBuilder.Build(loaded.Parsed));
            case "recovery":
                var recovered = SourceProvenance.ParseAllowingDiagnostics(RecoveryDocument);
                Assert.True(recovered.HasFrontEndErrors);
                return (RecoveryDocument, SemanticModelBuilder.Build(recovered.Parsed));
            case "missing-module":
                var missing = SourceProvenance.ParseAllowingDiagnostics(MissingModuleDocument);
                Assert.Contains(missing.Diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.LoadElaborationUnavailable);
                return (MissingModuleDocument, SemanticModelBuilder.Build(missing.Parsed));
            case "generated":
                var generated = GeneratedDocument(blocks: 6);
                return (generated, SemanticModelBuilder.Build(SourceProvenance.ParseValid(generated).Parsed));
            default:
                throw new ArgumentOutOfRangeException(nameof(name), name, null);
        }
    }

    private static RunOptions Downloading() => new()
    {
        DownloadCode = (url, _) => Modules.TryGetValue(url, out var source)
            ? ValueTask.FromResult(source)
            : throw new InvalidOperationException($"404 {url}"),
    };

    /// <summary>
    /// A representative editor document of <paramref name="blocks"/> repetitions: a library with
    /// public and private members and a nested public block, an alias chain to it, a scope that
    /// opens it and reads members through the aliases, Unicode names, a clause family, implicit
    /// parameters, three nested property levels and a pipeline.
    /// </summary>
    internal static string GeneratedDocument(int blocks)
    {
        var text = new StringBuilder();
        for (var i = 0; i < blocks; i++)
        {
            text.Append($"Lib{i} = {{\n");
            text.Append($"    public Größe{i} = {i}\n");
            text.Append($"    public Fläche{i}(w, h) = w * h + Größe{i}\n");
            text.Append($"    Helper{i} = Größe{i} * 2\n");
            text.Append($"    public Inner{i} = {{\n        public Deep{i} = Helper{i} + 1\n    }}\n");
            text.Append("}\n");
            text.Append($"Alias{i} = Lib{i}\n");
            text.Append($"Chain{i} = Alias{i}\n");
            text.Append($"Use{i} = {{\n");
            text.Append($"    open Lib{i}\n");
            text.Append($"    Local{i} = Fläche{i}(2, 3) + Größe{i}\n");
            text.Append($"    Shadow = Local{i} * 2\n");
            text.Append($"    Local{i} + Chain{i}.Helper{i} + Alias{i}.Inner{i}.Deep{i} + Shadow\n");
            text.Append("}\n");
            text.Append($"Скорость{i}(x) = x + Use{i} + λ{i}\n");
            text.Append($"λ{i} = Lib{i}.Größe{i} * Math.Pi + sin(1)\n");
            text.Append($"Clause{i}(0) = 1\n");
            text.Append($"Clause{i}(n) = n * 2\n");
            text.Append($"Imp{i} = a + b * Скорость{i}(1)\n");
            text.Append($"Nest{i} = {{\n    L1 = {{\n        L2 = {{\n            V = Imp{i}(1, 2) + Clause{i}(3)\n            V\n        }}\n        L2 + 1\n    }}\n    L1\n}}\n");
            text.Append($"Rows{i} = range(1, 3).map(Скорость{i}).sum + Nest{i}\n");
        }

        return text.Append("Rows0").ToString();
    }

    /// <summary>The former query: the first listed site whose half-open span contains the position.</summary>
    private static IdentifierResolution? LinearReference(SemanticModel model, SourcePosition position)
        => model.IdentifierResolutions.FirstOrDefault(resolution => resolution.Occurrence.Span.Contains(position));

    /// <summary>Every column of every line (UTF-16), two columns past each line end, and the line after the last one.</summary>
    private static IEnumerable<SourcePosition> EveryPosition(string source)
    {
        var lines = source.Split('\n');
        for (var line = 0; line <= lines.Length; line++)
        {
            var width = line < lines.Length ? lines[line].Length : 0;
            for (var column = 1; column <= width + 2; column++)
                yield return new SourcePosition(line + 1, column);
        }
    }

    /// <summary>Asserts the query returns the reference's resolution OBJECT (and property) at each position; returns the hit count.</summary>
    private static int AssertMatchesTheLinearReference(SemanticModel model, IEnumerable<SourcePosition> positions)
    {
        var hits = 0;
        foreach (var position in positions)
        {
            var expected = LinearReference(model, position);
            var actual = model.FindResolutionAt(position);
            Assert.True(
                ReferenceEquals(expected, actual),
                $"FindResolutionAt({position}) returned {actual?.Occurrence.ToString() ?? "null"}; the first containing site is {expected?.Occurrence.ToString() ?? "none"}.");
            Assert.Same(expected?.ResolvedProperty, model.FindPropertyAt(position));
            if (expected is not null)
                hits++;
        }

        return hits;
    }

    private static SourcePosition PositionOf(string source, int line, string word, int occurrence = 1)
    {
        var text = source.Split('\n')[line - 1];
        var index = -1;
        for (var i = 0; i < occurrence; i++)
        {
            index = text.IndexOf(word, index + 1, StringComparison.Ordinal);
            Assert.True(index >= 0, $"'{word}' #{occurrence} is not on line {line}: {text}");
        }

        return new SourcePosition(line, index + 1);
    }

    [Theory]
    [MemberData(nameof(ParsedDocuments))]
    public async Task ParsedDocument_EveryPosition_MatchesTheLinearScan(string name)
    {
        var (source, model) = await ModelOf(name);

        // A parsed document's sites never nest, so the query takes the binary search.
        Assert.True(model.ResolutionSitesAreMonotone, $"{name}: the parsed listing should be ordered by start and end");
        var hits = AssertMatchesTheLinearReference(model, EveryPosition(source));

        // Every site is a written name on one line, found at its first and last character.
        foreach (var resolution in model.IdentifierResolutions)
        {
            var span = resolution.Occurrence.Span;
            Assert.True(span.Start < span.End && span.Start.Line == span.End.Line, $"{name}: site {resolution.Occurrence}");
            Assert.Equal(span, model.FindResolutionAt(span.Start)?.Occurrence.Span);
            Assert.Equal(span, model.FindResolutionAt(new SourcePosition(span.End.Line, span.End.Column - 1))?.Occurrence.Span);
        }

        Assert.True(hits > model.IdentifierResolutions.Count, $"{name}: {hits} hits for {model.IdentifierResolutions.Count} sites");
    }

    [Fact]
    public void Definition_KeepsShadowingAliasAndOpenTargets()
    {
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(ScopesDocument).Parsed);
        DeclarationOccurrence DefinitionAt(SourcePosition position)
            => Assert.IsType<DeclarationOccurrence>(model.FindResolutionAt(position)?.ResolvedDeclaration);

        var libGröße = PositionOf(ScopesDocument, 3, "Größe");
        var shadowGröße = PositionOf(ScopesDocument, 21, "Größe");
        var tief = PositionOf(ScopesDocument, 6, "Tief");

        // The nested local shadows the opened library member; a qualified read through the alias
        // chain and the root read through the deduplicated open reach the library's declaration.
        Assert.Equal(shadowGröße, DefinitionAt(PositionOf(ScopesDocument, 23, "Größe")).Span.Start);
        Assert.Equal(libGröße, DefinitionAt(PositionOf(ScopesDocument, 28, "Größe")).Span.Start);
        Assert.Equal(libGröße, DefinitionAt(PositionOf(ScopesDocument, 33, "Größe")).Span.Start);
        // The dotted open through the alias chain supplies `Tief`; so does the qualified read.
        Assert.Equal(tief, DefinitionAt(PositionOf(ScopesDocument, 19, "Tief")).Span.Start);
        Assert.Equal(tief, DefinitionAt(PositionOf(ScopesDocument, 28, "Tief")).Span.Start);
        // Hover reads the property of the same declaration identity.
        var property = Assert.IsType<PropertyInfo>(model.FindPropertyAt(PositionOf(ScopesDocument, 23, "Größe")));
        Assert.Same(DefinitionAt(PositionOf(ScopesDocument, 23, "Größe")), property.Declaration);
    }

    [Fact]
    public async Task Definition_OfAModuleProvidedMember_IsLocationless()
    {
        var model = SemanticModelBuilder.Build((await SourceProvenance.ParseValidAsync(ModuleDocument, Downloading())).Parsed);

        foreach (var (line, word) in new[] { (5, "Fläche"), (5, "Größe"), (5, "Wert"), (7, "Wert"), (7, "Tief") })
        {
            var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(PositionOf(ModuleDocument, line, word)));
            Assert.Equal(word, resolution.Occurrence.Name);
            Assert.Null(resolution.ResolvedDeclaration);
            Assert.NotNull(resolution.ResolvedProperty);
            Assert.Same(resolution.ResolvedProperty, model.FindPropertyAt(PositionOf(ModuleDocument, line, word)));
        }
    }

    [Fact]
    public void Unicode_ColumnsAreUtf16CodeUnits()
    {
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(UnicodeDocument).Parsed);

        // `Paar = ['😀😀', Größe, 'é𝐀']`: each emoji is two UTF-16 code units, so `Größe` starts at column 17.
        var größe = new SourcePosition(3, 17);
        Assert.Equal(größe, PositionOf(UnicodeDocument, 3, "Größe"));
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(größe));
        Assert.Equal("Größe", resolution.Occurrence.Name);
        Assert.Equal(new SourcePosition(3, 22), resolution.Occurrence.Span.End);
        Assert.Same(resolution, model.FindResolutionAt(new SourcePosition(3, 21)));
        Assert.Null(model.FindResolutionAt(new SourcePosition(3, 22)));
        // Inside the string literals (columns 9-14 and 24-28) there is no site.
        foreach (var column in Enumerable.Range(9, 6).Concat(Enumerable.Range(24, 5)))
            Assert.Null(model.FindResolutionAt(new SourcePosition(3, column)));
    }

    // ── Host-constructed listings: exact on both paths ─────────────────────────────────────

    private static IdentifierResolution Site(SourceSpan span, string name = "x")
        => new(new IdentifierOccurrence(name, span, OccurrenceKind.ResolveReference), IdentifierClassification.Unresolved, null, null);

    private static SemanticModel ModelWith(params IdentifierResolution[] resolutions)
        => new(
            SourceProvenance.ParseValid("1").Root,
            [],
            [],
            resolutions,
            [],
            new Dictionary<DeclarationOccurrence, PropertyInfo>(ReferenceEqualityComparer.Instance));

    private static IEnumerable<SourcePosition> Grid(int lines, int columns)
    {
        for (var line = 1; line <= lines; line++)
        {
            for (var column = 1; column <= columns; column++)
                yield return new SourcePosition(line, column);
        }
    }

    [Fact]
    public void TiedSites_TheFirstListedSiteWins()
    {
        var span = new SourceSpan(1, 3, 1, 5);
        var first = Site(span, "Z");
        var second = Site(span, "E");
        var model = ModelWith(Site(new SourceSpan(1, 1, 1, 2)), first, second, Site(new SourceSpan(1, 5, 1, 6)));

        Assert.True(model.ResolutionSitesAreMonotone);
        Assert.Same(first, model.FindResolutionAt(new SourcePosition(1, 3)));
        Assert.Same(first, model.FindResolutionAt(new SourcePosition(1, 4)));
        AssertMatchesTheLinearReference(model, Grid(2, 8));
    }

    [Fact]
    public void AdjacentAndZeroWidthSites_FollowTheHalfOpenRule()
    {
        var left = Site(new SourceSpan(1, 1, 1, 3));
        var empty = Site(new SourceSpan(1, 3, 1, 3));
        var right = Site(new SourceSpan(1, 3, 1, 5));
        var multiLine = Site(new SourceSpan(1, 7, 3, 2));
        var model = ModelWith(left, empty, right, multiLine);

        Assert.True(model.ResolutionSitesAreMonotone);
        Assert.Same(left, model.FindResolutionAt(new SourcePosition(1, 2)));
        // A site's exclusive end belongs to the next site; a zero-width site contains nothing.
        Assert.Same(right, model.FindResolutionAt(new SourcePosition(1, 3)));
        Assert.Null(model.FindResolutionAt(new SourcePosition(1, 5)));
        Assert.Same(multiLine, model.FindResolutionAt(new SourcePosition(2, 40)));
        Assert.Null(model.FindResolutionAt(new SourcePosition(3, 2)));
        AssertMatchesTheLinearReference(model, Grid(4, 10));
    }

    [Fact]
    public void NestedSites_KeepTheScanAndItsFirstContainingSite()
    {
        var outer = Site(new SourceSpan(1, 1, 1, 10), "Outer");
        var inner = Site(new SourceSpan(1, 3, 1, 5), "Inner");
        var model = ModelWith(outer, inner, Site(new SourceSpan(1, 12, 1, 13)));

        Assert.False(model.ResolutionSitesAreMonotone);
        Assert.Same(outer, model.FindResolutionAt(new SourcePosition(1, 4)));
        Assert.Same(outer, model.FindResolutionAt(new SourcePosition(1, 9)));
        Assert.Null(model.FindResolutionAt(new SourcePosition(1, 10)));
        AssertMatchesTheLinearReference(model, Grid(2, 14));
    }

    [Fact]
    public void UnorderedListing_KeepsTheScanAndItsListingOrder()
    {
        var late = Site(new SourceSpan(2, 1, 2, 3), "Late");
        var early = Site(new SourceSpan(1, 1, 1, 3), "Early");
        var overlapping = Site(new SourceSpan(1, 2, 1, 4), "Overlapping");
        var model = ModelWith(late, early, overlapping);

        Assert.False(model.ResolutionSitesAreMonotone);
        Assert.Same(early, model.FindResolutionAt(new SourcePosition(1, 2)));
        Assert.Same(overlapping, model.FindResolutionAt(new SourcePosition(1, 3)));
        Assert.Same(late, model.FindResolutionAt(new SourcePosition(2, 1)));
        AssertMatchesTheLinearReference(model, Grid(3, 6));
    }

    [Fact]
    public void EmptyListing_FindsNothing()
    {
        var model = ModelWith();
        Assert.True(model.ResolutionSitesAreMonotone);
        Assert.Null(model.FindResolutionAt(new SourcePosition(1, 1)));
        Assert.Null(model.FindPropertyAt(new SourcePosition(1, 1)));
    }

    /// <summary>
    /// Seeded random listings — tied, adjacent, zero-width, multi-line, nested and partially
    /// overlapping sites, the default span, in the builder's (start, end) order or shuffled — agree
    /// with the scan at every grid position, on both paths.
    /// </summary>
    [Fact]
    public void RandomListings_MatchTheLinearScan_OnBothPaths()
    {
        var random = new Random(20261117);
        var monotone = 0;
        var scanned = 0;
        for (var round = 0; round < 1_500; round++)
        {
            var sites = new List<IdentifierResolution>();
            var count = random.Next(0, 13);
            for (var i = 0; i < count; i++)
                sites.Add(Site(RandomSpan(random), $"s{i}"));

            var listing = random.Next(3) == 0
                ? sites.OrderBy(_ => random.Next()).ToArray()
                : sites.OrderBy(site => site.Occurrence.Span.Start).ThenBy(site => site.Occurrence.Span.End).ToArray();
            var model = ModelWith(listing);
            if (model.ResolutionSitesAreMonotone)
                monotone++;
            else
                scanned++;
            AssertMatchesTheLinearReference(model, Grid(8, 11));
        }

        output.WriteLine($"binary-searched listings: {monotone}, scanned listings: {scanned}");
        Assert.True(monotone > 300 && scanned > 300, $"both paths must be exercised ({monotone} / {scanned})");
    }

    private static SourceSpan RandomSpan(Random random)
    {
        if (random.Next(40) == 0)
            return default;

        var startLine = random.Next(1, 7);
        var startColumn = random.Next(1, 9);
        if (random.Next(4) == 0)
            return new SourceSpan(startLine, startColumn, startLine, startColumn);
        if (random.Next(5) == 0)
            return new SourceSpan(startLine, startColumn, startLine + random.Next(1, 3), random.Next(1, 9));
        return new SourceSpan(startLine, startColumn, startLine, startColumn + random.Next(1, 5));
    }

    // ── Cost ─────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// Hover and go-to-definition allocate nothing: the former query allocated a closure, a
    /// delegate and an enumerator per call (112 bytes).
    /// </summary>
    [Fact]
    public void PositionQueries_AllocateNothing_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var source = GeneratedDocument(blocks: 4);
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        var positions = model.IdentifierResolutions
            .SelectMany(resolution => new[] { resolution.Occurrence.Span.Start, resolution.Occurrence.Span.End })
            .Concat(Enumerable.Range(1, source.Count(c => c == '\n') + 2).Select(line => new SourcePosition(line, 1)))
            .ToArray();
        int Sweep()
        {
            var found = 0;
            foreach (var position in positions)
            {
                if (model.FindResolutionAt(position) is not null)
                    found++;
                if (model.FindPropertyAt(position) is not null)
                    found++;
            }

            return found;
        }

        var expected = Sweep();
        var before = GC.GetAllocatedBytesForCurrentThread();
        var found = Sweep();
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(expected, found);
        Assert.True(found > model.IdentifierResolutions.Count);
        Assert.Equal(0, allocated);
        GcIsolatedAllocation.Complete();
    }

    /// <summary>
    /// A position query does not scan the listing. The test counts each query's work, not its
    /// time. <see cref="SemanticModel.FindResolutionAtCounted"/> runs
    /// <see cref="SemanticModel.FindResolutionAt"/>'s own search and reports the sites it
    /// inspected: the sites its binary search compared with the position, or the sites a scan
    /// visited. The count is the same on every run. The bounds are at least one probe and at most
    /// ⌊log₂ R⌋ + 1 per query for R sites, the same site instance the public query returns, and
    /// twice the small total for the large listing (64 times the sites). The small listing is
    /// checked first, so a query that scans the sites (up to 512 probes there) fails at once. The
    /// public query itself must also allocate nothing beyond the counter quantum (16 KiB for 8,192
    /// queries). The former LINQ query allocated a closure, a delegate and an enumerator per call
    /// (112 bytes, 917,504 for 8,192 queries), even where it bypassed the counted search. Like the
    /// probe count, this bound does not depend on elapsed time. A scan of the site array written
    /// into the public wrapper would allocate nothing and escape the probes, so the test first
    /// requires the wrapper to be exactly the call of the core the probes measure
    /// (<see cref="MeasuredPositionQueries"/>).
    /// </summary>
    [Fact]
    public void PositionQueryCost_DoesNotGrowWithTheSiteCount()
    {
        // Probes can only measure the algorithm the public entry point delegates to. A private
        // array scan in the wrapper returns the same results and also allocates zero bytes.
        MeasuredPositionQueries.RequireDelegation(
            nameof(SemanticModel.FindResolutionAt), nameof(SemanticModel.FindResolutionAtCounted), "FindResolution");

        static (SemanticModel Model, SourcePosition[] Queries) Listing(int sites)
        {
            var listing = new IdentifierResolution[sites];
            for (var i = 0; i < sites; i++)
                listing[i] = Site(new SourceSpan(i + 1, 3, i + 1, 6), "n");
            var model = ModelWith(listing);
            Assert.True(model.ResolutionSitesAreMonotone);
            // Hits and misses over the whole listing, in document order as an editor sweep issues them.
            var queries = new SourcePosition[8_192];
            for (var q = 0; q < queries.Length; q++)
                queries[q] = new SourcePosition(1 + (int)((long)q * sites / queries.Length), q % 2 == 0 ? 4 : 1);
            return (model, queries);
        }

        // The binary search halves the R sites with each probe: at most ⌊log₂ R⌋ + 1 probes. A query
        // that inspects nothing has a disconnected count, so at least one probe is required.
        static (long Total, int Fewest, int Most) Probes(SemanticModel model, SourcePosition[] queries)
        {
            var limit = System.Numerics.BitOperations.Log2((uint)model.IdentifierResolutions.Count) + 1;
            var (total, fewest, most, found) = (0L, int.MaxValue, 0, 0);
            foreach (var query in queries)
            {
                var resolution = model.FindResolutionAtCounted(query, out var probes);
                Assert.Same(model.FindResolutionAt(query), resolution);
                Assert.InRange(probes, 1, limit);
                if (resolution is not null)
                    found++;
                total += probes;
                fewest = Math.Min(fewest, probes);
                most = Math.Max(most, probes);
            }

            Assert.Equal(queries.Length / 2, found);
            return (total, fewest, most);
        }

        static long AllocatedBytes(SemanticModel model, SourcePosition[] queries)
        {
            var found = 0;
            var before = GC.GetAllocatedBytesForCurrentThread();
            foreach (var query in queries)
            {
                if (model.FindResolutionAt(query) is not null)
                    found++;
            }

            var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.Equal(queries.Length / 2, found);
            return bytes;
        }

        var (small, smallQueries) = Listing(512);
        var smallProbes = Probes(small, smallQueries);
        var (large, largeQueries) = Listing(32_768);
        var largeProbes = Probes(large, largeQueries);
        var smallBytes = AllocatedBytes(small, smallQueries);
        var largeBytes = AllocatedBytes(large, largeQueries);
        output.WriteLine(
            $"8,192 queries: {smallProbes.Total:N0} -> {largeProbes.Total:N0} probes ({(double)largeProbes.Total / smallProbes.Total:F2} times; "
            + $"{smallProbes.Fewest}-{smallProbes.Most} -> {largeProbes.Fewest}-{largeProbes.Most} per query) over 512 -> 32,768 sites, "
            + $"{smallBytes:N0} -> {largeBytes:N0} B");
        Assert.True(
            largeProbes.Total <= 2 * smallProbes.Total,
            $"64 times the sites made the queries take {(double)largeProbes.Total / smallProbes.Total:F1} times the probes ({smallProbes.Total:N0} -> {largeProbes.Total:N0}).");

        // The public query allocates nothing. The former LINQ query allocated 112 bytes per call
        // (917,504 for 8,192 queries) even outside the counted search. The bound is the ~8 KB counter
        // quantum of a background collection, twice.
        Assert.True(smallBytes <= 16_384, $"8,192 queries over 512 sites allocated {smallBytes:N0} B.");
        Assert.True(largeBytes <= 16_384, $"8,192 queries over 32,768 sites allocated {largeBytes:N0} B.");
    }
}
