using System.Diagnostics;
using System.Numerics;
using System.Text;
using KatLang.Semantics;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// Name lookup — <see cref="SemanticModel.FindResolutions"/> and <see cref="SemanticModel.FindDeclarations"/>,
/// the find-references, rename and highlight queries — reads a name index that the model builds on
/// a query's first call, instead of filtering every site on every call. These tests pin that each
/// answer is EXACTLY the former filter's: the same instances, in listing order, with ordinal name
/// comparison. A call that finds anything returns a new read-only list; a call that finds nothing
/// returns the shared empty one. Parsed documents (repeated names and shadowing, Unicode, opens and
/// modules, deferred and missing modules, recovery trees) and host-constructed listings (repeated
/// instances, unordered spans, null names, ordinal near-misses, random listings) are compared with
/// the filter, which is kept here verbatim as the oracle. The comparison also runs through an index
/// whose hash is the name's length, so that names collide. A listing with a null entry keeps the
/// scan, which throws as it always did. The tests also pin lazy publication, 8 bytes per indexed
/// item, the comparisons that locate each query's hash run, and that a warmed query allocates
/// only its result. Implementation-only optimization: no editor-visible result changes.
/// </summary>
public class SemanticModelNameLookupTests(ITestOutputHelper output)
{
    private static readonly Algorithm HostRoot = SourceProvenance.ParseValid("1").Root;

    /// <summary>The former <see cref="SemanticModel.FindResolutions"/>, verbatim.</summary>
    private static IdentifierResolution[] ResolutionsByFilter(SemanticModel model, string name)
        => model.IdentifierResolutions.Where(resolution => resolution.Occurrence.Name == name).ToArray();

    /// <summary>The former <see cref="SemanticModel.FindDeclarations"/>, verbatim.</summary>
    private static DeclarationOccurrence[] DeclarationsByFilter(SemanticModel model, string name)
        => model.Declarations.Where(declaration => declaration.Name == name).ToArray();

    /// <summary>
    /// The filter's instances in its order, in a read-only list of their own. The former query
    /// wrapped a new array in a new view, and an empty array in the shared empty view.
    /// </summary>
    private static void AssertSameItems<T>(T[] expected, IReadOnlyList<T>? actual, string context)
        where T : class
    {
        Assert.NotNull(actual);
        Assert.True(expected.Length == actual!.Count, $"{context}: {actual.Count} results; the filter finds {expected.Length}");
        for (var i = 0; i < expected.Length; i++)
            Assert.True(ReferenceEquals(expected[i], actual[i]), $"{context}: result {i} is {actual[i]}; the filter's is {expected[i]}");
        if (expected.Length == 0)
            Assert.Same(SafeReadOnlyCollection<T>.Empty, actual);
        else
            Assert.IsType<SafeReadOnlyCollection<T>>(actual);
    }

    /// <summary>Every name the model lists, each with ordinal near-misses (case, prefix, suffix, decomposition), and absent names.</summary>
    private static IEnumerable<string> QueryNames(SemanticModel model)
    {
        var names = new SortedSet<string>(StringComparer.Ordinal) { "", " ", "NoSuchName", "_error_" };
        foreach (var resolution in model.IdentifierResolutions)
            names.Add(resolution.Occurrence.Name);
        foreach (var declaration in model.Declarations)
            names.Add(declaration.Name);
        foreach (var property in model.PropertyInfos)
            names.Add(property.Name);
        foreach (var name in names.ToArray())
        {
            names.Add(name.ToUpperInvariant());
            names.Add(name.ToLowerInvariant());
            names.Add(name + "x");
            names.Add(name.Normalize(NormalizationForm.FormD));
            if (name.Length > 0)
                names.Add(name[..^1]);
        }

        return names;
    }

    /// <summary>
    /// Every query name through the public queries, their counted seams and the length-hashed index
    /// agrees with the filter. Returns the number of names, and of names that found something.
    /// </summary>
    private static (int Names, int Hits) AssertEveryNameMatchesTheFilter(SemanticModel model, string context)
    {
        var (names, hits) = (0, 0);
        foreach (var name in QueryNames(model))
        {
            var resolutions = ResolutionsByFilter(model, name);
            var declarations = DeclarationsByFilter(model, name);
            AssertSameItems(resolutions, model.FindResolutions(name), $"{context}: FindResolutions('{name}')");
            AssertSameItems(declarations, model.FindDeclarations(name), $"{context}: FindDeclarations('{name}')");
            AssertSameItems(resolutions, model.FindResolutionsCounted(name, out _), $"{context}: FindResolutionsCounted('{name}')");
            AssertSameItems(declarations, model.FindDeclarationsCounted(name, out _), $"{context}: FindDeclarationsCounted('{name}')");
            AssertSameItems(resolutions, model.FindResolutionsByLengthHash(name), $"{context}: length-hashed FindResolutions('{name}')");
            AssertSameItems(declarations, model.FindDeclarationsByLengthHash(name), $"{context}: length-hashed FindDeclarations('{name}')");
            names++;
            if (resolutions.Length + declarations.Length > 0)
                hits++;
        }

        return (names, hits);
    }

    // ── Parsed documents ─────────────────────────────────────────────────────────────────

    /// <summary>
    /// Names that repeat: a root property shadowed in a nested body, the same parameter name in several
    /// callables and at two nesting levels, a clause family, the same public member in two libraries,
    /// an opened member, dotted members, implicit parameters and builtins.
    /// </summary>
    private const string RepeatedNamesDocument =
        "Wert = 1\n"
        + "F(x) = x + x * Wert\n"
        + "G(x, y) = x * y + F(x)\n"
        + "H(x) = {\n"
        + "    Wert = x + 1\n"
        + "    Inner(x) = x + Wert\n"
        + "    Inner(Wert)\n"
        + "}\n"
        + "Clause(0) = 0\n"
        + "Clause(n) = n + Clause(n - 1)\n"
        + "A = {\n"
        + "    public Wert = 2\n"
        + "    public Mehr = Wert + 1\n"
        + "}\n"
        + "B = {\n"
        + "    public Wert = 3\n"
        + "}\n"
        + "Use = {\n"
        + "    open A\n"
        + "    Mehr + A.Wert + B.Wert\n"
        + "}\n"
        + "Imp = a + b * a\n"
        + "Use + Imp(1, 2) + G(1, 2) + H(3) + Clause(2) + F(Wert) + count([Wert, Wert])";

    private const string UnicodeDocument =
        "Größe = 2\n"
        + "Fläche(w, h) = w * h + Größe\n"
        + "Paar = ['😀😀', Größe, 'é𝐀']\n"
        + "Скорость(x) = x + λ + count(Paar)\n"
        + "λ = Größe + Fläche(Größe, 3)\n"
        + "Скорость(1)";

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

    /// <summary>Deferred module regions (B2c): two load-bearing branches whose modules are never fetched.</summary>
    private const string DeferredDocument =
        "open 'https://katlang.org/lib.kat'\n"
        + "F(0) = {\n"
        + "    open 'https://katlang.org/deferred.kat'\n"
        + "    Later + Größe\n"
        + "}\n"
        + "F(1) = {\n"
        + "    D = load('https://katlang.org/deferred-load.kat')\n"
        + "    D.Wert + Größe\n"
        + "}\n"
        + "F(n) = n + Größe\n"
        + "F(2)";

    /// <summary>Modules the parse could not load (no downloader): their names classify as deferred.</summary>
    private const string MissingModuleDocument =
        "open 'https://katlang.org/lib.kat'\n"
        + "X = Größe + Fläche(1, 2)\n"
        + "M = load('https://katlang.org/other.kat')\n"
        + "Y = {\n"
        + "    open M\n"
        + "    Z = Wert + Unklar\n"
        + "    Z\n"
        + "}\n"
        + "X + Y";

    /// <summary>Recovery trees: unclosed groups and blocks, an open of an undeclared name, a missing right-hand side, a malformed pattern and stray closers.</summary>
    private static readonly string[] RecoveryDocuments =
    [
        "A = (1 +\n"
        + "B = A + Größe\n"
        + "C = { D = B +\n"
        + "Ω = { open Missing\n"
        + "  Ω + ",
        "F(x) =\n"
        + "G(y) = { H = y +\n"
        + "  }\n"
        + "}\n"
        + "K(*) = { L = { M =\n"
        + "G(",
        "P = {\n"
        + "    Q(a) = {\n"
        + "        R = a +\n"
        + "    S = {\n"
        + "T = Q(1",
        "x = 1\n"
        + "x = 2\n"
        + "F(x, x) = x\n"
        + "F(1, 2) + x + )",
    ];

    public static TheoryData<string> ParsedDocuments => new()
    {
        "repeated",
        "unicode",
        "generated",
        "module",
        "deferred",
        "missing-module",
        "recovery-0",
        "recovery-1",
        "recovery-2",
        "recovery-3",
    };

    private static RunOptions Downloading() => new()
    {
        DownloadCode = (url, _) => Modules.TryGetValue(url, out var source)
            ? ValueTask.FromResult(source)
            : throw new InvalidOperationException($"404 {url}"),
    };

    private static async Task<SemanticModel> ModelOf(string name)
    {
        switch (name)
        {
            case "repeated":
                return Valid(RepeatedNamesDocument);
            case "unicode":
                return Valid(UnicodeDocument);
            case "generated":
                return Valid(SemanticModelPositionLookupTests.GeneratedDocument(blocks: 5));
            case "module":
                return SemanticModelBuilder.Build((await SourceProvenance.ParseValidAsync(ModuleDocument, Downloading())).Parsed);
            case "deferred":
                var deferred = SemanticModelBuilder.Build((await SourceProvenance.ParseValidAsync(DeferredDocument, Downloading())).Parsed);
                Assert.Contains(deferred.IdentifierResolutions, resolution => resolution.Classification == IdentifierClassification.DeferredModuleReference);
                return deferred;
            case "missing-module":
                var missing = SourceProvenance.ParseAllowingDiagnostics(MissingModuleDocument);
                Assert.Contains(missing.Diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.LoadElaborationUnavailable);
                return SemanticModelBuilder.Build(missing.Parsed);
            default:
                Assert.StartsWith("recovery-", name);
                var source = RecoveryDocuments[int.Parse(name["recovery-".Length..], System.Globalization.CultureInfo.InvariantCulture)];
                var recovered = SourceProvenance.ParseAllowingDiagnostics(source);
                Assert.True(recovered.HasFrontEndErrors, $"{name} should be malformed");
                return SemanticModelBuilder.Build(recovered.Parsed);
        }

        static SemanticModel Valid(string source) => SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
    }

    [Theory]
    [MemberData(nameof(ParsedDocuments))]
    public async Task ParsedDocument_EveryName_MatchesTheFilter(string document)
    {
        var model = await ModelOf(document);

        // A built model has no name index until a name query runs.
        Assert.Equal(-1, model.ResolutionNameKeys);
        Assert.Equal(-1, model.DeclarationNameKeys);

        var (names, hits) = AssertEveryNameMatchesTheFilter(model, document);

        // Every builder site and declaration has a name, so each has one key.
        Assert.Equal(model.IdentifierResolutions.Count, model.ResolutionNameKeys);
        Assert.Equal(model.Declarations.Count, model.DeclarationNameKeys);
        output.WriteLine($"{document}: {names} names, {hits} found something; {model.IdentifierResolutions.Count} sites, {model.Declarations.Count} declarations");
        Assert.True(hits > 0, $"{document}: no query name found anything");
    }

    [Fact]
    public void RepeatedNames_ReturnEveryOccurrenceInListingOrder()
    {
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(RepeatedNamesDocument).Parsed);

        // `Wert`: the root property, the body local of H, and the members of A and B, all declared;
        // read at the root, in H, in A, through `A.` and `B.`, and twice in the final row.
        var declarations = model.FindDeclarations("Wert");
        Assert.Equal(4, declarations.Count);
        Assert.Equal([1, 5, 12, 16], declarations.Select(static declaration => declaration.Span.Start.Line));
        var resolutions = model.FindResolutions("Wert");
        Assert.True(resolutions.Count > declarations.Count, $"{resolutions.Count} sites named Wert");
        Assert.Equal(
            resolutions.Select(static resolution => resolution.Occurrence.Span.Start).Order(),
            resolutions.Select(static resolution => resolution.Occurrence.Span.Start));
        foreach (var declaration in declarations)
            Assert.Contains(resolutions, resolution => ReferenceEquals(resolution.Occurrence, declaration));

        // `x` is a parameter of F, G, H and Inner.
        Assert.Equal([2, 3, 4, 6], model.FindDeclarations("x").Select(static declaration => declaration.Span.Start.Line));
        // The clause family declares `Clause` once per clause.
        Assert.Equal(2, model.FindDeclarations("Clause").Count);
    }

    // ── Host-constructed listings ────────────────────────────────────────────────────────

    private static IdentifierResolution Site(string name, int line)
        => new(
            new IdentifierOccurrence(name, new SourceSpan(line, 1, line, 2), OccurrenceKind.ResolveReference),
            IdentifierClassification.Unresolved,
            null,
            null);

    private static DeclarationOccurrence Declared(string name, int line)
        => new(name, new SourceSpan(line, 1, line, 2), OccurrenceKind.PropertyDefinition);

    private static SemanticModel ModelWith(IdentifierResolution[] resolutions, DeclarationOccurrence[]? declarations = null)
        => new(
            HostRoot,
            [],
            declarations ?? [],
            resolutions,
            [],
            new Dictionary<DeclarationOccurrence, PropertyInfo>(ReferenceEqualityComparer.Instance));

    /// <summary>
    /// Names compare ordinally, as the filter's <c>==</c> did: composed and decomposed forms, case,
    /// culture-sensitive pairs, empty, NUL, a lone surrogate and full-width letters are all different
    /// names. Many of them have one length, so the length-hashed index also runs them as one shared run.
    /// </summary>
    [Fact]
    public void OrdinalNearMisses_AreDifferentNames()
    {
        string[] names =
        [
            "Größe", "Größe", "größe", "GRÖSSE", "Grösse", "i", "I", "İ", "ı", "ß", "ss", "SS",
            "", "\0", "a\0", "\uD800", "😀", "é", "é", "Ａ", "A",
        ];
        var resolutions = names.Concat(Enumerable.Reverse(names)).Select(static (name, i) => Site(name, i + 1)).ToArray();
        var declarations = names.Select(static (name, i) => Declared(name, i + 1)).ToArray();
        var model = ModelWith(resolutions, declarations);

        foreach (var name in names.Append("Gr").Append("ö").Append("a"))
        {
            AssertSameItems(ResolutionsByFilter(model, name), model.FindResolutions(name), $"FindResolutions('{name}')");
            AssertSameItems(DeclarationsByFilter(model, name), model.FindDeclarations(name), $"FindDeclarations('{name}')");
            AssertSameItems(ResolutionsByFilter(model, name), model.FindResolutionsByLengthHash(name), $"length-hashed FindResolutions('{name}')");
            AssertSameItems(DeclarationsByFilter(model, name), model.FindDeclarationsByLengthHash(name), $"length-hashed FindDeclarations('{name}')");
        }

        // Each listed name finds exactly its own two sites and its declaration.
        foreach (var name in names)
        {
            Assert.All(model.FindResolutions(name), resolution => Assert.Equal(name, resolution.Occurrence.Name));
            Assert.Equal(2, model.FindResolutions(name).Count);
            Assert.Same(Assert.Single(model.FindDeclarations(name)), declarations[Array.IndexOf(names, name)]);
        }
    }

    /// <summary>
    /// The index keeps the filter's listing order whatever the spans are: an instance listed twice is
    /// found twice, and an unordered listing comes back in its own order, not by position.
    /// </summary>
    [Fact]
    public void RepeatedInstancesAndUnorderedListings_KeepTheListingOrder()
    {
        var late = Site("n", 9);
        var early = Site("n", 1);
        var other = Site("m", 5);
        var model = ModelWith([late, other, early, late, other, early], [Declared("n", 4), Declared("n", 2)]);

        Assert.Equal([late, early, late, early], model.FindResolutions("n"));
        Assert.Equal([other, other], model.FindResolutions("m"));
        Assert.Equal([4, 2], model.FindDeclarations("n").Select(static declaration => declaration.Span.Start.Line));
        Assert.Equal([late, early, late, early], model.FindResolutionsByLengthHash("n"));
        Assert.Equal(6, model.ResolutionNameKeys);
    }

    /// <summary>
    /// A null name is never found: the filter's <c>==</c> never matched it, because the query refuses
    /// a null name. Such an item gets no key, and the rest of the listing is indexed as usual.
    /// </summary>
    [Fact]
    public void NullNames_AreNeverFound_AndGetNoKey()
    {
        var model = ModelWith(
            [Site(null!, 1), Site("n", 2), Site(null!, 3), Site("n", 4)],
            [Declared(null!, 1), Declared("n", 2)]);

        foreach (var name in new[] { "n", "", "null" })
        {
            AssertSameItems(ResolutionsByFilter(model, name), model.FindResolutions(name), $"FindResolutions('{name}')");
            AssertSameItems(DeclarationsByFilter(model, name), model.FindDeclarations(name), $"FindDeclarations('{name}')");
        }

        Assert.Equal(2, model.FindResolutions("n").Count);
        Assert.Equal(2, model.ResolutionNameKeys);
        Assert.Equal(1, model.DeclarationNameKeys);
        Assert.Equal("name", Assert.Throws<ArgumentNullException>(() => model.FindResolutions(null!)).ParamName);
        Assert.Equal("name", Assert.Throws<ArgumentNullException>(() => model.FindDeclarations(null!)).ParamName);
    }

    /// <summary>
    /// The internal constructor accepts a listing with a null entry, which no builder model has. That
    /// listing gets no index, and its query keeps the scan, which throws on every call as it always
    /// did. The other listing's query is unaffected.
    /// </summary>
    [Fact]
    public void NullEntry_KeepsTheScan()
    {
        var nullResolution = ModelWith([Site("n", 1), null!], [Declared("n", 1)]);
        Assert.Throws<NullReferenceException>(() => nullResolution.FindResolutions("n"));
        Assert.Throws<NullReferenceException>(() => nullResolution.FindResolutions("absent"));
        Assert.Equal(-1, nullResolution.ResolutionNameKeys);
        Assert.Null(nullResolution.FindResolutionsByLengthHash("n"));
        Assert.Single(nullResolution.FindDeclarations("n"));
        Assert.Equal(1, nullResolution.DeclarationNameKeys);

        var noOccurrence = ModelWith([new IdentifierResolution(null!, IdentifierClassification.Unresolved, null, null)]);
        Assert.Throws<NullReferenceException>(() => noOccurrence.FindResolutions("n"));
        Assert.Equal(-1, noOccurrence.ResolutionNameKeys);

        var nullDeclaration = ModelWith([Site("n", 1)], [Declared("n", 1), null!]);
        Assert.Throws<NullReferenceException>(() => nullDeclaration.FindDeclarations("n"));
        Assert.Throws<NullReferenceException>(() => nullDeclaration.FindDeclarations("n"));
        Assert.Equal(-1, nullDeclaration.DeclarationNameKeys);
        Assert.Null(nullDeclaration.FindDeclarationsByLengthHash("n"));
        Assert.Single(nullDeclaration.FindResolutions("n"));
    }

    /// <summary>
    /// The shared-hash path, through the length-hashed index: names of one length share one run of
    /// keys, which the build flags. The query then compares each item's name, keeps the listing order
    /// and returns just the matches. A run shared without a match finds nothing, and so does a
    /// run owned by another name of the query's length.
    /// </summary>
    [Fact]
    public void SharedHashRuns_SeparateTheirNames()
    {
        var ab1 = Site("ab", 1);
        var cd2 = Site("cd", 2);
        var ab3 = Site("ab", 3);
        var xyz4 = Site("xyz", 4);
        var cd5 = Site("cd", 5);
        var ef6 = Site("ef", 6);
        var model = ModelWith([ab1, cd2, ab3, xyz4, cd5, ef6], [Declared("cd", 1), Declared("ab", 2), Declared("cd", 3)]);

        Assert.Equal([ab1, ab3], model.FindResolutionsByLengthHash("ab"));
        Assert.Equal([cd2, cd5], model.FindResolutionsByLengthHash("cd"));
        Assert.Equal([ef6], model.FindResolutionsByLengthHash("ef"));
        Assert.Equal([xyz4], model.FindResolutionsByLengthHash("xyz"));
        Assert.Same(SafeReadOnlyCollection<IdentifierResolution>.Empty, model.FindResolutionsByLengthHash("zz"));
        Assert.Same(SafeReadOnlyCollection<IdentifierResolution>.Empty, model.FindResolutionsByLengthHash("qrs"));
        Assert.Same(SafeReadOnlyCollection<IdentifierResolution>.Empty, model.FindResolutionsByLengthHash("q"));
        Assert.Equal([1, 3], model.FindDeclarationsByLengthHash("cd")!.Select(static declaration => declaration.Span.Start.Line));
        Assert.Equal([2], model.FindDeclarationsByLengthHash("ab")!.Select(static declaration => declaration.Span.Start.Line));

        // The ordinal index agrees.
        foreach (var name in new[] { "ab", "cd", "ef", "xyz", "zz", "qrs", "q" })
        {
            AssertSameItems(ResolutionsByFilter(model, name), model.FindResolutions(name), $"FindResolutions('{name}')");
            AssertSameItems(ResolutionsByFilter(model, name), model.FindResolutionsByLengthHash(name), $"length-hashed FindResolutions('{name}')");
            AssertSameItems(DeclarationsByFilter(model, name), model.FindDeclarations(name), $"FindDeclarations('{name}')");
        }
    }

    /// <summary>
    /// Seeded random listings — names from a small alphabet, so that names repeat and many share a
    /// length, null names, repeated instances, any order — agree with the filter for every name and
    /// for absent names, through the ordinal index, the counted seam and the length-hashed index.
    /// </summary>
    [Fact]
    public void RandomListings_MatchTheFilter()
    {
        string?[] alphabet = ["a", "b", "ab", "ba", "abc", "A", "Ä", "ä", "x", "xy", "", "😀", null];
        var random = new Random(20261121);
        var sharedRuns = 0;
        for (var round = 0; round < 1_500; round++)
        {
            var resolutions = new List<IdentifierResolution>();
            var count = random.Next(0, 30);
            for (var i = 0; i < count; i++)
            {
                resolutions.Add(resolutions.Count > 0 && random.Next(6) == 0
                    ? resolutions[random.Next(resolutions.Count)]
                    : Site(alphabet[random.Next(alphabet.Length)]!, random.Next(1, 20)));
            }

            var declarations = new List<DeclarationOccurrence>();
            var declared = random.Next(0, 12);
            for (var i = 0; i < declared; i++)
                declarations.Add(Declared(alphabet[random.Next(alphabet.Length)]!, random.Next(1, 20)));

            var model = ModelWith([.. resolutions], [.. declarations]);
            foreach (var name in alphabet.OfType<string>().Append("abcd").Append("y").Append("aa"))
            {
                var expected = ResolutionsByFilter(model, name);
                AssertSameItems(expected, model.FindResolutions(name), $"round {round}: FindResolutions('{name}')");
                AssertSameItems(expected, model.FindResolutionsCounted(name, out _), $"round {round}: FindResolutionsCounted('{name}')");
                AssertSameItems(expected, model.FindResolutionsByLengthHash(name), $"round {round}: length-hashed FindResolutions('{name}')");
                AssertSameItems(DeclarationsByFilter(model, name), model.FindDeclarations(name), $"round {round}: FindDeclarations('{name}')");
                AssertSameItems(DeclarationsByFilter(model, name), model.FindDeclarationsByLengthHash(name), $"round {round}: length-hashed FindDeclarations('{name}')");
                if (expected.Length > 0
                    && resolutions.Any(resolution => resolution.Occurrence.Name is { } other && other.Length == name.Length && other != name))
                {
                    sharedRuns++;
                }
            }
        }

        output.WriteLine($"queries that found a name in a shared length-hash run: {sharedRuns}");
        Assert.True(sharedRuns > 1_000, $"the shared-hash path must be exercised ({sharedRuns})");
    }

    // ── Results, laziness and publication ────────────────────────────────────────────────

    /// <summary>
    /// Each call that finds something returns a new read-only list over its own array, as the former
    /// query did. Its storage is never handed out: writes are refused and its SyncRoot is the view
    /// itself. A call that finds nothing returns the shared empty list.
    /// </summary>
    [Fact]
    public void Results_AreNewReadOnlyListsOfTheirOwn()
    {
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(RepeatedNamesDocument).Parsed);

        var first = model.FindResolutions("Wert");
        var second = model.FindResolutions("Wert");
        Assert.NotSame(first, second);
        Assert.Equal(first, second);
        Assert.NotSame(model.FindDeclarations("Wert"), model.FindDeclarations("Wert"));
        foreach (var list in new System.Collections.IList[] { (System.Collections.IList)first, (System.Collections.IList)model.FindDeclarations("x") })
        {
            Assert.True(list.IsReadOnly);
            Assert.Throws<NotSupportedException>(() => list[0] = list[0]);
            Assert.Same(list, list.SyncRoot);
        }

        Assert.Throws<NotSupportedException>(() => ((IList<IdentifierResolution>)first)[0] = first[1]);
        Assert.Same(SafeReadOnlyCollection<IdentifierResolution>.Empty, model.FindResolutions("NoSuchName"));
        Assert.Same(SafeReadOnlyCollection<DeclarationOccurrence>.Empty, model.FindDeclarations("count"));
    }

    /// <summary>
    /// Each listing is indexed on its query's first call, not when the model is built, so a model that
    /// is never queried by name stores no index. Later calls reuse that index.
    /// </summary>
    [Fact]
    public void EachIndex_IsBuiltOnItsQuerysFirstCall()
    {
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(RepeatedNamesDocument).Parsed);
        Assert.Equal(-1, model.ResolutionNameKeys);
        Assert.Equal(-1, model.DeclarationNameKeys);

        Assert.NotEmpty(model.FindDeclarations("Wert"));
        Assert.Equal(model.Declarations.Count, model.DeclarationNameKeys);
        Assert.Equal(-1, model.ResolutionNameKeys);

        Assert.Empty(model.FindResolutions("NoSuchName"));
        Assert.Equal(model.IdentifierResolutions.Count, model.ResolutionNameKeys);

        // Position and scope queries do not build a name index.
        var other = SemanticModelBuilder.Build(SourceProvenance.ParseValid(RepeatedNamesDocument).Parsed);
        _ = other.FindResolutionAt(new SourcePosition(2, 8));
        _ = other.GetVisibleSymbolsAt(new SourcePosition(5, 5));
        Assert.Equal(-1, other.ResolutionNameKeys);
        Assert.Equal(-1, other.DeclarationNameKeys);
    }

    /// <summary>
    /// Concurrent first calls on a fresh model race to build and publish its index. Every caller
    /// gets the filter's answer, whichever index wins.
    /// </summary>
    [Fact]
    public void ConcurrentFirstCalls_AllMatchTheFilter()
    {
        var parsed = SourceProvenance.ParseValid(SemanticModelPositionLookupTests.GeneratedDocument(blocks: 4)).Parsed;
        const int threads = 8;
        for (var round = 0; round < 25; round++)
        {
            var model = SemanticModelBuilder.Build(parsed);
            var names = model.Declarations.Select(static declaration => declaration.Name).Distinct().ToArray();
            using var start = new Barrier(threads);
            var failures = new System.Collections.Concurrent.ConcurrentQueue<string>();
            var workers = Enumerable.Range(0, threads).Select(worker => new Thread(() =>
            {
                start.SignalAndWait();
                for (var i = worker; i < names.Length; i += threads)
                {
                    var name = names[i];
                    if (!model.FindResolutions(name).SequenceEqual(ResolutionsByFilter(model, name), ReferenceEqualityComparer.Instance))
                        failures.Enqueue($"FindResolutions('{name}')");
                    if (!model.FindDeclarations(name).SequenceEqual(DeclarationsByFilter(model, name), ReferenceEqualityComparer.Instance))
                        failures.Enqueue($"FindDeclarations('{name}')");
                }
            })).ToArray();
            foreach (var worker in workers)
                worker.Start();
            foreach (var worker in workers)
                worker.Join();

            Assert.Empty(failures);
            Assert.Equal(model.IdentifierResolutions.Count, model.ResolutionNameKeys);
            Assert.Equal(model.Declarations.Count, model.DeclarationNameKeys);
        }
    }

    // ── Cost ─────────────────────────────────────────────────────────────────────────────

    /// <summary>A listing of <paramref name="sites"/> sites in which each of <c>sites / 2</c> names labels two far-apart sites.</summary>
    private static SemanticModel PairedListing(int sites)
    {
        var listing = new IdentifierResolution[sites];
        for (var i = 0; i < sites; i++)
            listing[i] = Site($"n{i % (sites / 2)}", i + 1);
        return ModelWith(listing, listing.Select(static resolution => Declared(resolution.Occurrence.Name, resolution.Occurrence.Span.Start.Line)).ToArray());
    }

    /// <summary>
    /// The counted seam reports the comparisons the public query uses to locate its hash run.
    /// It counts at most ⌊log₂ K⌋ + 1 binary-search probes over K keys, then the
    /// run of keys with the name's hash, and the key after the run. The run holds the name's two
    /// sites and any other name with the same ordinal string hash, which the test counts itself. For
    /// 8,192 hits and misses, 64 times the sites (512 to 32,768) took 1.55 times the probes (90,108
    /// to 139,262), and the bound is twice the small total. A query that counts no probe fails the
    /// lower bound of one, so a scan that bypasses the index fails too. The public queries allocate
    /// only their results: nothing for a miss, and one view and one array of two for a hit. The
    /// former filter allocated an enumerator, a closure and a delegate per query, even when it found
    /// nothing. Probes and bytes do not depend on load; elapsed time is printed, not asserted.
    /// Measured 2026-11-20 with BenchmarkDotNet on the 12,801-line benchmark document: both queries
    /// took 35 ns for an absent name and 60 ns for a sparse one, against 143 µs and 120 µs for the
    /// former filter.
    /// </summary>
    [Fact]
    public void NameQueryCost_InspectsTheResultsNotTheListing()
    {
        static string[] Queries(int sites)
        {
            var queries = new string[8_192];
            for (var q = 0; q < queries.Length; q++)
                queries[q] = q % 2 == 0 ? $"n{(int)((long)q * (sites / 2) / queries.Length)}" : $"m{q}";
            return queries;
        }

        (long Total, int Fewest, int Most) Probes(SemanticModel model, string[] queries)
        {
            Assert.Equal(-1, model.ResolutionNameKeys);
            var keys = model.IdentifierResolutions.Count;
            var hashes = model.IdentifierResolutions
                .GroupBy(static resolution => resolution.Occurrence.Name.GetHashCode())
                .ToDictionary(static group => group.Key, static group => group.Count());
            var search = BitOperations.Log2((uint)keys) + 1;
            var (total, fewest, most, hits) = (0L, int.MaxValue, 0, 0);
            foreach (var query in queries)
            {
                var found = model.FindResolutionsCounted(query, out var probes);
                var run = hashes.GetValueOrDefault(query.GetHashCode());
                Assert.Equal(query[0] == 'n' ? 2 : 0, found.Count);
                Assert.InRange(probes, 1, search + run + 1);
                Assert.Equal(keys, model.ResolutionNameKeys);
                var declarations = model.FindDeclarationsCounted(query, out var declarationProbes);
                Assert.Equal(found.Count, declarations.Count);
                Assert.InRange(declarationProbes, 1, search + run + 1);
                if (found.Count > 0)
                    hits++;
                total += probes;
                fewest = Math.Min(fewest, probes);
                most = Math.Max(most, probes);
            }

            Assert.Equal(queries.Length / 2, hits);
            return (total, fewest, most);
        }

        // The public queries, five times: the fewest bytes a run allocated and the best time.
        static (long Bytes, double Milliseconds) PublicQueries(SemanticModel model, string[] queries)
        {
            var bytes = long.MaxValue;
            var best = double.MaxValue;
            for (var run = 0; run < 5; run++)
            {
                var found = 0;
                var before = GC.GetAllocatedBytesForCurrentThread();
                var watch = Stopwatch.StartNew();
                foreach (var query in queries)
                    found += model.FindResolutions(query).Count + model.FindDeclarations(query).Count;
                watch.Stop();
                bytes = Math.Min(bytes, GC.GetAllocatedBytesForCurrentThread() - before);
                Assert.Equal(2 * queries.Length, found);
                best = Math.Min(best, watch.Elapsed.TotalMilliseconds);
            }

            return (bytes, best);
        }

        var small = PairedListing(512);
        var smallQueries = Queries(512);
        var smallProbes = Probes(small, smallQueries);
        var large = PairedListing(32_768);
        var largeQueries = Queries(32_768);
        var largeProbes = Probes(large, largeQueries);
        _ = PublicQueries(small, smallQueries);
        var smallRuns = PublicQueries(small, smallQueries);
        var largeRuns = PublicQueries(large, largeQueries);
        output.WriteLine(
            $"8,192 resolution queries: {smallProbes.Total:N0} -> {largeProbes.Total:N0} probes ({(double)largeProbes.Total / smallProbes.Total:F2} times; "
            + $"{smallProbes.Fewest}-{smallProbes.Most} -> {largeProbes.Fewest}-{largeProbes.Most} per query) over 512 -> 32,768 sites; "
            + $"both queries: {smallRuns.Bytes:N0} -> {largeRuns.Bytes:N0} B; not asserted: {smallRuns.Milliseconds:F3} -> {largeRuns.Milliseconds:F3} ms (best of five)");
        Assert.True(
            largeProbes.Total <= 2 * smallProbes.Total,
            $"64 times the sites made the queries take {(double)largeProbes.Total / smallProbes.Total:F1} times the probes ({smallProbes.Total:N0} -> {largeProbes.Total:N0}).");

        // 4,096 hits per query kind, each a 24-byte view over a 40-byte array of two (64-bit): 524,288
        // bytes, and nothing for the misses. The slack is the ~8 KB counter quantum of a background
        // collection, twice. The former filter allocated 168 bytes more per query (2.6 MB in all).
        const long results = 2L * 4_096 * (24 + 40);
        Assert.True(smallRuns.Bytes <= results + 16_384, $"16,384 queries over 512 sites allocated {smallRuns.Bytes:N0} B.");
        Assert.True(largeRuns.Bytes <= results + 16_384, $"16,384 queries over 32,768 sites allocated {largeRuns.Bytes:N0} B.");
    }

    /// <summary>
    /// The index stores 8 bytes per item and nothing per name. The first query on 32,768 sites with
    /// 16,384 names allocates the key array (8 bytes a key plus its header), the index object and the
    /// list it returns, and keeps all but the list. The bound adds 1 KiB for the objects and the
    /// counter quantum twice. A dictionary from each name to its items, measured before this layout
    /// was chosen, kept 2.4 times as much for both indexes (681 KB against 288 KB on the 12,801-line
    /// benchmark document, whose model retains 12.8 MB). The build time is printed, not asserted. On
    /// that document BenchmarkDotNet measured 1.7 ms to build both indexes, about twelve of the
    /// former query pairs, and a fresh model's first FindResolutions took 1.9 ms, against 0.3 ms
    /// for the former filter.
    /// </summary>
    [Fact]
    public void NameIndex_StoresEightBytesPerItem()
    {
        var warm = PairedListing(512);
        _ = warm.FindResolutions("n1");
        _ = warm.FindDeclarations("n1");

        var model = PairedListing(32_768);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var watch = Stopwatch.StartNew();
        var found = model.FindResolutions("n7");
        watch.Stop();
        var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
        var declarationsBefore = GC.GetAllocatedBytesForCurrentThread();
        var declarations = model.FindDeclarations("n7");
        var declarationBytes = GC.GetAllocatedBytesForCurrentThread() - declarationsBefore;
        output.WriteLine($"first queries over 32,768 items: {bytes:N0} and {declarationBytes:N0} B; not asserted: {watch.Elapsed.TotalMilliseconds:F3} ms for the resolutions");

        Assert.Equal(2, found.Count);
        Assert.Equal(2, declarations.Count);
        Assert.Equal(32_768, model.ResolutionNameKeys);
        Assert.Equal(32_768, model.DeclarationNameKeys);
        const long keys = 8L * 32_768;
        Assert.InRange(bytes, keys, keys + 1_024 + 16_384);
        Assert.InRange(declarationBytes, keys, keys + 1_024 + 16_384);
    }

    // Where the exact-bytes test stores the lists it measures, so that none can be stack-allocated.
    private static object? s_sink;

    /// <summary>
    /// An indexed query allocates exactly its result: nothing when it finds nothing, and otherwise one
    /// array of its results and one view over it — what <c>SafeReadOnlyCollection.Over</c> of a new
    /// array of that length allocates. The former filter added an enumerator, a closure, a delegate
    /// and a growth buffer to every query, and the indexed path once allocated the filter's closure
    /// on every call.
    /// </summary>
    [Fact]
    public void NameQueries_AllocateOnlyTheirResultLists_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(SemanticModelPositionLookupTests.GeneratedDocument(blocks: 4)).Parsed);
        var names = QueryNames(model).ToArray();
        foreach (var name in names)
        {
            _ = model.FindResolutions(name);
            _ = model.FindDeclarations(name);
        }

        static long ResultBytes<T>(int count)
        {
            if (count == 0)
                return 0;
            var before = GC.GetAllocatedBytesForCurrentThread();
            s_sink = SafeReadOnlyCollection.Over(new T[count]);
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        _ = ResultBytes<IdentifierResolution>(1);
        _ = ResultBytes<DeclarationOccurrence>(1);
        var (misses, hits) = (0, 0);
        foreach (var name in names)
        {
            var before = GC.GetAllocatedBytesForCurrentThread();
            var resolutions = model.FindResolutions(name);
            var resolutionBytes = GC.GetAllocatedBytesForCurrentThread() - before;
            before = GC.GetAllocatedBytesForCurrentThread();
            var declarations = model.FindDeclarations(name);
            var declarationBytes = GC.GetAllocatedBytesForCurrentThread() - before;

            Assert.Equal(ResultBytes<IdentifierResolution>(resolutions.Count), resolutionBytes);
            Assert.Equal(ResultBytes<DeclarationOccurrence>(declarations.Count), declarationBytes);
            if (resolutions.Count == 0)
                misses++;
            else
                hits++;
        }

        Assert.True(misses > 100 && hits > 50, $"{misses} misses and {hits} hits");

        // The length-hashed seam rebuilds the same index on each call. A different-length miss
        // measures the build alone. The shared run contains both "aa" and "bb" in all three calls.
        var shared = ModelWith([Site("aa", 1), Site("bb", 2), Site("aa", 3)]);
        long LengthHashBytes(string name)
        {
            var before = GC.GetAllocatedBytesForCurrentThread();
            s_sink = shared.FindResolutionsByLengthHash(name);
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        _ = LengthHashBytes("zz");
        _ = LengthHashBytes("aa");
        var buildBytes = LengthHashBytes("z");
        Assert.Equal(buildBytes, LengthHashBytes("zz"));
        Assert.Equal(buildBytes + ResultBytes<IdentifierResolution>(2), LengthHashBytes("aa"));
        GcIsolatedAllocation.Complete();
    }
}
