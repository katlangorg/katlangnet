using System.Diagnostics;
using System.Text;
using KatLang.Semantics;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// Scope selection (KL-05) — <see cref="SemanticModel.FindScopeAt"/>, and through it
/// <see cref="SemanticModel.GetVisibleSymbolsAt"/>, completion's query — binary-searches a position
/// index the model builds once instead of inspecting every scope region per query. These tests
/// pin that the selected scope is EXACTLY the instance the former scan selected, at every
/// position: of the containing regions the deepest, at equal depth the later start and then the
/// earlier end, of identical hulls the first listed; a hull's end and an empty hull contain
/// nothing; outside every region the first spanless scope, else a fresh empty one. Parsed
/// documents (wide siblings, deep nesting, Unicode, opens and modules, deferred and missing
/// modules, recovery trees) and host-constructed listings (disjoint, adjacent, overlapping,
/// identical at different and equal depths, zero-width, default, rootless, repeated, random) are
/// compared with the scan, kept here verbatim as the oracle. They also pin that the index stores
/// at most two intervals per non-empty hull, that query cost grows sublinearly with the number
/// of siblings, and that building the index takes O(S log S) counted steps for nested, tied,
/// overlapping and wide listings. Implementation-only optimization: no editor-visible result changes.
/// </summary>
public class SemanticModelScopeLookupTests(ITestOutputHelper output)
{
    private static readonly Algorithm HostRoot = SourceProvenance.ParseValid("1").Root;

    /// <summary>The scan <see cref="SemanticModel.FindScopeAt"/> performed before the index, verbatim.</summary>
    private static ScopeVisibility Scan(SemanticModel model, SourcePosition position)
    {
        ScopeVisibility? root = null;
        ScopeVisibility? best = null;
        SourceSpan? bestHull = null;
        foreach (var scope in model.ScopeVisibilities)
        {
            if (scope.Span is not { } hull)
            {
                root ??= scope;
                continue;
            }

            if (!hull.Contains(position))
                continue;

            if (best is null
                || scope.NestingDepth > best.NestingDepth
                || (scope.NestingDepth == best.NestingDepth && bestHull is { } current && IsInnerSpan(hull, current)))
            {
                best = scope;
                bestHull = hull;
            }
        }

        return best ?? root ?? new ScopeVisibility(Span: null, Symbols: []);
    }

    private static bool IsInnerSpan(SourceSpan candidate, SourceSpan current)
    {
        var byStart = candidate.Start.CompareTo(current.Start);
        return byStart != 0 ? byStart > 0 : candidate.End < current.End;
    }

    private static bool Listed(SemanticModel model, ScopeVisibility scope)
        => model.ScopeVisibilities.Contains(scope, ReferenceEqualityComparer.Instance);

    /// <summary>
    /// Asserts the query selects the scan's instance at the position — or, where the scan made a
    /// fresh empty scope (a listing with no spanless scope), a fresh empty scope too. Returns
    /// whether a nested region (one with a hull) was selected.
    /// </summary>
    private static bool AssertSelectsTheScansScope(SemanticModel model, SourcePosition position)
    {
        var expected = Scan(model, position);
        var actual = model.FindScopeAt(position);
        if (Listed(model, expected))
        {
            Assert.True(
                ReferenceEquals(expected, actual),
                $"FindScopeAt({position}) selected {Describe(model, actual)}; the scan selects {Describe(model, expected)}.");
        }
        else
        {
            Assert.False(Listed(model, actual), $"FindScopeAt({position}) selected the listed {Describe(model, actual)}; the scan selects no listed scope.");
            Assert.Null(actual.Span);
            Assert.Empty(actual.Symbols);
            Assert.Equal(0, actual.NestingDepth);
            Assert.NotSame(actual, model.FindScopeAt(position));
        }

        return expected.Span is not null;
    }

    private static string Describe(SemanticModel model, ScopeVisibility scope)
    {
        var index = -1;
        for (var i = 0; i < model.ScopeVisibilities.Count; i++)
        {
            if (ReferenceEquals(model.ScopeVisibilities[i], scope))
            {
                index = i;
                break;
            }
        }

        return $"#{index} {scope.Span?.ToString() ?? "(no span)"} depth {scope.NestingDepth}";
    }

    private static int NonEmptyHulls(SemanticModel model)
        => model.ScopeVisibilities.Count(static scope => scope.Span is { } hull && hull.Start < hull.End);

    private static void AssertIndexIsBoundedByTheHulls(SemanticModel model)
        => Assert.InRange(model.ScopeIndexIntervals, 0, 2 * NonEmptyHulls(model));

    // ── Parsed documents ────────────────────────────────────────────────────────────────

    /// <summary>The brief's reproduction: <c>k</c> one-line definitions <c>Fi(x) = x + 1</c> and a root row <c>0</c>.</summary>
    private static string Definitions(int k)
    {
        var text = new StringBuilder();
        for (var i = 0; i < k; i++)
            text.Append($"F{i}(x) = x + 1\n");
        return text.Append('0').ToString();
    }

    /// <summary>Blocks nested <paramref name="depth"/> deep, each reading the one around it, with siblings at every level.</summary>
    private static string NestedDocument(int depth)
    {
        var text = new StringBuilder();
        for (var level = 0; level < depth; level++)
        {
            var indent = new string(' ', 4 * level);
            text.Append($"{indent}L{level} = {{\n");
            text.Append($"{indent}    V{level} = {(level == 0 ? "1" : $"V{level - 1} + 1")}\n");
            text.Append($"{indent}    S{level}(x) = x + V{level}\n");
        }

        for (var level = depth - 1; level >= 0; level--)
        {
            var indent = new string(' ', 4 * level);
            text.Append($"{indent}    {(level == depth - 1 ? $"V{level}" : $"L{level + 1} + S{level}(V{level})")}\n");
            text.Append($"{indent}}}\n");
        }

        return text.Append("L0").ToString();
    }

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

    /// <summary>A root module open and a module property opened in a nested scope: module subtrees emit no regions.</summary>
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
    ];

    public static TheoryData<string> ParsedDocuments => new()
    {
        "definitions",
        "nested",
        "generated",
        "unicode",
        "module",
        "deferred",
        "missing-module",
        "recovery-0",
        "recovery-1",
        "recovery-2",
    };

    private static RunOptions Downloading(ICollection<string>? fetched = null) => new()
    {
        DownloadCode = (url, _) =>
        {
            fetched?.Add(url);
            return Modules.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : throw new InvalidOperationException($"404 {url}");
        },
    };

    private static async Task<(string Source, SemanticModel Model)> ModelOf(string name)
    {
        switch (name)
        {
            case "definitions":
                return Valid(Definitions(24));
            case "nested":
                return Valid(NestedDocument(7));
            case "generated":
                return Valid(SemanticModelPositionLookupTests.GeneratedDocument(blocks: 5));
            case "unicode":
                return Valid(UnicodeDocument);
            case "module":
                return (ModuleDocument, SemanticModelBuilder.Build((await SourceProvenance.ParseValidAsync(ModuleDocument, Downloading())).Parsed));
            case "deferred":
                var fetched = new List<string>();
                var deferred = SemanticModelBuilder.Build((await SourceProvenance.ParseValidAsync(DeferredDocument, Downloading(fetched))).Parsed);
                Assert.Equal([LibUrl], fetched);
                Assert.Contains(deferred.IdentifierResolutions, resolution => resolution.Classification == IdentifierClassification.DeferredModuleReference);
                return (DeferredDocument, deferred);
            case "missing-module":
                var missing = SourceProvenance.ParseAllowingDiagnostics(MissingModuleDocument);
                Assert.Contains(missing.Diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.LoadElaborationUnavailable);
                return (MissingModuleDocument, SemanticModelBuilder.Build(missing.Parsed));
            default:
                Assert.StartsWith("recovery-", name);
                var source = RecoveryDocuments[int.Parse(name["recovery-".Length..], System.Globalization.CultureInfo.InvariantCulture)];
                var recovered = SourceProvenance.ParseAllowingDiagnostics(source);
                Assert.True(recovered.HasFrontEndErrors, $"{name} should be malformed");
                return (source, SemanticModelBuilder.Build(recovered.Parsed));
        }

        static (string, SemanticModel) Valid(string source)
            => (source, SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed));
    }

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

    [Theory]
    [MemberData(nameof(ParsedDocuments))]
    public async Task ParsedDocument_EveryPosition_SelectsTheScansScope(string name)
    {
        var (source, model) = await ModelOf(name);
        AssertIndexIsBoundedByTheHulls(model);

        var nested = 0;
        var positions = 0;
        foreach (var position in EveryPosition(source))
        {
            positions++;
            if (AssertSelectsTheScansScope(model, position))
                nested++;

            // Completion reads the selected scope's names, then the prelude names they leave unshadowed.
            var scope = Scan(model, position);
            var shadowed = scope.Symbols.Select(static symbol => symbol.Name).ToHashSet(StringComparer.Ordinal);
            Assert.Equal<VisibleSymbol>(
                scope.Symbols.Concat(model.PreludeSymbols.Where(symbol => !shadowed.Contains(symbol.Name))),
                model.GetVisibleSymbolsAt(position),
                ReferenceEqualityComparer.Instance);
        }

        // Each region is selected at its own start, unless a deeper or inner region starts there too.
        foreach (var scope in model.ScopeVisibilities)
        {
            if (scope.Span is { } hull)
            {
                AssertSelectsTheScansScope(model, hull.Start);
                AssertSelectsTheScansScope(model, hull.End);
            }
        }

        var depth = model.ScopeVisibilities.Max(static scope => scope.NestingDepth);
        output.WriteLine($"{name}: {model.ScopeVisibilities.Count} scopes (deepest {depth}), {model.ScopeIndexIntervals} index intervals, {nested} of {positions} positions in a nested region");
        Assert.True(nested > 0, $"{name}: no position selects a nested region");
        if (name == "nested")
            Assert.True(depth >= 7, $"nested: the deepest region is at depth {depth}");
    }

    /// <summary>
    /// The brief's reproduction at 16, 64 and 256 definitions: 17, 65 and 257 scope records, each
    /// definition's right-hand <c>x</c> in its own depth-1 region — the scan visited all of them per
    /// query (272, 4,160 and 65,792 records for one query per definition).
    /// </summary>
    [Theory]
    [InlineData(16)]
    [InlineData(64)]
    [InlineData(256)]
    public void Definitions_EachRightHandSide_SelectsItsDefinitionsScope(int k)
    {
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(Definitions(k)).Parsed);
        Assert.Equal(k + 1, model.ScopeVisibilities.Count);
        AssertIndexIsBoundedByTheHulls(model);

        var selected = new HashSet<ScopeVisibility>(ReferenceEqualityComparer.Instance);
        for (var i = 0; i < k; i++)
        {
            var x = new SourcePosition(i + 1, $"F{i}(x) = ".Length + 1);
            Assert.True(AssertSelectsTheScansScope(model, x));
            var scope = model.FindScopeAt(x);
            Assert.Equal(1, scope.NestingDepth);
            Assert.True(scope.Span!.Value.Contains(x));
            Assert.True(selected.Add(scope), $"definition {i} shares its scope with another definition");
        }

        // The root row is in the root scope, the first listed one.
        Assert.Same(model.ScopeVisibilities[0], model.FindScopeAt(new SourcePosition(k + 1, 1)));
        Assert.Null(model.ScopeVisibilities[0].Span);
    }

    // ── Host-constructed listings ───────────────────────────────────────────────────────

    private static ScopeVisibility Scope(SourceSpan? span, int depth, string name = "s")
        => new(span, [new VisibleSymbol(name, IdentifierClassification.PropertyReference, null, null)], depth);

    private static ScopeVisibility Root(string name = "root") => Scope(null, 0, name);

    private static SemanticModel ModelWith(params ScopeVisibility[] scopes)
        => new(
            HostRoot,
            [],
            [],
            [],
            [],
            new Dictionary<DeclarationOccurrence, PropertyInfo>(ReferenceEqualityComparer.Instance),
            scopes);

    private static IEnumerable<SourcePosition> Grid(int lines, int columns)
    {
        for (var line = 1; line <= lines; line++)
        {
            for (var column = 1; column <= columns; column++)
                yield return new SourcePosition(line, column);
        }
    }

    private static void AssertEveryGridPositionSelectsTheScansScope(SemanticModel model, int lines = 6, int columns = 14)
    {
        AssertIndexIsBoundedByTheHulls(model);
        foreach (var position in Grid(lines, columns))
            AssertSelectsTheScansScope(model, position);
    }

    [Fact]
    public void DisjointAndAdjacentSiblings_FollowTheHalfOpenRule()
    {
        var root = Root();
        var left = Scope(new SourceSpan(1, 1, 1, 4), 1, "Left");
        var right = Scope(new SourceSpan(1, 4, 1, 7), 1, "Right");
        var later = Scope(new SourceSpan(1, 9, 2, 3), 1, "Later");
        var model = ModelWith(root, later, right, left);

        Assert.Same(left, model.FindScopeAt(new SourcePosition(1, 1)));
        Assert.Same(left, model.FindScopeAt(new SourcePosition(1, 3)));
        // A hull's exclusive end belongs to the adjacent sibling, or to the root in a gap.
        Assert.Same(right, model.FindScopeAt(new SourcePosition(1, 4)));
        Assert.Same(root, model.FindScopeAt(new SourcePosition(1, 7)));
        Assert.Same(later, model.FindScopeAt(new SourcePosition(1, 9)));
        Assert.Same(later, model.FindScopeAt(new SourcePosition(2, 1)));
        Assert.Same(root, model.FindScopeAt(new SourcePosition(2, 3)));
        Assert.Same(root, model.FindScopeAt(new SourcePosition(9, 1)));
        AssertEveryGridPositionSelectsTheScansScope(model);
    }

    [Fact]
    public void OverlappingHulls_PreferTheDeeperScope_ThenTheLaterStart_ThenTheEarlierEnd()
    {
        var root = Root();
        var wide = Scope(new SourceSpan(1, 1, 1, 12), 1, "Wide");
        var overlap = Scope(new SourceSpan(1, 5, 1, 14), 1, "Overlap");
        var prefix = Scope(new SourceSpan(1, 5, 1, 8), 1, "Prefix");
        var shallowInner = Scope(new SourceSpan(1, 9, 1, 10), 0, "ShallowInner");
        var deepOuter = Scope(new SourceSpan(2, 1, 3, 1), 3, "DeepOuter");
        var shallowerInner = Scope(new SourceSpan(2, 3, 2, 5), 2, "ShallowerInner");
        var model = ModelWith(wide, overlap, prefix, shallowInner, root, deepOuter, shallowerInner);

        Assert.Same(wide, model.FindScopeAt(new SourcePosition(1, 4)));
        // At equal depth the later start wins, and of equal starts the earlier end.
        Assert.Same(prefix, model.FindScopeAt(new SourcePosition(1, 5)));
        Assert.Same(overlap, model.FindScopeAt(new SourcePosition(1, 8)));
        // Depth comes first: a shallower hull inside a deeper one never wins.
        Assert.Same(overlap, model.FindScopeAt(new SourcePosition(1, 9)));
        Assert.Same(overlap, model.FindScopeAt(new SourcePosition(1, 13)));
        Assert.Same(deepOuter, model.FindScopeAt(new SourcePosition(2, 3)));
        Assert.Same(root, model.FindScopeAt(new SourcePosition(1, 14)));
        AssertEveryGridPositionSelectsTheScansScope(model);
    }

    [Fact]
    public void IdenticalHulls_TheDeeperScopeWins_InEitherListingOrder()
    {
        var span = new SourceSpan(1, 2, 1, 6);
        var outer = Scope(span, 1, "Outer");
        var inner = Scope(span, 2, "Inner");
        var position = new SourcePosition(1, 3);

        Assert.Same(inner, ModelWith(outer, inner, Root()).FindScopeAt(position));
        Assert.Same(inner, ModelWith(inner, outer, Root()).FindScopeAt(position));
        AssertEveryGridPositionSelectsTheScansScope(ModelWith(Root(), outer, inner));
        AssertEveryGridPositionSelectsTheScansScope(ModelWith(inner, Root(), outer));
    }

    [Fact]
    public void IdenticalHullsAtOneDepth_TheFirstListedWins()
    {
        var span = new SourceSpan(1, 2, 2, 3);
        var first = Scope(span, 1, "First");
        var second = Scope(span, 1, "Second");
        var third = Scope(span, 1, "Third");
        var position = new SourcePosition(1, 7);

        Assert.Same(first, ModelWith(Root(), first, second, third).FindScopeAt(position));
        Assert.Same(third, ModelWith(third, Root(), first, second).FindScopeAt(position));
        Assert.Same(second, ModelWith(second, third, first, Root()).FindScopeAt(position));
        // One instance listed twice is one scope.
        Assert.Same(second, ModelWith(Root(), second, first, second).FindScopeAt(position));
        AssertEveryGridPositionSelectsTheScansScope(ModelWith(Root(), second, first, third, second));
    }

    [Fact]
    public void ZeroWidthAndDefaultHulls_ContainNothing()
    {
        var root = Root();
        var empty = Scope(new SourceSpan(1, 3, 1, 3), 5, "Empty");
        var defaulted = Scope(default(SourceSpan), 5, "Default");
        var real = Scope(new SourceSpan(1, 3, 1, 5), 1, "Real");
        var model = ModelWith(empty, defaulted, root, real);

        Assert.Same(real, model.FindScopeAt(new SourcePosition(1, 3)));
        Assert.Same(root, model.FindScopeAt(new SourcePosition(1, 2)));
        Assert.Same(root, model.FindScopeAt(new SourcePosition(1, 5)));
        Assert.Same(root, model.FindScopeAt(default));
        Assert.Equal(2, model.ScopeIndexIntervals);
        AssertEveryGridPositionSelectsTheScansScope(model);

        // With only empty hulls there is nothing to index, and every position is the root's.
        var onlyEmpty = ModelWith(empty, root, defaulted);
        Assert.Equal(0, onlyEmpty.ScopeIndexIntervals);
        Assert.Same(root, onlyEmpty.FindScopeAt(new SourcePosition(1, 3)));
        AssertEveryGridPositionSelectsTheScansScope(onlyEmpty);
    }

    [Fact]
    public void RootFallback_IsTheFirstSpanlessScope_ElseAFreshEmptyScope()
    {
        var first = Root("First");
        var second = Root("Second");
        var nested = Scope(new SourceSpan(2, 1, 2, 4), 1, "Nested");
        var model = ModelWith(nested, first, second);
        Assert.Same(first, model.FindScopeAt(new SourcePosition(1, 1)));
        Assert.Same(nested, model.FindScopeAt(new SourcePosition(2, 1)));
        AssertEveryGridPositionSelectsTheScansScope(model);

        // A spanless scope at any depth is the root: the scan takes the first one listed.
        var deepSpanless = Scope(null, 3, "DeepSpanless");
        Assert.Same(deepSpanless, ModelWith(nested, deepSpanless, first).FindScopeAt(new SourcePosition(1, 1)));

        // Without a spanless scope, a position outside every region gets a fresh empty scope, as
        // with no scopes at all; one inside a region still gets the region.
        var rootless = ModelWith(nested);
        Assert.Same(nested, rootless.FindScopeAt(new SourcePosition(2, 2)));
        AssertEveryGridPositionSelectsTheScansScope(rootless);
        AssertEveryGridPositionSelectsTheScansScope(ModelWith());

        // A model built without a scope listing has one empty root.
        var unlisted = new SemanticModel(
            HostRoot, [], [], [], [], new Dictionary<DeclarationOccurrence, PropertyInfo>(ReferenceEqualityComparer.Instance));
        Assert.Same(Assert.Single(unlisted.ScopeVisibilities), unlisted.FindScopeAt(new SourcePosition(1, 1)));
    }

    /// <summary>
    /// The internal constructor accepts a listing with a null entry, which no builder model has;
    /// the index refuses it and the query keeps the scan, which throws as it always did.
    /// </summary>
    [Fact]
    public void NullEntry_KeepsTheScan()
    {
        var model = ModelWith(Root(), null!, Scope(new SourceSpan(1, 1, 1, 3), 1));
        Assert.Equal(-1, model.ScopeIndexIntervals);
        Assert.Throws<NullReferenceException>(() => model.FindScopeAt(new SourcePosition(1, 1)));
    }

    /// <summary>
    /// Seeded random listings — spanless, default, zero-width, single- and multi-line hulls,
    /// repeated hulls and repeated instances, depths 0–3, in the builder's order or shuffled —
    /// select the scan's scope at every grid position.
    /// </summary>
    [Fact]
    public void RandomListings_SelectTheScansScope()
    {
        var random = new Random(20261120);
        var nestedSelections = 0;
        var freshFallbacks = 0;
        for (var round = 0; round < 2_000; round++)
        {
            var scopes = new List<ScopeVisibility>();
            var count = random.Next(0, 14);
            for (var i = 0; i < count; i++)
            {
                var depth = random.Next(0, 4);
                scopes.Add(random.Next(10) switch
                {
                    0 => Scope(null, depth, $"s{i}"),
                    1 when scopes.Count > 0 => scopes[random.Next(scopes.Count)],
                    2 when scopes.Count > 0 && scopes[random.Next(scopes.Count)].Span is { } tied => Scope(tied, depth, $"s{i}"),
                    _ => Scope(RandomSpan(random), depth, $"s{i}"),
                });
            }

            var listing = random.Next(3) == 0
                ? scopes.OrderBy(_ => random.Next()).ToArray()
                : scopes
                    .OrderBy(static scope => scope.Span is null ? 0 : 1)
                    .ThenBy(static scope => scope.NestingDepth)
                    .ThenBy(static scope => scope.Span?.Start)
                    .ThenBy(static scope => scope.Span?.End)
                    .ToArray();
            var model = ModelWith(listing);
            AssertIndexIsBoundedByTheHulls(model);
            foreach (var position in Grid(8, 11))
            {
                if (AssertSelectsTheScansScope(model, position))
                    nestedSelections++;
                else if (!Listed(model, model.FindScopeAt(position)))
                    freshFallbacks++;
            }
        }

        output.WriteLine($"nested selections: {nestedSelections}, fresh fallbacks: {freshFallbacks}");
        Assert.True(nestedSelections > 10_000 && freshFallbacks > 1_000, $"both selections and fallbacks must be exercised ({nestedSelections} / {freshFallbacks})");
    }

    private static SourceSpan RandomSpan(Random random)
    {
        if (random.Next(30) == 0)
            return default;

        var startLine = random.Next(1, 7);
        var startColumn = random.Next(1, 9);
        if (random.Next(5) == 0)
            return new SourceSpan(startLine, startColumn, startLine, startColumn);
        if (random.Next(4) == 0)
            return new SourceSpan(startLine, startColumn, startLine + random.Next(1, 3), random.Next(1, 9));
        return new SourceSpan(startLine, startColumn, startLine, startColumn + random.Next(1, 6));
    }

    // ── Cost ─────────────────────────────────────────────────────────────────────────────

    /// <summary>Host listings of <paramref name="scopes"/> nested regions under one root, in the shape a cost test needs.</summary>
    private static ScopeVisibility[] Shaped(string shape, int scopes)
    {
        var listing = new ScopeVisibility[scopes + 1];
        listing[0] = new ScopeVisibility(null, [], 0);
        for (var i = 0; i < scopes; i++)
        {
            listing[i + 1] = shape switch
            {
                // Disjoint siblings, one per line.
                "wide" => new ScopeVisibility(new SourceSpan(i + 1, 3, i + 1, 9), [], 1),
                // Each region strictly inside the one before, one level deeper.
                "nested" => new ScopeVisibility(new SourceSpan(i + 1, 1, (2 * scopes) - i, 1), [], i + 1),
                // One hull at one depth, listed again and again.
                "tied" => new ScopeVisibility(new SourceSpan(1, 1, 2, 1), [], 1),
                // One hull at ever smaller depths.
                "tied-depths" => new ScopeVisibility(new SourceSpan(1, 1, 2, 1), [], scopes - i),
                // Overlapping, never nested, at one depth.
                "staircase" => new ScopeVisibility(new SourceSpan(i + 1, 1, i + 1 + scopes, 1), [], 1),
                _ => throw new ArgumentOutOfRangeException(nameof(shape), shape, null),
            };
        }

        return listing;
    }

    /// <summary>
    /// A query does not inspect every scope: 64 times as many sibling regions cost far less than
    /// 64 times as much. Measured 2026-11-20 (Release, tiering off): the binary search 54 ns over
    /// 4,096 siblings and 66 ns over 65,536, the former scan 19 µs and 314 µs. The 16-times bound
    /// is generous and the best of five runs is compared, so it is not a microbenchmark.
    /// </summary>
    [Fact]
    public void ScopeQueryCost_GrowsSublinearlyWithTheSiblingCount()
    {
        static (SemanticModel Model, SourcePosition[] Queries) Siblings(int scopes)
        {
            var model = ModelWith(Shaped("wide", scopes));
            // Hits and root fallbacks over the whole listing, in document order as an editor sweep issues them.
            var queries = new SourcePosition[8_192];
            for (var q = 0; q < queries.Length; q++)
                queries[q] = new SourcePosition(1 + (int)((long)q * scopes / queries.Length), q % 2 == 0 ? 4 : 1);
            return (model, queries);
        }

        static double BestMilliseconds(SemanticModel model, SourcePosition[] queries)
        {
            var root = model.ScopeVisibilities[0];
            var best = double.MaxValue;
            for (var run = 0; run < 5; run++)
            {
                var nested = 0;
                var watch = Stopwatch.StartNew();
                foreach (var query in queries)
                {
                    if (!ReferenceEquals(model.FindScopeAt(query), root))
                        nested++;
                }

                watch.Stop();
                Assert.Equal(queries.Length / 2, nested);
                best = Math.Min(best, watch.Elapsed.TotalMilliseconds);
            }

            return best;
        }

        var (small, smallQueries) = Siblings(512);
        var (large, largeQueries) = Siblings(32_768);
        _ = BestMilliseconds(small, smallQueries);
        var smallTime = BestMilliseconds(small, smallQueries);
        var largeTime = BestMilliseconds(large, largeQueries);
        output.WriteLine($"8,192 queries: {smallTime:F3} ms over 512 scopes, {largeTime:F3} ms over 32,768 scopes");
        Assert.True(
            largeTime < 16 * Math.Max(smallTime, 0.05),
            $"64 times the scopes made the queries {largeTime / smallTime:F1} times slower ({smallTime:F3} -> {largeTime:F3} ms).");
    }

    /// <summary>
    /// Building the index scales with the scopes whatever their shape. The test counts the
    /// builder's work, not its time: <see cref="SemanticModel.ScopeIndexBuildSteps"/> is the number
    /// of candidate comparisons and expiry checks the sweep made, the same on every run of a
    /// listing. 16 times as many nested, tied, overlapping or sibling regions (2,048 to 32,768) took
    /// 16 to 22.1 times the steps, where S log₂ S predicts 21.8: about 2.4 S log₂ S steps at most
    /// for S hulls. The builds also allocated 16 times the bytes: about 76 bytes per scope for wide,
    /// nested and tied hulls, and 92 for the staircase. The bounds are 4 S log₂ S steps at each size,
    /// 32 times the steps and 20 times the bytes. The small listing is checked before the large one
    /// is built, so a quadratic sweep fails quickly. A sweep that rescans its active candidates at
    /// every boundary still selects the right scopes and allocates little, but it takes about S²
    /// steps on the nested and staircase listings and fails. Elapsed time is printed, not asserted:
    /// the full parallel suite measured time ratios of 70 to 144 for this unchanged work (64 was
    /// the former bound), and a reproduction with allocating threads in the same process showed
    /// collection pauses landing in the long builds and almost never in the short ones. Every
    /// listing indexes at most two intervals per hull.
    /// </summary>
    [Theory]
    [InlineData("wide")]
    [InlineData("nested")]
    [InlineData("tied")]
    [InlineData("tied-depths")]
    [InlineData("staircase")]
    public void IndexConstruction_ScalesWithTheScopes(string shape)
    {
        var dictionary = new Dictionary<DeclarationOccurrence, PropertyInfo>(ReferenceEqualityComparer.Instance);
        (long Steps, long Bytes, double Milliseconds, TimeSpan Paused, SemanticModel Model) Build(ScopeVisibility[] listing)
        {
            var steps = -1L;
            var bytes = long.MaxValue;
            var best = double.MaxValue;
            var paused = GC.GetTotalPauseDuration();
            SemanticModel? model = null;
            for (var run = 0; run < 4; run++)
            {
                var before = GC.GetAllocatedBytesForCurrentThread();
                var watch = Stopwatch.StartNew();
                model = new SemanticModel(HostRoot, [], [], [], [], dictionary, listing);
                watch.Stop();
                bytes = Math.Min(bytes, GC.GetAllocatedBytesForCurrentThread() - before);
                if (run == 0)
                {
                    steps = model.ScopeIndexBuildSteps;
                }
                else
                {
                    best = Math.Min(best, watch.Elapsed.TotalMilliseconds);
                    Assert.Equal(steps, model.ScopeIndexBuildSteps);
                }
            }

            return (steps, bytes, best, GC.GetTotalPauseDuration() - paused, model!);
        }

        // Each hull enters the sweep's queue once and leaves it at most once. PriorityQueue's
        // four-way heap compares about log₄ S times on the way in and 4 log₄ S on the way out
        // (2.5 log₂ S a hull; a binary heap would take 3), and each departure and each boundary
        // add at most one expiry check: 4 S log₂ S covers both. Every hull costs at least one
        // step, so a disconnected count fails too.
        static void AssertSweepStepsAreBounded(SemanticModel model, long steps)
        {
            var hulls = NonEmptyHulls(model);
            Assert.InRange(steps, hulls, 4L * hulls * (long)Math.Ceiling(Math.Log2(hulls)));
        }

        var small = Build(Shaped(shape, 2_048));
        AssertIndexIsBoundedByTheHulls(small.Model);
        AssertSweepStepsAreBounded(small.Model, small.Steps);
        var large = Build(Shaped(shape, 32_768));
        output.WriteLine(
            $"{shape}: {small.Steps:N0} -> {large.Steps:N0} steps ({(double)large.Steps / small.Steps:F2} times), "
            + $"{small.Bytes:N0} -> {large.Bytes:N0} B ({(double)large.Bytes / small.Bytes:F2} times); not asserted: "
            + $"{small.Milliseconds:F3} -> {large.Milliseconds:F3} ms (best of three), garbage collection paused the process "
            + $"{small.Paused.TotalMilliseconds:F1} -> {large.Paused.TotalMilliseconds:F1} ms during the four builds");

        AssertIndexIsBoundedByTheHulls(large.Model);
        AssertSweepStepsAreBounded(large.Model, large.Steps);
        Assert.True(
            large.Steps <= 32 * small.Steps,
            $"16 times the scopes made the build take {(double)large.Steps / small.Steps:F1} times the steps ({small.Steps:N0} -> {large.Steps:N0}).");
        Assert.True(
            large.Bytes < 20 * small.Bytes,
            $"16 times the scopes made the build allocate {(double)large.Bytes / small.Bytes:F1} times as much ({small.Bytes:N0} -> {large.Bytes:N0} B).");

        // Spot checks against the scan at hull starts, ends and midpoints.
        foreach (var scope in large.Model.ScopeVisibilities.Where(static (_, i) => i % 997 == 1))
        {
            var hull = scope.Span!.Value;
            AssertSelectsTheScansScope(large.Model, hull.Start);
            AssertSelectsTheScansScope(large.Model, hull.End);
            AssertSelectsTheScansScope(large.Model, new SourcePosition(hull.Start.Line, hull.Start.Column + 1));
        }
    }
}
