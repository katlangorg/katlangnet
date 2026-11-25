using System.Globalization;
using System.Reflection;
using System.Text;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// The semantic model builder's own work (editor tooling, no Lean counterpart): the scope-close
/// metadata-registration worklists, the deferred-module ownership read by deferred-reference walks,
/// and the cancellation checkpoints of the cancellable build.
///
/// <para>A shadowed unfinished entry is PARKED on the frame that shadows it and returns when that
/// frame's region closes, so the scopes closing inside the region no longer examine it again; a
/// level's deferred-module ownership is evaluated once, when its frame is created, and read from the
/// frame by every walk that crosses the level. Both are implementation-only: every model here is
/// compared, listing order and identities included, with the retained pre-parking reference
/// (<see cref="SemanticModelBuilder.VisibilityConstructionOptions.RescanReference"/>), which rescans
/// every unfinished entry at every close and re-evaluates every level a walk crosses. Registration
/// order is visible only where declaration spans tie, so the order tests tie every property
/// declaration of a host copy of the tree to one span. Work is asserted as deterministic counts,
/// never time.</para>
/// </summary>
public sealed class SemanticModelBuildWorkTests
{
    private static readonly SourceSpan TiedSpan = new(new SourcePosition(9000, 1), new SourcePosition(9000, 2));

    private const string MissingUrl = "https://katlang.org/missing.kat";
    private const string EagerUrl = "https://katlang.org/eager.kat";
    private const string DeferredUrl = "https://katlang.org/deferred.kat";

    // ── Shadowed metadata ────────────────────────────────────────────────

    [Fact]
    public void ShadowedDirectMetadata_IsExaminedOncePerShadowingRegion()
    {
        const int depth = 4, width = 32, siblings = 16;
        var (fewer, fewerReference) = Measure(Parse(DirectShadow(depth, width, siblings)));
        var (more, moreReference) = Measure(Parse(DirectShadow(depth, width, 2 * siblings)));

        // Each of the root's shadowed entries is parked once, on B, and returns when B closes.
        Assert.Equal(width, fewer.ScopeVisibilityMetadataParks);
        Assert.Equal(width, more.ScopeVisibilityMetadataParks);
        // A further scope closing inside B examines a few entries of its own, never the shadowed width...
        Assert.InRange(more.ScopeVisibilityMetadataEntries - fewer.ScopeVisibilityMetadataEntries, siblings, 8L * siblings);
        // ...which the rescanning reference examines again at every close.
        Assert.True(moreReference.ScopeVisibilityMetadataEntries - fewerReference.ScopeVisibilityMetadataEntries >= (long)width * siblings,
            $"reference {fewerReference.ScopeVisibilityMetadataEntries} -> {moreReference.ScopeVisibilityMetadataEntries}");
    }

    /// <summary>
    /// Opened entries: a direct name of an enclosing level beats the open for every scope of the opener
    /// (finished, never parked); a nearer open answers the name inside its own region (parked there); an
    /// ambiguous opener answers it the same way for every scope (registered once, then finished).
    /// </summary>
    [Theory]
    [InlineData("direct", false)]
    [InlineData("nearer", true)]
    [InlineData("ambiguous", false)]
    public void ShadowedOpenedMetadata_IsNotExaminedAgainAtEveryClose(string shadow, bool parks)
    {
        const int depth = 4, width = 32, siblings = 16;
        var (fewer, fewerReference) = Measure(Parse(OpenShadow(shadow, depth, width, siblings)));
        var (more, moreReference) = Measure(Parse(OpenShadow(shadow, depth, width, 2 * siblings)));

        Assert.Equal(parks ? width : 0, fewer.ScopeVisibilityMetadataParks);
        Assert.Equal(parks ? width : 0, more.ScopeVisibilityMetadataParks);
        Assert.InRange(more.ScopeVisibilityMetadataEntries - fewer.ScopeVisibilityMetadataEntries, siblings, 8L * siblings);
        Assert.True(moreReference.ScopeVisibilityMetadataEntries - fewerReference.ScopeVisibilityMetadataEntries >= (long)width * siblings,
            $"reference {fewerReference.ScopeVisibilityMetadataEntries} -> {moreReference.ScopeVisibilityMetadataEntries}");
    }

    public static TheoryData<string> LatePrograms => ["late-direct", "late-param", "late-open", "late-nearer"];

    /// <summary>
    /// An entry shadowed inside a region is registered at the first scope closing after that region, as
    /// before. Each program parks one entry whose members (<c>Inner.T0</c>'s <c>x</c>) nothing else
    /// registers before the walk reaches <c>Lib</c>, after <c>G</c>'s nested <c>h</c>: with every
    /// property declaration tied to one span, an entry that never returned, or returned late, would list
    /// <c>x</c> after <c>h</c>. The whole tied model equals the rescanning reference.
    /// </summary>
    [Theory]
    [MemberData(nameof(LatePrograms))]
    public void ReleasedEntries_RegisterAtTheFirstCloseAfterTheShadowingRegion(string program)
    {
        var tied = Tie(Parse(LateProgram(program)));
        var (observed, _) = Measure(tied);
        Assert.Equal(1, observed.ScopeVisibilityMetadataParks);

        var order = SemanticModelBuilder.Build(tied, observations: null).Declarations
            .Where(declaration => declaration.Span == TiedSpan).Select(declaration => declaration.Name).ToList();
        Assert.True(order.IndexOf("x") >= 0 && order.IndexOf("x") < order.IndexOf("h"), string.Join(' ', order));
    }

    /// <summary>
    /// Entries return in the order their shadowing regions close, not in declaration order: the first scope closing
    /// inside C parks A0 on C and A1 on B, and once C has closed, the next scope inside B parks A0 on B again (B's own
    /// A0 decides it there), so B returns A1 before A0. They are examined in declaration order again, so A0's member
    /// <c>x0</c> registers before A1's <c>x1</c>, exactly as in the reference.
    /// </summary>
    [Fact]
    public void ReturnedEntries_AreExaminedInDeclarationOrder()
    {
        const string source = "B = {\n  C = {\n    A0 = 0\n    D = {\n      d = 0\n      d + 1\n    }\n    A0 + 0\n  }\n  A0 = 0\n  A1 = 0\n"
            + "  F = {\n    f = 0\n    f + 1\n  }\n  0\n}\n"
            + "E = {\n  e = 0\n  e + 1\n}\nG = {\n  H = {\n    h = 0\n    h + 1\n  }\n  0\n}\nA0 = Lib.T0\nA1 = Lib.T1\n"
            + "Lib = {\n  Inner = {\n    T0 = {\n      x0 = 0\n      x0 + 1\n    }\n    T1 = {\n      x1 = 0\n      x1 + 1\n    }\n    0\n  }\n"
            + "  T0 = Inner.T0\n  T1 = Inner.T1\n  0\n}\nB + E + G + A0.x0 + A1.x1\n";
        var tied = Tie(Parse(source));
        var (observed, _) = Measure(tied);
        Assert.Equal(3, observed.ScopeVisibilityMetadataParks);

        var order = SemanticModelBuilder.Build(tied, observations: null).Declarations
            .Where(declaration => declaration.Span == TiedSpan).Select(declaration => declaration.Name).ToList();
        Assert.True(order.IndexOf("x0") >= 0 && order.IndexOf("x0") < order.IndexOf("x1") && order.IndexOf("x1") < order.IndexOf("h"),
            string.Join(' ', order));
    }

    /// <summary>The shadow shapes, tied: the parked registration order equals the reference's everywhere.</summary>
    [Theory]
    [InlineData("direct-shadow")]
    [InlineData("open-direct")]
    [InlineData("open-nearer")]
    [InlineData("open-ambiguous")]
    [InlineData("parameter-shadow")]
    public void TiedShadowShapes_KeepTheReferenceRegistrationOrder(string shape)
    {
        var source = shape switch
        {
            "direct-shadow" => DirectShadow(depth: 3, width: 4, siblings: 3),
            "open-direct" => OpenShadow("direct", depth: 3, width: 4, siblings: 3),
            "open-nearer" => OpenShadow("nearer", depth: 3, width: 4, siblings: 3),
            "open-ambiguous" => OpenShadow("ambiguous", depth: 3, width: 4, siblings: 3),
            _ => ParameterShadow(depth: 3, width: 4, siblings: 3),
        };
        var tied = Tie(Parse(source));
        _ = Measure(tied);
        Assert.True(SemanticModelBuilder.Build(tied, observations: null).Declarations.Count(declaration => declaration.Span == TiedSpan) > 8);
    }

    // ── Deferred-module ownership ────────────────────────────────────────

    /// <summary>
    /// <c>V</c> crosses every level of the chain to the level that owns the missing or deferred open
    /// (indeterminate there), <c>Q*</c> is answered by the innermost level's own resolved opens; the
    /// resolved control has no deferred open. A walk reads each level's ownership from its frame, so the
    /// evaluations are one per frame however many references cross the levels.
    /// </summary>
    [Theory]
    [InlineData("missing")]
    [InlineData("deferred")]
    [InlineData("resolved")]
    public async Task DeferredReferenceWalks_ReadEachLevelsOwnershipFromItsFrame(string control)
    {
        const int depth = 6, opens = 2;
        var (few, fewReference) = Measure(await ParseLookup(control, depth, opens, references: 2));
        var many = await ParseLookup(control, depth, opens, references: 32);
        var (observed, reference) = Measure(many);

        Assert.Equal(few.SemanticModelDeferredOpenChecks, observed.SemanticModelDeferredOpenChecks);
        Assert.Equal(observed.SemanticModelAlgorithmVisits, observed.SemanticModelDeferredOpenChecks);
        if (control == "resolved")
            Assert.Equal(observed.SemanticModelDeferredOpenChecks, reference.SemanticModelDeferredOpenChecks);
        else
            Assert.True(reference.SemanticModelDeferredOpenChecks - fewReference.SemanticModelDeferredOpenChecks >= 30L * depth,
                $"reference {fewReference.SemanticModelDeferredOpenChecks} -> {reference.SemanticModelDeferredOpenChecks}");

        var model = SemanticModelBuilder.Build(many);
        var q = model.FindResolutions("Q0").Where(static resolution => resolution.Occurrence.Kind == OccurrenceKind.ResolveReference).ToList();
        Assert.Equal(8, q.Count);
        Assert.All(q, resolution => Assert.Equal(IdentifierClassification.PropertyReference, resolution.Classification));
        var bottom = q[0].Occurrence.Span.Start.Line;
        var v = model.FindResolutions("V").Where(resolution => resolution.Occurrence.Kind == OccurrenceKind.ResolveReference
            && resolution.Occurrence.Span.Start.Line == bottom).ToList();
        Assert.Equal(16, v.Count);
        Assert.All(v, resolution => Assert.Equal(
            control == "resolved" ? IdentifierClassification.PropertyReference : IdentifierClassification.DeferredModuleReference,
            resolution.Classification));
    }

    /// <summary>The lookup shapes, tied, against the reference (registration order and classification together).</summary>
    [Theory]
    [InlineData("missing")]
    [InlineData("deferred")]
    [InlineData("resolved")]
    public async Task TiedLookupShapes_KeepTheReferenceModel(string control)
        => _ = Measure(Tie(await ParseLookup(control, depth: 3, opens: 2, references: 4)));

    // ── Cancellation ─────────────────────────────────────────────────────

    /// <summary>
    /// The cancellable build observes its token in the walk, metadata worklists, deferred-open
    /// analysis and scope emission (<see cref="FrontEndTraversalObservations.ObserveCancellation"/>). The hook
    /// cancels at one checkpoint BEFORE the token is read, so that checkpoint throws with the token and
    /// nothing runs after it: every counter stays where the hook saw it.
    /// </summary>
    [Theory]
    [InlineData(nameof(FrontEndCancellationCheckpoint.SemanticModelAlgorithm), 1)]
    [InlineData(nameof(FrontEndCancellationCheckpoint.SemanticModelAlgorithm), 20)]
    [InlineData(nameof(FrontEndCancellationCheckpoint.SemanticModelRow), 1)]
    [InlineData(nameof(FrontEndCancellationCheckpoint.SemanticModelRow), 12)]
    [InlineData(nameof(FrontEndCancellationCheckpoint.SemanticModelScope), 1)]
    [InlineData(nameof(FrontEndCancellationCheckpoint.SemanticModelScope), 10)]
    [InlineData(nameof(FrontEndCancellationCheckpoint.SemanticModelMetadata), 40)]
    [InlineData(nameof(FrontEndCancellationCheckpoint.SemanticModelDeferredOpen), 5)]
    [InlineData(nameof(FrontEndCancellationCheckpoint.SemanticModelDeferredLookup), 5)]
    public void Cancellation_AtABuilderCheckpoint_StopsThereWithTheToken(string kindName, long ordinal)
    {
        var kind = Enum.Parse<FrontEndCancellationCheckpoint>(kindName);
        var parsed = kind is FrontEndCancellationCheckpoint.SemanticModelDeferredLookup or FrontEndCancellationCheckpoint.SemanticModelDeferredOpen
            ? SourceProvenance.ParseAllowingDiagnostics(Lookup("missing", depth: 6, opens: 2, references: 32)).Parsed
            : Parse(DirectShadow(depth: 3, width: 8, siblings: 8));
        using var cancellation = new CancellationTokenSource();
        SortedDictionary<string, long>? atCancel = null;
        FrontEndTraversalObservations observations = null!;
        observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (reached, reachedOrdinal) =>
            {
                if (reached != kind || reachedOrdinal != ordinal || cancellation.IsCancellationRequested)
                    return;
                atCancel = Counters(observations);
                cancellation.Cancel();
            },
        };

        var error = Assert.Throws<OperationCanceledException>(
            () => SemanticModelBuilder.Build(parsed, observations, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.NotNull(atCancel);
        Assert.Equal(atCancel, Counters(observations));
        Assert.Equal(ordinal, observations.CancellationCheckpointsOf(kind));
    }

    [Fact]
    public void HoistedDeconstructionSource_RowsKeepTheirCancellationCheckpoint()
    {
        var parsed = Parse("a, b = (1, 2)\na");
        Assert.Contains(parsed.Root.Properties, property => property.Value is Algorithm.User { IsAssignmentDeconstructionSource: true });
        var rows = parsed.Root.Output.Count + parsed.Root.Properties.Sum(static property => property.Value.Output.Count);
        var observed = new FrontEndTraversalObservations();
        SemanticModelBuilder.Build(parsed, observed);
        Assert.Equal(rows, observed.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SemanticModelRow));
    }

    [Fact]
    public void LiveToken_ChangesNoModelContentOrWork()
    {
        var parsed = Parse(DirectShadow(depth: 3, width: 8, siblings: 8));
        var options = new SemanticModelBuilder.VisibilityConstructionOptions(
            PriorityOverride: static name => name is null ? 0 : StringComparer.Ordinal.GetHashCode(name));
        using var live = new CancellationTokenSource();
        var plain = new FrontEndTraversalObservations();
        var withToken = new FrontEndTraversalObservations();

        var expected = Dump(SemanticModelBuilder.Build(parsed, plain, options));
        var actual = Dump(SemanticModelBuilder.Build(parsed, withToken, options, live.Token));

        Assert.Equal(expected, actual);
        Assert.Equal(Counters(plain), Counters(withToken));
        foreach (var kind in new[] { FrontEndCancellationCheckpoint.SemanticModelAlgorithm, FrontEndCancellationCheckpoint.SemanticModelRow,
                     FrontEndCancellationCheckpoint.SemanticModelScope })
            Assert.True(withToken.CancellationCheckpointsOf(kind) > 0, kind.ToString());
    }

    // ── Builds ───────────────────────────────────────────────────────────

    /// <summary>Builds with parking and with the rescanning reference, requires the same model, returns both observers.</summary>
    private static (FrontEndTraversalObservations Parking, FrontEndTraversalObservations Reference) Measure(ParseResult parsed)
    {
        var parking = new FrontEndTraversalObservations();
        var reference = new FrontEndTraversalObservations();
        var model = SemanticModelBuilder.Build(parsed, parking);
        var referenceModel = SemanticModelBuilder.Build(parsed, reference,
            new SemanticModelBuilder.VisibilityConstructionOptions(RescanReference: true));
        Assert.Equal(Dump(referenceModel), Dump(model));
        return (parking, reference);
    }

    private static ParseResult Parse(string source) => SourceProvenance.ParseValid(source).Parsed;

    /// <summary>A host copy of the parse whose every property declaration (through property bodies, aliases and clause bodies) sits at <see cref="TiedSpan"/>.</summary>
    private static ParseResult Tie(ParseResult parsed)
    {
        var memo = new Dictionary<Algorithm, Algorithm>(ReferenceEqualityComparer.Instance);
        Property TieProperty(Property property) => property with { DeclarationSpans = [TiedSpan], Value = Of(property.Value) };
        Algorithm Of(Algorithm algorithm)
        {
            if (memo.TryGetValue(algorithm, out var known))
                return known;
            Algorithm tied = algorithm switch
            {
                Algorithm.User user => user with { Properties = user.Properties.Select(TieProperty).ToArray() },
                Algorithm.Alias alias => alias with { Properties = alias.Properties.Select(TieProperty).ToArray() },
                Algorithm.Conditional family => family with { Branches = family.Branches.Select(branch => branch with { Body = Of(branch.Body) }).ToArray() },
                _ => algorithm,
            };
            memo.Add(algorithm, tied);
            return tied;
        }

        return new ParseResult((Algorithm.User)Of(parsed.Root), parsed.Diagnostics);
    }

    private static async Task<ParseResult> ParseLookup(string control, int depth, int opens, int references)
    {
        var source = Lookup(control, depth, opens, references);
        if (control == "missing")
        {
            var parsed = SourceProvenance.ParseAllowingDiagnostics(source).Parsed;
            Assert.All(parsed.Diagnostics, diagnostic => Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, diagnostic.Code));
            return parsed;
        }

        var options = new RunOptions
        {
            DownloadCode = (url, _) => url == EagerUrl
                ? ValueTask.FromResult("public V = 5\npublic W = 6\nFee = 9")
                : throw new InvalidOperationException($"The model build must not fetch {url}."),
        };
        return (await SourceProvenance.ParseValidAsync(source, options)).Parsed;
    }

    /// <summary>
    /// Everything a model lists and answers, in listing order, with every occurrence, declaration, property,
    /// scope and visible symbol named by its first appearance: two builds of one tree agree exactly when their
    /// dumps do. Positions: every identifier site's start and end.
    /// </summary>
    private static string Dump(SemanticModel model)
    {
        var ids = new Dictionary<object, int>(ReferenceEqualityComparer.Instance);
        var text = new StringBuilder();
        string Id(object? value)
        {
            if (value is null)
                return "-";
            if (!ids.TryGetValue(value, out var id))
                ids.Add(value, id = ids.Count);
            return id.ToString(CultureInfo.InvariantCulture);
        }

        void Symbol(VisibleSymbol symbol)
        {
            text.Append(' ').Append(Id(symbol)).Append(':').Append(symbol.Name).Append('/').Append(symbol.Classification)
                .Append('/').Append(Id(symbol.Declaration)).Append('/').Append(Id(symbol.Property)).Append('[');
            foreach (var member in symbol.Members)
                text.Append(Id(member)).Append(':').Append(member.Name).Append('/').Append(member.Classification)
                    .Append('/').Append(Id(member.Declaration)).Append('/').Append(Id(member.Property)).Append(',');
            text.Append(']');
        }

        foreach (var occurrence in model.IdentifierOccurrences)
            text.Append("O ").Append(Id(occurrence)).Append(' ').Append(occurrence.Name).Append(' ').Append(occurrence.Span).Append(' ').Append(occurrence.Kind).Append('\n');
        foreach (var declaration in model.Declarations)
            text.Append("D ").Append(Id(declaration)).Append(' ').Append(declaration.Name).Append(' ').Append(declaration.Span).Append(' ').Append(declaration.Kind).Append('\n');
        foreach (var resolution in model.IdentifierResolutions)
            text.Append("R ").Append(Id(resolution)).Append(' ').Append(Id(resolution.Occurrence)).Append(' ').Append(resolution.Occurrence.Name)
                .Append(' ').Append(resolution.Occurrence.Span).Append(' ').Append(resolution.Classification).Append(' ')
                .Append(Id(resolution.ResolvedDeclaration)).Append(' ').Append(Id(resolution.ResolvedProperty)).Append('\n');
        foreach (var property in model.PropertyInfos)
            text.Append("P ").Append(Id(property)).Append(' ').Append(property.Name).Append(' ').Append(Id(property.Declaration)).Append(' ')
                .Append(property.Shape).Append(' ').Append(property.DisplaySignature).Append('\n');
        foreach (var scope in model.ScopeVisibilities)
        {
            text.Append("V ").Append(Id(scope)).Append(' ').Append(scope.Span).Append(' ').Append(scope.NestingDepth);
            foreach (var symbol in scope.Symbols)
                Symbol(symbol);
            text.Append('\n');
        }

        foreach (var position in model.IdentifierResolutions.SelectMany(static r => new[] { r.Occurrence.Span.Start, r.Occurrence.Span.End }).Distinct())
        {
            text.Append("Q ").Append(position).Append(' ').Append(Id(model.FindResolutionAt(position))).Append(' ')
                .Append(Id(model.FindPropertyAt(position))).Append(' ').Append(Id(model.FindScopeAt(position)));
            foreach (var symbol in model.GetVisibleSymbolsAt(position))
                Symbol(symbol);
            text.Append('\n');
        }

        return text.ToString();
    }

    /// <summary>Every public counter of an observer by name, and the checkpoints of each kind.</summary>
    private static SortedDictionary<string, long> Counters(FrontEndTraversalObservations observations)
    {
        var counters = new SortedDictionary<string, long>(StringComparer.Ordinal);
        foreach (var property in typeof(FrontEndTraversalObservations).GetProperties(BindingFlags.Instance | BindingFlags.Public))
        {
            if (property.PropertyType == typeof(long) || property.PropertyType == typeof(int))
                counters[property.Name] = Convert.ToInt64(property.GetValue(observations), CultureInfo.InvariantCulture);
        }

        foreach (var kind in Enum.GetValues<FrontEndCancellationCheckpoint>())
            counters["Checkpoints." + kind] = observations.CancellationCheckpointsOf(kind);
        return counters;
    }

    // ── Programs ─────────────────────────────────────────────────────────

    /// <summary>
    /// B redeclares the root's member-bearing <c>A*</c>, which follow it (a body the walk has entered has its members
    /// registered, so only a later body's metadata is still unfinished inside B); a chain of depth
    /// <paramref name="depth"/> inside B ends in <paramref name="siblings"/> sibling scopes.
    /// </summary>
    private static string DirectShadow(int depth, int width, int siblings)
    {
        var text = new StringBuilder("B = {\n");
        for (var i = 0; i < width; i++)
            text.Append(CultureInfo.InvariantCulture, $"  A{i} = {i}\n");
        Chain(text, depth, siblings);
        text.Append("  0\n}\n");
        for (var i = 0; i < width; i++)
            text.Append(CultureInfo.InvariantCulture, $"A{i} = {{\n  x = {i}\n  x + 1\n}}\n");
        return text.Append("B + 0\n").ToString();
    }

    /// <summary>B's explicit parameters shadow the root's later <c>A*</c> (a wrapper keeps B first in the walk).</summary>
    private static string ParameterShadow(int depth, int width, int siblings)
    {
        var parameters = string.Join(", ", Enumerable.Range(0, width).Select(i => $"A{i}"));
        var text = new StringBuilder($"S = {{\nB({parameters}) = {{\n");
        Chain(text, depth, siblings);
        text.Append("  A0 + 0\n}\nB(").Append(string.Join(", ", Enumerable.Range(0, width))).Append(")\n}\n");
        for (var i = 0; i < width; i++)
            text.Append(CultureInfo.InvariantCulture, $"A{i} = {{\n  x = {i}\n  x + 1\n}}\n");
        return text.Append("S + 0\n").ToString();
    }

    /// <summary>
    /// B opens the later Lib: <c>direct</c> declares Lib's names at the root, <c>nearer</c> opens Lib2 (the same names)
    /// in C inside B, <c>ambiguous</c> opens Lib and Lib2 together in B.
    /// </summary>
    private static string OpenShadow(string shadow, int depth, int width, int siblings)
    {
        var text = new StringBuilder();
        if (shadow == "direct")
        {
            for (var i = 0; i < width; i++)
                text.Append(CultureInfo.InvariantCulture, $"M{i} = {i}\n");
        }

        text.Append(shadow == "ambiguous" ? "B = {\n  open Lib, Lib2\n" : "B = {\n  open Lib\n");
        if (shadow == "nearer")
            text.Append("C = {\n  open Lib2\n");
        Chain(text, depth, siblings);
        if (shadow == "nearer")
            text.Append("  0\n}\n");
        text.Append("  0\n}\n");
        foreach (var library in shadow == "direct" ? new[] { "Lib" } : ["Lib", "Lib2"])
        {
            text.Append(library).Append(" = {\n");
            for (var i = 0; i < width; i++)
                text.Append(CultureInfo.InvariantCulture, $"  public M{i} = {{\n    y = {i}\n    y + 1\n  }}\n");
            text.Append("  0\n}\n");
        }

        return text.Append("B + 0\n").ToString();
    }

    private static void Chain(StringBuilder text, int depth, int siblings)
    {
        for (var level = 1; level <= depth; level++)
            text.Append(CultureInfo.InvariantCulture, $"L{level} = {{\n");
        for (var j = 0; j < siblings; j++)
            text.Append(CultureInfo.InvariantCulture, $"C{j} = {{\n  k = {j}\n  k + 1\n}}\n");
        for (var level = depth; level >= 1; level--)
            text.Append("  0\n}\n");
    }

    /// <summary>
    /// One parked entry each, whose member <c>x</c> lives one level down in Lib (so only Lib's own visit, after G's
    /// nested <c>h</c>, would register it): shadowed by B's property, by B's parameter, by C's property against B's
    /// open, and by C's nearer open of Lib2. E is the first scope to close after the shadowing region.
    /// </summary>
    private static string LateProgram(string program)
    {
        const string tail = "E = {\n  e = 0\n  e + 1\n}\nG = {\n  H = {\n    h = 0\n    h + 1\n  }\n  0\n}\n";
        static string Library(string extra)
            => "Lib = {\n" + extra + "  Inner = {\n    T0 = {\n      x = 0\n      x + 1\n    }\n    0\n  }\n  T0 = Inner.T0\n  0\n}\n";
        const string inner = "    D = {\n      d = 0\n      d + 1\n    }\n    M0 + 0\n  }\n";
        return program switch
        {
            "late-direct" => "B = {\n  A0 = 0\n  C = {\n    k = 0\n    k + 1\n  }\n  0\n}\n" + tail + "A0 = Lib.T0\n" + Library("")
                + "B + E + G + A0.x\n",
            "late-param" => "S = {\n  B(A0) = {\n    C = {\n      k = 0\n      k + 1\n    }\n    A0 + 0\n  }\n  B(1)\n}\n" + tail
                + "A0 = Lib.T0\n" + Library("") + "S + E + G + A0.x\n",
            "late-open" => "B = {\n  open Lib\n  C = {\n    M0 = 0\n" + inner + tail + "  M0 + 0\n}\n"
                + Library("  public M0 = Inner.T0\n") + "B + 0\n",
            "late-nearer" => "B = {\n  open Lib\n  C = {\n    open Lib2\n" + inner + tail + "  M0 + 0\n}\n"
                + Library("  public M0 = Inner.T0\n") + "Lib2 = {\n  public M0 = {\n    z = 0\n    z + 1\n  }\n  0\n}\nB + 0\n",
            _ => throw new ArgumentOutOfRangeException(nameof(program)),
        };
    }

    /// <summary>
    /// A chain R → L1 … L<paramref name="depth"/> whose every level opens <paramref name="opens"/> resolved providers
    /// (<c>P*.In</c>, supplying <c>Q*</c>), with <paramref name="references"/> alternating references to <c>V</c> and
    /// <c>Q*</c> at the bottom: <c>V</c> comes from the missing open's level (<c>missing</c>), from the eager module
    /// open outside a deferred branch whose body owns the deferred open (<c>deferred</c>), or from a resolved eager
    /// module (<c>resolved</c>).
    /// </summary>
    private static string Lookup(string control, int depth, int opens, int references)
    {
        var text = new StringBuilder();
        text.Append(control switch
        {
            "missing" => $"open '{MissingUrl}', Lib\n",
            _ => $"open '{EagerUrl}'\n",
        });
        for (var k = 0; k < opens; k++)
            text.Append(CultureInfo.InvariantCulture, $"P{k} = {{\n  public In = {{\n    public Q{k} = {k}\n    0\n  }}\n  0\n}}\n");
        if (control == "missing")
            text.Append("Lib = {\n  public V = 1\n  0\n}\n");
        text.Append(control == "deferred" ? $"F(0) = {{\n  open '{DeferredUrl}'\n" : "R = {\n");
        var providers = string.Join(", ", Enumerable.Range(0, opens).Select(k => $"P{k}.In"));
        for (var level = 1; level <= depth; level++)
            text.Append(CultureInfo.InvariantCulture, $"L{level} = {{\n  open {providers}\n");
        text.Append(string.Join(" + ", Enumerable.Range(0, references).Select(r => r % 2 == 0 ? "V" : $"Q{r / 2 % opens}"))).Append('\n');
        for (var level = depth; level >= 1; level--)
            text.Append(level == depth ? "}\n" : $"L{level + 1} + 0\n}}\n");
        return text.Append(control == "deferred" ? "L1 + Later\n}\nF(1) = V\nF(1)\n" : "L1 + 0\n}\nR + 0\n").ToString();
    }
}
