using static KatLang.PropertyDependencyGraphBuilder;

namespace KatLang.Tests;

/// <summary>
/// EMPTIED OWN SETS (November 27 2026; C# exposure implementation only, a runtime compatibility repair. No
/// classification, requirement, diagnostic kind, value or Lean rule changes). On .NET 11.0.0, <c>HashSet.UnionWith</c>
/// into an empty set copies a source with the same comparer through the runtime's internal copy, which assumes a new set
/// (dotnet/runtime #122952). A set emptied by <c>Remove</c> or <c>RemoveWhere</c> keeps its removed entries on its free
/// list, and the copy throws <see cref="IndexOutOfRangeException"/> when the source has many more buckets than entries
/// (dotnet/runtime #137834). Qualification emptied the required names in all three archived call paths. Removing an
/// owner's parameters can also empty the owner-qualified set. The three <c>Parser.Parse</c> failures reached
/// <c>SummarySeed.UnionOwnSets</c>: a share-shaped component's <c>AbsorbCompleted</c>, a member expansion's
/// <c>HoldMember</c>, and exposure settlement's fold of a qualified seed part (<c>SeedRequirements</c>). Each program
/// here is reduced from an archived record that threw (corpus program 17,283, cycle-dense level 6,420, narrow-chain
/// program 5,249). The repair clears an empty destination before the union, so the union leaves it exactly as it leaves a
/// new set. Oracles: a seam route that never unites into the emptied set where one exists, otherwise requirements and
/// values worked out by hand; for the unit matrix, the same union into a new seed.
/// </summary>
public sealed class SeedSetUnionCompatibilityTests
{
    private static string Value(string source) => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString();

    private static string Metadata(string source) => ExposureSettlementFrameChargeTests.Metadata(SourceProvenance.ParseValid(source).Root);

    private static T With<T>(AsyncLocal<bool> seam, Func<T> work)
    {
        var previous = seam.Value;
        seam.Value = true;
        try { return work(); }
        finally { seam.Value = previous; }
    }

    private static void AssertRequires(Algorithm root, string[] path, params (string Name, int Depth)[] requirements)
        => ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, path), requirements);

    // ── The public paths that threw ─────────────────────────────────────────

    /// <summary>
    /// <c>M1</c> and <c>M2</c> form a share-shaped cycle, solved as one component: its seed qualifies <c>M2</c>'s own
    /// <c>p4</c> at <c>G</c>, which empties its name set, and then copies the small completed seed of <c>Base</c>, whose
    /// names <c>G</c> qualified all but <c>F</c>'s <c>p12</c>, <c>p13</c> and <c>p14</c>. No seam avoids this union,
    /// so the requirements and the value are worked out by hand: <c>M5 = N(p7) = 9 + 4</c>.
    /// </summary>
    [Fact]
    public void AComponentThatQualifiesItsOwnNamesAway_CopiesACompletedMember()
    {
        const string Source = """
            F(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14) = {
              G(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10) = {
                Lib = {
                }
                Base = p8, p13, p7, p6, p4, p9, p4, p14, p12
                N(z) = z + p6
                M1 = Base + M2 + Base
                M2 = M1 + p4
                M5 = N(p7)
                M5
              }
              G(8, 6, 5, 6, 9, 4, 9, 1, 5, 8)
            }
            F(8, 3, 1, 9, 7, 4, 5, 7, 1, 2, 7, 6, 9, 4)
            """;
        var root = SourceProvenance.ParseValid(Source).Root;
        foreach (var member in new[] { "Base", "M1", "M2" })
        {
            AssertRequires(root, ["F", "G", member],
                ("p12", 1), ("p13", 1), ("p14", 1), ("p4", 0), ("p6", 0), ("p7", 0), ("p8", 0), ("p9", 0));
        }
        AssertRequires(root, ["F", "G", "M5"], ("p6", 0), ("p7", 0));
        AssertRequires(root, ["F", "G", "N"], ("p6", 0));
        Assert.Equal("13", Value(Source));
    }

    /// <summary>
    /// <c>M4</c>, outside the cycle through <c>M3</c>, <c>M5</c>, <c>M13</c> and <c>M17</c>, reads two members (so it is no
    /// single-member share) and takes the full expansion that holds members: it qualifies its own <c>p4</c> at <c>G</c>
    /// first, which empties its name set, and then copies the small seed of the cycle member <c>M3</c>, whose names
    /// <c>G</c> qualified all but <c>F</c>'s <c>p9</c>. Oracle: copied member seeds, which qualify after the union
    /// (<see cref="PropertyDependencyGraphBuilder.MemberSeedsCopiedForTesting"/>); that route parsed this program before
    /// the repair. The output reads no cycle member: <c>M18 + M10 = 9 + 4</c>.
    /// </summary>
    [Fact]
    public void AnExpansionThatQualifiesItsOwnNamesAway_CopiesASmallMember()
    {
        const string Source = """
            F(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10) = {
              G(p1, p2, p3, p4, p5, p6, p7, p8) = {
                Lib = {
                }
                N(z) = z + p3
                public M19 = M3 + 7 + p6 + p3
                public M18 = p3
                M17 = M19 + p9 + M18 + M16
                public M16 = M3 + M7 + p3
                M15 = p1 + p8 + M13
                public M13 = M17 + M17 + p9 + 8
                public M11 = M9 + p2 + M13 + M1
                M10 = 4
                public M9 = p1 + M15
                M7 = p5 + M10 + M6
                public M6 = p6 + M5 + M9
                M5 = M13 + p6 + p5 + p6
                public M4 = M3 + p4 + N(p4)
                M3 = p6 + p4 + M5 + M11
                M1 = M5
                M18 + M10
              }
              G(3, 9, 9, 3, 2, 6, 1, 5)
            }
            F(1, 8, 8, 6, 3, 2, 4, 8, 7, 5)
            """;
        var metadata = Metadata(Source);
        Assert.Equal(metadata, With(MemberSeedsCopiedForTesting, () => Metadata(Source)));
        var root = SourceProvenance.ParseValid(Source).Root;
        foreach (var member in new[] { "M1", "M3", "M4", "M5", "M13", "M17", "M19" })
        {
            AssertRequires(root, ["F", "G", member],
                ("p1", 0), ("p2", 0), ("p3", 0), ("p4", 0), ("p5", 0), ("p6", 0), ("p8", 0), ("p9", 1));
        }
        AssertRequires(root, ["F", "G", "M18"], ("p3", 0));
        AssertRequires(root, ["F", "G", "M10"]);
        Assert.Equal("13", Value(Source));
    }

    /// <summary>
    /// <c>D3</c> reads <c>F.G.C.M16</c>. Exposure settlement qualifies the member's published seed part by part at
    /// <c>G</c> (QUALIFIED SEED PARTS, <c>SummarySeed.QualifiedOwnSets</c>): a part whose own names are all <c>G</c>'s
    /// parameters gets an empty name set, and reading its requirements (<c>SeedRequirements</c>) folds its qualified
    /// children into that set. Oracle: the former walks, which fold each seed whole before they qualify it
    /// (<see cref="PropertyExposureResolver.SeedPartsFoldedForTesting"/>, <see cref="PropertyExposureResolver.PathPartsFoldedForTesting"/>);
    /// both parsed this program before the repair. <c>R22</c> sums the chain to 172 and adds <c>Lib.X = p31 + 1</c>.
    /// </summary>
    [Fact]
    public void ASeedPartQualifiedEmpty_FoldsItsChildrenWhenItsRequirementsAreRead()
    {
        const string Source = """
            F(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35) = {
            G(q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16) = {
            Lib = {
            public X = p31 + 1
            }
            Q = { public Z = 3 }
            C = {
            public M1 = p12
            public M2 = M1 + q7
            public M3 = M2 + q1
            public M4 = M3 + p13 + q12
            public M5 = M4 + q5 + q11
            public M6 = M5 + p5
            public M7 = M6 + q14 + Q.Z
            public M8 = M7 + q5 + q12
            public M9 = M8 + q11
            public M10 = M9 + p23
            public M11 = M10 + q1
            public M12 = M11 + q7 + q3
            public M13 = M12 + p4 + p19
            public M14 = M13 + p34
            public M15 = M14 + q7 + q16
            public M16 = M15 + p31
            public M17 = M16 + q16
            public M18 = M17 + q13
            public M19 = M18 + q7 + q9
            public M20 = M19 + q14 + q16
            public M21 = M20 + q5
            public M22 = M21 + q1
            }
            R22 = C.M22 + Lib.X
            R22
            }
            G(9, 6, 9, 5, 8, 8, 1, 4, 2, 6, 6, 9, 5, 9, 9, 2)
            }
            D3 = F.G.C.M16
            F(5, 1, 8, 5, 4, 1, 7, 6, 7, 3, 9, 2, 6, 8, 6, 8, 4, 3, 8, 2, 2, 9, 9, 5, 9, 3, 4, 3, 9, 7, 1, 8, 3, 9, 1)
            """;
        var metadata = Metadata(Source);
        Assert.Equal(metadata, With(PropertyExposureResolver.SeedPartsFoldedForTesting, () => Metadata(Source)));
        Assert.Equal(metadata, With(PropertyExposureResolver.PathPartsFoldedForTesting, () => Metadata(Source)));
        var root = SourceProvenance.ParseValid(Source).Root;
        AssertRequires(root, ["F", "G", "C", "M16"],
            ("p12", 2), ("p13", 2), ("p19", 2), ("p23", 2), ("p31", 2), ("p34", 2), ("p4", 2), ("p5", 2),
            ("q1", 1), ("q11", 1), ("q12", 1), ("q14", 1), ("q16", 1), ("q3", 1), ("q5", 1), ("q7", 1));
        AssertRequires(root, ["F", "G", "C", "M1"], ("p12", 2));
        AssertRequires(root, ["F", "G", "Lib", "X"], ("p31", 2));
        AssertRequires(root, ["D3"]);
        Assert.Equal("174", Value(Source));
    }

    // ── Every own set, every union route ────────────────────────────────────

    public enum OwnSet { RequiredNames, VisibleNames, QualifiedParameters }

    public enum UnionRoute { UnionWith, AbsorbCompleted, HoldMember, Fold }

    public static TheoryData<OwnSet, UnionRoute> EveryOwnSetAndRoute()
    {
        var data = new TheoryData<OwnSet, UnionRoute>();
        foreach (var set in Enum.GetValues<OwnSet>())
            foreach (var route in Enum.GetValues<UnionRoute>())
                data.Add(set, route);
        return data;
    }

    private static Algorithm.User Owner() => new(null, [], [], [], new OutputBundle([]));

    // Twenty entries make a set whose storage outlives the three entries it keeps: the union source the runtime copies
    // entry by entry instead of copying its storage.
    private static readonly string[] Wide = [.. Enumerable.Range(0, 20).Select(i => $"n{i}")];
    private static readonly string[] Kept = ["n13", "n0", "n7"];

    private static HashSet<string> Removed() => new(Wide.Except(Kept), StringComparer.Ordinal);

    // A completed seed with three entries in the given set and nothing else, left by the removals production uses.
    private static SummarySeed SparseSource(OwnSet set, Algorithm owner)
    {
        switch (set)
        {
            case OwnSet.RequiredNames:
                var required = new SummarySeed(requiredAncestorOwnedParameterNames: Wide);
                required.RemoveRequiredAncestorOwnedParameterNames(Removed(), owner, ownerHasParameters: false, observations: null);
                return required;
            case OwnSet.VisibleNames:
                // Production never removes a visible name; a caller can, through the public accessor.
                var visible = new SummarySeed(visiblePropertyDependencyNames: Wide);
                foreach (var name in Removed())
                    visible.VisiblePropertyDependencyNames.Remove(name);
                return visible;
            default:
                var qualified = new SummarySeed(ownerQualifiedParameters: Wide.Select(name => new OwnerQualifiedParameter(name, owner)));
                qualified.RemoveRequiredAncestorOwnedParameterNames(Removed(), owner, ownerHasParameters: false, observations: null);
                return qualified;
        }
    }

    // The seed's set object itself (the public accessor, which folds what the seed holds) and its entries in order.
    private static System.Collections.IEnumerable SetOf(SummarySeed seed, OwnSet set) => set switch
    {
        OwnSet.RequiredNames => seed.RequiredAncestorOwnedParameterNames,
        OwnSet.VisibleNames => seed.VisiblePropertyDependencyNames,
        _ => seed.OwnerQualifiedParameters,
    };

    private static object[] EntriesOf(SummarySeed seed, OwnSet set) => [.. SetOf(seed, set).Cast<object>()];

    private static object ComparerOf(System.Collections.IEnumerable set) => set switch
    {
        HashSet<string> names => names.Comparer,
        HashSet<OwnerQualifiedParameter> parameters => parameters.Comparer,
        _ => throw new InvalidOperationException("Not an own set."),
    };

    private static void Unite(SummarySeed destination, SummarySeed source, UnionRoute route)
    {
        switch (route)
        {
            case UnionRoute.UnionWith:
                destination.UnionWith(source);
                break;
            case UnionRoute.AbsorbCompleted:
                // At most CopiedCompletedEntries entries: copied, not held.
                destination.AbsorbCompleted(source);
                Assert.Null(destination.AbsorbedPartsWithoutFolding);
                break;
            case UnionRoute.HoldMember:
                destination.HoldMember(source, observations: null);
                Assert.Null(destination.AbsorbedPartsWithoutFolding);
                break;
            default:
                // Held by reference, then folded by the first read.
                destination.AbsorbReference(source);
                Assert.NotNull(destination.AbsorbedPartsWithoutFolding);
                break;
        }
    }

    /// <summary>
    /// A seed's own set that the removals production uses emptied — qualification for the required names (<c>Remove</c>),
    /// the owner's strip for the owner-qualified parameters (<c>RemoveWhere</c>), and a caller through the public accessor
    /// for the visible names — receives a sparse completed seed by every route that unites own sets. The union completes
    /// and leaves the same entries in the same order as the union into a new seed. The destination keeps its set object
    /// and comparer, so a caller holding the set sees the result. The source is unchanged and shares no set.
    /// </summary>
    [Theory]
    [MemberData(nameof(EveryOwnSetAndRoute))]
    public void AUnionIntoAnOwnSetThatRemovalsEmptied_EqualsTheUnionIntoANewSeed(OwnSet set, UnionRoute route)
    {
        var owner = Owner();
        var source = SparseSource(set, owner);
        Assert.Equal(Kept.Length, source.OwnEntryCount);
        var sourceEntries = EntriesOf(source, set);

        var expected = new SummarySeed();
        Unite(expected, SparseSource(set, owner), route);
        Assert.Equal(sourceEntries, EntriesOf(expected, set));

        SummarySeed destination;
        switch (set)
        {
            case OwnSet.RequiredNames:
                destination = new SummarySeed(requiredAncestorOwnedParameterNames: ["a"]);
                _ = destination.RequiredAncestorOwnedParameterNames;
                destination.QualifyParameters(owner, new HashSet<string>(["a"], StringComparer.Ordinal), observations: null);
                break;
            case OwnSet.VisibleNames:
                destination = new SummarySeed(visiblePropertyDependencyNames: ["a"]);
                Assert.True(destination.VisiblePropertyDependencyNames.Remove("a"));
                break;
            default:
                destination = new SummarySeed(ownerQualifiedParameters: [new OwnerQualifiedParameter("a", owner)]);
                _ = destination.OwnerQualifiedParameters;
                destination.RemoveRequiredAncestorOwnedParameterNames(new HashSet<string>(["a"], StringComparer.Ordinal), owner,
                    ownerHasParameters: false, observations: null);
                break;
        }
        var emptied = SetOf(destination, set);
        Assert.Empty(emptied);
        var comparer = ComparerOf(emptied);
        Assert.Same(set == OwnSet.QualifiedParameters ? EqualityComparer<OwnerQualifiedParameter>.Default : StringComparer.Ordinal as object,
            comparer);

        Unite(destination, source, route);

        Assert.Equal(EntriesOf(expected, set), EntriesOf(destination, set));
        Assert.Same(emptied, SetOf(destination, set));
        Assert.Same(comparer, ComparerOf(emptied));
        Assert.NotSame(SetOf(source, set), emptied);
        Assert.Equal(sourceEntries, EntriesOf(source, set));
    }

    /// <summary>
    /// A nonempty destination keeps the ordinary runtime union's enumeration order, including reuse of a removed slot.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AUnionIntoANonemptyOwnSet_PreservesTheOrdinaryUnionOrder(bool removeMiddleEntry)
    {
        string[] initial = ["b", "middle", "a"];
        string[] incoming = ["c", "a", "d"];
        var expected = new HashSet<string>(initial, StringComparer.Ordinal);
        var destination = new SummarySeed(requiredAncestorOwnedParameterNames: initial);
        var names = destination.RequiredAncestorOwnedParameterNames;
        if (removeMiddleEntry)
        {
            Assert.True(expected.Remove("middle"));
            Assert.True(names.Remove("middle"));
        }

        expected.UnionWith(incoming);
        destination.UnionWith(new SummarySeed(requiredAncestorOwnedParameterNames: incoming));
        Assert.Same(names, destination.RequiredAncestorOwnedParameterNames);
        Assert.Equal(expected.ToArray(), names.ToArray());
    }
}
