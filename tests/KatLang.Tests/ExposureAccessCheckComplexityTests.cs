using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// The cost of charging the access checks a crossed transparent reference's target walk and the open
/// levels a lookup consults perform (owner decision 2026-11-13; <see cref="ExposureAccessCheckTests"/>).
/// A member-less reference chain <c>L0 = Lib.Sub</c>, <c>Lk = L(k-1)</c> read by one reader per link is
/// followed by a memoized loop (<c>SummaryMemo.ReferenceTerminal</c>, path-compressed): every link of the
/// chain is walked once over all of the readers, so the walk steps grow linearly with the chain, where
/// following each reader's chain anew would be quadratic. A level's open walks are settled as ONE
/// reference per level (<c>PendingSelection.OpenWalks</c>) that the run's settlement share keeps, so M
/// readers of M opened names cost linear settlement frames in M. Readers with BOUND OWNERS (their own
/// parameters, a parameterized block around them, a clause family) reuse one unbound settlement of the level's
/// walks too (C1, <c>PendingResolution.SharedOpenWalksLevel</c>), and the per-reader seam
/// (<see cref="PropertyExposureResolver.OpenWalksPerReaderForTesting"/>) shows the published metadata is the
/// unshared settlement's. Each oracle counts deterministic work
/// (<see cref="FrontEndTraversalObservations"/>), and classification is pinned exactly.
/// </summary>
public sealed class ExposureAccessCheckComplexityTests(ITestOutputHelper output)
{
    private static string ReferenceChain(int length)
    {
        var source = new System.Text.StringBuilder("F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n");
        source.Append("  L0 = Lib.Sub\n");
        for (var i = 1; i < length; i++) source.Append($"  L{i} = L{i - 1}\n");
        for (var i = 0; i < length; i++) source.Append($"  A{i} = L{i}.Q + 0\n");
        source.Append("  0\n}\nF(5)\n");
        return source.ToString();
    }

    private static string OpenList(int width)
    {
        var source = new System.Text.StringBuilder("F(y) = {\n  open ");
        source.Append(string.Join(", ", Enumerable.Range(0, width).Select(i => $"X{i}.Sub")));
        source.Append('\n');
        for (var i = 0; i < width; i++)
            source.Append($"  X{i} = {{\n    public Sub = {{\n      public Q{i} = 1\n      y\n    }}\n    0\n  }}\n");
        for (var i = 0; i < width; i++) source.Append($"  A{i} = Q{i} + 0\n");
        source.Append("  0\n}\nF(5)\n");
        return source.ToString();
    }

    private static (Algorithm.User Root, FrontEndTraversalObservations Observations) Exposed(string source)
    {
        var observations = new FrontEndTraversalObservations();
        return (ExposureOpenChainComplexityTests.Exposed(source, observations), observations);
    }

    private static void AssertEveryReaderRequiresY(Algorithm.User root, int count)
    {
        for (var i = 0; i < count; i++)
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"A{i}"), ("y", 0));
    }

    [Fact]
    public void MemberlessReferenceChain_EveryReaderIsCharged_AndTheWalkIsLinear()
    {
        var steps = new long[3];
        var lengths = new[] { 100, 200, 400 };
        for (var k = 0; k < lengths.Length; k++)
        {
            var (root, observations) = Exposed(ReferenceChain(lengths[k]));
            AssertEveryReaderRequiresY(root, lengths[k]);
            steps[k] = observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel);
        }

        // Linear: doubling the chain (and its readers) at most a little more than doubles the work. Following
        // every reader's chain anew costs N(N + 1) / 2 steps, a ratio near 4 at these sizes.
        Assert.InRange((double)steps[1] / steps[0], 1.5, 2.5);
        Assert.InRange((double)steps[2] / steps[1], 1.5, 2.5);
    }

    [Fact]
    public void OpenListReadByEveryProvidedName_SettlesInLinearFrames()
    {
        var frames = new long[3];
        var widths = new[] { 25, 50, 100 };
        for (var k = 0; k < widths.Length; k++)
        {
            var (root, observations) = Exposed(OpenList(widths[k]));
            AssertEveryReaderRequiresY(root, widths[k]);
            frames[k] = observations.RequiredAncestorSettlementFrames;
        }

        Assert.InRange((double)frames[1] / frames[0], 1.5, 2.5);
        Assert.InRange((double)frames[2] / frames[1], 1.5, 2.5);
    }

    // ── C1: one settlement of a level's open walks answers every reader, whatever its bound owners ─────────

    /// <summary>
    /// <see cref="OpenList"/> with every reader's declaration rewritten (each reader of the family reads <c>Q{i}</c>, or
    /// <c>X</c> for the unused-target family, through the open list of <c>F</c>).
    /// </summary>
    private static string OpenFamily(string family, int width)
    {
        var source = new System.Text.StringBuilder("F(y) = {\n  open ");
        if (family == "unused") source.Append("Other, ");
        source.Append(string.Join(", ", Enumerable.Range(0, width).Select(i => $"X{i}.Sub")));
        source.Append('\n');
        if (family == "unused") source.Append("  Other = {\n    public X = 1\n  }\n");
        for (var i = 0; i < width; i++)
            source.Append($"  X{i} = {{\n    public Sub = {{\n      public Q{i} = 1\n      y\n    }}\n    0\n  }}\n");
        for (var i = 0; i < width; i++)
            source.Append(family switch
            {
                "parameterized" => $"  A{i}(z) = Q{i} + 0\n",
                "block" => $"  B{i}(w) = {{\n    C(z) = Q{i} + 0\n    C(0)\n  }}\n",
                "clause" => $"  G{i}(0) = Q{i} + 0\n  G{i}(n) = n\n",
                "unused" => $"  A{i}(z) = X + 0\n",
                _ => throw new ArgumentOutOfRangeException(nameof(family)),
            });
        source.Append("  0\n}\nF(5)\n");
        return source.ToString();
    }

    private static void AssertFamilyMetadata(string family, Algorithm.User root, int width)
    {
        for (var i = 0; i < width; i++)
        {
            switch (family)
            {
                case "block":
                    ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"B{i}"), ("y", 0));
                    ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"B{i}", "C"), ("y", 1));
                    break;
                case "clause":
                    ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"G{i}"), ("y", 0));
                    break;
                default:
                    ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"A{i}"), ("y", 0));
                    break;
            }
        }
    }

    /// <summary>
    /// Readers with bound owners — their own parameter (the review's reproduction, formerly 2M² + 4M frames: 1,350,
    /// 5,200, 20,400), a parameterized block around the reader, a clause family, and readers of a name an unused-target
    /// level provides — settle a level's walks once between them: doubling the open list and its readers at most a
    /// little more than doubles the frames, and every reader keeps its classification.
    /// </summary>
    [Theory]
    [InlineData("parameterized")]
    [InlineData("block")]
    [InlineData("clause")]
    [InlineData("unused")]
    public void OpenListReadByReadersWithBoundOwners_SettlesInLinearFrames(string family)
    {
        var frames = new long[3];
        var widths = new[] { 25, 50, 100 };
        for (var k = 0; k < widths.Length; k++)
        {
            var (root, observations) = Exposed(OpenFamily(family, widths[k]));
            AssertFamilyMetadata(family, root, widths[k]);
            frames[k] = observations.RequiredAncestorSettlementFrames;
            var unshared = new FrontEndTraversalObservations();
            WithOpenWalks(true, () => ExposureOpenChainComplexityTests.Exposed(OpenFamily(family, widths[k]), unshared));
            output.WriteLine($"{family} width {widths[k]}: shared {frames[k]} frames, per-reader {unshared.RequiredAncestorSettlementFrames} frames");
        }

        Assert.InRange((double)frames[1] / frames[0], 1.5, 2.5);
        Assert.InRange((double)frames[2] / frames[1], 1.5, 2.5);
    }

    /// <summary>
    /// D nested levels, each with its own chargeable open and a parameterized reader of a name only the OUTERMOST
    /// level's open provides: every reader consults every level from its own outward. Each level's walks are computed
    /// once over all of the readers (a counter, not a ratio), and none is computed with a reader's bound owners.
    /// </summary>
    [Fact]
    public void NestedOpenLevels_EachLevelsWalksAreSettledOnce()
    {
        const int depth = 12;
        var source = new System.Text.StringBuilder("F(y) = {\n");
        for (var k = 0; k < depth; k++)
        {
            var indent = new string(' ', 2 * k + 2);
            source.Append($"{indent}open X{k}.Sub\n");
            source.Append($"{indent}X{k} = {{\n{indent}  public Sub = {{\n{indent}    public {(k == 0 ? "Q" : $"Q{k}")} = 1\n{indent}    y\n{indent}  }}\n{indent}  0\n{indent}}}\n");
            source.Append($"{indent}R{k}(z) = Q + 0\n");
            if (k + 1 < depth) source.Append($"{indent}N{k + 1} = {{\n");
        }
        for (var k = depth - 1; k >= 0; k--)
        {
            var indent = new string(' ', 2 * k + 2);
            source.Append($"{indent}0\n");
            if (k > 0) source.Append($"{new string(' ', 2 * k)}}}\n");
        }
        source.Append("}\nF(5)\n");

        var (root, observations) = Exposed(source.ToString());
        Algorithm level = ExposureOpenChainComplexityTests.Member(root, "F").Value;
        for (var k = 0; k < depth; k++)
        {
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(level, $"R{k}"), ("y", k));
            if (k + 1 < depth) level = ExposureOpenChainComplexityTests.Member(level, $"N{k + 1}").Value;
        }

        Assert.Equal(depth, observations.OpenWalksSettlements.Count);
        Assert.All(observations.OpenWalksSettlements.Values, count => Assert.Equal(1, count));
        Assert.Equal(0, observations.OpenWalksSettlementsWithBoundOwners);
    }

    /// <summary>
    /// The trap a share keyed by the level alone would fall into: <c>Mid</c>'s own reads of <c>Q</c> discharge
    /// <c>p</c> (<c>Mid</c> is a bound owner of its own summary), while the reader <c>A</c> inside <c>Mid</c> keeps it.
    /// The level's walks anchor through <c>Lib</c>, which lies on both readers' chains, so each settles them itself.
    /// </summary>
    [Fact]
    public void OwnerOnTheTargetPath_KeepsTheDischargeOfEachReader()
    {
        const string source = "F(y) = {\n  open Lib.Mid.Sub\n  Lib = {\n    public Mid(p) = {\n      public Sub = {\n        public Q = 1\n        p\n      }\n      A(z) = Q + 0\n      A(0) + Q\n    }\n    0\n  }\n  Lib.Mid(5)\n}\nF(1)\n";
        foreach (var perReader in new[] { false, true })
        {
            var root = WithOpenWalks(perReader, () => ExposureOpenChainComplexityTests.Exposed(source, new FrontEndTraversalObservations()));
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", "Lib", "Mid"));
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", "Lib", "Mid", "A"), ("p", 0));
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", "Lib", "Mid", "Sub"), ("p", 0));
            // I25's eager charge of F's own dotted open: p has no owner on F's chain.
            var f = ExposureOpenChainComplexityTests.Member(root, "F");
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, f.Exposure);
            Assert.Equal(["p"], f.RequiredAncestorParameters);
        }
    }

    private static T WithOpenWalks<T>(bool perReader, Func<T> work)
    {
        var previous = PropertyExposureResolver.OpenWalksPerReaderForTesting.Value;
        PropertyExposureResolver.OpenWalksPerReaderForTesting.Value = perReader;
        try { return work(); }
        finally { PropertyExposureResolver.OpenWalksPerReaderForTesting.Value = previous; }
    }

    private static string MetadataOf(Algorithm root)
    {
        var lines = new List<string>();
        var pending = new Stack<(Algorithm Algorithm, string Path)>();
        pending.Push((root, "root"));
        while (pending.TryPop(out var item))
        {
            if (item.Algorithm is Algorithm.Conditional conditional)
            {
                for (var b = 0; b < conditional.Branches.Count; b++)
                    pending.Push((conditional.Branches[b].Body, $"{item.Path}#{b}"));
                continue;
            }

            IReadOnlyList<Property> properties = item.Algorithm switch
            {
                Algorithm.User user => user.Properties,
                Algorithm.Alias alias => alias.Properties,
                _ => [],
            };
            foreach (var property in properties)
            {
                var path = $"{item.Path}.{property.Name}";
                lines.Add($"{path}: {property.Exposure} [{string.Join(",", property.RequiredAncestorParameters)}] "
                    + string.Join(",", (property.CaptureRequirements ?? []).Select(r => r.ToString())));
                pending.Push((property.Value, path));
            }
        }

        return string.Join("\n", lines);
    }

    public static TheoryData<string> EquivalenceSources()
    {
        var data = new TheoryData<string>();
        foreach (var family in new[] { "parameterized", "block", "clause", "unused" })
            data.Add(OpenFamily(family, 6));
        data.Add(OpenList(6));
        data.Add("F(y) = {\n  open Lib.Mid.Sub\n  Lib = {\n    public Mid(p) = {\n      public Sub = {\n        public Q = 1\n        p\n      }\n      A(z) = Q + 0\n      A(0) + Q\n    }\n    0\n  }\n  Lib.Mid(5)\n}\nF(1)\n");
        data.Add("F(y) = {\n  open Lib.Mid.Sub, X.Sub\n  X = {\n    public Sub = {\n      public T = 1\n      y\n    }\n    0\n  }\n  Lib = {\n    public Mid(p) = {\n      public Sub = {\n        public Q = 1\n        p\n      }\n      A(z) = Q + T\n      B = { C(w) = Q + 0\n        C(1) }\n      A(0) + Q\n    }\n    0\n  }\n  R(z) = T + Q\n  Lib.Mid(5)\n}\nF(1)\n");
        data.Add("F(y) = {\n  open L, Other\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  Other = { public Z = 2 }\n  A(z) = Z + 0\n  N(w) = {\n    open M\n    M = Lib\n    B(v) = Q + Z\n    B(1)\n  }\n  N(1)\n}\nF(5)\n");
        return data;
    }

    /// <summary>
    /// The shared settlement publishes exactly the metadata of the unshared one (every reader settling the walks with
    /// its own bound owners), on the generated families and on programs whose walks anchor through a reader's chain.
    /// </summary>
    [Theory]
    [MemberData(nameof(EquivalenceSources))]
    public void SharedOpenWalks_PublishTheMetadataOfPerReaderSettlement(string source)
    {
        var shared = MetadataOf(WithOpenWalks(false, () => ExposureOpenChainComplexityTests.Exposed(source, new FrontEndTraversalObservations())));
        var perReader = MetadataOf(WithOpenWalks(true, () => ExposureOpenChainComplexityTests.Exposed(source, new FrontEndTraversalObservations())));
        Assert.Equal(perReader, shared);
    }

    /// <summary>A 2,000-link member-less chain settles on heap frames and a loop: a 1 MiB stack suffices.</summary>
    [Fact]
    public void DeepMemberlessReferenceChain_IsChargedOnAOneMebibyteStack()
    {
        const int length = 2000;
        var source = ReferenceChain(length);
        Algorithm.User? root = null;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(1024 * 1024,
            () => root = ExposureOpenChainComplexityTests.Exposed(source, new FrontEndTraversalObservations()));
        Assert.NotNull(root);
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root!, "F", $"A{length - 1}"), ("y", 0));
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root!, "F", $"L{length - 1}"), ("y", 0));
    }
}
