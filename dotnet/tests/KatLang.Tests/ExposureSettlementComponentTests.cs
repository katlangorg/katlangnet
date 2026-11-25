using System.Globalization;
using System.Text;

namespace KatLang.Tests;

using Mode = PropertyExposureResolver.SettlementShareMode;

/// <summary>
/// COMPONENT SETTLEMENTS (<c>PropertyExposureResolver.PendingResolution</c>, C# implementation only; Lean models no
/// exposure analysis). A settlement a cycle cut left partial used to be discarded, so every later meeting of its key
/// walked everything below it again: once per simple path through a component of mutually reading members. The
/// adversarial audit of 2026-11-21 (finding 5) measured that as exponential settlement frames, and a 377-byte valid,
/// terminating program refused by the static work bound. A partial settlement is now kept for its exact key while its
/// component is being settled, a later meeting of the key takes it and is cut where it was cut, and a seed reached recursively can
/// be settled by its component's verified union equations. Nothing partial is ever published.
///
/// <para>The oracles are deterministic work (<see cref="FrontEndTraversalObservations"/>), exact published metadata
/// against the former per-path walk (<see cref="PropertyExposureResolver.ComponentSettlementsPerPathForTesting"/>) at
/// every size that walk completes, an oracle written without any of the analysis (a member requires an enclosing
/// input exactly when a member it reaches reads it), and evaluation: two activations of an owner in ONE run must give
/// the values of two separate runs, which direct recursion computes. The independent classification
/// check also catches a wrong exposure that happens to give the expected values.</para>
///
/// <para>The frame bounds are linear in written reads for the ring and all-to-all families, including
/// parameterized members whose calls extend the bound-owner set. The per-path controls exercise contexts
/// where a direct union cannot answer and each owner-sensitive lookup must keep its exact key.</para>
/// </summary>
public sealed class ExposureSettlementComponentTests
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private sealed record Parsed(string Diagnostics, string Metadata, FrontEndTraversalObservations Observations, Algorithm Root);

    /// <summary>The eager parse of <paramref name="source"/>: per path (the former walk) or with component settlements.</summary>
    private static Parsed Parse(string source, bool perPath = false, Mode mode = Mode.Footprint)
    {
        var observations = new FrontEndTraversalObservations();
        var previousPath = PropertyExposureResolver.ComponentSettlementsPerPathForTesting.Value;
        var previousMode = PropertyExposureResolver.SettlementShareModeForTesting.Value;
        PropertyExposureResolver.ComponentSettlementsPerPathForTesting.Value = perPath;
        PropertyExposureResolver.SettlementShareModeForTesting.Value = mode;
        try
        {
            var parsed = Parser.ParseObserved(source, options: null, observations);
            var diagnostics = string.Join("\n", parsed.Diagnostics.Select(d => $"{d.Code}/{d.Severity}@{d.Span}"));
            return new(diagnostics, ExposureSettlementFrameChargeTests.Metadata(parsed.Root), observations, parsed.Root);
        }
        finally
        {
            PropertyExposureResolver.ComponentSettlementsPerPathForTesting.Value = previousPath;
            PropertyExposureResolver.SettlementShareModeForTesting.Value = previousMode;
        }
    }

    private static Parsed Clean(string source)
    {
        var parsed = Parse(source);
        Assert.Equal("", parsed.Diagnostics);
        return parsed;
    }

    private static string Display(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n");

    // ── Families ────────────────────────────────────────────────────────────

    private static IEnumerable<int> Next(int member, int size, int reads)
        => Enumerable.Range(1, reads).Select(step => (member + step) % size);

    /// <summary>
    /// <paramref name="size"/> libraries of one VALUE each, every one reading the next <paramref name="reads"/> through
    /// dotted paths or through opens. With an <paramref name="entry"/> they stand inside <c>O(x)</c> and the owner's
    /// input enters at that member; each is also read dotted (<c>C{i}</c>) and through an open (<c>A{i}</c>).
    /// </summary>
    internal static string ValueRing(int size, int reads, bool opened, int entry = -1)
    {
        var owner = entry >= 0;
        var indent = owner ? "    " : "";
        var source = new StringBuilder(owner ? "O(x) = {\n" : "");
        for (var i = 0; i < size; i++)
        {
            var targets = Next(i, size, reads).ToList();
            var value = string.Join(" + ", targets.Select(t => opened ? $"V{t}" : $"L{t}.V{t}")) + (i == entry ? " + x" : " + 1");
            source.Append(indent).Append($"L{i} = {{\n");
            if (opened)
                source.Append(indent).Append("    open ").AppendJoin(", ", targets.Select(t => $"L{t}")).Append('\n');
            source.Append(indent).Append($"    public V{i} = {value}\n").Append(indent).Append("}\n");
        }

        if (!owner)
            return source.Append("R = L0.V0\n1").ToString();
        for (var i = 0; i < size; i++)
            source.Append($"    A{i} = {{\n        open L{i}\n        V{i}\n    }}\n    C{i} = L{i}.V{i}\n");
        return source.Append("    1\n}\n1").ToString();
    }

    /// <summary>A terminating mutual recursion: each library's function calls the next <paramref name="reads"/>.</summary>
    internal static string FunctionRing(int size, int reads, bool opened)
    {
        var source = new StringBuilder();
        for (var i = 0; i < size; i++)
        {
            var targets = Next(i, size, reads).ToList();
            source.Append($"L{i} = {{\n");
            if (opened)
                source.Append("    open ").AppendJoin(", ", targets.Select(t => $"L{t}")).Append('\n');
            source.Append($"    public V{i}(n) = if(n < 1, 1, ")
                .AppendJoin(" + ", targets.Select(t => opened ? $"V{t}(n - 1)" : $"L{t}.V{t}(n - 1)")).Append(")\n}\n");
        }

        return source.Append("L0.V0(3)").ToString();
    }

    /// <summary>One library whose functions call two siblings through the library's own name.</summary>
    internal static string SelfPath(int size)
    {
        var source = new StringBuilder("Lib = {\n");
        for (var i = 0; i < size; i++)
            source.Append($"    public V{i}(n) = if(n < 1, 1, Lib.V{(i + 1) % size}(n - 1) + Lib.V{(i + 2) % size}(n - 1))\n");
        return source.Append("}\nLib.V0(3)").ToString();
    }

    /// <summary>Two libraries whose functions call two functions of the other, through opens or dotted paths.</summary>
    internal static string TwoLibraries(int size, bool opened)
    {
        var first = new StringBuilder("A = {\n" + (opened ? "    open B\n" : ""));
        var second = new StringBuilder("B = {\n" + (opened ? "    open A\n" : ""));
        var (a, b) = opened ? ("", "") : ("A.", "B.");
        for (var i = 0; i < size; i++)
        {
            first.Append($"    public A{i}(n) = if(n < 1, 1, {b}B{i}(n - 1) + {b}B{(i + 1) % size}(n - 1))\n");
            second.Append($"    public B{i}(n) = if(n < 1, 1, {a}A{(i + 1) % size}(n - 1) + {a}A{(i + 2) % size}(n - 1))\n");
        }

        return first.Append("}\n").Append(second).Append("}\nA.A0(3)").ToString();
    }

    /// <summary>A component whose every member reads EVERY other: values of one library, or one value per opened library.</summary>
    internal static string CompleteValues(int size, bool opened)
    {
        var source = new StringBuilder();
        if (!opened)
        {
            source.Append("Lib = {\n");
            for (var i = 0; i < size; i++)
                source.Append($"    public V{i} = ").AppendJoin(" + ", Enumerable.Range(0, size).Where(j => j != i).Select(j => $"Lib.V{j}")).Append(" + 1\n");
            return source.Append("}\nR = Lib.V0\n1").ToString();
        }

        for (var i = 0; i < size; i++)
        {
            var others = Enumerable.Range(0, size).Where(j => j != i).ToList();
            source.Append($"L{i} = {{\n    open ").AppendJoin(", ", others.Select(j => $"L{j}"))
                .Append($"\n    public V{i} = ").AppendJoin(" + ", others.Select(j => $"V{j}")).Append(" + 1\n}\n");
        }

        return source.Append("R = L0.V0\n1").ToString();
    }

    /// <summary>
    /// The audit's witness family: <paramref name="size"/> libraries, each function calling every other library's,
    /// through opens (4 libraries are the 377-byte program) or dotted paths.
    /// </summary>
    internal static string CompleteFunctions(int size, bool opened, int depth = 2)
    {
        var source = new StringBuilder();
        for (var i = 0; i < size; i++)
        {
            var others = Enumerable.Range(0, size).Where(j => j != i).ToList();
            if (opened)
                source.Append($"L{i} = {{\n  open ").AppendJoin(", ", others.Select(j => $"L{j}"))
                    .Append($"\n  public F{i}(n) = if(n < 1, 0, ").AppendJoin(" + ", others.Select(j => $"F{j}(n - 1)")).Append(")\n}\n");
            else
                source.Append($"L{i} = {{ public F{i}(n) = if(n < 1, 0, ").AppendJoin(" + ", others.Select(j => $"L{j}.F{j}(n - 1)")).Append(") }\n");
        }

        return source.Append($"L0.F0({depth})").ToString();
    }

    /// <summary>One library whose functions each call every sibling through the library's own name.</summary>
    internal static string SelfComplete(int size)
    {
        var source = new StringBuilder("Lib = {\n");
        for (var i = 0; i < size; i++)
            source.Append($"  public V{i}(n) = if(n < 1, 1, ").AppendJoin(" + ", Enumerable.Range(0, size).Where(j => j != i).Select(j => $"Lib.V{j}(n - 1)")).Append(")\n");
        return source.Append("}\nLib.V0(2)").ToString();
    }

    /// <summary>The acyclic twin of the dotted value ring: member i reads the next two only while they exist.</summary>
    private static string Dag(int size)
    {
        var source = new StringBuilder("O(x) = {\n");
        for (var i = 0; i < size; i++)
        {
            var targets = Enumerable.Range(i + 1, 2).Where(t => t < size).ToList();
            source.Append($"    L{i} = {{ public V{i} = {(targets.Count > 0 ? string.Join(" + ", targets.Select(t => $"L{t}.V{t}")) : "x")} + 1 }}\n");
        }

        return source.Append("    R = L0.V0\n    1\n}\nO(1)").ToString();
    }

    private static string Family(string family, int size) => family switch
    {
        "ring2" => ValueRing(size, 2, opened: false),
        "ring3" => ValueRing(size, 3, opened: false),
        "ring2-owner" => ValueRing(size, 2, opened: false, entry: 0),
        "open2" => ValueRing(size, 2, opened: true),
        "open3" => ValueRing(size, 3, opened: true),
        "open2-owner" => ValueRing(size, 2, opened: true, entry: 0),
        "fn2" => FunctionRing(size, 2, opened: false),
        "fn3" => FunctionRing(size, 3, opened: false),
        "fnopen2" => FunctionRing(size, 2, opened: true),
        "fnopen3" => FunctionRing(size, 3, opened: true),
        "selfpath" => SelfPath(size),
        "twolib-open" => TwoLibraries(size, opened: true),
        "twolib-dotted" => TwoLibraries(size, opened: false),
        "values-complete" => CompleteValues(size, opened: false),
        "values-complete-open" => CompleteValues(size, opened: true),
        "functions-complete" => CompleteFunctions(size, opened: false),
        "functions-complete-open" => CompleteFunctions(size, opened: true),
        "self-complete" => SelfComplete(size),
        _ => throw new ArgumentOutOfRangeException(nameof(family)),
    };

    // ── Frames: rings and other components of bounded reads ─────────────────

    /// <summary>
    /// Members that each read two or three others, through dotted paths and through opens, as values and as
    /// terminating functions, in one library, two or many: frames are linear in the members (the bounds include the charged
    /// discovery of the component) and double with them. Formerly the frames grew by the golden ratio
    /// squared for every two members of the plain ring (65 / 399 / 2,533 at 4 / 8 / 12 libraries), and the larger
    /// sizes here were refused by the static work bound.
    /// </summary>
    [Theory]
    [InlineData("ring2", 16)]
    [InlineData("ring3", 26)]
    [InlineData("ring2-owner", 22)]
    [InlineData("open2", 19)]
    [InlineData("open3", 28)]
    [InlineData("open2-owner", 32)]
    [InlineData("fn2", 21)]
    [InlineData("fn3", 33)]
    [InlineData("fnopen2", 31)]
    [InlineData("fnopen3", 51)]
    [InlineData("selfpath", 21)]
    [InlineData("twolib-open", 70)]
    [InlineData("twolib-dotted", 41)]
    public void ComponentsOfBoundedReads_SettleInLinearFrames(string family, int framesPerMember)
    {
        long previous = 0;
        foreach (var size in new[] { 8, 16, 32, 64 })
        {
            var parsed = Clean(Family(family, size));
            var frames = parsed.Observations.RequiredAncestorSettlementFrames;
            Assert.InRange(frames, size, (long)framesPerMember * size);
            if (previous > 0)
                Assert.InRange(frames, previous, previous * 22 / 10);
            previous = frames;
            Assert.True(parsed.Observations.SettlementComponentCompletions > 0);
        }
    }

    // ── Frames: dense components ────────────────────────────────────────────

    /// <summary>
    /// Every member reads EVERY other, so K members hold K(K − 1) reads. As values they settle in frames linear in
    /// those reads, including the work of discovering the component.
    /// Formerly 114 / 128,642 frames at 4 / 8 values of one library and a refusal from 12; 1,598 frames at 4 opened
    /// libraries and a refusal from 6.
    /// </summary>
    [Theory]
    [InlineData("values-complete", 5)]
    [InlineData("values-complete-open", 11)]
    public void DenseComponentsOfValues_SettleInFramesLinearInTheirReads(string family, int framesPerSquare)
    {
        long previous = 0;
        foreach (var size in new[] { 4, 8, 16, 32 })
        {
            var parsed = Clean(Family(family, size));
            var frames = parsed.Observations.RequiredAncestorSettlementFrames;
            Assert.InRange(frames, size, (long)framesPerSquare * size * size);
            // Doubling the members quadruples the reads.
            if (previous > 0)
                Assert.InRange(frames, previous, previous * 46 / 10);
            previous = frames;
            Assert.True(parsed.Observations.SettlementComponentCompletions > 0);
        }
    }

    [Theory]
    [InlineData(4, 65)]
    [InlineData(8, 229)]
    [InlineData(16, 845)]
    [InlineData(32, 3229)]
    public void DenseLibraryOfValues_CountsEverySettlementFrame(int size, long expected)
        => Assert.Equal(expected, Clean(CompleteValues(size, opened: false)).Observations.RequiredAncestorSettlementFrames);

    /// <summary>The audit's dense functions write K(K−1) calls. Doubling K roughly quadruples the
    /// calls. A repeated full walk per additional bound owner would grow faster than these bounds.</summary>
    [Theory]
    [InlineData("functions-complete-open", 12)]
    [InlineData("functions-complete", 5)]
    [InlineData("self-complete", 5)]
    public void DenseFunctions_SettleInFramesLinearInTheirWrittenCalls(string family, int framesPerSquare)
    {
        long previous = 0;
        foreach (var size in new[] { 4, 8, 16, 32 })
        {
            var parsed = Clean(Family(family, size));
            var frames = parsed.Observations.RequiredAncestorSettlementFrames;
            Assert.InRange(frames, size, (long)framesPerSquare * size * size);
            if (previous > 0)
                Assert.InRange(frames, previous, previous * 42 / 10);
            previous = frames;
            Assert.True(parsed.Observations.SettlementComponentCompletions > 0);
        }
    }

    /// <summary>
    /// The measured counts of the families above, pinned exactly at one size each so that a change of the rule shows:
    /// frames, meetings answered by a kept partial settlement, and requested seeds answered from the component equations.
    /// </summary>
    [Theory]
    [InlineData("ring2", 16, 240, 14, 1)]
    [InlineData("open2", 16, 290, 0, 17)]
    [InlineData("fn2", 16, 256, 0, 2)]
    [InlineData("fnopen2", 16, 352, 0, 17)]
    [InlineData("twolib-open", 8, 432, 0, 6)]
    [InlineData("values-complete-open", 8, 644, 0, 14)]
    [InlineData("functions-complete-open", 4, 184, 0, 6)]
    [InlineData("functions-complete", 8, 278, 0, 7)]
    public void MeasuredWork_IsExact(string family, int size, long frames, long reuses, long completions)
    {
        var observations = Clean(Family(family, size)).Observations;
        Assert.Equal(frames, observations.RequiredAncestorSettlementFrames);
        Assert.Equal(reuses, observations.SettlementComponentReuses);
        Assert.Equal(completions, observations.SettlementComponentCompletions);
    }

    [Fact]
    public void DownstreamMemberOutsideTheCycle_KeepsItsOwnRequirements()
    {
        const string source = """
            O(x) = {
                A = { public F(n) = if(n < 1, x, B.G(n - 1) + Tail.Leaf(n)) }
                B = { public G(n) = if(n < 1, 1, A.F(n - 1) + Tail.Leaf(n)) }
                Tail = { public Leaf(n) = Term.T(n) + 0 }
                Term = { public T(n) = n }
                A.F(2), Tail.Leaf(2)
            }
            O(3), O(7)
            """;
        var parsed = Clean(source);
        var owner = ExposureOpenChainComplexityTests.Member(parsed.Root, "O").Value;
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, "A", "F"), ("x", 1));
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, "B", "G"), ("x", 1));
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, "Tail", "Leaf"));
        Assert.Equal(Parse(source, perPath: true).Metadata, parsed.Metadata);
        Assert.True(parsed.Observations.SettlementComponentCompletions > 0);
        Assert.Equal(new[] { "6", "2", "10", "2" }, Numbers(Display(source)));
    }

    [Fact]
    public void CancellationAtAnyWitnessFrame_StopsBeforeAnotherIsCharged()
    {
        var expected = Clean(ReportWitness);
        for (long stop = 1; stop <= expected.Observations.RequiredAncestorSettlementFrames; stop++)
        {
            using var cancellation = new CancellationTokenSource();
            var observations = new FrontEndTraversalObservations();
            observations.RequiredAncestorSettlementObserver = _ =>
            {
                if (observations.RequiredAncestorSettlementFrames == stop)
                    cancellation.Cancel();
            };
            var options = new RunOptions { SourceProcessingCancellationToken = cancellation.Token };
            var error = Assert.ThrowsAny<OperationCanceledException>(() => Parser.ParseObserved(ReportWitness, options, observations));
            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.Equal(stop, observations.RequiredAncestorSettlementFrames);
        }

        Assert.Equal(expected.Metadata, Clean(ReportWitness).Metadata);
    }

    // ── The report's witness ────────────────────────────────────────────────

    /// <summary>The 377-byte program of the audit's finding 5, verbatim: valid, terminating, and formerly refused.</summary>
    internal const string ReportWitness = """
        L0 = {
          open L1, L2, L3
          public F0(n) = if(n < 1, 0, F1(n - 1) + F2(n - 1) + F3(n - 1))
        }
        L1 = {
          open L0, L2, L3
          public F1(n) = if(n < 1, 0, F0(n - 1) + F2(n - 1) + F3(n - 1))
        }
        L2 = {
          open L0, L1, L3
          public F2(n) = if(n < 1, 0, F0(n - 1) + F1(n - 1) + F3(n - 1))
        }
        L3 = {
          open L0, L1, L2
          public F3(n) = if(n < 1, 0, F0(n - 1) + F1(n - 1) + F2(n - 1))
        }
        L0.F0(2)
        """;

    /// <summary>
    /// The witness is accepted (formerly <see cref="DiagnosticCode.StaticStructureLimitExceeded"/> after its work
    /// bound, 484,352 units) and evaluates: every base case is 0, so the call is 0. Every member is exported.
    /// </summary>
    [Fact]
    public void ReportWitness_IsAccepted_AndEvaluates()
    {
        var source = ReportWitness.ReplaceLineEndings("\n");
        Assert.Equal(377, Encoding.UTF8.GetByteCount(source) + 1);
        Assert.Equal(source, CompleteFunctions(4, opened: true));
        var parsed = Clean(source);
        Assert.Equal(184, parsed.Observations.RequiredAncestorSettlementFrames);
        for (var i = 0; i < 4; i++)
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(parsed.Root, $"L{i}", $"F{i}"));
        Assert.Equal("0", Display(source));
        // With a base case that counts, the same recursion has a value to get wrong: 3 calls, each of 3 base cases.
        Assert.Equal("9", Display(source.Replace("if(n < 1, 0,", "if(n < 1, 1,", StringComparison.Ordinal)));
    }

    /// <summary>
    /// The other small programs the audit's verifiers found refused: one library of 5 functions calling each other
    /// (485 bytes), 5 libraries through dotted calls, one library of 16 functions each calling two siblings (1 KB),
    /// and two libraries of 8 functions opening each other. Each parses clean and evaluates.
    /// </summary>
    [Theory]
    [InlineData("self-complete", 5, "16")]
    [InlineData("functions-complete", 5, "0")]
    [InlineData("selfpath", 16, "8")]
    [InlineData("twolib-open", 8, "8")]
    [InlineData("fnopen2", 8, "8")]
    [InlineData("fn2", 16, "8")]
    public void FormerlyRefusedPrograms_ParseCleanAndEvaluate(string family, int size, string value)
    {
        var source = Family(family, size);
        Clean(source);
        Assert.Equal(value, Display(source));
    }

    // ── Classification: the former walk ─────────────────────────────────────

    /// <summary>
    /// At every size the per-path walk completes quickly, component settlements publish the metadata it publishes
    /// (every property's exposure, required inputs and capture positions), in the three share modes. A small cycle may spend more
    /// frames discovering the equations than it saves. The growth tests count all discovery frames.
    /// </summary>
    [Theory]
    [InlineData("ring2", 4, 10)]
    [InlineData("ring3", 4, 8)]
    [InlineData("ring2-owner", 3, 8)]
    [InlineData("open2", 4, 8)]
    [InlineData("open3", 4, 5)]
    [InlineData("open2-owner", 3, 6)]
    [InlineData("fn2", 4, 8)]
    [InlineData("fn3", 4, 5)]
    [InlineData("fnopen2", 3, 5)]
    [InlineData("selfpath", 4, 8)]
    [InlineData("twolib-open", 2, 4)]
    [InlineData("twolib-dotted", 2, 4)]
    [InlineData("values-complete", 3, 6)]
    [InlineData("values-complete-open", 3, 4)]
    [InlineData("functions-complete", 3, 4)]
    [InlineData("functions-complete-open", 2, 3)]
    [InlineData("self-complete", 3, 4)]
    public void ComponentSettlements_PublishWhatThePerPathWalkPublishes(string family, int from, int to)
    {
        for (var size = from; size <= to; size++)
        {
            var source = Family(family, size);
            var perPath = Parse(source, perPath: true);
            Assert.Equal("", perPath.Diagnostics);
            Assert.Equal(0, perPath.Observations.SettlementComponentReuses);
            Assert.Equal(0, perPath.Observations.SettlementComponentCompletions);
            foreach (var mode in new[] { Mode.Footprint, Mode.ExactBoundOwners, Mode.Unshared })
            {
                var component = Parse(source, mode: mode);
                Assert.Equal(perPath.Diagnostics, component.Diagnostics);
                Assert.Equal(perPath.Metadata, component.Metadata);
                if (mode == Mode.Footprint)
                    Assert.InRange(component.Observations.RequiredAncestorSettlementFrames, 1,
                        perPath.Observations.RequiredAncestorSettlementFrames + component.Observations.SettlementComponentDiscoveryFrames);
            }
        }
    }

    /// <summary>
    /// The seam is the former walk: the plain ring's frames grow by the golden ratio squared per two libraries, and
    /// the all-to-all functions by far more, while component settlements take the linear counts.
    /// </summary>
    [Fact]
    public void PerPathWalk_TakesTheFormerFrames()
    {
        (int Size, long PerPath, long Component)[] ring = [(4, 65, 60), (8, 399, 120), (12, 2533, 180)];
        foreach (var (size, perPath, component) in ring)
        {
            var source = ValueRing(size, 2, opened: false);
            Assert.Equal(perPath, Parse(source, perPath: true).Observations.RequiredAncestorSettlementFrames);
            Assert.Equal(component, Parse(source).Observations.RequiredAncestorSettlementFrames);
        }

        Assert.Equal(519, Parse(CompleteFunctions(3, opened: true), perPath: true).Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(107, Parse(CompleteFunctions(3, opened: true)).Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(10910, Parse(CompleteFunctions(4, opened: false), perPath: true).Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(74, Parse(CompleteFunctions(4, opened: false)).Observations.RequiredAncestorSettlementFrames);
    }

    /// <summary>
    /// A program without a cycle cut keeps no partial settlement, so it is settled frame for frame as before: the
    /// acyclic twin of the ring, same-level recursion (no member read), and the opened and dotted chains.
    /// </summary>
    [Fact]
    public void ProgramsWithoutACycleCut_AreSettledAsBefore()
    {
        var sameLevel = string.Concat(Enumerable.Range(0, 16).Select(i => $"V{i}(n) = if(n < 1, 1, V{(i + 1) % 16}(n - 1) + V{(i + 2) % 16}(n - 1))\n")) + "V0(3)";
        string[] sources =
        [
            Dag(8), Dag(32), sameLevel,
            ExposureOpenChainComplexityTests.NestedOwnerChain(24),
            ExposureOpenChainComplexityTests.NestedOwnerChain(24, "dotted", last: "p"),
            ExposureSettlementFootprintTests.NestedOwnerBranchingChain(2, 12),
        ];
        foreach (var source in sources)
        {
            var component = Clean(source);
            var perPath = Parse(source, perPath: true);
            Assert.Equal(0, component.Observations.SettlementComponentReuses);
            Assert.Equal(0, component.Observations.SettlementComponentCompletions);
            Assert.Equal(perPath.Metadata, component.Metadata);
            Assert.Equal(perPath.Observations.RequiredAncestorSettlementFrames, component.Observations.RequiredAncestorSettlementFrames);
            Assert.Equal(perPath.Observations.SettlementShareStores, component.Observations.SettlementShareStores);
            Assert.Equal(perPath.Observations.SettlementShareHits, component.Observations.SettlementShareHits);
        }
    }

    // ── Classification: the owner's input entering a component ──────────────

    /// <summary>
    /// The owner's input enters at ONE member of a component whose members each read two others; whichever member it
    /// is, every member requires it one level up and every reader at the owner, read dotted and through an open. A
    /// meeting that took a kept partial settlement as if it were whole, or a member completed with less than its
    /// component's union, publishes one of them exported. This is the generalization of
    /// <see cref="ExposureSettlementShareTests.OpenedMemberRing_CycleCutResultsAreNeverShared"/> to keys met twice.
    /// </summary>
    [Theory]
    [InlineData(false, 3)]
    [InlineData(false, 5)]
    [InlineData(false, 8)]
    [InlineData(true, 3)]
    [InlineData(true, 5)]
    [InlineData(true, 8)]
    public void OwnerInputEnteringAtAnyMember_IsRequiredByEveryMemberAndReader(bool opened, int size)
    {
        for (var entry = 0; entry < size; entry++)
        {
            var observations = new FrontEndTraversalObservations();
            var owner = ExposureOpenChainComplexityTests.Member(
                ExposureOpenChainComplexityTests.Exposed(ValueRing(size, 2, opened, entry), observations), "O").Value;
            Assert.True(observations.SettlementComponentReuses + observations.SettlementComponentCompletions > 0);
            for (var i = 0; i < size; i++)
            {
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"L{i}", $"V{i}"), ("x", 1));
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"A{i}"), ("x", 0));
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"C{i}"), ("x", 0));
            }
        }
    }

    // ── Classification and values: the independent oracle ───────────────────

    /// <summary>
    /// Random libraries inside <c>O(x)</c>, inside <c>W(y)</c> around it, or at the root. Each member is a function
    /// (every read is live, the recursion ends at depth 0) or a value (forward reads are live, any member is read in a
    /// dead branch), and reads others through a dotted path, an open, an alias of the library, or an open of that
    /// alias. The oracle uses none of the analysis.
    /// </summary>
    private sealed class Libraries
    {
        public enum Wrapper { Owner, Nested, Root }
        public enum Via { Dotted, Open, AliasDotted, AliasOpen }
        public sealed record Read(int Target, Via Via, bool Live);

        public Wrapper Layout;
        public bool Functions;
        public (string Base, List<Read> Reads)[] Members = [];
        public const int Depth = 2;

        public static Libraries Create(int seed)
        {
            var random = new Random(seed);
            var size = 2 + random.Next(5);
            var program = new Libraries { Layout = (Wrapper)random.Next(3), Functions = random.Next(3) != 0, Members = new (string, List<Read>)[size] };
            var maxReads = 1 + random.Next(3);
            for (var i = 0; i < size; i++)
            {
                var roll = random.Next(size + 2);
                var constant = (i + 1).ToString(CultureInfo.InvariantCulture);
                var input = program.Layout == Wrapper.Root ? constant
                    : roll == 0 ? "x" : roll == 1 && program.Layout == Wrapper.Nested ? "y" : constant;
                var reads = new List<Read>();
                var seen = new HashSet<int>();
                for (var r = random.Next(maxReads + 1); r > 0; r--)
                {
                    var target = random.Next(size);
                    if (!seen.Add(target))
                        continue;
                    var via = (Via)random.Next(4);
                    reads.Add(new Read(target, via, program.Functions || target > i && random.Next(3) != 0));
                }

                program.Members[i] = (input, reads);
            }

            return program;
        }

        private string Name(int i) => Functions ? $"F{i}" : $"V{i}";

        private string Text(Read read, string argument)
        {
            var call = Functions ? $"({argument})" : "";
            return read.Via switch
            {
                Via.Dotted => $"L{read.Target}.{Name(read.Target)}{call}",
                Via.AliasDotted => $"M{read.Target}.{Name(read.Target)}{call}",
                _ => $"{Name(read.Target)}{call}",
            };
        }

        /// <summary>The program, with the owner called once per input in ONE run (a root layout has no call).</summary>
        public string Source(params int[] inputs)
        {
            var text = new StringBuilder();
            var indent = Layout switch { Wrapper.Owner => "    ", Wrapper.Nested => "        ", _ => "" };
            text.Append(Layout switch { Wrapper.Nested => "W(y) = {\n    O(x) = {\n", Wrapper.Owner => "O(x) = {\n", _ => "" });
            for (var i = 0; i < Members.Length; i++)
            {
                var (input, reads) = Members[i];
                text.Append(indent).Append($"L{i} = {{\n");
                var opens = reads.Where(r => r.Via is Via.Open or Via.AliasOpen).Select(r => r.Via == Via.Open ? $"L{r.Target}" : $"M{r.Target}").Distinct().ToList();
                if (opens.Count > 0)
                    text.Append(indent).Append("    open ").AppendJoin(", ", opens).Append('\n');
                if (Functions)
                    text.Append(indent).Append($"    public F{i}(n) = if(n < 1, {input}, {(reads.Count == 0 ? input : string.Join(" + ", reads.Select(r => Text(r, "n - 1"))))})\n");
                else
                    text.Append(indent).Append($"    public V{i} = if(1 < 0, {string.Join(" + ", reads.Where(r => !r.Live).Select(r => Text(r, "")).DefaultIfEmpty("0"))}, {input}{string.Concat(reads.Where(r => r.Live).Select(r => " + " + Text(r, "")))})\n");
                text.Append(indent).Append("}\n");
            }

            foreach (var target in Members.SelectMany(m => m.Reads).Where(r => r.Via is Via.AliasDotted or Via.AliasOpen).Select(r => r.Target).Distinct().Order())
                text.Append(indent).Append($"M{target} = L{target}\n");
            var call = Functions ? $"({Depth})" : "";
            for (var i = 0; i < Members.Length; i++)
                text.Append(indent).Append($"R{i} = L{i}.{Name(i)}{call}\n")
                    .Append(indent).Append($"A{i} = {{\n").Append(indent).Append($"    open L{i}\n").Append(indent).Append($"    {Name(i)}{call}\n").Append(indent).Append("}\n");
            text.Append(indent).AppendJoin(", ", Enumerable.Range(0, Members.Length).SelectMany(i => new[] { $"R{i}", $"A{i}" })).Append('\n');
            var calls = string.Join(", ", inputs.Select(x => $"O({x})"));
            return text.Append(Layout switch { Wrapper.Nested => $"    }}\n    {calls}\n}}\nW(3)\n", Wrapper.Owner => $"}}\n{calls}\n", _ => "" }).ToString();
        }

        /// <summary>The enclosing inputs a member requires: those some member it reaches, by any written read, reads.</summary>
        public SortedSet<string> Requires(int member)
        {
            var required = new SortedSet<string>(StringComparer.Ordinal);
            var seen = new HashSet<int>();
            var pending = new Stack<int>([member]);
            while (pending.TryPop(out var at))
            {
                if (!seen.Add(at))
                    continue;
                if (Members[at].Base is "x" or "y")
                    required.Add(Members[at].Base);
                foreach (var read in Members[at].Reads)
                    pending.Push(read.Target);
            }

            return required;
        }

        private decimal Value(int member, int x, int n)
        {
            var (input, reads) = Members[member];
            var own = input switch { "x" => x, "y" => 3, _ => decimal.Parse(input, CultureInfo.InvariantCulture) };
            if (Functions)
                return n < 1 || reads.Count == 0 ? own : reads.Sum(read => Value(read.Target, x, n - 1));
            return own + reads.Where(read => read.Live).Sum(read => Value(read.Target, x, 0));
        }

        /// <summary>The numbers one call of the owner emits, by direct recursion: <c>R0, A0, R1, A1, …</c>.</summary>
        public IEnumerable<string> Expected(int x)
            => Enumerable.Range(0, Members.Length).SelectMany(i =>
            {
                var value = Value(i, x, Depth).ToString(CultureInfo.InvariantCulture);
                return new[] { value, value };
            });
    }

    private static string[] Numbers(string display)
        => display.Split([' ', ',', '(', ')', '\n'], StringSplitOptions.RemoveEmptyEntries);

    /// <summary>
    /// 240 random programs of mutually reading libraries (most of them cyclic, about one in seven with a key met twice):
    /// every member and reader requires exactly the inputs its reads reach; the metadata is the per-path walk's; and
    /// two activations in ONE run give the values of two separate runs, which are the values direct recursion
    /// computes. This exercises the cache and detachment paths as well as checking every member's declared exposure.
    /// </summary>
    [Fact]
    public void RandomLibraries_MatchTheIndependentOracle_AndEvaluatePerActivation()
    {
        long reuses = 0, completions = 0, captured = 0;
        for (var seed = 0; seed < 240; seed++)
        {
            var program = Libraries.Create(seed);
            var source = program.Source(1, 20);
            var parsed = Parse(source);
            Assert.True(parsed.Diagnostics.Length == 0, $"seed {seed}: {parsed.Diagnostics}\n{source}");
            reuses += parsed.Observations.SettlementComponentReuses;
            completions += parsed.Observations.SettlementComponentCompletions;
            Assert.Equal(Parse(source, perPath: true).Metadata, parsed.Metadata);

            var properties = new Dictionary<string, Property>(StringComparer.Ordinal);
            var pending = new Stack<Algorithm>([parsed.Root]);
            while (pending.TryPop(out var body))
                foreach (var property in body.Properties)
                {
                    properties.TryAdd(property.Name, property);
                    pending.Push(property.Value);
                }

            for (var i = 0; i < program.Members.Length; i++)
            {
                var expected = program.Requires(i);
                captured += expected.Count > 0 ? 1 : 0;
                foreach (var name in new[] { program.Functions ? $"F{i}" : $"V{i}", $"R{i}", $"A{i}" })
                {
                    var property = properties[name];
                    Assert.True(expected.SetEquals(property.RequiredAncestorParameters),
                        $"seed {seed}: {name} requires [{string.Join(",", property.RequiredAncestorParameters)}], expected [{string.Join(",", expected)}]\n{source}");
                    Assert.Equal(expected.Count == 0 ? PropertyExposure.Exported : PropertyExposure.LocalOnlyCapturedAncestorParameters, property.Exposure);
                }
            }

            if (program.Layout == Libraries.Wrapper.Root)
            {
                Assert.Equal(program.Expected(0), Numbers(Display(source)));
                continue;
            }

            Assert.Equal(program.Expected(1), Numbers(Display(program.Source(1))));
            Assert.Equal(program.Expected(20), Numbers(Display(program.Source(20))));
            Assert.Equal(program.Expected(1).Concat(program.Expected(20)), Numbers(Display(source)));
        }

        // The sample exercises the rule and the classification it must not disturb.
        Assert.True(reuses >= 20, $"partial reuses {reuses}");
        Assert.True(completions > 100, $"completions {completions}");
        Assert.True(captured > 100, $"captured {captured}");
    }

    // ── The off-chain gap ───────────────────────────────────────────────────

    /// <summary>
    /// A program of the audit's fuzz generator (its front-end errors included: exposure classifies the recovered tree
    /// all the same). A component in it makes an owner lookup off its site's chain. Completing that component's
    /// members into the run's share lets a member kept from one site answer a deeper one, and <c>L</c> loses the
    /// requirements <c>p</c> and <c>x</c> the per-path walk publishes.
    /// </summary>
    private const string OffChainComponentKeptFromAnotherSite = """
        open B
        Q = Q.X.C
        M = P
        L(x, p) = {
          open P
          X = A.M
          Q = {
            L = {
              open B.P.M
              M(y, q) = {
                open P, B.M, Q
                L = C + 3 - N.M + P.C.B(1) + Q.N
                x
              }
              public X(x) = {
                public Q(q) = q
                M(0) = Y * P - y * N + 1
                M(p) = L
                public Y = M.X
                public Q = P
                C.C - X.Algorithm - 2
              }
              A = {
                P = x + C * p
                public L = L.B.L
                public A = 8 + Y + X(X(A.Algorithm)) + { p } * p + 2
                public Q = Y
                x
              }
              public X = X + 0
              N = {
                public M = 9 + X(p)
                public X = x - x * p - X
                public P = Y.Q
                public Q = Y
                x2, z0 = X.M, p + x + x * Y
                L
              }
              P(p) - p
            }
            N + B - x + A - C * X.X
          }
          public N(p) = {
            L(0) = z - Q * A(6) * P * x
            L(z) = p
            p * L + C + C(Y(A))
          }
          L = M * N + A.P(P.Algorithm) - X.X * 2
          public C(z, q) = p * Q.Q * { p } * x - Q
          9 + L
        }
        B = L.C
        X(q, x) = {
          public Q = Q(C.Algorithm)
          X.A.C + 9 - M - Y + { q }
        }
        C(Q) * A - N.Algorithm * Y - A * P
        """;

    /// <summary>
    /// Another program of the same generator. Here the per-path walk itself keeps a settlement without its site that
    /// a deeper site is then answered from (THE OFF-CHAIN GAP); completing the component's members for the run only
    /// replaces that settlement, and <c>Y</c> gains the requirement <c>N</c> the per-path walk does not publish.
    /// </summary>
    private const string OffChainComponentThePerPathWalkKeeps = """
        Y = {
          public X = {
            open Q.A
            X = L
            public L(q, x) = {
              open C.N.L
              public C = {
                M = x + C.M.P + Q.P.A * C
                X(0) = { Q.P(M) } - { C(A.A) }
                X(y) = 5 - P - Q.M - y
                public L = x * A
                public Q = q
                q
              }
              M(p) = p - z - x - Y
              M.C.X
            }
            B(p, y) = {
              open P
              X = {
                open N.C
                Q(0) = { B } - A.B - M
                Q(z) = B.Algorithm
                M(Q.Q.Y)
              }
              L = Y.Algorithm
              P = C.L.L
              P(x, z) = {
                open A, P.Q, B.P.B
                N = A.Y.L + B + z + X
                A = y * L * A.N.P - N * Q(Q.Algorithm) - M.B.B
                public X = 7 * { X }
                public C = Q.P.C - B.M - X + y - A.A.Q
                A = X.Algorithm
                A
              }
              Q * 4 * M.Algorithm * 7 - L
            }
            X
          }
          A
        }
        L = Y.B - N * Q
        L = C.B
        P = L.B
        Q = B.C.C(A) - P * N * L * N * P
        Q(0) = z
        Q(y) = Q
        Q(q) = {
          C(p) = {
            open C.A.A
            M = {
              public M = N.C
              N = X.C.X
              L = q
              X.L * N
            }
            public X = {
              C = {
                open M.B.Q, Q, B.Y.X
                C = q - p
                L = M
                public L = N.Y - M.Algorithm - q + p * 2
                public Q = y - C.N * Q * P - P
                public P = { p } + Q + M(x) + Y
                B.C(X.Algorithm) - X * M + Y
              }
              public Y = M.N.Y
              p * p + 9 * C + N.Q.B(N.Q)
            }
            X
          }
          X = {
            open C.N
            public M(q) = {
              N = { q } * q + 6 + N
              public X = P
              public Q = {
                public M = A(C)
                q
              }
              M = {
                N = M.Y
                q
              }
              A.X.A - 6 - Q * L.C * L(q) + { 8 } * P
            }
            L.N - C + X * B(Y) - M.M - N.Algorithm * L
          }
          public B = B.B.Y
          public A = B - q * C
          A.Q - q
        }
        L.M
        """;

    /// <summary>
    /// A program of the same generator in which a component is settled while a summary of the level in progress is
    /// still growing. A member completed with its component carries the component's live reads, so it is kept for
    /// its own top-level settlement only; kept in the run's share, it answers a later settlement with the summary as
    /// it was, and the published requirements change.
    /// </summary>
    private const string ComponentThatReadALiveSummary = """
        C(y, p) = {
          open X.Q.P
          B = N.Y
          public L = p
          public N(z) = { 0 } * X(C) * B - N.B
          L.Y - { Y } + 8 * { Q } - B - Q + M
        }
        M(q, p) = {
          X = Y
          Y + { { C.B } } + P * 2
        }
        Q.X - N - X
        """;

    /// <summary>
    /// A program of the same generator whose component reads bound owners. A member completed with its component is
    /// kept with the component's bound-owner reads; kept as if it had read none, it answers settlements under bound
    /// owners that decide otherwise, and the published requirements change.
    /// </summary>
    private const string ComponentThatReadBoundOwners = """
        N(y) = y - y + { Q(N) } - L.A
        A = {
          public L = {
            public C(y, x) = {
              N = Y
              Y = C.X
              X = {
                A = y
                N - X.X(A(A)) * { 3 } + N - 5 + Q(5)
              }
              public A = B - A.M.A
              M(y) - X(X.L) - B(x) - L(y)
            }
            M = L * C - X - X.X.N
            L(X)
          }
          public N = P
          X(q, z) = {
            open A, B.Q
            N(y, x) = {
              A(y, z) = {
                open Q
                public C = C.P - N(q) * Q - y
                public L = Q(y)
                y - N
              }
              P = {
                open Y.C, C
                public Q(q) = q
                A = M
                public B = Y
                C + Y * y * A
              }
              public N = y * A + X(B) + P
              M
            }
            A = A(M.L)
            C = B
            { X(A.P) }
          }
          public C = X.Q + { M }
          N
        }
        C(z) = z
        A
        """;

    /// <summary>
    /// The live-summary and bound-owner mutation controls must keep the per-path walk's full published metadata.
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void OwnerAndLiveSummaryDependencies_KeepThePerPathMetadata(bool liveSummary)
    {
        var source = (liveSummary ? ComponentThatReadALiveSummary : ComponentThatReadBoundOwners).ReplaceLineEndings("\n") + "\n";
        var perPath = Parse(source, perPath: true);
        var component = Parse(source);
        Assert.NotEqual("", perPath.Diagnostics);
        Assert.Equal(perPath.Diagnostics, component.Diagnostics);
        Assert.Equal(perPath.Metadata, component.Metadata);
        Assert.InRange(component.Observations.RequiredAncestorSettlementFrames, 1,
            perPath.Observations.RequiredAncestorSettlementFrames + component.Observations.SettlementComponentDiscoveryFrames);
    }

    /// <summary>
    /// A component that made an owner lookup off its site's chain completes no member: which settlements are kept
    /// without their site decides what other sites are answered, so every member is settled when it is next met, as
    /// the per-path walk settles it, and the published metadata is the per-path walk's in both programs.
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void ComponentsWithAnOffChainLookup_PublishWhatThePerPathWalkPublishes(bool keptFromAnotherSite)
    {
        var source = (keptFromAnotherSite ? OffChainComponentKeptFromAnotherSite : OffChainComponentThePerPathWalkKeeps).ReplaceLineEndings("\n") + "\n";
        var perPath = Parse(source, perPath: true);
        var component = Parse(source);
        Assert.NotEqual("", perPath.Diagnostics);
        Assert.Equal(perPath.Diagnostics, component.Diagnostics);
        Assert.Equal(perPath.Metadata, component.Metadata);
        Assert.True(component.Observations.SettlementComponentReuses > 0);
        Assert.True(component.Observations.RequiredAncestorSettlementFrames * 10 < perPath.Observations.RequiredAncestorSettlementFrames);
    }

    /// <summary>
    /// The audit's dense family inside an owner whose input is the base case of ONE function: every function reaches
    /// it, so every function and reader requires the input, and two activations in one run keep their own values,
    /// which direct recursion computes.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DenseFunctionsInsideAnOwner_RequireItsInput_AndEvaluatePerActivation(bool opened)
    {
        const int Size = 4;
        var source = new StringBuilder("O(x) = {\n");
        for (var i = 0; i < Size; i++)
        {
            var others = Enumerable.Range(0, Size).Where(j => j != i).ToList();
            source.Append($"    L{i} = {{\n");
            if (opened)
                source.Append("        open ").AppendJoin(", ", others.Select(j => $"L{j}")).Append('\n');
            source.Append($"        public F{i}(n) = if(n < 1, {(i == 0 ? "x" : "1")}, ")
                .AppendJoin(" + ", others.Select(j => opened ? $"F{j}(n - 1)" : $"L{j}.F{j}(n - 1)")).Append(")\n    }\n");
        }

        for (var i = 0; i < Size; i++)
            source.Append($"    R{i} = L{i}.F{i}(2)\n");
        var body = source.Append("    ").AppendJoin(", ", Enumerable.Range(0, Size).Select(i => $"R{i}")).Append("\n}\n").ToString();

        var parsed = Clean(body + "O(1), O(20)");
        var owner = ExposureOpenChainComplexityTests.Member(parsed.Root, "O").Value;
        for (var i = 0; i < Size; i++)
        {
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"R{i}"), ("x", 0));
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"L{i}", $"F{i}"), ("x", 1));
        }

        // F_i(2) = sum over j ≠ i of F_j(1), and F_j(1) = sum over k ≠ j of the base cases: F0's is x, the others' 1.
        static decimal Value(int member, int n, int x)
            => n < 1 ? member == 0 ? x : 1 : Enumerable.Range(0, Size).Where(j => j != member).Sum(j => Value(j, n - 1, x));
        string[] Expected(int x) => [.. Enumerable.Range(0, Size).Select(i => Value(i, 2, x).ToString(CultureInfo.InvariantCulture))];
        Assert.Equal(Expected(1), Numbers(Display(body + "O(1)")));
        Assert.Equal(Expected(20), Numbers(Display(body + "O(20)")));
        Assert.Equal(Expected(1).Concat(Expected(20)), Numbers(Display(body + "O(1), O(20)")));
    }
}
