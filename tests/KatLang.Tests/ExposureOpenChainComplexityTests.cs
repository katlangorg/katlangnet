namespace KatLang.Tests;

/// <summary>
/// EXPOSURE-OPEN-1: the exposure pass on members read through <c>open</c> inside a parameterized owner.
/// The summary channel once carried, on every reference that escaped a level with opens, the seed its
/// provider charges, and that seed held the next link's — a chain of N members opened from one another
/// and read at the owner nested N deep. Two costs followed from that nesting. (A) Every enclosing link
/// rebuilt and re-serialized the whole nesting below it, so a chain of N cost O(N³) characters and
/// copies: N = 300 took 9 s and 20 GB. (B) A provider's seed grew during the member fixed point, and a
/// reference with the smaller seed was a DIFFERENT entry from the same reference with the larger one;
/// around a cycle of mutually reading libraries the stale entry circulated forever and the analysis
/// never terminated. A pending reference now carries no provider and no seed at all: it names its head,
/// member steps and completed origin, and the owning level's settlement selects the provider from the
/// completed structure. These shapes stay pinned as the reproducers of both costs.
///
/// <para>The regression oracle is deterministic work: <see cref="FrontEndTraversalObservations"/>
/// counts the summary computations, member expansions and evaluations, the key characters, and the
/// settlement frames, at several sizes, against absolute polynomial bounds and doubling ratios.
/// Classification is pinned exactly — every property's exposure, required names, and owner-relative
/// capture depths — against an independent fixed-point oracle (<see cref="OpenLibraryOracle"/>).</para>
/// </summary>
public sealed class ExposureOpenChainComplexityTests
{
    // ── Shapes ───────────────────────────────────────────────────────────────

    /// <summary>
    /// <c>P(i)</c> reads <c>A(i+1)</c> through its own <c>open P(i+1)</c> (or the dotted
    /// <c>P(i+1).A(i+1)</c>; <paramref name="mode"/> <c>mixed</c> alternates and adds a local
    /// intermediary), and the last member is <paramref name="last"/>.
    /// </summary>
    internal static string Chain(string mode, int length, string last, string indent)
    {
        var source = new System.Text.StringBuilder();
        for (var i = 1; i <= length; i++)
        {
            source.Append(indent).Append($"P{i} = {{\n");
            var useOpen = mode == "open" || mode == "mixed" && i % 2 == 1;
            if (useOpen && i < length)
                source.Append(indent).Append($"    open P{i + 1}\n");
            var value = i == length ? last : useOpen ? $"A{i + 1} + 1" : $"P{i + 1}.A{i + 1} + 1";
            if (mode == "mixed")
            {
                source.Append(indent).Append($"    Local{i} = {value}\n");
                value = $"Local{i} + 0";
            }

            source.Append(indent).Append($"    public A{i} = {value}\n");
            source.Append(indent).Append("    0\n");
            source.Append(indent).Append("}\n");
        }

        return source.ToString();
    }

    internal static string Reader(string mode, string indent, string name = "R")
        => mode == "dotted"
            ? $"{indent}{name} = P1.A1\n"
            : $"{indent}{name} = {{\n{indent}    open P1\n{indent}    A1\n{indent}}}\n";

    /// <summary>Reproducer A: the opened chain inside <c>O(p)</c>, read by <c>R</c> through <c>open P1</c>.</summary>
    internal static string NestedOwnerChain(int length, string mode = "open", string last = "5", string call = "O(1)")
        => "O(p) = {\n" + Chain(mode, length, last, "    ") + Reader(mode, "    ") + "    R\n}\n" + call;

    private static string RootChain(int length)
        => Chain("open", length, "5", "") + Reader("open", "") + "R";

    internal static Algorithm.User Exposed(string source, FrontEndTraversalObservations observations)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var detectedInput = ParameterDetector.DetectPrevalidated(syntax);
        var (detected, detectionDiagnostics) = detectedInput;
        Assert.Empty(detectionDiagnostics);
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detectedInput, observations: null, diagnostics);
        Assert.Empty(diagnostics);
        return (Algorithm.User)PropertyExposureResolver.Resolve(resolved, observations);
    }

    internal static Property Member(Algorithm owner, params string[] path)
    {
        var current = owner;
        Property? property = null;
        foreach (var name in path)
        {
            property = Assert.Single(current.Properties, p => p.Name == name);
            current = property.Value;
        }

        return property!;
    }

    internal static void AssertRequires(Property property, params (string Name, int Depth)[] requirements)
    {
        Assert.Equal(
            requirements.Length == 0 ? PropertyExposure.Exported : PropertyExposure.LocalOnlyCapturedAncestorParameters,
            property.Exposure);
        Assert.Equal(requirements.Select(r => r.Name), property.RequiredAncestorParameters);
        Assert.Equal(requirements.Select(r => new CapturedParameterRequirement(r.Name, r.Depth)), property.CaptureRequirements ?? []);
    }

    private static void OnOneMebibyteStack(Action work)
        => AstStructuralDepthProcessTests.RunOnThreadWithStack(1024 * 1024, work);

    /// <summary>
    /// The settlement frames of an N-link chain of any of the five shapes (opened, dotted, mixed, root-level,
    /// captured terminal) with the run's settlement share: the root level and the owner each walk the chain once,
    /// and every later link's level reuses that walk — 6N to 8N frames, less a constant. Formerly N(N + 3).
    /// </summary>
    internal static long SharedSettlementFrameBound(int length) => 8L * length + 16;

    // ── Reproducer A: nested owner + constant terminal + opens ───────────────

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(5)]
    [InlineData(8)]
    [InlineData(13)]
    public void NestedOwnerOpenedChain_WithAConstantTerminal_IsExportedThroughout_AndRuns(int length)
    {
        var source = NestedOwnerChain(length);
        var owner = Member(SourceProvenance.ParseValid(source).Root, "O").Value;
        for (var i = 1; i <= length; i++)
        {
            AssertRequires(Member(owner, $"P{i}"));
            AssertRequires(Member(owner, $"P{i}", $"A{i}"));
        }

        AssertRequires(Member(owner, "R"));
        Assert.Equal((length + 4).ToString(System.Globalization.CultureInfo.InvariantCulture),
            Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    /// <summary>
    /// The work of the opened chain at three doubling sizes. Each link's algorithm is summarized once
    /// (2N + 2 summaries, N + 2 member expansions in all) and its key costs its own entries (O(N)
    /// characters in all). The exposure settlement of each link's level reuses the walk of the links below
    /// it from the run's settlement share (<see cref="ExposureSettlementShareTests"/>): at most 8 frames a
    /// link, where every level formerly walked the whole chain below it (N(N + 3) frames, the order the
    /// root-level and dotted chains paid too). Before EXPOSURE-OPEN-1 every link rebuilt and re-serialized
    /// the nesting below it: 143,522 key characters at N = 16 and 9,110,136 at N = 64.
    /// </summary>
    [Fact]
    public void NestedOwnerOpenedChain_SummarizesEachLinkOnce_AndSettlesLinearly()
    {
        var previous = default(FrontEndTraversalObservations);
        foreach (var length in new[] { 16, 32, 64 })
        {
            var observations = new FrontEndTraversalObservations();
            var owner = Member(Exposed(NestedOwnerChain(length), observations), "O").Value;
            AssertRequires(Member(owner, "R"));
            AssertRequires(Member(owner, "P1", "A1"));

            Assert.Equal(2L * length + 2, observations.DependencyAlgorithmSummaryComputations);
            Assert.InRange(observations.SummaryKeyCharacters, 1, 512L * length);
            Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, SharedSettlementFrameBound(length));
            Assert.Equal(length + 2L, observations.SummaryMemberExpansions);
            Assert.InRange(observations.CompletedStaticStructureReads, 1, observations.RequiredAncestorSettlementFrames);
            if (previous is not null)
            {
                Assert.InRange(observations.DependencyAlgorithmSummaryComputations, 1, 5 * previous.DependencyAlgorithmSummaryComputations / 2);
                Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, 11 * previous.RequiredAncestorSettlementFrames / 5);
            }

            previous = observations;
        }
    }

    // ── Controls ─────────────────────────────────────────────────────────────

    /// <summary>
    /// The same chain at the root (no parameterized owner), and inside the owner through dotted reads
    /// (member paths instead of opens): settlement is the same linear walk.
    /// </summary>
    [Theory]
    [InlineData("root")]
    [InlineData("dotted")]
    public void ControlChains_SettleLinearly(string shape)
    {
        foreach (var length in new[] { 16, 32, 64 })
        {
            var observations = new FrontEndTraversalObservations();
            var source = shape == "root" ? RootChain(length) : NestedOwnerChain(length, "dotted");
            var root = Exposed(source, observations);
            var level = shape == "root" ? root : Member(root, "O").Value;
            AssertRequires(Member(level, "R"));
            for (var i = 1; i <= length; i++)
                AssertRequires(Member(level, $"P{i}", $"A{i}"));

            if (shape == "root") Assert.True(observations.CompletedStaticStructureReads > 0);
            else Assert.Equal(0, observations.CompletedStaticStructureReads); // symbolic dotted summaries need no projection
            Assert.InRange(observations.DependencyAlgorithmSummaryComputations, 1, 3L * length + 2);
            Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, SharedSettlementFrameBound(length));
        }

        var shortSource = shape == "root" ? RootChain(6) : NestedOwnerChain(6, "dotted");
        Assert.Equal("10", Assert.IsType<RunResult.Success>(KatLangEngine.Run(shortSource)).ToDisplayString());
    }

    /// <summary>
    /// The opened chain whose terminal reads the owner's parameter: every link requires <c>p</c> one
    /// level out, and the reader directly. The summary work is the constant-terminal chain's, and an
    /// activation-specific value proves the classification: a link wrongly classified exported
    /// would let the run cache hand the first call's value to the second.
    /// </summary>
    [Fact]
    public void CapturedTerminalChain_RequiresTheOwnersInputThroughout_AndKeepsActivationsApart()
    {
        foreach (var length in new[] { 16, 32, 64 })
        {
            var observations = new FrontEndTraversalObservations();
            var owner = Member(Exposed(NestedOwnerChain(length, last: "p"), observations), "O").Value;
            for (var i = 1; i <= length; i++)
            {
                AssertRequires(Member(owner, $"P{i}"));
                AssertRequires(Member(owner, $"P{i}", $"A{i}"), ("p", 1));
            }

            AssertRequires(Member(owner, "R"), ("p", 0));
            Assert.Equal(length + 2L, observations.SummaryMemberExpansions);
            Assert.Equal(2L * length + 2, observations.DependencyAlgorithmSummaryComputations);
            Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, SharedSettlementFrameBound(length));
            Assert.InRange(observations.CompletedStaticStructureReads, 1, observations.RequiredAncestorSettlementFrames);
        }

        const int Short = 7;
        Assert.Equal("22", Assert.IsType<RunResult.Success>(
            KatLangEngine.Run(NestedOwnerChain(Short, last: "p", call: "O(1) + O(9)"))).ToDisplayString());
    }

    /// <summary>Alternating opened and dotted links, each through a local intermediary before the public member.</summary>
    [Fact]
    public void MixedChain_WithLocalIntermediaries_IsExported_WithLinearWork()
    {
        foreach (var length in new[] { 16, 32, 64 })
        {
            var observations = new FrontEndTraversalObservations();
            var owner = Member(Exposed(NestedOwnerChain(length, "mixed"), observations), "O").Value;
            AssertRequires(Member(owner, "R"));
            for (var i = 1; i <= length; i++)
            {
                AssertRequires(Member(owner, $"P{i}", $"A{i}"));
                AssertRequires(Member(owner, $"P{i}", $"Local{i}"));
            }

            Assert.InRange(observations.SummaryMemberExpansions, 1, 2L * length + 2);
            Assert.InRange(observations.DependencyAlgorithmSummaryComputations, 1, 3L * length + 2);
            Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, SharedSettlementFrameBound(length));
        }

        Assert.Equal("10", Assert.IsType<RunResult.Success>(KatLangEngine.Run(NestedOwnerChain(6, "mixed"))).ToDisplayString());
    }

    // ── One chain under equal and different contexts ─────────────────────────

    /// <summary>
    /// K readers of one opened chain in ONE owner reach the same members: each reader is classified
    /// alike and the chain's settlement is shared by the level solver. The same chain declared under two
    /// owners whose parameters are both named <c>p</c> is two contexts: each reader requires its OWN
    /// owner's <c>p</c>, at its own depth.
    /// </summary>
    [Fact]
    public void ReadersOfOneChain_ShareItsClassification_WhileOwnersWithTheSameParameterNameStayApart()
    {
        const int Length = 12;
        const int Readers = 8;
        var readers = string.Concat(Enumerable.Range(0, Readers).Select(k => Reader("open", "    ", $"R{k}")));
        var shared = "O(p) = {\n" + Chain("open", Length, "p", "    ") + readers + "    R0\n}\nO(2) + O(5)";
        var observations = new FrontEndTraversalObservations();
        var owner = Member(Exposed(shared, observations), "O").Value;
        for (var k = 0; k < Readers; k++)
            AssertRequires(Member(owner, $"R{k}"), ("p", 0));
        // Equal readers have one base seed: the member solver expands it once and every reader shares it.
        Assert.Equal(Length + 2L, observations.SummaryMemberExpansions);
        Assert.Equal("29", Assert.IsType<RunResult.Success>(KatLangEngine.Run(shared)).ToDisplayString());

        // The inner owner declares its own `p`: the inner chain's terminal and reader require the
        // inner `p`, the outer reader the outer `p`.
        var nested = "O(p) = {\n" + Chain("open", Length, "p", "    ")
            + "    I(p) = {\n" + Chain("open", Length, "p", "        ") + Reader("open", "        ", "S") + "        S\n    }\n"
            + Reader("open", "    ") + "    R + I(100)\n}\nO(1)";
        var nestedOwner = Member(SourceProvenance.ParseValid(nested).Root, "O").Value;
        AssertRequires(Member(nestedOwner, "R"), ("p", 0));
        AssertRequires(Member(nestedOwner, "P1", "A1"), ("p", 1));
        AssertRequires(Member(nestedOwner, "I", "S"), ("p", 0));
        AssertRequires(Member(nestedOwner, "I", "P1", "A1"), ("p", 1));
        Assert.Equal("123", Assert.IsType<RunResult.Success>(KatLangEngine.Run(nested)).ToDisplayString());
    }

    // ── Reproducer B: mutually reading libraries ─────────────────────────────

    /// <summary>The task's reproducer B, verbatim.</summary>
    internal const string ReproducerB =
        "O(x0, x1, x2) = {\nL0 = { public V = P0\n1 }\nP0 = { open L3\nV }, L4.V\nL1 = { public V = P1\n1 }\nP1 = x0, x1, { open { public V = 3 }\nV + L2.V }, { open L3\nV }\nL2 = { public V = P2\n1 }\nP2 = x1, x2, { open L4, L0\nV }, L5.V\nL3 = { public V = P3\n1 }\nP3 = x2, { open L1, L2\nV }, { open L3, L3\nV }\nL4 = { public V = P4\n1 }\nP4 = x0, x2, { open { public V = 3 }\nV + L2.V }, { open { public V = 3 }\nV + L4.V }, { open L5\nV }\nL5 = { public V = P5\n1 }\nP5 = x1, { open { public V = 3 }\nV + L1.V }, { open L5\nV }\n1\n}\n1";

    private static OpenLibraryOracle.Library[] ReproducerBLibraries()
    {
        static OpenLibraryOracle.Item Input(int p) => new(OpenLibraryOracle.ItemKind.Input, p);
        static OpenLibraryOracle.Item Item(OpenLibraryOracle.ItemKind kind, int a, int b = 0) => new(kind, a, b);
        const OpenLibraryOracle.ItemKind Dotted = OpenLibraryOracle.ItemKind.Dotted, Opened = OpenLibraryOracle.ItemKind.Opened,
            Ambiguous = OpenLibraryOracle.ItemKind.Ambiguous, Duplicate = OpenLibraryOracle.ItemKind.Duplicate,
            Inline = OpenLibraryOracle.ItemKind.Inline;
        return
        [
            new([Item(Opened, 3), Item(Dotted, 4)]),
            new([Input(0), Input(1), Item(Inline, 2), Item(Opened, 3)]),
            new([Input(1), Input(2), Item(Ambiguous, 4, 0), Item(Dotted, 5)]),
            new([Input(2), Item(Ambiguous, 1, 2), Item(Duplicate, 3)]),
            new([Input(0), Input(2), Item(Inline, 2), Item(Inline, 4), Item(Opened, 5)]),
            new([Input(1), Item(Inline, 1), Item(Opened, 5)]),
        ];
    }

    /// <summary>
    /// Reproducer B — formerly more than a minute and never finishing: the member fixed point kept a
    /// stale provider seed alive around the library cycle. The outer owner is never called, so this is
    /// declaration analysis alone; it completes, reports exactly the two ambiguous opens, and classifies
    /// every library member and every <c>P(i)</c> as the independent oracle computes.
    /// </summary>
    [Fact]
    public void ReproducerB_CompletesWithTheOraclesClassification()
    {
        var libraries = ReproducerBLibraries();
        Assert.Equal(ReproducerB, OpenLibraryOracle.Render(libraries, order: null, shadow: false, call: "1"));

        FrontEndTraversalObservations observations = new();
        ParseResult parsed = null!;
        Algorithm.User exposed = null!;
        OnOneMebibyteStack(() =>
        {
            parsed = Parser.Parse(ReproducerB);
            exposed = OpenLibraryOracle.ExposedAllowingAmbiguity(ReproducerB, observations);
        });

        Assert.Equal([DiagnosticCode.AmbiguousOpen, DiagnosticCode.AmbiguousOpen], parsed.Diagnostics.Select(d => d.Code));
        OpenLibraryOracle.AssertMatches(libraries, shadow: false, Member(parsed.Root, "O").Value);
        OpenLibraryOracle.AssertMatches(libraries, shadow: false, Member(exposed, "O").Value);
        Assert.InRange(observations.SummaryMemberEvaluations, 1, 60);
        Assert.InRange(observations.SummaryMemberExpansions, 1, 60);
        Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, 120);
        Assert.True(observations.SummaryMemberEvaluations > observations.SummaryMemberExpansions);
    }

    /// <summary>
    /// The minimal core of B: two libraries reading each other through inline-provider blocks and
    /// opens, one of them reading a third library whose member captures the owner's input. That opened
    /// member's requirements are first empty and later <c>x0</c>; when a reference carried them as a
    /// seed, the two states were separate entries that circulated around the cycle forever (no
    /// termination). A reference carries no seed now, and the fixed point is reached in a few evaluations.
    /// </summary>
    [Fact]
    public void MutuallyReadingLibraries_ReachTheirFixedPoint_WhenAnOpenedMembersRequirementsGrowLate()
    {
        const string source = "O(x0) = {\nL1 = { public V = P1\n1 }\nP1 = { open { public V = 3 }\nV + L2.V }, { open L3\nV }\n"
            + "L2 = { public V = P2\n1 }\nP2 = L5.V\nL3 = { public V = P3\n1 }\nP3 = x0\nL5 = { public V = P5\n1 }\n"
            + "P5 = { open { public V = 3 }\nV + L1.V }, { open L5\nV }\n1\n}\nO(1)";
        var observations = new FrontEndTraversalObservations();
        Algorithm.User exposed = null!;
        OnOneMebibyteStack(() => exposed = Exposed(source, observations));
        var owner = Member(exposed, "O").Value;
        foreach (var name in new[] { "P1", "P2", "P3", "P5" })
            AssertRequires(Member(owner, name), ("x0", 0));
        foreach (var name in new[] { "L1", "L2", "L3", "L5" })
            AssertRequires(Member(owner, name, "V"), ("x0", 1));
        Assert.InRange(observations.SummaryMemberEvaluations, 1, 30);
        Assert.True(observations.SummaryMemberEvaluations > observations.SummaryMemberExpansions);
        Assert.Equal("1", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    /// <summary>
    /// The scalable family of B: N libraries, each <c>P(i)</c> reading an input, an inline provider beside a
    /// dotted read, an opened library, an AMBIGUOUS open of two libraries, a DUPLICATE open of one, and a
    /// dotted read — every library reaching every other through a cycle. Matches the oracle at every
    /// size; the member fixed point stays within absolute polynomial bounds (each member is re-evaluated
    /// at most a few times per library its seed grows by) and grows by at most the expected factor per
    /// doubling.
    /// </summary>
    [Fact]
    public void GeneratedReproducerBFamily_MatchesTheOracle_WithPolynomialWork()
    {
        var previous = default(FrontEndTraversalObservations);
        foreach (var size in new[] { 8, 16, 32 })
        {
            var libraries = OpenLibraryOracle.ReproducerBFamily(size);
            var source = OpenLibraryOracle.Render(libraries, order: null, shadow: false, call: "1");
            var observations = new FrontEndTraversalObservations();
            var exposed = OpenLibraryOracle.ExposedAllowingAmbiguity(source, observations);
            OpenLibraryOracle.AssertMatches(libraries, shadow: false, Member(exposed, "O").Value);

            long n = size;
            Assert.InRange(observations.SummaryMemberEvaluations, 1, 2 * n * n);
            Assert.InRange(observations.SummaryMemberExpansions, 1, 2 * n * n);
            // Full serialized seed keys include the growing reference sets, before their ids exist.
            Assert.InRange(observations.SummaryKeyCharacters, 1, 512 * n * n * n);
            Assert.InRange(observations.CompletedStaticStructureReads, 1, 64 * n * n * n);
            Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, 64 * n);
            if (previous is not null)
            {
                Assert.InRange(observations.SummaryMemberEvaluations, 1, 5 * previous.SummaryMemberEvaluations);
                Assert.InRange(observations.SummaryMemberExpansions, 1, 5 * previous.SummaryMemberExpansions);
                Assert.InRange(observations.SummaryKeyCharacters, 1, 10 * previous.SummaryKeyCharacters);
            }

            previous = observations;
        }
    }

    // ── Cycles of opens settled at one owner ─────────────────────────────────

    /// <summary>
    /// Siblings opening each other, read through an open at the owner: settling the opened member at the
    /// owner charges the member it opens, which opens back. That expansion formerly recursed until the
    /// host stack overflowed and killed the process, on a fifteen-line program. A re-entered expansion
    /// now charges nothing beyond the enclosing one (the least fixed point), so the cycle is classified
    /// — each member requiring what the whole cycle requires — and an activation-specific run agrees.
    /// </summary>
    [Theory]
    [InlineData(2, "p")]
    [InlineData(3, "p")]
    [InlineData(5, "p")]
    [InlineData(3, "5")]
    public void SiblingsOpeningEachOther_AreClassifiedAtTheOwner_OnASmallStack(int length, string terminal)
    {
        // P(i) opens P(i+1) (and the last opens P1); A(i) reads A(i+1), and the last member reads the
        // terminal — a cycle of opens whose values are acyclic.
        var body = new System.Text.StringBuilder();
        for (var i = 1; i <= length; i++)
        {
            var next = i == length ? 1 : i + 1;
            body.Append($"    P{i} = {{\n        open P{next}\n");
            body.Append(i == length ? $"        public A{i} = {terminal}\n" : $"        public A{i} = A{next} + 1\n");
            body.Append($"        public B{i} = 0\n        0\n    }}\n");
        }

        var source = "O(p) = {\n" + body + Reader("open", "    ") + "    R\n}\nO(1) + O(10)";
        Algorithm.User exposed = null!;
        OnOneMebibyteStack(() => exposed = Exposed(source, new FrontEndTraversalObservations()));
        var owner = Member(exposed, "O").Value;
        var captured = terminal == "p";
        for (var i = 1; i <= length; i++)
        {
            if (captured)
                AssertRequires(Member(owner, $"P{i}", $"A{i}"), ("p", 1));
            else
                AssertRequires(Member(owner, $"P{i}", $"A{i}"));
            AssertRequires(Member(owner, $"P{i}", $"B{i}"));
        }

        if (captured)
            AssertRequires(Member(owner, "R"), ("p", 0));
        else
            AssertRequires(Member(owner, "R"));
        var expected = captured ? 1 + 10 + 2 * (length - 1) : 2 * (5 + length - 1);
        Assert.Equal(expected.ToString(System.Globalization.CultureInfo.InvariantCulture),
            Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    /// <summary>
    /// The crash itself: members whose VALUES read around the open cycle (<c>A1 = A2 + 1</c> through
    /// <c>open P2</c>, …, the last reading <c>A1 + p</c> through <c>open P1</c>). Settling <c>A1</c> at the
    /// owner charged <c>A2</c>, which charged <c>A1</c> again, without end — the process died of a stack
    /// overflow during parsing. Evaluating such a value never terminates (that is the evaluator's
    /// business); declaration analysis classifies every member of the cycle as requiring <c>p</c>.
    /// </summary>
    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(6)]
    public void MembersReadingAroundAnOpenCycle_AreClassified_InsteadOfOverflowingTheStack(int length)
    {
        var body = new System.Text.StringBuilder();
        for (var i = 1; i <= length; i++)
        {
            var next = i == length ? 1 : i + 1;
            body.Append($"    P{i} = {{\n        open P{next}\n");
            body.Append(i == length ? $"        public A{i} = A{next} + p\n" : $"        public A{i} = A{next} + 1\n");
            body.Append("        0\n    }\n");
        }

        var source = "O(p) = {\n" + body + Reader("open", "    ") + "    R\n}\n0";
        var observations = new FrontEndTraversalObservations();
        ParseResult parsed = null!;
        OnOneMebibyteStack(() => parsed = Parser.Parse(source));
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var owner = Member(parsed.Root, "O").Value;
        for (var i = 1; i <= length; i++)
            AssertRequires(Member(owner, $"P{i}", $"A{i}"), ("p", 1));
        AssertRequires(Member(owner, "R"), ("p", 0));

        Algorithm.User exposed = null!;
        OnOneMebibyteStack(() => exposed = Exposed(source, observations));
        AssertRequires(Member(Member(exposed, "O").Value, "R"), ("p", 0));
        Assert.InRange(observations.SummaryMemberExpansions, 1, 4L * length * length);
    }

    /// <summary>
    /// A long opened chain with a reader at the owner, on a 1 MiB thread, in process: 400 links pin
    /// that the cubic cost does not come back (the implementation before EXPOSURE-OPEN-1 took 9 s at
    /// 300 links and 58 s at 500) — exactly N + 2 member expansions. Settling each link's charge
    /// at the owner formerly also took one group of host frames per link (OOS-22: the process died
    /// between 500 and 700 links on a 1 MiB Release thread); that expansion now runs on an explicit
    /// stack, and the deep chains are pinned in a child process
    /// (<see cref="ExposureOpenChainDepthProcessTests"/>), where an overflow cannot kill the test host.
    /// </summary>
    [Fact]
    public void LongNestedOwnerOpenedChain_SettlesOnASmallStack()
    {
        const int Length = 400;
        var observations = new FrontEndTraversalObservations();
        Algorithm.User exposed = null!;
        OnOneMebibyteStack(() => exposed = Exposed(NestedOwnerChain(Length, last: "p"), observations));
        var owner = Member(exposed, "O").Value;
        AssertRequires(Member(owner, "R"), ("p", 0));
        AssertRequires(Member(owner, $"P{Length}", $"A{Length}"), ("p", 1));
        Assert.Equal(Length + 2L, observations.SummaryMemberExpansions);
    }

    /// <summary>A failed Q8 member-summary read releases its expansion frame and never caches a partial result.</summary>
    [Fact]
    public void InterruptedChainExpansion_ReleasesItsActiveState_AndTheRetryMatchesAFreshAnalysis()
    {
        const int Length = 40;
        var owner = Member(SourceProvenance.ParseValid(NestedOwnerChain(Length, last: "p")).Root, "O").Value;
        var seed = new PropertyDependencyGraphBuilder.SummarySeed(visiblePropertyDependencyNames: ["P20"]);
        PropertyDependencyGraphBuilder.LevelContext? lastLevel = null;
        PropertyDependencyGraphBuilder.SummarySeed Settle(PropertyDependencyGraphBuilder.SummaryMemo memo, string? failAt)
        {
            var context = AnalyzedStaticStructures.ForBoundAst(owner);
            var memos = PropertyDependencyGraphBuilder.CreateWalkMemos(memo, observations: null, context);
            var members = new FailingMemberMap(PropertyDependencyGraphBuilder.GetAlgorithmSummary(owner, memos, context).MemberSeeds, failAt);
            var level = lastLevel = new PropertyDependencyGraphBuilder.LevelContext(owner, members, memos);
            return PropertyDependencyGraphBuilder.ExpandAtLevel(seed, level);
        }
        var shared = new PropertyDependencyGraphBuilder.SummaryMemo();
        var failure = Assert.Throws<InvalidOperationException>(() => Settle(shared, failAt: "P20"));
        Assert.Equal(FailingMemberMap.Message, failure.Message);
        Assert.Null(lastLevel!.ExpandedSeeds);
        var retried = Settle(shared, failAt: null);
        Assert.Null(lastLevel!.ExpandedSeeds);
        var fresh = Settle(new PropertyDependencyGraphBuilder.SummaryMemo(), failAt: null);
        Assert.Equal(fresh.ContentKey, retried.ContentKey);
        Assert.Equal(0, shared.ExpansionCycleCuts);
    }

    // A level's member map whose lookup fails for one member (the level expansion asks it whether the
    // level declares a visible name before carrying that name outward).
    private sealed class FailingMemberMap(IReadOnlyDictionary<string, PropertyDependencyGraphBuilder.SummarySeed> inner, string? failAt)
        : IReadOnlyDictionary<string, PropertyDependencyGraphBuilder.SummarySeed>
    {
        public const string Message = "member map failure";

        public PropertyDependencyGraphBuilder.SummarySeed this[string key] => inner[key];
        public IEnumerable<string> Keys => inner.Keys;
        public IEnumerable<PropertyDependencyGraphBuilder.SummarySeed> Values => inner.Values;
        public int Count => inner.Count;
        public bool ContainsKey(string key)
            => key == failAt ? throw new InvalidOperationException(Message) : inner.ContainsKey(key);
        public bool TryGetValue(string key, [System.Diagnostics.CodeAnalysis.MaybeNullWhen(false)] out PropertyDependencyGraphBuilder.SummarySeed value)
        {
            if (key == failAt) throw new InvalidOperationException(Message);
            return inner.TryGetValue(key, out value);
        }
        public IEnumerator<KeyValuePair<string, PropertyDependencyGraphBuilder.SummarySeed>> GetEnumerator() => inner.GetEnumerator();
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    // ── Shared members, the expansion cache and the reference set ────────────

    [Fact]
    public void OpenedMemberDiamonds_ShareChangedExpansionsAndCompleteSettlements()
    {
        FrontEndTraversalObservations? previous = null;
        foreach (var length in new[] { 8, 16, 32 })
        {
            var observations = new FrontEndTraversalObservations();
            var source = Diamond(length, terminal: "p");
            var owner = Member(Exposed(source, observations), "O").Value;
            for (var i = 1; i <= length; i++)
            {
                AssertRequires(Member(owner, $"P{i}"));
                AssertRequires(Member(owner, $"P{i}", $"A{i}"), ("p", 1));
                AssertRequires(Member(owner, $"P{i}", $"B{i}"), ("p", 1));
            }
            AssertRequires(Member(owner, "R"), ("p", 0));
            Assert.Equal(length + 2L, observations.SummaryMemberExpansions);
            Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, 7L * length * length);
            Assert.InRange(observations.SummaryKeyCharacters, 1, 1000L * length * length);
            if (previous is not null)
            {
                Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, 5 * previous.RequiredAncestorSettlementFrames);
                Assert.InRange(observations.SummaryKeyCharacters, 1, 5 * previous.SummaryKeyCharacters);
            }
            previous = observations;
        }

        var constant = Member(SourceProvenance.ParseValid(Diamond(8, "5")).Root, "O").Value;
        AssertRequires(Member(constant, "R"));
        Assert.Equal("160", Assert.IsType<RunResult.Success>(KatLangEngine.Run(Diamond(4, "p", "O(1) + O(9)"))).ToDisplayString());
    }

    private static string Diamond(int length, string terminal, string call = "1")
    {
        var source = new System.Text.StringBuilder("O(p) = {\n");
        for (var i = 1; i <= length; i++)
        {
            source.Append($"P{i} = {{\n");
            if (i < length)
                source.Append($"open P{i + 1}\n");
            var value = i == length ? terminal : $"A{i + 1} + B{i + 1}";
            source.Append($"public A{i} = {value}\npublic B{i} = {value}\n0\n}}\n");
        }
        return source.Append("R = { open P1\nA1 + B1 }\nR\n}\n").Append(call).ToString();
    }

    [Fact]
    public void ExpansionCache_EndsBeforeTheNextMemberMapUpdate()
    {
        var algorithm = SourceProvenance.ParseValid("D = 0\n0").Root;
        var memo = new PropertyDependencyGraphBuilder.SummaryMemo();
        var memos = PropertyDependencyGraphBuilder.CreateWalkMemos(memo, observations: null, AnalyzedStaticStructures.ForBoundAst(algorithm));
        var summaries = new Dictionary<string, PropertyDependencyGraphBuilder.SummarySeed>(StringComparer.Ordinal)
        {
            ["D"] = new(["p"]),
        };
        var level = new PropertyDependencyGraphBuilder.LevelContext(algorithm, summaries, memos);
        var seed = new PropertyDependencyGraphBuilder.SummarySeed(visiblePropertyDependencyNames: ["D"]);
        var first = PropertyDependencyGraphBuilder.ExpandAtLevel(seed, level);
        Assert.Equal(["p"], first.RequiredAncestorOwnedParameterNames);
        summaries["D"] = new(["q"]);
        var second = PropertyDependencyGraphBuilder.ExpandAtLevel(seed, level);
        Assert.Equal(["q"], second.RequiredAncestorOwnedParameterNames);
        Assert.Equal(["p"], first.RequiredAncestorOwnedParameterNames);
    }

    /// <summary>
    /// The pending-reference set keeps ONE entry per reference — its origin, selection, head and member
    /// steps — and a repeated reference keeps only the owners EVERY occurrence binds (intersection):
    /// (requirements − owner) ∪ requirements is the whole requirement. References that differ in head or
    /// member path stay apart, each with its own bound owners.
    /// </summary>
    [Fact]
    public void PendingReferenceSet_KeepsOneEntryPerReference_AndNarrowsBoundOwnersByIntersection()
    {
        var root = SourceProvenance.ParseValid("F(a) = a\nG(b) = b\n0").Root;
        var owner = root.Properties[0].Value;
        var other = root.Properties[1].Value;
        static PendingReference Reference(string head, params Algorithm[] bound) => new(head, [], bound);

        // Equal references are one entry.
        Assert.Single(new PendingReferenceSet([Reference("V"), Reference("V")]));
        Assert.Same(owner, Assert.Single(Assert.Single(new PendingReferenceSet([Reference("V", owner), Reference("V", owner)])).BoundOwners));

        // An occurrence that binds nothing unbinds the entry, in either order.
        Assert.Empty(Assert.Single(new PendingReferenceSet([Reference("V", owner), Reference("V")])).BoundOwners);
        Assert.Empty(Assert.Single(new PendingReferenceSet([Reference("V"), Reference("V", owner)])).BoundOwners);

        // Only the owners every occurrence binds stay bound.
        Assert.Same(other, Assert.Single(Assert.Single(new PendingReferenceSet([Reference("V", owner, other), Reference("V", other)])).BoundOwners));
        Assert.Empty(Assert.Single(new PendingReferenceSet([Reference("V", owner), Reference("V", other)])).BoundOwners);

        // A different head or member path is a different reference; narrowing one leaves the others alone.
        var apart = new PendingReferenceSet([Reference("V", owner), Reference("W", owner), new PendingReference("V", ["X"], [owner]), Reference("W")]);
        Assert.Equal(3, apart.Count);
        Assert.Equal(["V", "W", "V"], apart.Select(reference => reference.Head));
        Assert.Same(owner, Assert.Single(apart.First().BoundOwners));
        Assert.Empty(apart.Single(reference => reference.Head == "W").BoundOwners);
        Assert.Same(owner, Assert.Single(apart.Single(reference => reference.Members.Count == 1).BoundOwners));

        // Set equality is by content, bound owners included.
        Assert.True(new PendingReferenceSet([Reference("V", owner), Reference("V")]).SetEquals(new PendingReferenceSet([Reference("V")])));
        Assert.False(new PendingReferenceSet([Reference("V", owner)]).SetEquals(new PendingReferenceSet([Reference("V")])));
    }
}

/// <summary>
/// An independent model of mutually reading libraries inside <c>O(x0, x1, x2)</c>: library <c>L(i)</c>
/// publishes <c>V = P(i)</c>, and <c>P(i)</c> lists items — an input, a dotted read <c>L(j).V</c>, an opened
/// read <c>{ open L(j) V }</c>, an ambiguous open of two libraries (selects nothing), a duplicate open of
/// one (one provider), an inline provider beside a dotted read, a parameterized local reading through an
/// open (its own parameter bound), a local <c>V</c> shadowing the open, and an indirect local read. The
/// expected requirements are the least fixed point of plain set unions over the reads each item makes,
/// written without any of the analysis' machinery; a root-level <c>V</c> shadows every bare <c>V</c>.
/// </summary>
internal static class OpenLibraryOracle
{
    internal enum ItemKind
    {
        Input,
        Dotted,
        Opened,
        Ambiguous,
        Duplicate,
        Inline,
        BoundOwner,
        LocalShadow,
        Indirect,
    }

    internal readonly record struct Item(ItemKind Kind, int A, int B = 0);

    internal sealed record Library(Item[] Items);

    private static string Render(Item item) => item.Kind switch
    {
        ItemKind.Input => $"x{item.A}",
        ItemKind.Dotted => $"L{item.A}.V",
        ItemKind.Opened => $"{{ open L{item.A}\nV }}",
        ItemKind.Ambiguous => $"{{ open L{item.A}, L{item.B}\nV }}",
        ItemKind.Duplicate => $"{{ open L{item.A}, L{item.A}\nV }}",
        ItemKind.Inline => $"{{ open {{ public V = 3 }}\nV + L{item.A}.V }}",
        ItemKind.BoundOwner => $"{{ Q(y) = {{ open L{item.A}\nV + y }}\nQ(0) }}",
        ItemKind.LocalShadow => $"{{ open L{item.A}\nV = 9\nV }}",
        ItemKind.Indirect => $"{{ open L{item.A}\nW = V\nW }}",
        _ => throw new ArgumentOutOfRangeException(nameof(item)),
    };

    /// <summary>The libraries this item reads (as library indices).</summary>
    private static IEnumerable<int> Reads(Item item, bool shadow) => item.Kind switch
    {
        ItemKind.Input or ItemKind.Ambiguous or ItemKind.LocalShadow => [],
        ItemKind.Dotted or ItemKind.Inline => [item.A],
        ItemKind.Opened or ItemKind.Duplicate or ItemKind.BoundOwner or ItemKind.Indirect => shadow ? [] : [item.A],
        _ => throw new ArgumentOutOfRangeException(nameof(item)),
    };

    /// <summary>Declarations L0, P0, L1, P1, … in <paramref name="order"/> (identity when null).</summary>
    internal static string Render(Library[] libraries, IReadOnlyList<int>? order, bool shadow, string call)
    {
        var declarations = new List<string>();
        for (var i = 0; i < libraries.Length; i++)
        {
            declarations.Add($"L{i} = {{ public V = P{i}\n1 }}");
            declarations.Add($"P{i} = " + string.Join(", ", libraries[i].Items.Select(Render).DefaultIfEmpty("1")));
        }

        var ordered = order is null ? declarations : order.Select(index => declarations[index]).ToList();
        return (shadow ? "V = 7\n" : "") + "O(x0, x1, x2) = {\n" + string.Join("\n", ordered) + "\n1\n}\n" + call;
    }

    internal static HashSet<string>[] Expected(Library[] libraries, bool shadow)
    {
        var expected = libraries.Select(library => library.Items.Where(item => item.Kind == ItemKind.Input)
            .Select(item => $"x{item.A}").ToHashSet(StringComparer.Ordinal)).ToArray();
        bool changed;
        do
        {
            changed = false;
            for (var i = 0; i < libraries.Length; i++)
            {
                foreach (var read in libraries[i].Items.SelectMany(item => Reads(item, shadow)))
                {
                    foreach (var name in expected[read])
                        changed |= expected[i].Add(name);
                }
            }
        }
        while (changed);
        return expected;
    }

    /// <summary>Whether the source reaches an ambiguous open (reported by parameter detection).</summary>
    internal static bool HasAmbiguity(Library[] libraries, bool shadow)
        => !shadow && libraries.Any(library => library.Items.Any(item => item.Kind == ItemKind.Ambiguous && item.A != item.B));

    /// <summary>Every <c>P(i)</c> and library member <c>L(i).V</c> carries exactly the oracle's requirements.</summary>
    internal static void AssertMatches(Library[] libraries, bool shadow, Algorithm owner, string? context = null)
    {
        var expected = Expected(libraries, shadow);
        for (var i = 0; i < libraries.Length; i++)
        {
            var names = expected[i].Order(StringComparer.Ordinal).ToArray();
            var p = owner.Properties.Single(property => property.Name == $"P{i}");
            var v = owner.Properties.Single(property => property.Name == $"L{i}").Value.Properties.Single(property => property.Name == "V");
            foreach (var (property, depth) in new[] { (p, 0), (v, 1) })
            {
                Assert.True(names.SequenceEqual(property.RequiredAncestorParameters), $"{property.Name} of library {i}: {context}");
                Assert.Equal(names.Select(name => new CapturedParameterRequirement(name, depth)), property.CaptureRequirements ?? []);
                Assert.Equal(names.Length == 0 ? PropertyExposure.Exported : PropertyExposure.LocalOnlyCapturedAncestorParameters, property.Exposure);
            }
        }
    }

    /// <summary>The exposure pass after the preceding front-end stages, allowing only ambiguous-open detection diagnostics.</summary>
    internal static Algorithm.User ExposedAllowingAmbiguity(string source, FrontEndTraversalObservations? observations)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var detectedInput = ParameterDetector.DetectPrevalidated(syntax);
        var (detected, detectionDiagnostics) = detectedInput;
        Assert.All(detectionDiagnostics, diagnostic => Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code));
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detectedInput, observations: null, diagnostics);
        Assert.Empty(diagnostics);
        return (Algorithm.User)PropertyExposureResolver.Resolve(resolved, observations);
    }

    /// <summary>The scalable family of reproducer B (see <c>GeneratedReproducerBFamily_MatchesTheOracle_WithPolynomialWork</c>).</summary>
    internal static Library[] ReproducerBFamily(int size)
        => Enumerable.Range(0, size).Select(i => new Library(
        [
            new(ItemKind.Input, i % 3),
            new(ItemKind.Inline, (i + 2) % size),
            new(ItemKind.Opened, (i + 3) % size),
            new(ItemKind.Ambiguous, (i + 1) % size, (i + 4) % size),
            new(ItemKind.Duplicate, (i + 5) % size),
            new(ItemKind.Dotted, (i + 1) % size),
        ])).ToArray();

    /// <summary>Random libraries of every item kind (ambiguous items name two distinct libraries).</summary>
    internal static Library[] Random(Random random, int size, int maxReads)
        => Enumerable.Range(0, size).Select(_ =>
        {
            var items = Enumerable.Range(0, 3).Where(_ => random.Next(3) == 0).Select(p => new Item(ItemKind.Input, p)).ToList();
            var reads = random.Next(maxReads + 1);
            for (var k = 0; k < reads; k++)
            {
                var kind = (ItemKind)random.Next(1, Enum.GetValues<ItemKind>().Length);
                var a = random.Next(size);
                var b = (a + 1 + random.Next(size - 1)) % size;
                items.Add(new Item(kind, a, b));
            }

            return new Library([.. items]);
        }).ToArray();
}
