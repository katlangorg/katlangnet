namespace KatLang.Tests;

/// <summary>
/// EXPOSURE-OPEN-1: the exposure pass on members read through <c>open</c> inside a parameterized owner.
/// A resolved open candidate carries the seed its provider charges, and that seed can hold further
/// candidates — a chain of N members opened from one another and read at the owner nests N deep. Two
/// costs followed from that nesting. (A) Every enclosing link rebuilt the whole nesting below it (the
/// lexical-absence reduction and parameter qualification walked it) and re-serialized it into a
/// content key, so a chain of N cost O(N³) characters and copies: N = 300 took 9 s and 20 GB. (B) A
/// candidate's seed grows during the member fixed point, and a reference with the smaller seed was a
/// DIFFERENT entry from the same reference with the larger one; around a cycle of mutually reading
/// libraries the stale entry circulated forever and the analysis never terminated. Now candidates are
/// shared immutable nodes whose deep facts decide whether a transformation can change them, their keys
/// name their seeds by exact interned ids, and same-shape references unite their seeds.
///
/// <para>The regression oracle is deterministic work: <see cref="FrontEndTraversalObservations"/>
/// counts the candidate rebuilds, the key characters, and the settlement frames the old shape
/// amplified, at several sizes, against absolute polynomial bounds and doubling ratios. Classification
/// is pinned exactly — every property's exposure, required names, and owner-relative capture depths —
/// against an independent fixed-point oracle (<see cref="OpenLibraryOracle"/>).</para>
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
        var (detected, detectionDiagnostics) = ParameterDetector.DetectPrevalidated(syntax);
        Assert.Empty(detectionDiagnostics);
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations: null, diagnostics);
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
        => AstStructuralDepthProcessTests.RunOnThreadWithStack(1024 * 1024, work, TimeSpan.FromSeconds(60));

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
    /// The work of the opened chain at three doubling sizes. Each link is settled at the owner once and
    /// held by reference by the link above it, so its seed is built once (N candidate rebuilds in all)
    /// and its key costs its own entries (O(N) characters in all). The exposure settlement of each
    /// link's level still walks the links below it — exactly N(N + 3) frames, unchanged by the repair
    /// and of the same quadratic order the root-level and dotted chains pay.
    /// Formerly every link rebuilt and re-serialized the nesting below it (the same operations, counted on
    /// the former implementation): 560 rebuilds and 143,522 key characters at N = 16, 8,384 and 9,110,136 at N = 64.
    /// </summary>
    [Fact]
    public void NestedOwnerOpenedChain_BuildsEachCandidateOnce_AndSettlesQuadratically()
    {
        var previous = default(FrontEndTraversalObservations);
        foreach (var length in new[] { 16, 32, 64 })
        {
            var observations = new FrontEndTraversalObservations();
            var owner = Member(Exposed(NestedOwnerChain(length), observations), "O").Value;
            AssertRequires(Member(owner, "R"));
            AssertRequires(Member(owner, "P1", "A1"));

            Assert.Equal(length, observations.OpenCandidateSeedRebuilds);
            Assert.InRange(observations.OpenCandidateKeyCharacters, 1, 40L * length);
            Assert.InRange(observations.SummaryKeyCharacters, 1, 512L * length);
            Assert.Equal((long)length * (length + 3), observations.RequiredAncestorSettlementFrames);
            Assert.Equal(length + 2L, observations.SummaryMemberExpansions);
            Assert.InRange(observations.OpenCandidateFactProbes, 1, 4L * length);
            Assert.Equal(0, observations.PendingReferenceSeedMerges);
            if (previous is not null)
            {
                Assert.InRange(observations.OpenCandidateKeyCharacters, 1, 5 * previous.OpenCandidateKeyCharacters / 2);
                Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, 9 * previous.RequiredAncestorSettlementFrames / 2);
            }

            previous = observations;
        }
    }

    // ── Controls ─────────────────────────────────────────────────────────────

    /// <summary>
    /// The same chain at the root (whose members are settled only by the exposure pass, never nested in
    /// a candidate), and inside the owner through dotted reads (path expansions, no candidates): no
    /// candidate is ever built, and settlement is the same quadratic.
    /// </summary>
    [Theory]
    [InlineData("root")]
    [InlineData("dotted")]
    public void ControlChains_BuildNoCandidates(string shape)
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

            Assert.Equal(0, observations.OpenCandidateSeedRebuilds);
            Assert.Equal(0, observations.OpenCandidateKeyCharacters);
            Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, (long)length * (length + 3));
        }

        var shortSource = shape == "root" ? RootChain(6) : NestedOwnerChain(6, "dotted");
        Assert.Equal("10", Assert.IsType<RunResult.Success>(KatLangEngine.Run(shortSource)).ToDisplayString());
    }

    /// <summary>
    /// The opened chain whose terminal reads the owner's parameter: every link requires <c>p</c> one
    /// level out, and the reader directly. Each link is qualified by the owner once more (2N rebuilds),
    /// and an activation-specific value proves the classification: a link wrongly classified exported
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
            Assert.Equal(2L * length, observations.OpenCandidateSeedRebuilds);
            Assert.InRange(observations.OpenCandidateKeyCharacters, 1, 64L * length);
            Assert.Equal((long)length * (length + 3), observations.RequiredAncestorSettlementFrames);
            Assert.InRange(observations.OpenCandidateFactProbes, 1, 8L * length);
        }

        const int Short = 7;
        Assert.Equal("22", Assert.IsType<RunResult.Success>(
            KatLangEngine.Run(NestedOwnerChain(Short, last: "p", call: "O(1) + O(9)"))).ToDisplayString());
    }

    /// <summary>Alternating opened and dotted links, each through a local intermediary before the public member.</summary>
    [Fact]
    public void MixedChain_WithLocalIntermediaries_IsExported_AndBuildsEachOpenedCandidateOnce()
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

            Assert.InRange(observations.OpenCandidateSeedRebuilds, 1, length);
            Assert.InRange(observations.OpenCandidateKeyCharacters, 1, 40L * length);
            Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, (long)length * (length + 3));
        }

        Assert.Equal("10", Assert.IsType<RunResult.Success>(KatLangEngine.Run(NestedOwnerChain(6, "mixed"))).ToDisplayString());
    }

    // ── Shared candidates under equal and different contexts ─────────────────

    /// <summary>
    /// K readers of one opened chain in ONE owner reach the same candidates: each reader is classified
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
        Assert.Equal(2L * Length, observations.OpenCandidateSeedRebuilds);
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
    /// stale candidate seed alive around the library cycle. The outer owner is never called, so this is
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
        Assert.InRange(observations.OpenCandidateSeedRebuilds, 1, 120);
        Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, 120);
        Assert.InRange(observations.PendingReferenceSeedMerges, 1, 40);
    }

    /// <summary>
    /// The minimal core of B: two libraries reading each other through inline-provider blocks and
    /// opens, one of them reading a third library whose member captures the owner's input. The opened
    /// candidate of that third library is first settled with an empty seed and later with <c>x0</c>;
    /// as separate entries the two circulated around the cycle forever (no termination). United, the
    /// fixed point is reached in a few evaluations.
    /// </summary>
    [Fact]
    public void MutuallyReadingLibraries_ReachTheirFixedPoint_WhenACandidateSeedGrowsLate()
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
        Assert.InRange(observations.PendingReferenceSeedMerges, 1, 20);
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
            Assert.InRange(observations.OpenCandidateSeedRebuilds, 1, 16 * n * n);
            Assert.InRange(observations.OpenCandidateKeyCharacters, 1, 256 * n * n);
            // Full serialized seed keys include the growing reference sets, before their ids exist.
            Assert.InRange(observations.SummaryKeyCharacters, 1, 512 * n * n * n);
            Assert.InRange(observations.OpenCandidateFactProbes, 1, 64 * n * n * n);
            Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, 64 * n);
            if (previous is not null)
            {
                Assert.InRange(observations.SummaryMemberEvaluations, 1, 5 * previous.SummaryMemberEvaluations);
                Assert.InRange(observations.OpenCandidateSeedRebuilds, 1, 5 * previous.OpenCandidateSeedRebuilds);
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
        Assert.InRange(observations.OpenCandidateSeedRebuilds, 1, 4L * length * length);
    }

    /// <summary>
    /// A long opened chain with a reader at the owner, on a 1 MiB thread, in process: 400 links pin
    /// that the cubic cost does not come back (the implementation before EXPOSURE-OPEN-1 took 9 s at
    /// 300 links and 58 s at 500) — exactly two candidate rebuilds per link. Settling each link's charge
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
        Assert.Equal(2L * Length, observations.OpenCandidateSeedRebuilds);
    }

    /// <summary>
    /// OOS-22: the explicit-stack expansion holds the chain's active local-head keys and the level's
    /// expansion cache in suspended frames. An expansion interrupted deep inside the chain (here a
    /// member map that fails at link 20) must release every one of them, exactly as the recursion's
    /// <c>finally</c> blocks did: the retry on the SAME memo cuts no cycle and settles the same
    /// candidate a fresh analysis settles, instead of serving an unfinished link as an empty charge.
    /// </summary>
    [Fact]
    public void InterruptedChainExpansion_ReleasesItsActiveState_AndTheRetryMatchesAFreshAnalysis()
    {
        const int Length = 40;
        var owner = Member(SourceProvenance.ParseValid(NestedOwnerChain(Length, last: "p")).Root, "O").Value;
        var seed = new PropertyDependencyGraphBuilder.SummarySeed(
            pendingReferences: [new PendingReference("A1", [], [new UnresolvedOpenCandidate("P1", [], 0)])]);

        PropertyDependencyGraphBuilder.LevelContext? lastLevel = null;
        (ResolvedOpenCandidate Candidate, long Cuts) Settle(PropertyDependencyGraphBuilder.SummaryMemo memo, string? failAt)
        {
            var memos = PropertyDependencyGraphBuilder.CreateWalkMemos(memo, observations: null);
            var members = new FailingMemberMap(PropertyDependencyGraphBuilder.GetAlgorithmSummary(owner, memos).MemberSeeds, failAt);
            var level = lastLevel = new PropertyDependencyGraphBuilder.LevelContext(owner, members, memos);
            var cuts = memo.ExpansionCycleCuts;
            var expanded = PropertyDependencyGraphBuilder.ExpandAtLevel(seed, level);
            Assert.Null(level.ExpandedSeeds);
            var reference = Assert.Single(expanded.PendingReferences);
            return (Assert.IsType<ResolvedOpenCandidate>(Assert.Single(reference.Candidates)), memo.ExpansionCycleCuts - cuts);
        }

        var shared = new PropertyDependencyGraphBuilder.SummaryMemo();
        var failure = Assert.Throws<InvalidOperationException>(() => Settle(shared, failAt: "P20"));
        Assert.Equal(FailingMemberMap.Message, failure.Message);
        Assert.Empty(shared.ActiveLocalHeads ?? []);
        Assert.Empty(shared.ActiveLocalPaths ?? []);
        Assert.Null(lastLevel!.ExpandedSeeds);

        var (retried, retryCuts) = Settle(shared, failAt: null);
        var (fresh, freshCuts) = Settle(new PropertyDependencyGraphBuilder.SummaryMemo(), failAt: null);
        Assert.Equal(0, freshCuts);
        Assert.Equal(0, retryCuts);
        Assert.Empty(shared.ActiveLocalHeads ?? []);
        // Every link settled: the outermost candidate's deep facts reach the terminal's `p` and every
        // nested link's pending head, exactly as a fresh analysis's do.
        Assert.Equal(fresh.Facts.Count, retried.Facts.Count);
        Assert.True(retried.RequiresAny(new HashSet<string>(["p"], StringComparer.Ordinal), owner));
        Assert.True(shared.SeedFacts.HasHead(retried.Facts, $"A{Length}"));
    }

    // A level's member map whose presence test fails for one member (the escaping-candidate settlement
    // asks it whether the level declares a carried open target's head).
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
            => inner.TryGetValue(key, out value);
        public IEnumerator<KeyValuePair<string, PropertyDependencyGraphBuilder.SummarySeed>> GetEnumerator() => inner.GetEnumerator();
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    // ── The merge rule itself ────────────────────────────────────────────────

    [Fact]
    public void SharedCandidateDag_TransformsAndUnionsOncePerDistinctNode_AndSeparatesOwners()
    {
        foreach (var depth in new[] { 8, 16, 32 })
        {
            var observations = new FrontEndTraversalObservations();
            var memo = new PropertyDependencyGraphBuilder.SummaryMemo(observations);
            var root = SourceProvenance.ParseValid("F(p) = p\nG(p) = p\n0").Root;
            var owner = root.Properties[0].Value;
            var otherOwner = root.Properties[1].Value;
            var identity = OpenProviderIdentity.DeclaredAtRoot(owner);
            ResolvedOpenCandidate Dag(string name)
            {
                var candidate = new ResolvedOpenCandidate(new PropertyDependencyGraphBuilder.SummarySeed([name]), 0, identity, memo);
                for (var i = 0; i < depth; i++)
                {
                    var seed = new PropertyDependencyGraphBuilder.SummarySeed();
                    seed.PendingReferences.Add(new PendingReference("a", [], [candidate]));
                    seed.PendingReferences.Add(new PendingReference("b", [], [candidate]));
                    candidate = new ResolvedOpenCandidate(seed, 0, identity, memo);
                }
                return candidate;
            }

            var dag = Dag("p");
            var names = new HashSet<string>(["p"], StringComparer.Ordinal);
            var before = observations.OpenCandidateSeedRebuilds;
            var qualified = dag.QualifiedBy(owner, names);
            Assert.Equal(depth + 1, observations.OpenCandidateSeedRebuilds - before);
            var second = dag.QualifiedBy(otherOwner, names);
            var leaf = qualified;
            var secondLeaf = second;
            for (var i = 0; i < depth; i++)
            {
                var references = leaf.Seed.PendingReferences.ToArray();
                var firstChild = Assert.IsType<ResolvedOpenCandidate>(Assert.Single(references[0].Candidates));
                Assert.Same(firstChild, Assert.Single(references[1].Candidates));
                leaf = firstChild;
                secondLeaf = Assert.IsType<ResolvedOpenCandidate>(Assert.Single(secondLeaf.Seed.PendingReferences.First().Candidates));
            }
            Assert.Equal(new OwnerQualifiedParameter("p", owner), Assert.Single(leaf.Seed.OwnerQualifiedParameters));
            Assert.Equal(new OwnerQualifiedParameter("p", otherOwner), Assert.Single(secondLeaf.Seed.OwnerQualifiedParameters));

            before = observations.OpenCandidateSeedRebuilds;
            var reduced = dag.UnderMissingLexicalHead("a");
            // One reduction per node, plus the unions of the surviving `b` branches.
            Assert.InRange(observations.OpenCandidateSeedRebuilds - before, 1, 2 * depth);
            Assert.True(reduced.RequiresAny(names, owner));

            before = observations.OpenCandidateSeedRebuilds;
            var stripped = dag.Seed.Clone();
            stripped.RemoveRequiredAncestorOwnedParameterNames(names, owner, ownerHasParameters: true, observations);
            Assert.InRange(observations.OpenCandidateSeedRebuilds - before, 1, depth);
            Assert.False(new ResolvedOpenCandidate(stripped, 0, identity, memo).RequiresAny(names, owner));

            before = observations.OpenCandidateSeedRebuilds;
            var united = dag.UnitedWith(Dag("q"));
            Assert.Equal(depth + 1, observations.OpenCandidateSeedRebuilds - before);
            Assert.True(united.RequiresAny(names, owner));
            Assert.True(united.RequiresAny(new HashSet<string>(["q"], StringComparer.Ordinal), owner));
            Assert.InRange(observations.SummaryKeyCharacters, 1, 4000L * (depth + 1));
        }
    }

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
            Assert.Equal(3L * length, observations.OpenCandidateSeedRebuilds);
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
        var memos = PropertyDependencyGraphBuilder.CreateWalkMemos(memo, observations: null);
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
    /// The pending-reference set unites references that differ only in a resolved candidate's charged
    /// seed (one provider: one charge, the union), keeps references of different bound owners apart
    /// (their exclusions differ), and still narrows equal references' bound owners by intersection.
    /// </summary>
    [Fact]
    public void PendingReferenceSet_UnitesSameShapeSeeds_AndKeepsBoundOwnersExact()
    {
        var observations = new FrontEndTraversalObservations();
        var memo = new PropertyDependencyGraphBuilder.SummaryMemo(observations);
        var provider = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid("L = { public V = 1\n0 }\n0").Root.Properties.Single().Value);
        var owner = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid("F(a) = a\n0").Root.Properties.Single().Value);
        var identity = OpenProviderIdentity.DeclaredAtRoot(provider);
        PendingReference Reference(string[] required, params Algorithm[] bound)
            => new("V", [], [new ResolvedOpenCandidate(new PropertyDependencyGraphBuilder.SummarySeed(required), 0, identity, memo)], bound);

        var set = new PendingReferenceSet([Reference([]), Reference(["x0"])]);
        var united = Assert.Single(set);
        var candidate = Assert.IsType<ResolvedOpenCandidate>(Assert.Single(united.Candidates));
        Assert.Equal(["x0"], candidate.Seed.RequiredAncestorOwnedParameterNames);
        Assert.Equal(1, observations.PendingReferenceSeedMerges);

        // Either order gives the same content.
        Assert.True(set.SetEquals(new PendingReferenceSet([Reference(["x0"]), Reference([])])));

        // A bound owner is part of the shape: (V - owner) and V stay two references.
        var bound = new PendingReferenceSet([Reference(["x0"], owner), Reference(["x1"])]);
        Assert.Equal(2, bound.Count);

        // Equal references narrow their bound owners, and the narrowed reference unites with the unbound one.
        var narrowed = new PendingReferenceSet([Reference(["x0"], owner), Reference(["x1"]), Reference(["x0"])]);
        var only = Assert.Single(narrowed);
        Assert.Empty(only.BoundOwners);
        Assert.Equal(["x0", "x1"], Assert.IsType<ResolvedOpenCandidate>(Assert.Single(only.Candidates)).Seed.RequiredAncestorOwnedParameterNames.Order(StringComparer.Ordinal));
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
        var (detected, detectionDiagnostics) = ParameterDetector.DetectPrevalidated(syntax);
        Assert.All(detectionDiagnostics, diagnostic => Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code));
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations: null, diagnostics);
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
