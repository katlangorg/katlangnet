using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Two exposure laws of a static member path inside <c>F(y)</c> (independent audit of 2026-11-14, sections
/// 1.1 and SPECS 1–2; programs named as in the audit's probes).
///
/// <para>EVERY EDGE'S FALLBACK IS CHARGED. A path is one pending reference over all its steps, so each
/// intermediate edge whose structural lookup may miss (<c>Box.S.T</c> inside <c>Box.S.T.U</c>: <c>S</c> lacks
/// <c>T</c>, so the evaluator calls <c>T(Box.S)</c>) charges that fallback callee, for a named and an
/// inline-block head alike. A reader that dropped it stayed exported, and the run-wide cache of an exported
/// binding served the first activation's value to the next: <c>F(1), F(2)</c> gave (6, 6).</para>
///
/// <para>A BLOCK WRITTEN IN A DECONSTRUCTION RIGHT-HAND SIDE COUNTS THE SOURCE'S LEVEL. The evaluators wire
/// such a block under the synthetic source property, so a member's capture position is one more than the
/// written chain gives; a position counted on the written chain named a level that binds nothing, and the
/// selected member was refused inside its own owner's call.</para>
///
/// <para>Every program runs on <c>Run</c>, ordinary <c>RunAsync</c> and the asynchronous evaluator.</para>
/// </summary>
public sealed class ExposureFallbackEdgeTests(Xunit.Abstractions.ITestOutputHelper output)
{
    private const string NamedHead =
        "F(y) = {\n  T(v) = v + y\n  U(v) = v\n  Box = { public S = 5 }\n  A = Box.S.T.U + 0\n  A\n}\n";

    private const string FirstStepMiss =
        "F(y) = {\n  T(v) = v + y\n  U(v) = v\n  Box = { public S = 1\n    5 }\n  A = Box.T.U + 0\n  A\n}\n";

    private const string BlockHead =
        "F(y) = {\n  T(v) = v + y\n  U(v) = v\n  A = { public S = 5 }.S.T.U + 0\n  A\n}\n";

    private const string FinalEdgeOnly =
        "F(y) = {\n  T(v) = v + y\n  Box = { public S = 5 }\n  A = Box.S.T + 0\n  A\n}\n";

    // Every step is a declared member, beside same-named callables that read y: a structural hit charges no fallback.
    private const string DeclaredPath =
        "F(y) = {\n  Lib = { public Sub = { public Q = 4 } }\n  Sub(v) = v + y\n  Q(v) = v + y\n  A = Lib.Sub.Q + 0\n  A\n}\n";

    private const string DeclaredPathThenFallback =
        "F(y) = {\n  Lib = { public Sub = { public Q = 4 } }\n  Sub(v) = v + y\n  Q(v) = v + y\n  U(v) = v\n  A = Lib.Sub.Q.U + 0\n  A\n}\n";

    private const string BlockHeadedSource =
        "F(y) = {\n  a, b = { public Q = (y, y + 1) }.Q\n  a, b\n}\n";

    private const string NamedSource =
        "F(y) = {\n  Box = { public Q = (y, y + 1) }\n  a, b = Box.Q\n  a, b\n}\n";

    private static readonly HostOperation AsyncRouteMarker = HostOperation.CreateAsync("UnusedExposureFallbackEdgeRoute",
        static (_, _) => throw new InvalidOperationException("The route marker must never execute."));

    /// <summary>The three routes of <c>ExposureAccessCheckTests.BothEngines</c>, with optional host operations.</summary>
    private static async Task<RunResult[]> Routes(string source, params HostOperation[] operations)
    {
        var sync = operations.Length == 0 ? null : new RunOptions { HostOperations = HostOperations.Create(operations) };
        var forced = HostOperations.Create([.. operations, AsyncRouteMarker]);
        Assert.True(forced.ContainsAsynchronousOperations);
        return [KatLangEngine.Run(source, sync), await KatLangEngine.RunAsync(source, sync),
            await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = forced })];
    }

    private static async Task AssertValue(string source, string expected, params HostOperation[] operations)
    {
        SourceProvenance.ParseValid(source);
        foreach (var result in await Routes(source, operations))
            Assert.Equal(expected, SemanticExplorerHarness.Neutral(Assert.IsType<RunResult.Success>(result).Value));
    }

    private static async Task AssertRefused(string source, string property)
    {
        SourceProvenance.ParseValid(source);
        foreach (var result in await Routes(source))
        {
            var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
            Assert.Equal(KatLangErrorCode.LocalOnlyProperty, error.Code);
            Assert.Contains($"Property '{property}' on `F` is local-only", error.Message, StringComparison.Ordinal);
        }
    }

    private static Algorithm.User F(string source)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        return Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == "F").Value);
    }

    private static Property Member(Algorithm owner, string name) => Assert.Single(owner.Properties, property => property.Name == name);

    private static void AssertLocalOnly(Property property, params (string Name, int OwnerDepth)[] captures)
    {
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, property.Exposure);
        Assert.Equal(captures.Select(capture => capture.Name).Distinct().Order(StringComparer.Ordinal), property.RequiredAncestorParameters);
        Assert.Equal(captures.Select(capture => new CapturedParameterRequirement(capture.Name, capture.OwnerDepth)),
            Assert.IsAssignableFrom<IReadOnlyList<CapturedParameterRequirement>>(property.CaptureRequirements));
    }

    private static void AssertExported(Property property)
    {
        Assert.Equal(PropertyExposure.Exported, property.Exposure);
        Assert.Empty(property.RequiredAncestorParameters);
    }

    /// <summary>The one block written in the rows of <paramref name="f"/>'s only deconstruction source.</summary>
    private static Algorithm.User SourceBlock(Algorithm.User f, out Property source)
    {
        source = Assert.Single(f.Properties, property => property.Value is Algorithm.User { IsAssignmentDeconstructionSource: true });
        var row = Assert.Single(((Algorithm.User)source.Value).Output);
        while (row is Expr.DotCall edge) row = edge.Target;
        return Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(row).Algorithm);
    }

    // ── Intermediate-edge fallbacks ───────────────────────────────────────────────────────────────

    public static TheoryData<string, string> ReadersOfAFallbackEdge => new()
    {
        { "g01 named head, miss at the second step", NamedHead },
        { "g05 named head, miss at the first step", FirstStepMiss },
        { "g03 inline-block head, miss at the second step", BlockHead },
        { "g02 final edge only (control)", FinalEdgeOnly },
    };

    [Theory]
    [MemberData(nameof(ReadersOfAFallbackEdge))]
    public async Task PathWithAFallbackEdge_ChargesTheFallbackCallee(string name, string body)
    {
        _ = name;
        AssertLocalOnly(Member(F(body + "F(1)\n"), "A"), ("y", 0));

        await AssertValue(body + "F(1)\n", "6");
        await AssertValue(body + "F(2)\n", "7");
        // One run: an exported `A` held F(1)'s value for F(2).
        await AssertValue(body + "F(1), F(2)\n", "S[6, 7]");
        await AssertValue(body + "F(2), F(1)\n", "S[7, 6]");
        // g01e: the escaped read needs the activation the fallback callee reads.
        await AssertRefused(body + "F.A\n", "A");
        await AssertRefused(body + "F(1), F(2), F.A\n", "A");
    }

    [Fact]
    public async Task EveryMayFallbackOfALongerPath_IsCharged()
    {
        // Three fallback edges after the selected member; only the innermost one reads y.
        const string innermost = "F(y) = {\n  T(v) = v + y\n  U(v) = v\n  W(v) = v * 2\n  Box = { public S = 5 }\n  A = Box.S.T.U.W + 0\n  A\n}\n";
        AssertLocalOnly(Member(F(innermost + "F(1)\n"), "A"), ("y", 0));
        await AssertValue(innermost + "F(1), F(2)\n", "S[12, 14]");

        // The middle one reads y; the receiver is an argument-bearing final edge.
        const string middle = "F(y) = {\n  T(v) = v\n  U(v) = v + y\n  W(v, k) = v * k\n  Box = { public S = 5 }\n  A = Box.S.T.U.W(2) + 0\n  A\n}\n";
        AssertLocalOnly(Member(F(middle + "F(1)\n"), "A"), ("y", 0));
        await AssertValue(middle + "F(1), F(2)\n", "S[12, 14]");

        // A fallback that is an enclosing owner's parameter is charged like a written callee name.
        const string parameter = "Twice(v) = v * 2\nF(f) = {\n  U(v) = v\n  Box = { public S = 5 }\n  A = Box.S.f.U + 0\n  A\n}\nId(v) = v\n";
        AssertLocalOnly(Member(F(parameter + "F(Twice)\n"), "A"), ("f", 0));
        await AssertValue(parameter + "F(Twice), F(Id)\n", "S[10, 5]");
    }

    /// <summary>
    /// The charge is one leaf walk per intermediate edge: K readers of one fallback path, with a named or an
    /// inline-block head, cost linear summary work and linear settlement frames in K.
    /// </summary>
    [Theory]
    [InlineData("Box.S.T.U")]
    [InlineData("{ public S = 5 }.S.T.U")]
    public void ManyReadersOfAFallbackPath_AreChargedInLinearWork(string path)
    {
        var sizes = new[] { 100, 200, 400 };
        var expansions = new long[sizes.Length];
        var frames = new long[sizes.Length];
        var summaries = new long[sizes.Length];
        for (var k = 0; k < sizes.Length; k++)
        {
            var source = new System.Text.StringBuilder("F(y) = {\n  T(v) = v + y\n  U(v) = v\n  Box = { public S = 5 }\n");
            for (var i = 0; i < sizes[k]; i++) source.Append($"  A{i} = {path} + {i}\n");
            source.Append("  0\n}\nF(5)\n");
            var observations = new FrontEndTraversalObservations();
            var root = ExposureOpenChainComplexityTests.Exposed(source.ToString(), observations);
            for (var i = 0; i < sizes[k]; i++)
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"A{i}"), ("y", 0));
            expansions[k] = observations.DependencySeedExpansions;
            frames[k] = observations.RequiredAncestorSettlementFrames;
            summaries[k] = observations.DependencyAlgorithmSummaryComputations;
        }

        output.WriteLine($"{path}: seed expansions {string.Join(" / ", expansions)}; settlement frames {string.Join(" / ", frames)}; "
            + $"algorithm summaries {string.Join(" / ", summaries)}");
        // Doubling the readers at most a little more than doubles each count; a per-reader re-walk of the level
        // would give a ratio near 4. A count that does not grow at all (a shared settlement) is within the bound.
        for (var k = 1; k < sizes.Length; k++)
        {
            Assert.InRange((double)expansions[k] / expansions[k - 1], 1.5, 2.5);
            Assert.True(frames[k] <= 2.5 * frames[k - 1], $"settlement frames {frames[k - 1]} -> {frames[k]}");
            Assert.True(summaries[k] <= 2.5 * summaries[k - 1], $"algorithm summaries {summaries[k - 1]} -> {summaries[k]}");
        }
    }

    [Fact]
    public async Task DeclaredStructuralHits_ChargeNoFallback()
    {
        // `Lib.Sub.Q`: both edges select declared members, so the same-named callables that read y are never
        // called and the constant reader stays exported, inside and outside the call.
        AssertExported(Member(F(DeclaredPath + "F(1)\n"), "A"));
        await AssertValue(DeclaredPath + "F(1), F(2), F.A\n", "S[4, 4, 4]");

        // The declared prefix of a path that then falls back charges only the fallback that may be selected.
        AssertExported(Member(F(DeclaredPathThenFallback + "F(1)\n"), "A"));
        await AssertValue(DeclaredPathThenFallback + "F(1), F(2), F.A\n", "S[4, 4, 4]");
    }

    [Fact]
    public async Task EarlierBlockHeadValues_AreUnchanged()
    {
        // f01: a first-step miss reads the block's VALUE. f02: a later miss reads the reached member's.
        await AssertValue("F(y) = {\n  Twice(v) = v * 2\n  A = { public Q = 1\n    y }.Twice + 0\n  A\n}\nF(1), F(2)\n", "S[2, 4]");
        await AssertValue("F(y) = {\n  Twice(v) = v * 2\n  A = { public S = { public Q = 1\n    y } }.S.Twice + 0\n  A\n}\nF(1), F(2)\n", "S[2, 4]");

        // o02: a selected constant member never reads the block's value, so the reader stays exported.
        const string selected = "F(y) = {\n  A = { public Q = 5\n    y }.Q + 0\n  A\n}\n";
        AssertExported(Member(F(selected + "F(1)\n"), "A"));
        await AssertValue(selected + "F(1), F.A\n", "S[5, 5]");

        // o04: that exported reader is evaluated once for both calls.
        const string traced = "F(y) = {\n  A = { public Q = 5\n    y }.Q + trace(1)\n  A\n}\nF(1), F(2)\n";
        var calls = 0;
        var trace = HostOperation.Create("trace", (arguments, _) => { Interlocked.Increment(ref calls); return arguments[0]; }, "x");
        foreach (var result in await Routes(traced, trace))
            Assert.Equal("S[6, 6]", SemanticExplorerHarness.Neutral(Assert.IsType<RunResult.Success>(result).Value));
        Assert.Equal(3, calls); // once per route
    }

    // ── A block written in a deconstruction right-hand side ───────────────────────────────────────

    [Fact]
    public async Task BlockHeadedDeconstructionSource_IsAccepted()
    {
        var f = F(BlockHeadedSource + "F(1)\n");
        var block = SourceBlock(f, out var source);
        // The source reads the selected member, like the named control; its targets read the source.
        AssertLocalOnly(source, ("y", 0));
        AssertLocalOnly(Member(f, "a"), ("y", 0));
        AssertLocalOnly(Member(f, "b"), ("y", 0));
        // The member's owner is two runtime levels up: the block is wired under the source, the source under F.
        AssertLocalOnly(Member(block, "Q"), ("y", 2));

        await AssertValue(BlockHeadedSource + "F(1)\n", "S[1, 2]");
        await AssertValue(BlockHeadedSource + "F(1), F(2)\n", "S[S[1, 2], S[2, 3]]");
        await AssertRefused(BlockHeadedSource + "F.a\n", "a");
    }

    [Fact]
    public async Task NamedDeconstructionSource_IsUnchanged()
    {
        var f = F(NamedSource + "F(1)\n");
        AssertLocalOnly(Assert.Single(f.Properties, property => property.Value is Algorithm.User { IsAssignmentDeconstructionSource: true }), ("y", 0));
        // A named container is a property of F: its member stands one level below F.
        AssertLocalOnly(Member(Assert.IsType<Algorithm.User>(Member(f, "Box").Value), "Q"), ("y", 1));

        await AssertValue(NamedSource + "F(1)\n", "S[1, 2]");
        await AssertValue(NamedSource + "F(1), F(2)\n", "S[S[1, 2], S[2, 3]]");
    }

    // name, the body declaring F, the value of F(1), the value of F(2)
    public static TheoryData<string, string, string, string> BlocksInADeconstructionSource => new()
    {
        { "member of a nested member", "F(y) = {\n  a, b = { public S = { public Q = (y, y + 1) } }.S.Q\n  a, b\n}\n", "S[1, 2]", "S[2, 3]" },
        { "member reading a sibling of F", "F(y) = {\n  K = y\n  a, b = { public Q = (K, K + 1) }.Q\n  a, b\n}\n", "S[1, 2]", "S[2, 3]" },
        { "callee member", "F(y) = {\n  a, b = { public G(z) = (z + y, z) }.G(1)\n  a, b\n}\n", "S[2, 1]", "S[3, 1]" },
        { "block in a call argument", "Pair(v) = (v, v + 1)\nF(y) = {\n  a, b = Pair({ public Q = y }.Q)\n  a, b\n}\n", "S[1, 2]", "S[2, 3]" },
        { "runtime reference member, then a fallback", "Pair(v) = (v, v + 1)\nF(y) = {\n  a, b = { public L = y }.L.Pair\n  a, b\n}\n", "S[1, 2]", "S[2, 3]" },
        { "fallback edges after the member", "F(y) = {\n  T(v) = (v, v + y)\n  U(v) = v\n  a, b = { public S = 5 }.S.T.U\n  a, b\n}\n", "S[5, 6]", "S[5, 7]" },
        { "block read by its own output (lexical, control)", "F(y) = {\n  a, b = { Q = (y, y + 1)\n    Q }\n  a, b\n}\n", "S[1, 2]", "S[2, 3]" },
        { "constant member (control)", "F(y) = {\n  a, b = { public Q = (1, 2) }.Q\n  a, b\n}\n", "S[1, 2]", "S[1, 2]" },
        { "deconstruction inside a nested block", "F(y) = {\n  N = {\n    a, b = { public Q = (y, y + 1) }.Q\n    a + b\n  }\n  N, N\n}\n", "S[3, 3]", "S[5, 5]" },
        { "deconstruction in a clause branch body", "F(0) = (0, 0)\nF(y) = {\n  a, b = { public Q = (y, y + 1) }.Q\n  (a, b)\n}\n", "S[1, 2]", "S[2, 3]" },
    };

    [Theory]
    [MemberData(nameof(BlocksInADeconstructionSource))]
    public async Task BlockInADeconstructionSource_ReadsItsOwnersActivation(string name, string body, string one, string two)
    {
        _ = name;
        await AssertValue(body + "F(1)\n", one);
        await AssertValue(body + "F(1), F(2)\n", $"S[{one}, {two}]");
        await AssertValue(body + "F(2), F(1)\n", $"S[{two}, {one}]");
    }

    [Fact]
    public void CapturePositionsBelowADeconstructionSource_CountTheSourceLevel()
    {
        // Each level below the block keeps its own distance; only the step out of the source adds one.
        var nested = SourceBlock(F("F(y) = {\n  a, b = { public S = { public Q = (y, y + 1) } }.S.Q\n  a, b\n}\nF(1)\n"), out _);
        AssertExported(Member(nested, "S"));
        AssertLocalOnly(Member(Assert.IsType<Algorithm.User>(Member(nested, "S").Value), "Q"), ("y", 3));

        // The same block as an ordinary property's row stands under that property instead: the same two levels.
        var f = F("F(y) = {\n  A = { public Q = (y, y + 1) }.Q\n  A\n}\nF(1)\n");
        var row = Assert.Single(Member(f, "A").Value.Output);
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.IsType<Expr.DotCall>(row).Target).Algorithm;
        AssertLocalOnly(Member(block, "Q"), ("y", 2));
    }

    [Fact]
    public void Editor_ReadsACapturedRuntimeReferenceBelowADeconstructionSource()
    {
        // `{ public L = y }.L` is a captured runtime reference; the editor's static prerequisite walks the same
        // capture position over completed keys, which hold no level for the source.
        const string source = """
            Pair(v) = (v, v + 1)
            F(y) = {
              a, b = { public L = y }.L.Pair
              a, b
            }
            F(1)
            """;
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        var member = Assert.Single(model.IdentifierResolutions,
            resolution => resolution.Occurrence is { Kind: OccurrenceKind.DotMemberReference, Name: "Pair" });
        Assert.Equal(IdentifierClassification.PropertyReference, member.Classification);
        Assert.Same(Assert.Single(model.FindDeclarations("Pair")), member.ResolvedDeclaration);
    }

    [Fact]
    public void Editor_CaptureOwnerIndex_IsSharedByReadersOfWideDeconstructionRows()
    {
        var work = new List<long>();
        foreach (var width in new[] { 40, 80, 160 })
        {
            var source = new System.Text.StringBuilder("Pair(v) = (v, v + 1)\nF(y) = {\n");
            for (var i = 0; i < width; i++)
                source.Append($"  a{i}, b{i} = {{ public L = y }}.L.Pair\n");
            source.Append("  a0, b0\n}\nF(1)\n");
            var parsed = SourceProvenance.ParseValid(source.ToString()).Parsed;
            var observations = new FrontEndTraversalObservations();
            var model = SemanticModelBuilder.Build(parsed, observations);
            var readers = model.IdentifierResolutions.Where(resolution =>
                resolution.Occurrence is { Kind: OccurrenceKind.DotMemberReference, Name: "Pair" }).ToArray();
            Assert.Equal(width, readers.Length);
            Assert.All(readers, reader => Assert.Equal(IdentifierClassification.PropertyReference, reader.Classification));
            work.Add(observations.SemanticDeconstructionSourceIndexNodes);
        }

        output.WriteLine($"deconstruction owner-index inspections: {string.Join(" / ", work)}");
        Assert.True(work[0] > 0);
        for (var i = 1; i < work.Count; i++)
            Assert.True(work[i] <= 2.5 * work[i - 1], $"owner-index work {work[i - 1]} -> {work[i]}");
    }

    [Fact]
    public void BlockHeadedSource_MissingPublishedFacts_IsAnInvariantFailure()
    {
        var root = SourceProvenance.ParseValid(BlockHeadedSource + "F(1)\n").Root;
        var f = Assert.IsType<Algorithm.User>(Member(root, "F").Value);
        var block = SourceBlock(f, out _);
        var publication = root.CompletedStructure!;
        var facts = publication.Facts;
        var fKey = facts.Child(publication.Entry!, f)!;
        var blockKey = facts.Child(fKey, block)!;
        Assert.NotNull(facts.Facts(blockKey)?.Body);
        var missing = new MissingBlockFacts(facts, blockKey);
        // Exercise the parent's contextual facts rather than the block's standalone publication.
        block.CompletedStructure = null;

        var error = Assert.Throws<InvalidOperationException>(() =>
            PropertyDependencyGraphBuilder.BuildSummaries(f, completedContext: missing.Context(fKey)));
        Assert.Equal("A completed block-head requirement body is unavailable.", error.Message);
    }

    private sealed class MissingBlockFacts(StaticLookupFacts source, StaticScopeKey missing) : StaticLookupFacts
    {
        internal override StaticScopeKey PreludeKey => source.PreludeKey;
        internal override IEnumerable<StaticScopeKey> Scopes => source.Scopes;
        internal override CompletedStaticStructures.BodyFacts? Facts(StaticScopeKey key)
            => ReferenceEquals(key, missing) ? null : source.Facts(key);
        internal override StaticScopeKey? Child(StaticScopeKey parent, Algorithm body, Pattern? pattern = null)
            => source.Child(parent, body, pattern);
        internal override void EnsureUsable() => source.EnsureUsable();
    }
}
