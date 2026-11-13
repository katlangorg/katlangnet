namespace KatLang.Tests;

/// <summary>
/// Source fidelity and C# outcomes of the E-18 B2 preparation witnesses. Since the anchoring of
/// a container's chain (owner decision 2026-11-13) a member of a container fetched outside its
/// owner's call reads the call its reader is inside: the shadowed read is the owner's 1 (formerly
/// the reader's 99) and the call-reference read is the captured call's 5 (formerly UnknownName).
/// The reached-state Lean theorems use a root-only context; the outcome guards and these
/// tests use public entry points with the prelude. Neither proves whole-run admissibility.
/// The <c>FrontEnd</c> rows are source trees of the static exposure model: a member whose only
/// dependency is selected by a static dotted path, through a transparent reference, or by an
/// <c>open</c>. The <c>SelectionGaps</c> rows are the source-valid routes the former bounded
/// selector omitted (a repeated provider, an open-provided dotted head, a 65-link reference chain),
/// the <c>SelectionRoutes</c> rows are a source control for every route the selection model covers,
/// and the <c>AccessChecks</c> rows are one source program per access-check class the exposure pass
/// formerly under-charged (a reference's target walk, a chain, an inline-block head, an open through
/// a reference, an enclosing level's open) plus the controls it must keep exported (ledger E-18, F1);
/// Lean refuses each one's host-corrupted or pre-fix counterpart.
/// </summary>
public class NavigationSourceDomainWitnessTests
{
    private const string Container = "F(y) = {\n  p = {\n    Q = y\n    1\n  }\n";
    private const string MetaPrelude = "Capture(meta op) = op\nUse(f) = 1\n";
    private const string LeanPath = "lean/KatLangArityLaws/NavigationSourceDomainGuards.lean";

    /// <summary><c>F(y)</c> with <c>Lib.Q = y</c>, 65 transparent references <c>L0 = Lib</c> … <c>L64 = L63</c>, and <c>A = L64.Q + 0</c>.</summary>
    private static readonly string LongChain = "F(y) = {\n  Lib = {\n    public Q = y\n    1\n  }\n" +
        string.Join("\n", Enumerable.Range(0, 65).Select(i => $"  L{i} = {(i == 0 ? "Lib" : $"L{i - 1}")}")) +
        "\n  A = L64.Q + 0\n  A\n}\nF(5)\n";

    private const string ModuleUrl = "https://mods.test/m.kat";
    private const string ModuleSource =
        "G(k) = {\n  Lib = {\n    public Q = k\n    1\n  }\n  A = {\n    open Lib\n    Q + 0\n  }\n  A\n}\npublic V = G(5)\n";
    private const string ModuleHolder = "F(y) = {\n  Q = y\n  M = load('" + ModuleUrl + "')\n  M.V + 0\n}\nF(7)\n";

    public static TheoryData<string, string, string> Witnesses => new()
    {
        { "OutsideContainer", "program", MetaPrelude + Container + "  Capture(Use(y.Q))\n}\nF(F.p)\n" },
        { "EscapedContainer", "program", MetaPrelude + Container +
            "  Inner(z) = Capture(Use(z.Q))\n  K(meta r) = r\n  K(Inner(0))\n}\nR = F(5)\nR.Algorithm(F.p)\n" },
        { "", "outsideValue", Container + "  y.Q\n}\nF(F.p)\n" },
        { "", "shadowedRead", Container + "  G(g, y) = g.Q\n  G(y, 99)\n}\nF(F.p)\n" },
        { "", "insideRead", Container + "  G(g, y) = g.Q\n  G(p, 99)\n}\nF(5)\n" },
        { "", "escapedValue", Container +
            "  Inner(z) = z.Q\n  K(meta r) = r\n  K(Inner(0))\n}\nR = F(5)\nR.Algorithm(F.p)\n" },
        { "", "rootRead", Container + "  y\n}\nF.p.Q\n" },
        { "FrontEnd", "dotted", "F(y) = {\n  Lib = {\n    public Q = y\n    1\n  }\n  A = Lib.Q + 0\n  A\n}\nF(5)\n" },
        { "FrontEnd", "nested", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = y\n      1\n    }\n    1\n  }\n" +
            "  A = Lib.Sub.Q + 0\n  A\n}\nF(5)\n" },
        { "FrontEnd", "reference", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = y\n      1\n    }\n    1\n  }\n" +
            "  L = Lib.Sub\n  A = L.Q + 0\n  A\n}\nF(5)\n" },
        { "FrontEnd", "opened", "F(y) = {\n  Lib = {\n    public Q = y\n    1\n  }\n  A = {\n    open Lib\n    Q + 0\n  }\n  A\n}\nF(5)\n" },
        { "SelectionGaps", "duplicateOpened", "F(y) = {\n  Lib = {\n    public Q = y\n    1\n  }\n" +
            "  A = {\n    open Lib, Lib\n    Q + 0\n  }\n  A\n}\nF(5)\n" },
        { "SelectionGaps", "openedReceiver", "F(y) = {\n  Lib = {\n    public Box = {\n      public Q = y\n      1\n    }\n    1\n  }\n" +
            "  A = {\n    open Lib\n    Box.Q + 0\n  }\n  A\n}\nF(5)\n" },
        { "SelectionGaps", "longChainSource", LongChain },
        { "SelectionRoutes", "openedAliasTarget", "F(y) = {\n  Lib = {\n    public Box = {\n      public Q = y\n      1\n    }\n    1\n  }\n" +
            "  A = {\n    open Lib\n    L = Box\n    L.Q + 0\n  }\n  A\n}\nF(5)\n" },
        { "SelectionRoutes", "sameProvider", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = y\n      1\n    }\n    1\n  }\n" +
            "  Sub = Lib.Sub\n  A = {\n    open Sub, Lib.Sub\n    Q + 0\n  }\n  A\n}\nF(5)\n" },
        { "SelectionRoutes", "openedNestedHead", "F(y) = {\n  Lib = {\n    public Box = {\n      public Sub = {\n        public Q = y\n        1\n      }\n      1\n    }\n    1\n  }\n" +
            "  A = {\n    open Lib\n    Box.Sub.Q + 0\n  }\n  A\n}\nF(5)\n" },
        { "SelectionRoutes", "outerOpenAliasTarget", "F(y) = {\n  open Lib\n  Lib = {\n    public Box = {\n      public Q = y\n      1\n    }\n    1\n  }\n" +
            "  L = Box\n  A = L.Q + 0\n  A\n}\nF(5)\n" },
        { "SelectionRoutes", "ambiguousFallback", "F(y) = {\n  Lib1 = {\n    public Q = y\n    1\n  }\n  Lib2 = {\n    public Q = y\n    2\n  }\n" +
            "  Box = {\n    public Q = 5\n    0\n  }\n  G(obj) = {\n    open Lib1, Lib2\n    obj.Q\n  }\n  G(Box)\n}\nF(5)\n" },
        { "SelectionRoutes", "selectedMemberOnly", "F(y) = {\n  Lib = {\n    public Q = 1\n    y\n  }\n  A = Lib.Q + 0\n  A\n}\nF(5)\n" },
        { "SelectionRoutes", "preludeBeforeOpens", "F(y) = {\n  Lib = {\n    public count(xs) = y\n    1\n  }\n" +
            "  A = {\n    open Lib\n    count((1, 2)) + 0\n  }\n  A\n}\nF(5)\n" },
        { "AccessChecks", "referenceWalk", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  A = L.Q + 0\n  A\n}\nF(5)\n" },
        { "AccessChecks", "referenceChain", "F(y) = {\n  Lib = {\n    public Sub = {\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  L0 = Lib.Sub\n  M = L0.T\n  A = M.Q + 0\n  A\n}\nF(5)\n" },
        { "AccessChecks", "blockHead", "F(y) = {\n  A = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n  }.Sub.Q + 0\n  A\n}\nF(5)\n" },
        { "AccessChecks", "openThroughReference", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  A = {\n    open L\n    Q + 0\n  }\n  A\n}\nF(5)\n" },
        { "AccessChecks", "enclosingOpen", "F(y) = {\n  open Lib.Sub\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  A = Q + 0\n  A\n}\nF(5)\n" },
        { "AccessChecks", "enclosingUnusedOpen", "F(y) = {\n  open Lib.Sub, Other\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  Other = {\n    public X = 2\n  }\n  A = X + 0\n  A\n}\nF(5)\n" },
        { "AccessChecks", "intermediateSource", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  A = Lib.Sub.Q + 0\n  A\n}\nF(5)\n" },
        { "AccessChecks", "valueOnlyReference", "F(y) = {\n  Lib = {\n    public Q = 1\n    y\n  }\n  L = Lib\n  A = L.Q + 0\n  A\n}\nF(5)\n" },
        { "AccessChecks", "namedMemberOnly", "F(y) = {\n  B = {\n    public Q = 1\n    y + 0\n  }\n  A = B.Q + 0\n  A\n}\nF(5)\n" },
        { "AccessChecks", "blockHeadRelaxed", "F(y) = {\n  A = {\n    public Q = 1\n    y + 0\n  }.Q + 0\n  A\n}\nF(5)\n" },
        { "AccessChecks", "runtimeReferenceOpen", "F(y) = {\n  open L, Other\n  L = y\n  Other = { public Q = 1 }\n  A = Q + 0\n  A\n}\nF(5)\n" },
    };

    [Theory]
    [MemberData(nameof(Witnesses))]
    public void LeanWitness_IsTheActualElaboratedSource(string scope, string name, string source)
    {
        var encoded = LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(source).Root);
        var lean = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanPath)).ReplaceLineEndings("\n");
        if (scope.Length > 0)
        {
            var start = lean.IndexOf($"namespace {scope}\n", StringComparison.Ordinal);
            Assert.True(start >= 0, $"Missing Lean namespace {scope}");
            var end = lean.IndexOf($"end {scope}\n", start, StringComparison.Ordinal);
            Assert.True(end > start, $"Missing Lean namespace end {scope}");
            lean = lean[start..end];
        }

        Assert.Contains($"def {name} : Expr :=\n  {encoded}\n", lean, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("outsideValue", 1)]
    [InlineData("shadowedRead", 1)]
    [InlineData("insideRead", 5)]
    [InlineData("escapedValue", 5)]
    [InlineData("dotted", 5)]
    [InlineData("nested", 5)]
    [InlineData("reference", 5)]
    [InlineData("opened", 5)]
    [InlineData("duplicateOpened", 5)]
    [InlineData("openedReceiver", 5)]
    [InlineData("longChainSource", 5)]
    [InlineData("openedAliasTarget", 5)]
    [InlineData("sameProvider", 5)]
    [InlineData("openedNestedHead", 5)]
    [InlineData("outerOpenAliasTarget", 5)]
    [InlineData("ambiguousFallback", 5)]
    [InlineData("selectedMemberOnly", 1)]
    [InlineData("preludeBeforeOpens", 2)]
    [InlineData("referenceWalk", 1)]
    [InlineData("referenceChain", 1)]
    [InlineData("blockHead", 1)]
    [InlineData("openThroughReference", 1)]
    [InlineData("enclosingOpen", 1)]
    [InlineData("enclosingUnusedOpen", 2)]
    [InlineData("intermediateSource", 1)]
    [InlineData("valueOnlyReference", 1)]
    [InlineData("namedMemberOnly", 1)]
    [InlineData("blockHeadRelaxed", 1)]
    [InlineData("runtimeReferenceOpen", 1)]
    public void SourceWitness_HasTheLeanGuardValue(string name, int expected)
    {
        var source = Witnesses.Single(row => (string)row[1] == name)[2] as string;
        Assert.NotNull(source);
        SourceProvenance.ParseValid(source);
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(new Result.Atom(expected), success.Value);
    }

    [Theory]
    [InlineData("rootRead", KatLangErrorCode.LocalOnlyProperty)]
    public void SourceWitness_HasTheLeanGuardError(string name, KatLangErrorCode expected)
    {
        var source = Witnesses.Single(row => (string)row[1] == name)[2] as string;
        Assert.NotNull(source);
        SourceProvenance.ParseValid(source);
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        Assert.Equal(expected, Assert.Single(failure.Errors).Code);
    }

    [Theory]
    [InlineData("dotted")]
    [InlineData("nested")]
    [InlineData("reference")]
    [InlineData("opened")]
    [InlineData("duplicateOpened")]
    [InlineData("openedReceiver")]
    [InlineData("longChainSource")]
    [InlineData("openedAliasTarget")]
    [InlineData("sameProvider")]
    [InlineData("openedNestedHead")]
    [InlineData("outerOpenAliasTarget")]
    [InlineData("referenceWalk")]
    [InlineData("referenceChain")]
    [InlineData("blockHead")]
    [InlineData("openThroughReference")]
    [InlineData("enclosingOpen")]
    [InlineData("enclosingUnusedOpen")]
    [InlineData("intermediateSource")]
    public void SelectedDependencyWitness_MarksTheReaderLocalOnly(string name)
    {
        var source = Witnesses.Single(row => (string)row[1] == name)[2] as string;
        Assert.NotNull(source);
        var root = SourceProvenance.ParseValid(source).Root;
        var f = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties).Value);
        var a = f.Properties.Single(property => property.Name == "A");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, a.Exposure);
        Assert.Equal(["y"], a.RequiredAncestorParameters);
    }

    /// <summary>
    /// The readers the selection model requires NOTHING of: two distinct open providers
    /// at one level select nothing (a possible fallback), a selected member is read without its
    /// receiver's value, the prelude's builtin precedes every open, a member-less reference's VALUE
    /// is not read, and neither is a name or block head's VALUE when a member is selected. The front
    /// end keeps each reader exported; Lean admits it and refuses the same tree without that rule's condition.
    /// </summary>
    [Theory]
    [InlineData("ambiguousFallback", "G")]
    [InlineData("selectedMemberOnly", "A")]
    [InlineData("preludeBeforeOpens", "A")]
    [InlineData("valueOnlyReference", "A")]
    [InlineData("namedMemberOnly", "A")]
    [InlineData("blockHeadRelaxed", "A")]
    [InlineData("runtimeReferenceOpen", "A")]
    public void SelectionRouteWitness_KeepsTheReaderExported(string name, string reader)
    {
        var source = Witnesses.Single(row => (string)row[1] == name)[2] as string;
        Assert.NotNull(source);
        var root = SourceProvenance.ParseValid(source).Root;
        var f = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties).Value);
        var property = f.Properties.Single(candidate => candidate.Name == reader);
        Assert.Equal(PropertyExposure.Exported, property.Exposure);
        Assert.Empty(property.RequiredAncestorParameters);
    }

    /// <summary>
    /// A loaded module is rooted at the prelude: inside it, <c>Q</c> is the opened <c>Lib.Q</c>,
    /// never the holder's <c>Q</c>, so the module's <c>A</c> requires its own <c>k</c>. The tree is
    /// Lean's <c>SelectionRoutes.moduleCut</c>, and C# runs it to Lean's guard value.
    /// </summary>
    [Fact]
    public async Task ModuleCutWitness_IsTheActualElaboratedSource()
    {
        var server = new ModuleRouteAgreement.Modules((ModuleUrl, ModuleSource));
        var root = (await SourceProvenance.ParseValidAsync(ModuleHolder, server.Options())).Root;
        var lean = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanPath)).ReplaceLineEndings("\n");
        var start = lean.IndexOf("namespace SelectionRoutes\n", StringComparison.Ordinal);
        Assert.True(start >= 0, "Missing Lean namespace SelectionRoutes");
        var end = lean.IndexOf("end SelectionRoutes\n", start, StringComparison.Ordinal);
        Assert.True(end > start, "Missing Lean namespace end SelectionRoutes");
        Assert.Contains($"def moduleCut : Expr :=\n  {LeanAstEncoder.EncodeProgram(root)}\n", lean[start..end], StringComparison.Ordinal);

        var f = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties).Value);
        var module = Assert.IsType<Algorithm.User>(f.Properties.Single(property => property.Name == "M").Value);
        var g = Assert.IsType<Algorithm.User>(module.Properties.Single(property => property.Name == "G").Value);
        var a = g.Properties.Single(property => property.Name == "A");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, a.Exposure);
        Assert.Equal(["k"], a.RequiredAncestorParameters);

        var success = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(ModuleHolder, server.Options()));
        Assert.Equal(new Result.Atom(5), success.Value);
    }

    [Fact]
    public void LongTransparentReceiverChain_StillRequiresTheAncestorParameter()
    {
        // All 65 references reach Lib, and A requires F's y through the selected Q. The former Lean
        // selector's fixed 64-unit search lost this dependency; the selection model's fuel is
        // derived from the program (`selFuel`), and Lean refuses the exported counterpart
        // (`SelectionGaps.long_chain_exported_refused`).
        var source = LongChain;
        var root = SourceProvenance.ParseValid(source).Root;
        var f = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties).Value);
        var a = f.Properties.Single(property => property.Name == "A");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, a.Exposure);
        Assert.Equal(["y"], a.RequiredAncestorParameters);
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(new Result.Atom(5), success.Value);
    }

    [Fact]
    public void DottedMemberDependency_RequiresMoreThanTheLeanLexicalExposureFragment()
    {
        const string source = "F(y) = {\n  Lib = {\n    public Q = y\n    1\n  }\n  A = Lib.Q + 0\n  y\n}\n0\n";
        var root = SourceProvenance.ParseValid(source).Root;
        var f = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties).Value);
        var a = f.Properties.Single(property => property.Name == "A");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, a.Exposure);
        Assert.Equal(["y"], a.RequiredAncestorParameters);
        var encoded = LeanAstEncoder.EncodeProgram(root);
        Assert.Contains("privateLocalProp \"A\" (.localCapturedAncestorParams [\"y\"])", encoded);
    }
}
