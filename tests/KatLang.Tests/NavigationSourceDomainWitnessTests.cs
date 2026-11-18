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
/// Lean refuses each one's host-corrupted or pre-fix counterpart. The <c>ModuleProviders</c> rows are
/// the routes on which one loaded module is one open provider, their two-provider controls, and a
/// reader charged only through the open level such a module decides.
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
        { "CheckSites", "openCrossingInside", "F(y) = {\n  L = Lib.Mid.Sub\n  Lib = {\n    public Mid(p) = {\n      public Sub = {\n        public Q = 1\n        p\n      }\n      B(z) = {\n        open L\n        Q + 0\n      }\n      B(0)\n    }\n    0\n  }\n  Lib.Mid(y)\n}\nF(5)\n" },
        { "CheckSites", "valueCrossingOutside", "F(y) = {\n  L = Lib.Mid.Sub\n  Lib = {\n    public Mid(p) = {\n      public Sub = {\n        public Q = 1\n        p\n      }\n      0\n    }\n    0\n  }\n  Box = {\n    public A = if(false, L.Q + 0, 7)\n  }\n  Box.A\n}\nF(5)\n" },
        { "CheckSites", "consultedOutside", "F(y) = {\n  open Lib.Mid.Sub\n  Lib = {\n    public Mid(p) = {\n      public Sub = {\n        public Q = 1\n        p\n      }\n      A(z) = Q + 0\n      A(0)\n    }\n    0\n  }\n  Lib.Mid(y)\n}\nF(5)\n" },
        { "CheckSites", "untakenImpossible", "F(y) = {\n  A = y + 1\n  A\n}\nBox = {\n  public R = if(false, F.A, 0)\n}\nBox.R\n" },
        { "CheckSites", "staticPrefixRuntimeOpen", "F(y) = {\n  open L, Other\n  L = Lib.Sub.Algorithm\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  Other = { public Z = 2 }\n  A = Z + 0\n  A\n}\nF(5)\n" },
        { "CheckSites", "blockHeadedOpen", "F(y) = {\n  open L\n  L = {\n    public Sub = {\n      public Q = y\n      0\n    }\n  }.Sub\n  A = Q + 0\n  A\n}\nF(5)\n" },
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
    [InlineData("openCrossingInside", 1)]
    [InlineData("valueCrossingOutside", 7)]
    [InlineData("untakenImpossible", 0)]
    [InlineData("staticPrefixRuntimeOpen", 2)]
    [InlineData("blockHeadedOpen", 5)]
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
    [InlineData("consultedOutside", KatLangErrorCode.LocalOnlyProperty)]
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

    // ── One loaded module is one open provider (E-18 model correction, 2026-11-18; Lean `ModuleProviders`) ──

    private const string XUrl = "https://mods.test/x.kat";
    private const string YUrl = "https://mods.test/y.kat";
    private const string SubUrl = "https://mods.test/sub.kat";
    private const string Sub2Url = "https://mods.test/sub2.kat";
    private const string TwoUrl = "https://mods.test/two.kat";
    private const string XModule = "public X = 5\n";
    private const string SubModule = "public Sub = {\n  public X = 5\n}\n";
    private const string TwoModule = "public S1 = {\n  public X = 5\n}\npublic S2 = {\n  public X = 5\n}\n";

    /// <summary><c>R</c> reads <c>X</c> through <c>F</c>'s opens: the walk of <c>Lib.Sub</c> needs <c>y</c>, and two holders of one module provide <c>X</c>.</summary>
    private const string CaptureBody = "A = load('" + XUrl + "')\nB = load('" + XUrl + "')\n" +
        "F(y) = {\n  open Lib.Sub, A, B\n  Lib = {\n    public Sub = { y + 0 }\n    0\n  }\n  R = X + 0\n  R\n}\n";

    /// <summary>Two canonical URLs serve each text, so equal bytes under two module identities are available.</summary>
    private static ModuleRouteAgreement.Modules ProviderModules() => new(
        (XUrl, XModule), (YUrl, XModule), (SubUrl, SubModule), (Sub2Url, SubModule), (TwoUrl, TwoModule));

    private static string ModuleProvidersLean()
    {
        var lean = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanPath)).ReplaceLineEndings("\n");
        var start = lean.IndexOf("namespace ModuleProviders\n", StringComparison.Ordinal);
        Assert.True(start >= 0, "Missing Lean namespace ModuleProviders");
        var end = lean.IndexOf("end ModuleProviders\n", start, StringComparison.Ordinal);
        Assert.True(end > start, "Missing Lean namespace end ModuleProviders");
        return lean[start..end];
    }

    /// <summary>The asynchronous front end over the synchronous evaluator, and over the asynchronous twin.</summary>
    private static async Task<RunResult[]> ModuleEngines(string source)
    {
        var twin = HostOperations.Create(HostOperation.CreateAsync("UnusedModuleProviderRoute",
            static (_, _) => throw new InvalidOperationException("The route marker must never execute.")));
        Assert.True(twin.ContainsAsynchronousOperations);
        return [await KatLangEngine.RunAsync(source, ProviderModules().Options()),
            await KatLangEngine.RunAsync(source, ProviderModules().Options(twin))];
    }

    public static TheoryData<string, string> OneModuleProviderWitnesses => new()
    {
        { "twoHolders", "open A, B\nA = load('" + XUrl + "')\nB = load('" + XUrl + "')\nX\n" },
        { "holderAndWrittenLoad", "open A, load('" + XUrl + "')\nA = load('" + XUrl + "')\nX\n" },
        { "memberHolder", "open Box.M, A\nBox = {\n  public M = load('" + XUrl + "')\n}\nA = load('" + XUrl + "')\nX\n" },
        { "descendant", "open A.Sub, B.Sub\nA = load('" + SubUrl + "')\nB = load('" + SubUrl + "')\nX\n" },
        { "descendantReference", "open A.Sub, L\nA = load('" + SubUrl + "')\nB = load('" + SubUrl + "')\nL = B.Sub\nX\n" },
        { "writtenLoadDescendant", "open load('" + SubUrl + "').Sub, A.Sub\nA = load('" + SubUrl + "')\nX\n" },
        { "captureWitness", CaptureBody + "F(7)\n" },
    };

    /// <summary>
    /// Every reach of one loaded module is one open provider (Q-32 I-U): the opened name is read, in
    /// both engines, and the tree is Lean's <c>ModuleProviders</c> definition of that name, where
    /// production Lean and the static selection model select the same member.
    /// </summary>
    [Theory]
    [MemberData(nameof(OneModuleProviderWitnesses))]
    public async Task ModuleProviderWitness_OneModuleIsOneProvider(string name, string source)
    {
        var root = (await SourceProvenance.ParseValidAsync(source, ProviderModules().Options())).Root;
        Assert.Contains($"def {name} : Expr :=\n  {LeanAstEncoder.EncodeProgram(root)}\n", ModuleProvidersLean(), StringComparison.Ordinal);
        foreach (var result in await ModuleEngines(source))
            Assert.Equal(new Result.Atom(5), Assert.IsType<RunResult.Success>(result).Value);
    }

    public static TheoryData<string, string> TwoProviderWitnesses => new()
    {
        { "twoModules", "open A, B\nA = load('" + XUrl + "')\nB = load('" + YUrl + "')\n" },
        { "twoModuleDescendants", "open A.Sub, B.Sub\nA = load('" + SubUrl + "')\nB = load('" + Sub2Url + "')\n" },
        { "distinctDescendants", "open A.S1, B.S2\nA = load('" + TwoUrl + "')\nB = load('" + TwoUrl + "')\n" },
        { "writtenBlocks", "open { public X = 5 }, { public X = 5 }\n" },
    };

    /// <summary>
    /// Two module identities with equal bytes, two declarations of one module and two written blocks
    /// stay two providers. Reading the name they both provide is the front-end error
    /// <c>AmbiguousOpen</c>, so the Lean tree is the tree of the same source with the output row
    /// <c>1</c>, that row replaced by the read.
    /// </summary>
    [Theory]
    [MemberData(nameof(TwoProviderWitnesses))]
    public async Task ModuleProviderWitness_TwoProvidersStayTwo(string name, string body)
    {
        var read = await Parser.ParseAsync(body + "X\n", ProviderModules().Options());
        var error = Assert.Single(read.Diagnostics, diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.AmbiguousOpen, error.Code);

        const string unusedRow = "[.num 1])";
        var encoded = LeanAstEncoder.EncodeProgram((await SourceProvenance.ParseValidAsync(body + "1\n", ProviderModules().Options())).Root);
        Assert.EndsWith(unusedRow, encoded, StringComparison.Ordinal);
        Assert.Contains($"def {name} : Expr :=\n  {encoded[..^unusedRow.Length]}[.resolve \"X\"])\n", ModuleProvidersLean(), StringComparison.Ordinal);
    }

    /// <summary>
    /// The capture witness: the front end charges <c>R</c> the walk of the unused target <c>Lib.Sub</c>
    /// of the open level that the one module decides, at <c>F</c>'s <c>y</c>, and both engines refuse
    /// <c>R</c> outside the call. Lean's host-built copy is this tree with exactly that requirement
    /// removed; the static model refuses it (<c>ModuleProviders.captureWitness_hostBuilt_refused</c>).
    /// </summary>
    [Fact]
    public async Task ModuleProviderCaptureWitness_ChargesTheReaderTheUnusedTargetWalk()
    {
        var root = (await SourceProvenance.ParseValidAsync(CaptureBody + "F(7)\n", ProviderModules().Options())).Root;
        var f = Assert.IsType<Algorithm.User>(root.Properties.Single(property => property.Name == "F").Value);
        ExposureOpenChainComplexityTests.AssertRequires(f.Properties.Single(property => property.Name == "R"), ("y", 0));

        const string localOnlyReader = "{ (privateLocalProp \"R\" (.localCapturedAncestorParams [\"y\"]) (alg [] [] [] [(.binary .add (.resolve \"X\") (.num 0))])) with requiredOwnerDepths := some [(\"y\", some 0)] }";
        const string exportedReader = "privateProp \"R\" (alg [] [] [] [(.binary .add (.resolve \"X\") (.num 0))])";
        var lean = ModuleProvidersLean();
        var encoded = LeanAstEncoder.EncodeProgram(root);
        Assert.Contains(localOnlyReader, encoded, StringComparison.Ordinal);
        Assert.Contains($"def captureWitnessHostBuilt : Expr :=\n  {encoded.Replace(localOnlyReader, exportedReader, StringComparison.Ordinal)}\n", lean, StringComparison.Ordinal);

        var escaped = LeanAstEncoder.EncodeProgram((await SourceProvenance.ParseValidAsync(CaptureBody + "F(7), F.R\n", ProviderModules().Options())).Root);
        Assert.Contains($"def captureWitnessEscaped : Expr :=\n  {escaped}\n", lean, StringComparison.Ordinal);
        Assert.Contains($"def captureWitnessHostBuiltEscaped : Expr :=\n  {escaped.Replace(localOnlyReader, exportedReader, StringComparison.Ordinal)}\n", lean, StringComparison.Ordinal);

        foreach (var tail in new[] { "F.R\n", "F(7), F.R\n" })
            foreach (var result in await ModuleEngines(CaptureBody + tail))
            {
                var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
                Assert.Equal(KatLangErrorCode.LocalOnlyProperty, error.Code);
                Assert.Contains("Property 'R' on `F` is local-only", error.Message, StringComparison.Ordinal);
            }
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
