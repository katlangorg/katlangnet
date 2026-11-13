namespace KatLang.Tests;

/// <summary>
/// Source fidelity and C# outcomes of the E-18 B2 preparation witnesses. Since the anchoring of
/// a container's chain (owner decision 2026-11-13) a member of a container fetched outside its
/// owner's call reads the call its reader is inside: the shadowed read is the owner's 1 (formerly
/// the reader's 99) and the call-reference read is the captured call's 5 (formerly UnknownName).
/// The reached-state Lean theorems use a root-only context; the outcome guards and these
/// tests use public entry points with the prelude. Neither proves whole-run admissibility.
/// The <c>FrontEnd</c> rows are source trees of the candidate static exposure model: a member
/// whose only dependency is selected by a static dotted path, through a transparent reference,
/// or by an <c>open</c>. The <c>SelectionGaps</c> rows pin source-valid routes the model omits.
/// </summary>
public class NavigationSourceDomainWitnessTests
{
    private const string Container = "F(y) = {\n  p = {\n    Q = y\n    1\n  }\n";
    private const string MetaPrelude = "Capture(meta op) = op\nUse(f) = 1\n";
    private const string LeanPath = "lean/KatLangArityLaws/NavigationSourceDomainGuards.lean";

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

    [Fact]
    public void LongTransparentReceiverChain_StillRequiresTheAncestorParameter()
    {
        // The Lean predicate's 64-unit search loses this dependency. Production has no such
        // cutoff: all 65 references reach Lib, and A requires F's y through the selected Q.
        var links = string.Join("\n", Enumerable.Range(0, 65)
            .Select(i => $"  L{i} = {(i == 0 ? "Lib" : $"L{i - 1}")}"));
        var source = "F(y) = {\n  Lib = {\n    public Q = y\n    1\n  }\n" + links +
            "\n  A = L64.Q + 0\n  A\n}\nF(5)\n";
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
