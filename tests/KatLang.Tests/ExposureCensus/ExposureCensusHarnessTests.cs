namespace KatLang.Tests.ExposureCensus;

/// <summary>Negative controls for the census itself: incomplete evidence and failed programs stay visible.</summary>
public sealed class ExposureCensusHarnessTests
{
    [Fact]
    public async Task OpenProvidedHeads_ReachEveryNonOpenConsumer()
    {
        foreach (var pos in new[] { "value", "callee", "spread", "fallback" })
        {
            Assert.Null(CensusGrid.Exclusion("opened", pos, "own-used", "plain", "outside", "found", "member"));
            var @case = CensusGrid.Build(["opened", pos, "own-used", "plain", "outside", "found", "member"]);
            SourceProvenance.ParseValid(@case.Body + CensusRunner.Inside5);
            var result = await CensusRunner.Run(@case, collectLean: false);
            Assert.Null(result.Skipped);
            Assert.True(result.InsideWorks);
            Assert.StartsWith("LocalOnlyCapturedAncestorParameters[y@", result.Metadata["A"], StringComparison.Ordinal);
        }
    }

    [Fact]
    public void DeepRequirements_AreGeneratedForReadersOutsideTheirOwner()
    {
        foreach (var place in new[] { "outside", "in-lib", "in-box" })
        {
            Assert.Null(CensusGrid.Exclusion("name", "value", "none", "plain", place, "found", "deep"));
            var @case = CensusGrid.Build(["name", "value", "none", "plain", place, "found", "deep"]);
            SourceProvenance.ParseValid(@case.Body + CensusRunner.Inside5);
        }
    }

    [Fact]
    public void SourceRunErrors_KeepCategoryAndSubject()
    {
        foreach (var (source, expected) in new[]
        {
            ("1 / 0", "err div0"),
            ("true + 0", "err type"),
            ("F(y) = {\n A = y + 0\n 0\n}\nF.A", "err localOnlyProperty:A"),
        })
        {
            SourceProvenance.ParseValid(source);
            Assert.Equal(expected, CensusRunner.RenderEngine(KatLangEngine.Run(source)));
        }
    }

    [Fact]
    public async Task FailingInside_DoesNotSuppressTheEscapedUndercharge()
    {
        var @case = new CensusCase("harness=failed-inside-undercharge", [], """
            F(y) = {
              L = { public Sub = { public Q = y
                0 } }.Sub
              A = {
                open L
                Q + 0
              }
              1 / 0
            }

            """, [new CensusReader("A", ["F", "A"], "F.A")]);
        var result = await CensusRunner.Run(@case, collectLean: false);
        Assert.Null(result.Skipped);
        Assert.False(result.InsideWorks);
        Assert.Contains(result.Gaps, gap => gap.Class == "under-charge-masked-access");
    }

    [Fact]
    public async Task FailingInside_DoesNotSuppressNeededCopiesInTheModelCheck()
    {
        var @case = new CensusCase("harness=failed-inside-copy", [], """
            F(y) = {
              Lib = { public Sub = { public Q = 1
                y }
                0 }
              A = Lib.Sub.Q + 0
              1 / 0
            }

            """, [new CensusReader("A", ["F", "A"], "F.A")]);
        var result = await CensusRunner.Run(@case, collectLean: true);
        Assert.Null(result.Skipped);
        Assert.False(result.InsideWorks);
        Assert.Contains(result.Lean, item => item.Role == "copy-needed");
        Assert.DoesNotContain(result.Lean, item => item.Role == "copy-dead");
    }

    [Fact]
    public void ExternalEvidence_RejectsMissingDuplicateMalformedAndStaleResults()
    {
        var directory = Path.Combine(Path.GetTempPath(), "katlang-census-evidence-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(directory);
        try
        {
            var root = SourceProvenance.ParseValid("1").Root;
            CensusLeanItem[] items = [new("one#real#in5", "one", "real", "real", root, "ok 1")];
            CensusLean.Emit(items, directory);
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory, items));
            var path = Path.Combine(directory, "census-0000.out");
            const string observation = "CENSUS\tone#real#in5\ttrue\ttrue\tok 1\n";
            File.WriteAllText(path, observation + observation);
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory, items));
            File.WriteAllText(path, observation.Replace("true", "unknown", StringComparison.Ordinal));
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory, items));
            File.WriteAllText(path, observation);
            Assert.Empty(CensusLean.Check(directory, items));
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory,
                [items[0] with { Tree = SourceProvenance.ParseValid("2").Root }]));
            File.WriteAllText(Path.Combine(directory, "manifest.tsv"), "");
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory, items));

            var headPath = Path.Combine(directory, "head.out");
            const string head = "one\tin5\tOUT\tOK 1\n";
            File.WriteAllText(headPath, head);
            Assert.Throws<InvalidDataException>(() => ExposureCensusTests.HeadOutput.Read(headPath).RequireComplete([("one", "in5")]));
            File.WriteAllText(headPath, head + head);
            Assert.Throws<InvalidDataException>(() => ExposureCensusTests.HeadOutput.Read(headPath));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }
}
