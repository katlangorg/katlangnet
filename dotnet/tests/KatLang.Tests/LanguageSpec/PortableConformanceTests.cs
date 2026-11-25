namespace KatLang.Tests.LanguageSpec;

public class PortableConformanceTests
{
    [Theory]
    [InlineData("unlisted", "Unlisted")]
    [InlineData("missing", "Missing or repeated")]
    [InlineData("duplicate", "Missing or repeated")]
    [InlineData("unknown-field", "unexpectedField")]
    public void AFeatureCannotBeSilentlySkippedOrMisread(string change, string expectedError)
    {
        var directory = Directory.CreateTempSubdirectory();
        try
        {
            var features = directory.CreateSubdirectory("features");
            var names = change == "duplicate" ? """["features/a.json","features/a.json"]""" : """["features/a.json"]""";
            File.WriteAllText(Path.Combine(directory.FullName, "cases.json"),
                $$"""{"schemaVersion":3,"categories":["arithmetic"],"files":{{names}}}""");
            if (change != "missing")
                File.WriteAllText(Path.Combine(features.FullName, "a.json"), """[{"unexpectedField":0}]""");
            if (change == "unlisted")
                File.WriteAllText(Path.Combine(features.FullName, "b.json"), "[]");

            var error = Assert.Throws<InvalidDataException>(() => new SharedConformanceFiles(directory.FullName).ReadCases().ToList());
            Assert.Contains(expectedError, error.Message, StringComparison.Ordinal);
        }
        finally
        {
            directory.Delete(recursive: true);
        }
    }

    [Fact]
    public void ExposureShapesCoverEveryContainerRouteAndCapture()
    {
        var ids = LanguageSpecCorpus.AllCases().Select(c => c.Id).ToHashSet(StringComparer.Ordinal);
        foreach (var container in new[] { "member", "reference", "carrier", "inline-head" })
        foreach (var route in new[] { "dot-path", "dotted-open", "open-of-reference", "enclosing-open" })
        foreach (var capture in new[] { "row-capture", "member-capture" })
        {
            var prefix = $"exposure-shape-{container}-{route}-{capture}-";
            if (container == "inline-head" && capture == "row-capture" && route is "dotted-open" or "enclosing-open")
                Assert.Contains(prefix + "refused-open", ids);
            else
            {
                Assert.Contains(prefix + "inside", ids);
                Assert.Contains(prefix + "outside", ids);
            }
        }
    }
}
