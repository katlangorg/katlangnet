using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace KatLang.Tests.Infrastructure;

/// <summary>
/// Pins the release-version architecture: <c>KatLangVersion.props</c> is the ONE
/// place the KatLang version is written; the library, the CLI and the CLI test
/// assembly (whose build-time <c>IntendedKatLangVersion</c> metadata is the
/// oracle the CLI version tests compare the loaded runtime against) all derive
/// theirs from it; no other MSBuild file carries a release-version literal; and
/// nothing inside the repository consumes KatLang as a version-pinned package,
/// so the CLI cannot lag behind the library it is built with.
/// </summary>
public class ReleaseVersionSourceTests
{
    private const string PropsRelativePath = "KatLangVersion.props";
    private const string CentralProperty = "KatLangVersion";
    private const string DerivedValue = "$(KatLangVersion)";

    /// <summary>A release version: major.minor.patch with an optional pre-release label and no build metadata.</summary>
    private static readonly Regex ReleaseVersion = new(
        @"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z.-]+)?$",
        RegexOptions.CultureInvariant);

    /// <summary>MSBuild properties that would set a version if written into a project.</summary>
    private static readonly string[] VersionBearingProperties =
    [
        "Version", "PackageVersion", "AssemblyVersion", "FileVersion", "InformationalVersion",
        "VersionPrefix", "VersionSuffix", CentralProperty,
    ];

    /// <summary>The projects that ship, or check, the KatLang version.</summary>
    private static readonly string[] ShippedProjects =
    [
        "src/KatLang/KatLang.csproj",
        "KatLang.CLI/KatLang.CLI.csproj",
    ];

    [Fact]
    public void KatLangVersionProps_WritesTheReleaseVersionExactlyOnce()
    {
        var props = Load(PropsRelativePath);

        var definition = Assert.Single(props.Descendants(CentralProperty));
        Assert.Matches(ReleaseVersion, definition.Value.Trim());

        var otherVersionProperties = props.Descendants()
            .Where(element => VersionBearingProperties.Contains(element.Name.LocalName, StringComparer.Ordinal))
            .Where(element => element.Name.LocalName != CentralProperty)
            .Select(element => element.Name.LocalName)
            .ToList();
        Assert.Empty(otherVersionProperties);
    }

    [Theory]
    [InlineData("src/KatLang/KatLang.csproj")]
    [InlineData("KatLang.CLI/KatLang.CLI.csproj")]
    [InlineData("tests/KatLang.CLI.Tests/KatLang.CLI.Tests.csproj")]
    public void EveryVersionedProject_ImportsThePropsAndDerivesEveryVersionPropertyFromIt(string relativePath)
    {
        var project = Load(relativePath);

        var imports = project.Descendants("Import")
            .Select(import => (string?)import.Attribute("Project"))
            .Where(path => path is not null && path.EndsWith(PropsRelativePath, StringComparison.Ordinal))
            .ToList();
        Assert.Single(imports);

        foreach (var element in project.Descendants()
                     .Where(element => VersionBearingProperties.Contains(element.Name.LocalName, StringComparer.Ordinal)))
        {
            Assert.True(element.Value.Trim() == DerivedValue,
                $"{relativePath}: <{element.Name.LocalName}> is {element.Value.Trim()}; every version property must be {DerivedValue}.");
        }
    }

    [Fact]
    public void ShippedProjects_SetTheirVersionFromTheCentralProperty()
    {
        foreach (var relativePath in ShippedProjects)
        {
            var versions = Load(relativePath).Descendants("Version").Select(element => element.Value.Trim()).ToList();
            Assert.Equal([DerivedValue], versions);
        }
    }

    /// <summary>
    /// The expectation of the CLI version tests is compiled into the CLI TEST
    /// assembly from the central property — build intent — and deliberately not
    /// read from the KatLang assembly under test. A literal here would be a
    /// second hand-synchronized pin that passes until the next release moves
    /// the props.
    /// </summary>
    [Fact]
    public void CliTests_ReceiveTheIntendedVersionAsBuildMetadata_DerivedNotRestated()
    {
        var project = Load("tests/KatLang.CLI.Tests/KatLang.CLI.Tests.csproj");
        var metadata = project.Descendants("AssemblyMetadata")
            .Where(item => (string?)item.Attribute("Include") == "IntendedKatLangVersion")
            .ToList();

        var intended = Assert.Single(metadata);
        Assert.Equal(DerivedValue, (string?)intended.Attribute("Value"));
    }

    [Fact]
    public void CliVersionTestOracle_ReadsTestBuildMetadata_NotTheRuntimeUnderTest()
    {
        var path = Path.Combine(RepoRoot.Find(), "tests", "KatLang.CLI.Tests", "CliApplicationTests.cs");
        var source = File.ReadAllText(path).ReplaceLineEndings("\n");
        Assert.Matches(
            @"IntendedKatLangVersion\s*=>\s*ReadIntendedKatLangVersion\s*\(\s*\)",
            source);

        var start = source.IndexOf("private static string ReadIntendedKatLangVersion()", StringComparison.Ordinal);
        var end = source.IndexOf("private sealed class", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start, "could not locate the intended-version reader in CliApplicationTests.cs");
        var reader = source[start..end];

        Assert.Contains("typeof(CliApplicationTests).Assembly", reader, StringComparison.Ordinal);
        Assert.Contains("GetCustomAttributes<AssemblyMetadataAttribute>()", reader, StringComparison.Ordinal);
        Assert.DoesNotContain("typeof(KatLangEngine)", reader, StringComparison.Ordinal);
        Assert.DoesNotMatch(@"0\.[0-9]+\.[0-9]+", reader);
    }

    [Fact]
    public void NoOtherMsBuildFile_CarriesAReleaseVersionLiteral()
    {
        var root = RepoRoot.Find();
        var offenders = new List<string>();

        foreach (var file in MsBuildFiles(root))
        {
            var relative = Path.GetRelativePath(root, file).Replace('\\', '/');
            if (relative == PropsRelativePath)
                continue;

            foreach (var element in XDocument.Load(file).Descendants()
                         .Where(element => VersionBearingProperties.Contains(element.Name.LocalName, StringComparer.Ordinal)))
            {
                if (element.Value.Trim() != DerivedValue)
                    offenders.Add($"{relative}: <{element.Name.LocalName}>{element.Value.Trim()}</{element.Name.LocalName}>");
            }
        }

        Assert.True(offenders.Count == 0,
            $"Release versions may only be written in {PropsRelativePath}; derive these from {DerivedValue}:\n" +
            string.Join("\n", offenders));
    }

    /// <summary>
    /// The drift class the CLI once had — a <c>PackageReference</c> to KatLang
    /// pinned at a previously published version — is structurally impossible
    /// while every in-repository consumer references the KatLang PROJECT.
    /// </summary>
    [Fact]
    public void NothingInTheRepository_ConsumesKatLangAsAVersionPinnedPackage()
    {
        var root = RepoRoot.Find();
        var packagePins = new List<string>();
        var projectReferences = 0;

        foreach (var file in MsBuildFiles(root).Where(file => file.EndsWith(".csproj", StringComparison.OrdinalIgnoreCase)))
        {
            var project = XDocument.Load(file);
            packagePins.AddRange(project.Descendants("PackageReference")
                .Where(reference => string.Equals((string?)reference.Attribute("Include"), "KatLang", StringComparison.OrdinalIgnoreCase))
                .Select(_ => Path.GetRelativePath(root, file).Replace('\\', '/')));
            projectReferences += project.Descendants("ProjectReference")
                .Count(reference => ((string?)reference.Attribute("Include") ?? "").EndsWith("KatLang.csproj", StringComparison.OrdinalIgnoreCase));
        }

        Assert.Empty(packagePins);
        Assert.True(projectReferences >= 2, "expected at least the CLI and the library tests to reference the KatLang project");

        var cli = Load("KatLang.CLI/KatLang.CLI.csproj");
        var cliKatLangReferences = cli.Descendants("ProjectReference")
            .Select(reference => (string?)reference.Attribute("Include") ?? "")
            .Where(path => path.EndsWith("KatLang.csproj", StringComparison.OrdinalIgnoreCase))
            .ToList();
        Assert.Single(cliKatLangReferences);
    }

    [Fact]
    public void NoRepositoryScriptOrWorkflow_OverridesTheCentralReleaseVersion()
    {
        var root = RepoRoot.Find();
        var assignment = new Regex(
            @"(?ix)(?:-|/)p:(?:Version|PackageVersion|AssemblyVersion|FileVersion|InformationalVersion|VersionPrefix|VersionSuffix|KatLangVersion)\s*=|--property(?::|\s+)(?:Version|PackageVersion|AssemblyVersion|FileVersion|InformationalVersion|VersionPrefix|VersionSuffix|KatLangVersion)\s*=",
            RegexOptions.CultureInvariant);
        var offenders = ArtifactRegenerationPolicyTests.EnumerateRepositoryTextFiles(root)
            .Where(file => new[] { ".ps1", ".psm1", ".sh", ".cmd", ".bat", ".yml", ".yaml" }
                .Contains(Path.GetExtension(file), StringComparer.OrdinalIgnoreCase))
            .Where(file => assignment.IsMatch(OperationalScriptText(file)))
            .Select(file => Path.GetRelativePath(root, file).Replace('\\', '/'))
            .ToList();

        Assert.True(offenders.Count == 0,
            $"Release scripts/workflows must consume {PropsRelativePath}, not override its version on the command line:\n" +
            string.Join("\n", offenders));
    }

    private static string OperationalScriptText(string file)
    {
        var extension = Path.GetExtension(file);
        return string.Join("\n", File.ReadLines(file).Where(line =>
        {
            var trimmed = line.TrimStart();
            if (trimmed.StartsWith('#'))
                return false;
            if (extension.Equals(".cmd", StringComparison.OrdinalIgnoreCase)
                || extension.Equals(".bat", StringComparison.OrdinalIgnoreCase))
            {
                return !trimmed.StartsWith("REM ", StringComparison.OrdinalIgnoreCase)
                       && !trimmed.StartsWith("::", StringComparison.Ordinal);
            }

            return true;
        }));
    }

    private static XDocument Load(string relativePath)
        => XDocument.Load(Path.Combine(RepoRoot.Find(), relativePath));

    private static IEnumerable<string> MsBuildFiles(string root)
        => ArtifactRegenerationPolicyTests.EnumerateRepositoryTextFiles(root)
            .Where(file =>
            {
                var extension = Path.GetExtension(file);
                return extension.Equals(".csproj", StringComparison.OrdinalIgnoreCase)
                    || extension.Equals(".props", StringComparison.OrdinalIgnoreCase)
                    || extension.Equals(".targets", StringComparison.OrdinalIgnoreCase);
            });
}
