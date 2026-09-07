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

    /// <summary>
    /// A product name immediately followed by a version, allowing ordinary
    /// header punctuation, Markdown and wrapped Lean comments. Requiring that
    /// adjacency keeps unrelated numbers, toolchain versions and references to
    /// KatLangVersion.props outside this policy.
    /// </summary>
    private static readonly Regex KatLangVersionLiteral = new(
        """\bKatLang\b[\s:="'`*()\[\]–—-]+(?:version\b[\s:="'`*()\[\]–—-]+)?v?[ \t]*(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(?!\w)""",
        RegexOptions.CultureInvariant | RegexOptions.IgnoreCase);

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
        "src/KatLang.CLI/KatLang.CLI.csproj",
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
    [InlineData("src/KatLang.CLI/KatLang.CLI.csproj")]
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
    /// Prevents a stale product-version header in the Lean model or its docs.
    /// The central version policy also applies outside MSBuild files.
    /// </summary>
    [Fact]
    public void LeanSourcesAndDocs_CarryNoKatLangVersionLiteral()
    {
        var root = RepoRoot.Find();
        var offenders = FindLeanVersionLiterals(Path.Combine(root, "lean"));

        Assert.True(offenders.Count == 0,
            $"The KatLang release version is written only in {PropsRelativePath}; the Lean model is versioned with the " +
            "product and must not restate its number. Remove these version literals from lean/:\n" +
            string.Join("\n", offenders.Select(offender => "lean/" + offender)));
    }

    private static IReadOnlyList<string> FindLeanVersionLiterals(string leanRoot)
    {
        var offenders = new List<string>();
        // The shared walker excludes .lake, bin, obj and other build outputs,
        // and selects text extensions only. Sort normalized relative paths so
        // diagnostics do not depend on filesystem enumeration order or OS.
        var files = ArtifactRegenerationPolicyTests.EnumerateRepositoryTextFiles(leanRoot)
            .Select(file => (File: file, Relative: Path.GetRelativePath(leanRoot, file).Replace('\\', '/')))
            .OrderBy(entry => entry.Relative, StringComparer.Ordinal);
        foreach (var (file, relative) in files)
        {
            var text = File.ReadAllText(file).ReplaceLineEndings("\n");
            foreach (Match match in KatLangVersionLiteral.Matches(text))
            {
                var lineNumber = 1 + text[..match.Index].Count(c => c == '\n');
                offenders.Add($"{relative}:{lineNumber}: {match.Value.ReplaceLineEndings(" ")}");
            }
        }
        return offenders;
    }

    [Fact]
    public void LeanVersionScan_IsRecursiveSortedAndSkipsBuildOutputs()
    {
        var scratch = Path.Combine(Path.GetTempPath(), "katlang-version-policy", Guid.NewGuid().ToString("N"));
        try
        {
            foreach (var relative in new[]
            {
                "z/nested/Header.LEAN", "a/notes.md", ".lake/packages/Header.lean",
                "bin/Header.lean", "obj/notes.md", "compiled.olean", "binary.dll",
            })
            {
                var file = Path.Combine(scratch, relative);
                Directory.CreateDirectory(Path.GetDirectoryName(file)!);
                File.WriteAllText(file, "intro\r\n-- KatLang version:\r\n-- 1.2.3\r\n");
            }
            Assert.Equal(
                new[] { "a/notes.md:2: KatLang version: -- 1.2.3", "z/nested/Header.LEAN:2: KatLang version: -- 1.2.3" },
                FindLeanVersionLiterals(scratch));
        }
        finally
        {
            if (Directory.Exists(scratch))
                Directory.Delete(scratch, recursive: true);
        }
    }

    [Theory]
    [InlineData("-- KatLang v0.8.190 (core AST + semantics + while/repeat init boundaries)", true)]
    [InlineData("KatLang 0.8.196", true)]
    [InlineData("katlang v1.2.3-rc.1", true)]
    [InlineData("KatLang version 0.9.0", true)]
    [InlineData("This is KatLang version 1.2.3.", true)]
    [InlineData("-- KATLANG\tVERSION:\tV1.2.3", true)]
    [InlineData("KatLang: 1.2.3", true)]
    [InlineData("KatLang-version: 1.2.3-rc.1+build.42", true)]
    [InlineData("KatLang (v1.2.3)", true)]
    [InlineData("KatLang — v1.2.3", true)]
    [InlineData("/- **KatLang** version: `1.2.3` -/", true)]
    [InlineData("def banner := \"KatLang: v1.2.3\"", true)]
    [InlineData("-- KatLang version:\r\n-- 1.2.3", true)]
    [InlineData("-- KatLang authoritative language model (core AST + semantics)", false)]
    [InlineData("KatLangVersion.props is the single version source", false)]
    [InlineData("See `KatLangVersion.props` for the KatLang version.", false)]
    [InlineData("KatLang uses Lean v4.28.0", false)]
    [InlineData("KatLang previously used a different version policy (see 1.2.3).", false)]
    [InlineData("NotKatLang v1.2.3", false)]
    [InlineData("KatLang 1.2.30x", false)]
    [InlineData("KatLang 1.2.3.4", true)]
    [InlineData("leanprover/lean4:v4.28.0", false)]
    [InlineData("v0.8.196", false)]
    [InlineData("0.8.196", false)]
    [InlineData("KatLang 4 rows and 1.5 items", false)]
    public void KatLangVersionLiteralPattern_MatchesTheProductVersionForm_NotOrdinaryNumerals(string text, bool matches)
        => Assert.Equal(matches, KatLangVersionLiteral.IsMatch(text));

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

        var cli = Load("src/KatLang.CLI/KatLang.CLI.csproj");
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
