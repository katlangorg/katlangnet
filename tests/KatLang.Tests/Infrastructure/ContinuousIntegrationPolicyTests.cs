using System.Text.Json;
using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace KatLang.Tests.Infrastructure;

/// <summary>
/// Pins the repository-owned CI/release architecture. These tests intentionally
/// inspect workflow source: GitHub-hosted execution is the integration proof,
/// while this suite prevents quiet policy drift before a workflow is pushed.
/// </summary>
public class ContinuousIntegrationPolicyTests
{
    private const string ValidatePath = ".github/workflows/validate.yml";
    private const string ReleasePath = ".github/workflows/release.yml";

    private static readonly string[] LeanTargets =
    [
        "CoreTests",
        "KatLangArityLaws",
        "AstDemo",
        "CoreArityAlgebra",
        "CoreArityAlgebraProofs",
        "SemanticExplorerCases",
        "LanguageSpecCases",
    ];

    private static readonly IReadOnlyDictionary<string, string> ReleaseRunners =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["win-x64"] = "windows-2025",
            ["win-arm64"] = "windows-11-arm",
            ["linux-x64"] = "ubuntu-24.04",
            ["linux-arm64"] = "ubuntu-24.04-arm",
            ["osx-x64"] = "macos-15-intel",
            ["osx-arm64"] = "macos-15",
        };

    [Fact]
    public void RequiredWorkflowFilesExist()
    {
        Assert.True(File.Exists(Absolute(ValidatePath)), $"Missing {ValidatePath}.");
        Assert.True(File.Exists(Absolute(ReleasePath)), $"Missing {ReleasePath}.");
    }

    [Fact]
    public void ValidateWorkflow_HasExactlyTheRequiredEventFamilies()
    {
        var source = Text(ValidatePath);
        Assert.Matches(@"(?m)^on:\n  pull_request:\n  push:\n    branches:\n      - main\n  workflow_dispatch:$", source);
        Assert.DoesNotContain("pull_request_target", source, StringComparison.Ordinal);
        Assert.DoesNotMatch(@"(?m)^\s+paths(?:-ignore)?:", source);
    }

    [Fact]
    public void ValidateWorkflow_IsReadOnly()
    {
        var source = Text(ValidatePath);
        Assert.Matches(@"(?m)^permissions:\n  contents: read$", source);
        Assert.DoesNotContain("contents: write", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ValidateWorkflow_CancelsOnlySupersededPullRequests()
    {
        var source = Text(ValidatePath);
        Assert.Contains("github.event.pull_request.number || github.run_id", source, StringComparison.Ordinal);
        Assert.Contains("cancel-in-progress: ${{ github.event_name == 'pull_request' }}", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ValidateWorkflow_ExposesStableCheckNames()
    {
        var source = Text(ValidatePath);
        Assert.Single(Regex.Matches(source, @"(?m)^    name: \.NET validation$").Cast<Match>());
        Assert.Single(Regex.Matches(source, @"(?m)^    name: Lean validation$").Cast<Match>());
    }

    [Fact]
    public void ValidateWorkflow_UsesTheCanonicalScriptPhases()
    {
        var source = Text(ValidatePath);
        Assert.Single(Regex.Matches(source, @"validate-all\.ps1 -Phase DotNet").Cast<Match>());
        Assert.Single(Regex.Matches(source, @"validate-all\.ps1 -Phase Lean").Cast<Match>());
    }

    [Fact]
    public void Workflows_DoNotDuplicateCanonicalValidationCommands()
    {
        var source = WorkflowText();
        Assert.DoesNotMatch(@"(?im)^\s*(?:run:\s*)?dotnet\s+(?:build|test)\b", source);
        Assert.DoesNotMatch(@"(?im)^\s*(?:run:\s*)?lake\s+build\b", source);
        Assert.DoesNotContain("KatLang.slnx", source, StringComparison.OrdinalIgnoreCase);
        foreach (var target in LeanTargets)
            Assert.DoesNotContain(target, source, StringComparison.Ordinal);
    }

    [Fact]
    public void ReleaseWorkflow_IsManualOnly()
    {
        var source = Text(ReleasePath);
        Assert.Matches(@"(?m)^on:\n  workflow_dispatch:", source);
        Assert.DoesNotMatch(@"(?m)^  (?:push|pull_request|schedule|repository_dispatch):", source);
        Assert.DoesNotContain("pull_request_target", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ReleaseWorkflow_AcceptsOneAuthoritativeVersionInput()
    {
        var source = Text(ReleasePath);
        Assert.Matches(@"(?m)^  workflow_dispatch:\n    inputs:\n      version:\n", source);
        Assert.Single(Regex.Matches(source, @"(?m)^      [a-zA-Z0-9_-]+:\n        description:").Cast<Match>());
        Assert.Contains("REQUESTED_VERSION: ${{ inputs.version }}", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ReleaseWorkflow_PinsTheExactDispatchedMainCommit()
    {
        var source = Text(ReleasePath);
        Assert.Contains("SOURCE_REF: ${{ github.ref }}", source, StringComparison.Ordinal);
        Assert.Contains("refs/heads/main", source, StringComparison.Ordinal);
        Assert.Contains("SOURCE_SHA: ${{ github.sha }}", source, StringComparison.Ordinal);
        Assert.Contains("source-sha: ${{ steps.release.outputs.source-sha }}", source, StringComparison.Ordinal);
        Assert.True(Regex.Matches(source, @"ref: \$\{\{ needs\.verify\.outputs\.source-sha \}\}").Count >= 3);
    }

    [Fact]
    public void ReleaseWorkflow_UsesTheRepositoryVersionAuthority()
    {
        var source = Text(ReleasePath);
        Assert.True(Regex.Matches(source, @"scripts/release-version\.ps1 -RequestedVersion").Count >= 2);
        Assert.DoesNotMatch(@"(?m)release-version\.ps1[^\n]*\n\s*if \(\$LASTEXITCODE", source);
        Assert.Contains("$version -cne $env:REQUESTED_VERSION", source, StringComparison.Ordinal);
        Assert.Contains("$repositoryVersion -cne $env:VERSION", source, StringComparison.Ordinal);
        Assert.DoesNotMatch(@"(?i)(?:-|/)p:(?:Version|KatLangVersion)\s*=", source);
        Assert.DoesNotContain("--property:Version", source, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReleaseWorkflow_RevalidatesBeforeEveryBuild()
    {
        var source = Text(ReleasePath);
        Assert.Contains("name: .NET validation", source, StringComparison.Ordinal);
        Assert.Contains("validate-all.ps1 -Phase DotNet", source, StringComparison.Ordinal);
        Assert.Contains("name: Lean validation", source, StringComparison.Ordinal);
        Assert.Contains("validate-all.ps1 -Phase Lean", source, StringComparison.Ordinal);
        Assert.Matches(@"(?s)  build:.*?needs:\n      - verify\n      - dotnet-validation\n      - lean-validation", source);
    }

    [Fact]
    public void ReleaseWorkflow_UsesTheReviewedNativeRunnerMatrix()
    {
        var source = Text(ReleasePath);
        foreach (var (rid, runner) in ReleaseRunners)
            Assert.Matches($@"(?m)^          - rid: {Regex.Escape(rid)}\n            runner: {Regex.Escape(runner)}$", source);

        Assert.Equal(ReleaseRunners.Count, Regex.Matches(source, @"(?m)^          - rid:").Count);
        Assert.Contains("runs-on: ${{ matrix.runner }}", source, StringComparison.Ordinal);
        Assert.Contains("fail-fast: false", source, StringComparison.Ordinal);
    }

    [Fact]
    public void CliProject_ScopesTheMacOsLinkerWorkaroundToX64()
    {
        var source = Text("src/KatLang.CLI/KatLang.CLI.csproj");
        Assert.Matches(
            @"(?s)<ItemGroup Condition=""'\$\(RuntimeIdentifier\)' == 'osx-x64'"">\s*<LinkerArg Include=""-Wl,-no_fixup_chains""\s*/>\s*</ItemGroup>",
            source);
        Assert.Single(Regex.Matches(source, @"<LinkerArg Include=""-Wl,-no_fixup_chains""\s*/>").Cast<Match>());
    }

    [Fact]
    public void ReleaseWorkflow_PublishesNativeAotWithoutOverridingVersion()
    {
        var source = Text(ReleasePath);
        Assert.Contains("dotnet publish ./src/KatLang.CLI/KatLang.CLI.csproj", source, StringComparison.Ordinal);
        Assert.Contains("--configuration Release", source, StringComparison.Ordinal);
        Assert.Contains("--runtime $env:RID", source, StringComparison.Ordinal);
        Assert.DoesNotContain("PublishAot=false", source, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotMatch(@"(?i)-p:(?:Version|KatLangVersion)=", source);
    }

    [Fact]
    public void ReleaseWorkflow_SmokeTestsEveryPublishedBinary()
    {
        var source = Text(ReleasePath);
        Assert.Contains("Invoke-Smoke -Arguments @('--version')", source, StringComparison.Ordinal);
        Assert.Contains("Invoke-Smoke -Arguments @('eval', '1 + 2')", source, StringComparison.Ordinal);
        Assert.Contains("Invoke-Smoke -Arguments @('eval', 'sin(1.234)')", source, StringComparison.Ordinal);
        Assert.Contains("0.9438182093746337048617510061568276", source, StringComparison.Ordinal);
        Assert.Matches(@"(?s)Smoke-test published executable.*?Package and verify release archive", source);
    }

    [Fact]
    public void ReleaseWorkflow_PackagesTheExecutableAndLegalFiles()
    {
        var source = Text(ReleasePath);
        Assert.Contains("$repositoryLegalFiles = @('LICENSE', 'NOTICE', 'PATENTS')", source, StringComparison.Ordinal);
        Assert.Contains("$dotnetLegalFiles = @('DOTNET-LICENSE.TXT', 'THIRD-PARTY-NOTICES.TXT')", source, StringComparison.Ordinal);
        Assert.Contains("$expectedEntries = @($executableName) + $repositoryLegalFiles + $dotnetLegalFiles", source, StringComparison.Ordinal);
        Assert.Contains("SourceName = 'LICENSE.txt'; DestinationName = 'DOTNET-LICENSE.TXT'", source, StringComparison.Ordinal);
        Assert.Contains("SourceName = 'ThirdPartyNotices.txt'; DestinationName = 'THIRD-PARTY-NOTICES.TXT'", source, StringComparison.Ordinal);
        Assert.Contains("Get-ChildItem -LiteralPath $env:DOTNET_ROOT -File", source, StringComparison.Ordinal);
        Assert.Contains("Copy-Item -LiteralPath $Source -Destination (Join-Path $packageDirectory $DestinationName)", source, StringComparison.Ordinal);
        Assert.Contains("Compare-Object -ReferenceObject $expectedEntries -DifferenceObject $actualEntries", source, StringComparison.Ordinal);
        Assert.Contains("$actualEntries.Count -ne $expectedEntries.Count", source, StringComparison.Ordinal);
        Assert.Contains("$entry.Length -eq 0", source, StringComparison.Ordinal);
        Assert.Contains("$verboseEntry -notmatch '^-rwxr-xr-x'", source, StringComparison.Ordinal);
        Assert.DoesNotContain(".dbg", source, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain(".pdb", source, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData("src/KatLang/KatLang.csproj")]
    [InlineData("src/KatLang.CLI/KatLang.CLI.csproj")]
    public void ReleaseNoticeInventory_HasNoUnreviewedProductNuGetDependencies(string project)
    {
        var document = XDocument.Parse(Text(project));
        var packageReferences = document
            .Descendants()
            .Where(element => element.Name.LocalName == "PackageReference")
            .Select(element => (string?)element.Attribute("Include") ?? element.ToString())
            .ToArray();

        Assert.Empty(packageReferences);
    }

    [Fact]
    public void ReleaseWorkflow_CollectsAllSixArchivesBeforePublication()
    {
        var source = Text(ReleasePath);
        foreach (var rid in ReleaseRunners.Keys)
        {
            var extension = rid.StartsWith("win-", StringComparison.Ordinal) ? "zip" : "tar.gz";
            Assert.Contains($"katlang-cli-$env:VERSION-{rid}.{extension}", source, StringComparison.Ordinal);
        }

        Assert.Contains("pattern: release-*", source, StringComparison.Ordinal);
        Assert.Contains("name: complete-release-bundle", source, StringComparison.Ordinal);
        Assert.Contains("SHA256SUMS", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ReleaseWorkflow_PublicationDependsOnTheCompleteBundle()
    {
        var source = Text(ReleasePath);
        Assert.Matches(@"(?s)  collect:.*?needs:\n      - verify\n      - build", source);
        Assert.Matches(@"(?s)  publish:.*?needs:\n      - verify\n      - collect", source);
    }

    [Fact]
    public void ReleaseWorkflow_UsesADraftAsThePublicVisibilityGate()
    {
        var source = Text(ReleasePath);
        var create = source.IndexOf("gh release create", StringComparison.Ordinal);
        var verifyAssets = source.IndexOf("$assetDifference", create, StringComparison.Ordinal);
        var publish = source.IndexOf("gh release edit", verifyAssets, StringComparison.Ordinal);
        Assert.True(create >= 0 && verifyAssets > create && publish > verifyAssets,
            "release must be created as a draft, asset-verified, and only then published");
        Assert.Contains("--draft `", source, StringComparison.Ordinal);
        Assert.Contains("--draft=false", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ReleaseWorkflow_UsesUserFacingCliMetadata()
    {
        var source = Text(ReleasePath);
        Assert.Contains("--title \"KatLang.CLI $env:VERSION\"", source, StringComparison.Ordinal);
        Assert.Contains("KatLang command-line interface (CLI) for Windows, Linux, and macOS, available for x64 and ARM64.", source, StringComparison.Ordinal);
        Assert.Contains("Each archive contains a standalone executable, KatLang licensing files, and the .NET license and third-party notices; no .NET installation is required.", source, StringComparison.Ordinal);
        Assert.DoesNotContain("NativeAOT command-line binaries", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ReleaseWorkflow_RefusesExistingVersionsBeforeAndAfterBuilds()
    {
        var source = Text(ReleasePath);
        Assert.True(Regex.Matches(source, @"git ls-remote --tags origin").Count >= 2);
        Assert.True(Regex.Matches(source, @"gh api --paginate").Count >= 2);
        Assert.DoesNotContain("--force", source, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("release delete", source, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReleaseWorkflow_SerializesPublicationWithoutCancelling()
    {
        var source = Text(ReleasePath);
        Assert.Contains("group: katlang-release-publication", source, StringComparison.Ordinal);
        Assert.Contains("cancel-in-progress: false", source, StringComparison.Ordinal);
    }

    [Fact]
    public void Workflows_UseMinimumContentPermissions()
    {
        var validate = Text(ValidatePath);
        var release = Text(ReleasePath);
        Assert.Single(Regex.Matches(validate, @"(?m)^  contents: read$").Cast<Match>());
        Assert.Single(Regex.Matches(release, @"(?m)^  contents: read$").Cast<Match>());
        Assert.Single(Regex.Matches(release, @"(?m)^      contents: write$").Cast<Match>());
    }

    [Fact]
    public void Workflows_RequireNoUserManagedSecrets()
    {
        var source = WorkflowText();
        Assert.DoesNotContain("secrets.", source, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("GH_TOKEN: ${{ github.token }}", Text(ReleasePath), StringComparison.Ordinal);
    }

    [Fact]
    public void EveryActionUse_IsPinnedToACommentedCommitSha()
    {
        var uses = Regex.Matches(WorkflowText(), @"(?m)^\s*uses:\s*(?<action>[^@\s]+)@(?<revision>[^\s#]+)\s+#\s+(?<version>v\S+)\s*$");
        Assert.True(uses.Count > 0, "expected pinned action uses");
        foreach (Match use in uses)
        {
            Assert.Matches("^[0-9a-f]{40}$", use.Groups["revision"].Value);
            Assert.Matches(@"^v[0-9]+\.[0-9]+\.[0-9]+$", use.Groups["version"].Value);
        }

        Assert.Equal(Regex.Matches(WorkflowText(), @"(?m)^\s*uses:").Count, uses.Count);
    }

    [Fact]
    public void EveryCheckoutDisablesCredentialPersistence()
    {
        var source = WorkflowText();
        var checkouts = Regex.Matches(source, @"(?m)^\s*uses: actions/checkout@");
        Assert.True(checkouts.Count > 0);
        foreach (Match checkout in checkouts)
        {
            var following = source.Substring(checkout.Index, Math.Min(300, source.Length - checkout.Index));
            Assert.Contains("persist-credentials: false", following, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Workflows_StartWithoutBuildCaches()
    {
        var source = WorkflowText();
        Assert.DoesNotContain("actions/cache", source, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotMatch(@"(?m)^\s+cache:", source);
    }

    [Fact]
    public void GlobalJson_PinsTheExactSdkWithoutRollForward()
    {
        using var document = JsonDocument.Parse(Text("global.json"));
        var sdk = document.RootElement.GetProperty("sdk");
        Assert.Equal("11.0.100-preview.7.26381.103", sdk.GetProperty("version").GetString());
        Assert.Equal("disable", sdk.GetProperty("rollForward").GetString());
        Assert.True(sdk.GetProperty("allowPrerelease").GetBoolean());
    }

    [Fact]
    public void LeanToolchain_RemainsTheOnlyLeanVersionAuthority()
    {
        var source = WorkflowText();
        var toolchain = Text("lean/lean-toolchain").Trim();
        Assert.DoesNotContain(toolchain, source, StringComparison.Ordinal);
        Assert.Contains("leanprover/elan/227caca133724d5516bee25c2aeb3e609478f2d8/elan-init.sh", source, StringComparison.Ordinal);
        Assert.Contains("a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53", source, StringComparison.Ordinal);
    }

    [Fact]
    public void Dependabot_UpdatesOnlyGitHubActionsPins()
    {
        var source = Text(".github/dependabot.yml");
        Assert.Single(Regex.Matches(source, @"package-ecosystem:").Cast<Match>());
        Assert.Contains("package-ecosystem: github-actions", source, StringComparison.Ordinal);
        Assert.Contains("interval: monthly", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ValidateScript_HasAllDotNetLeanPhaseContract()
    {
        var source = Text("scripts/validate-all.ps1");
        Assert.Contains("[ValidateSet(\"All\", \"DotNet\", \"Lean\")]", source, StringComparison.Ordinal);
        Assert.Contains("[string]$Phase = \"All\"", source, StringComparison.Ordinal);
        Assert.Contains("$Phase -in @(\"All\", \"DotNet\")", source, StringComparison.Ordinal);
        Assert.Contains("$Phase -in @(\"All\", \"Lean\")", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ValidateScript_OwnsEachLeanTargetExactlyOnce()
    {
        var source = Text("scripts/validate-all.ps1");
        foreach (var target in LeanTargets)
            Assert.Single(Regex.Matches(source, "\"" + Regex.Escape(target) + "\"").Cast<Match>());
        Assert.Contains("foreach ($target in $leanTargets)", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ValidateScript_PreservesDirtyDeveloperStateAndChecksCleanCiDirectly()
    {
        var source = Text("scripts/validate-all.ps1");
        Assert.Contains("Get-RepositorySnapshot", source, StringComparison.Ordinal);
        Assert.Contains("IndexDigest", source, StringComparison.Ordinal);
        Assert.Contains("WorktreeDigest", source, StringComparison.Ordinal);
        Assert.Contains("UntrackedDigest", source, StringComparison.Ordinal);
        Assert.Contains("\"diff\", \"--exit-code\", \"--\"", source, StringComparison.Ordinal);
        Assert.Contains("\"status\", \"--porcelain=v1\", \"--untracked-files=all\"", source, StringComparison.Ordinal);
    }

    [Fact]
    public void CliProject_RenamesEveryReleaseOsButDoesNotPackage()
    {
        var source = Text("src/KatLang.CLI/KatLang.CLI.csproj");
        Assert.Contains("StartsWith('win-')", source, StringComparison.Ordinal);
        Assert.Contains("StartsWith('linux-')", source, StringComparison.Ordinal);
        Assert.Contains("StartsWith('osx-')", source, StringComparison.Ordinal);
        Assert.DoesNotContain("Compress-Archive", source, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotMatch(@"(?i)<Exec\b[^>]*\btar\b", source);
    }

    private static string WorkflowText()
        => Text(ValidatePath) + "\n" + Text(ReleasePath);

    private static string Text(string relativePath)
        => File.ReadAllText(Absolute(relativePath)).ReplaceLineEndings("\n");

    private static string Absolute(string relativePath)
        => Path.Combine(RepoRoot.Find(), relativePath.Replace('/', Path.DirectorySeparatorChar));
}
