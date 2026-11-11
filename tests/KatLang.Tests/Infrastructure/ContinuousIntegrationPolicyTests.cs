using System.Diagnostics;
using System.Reflection;
using System.Reflection.Emit;
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
    private const string DotNetSetupPath = ".github/actions/setup-baseline-dotnet";
    private const string LeanInstallPath = "scripts/install-lean-toolchain.sh";

    // Every local action a workflow may use. Its steps run inside the calling job, so the
    // pinning, cache, failure-masking and Dependabot policies extend to each entry.
    private static readonly string[] LocalActionPaths = [DotNetSetupPath];

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
            ["win-arm64"] = "windows-11-vs2026-arm",
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
    public void ValidationJobs_UseTheAgreedCiTimeouts()
    {
        foreach (var workflow in new[] { ValidatePath, ReleasePath })
        {
            var source = Text(workflow);
            foreach (var (job, minutes) in new[] { ("dotnet-validation", 60), ("lean-validation", 30) })
            {
                var section = Regex.Match(source, $@"(?ms)^  {job}:\n.*?(?=^  [a-z][a-z-]*:|\z)");
                Assert.True(section.Success, $"Missing validation job in {workflow}: {job}");
                Assert.Single(Regex.Matches(section.Value, @"(?m)^    timeout-minutes:").Cast<Match>());
                Assert.Matches($@"(?m)^    timeout-minutes: {minutes}$", section.Value);
            }
        }
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
        // A value-taking option through the native executable: option parsing and the host
        // display default survive NativeAOT publication on every platform.
        Assert.Contains("Invoke-Smoke -Arguments @('eval', '--display-decimals', '2', '1 / 3')", source, StringComparison.Ordinal);
        Assert.Contains("if ($displayOutput -cne '0.33')", source, StringComparison.Ordinal);
        Assert.Matches(@"(?s)Smoke-test published executable.*?Package and verify release archive", source);
    }

    [Fact]
    public void ReleaseWorkflow_PackagesTheExecutableAndLegalFiles()
    {
        var source = Text(ReleasePath);
        Assert.Contains("$repositoryLegalFiles = @('LICENSE', 'NOTICE', 'PATENTS')", source, StringComparison.Ordinal);
        Assert.Contains("$dotnetLegalFiles = @('DOTNET-LICENSE.TXT', 'THIRD-PARTY-NOTICES.TXT')", source, StringComparison.Ordinal);
        Assert.Contains("$textFileNames = $repositoryLegalFiles + $dotnetLegalFiles", source, StringComparison.Ordinal);
        Assert.Contains("$expectedEntries = @($executableName) + $textFileNames", source, StringComparison.Ordinal);
        Assert.Contains("src/KatLang.CLI/obj/project.assets.json", source, StringComparison.Ordinal);
        Assert.Contains("$assets.project.frameworks.PSObject.Properties", source, StringComparison.Ordinal);
        Assert.Contains("$runtimePackId = \"Microsoft.NETCore.App.Runtime.$env:RID\"", source, StringComparison.Ordinal);
        Assert.Contains("$compilerPackId = \"runtime.$env:RID.Microsoft.DotNet.ILCompiler\"", source, StringComparison.Ordinal);
        Assert.Contains("-FileName 'LICENSE.TXT'", source, StringComparison.Ordinal);
        Assert.True(Regex.Matches(source, "-FileName 'THIRD-PARTY-NOTICES.TXT'").Count >= 2);
        Assert.Contains("$runtimeNoticeHash -cne $compilerNoticeHash", source, StringComparison.Ordinal);
        Assert.Contains("-Source $runtimeLicense -DestinationName 'DOTNET-LICENSE.TXT'", source, StringComparison.Ordinal);
        Assert.Contains("-Source $runtimeNotices -DestinationName 'THIRD-PARTY-NOTICES.TXT'", source, StringComparison.Ordinal);
        Assert.DoesNotContain("Get-ChildItem -LiteralPath $env:DOTNET_ROOT", source, StringComparison.Ordinal);
        Assert.Contains("Copy-Item -LiteralPath $Source -Destination (Join-Path $packageDirectory $DestinationName)", source, StringComparison.Ordinal);
        Assert.Contains("Compare-Object -ReferenceObject $expectedEntries -DifferenceObject $actualEntries", source, StringComparison.Ordinal);
        Assert.Contains("$actualEntries.Count -ne $expectedEntries.Count", source, StringComparison.Ordinal);
        Assert.Contains("$entry.Length -eq 0", source, StringComparison.Ordinal);
        Assert.Contains("& chmod 0755 $executable", source, StringComparison.Ordinal);
        Assert.Contains("& chmod 0644 $textFile", source, StringComparison.Ordinal);
        Assert.True(Regex.Matches(source, @"foreach \(\$name in \$textFileNames\)").Count >= 2);
        Assert.Contains("$verboseExecutableEntry -notmatch '^-rwxr-xr-x'", source, StringComparison.Ordinal);
        Assert.Contains("$verboseTextEntry -notmatch '^-rw-r--r--'", source, StringComparison.Ordinal);
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
        var create = source.IndexOf("$draftUrl = (& gh release create", StringComparison.Ordinal);
        var lookup = source.IndexOf("gh api --paginate --slurp", create, StringComparison.Ordinal);
        var verifyAssets = source.IndexOf("$assetDifference", create, StringComparison.Ordinal);
        var publish = source.IndexOf("gh api --method PATCH", verifyAssets, StringComparison.Ordinal);
        Assert.True(create >= 0 && lookup > create && verifyAssets > lookup && publish > verifyAssets,
            "release must be created as a draft, resolved from the release list, asset-verified, and only then published");
        Assert.Contains("--draft `", source, StringComparison.Ordinal);
        Assert.Contains("releases/tag/[^/?#]+$", source, StringComparison.Ordinal);
        Assert.Contains("$release.html_url -ceq $draftUrl", source, StringComparison.Ordinal);
        Assert.Contains("\"repos/$env:REPOSITORY/releases/$($draft.id)\"", source, StringComparison.Ordinal);
        Assert.Contains("-F \"tag_name=$env:TAG\"", source, StringComparison.Ordinal);
        Assert.Contains("-F draft=false", source, StringComparison.Ordinal);
        Assert.DoesNotContain("gh release edit $env:TAG --draft=false", source, StringComparison.Ordinal);
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
    public void EveryExternalActionUse_IsPinnedToACommentedCommitSha()
    {
        var source = WorkflowAndLocalActionText();
        // `uses:` is a step key, alone on its line or opening the step (`- uses:`).
        var uses = Regex.Matches(source, @"(?m)^ *(?:- +)?uses: *(?<reference>[^\n]*)$");
        Assert.True(uses.Count > 0, "expected pinned action uses");
        foreach (Match use in uses)
        {
            var reference = use.Groups["reference"].Value;
            if (LocalActionPaths.Any(path => reference == $"./{path}"))
                continue;

            Assert.Matches(@"^[^@\s]+@[0-9a-f]{40}\s+#\s+v[0-9]+\.[0-9]+\.[0-9]+$", reference);
        }

        // No `uses:` is written in a form the scan above cannot read.
        Assert.Equal(Regex.Matches(source, @"\buses\s*:").Count, uses.Count);
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
        // setup-dotnet's `cache:` input belongs to the local setup action, so the scan includes it.
        var source = WorkflowAndLocalActionText();
        Assert.DoesNotContain("actions/cache", source, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotMatch(@"(?m)^\s+cache:", source);
    }

    [Fact]
    public void GlobalJson_AllowsStableDotNet11AndLaterSdks()
    {
        // Both workflows install the baseline SDK from global.json. The CLI uses
        // the same file to select the highest installed stable SDK at or above it.
        Assert.True(
            File.Exists(Absolute("global.json")),
            "global.json defines the repository's SDK policy and supplies the baseline SDK to both workflows.");

        using var document = JsonDocument.Parse(Text("global.json"));
        var sdk = document.RootElement.GetProperty("sdk");
        Assert.Equal("11.0.100", sdk.GetProperty("version").GetString());
        Assert.Equal("latestMajor", sdk.GetProperty("rollForward").GetString());
        Assert.False(sdk.GetProperty("allowPrerelease").GetBoolean());
    }

    [Fact]
    public void DotNetSetup_InstallsTheExactGlobalJsonSdkVersion()
    {
        var source = Text($"{DotNetSetupPath}/action.yml");
        Assert.Contains("(Join-Path $env:GITHUB_WORKSPACE 'global.json') -Raw | ConvertFrom-Json", source, StringComparison.Ordinal);
        Assert.Contains("$version = $config.sdk.version", source, StringComparison.Ordinal);
        Assert.Contains("-Value \"version=$version\"", source, StringComparison.Ordinal);
        Assert.Contains("uses: actions/setup-dotnet@", source, StringComparison.Ordinal);
        Assert.Contains("dotnet-version: ${{ steps.sdk.outputs.version }}", source, StringComparison.Ordinal);
        Assert.DoesNotContain("global-json-file:", source, StringComparison.Ordinal);
        Assert.DoesNotContain("uses: actions/setup-dotnet@", WorkflowText(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(ValidatePath, "dotnet-validation", "./scripts/validate-all.ps1 -Phase DotNet")]
    [InlineData(ValidatePath, StackSuiteJob, "./scripts/validate-stack-suites.ps1")]
    [InlineData(ValidatePath, StandaloneBuildJob, "./scripts/build-standalone-tools.ps1")]
    [InlineData(ReleasePath, "dotnet-validation", "./scripts/validate-all.ps1 -Phase DotNet")]
    [InlineData(ReleasePath, StackSuiteJob, "./scripts/validate-stack-suites.ps1")]
    [InlineData(ReleasePath, "build", "dotnet publish ")]
    public void DotNetJobs_SetUpTheBaselineSdkBeforeBuilding(string workflow, string job, string command)
    {
        var section = JobSection(Text(workflow), job);
        var checkout = section.IndexOf("uses: actions/checkout@", StringComparison.Ordinal);
        var setup = section.IndexOf($"uses: ./{DotNetSetupPath}", StringComparison.Ordinal);
        var build = section.IndexOf(command, StringComparison.Ordinal);
        Assert.True(checkout >= 0 && setup > checkout && build > setup, $"Expected checkout, SDK setup, and build in order in {workflow} ({job}).");
    }

    [Fact]
    public void LeanToolchain_RemainsTheOnlyLeanVersionAuthority()
    {
        var source = WorkflowText();
        var toolchain = Text("lean/lean-toolchain").Trim();
        var installScript = Text(LeanInstallPath);
        Assert.DoesNotContain(toolchain, source + installScript, StringComparison.Ordinal);
        Assert.Contains("$(<lean/lean-toolchain)", installScript, StringComparison.Ordinal);
        Assert.Contains("https://api.github.com/repos/leanprover/lean4/releases", installScript, StringComparison.Ordinal);
        Assert.Contains("Accept: application/octet-stream", installScript, StringComparison.Ordinal);
        Assert.Contains("sha256sum -c -", installScript, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(ValidatePath)]
    [InlineData(ReleasePath)]
    public void LeanValidation_InstallsToolchainBeforeBuilding(string workflow)
    {
        var source = Text(workflow);
        var install = source.IndexOf($"bash {LeanInstallPath}", StringComparison.Ordinal);
        var validation = source.IndexOf("validate-all.ps1 -Phase Lean", StringComparison.Ordinal);
        Assert.True(install >= 0 && install < validation,
            $"{workflow} must install the Lean toolchain before running Lean validation.");
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
    public void Dependabot_CoversTheWorkflowsAndEveryLocalAction()
    {
        // The directory "/" covers .github/workflows and a root action.yml only: a pin
        // inside a local action is proposed for update only when its directory is listed.
        var source = Text(".github/dependabot.yml");
        Assert.DoesNotMatch(@"(?m)^\s*directory:", source);
        var list = Regex.Match(source, @"(?m)^    directories:\n(?<entries>(?:      - [^\n]*\n)+)");
        Assert.True(list.Success, "dependabot.yml must list the directories it updates.");
        var directories = Regex.Matches(list.Groups["entries"].Value, @"(?m)^      - (?<directory>[^\n]*)$")
            .Select(match => match.Groups["directory"].Value);
        Assert.Equal(LocalActionPaths.Select(path => $"/{path}").Prepend("/"), directories);
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
    public void ValidateScript_RunsOneOrdinaryMode_BeforeAnyTestHostStarts()
    {
        var source = Text("scripts/validate-all.ps1");
        Assert.DoesNotContain("ForceInvocationPlans", source, StringComparison.Ordinal);
        Assert.Contains($"$planModeVariable = \"{ForcedInvocationPlansHook.Variable}\"", source, StringComparison.Ordinal);
        // An inherited diagnostic flag must not silently change normal validation.
        const string fix = "Set-PlanModeVariable -Value $null";
        Assert.Single(Regex.Matches(source, Regex.Escape(fix)).Cast<Match>());
        Assert.True(source.IndexOf(fix, StringComparison.Ordinal) < source.IndexOf("\"build\", \"./KatLang.slnx\"", StringComparison.Ordinal));
        Assert.Contains("Set-PlanModeVariable -Value $inheritedPlanMode", source, StringComparison.Ordinal);
        // Removal goes through the Env: drive: PowerShell would pass $null to SetEnvironmentVariable as "".
        Assert.Contains("Remove-Item -LiteralPath \"Env:$planModeVariable\"", source, StringComparison.Ordinal);
        Assert.DoesNotContain("SetEnvironmentVariable($planModeVariable", source, StringComparison.Ordinal);
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
    public void ValidateScript_KeepsOneTrxPerTestProjectInAnIgnoredDirectory()
    {
        var source = Text("scripts/validate-all.ps1");
        // The full test invocation is unchanged apart from its result output.
        Assert.Single(Regex.Matches(source, Regex.Escape("\"test\", \"./KatLang.slnx\", \"-p:UseSharedCompilation=false\", \"--no-build\",")).Cast<Match>());
        Assert.Single(Regex.Matches(source, Regex.Escape("\"build\", \"./KatLang.slnx\", \"-p:UseSharedCompilation=false\")")).Cast<Match>());
        // A prefix gets a reserved, collision-free file per project; a fixed LogFileName would be overwritten.
        Assert.Contains("\"--logger\", \"trx;LogFilePrefix=katlang\", \"--results-directory\", $testResults", source, StringComparison.Ordinal);
        Assert.DoesNotContain("LogFileName", source, StringComparison.Ordinal);
        // Diagnostics are written under artifacts/validation only once git confirms it is ignored.
        Assert.Contains("& git check-ignore -q -- \"$relative/validation-record.txt\"", source, StringComparison.Ordinal);
        Assert.Contains("$relative = \"artifacts/validation/$name\"", source, StringComparison.Ordinal);
        Assert.Contains("[System.IO.Path]::GetTempPath()", source, StringComparison.Ordinal);
        Assert.Matches(@"(?m)^artifacts/$", Text(".gitignore"));
        // The strict allocation probes leave their logs in the same directory.
        Assert.Contains(
            $"$testDiagnosticsVariable = \"{GcIsolatedAllocation.DiagnosticsDirectoryEnvironment}\"",
            source,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ValidateScript_RecordsCommandsWithoutChangingTheirResult()
    {
        var source = Text("scripts/validate-all.ps1");
        Assert.Contains("Write-ValidationRecord \"command: $FilePath", source, StringComparison.Ordinal);
        // A nonzero exit still throws after it is recorded, and the summary runs in a finally.
        Assert.Matches(@"finally \{\n\s+\$outcome = [^\n]+\n\s+Write-ValidationRecord [^\n]+\n\s+\}\n\n\s+if \(\$exitCode -ne 0\) \{\n\s+throw ", source);
        Assert.Matches(@"finally \{\n\s+\[Environment\]::SetEnvironmentVariable\(\$testDiagnosticsVariable, \$inheritedTestDiagnostics\)\n\s+Write-TestResultSummary ", source);
        Assert.Contains("exit 1", source, StringComparison.Ordinal);
    }

    [Fact]
    public void ValidateScript_SurvivesALostConsoleWithoutMaskingFailures()
    {
        var source = Text("scripts/validate-all.ps1");
        // Only the console host's Win32 233 failure (ERROR_PIPE_NOT_CONNECTED) is recognized.
        Assert.Contains("$errorPipeNotConnected = 233", source, StringComparison.Ordinal);
        Assert.Contains("-isnot [System.ComponentModel.Win32Exception]", source, StringComparison.Ordinal);
        // After completion the command's own exit code is kept; before start the command never ran.
        Assert.Contains(
            "if (-not $wrapped -and $null -ne $global:LASTEXITCODE -and $errorId -in @(\"SetConsoleWindowTitle\", \"SetConsoleMode\")) {",
            source, StringComparison.Ordinal);
        Assert.Contains(
            "if ($wrapped -and $null -eq $global:LASTEXITCODE -and $errorId -in @(\"GetConsoleMode\", \"SetConsoleMode\", \"RetreiveActiveScreenBufferConsoleHandle\")) {",
            source, StringComparison.Ordinal);
        Assert.Contains("    if ($null -eq $loss) {\n        throw $ErrorRecord\n    }", source, StringComparison.Ordinal);
        // Every native call resets the exit code first and resolves a lost console the same way.
        Assert.Equal(3, Regex.Matches(source, @"(?m)^\s+\$global:LASTEXITCODE = \$null$").Count);
        Assert.Equal(3, Regex.Matches(source, Regex.Escape("= Resolve-ConsoleHostLoss -ErrorRecord $_ -FilePath ")).Count);
        Assert.Contains("$startInfo.CreateNoWindow = $true", source, StringComparison.Ordinal);
        Assert.Contains("return $process.ExitCode", source, StringComparison.Ordinal);
        // ConsoleHost also reads its dead screen buffer while formatting Write-Warning.
        // Once the loss is known, even diagnostic output must bypass that formatter.
        Assert.Contains("function Write-ValidationWarning {", source, StringComparison.Ordinal);
        var warning = source[source.IndexOf("function Write-ValidationWarning {", StringComparison.Ordinal)
            ..source.IndexOf("function Write-ValidationRecord {", StringComparison.Ordinal)];
        Assert.Contains("if ($script:consoleHostLost)", warning, StringComparison.Ordinal);
        Assert.Contains("[Console]::Error.WriteLine(\"WARNING: $Message\")", warning, StringComparison.Ordinal);
        Assert.Contains("else {\n        Write-Warning $Message\n    }", warning, StringComparison.Ordinal);
        Assert.Single(Regex.Matches(source, @"(?m)^\s+Write-Warning ").Cast<Match>());
        Assert.Contains("Write-ValidationWarning \"The console of this run went away", source, StringComparison.Ordinal);
        // No other bare native invocation bypasses the handling.
        Assert.Equal(4, Regex.Matches(source, @"(?m)^\s+& (?:\$FilePath|git) ").Count);
    }

    [Fact]
    public void ValidateWorkflow_UploadsDiagnosticsEvenAfterAFailure_WithoutMaskingIt()
    {
        var source = Text(ValidatePath);
        Assert.DoesNotContain("continue-on-error", WorkflowAndLocalActionText(), StringComparison.Ordinal);
        foreach (var (phase, artifact) in new[] { ("DotNet", "dotnet-validation-diagnostics"), ("Lean", "lean-validation-diagnostics") })
        {
            var run = source.IndexOf($"validate-all.ps1 -Phase {phase}", StringComparison.Ordinal);
            var upload = source.IndexOf($"name: {artifact}", StringComparison.Ordinal);
            Assert.True(run > 0 && upload > run, $"the {artifact} upload must follow the {phase} validation step");
            var step = source[source.LastIndexOf("- name:", upload, StringComparison.Ordinal)..upload];
            Assert.Contains("if: ${{ always() }}", step, StringComparison.Ordinal);
            // Revision pinning is covered by EveryExternalActionUse_IsPinnedToACommentedCommitSha.
            Assert.Contains("uses: actions/upload-artifact@", step, StringComparison.Ordinal);
        }
        Assert.Equal(2, Regex.Matches(source, @"(?m)^          path: artifacts/validation/$").Count);
        Assert.Contains($"bash {LeanInstallPath} 2>&1 | tee artifacts/validation/lean-toolchain-install.log",
            source, StringComparison.Ordinal);
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

    private const string StackSuiteScriptPath = "scripts/validate-stack-suites.ps1";
    private const string StackSuiteJob = "release-stack-suites";
    private const string StackSuiteInvocation = "pwsh -NoProfile -File ./scripts/validate-stack-suites.ps1";

    // The Release stack-suite job's class list. Every class but the in-process async-twin
    // characterization is a SubprocessProbe process-death probe.
    private static readonly string[] StackSuiteClasses =
    [
        "KatLang.Tests.AstStructuralDepthProcessTests",
        "KatLang.Tests.EvaluationLimitsProcessTests",
        "KatLang.Tests.ModelCStackProcessTests",
        "KatLang.Tests.DeferredCompileStackProcessTests",
        "KatLang.Tests.ExposureOpenChainDepthProcessTests",
        "KatLang.Tests.EvaluatorOpenChainStackProcessTests",
        "KatLang.Tests.StructuralNestingStackBackstopProcessTests",
        "KatLang.Tests.ClauseFamilyCompositionDepthProcessTests",
        "KatLang.Tests.AstGraphFuzzProcessTests",
        "KatLang.Tests.WeightedCostCompositionProcessTests",
        "KatLang.Tests.ScopeVisibilityIterativeUpdateTests",
        "KatLang.Tests.ParserExpressionChainDepthTests",
        "KatLang.Tests.LimitConfigurationTransparencyTests",
        "KatLang.Tests.AsyncEvaluation.AsyncStackDepthTests",
    ];

    private static readonly string[] InProcessStackSuiteClasses =
    [
        "KatLang.Tests.AsyncEvaluation.AsyncStackDepthTests",
    ];

    [Theory]
    [InlineData(ValidatePath)]
    [InlineData(ReleasePath)]
    public void ReleaseStackSuiteJob_RunsTheFocusedReleaseScript(string workflow)
    {
        var section = JobSection(Text(workflow), StackSuiteJob);
        Assert.True(section.Length > 0, $"Missing {StackSuiteJob} job in {workflow}.");
        // Stable check name; the matrix leg is the architecture.
        Assert.Single(Regex.Matches(section, @"(?m)^    name: Release stack suites \(\$\{\{ matrix\.arch \}\}\)$").Cast<Match>());
        Assert.Matches(@"(?m)^    runs-on: \$\{\{ matrix\.runner \}\}$", section);
        // x64 only until ARM64 frame sizes are measured; a later ARM64 leg is another include entry.
        Assert.Single(Regex.Matches(section, @"(?m)^          - arch:").Cast<Match>());
        Assert.Matches(@"(?m)^          - arch: x64\n            runner: ubuntu-24.04$", section);
        // Comfortably inside the agreed 60-minute .NET budget.
        Assert.Single(Regex.Matches(section, @"(?m)^    timeout-minutes:").Cast<Match>());
        Assert.Matches(@"(?m)^    timeout-minutes: 30$", section);
        Assert.Single(Regex.Matches(section, Regex.Escape(StackSuiteInvocation)).Cast<Match>());
        Assert.DoesNotContain("validate-all.ps1", section, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(ValidatePath)]
    [InlineData(ReleasePath)]
    public void ReleaseStackSuiteJob_UploadsDiagnosticsEvenAfterAFailure_OutsideTheReleaseBundle(string workflow)
    {
        var section = JobSection(Text(workflow), StackSuiteJob);
        var run = section.IndexOf(StackSuiteInvocation, StringComparison.Ordinal);
        var upload = section.IndexOf("name: stack-suite-diagnostics-${{ matrix.arch }}", StringComparison.Ordinal);
        Assert.True(run > 0 && upload > run, $"the stack-suite diagnostics upload must follow the script in {workflow}");
        var step = section[section.LastIndexOf("- name:", upload, StringComparison.Ordinal)..upload];
        Assert.Contains("if: ${{ always() }}", step, StringComparison.Ordinal);
        Assert.Contains("uses: actions/upload-artifact@", step, StringComparison.Ordinal);
        Assert.Matches(@"(?m)^          path: artifacts/validation/stack-suites-release-\*/$", section);
        // The release collect job downloads every `release-*` artifact into the published bundle.
        Assert.DoesNotMatch(@"(?m)^          name: release-", section);
    }

    [Fact]
    public void ValidateWorkflow_ExposesTheReleaseStackSuiteCheckOnce()
    {
        var source = Text(ValidatePath);
        Assert.Single(Regex.Matches(source, @"(?m)^  release-stack-suites:$").Cast<Match>());
        Assert.Single(Regex.Matches(source, Regex.Escape(StackSuiteInvocation)).Cast<Match>());
    }

    [Fact]
    public void ReleaseWorkflow_GatesEveryBuildOnTheReleaseStackSuites()
    {
        var source = Text(ReleasePath);
        Assert.Matches(@"(?m)^  release-stack-suites:\n    name: [^\n]+\n    needs: verify$", source);
        Assert.Contains("ref: ${{ needs.verify.outputs.source-sha }}", JobSection(source, StackSuiteJob), StringComparison.Ordinal);
        Assert.Matches(@"(?s)  build:.*?needs:\n      - verify\n      - dotnet-validation\n      - lean-validation\n      - release-stack-suites\n", source);
    }

    [Fact]
    public void StackSuiteScript_BuildsAndTestsInRelease()
    {
        var source = Text(StackSuiteScriptPath);
        Assert.Single(Regex.Matches(source, Regex.Escape("& dotnet build $project -c Release -p:UseSharedCompilation=false")).Cast<Match>());
        Assert.Single(Regex.Matches(source, Regex.Escape("& dotnet test $project -c Release -p:UseSharedCompilation=false --no-build")).Cast<Match>());
        Assert.Contains("$project = \"./tests/KatLang.Tests/KatLang.Tests.csproj\"", source, StringComparison.Ordinal);
        Assert.DoesNotMatch(@"(?i)(?:-c|--configuration)\s+Debug", source);
        Assert.Equal(2, Regex.Matches(source, @"(?m)^\s*& dotnet ").Count);
        // The filter is built from the class list, members of each named class only.
        Assert.Contains("$filter = ($stackSuiteClasses | ForEach-Object { \"FullyQualifiedName~$_.\" }) -join \"|\"", source, StringComparison.Ordinal);
        Assert.Contains("--filter $filter", source, StringComparison.Ordinal);
    }

    [Fact]
    public void StackSuiteScript_TreatsZeroExecutedTestsAsAFailure()
    {
        var source = Text(StackSuiteScriptPath);
        var anyGuard = source.IndexOf("if ($results.Count -eq 0) {", StringComparison.Ordinal);
        var classGuard = source.IndexOf("if ($classResults.Count -eq 0) {", StringComparison.Ordinal);
        var missingGuard = source.IndexOf("if ($missingClasses.Count -gt 0) {", StringComparison.Ordinal);
        var passed = source.IndexOf("Write-Host \"Release stack suites passed.\"", StringComparison.Ordinal);
        Assert.True(anyGuard > 0 && classGuard > 0 && missingGuard > 0 && passed > anyGuard && passed > missingGuard,
            "the script must fail when nothing ran or a listed class ran nothing, before it reports a pass");
        Assert.Contains("Release stack suites FAILED: the filter executed no tests.", source, StringComparison.Ordinal);
        // VSTest's exit code is not trusted for discovery: the executed tests are read from the TRX.
        Assert.Contains("Read-TrxResults -Path (Join-Path $resultsDirectory $trxName)", source, StringComparison.Ordinal);
        Assert.Contains("exit $exitCode", source, StringComparison.Ordinal);
        Assert.DoesNotContain("continue-on-error", source, StringComparison.Ordinal);
    }

    [Fact]
    public void StackSuiteScript_KeepsDiagnosticsInAnIgnoredDirectory()
    {
        var source = Text(StackSuiteScriptPath);
        Assert.Contains("$relative = \"artifacts/validation/$name\"", source, StringComparison.Ordinal);
        Assert.Contains("& git check-ignore -q -- \"$relative/stack-suites-build.log\"", source, StringComparison.Ordinal);
        Assert.Contains("\"stack-suites-release-{0:yyyyMMddTHHmmssZ}-{1}\"", source, StringComparison.Ordinal);
        Assert.DoesNotContain("Remove-Item", source, StringComparison.Ordinal);
    }

    [Fact]
    public void StackSuiteScript_NamesRealStackSuites()
    {
        var source = Text(StackSuiteScriptPath);
        var list = Regex.Match(source, @"(?s)\$stackSuiteClasses = @\((?<body>.*?)\n\)");
        Assert.True(list.Success, "the script must declare $stackSuiteClasses");
        var named = Regex.Matches(list.Groups["body"].Value, "\"(?<name>[^\"]+)\"").Select(match => match.Groups["name"].Value).ToArray();
        Assert.Equal(StackSuiteClasses, named);

        var testFiles = Directory.GetFiles(Absolute("tests/KatLang.Tests"), "*.cs", SearchOption.AllDirectories)
            .Where(path => !path.Contains($"{Path.DirectorySeparatorChar}obj{Path.DirectorySeparatorChar}", StringComparison.Ordinal)
                && !path.Contains($"{Path.DirectorySeparatorChar}bin{Path.DirectorySeparatorChar}", StringComparison.Ordinal))
            .ToArray();
        foreach (var name in named)
        {
            var type = typeof(ContinuousIntegrationPolicyTests).Assembly.GetType(name);
            Assert.True(type is not null, $"{name} is not a test class of KatLang.Tests.");
            Assert.True(
                type!.GetMethods().Any(method => method.GetCustomAttributes(typeof(FactAttribute), inherit: true).Length > 0),
                $"{name} declares no test.");
            if (InProcessStackSuiteClasses.Contains(name))
                continue;

            // A process-death probe runs its deep shapes in a SubprocessProbe child and rejects overflow text.
            var declaration = new Regex($@"\bclass {Regex.Escape(type.Name)}\b");
            var file = Assert.Single(testFiles, path => declaration.IsMatch(File.ReadAllText(path)));
            var text = File.ReadAllText(file);
            Assert.Contains("SubprocessProbe.StartInfo(", text, StringComparison.Ordinal);
            Assert.Contains("Stack overflow", text, StringComparison.Ordinal);
        }
    }

    // Test classes that launch a SubprocessProbe child themselves but stay out of the Release
    // stack-suite job, each with the reason. Every other such class must be in StackSuiteClasses.
    private static readonly IReadOnlyDictionary<string, string> ProcessProbeClassesOutsideTheStackSuite =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["KatLang.Tests.RuntimeCallableAliasCorpusTests"] =
                "its child isolates an alias-to-self dispatch regression, which is unbounded recursion and overflows in every configuration, so the Debug phase already catches it; no frame-size frontier is swept",
            ["KatLang.Tests.Infrastructure.SubprocessProbeTests"] =
                "tests the probe launcher itself with trivial fixture children; no stack workload",
            ["KatLang.Tests.Infrastructure.TerminationProbeTests"] =
                "tests the termination (hang) probe harness with trivial fixture children; no stack workload",
        };

    /// <summary>
    /// Every test class that launches a <see cref="SubprocessProbe"/> child is either in
    /// the Release stack-suite job or excluded above with a reason, so a new process-death probe
    /// class cannot be missed silently. Inspect method operands in the compiled assembly, including
    /// async state machines and closures, so formatting, namespaces, partial classes and sibling
    /// classes in one file cannot hide or misattribute a probe. The helpers that wrap the launcher (<c>TerminationProbe</c>,
    /// <c>GcIsolatedAllocation</c>, <c>DagTraversalProbe</c>) are not test classes, and their
    /// callers are termination and allocation probes, not stack probes.
    /// </summary>
    [Fact]
    public void EveryProcessProbeClass_IsInTheReleaseStackSuite_OrExcludedWithAReason()
    {
        var launchTokens = typeof(SubprocessProbe).GetMethods(BindingFlags.Public | BindingFlags.Static)
            .Where(method => method.Name == nameof(SubprocessProbe.StartInfo))
            .Select(method => method.MetadataToken).ToHashSet();
        var testTypes = typeof(ContinuousIntegrationPolicyTests).Assembly.GetTypes()
            .Where(type => type.IsClass && type.GetMethods()
                .Any(method => method.GetCustomAttributes(typeof(FactAttribute), inherit: true).Length > 0))
            .ToArray();
        var found = testTypes.Where(type => LaunchesSubprocessProbe(type, launchTokens))
            .Select(type => type.FullName!).ToHashSet(StringComparer.Ordinal);

        // The scan sees the known probe classes, so a broken pattern cannot pass vacuously.
        Assert.Contains("KatLang.Tests.EvaluatorOpenChainStackProcessTests", found);
        Assert.Contains("KatLang.Tests.AstStructuralDepthProcessTests", found);
        foreach (var name in found)
        {
            Assert.True(StackSuiteClasses.Contains(name) || ProcessProbeClassesOutsideTheStackSuite.ContainsKey(name),
                $"{name} launches a SubprocessProbe child but is neither in {StackSuiteScriptPath} nor excluded with a reason in ProcessProbeClassesOutsideTheStackSuite.");
        }

        foreach (var (name, reason) in ProcessProbeClassesOutsideTheStackSuite)
        {
            Assert.Contains(name, found);
            Assert.DoesNotContain(name, StackSuiteClasses);
            Assert.False(string.IsNullOrWhiteSpace(reason), $"{name} needs a reason to stay out of the stack suite.");
        }
    }

    private static readonly IReadOnlyDictionary<short, OpCode> ProbeInventoryOpCodes = typeof(OpCodes)
        .GetFields(BindingFlags.Public | BindingFlags.Static)
        .Select(field => (OpCode)field.GetValue(null)!).ToDictionary(opCode => opCode.Value);

    private static bool LaunchesSubprocessProbe(Type type, HashSet<int> launchTokens)
    {
        const BindingFlags declared = BindingFlags.DeclaredOnly | BindingFlags.Public | BindingFlags.NonPublic
            | BindingFlags.Static | BindingFlags.Instance;
        foreach (var method in type.GetMethods(declared).Cast<MethodBase>().Concat(type.GetConstructors(declared)))
        {
            if (method.GetMethodBody()?.GetILAsByteArray() is not { } il)
                continue;
            var offset = 0;
            while (offset < il.Length)
            {
                short value = il[offset++];
                if (value == 0xFE)
                    value = (short)(0xFE00 | il[offset++]);
                var operand = ProbeInventoryOpCodes[value].OperandType;
                if (operand == OperandType.InlineMethod && launchTokens.Contains(BitConverter.ToInt32(il, offset)))
                    return true;
                offset += operand switch
                {
                    OperandType.InlineNone => 0,
                    OperandType.ShortInlineBrTarget or OperandType.ShortInlineI or OperandType.ShortInlineVar => 1,
                    OperandType.InlineVar => 2,
                    OperandType.InlineBrTarget or OperandType.InlineField or OperandType.InlineI or OperandType.InlineMethod
                        or OperandType.InlineSig or OperandType.InlineString or OperandType.InlineTok or OperandType.InlineType
                        or OperandType.ShortInlineR => 4,
                    OperandType.InlineI8 or OperandType.InlineR => 8,
                    OperandType.InlineSwitch => 4 + 4 * BitConverter.ToInt32(il, offset),
                    _ => throw new InvalidOperationException($"Unexpected IL operand {operand} in {method}"),
                };
            }
        }

        return type.GetNestedTypes(BindingFlags.Public | BindingFlags.NonPublic)
            .Any(nested => LaunchesSubprocessProbe(nested, launchTokens));
    }

    private const string StandaloneBuildScriptPath = "scripts/build-standalone-tools.ps1";
    private const string StandaloneBuildJob = "standalone-tool-build";
    private const string StandaloneBuildInvocation = "pwsh -NoProfile -File ./scripts/build-standalone-tools.ps1";

    // Every tracked project KatLang.slnx omits; the build-only job compiles each of them.
    private static readonly string[] StandaloneProjects =
    [
        "fuzz/KatLang.ParserFuzz/KatLang.ParserFuzz.csproj",
    ];

    [Fact]
    public void StandaloneToolBuildJob_RunsTheFocusedBuildScript()
    {
        var section = JobSection(Text(ValidatePath), StandaloneBuildJob);
        Assert.True(section.Length > 0, $"Missing {StandaloneBuildJob} job in {ValidatePath}.");
        Assert.Single(Regex.Matches(section, @"(?m)^    name: Standalone tool build$").Cast<Match>());
        Assert.Matches(@"(?m)^    runs-on: ubuntu-24\.04$", section);
        Assert.Single(Regex.Matches(section, @"(?m)^    timeout-minutes:").Cast<Match>());
        Assert.Matches(@"(?m)^    timeout-minutes: 15$", section);
        Assert.Single(Regex.Matches(section, Regex.Escape(StandaloneBuildInvocation)).Cast<Match>());
        Assert.DoesNotContain("validate-all.ps1", section, StringComparison.Ordinal);
        Assert.DoesNotContain("validate-stack-suites.ps1", section, StringComparison.Ordinal);
        Assert.DoesNotContain("needs:", section, StringComparison.Ordinal);
        Assert.DoesNotContain("continue-on-error", section, StringComparison.Ordinal);
    }

    [Fact]
    public void StandaloneToolBuildJob_UploadsDiagnosticsEvenAfterAFailure()
    {
        var section = JobSection(Text(ValidatePath), StandaloneBuildJob);
        var run = section.IndexOf(StandaloneBuildInvocation, StringComparison.Ordinal);
        var upload = section.IndexOf("name: standalone-tool-build-diagnostics", StringComparison.Ordinal);
        Assert.True(run > 0 && upload > run, "the standalone build diagnostics upload must follow the script");
        var step = section[section.LastIndexOf("- name:", upload, StringComparison.Ordinal)..upload];
        Assert.Contains("if: ${{ always() }}", step, StringComparison.Ordinal);
        Assert.Contains("uses: actions/upload-artifact@", step, StringComparison.Ordinal);
        Assert.Matches(@"(?m)^          path: artifacts/validation/standalone-tools-build-\*/$", section);
    }

    [Fact]
    public void ValidateWorkflow_ExposesTheStandaloneToolBuildCheckOnce()
    {
        var source = Text(ValidatePath);
        Assert.Single(Regex.Matches(source, @"(?m)^  standalone-tool-build:$").Cast<Match>());
        Assert.Single(Regex.Matches(WorkflowText(), Regex.Escape(StandaloneBuildInvocation)).Cast<Match>());
    }

    [Fact]
    public void StandaloneToolBuildScript_BuildsEveryListedProjectInDebugAndRelease()
    {
        var source = Text(StandaloneBuildScriptPath);
        Assert.Equal(StandaloneProjects, DeclaredStandaloneProjects(source));
        Assert.Contains("$configurations = @(\"Debug\", \"Release\")", source, StringComparison.Ordinal);
        Assert.Matches(@"(?m)^    foreach \(\$project in \$standaloneProjects\) \{\n        foreach \(\$configuration in \$configurations\) \{$", source);
        // The only native .NET command is a build of the listed project: no tool run, no test, no publish.
        Assert.Single(Regex.Matches(source, Regex.Escape("& dotnet build $project -c $configuration -p:UseSharedCompilation=false *> $log")).Cast<Match>());
        Assert.Single(Regex.Matches(source, @"(?m)^\s*& dotnet ").Cast<Match>());
        Assert.DoesNotMatch(@"(?m)^[^#\n]*\bdotnet\s+(?:test|run|publish)\b", source);
        Assert.DoesNotContain("--no-build", source, StringComparison.Ordinal);
    }

    [Fact]
    public void StandaloneToolBuildScript_FailsOnABuildFailureOrAnInventoryMismatch()
    {
        var source = Text(StandaloneBuildScriptPath);
        var inventory = source.IndexOf("$problems = @(Test-StandaloneInventory)", StringComparison.Ordinal);
        var build = source.IndexOf("& dotnet build $project", StringComparison.Ordinal);
        var passed = source.IndexOf("Write-Host \"Standalone tool build passed:", StringComparison.Ordinal);
        Assert.True(inventory > 0 && build > inventory && passed > build,
            "the inventory check must run before any build, and both before the pass is reported");
        Assert.Contains("$buildExitCode = $LASTEXITCODE", source, StringComparison.Ordinal);
        Assert.Contains("return $buildExitCode", source, StringComparison.Ordinal);
        Assert.Contains("if ($project -notin $inSolution -and $project -notin $standaloneProjects) {", source, StringComparison.Ordinal);
        Assert.Contains("if ($project -in $inSolution) {", source, StringComparison.Ordinal);
        Assert.Contains("& git ls-files -- \"*.csproj\" \"*.fsproj\" \"*.vbproj\"", source, StringComparison.Ordinal);
        Assert.Contains("exit $exitCode", source, StringComparison.Ordinal);
        Assert.DoesNotContain("continue-on-error", source, StringComparison.Ordinal);
    }

    [Fact]
    public void StandaloneToolBuildScript_KeepsDiagnosticsInAnIgnoredDirectory()
    {
        var source = Text(StandaloneBuildScriptPath);
        Assert.Contains("$relative = \"artifacts/validation/$name\"", source, StringComparison.Ordinal);
        Assert.Contains("& git check-ignore -q -- \"$relative/standalone-tools-build.log\"", source, StringComparison.Ordinal);
        Assert.Contains("\"standalone-tools-build-{0:yyyyMMddTHHmmssZ}-{1}\"", source, StringComparison.Ordinal);
        Assert.DoesNotContain("Remove-Item", source, StringComparison.Ordinal);
    }

    [Fact]
    public async Task StandaloneProjects_AreExactlyTheProjectsTheSolutionOmits()
    {
        var root = RepoRoot.Find();
        var inSolution = Regex.Matches(Text("KatLang.slnx"), "Path=\"(?<path>[^\"]+)\"")
            .Select(match => match.Groups["path"].Value.Replace('\\', '/'))
            .ToHashSet(StringComparer.Ordinal);
        // Use the script's tracked inventory: ignored copies may live anywhere, including Backup*/.
        // Filtering after a recursive filesystem scan would also traverse every scratch worktree.
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = root,
            UseShellExecute = false,
            CreateNoWindow = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            StandardOutputEncoding = System.Text.Encoding.UTF8,
        };
        foreach (var argument in new[] { "ls-files", "-z", "--", "*.csproj", "*.fsproj", "*.vbproj" })
            startInfo.ArgumentList.Add(argument);
        using var git = Process.Start(startInfo) ?? throw new InvalidOperationException("Could not start git ls-files.");
        var errorOutput = git.StandardError.ReadToEndAsync();
        var projectOutput = await git.StandardOutput.ReadToEndAsync();
        await git.WaitForExitAsync();
        var errorText = await errorOutput;
        Assert.True(git.ExitCode == 0, $"git ls-files failed: {errorText}");

        var omitted = projectOutput.Split('\0', StringSplitOptions.RemoveEmptyEntries)
            .Where(path => !inSolution.Contains(path))
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(StandaloneProjects.Order(StringComparer.Ordinal), omitted);
        foreach (var project in StandaloneProjects)
            Assert.True(File.Exists(Absolute(project)), $"{project} does not exist.");
    }

    private static string[] DeclaredStandaloneProjects(string source)
    {
        var list = Regex.Match(source, @"(?s)\$standaloneProjects = @\((?<body>.*?)\n\)");
        Assert.True(list.Success, "the script must declare $standaloneProjects");
        return Regex.Matches(list.Groups["body"].Value, "\"(?<name>[^\"]+)\"").Select(match => match.Groups["name"].Value).ToArray();
    }

    private static string JobSection(string source, string job)
    {
        var section = Regex.Match(source, $@"(?ms)^  {Regex.Escape(job)}:\n.*?(?=^  [a-z][a-z-]*:|\z)");
        return section.Success ? section.Value : string.Empty;
    }

    private static string WorkflowText()
        => Text(ValidatePath) + "\n" + Text(ReleasePath);

    private static string WorkflowAndLocalActionText()
        => string.Join("\n", LocalActionPaths.Select(path => Text($"{path}/action.yml")).Prepend(WorkflowText()));

    private static string Text(string relativePath)
        => File.ReadAllText(Absolute(relativePath)).ReplaceLineEndings("\n");

    private static string Absolute(string relativePath)
        => Path.Combine(RepoRoot.Find(), relativePath.Replace('/', Path.DirectorySeparatorChar));
}
