using System.Text.RegularExpressions;

namespace KatLang.Tests.Infrastructure;

/// <summary>
/// Pins the regeneration discipline for tracked generated artifacts (see
/// <see cref="ArtifactRegeneration"/>): verification never writes, explicit
/// regeneration writes and then fails, every flag is registered, no test reads
/// a flag outside the shared helper, and <c>scripts/validate-all.ps1</c>
/// neutralizes the whole flag namespace before anything can observe it.
/// </summary>
public class ArtifactRegenerationPolicyTests
{
    private static readonly Regex FlagToken = new(
        Regex.Escape(RegenerationFlags.Prefix) + "[A-Za-z0-9_]*",
        RegexOptions.CultureInvariant);

    /// <summary>
    /// The two files that legitimately combine an environment read with the
    /// regeneration vocabulary: the helper (the one sanctioned reader) and this
    /// policy suite (which names both in its scans).
    /// </summary>
    private static readonly string[] SanctionedReaderFiles =
    [
        "tests/KatLang.Tests/Infrastructure/ArtifactRegeneration.cs",
        "tests/KatLang.Tests/Infrastructure/ArtifactRegenerationPolicyTests.cs",
    ];

    private static readonly HashSet<string> ExcludedDirectories = new(StringComparer.OrdinalIgnoreCase)
    {
        ".git", "bin", "obj", ".lake", "artifacts", ".claude", "BenchmarkDotNet.Artifacts",
        "TestResults", "test-results", ".vs", ".idea", "node_modules",
    };

    private static readonly HashSet<string> ScannedExtensions = new(StringComparer.OrdinalIgnoreCase)
    {
        ".cs", ".csproj", ".props", ".targets", ".slnx", ".ps1", ".psm1", ".sh", ".cmd", ".bat",
        ".md", ".txt", ".lean", ".json", ".yml", ".yaml", ".ebnf",
    };

    private static readonly HashSet<string> LiveRegenerationPolicyExtensions = new(StringComparer.OrdinalIgnoreCase)
    {
        ".cs", ".csproj", ".props", ".targets", ".ps1", ".psm1", ".sh", ".cmd", ".bat", ".yml", ".yaml",
    };

    // ── Registry ────────────────────────────────────────────────────────────

    [Fact]
    public void Registry_ListsEveryDeclaredFlag_UnderTheCanonicalPrefix()
    {
        var declared = typeof(RegenerationFlags)
            .GetFields(System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.Static)
            .Where(field => field.FieldType == typeof(RegenerationFlag))
            .Select(field => (RegenerationFlag)field.GetValue(null)!)
            .ToList();

        Assert.NotEmpty(declared);
        Assert.Equal(
            declared.Select(flag => flag.Variable).OrderBy(name => name, StringComparer.Ordinal),
            RegenerationFlags.All.Select(flag => flag.Variable).OrderBy(name => name, StringComparer.Ordinal));
        Assert.Equal(
            RegenerationFlags.All.Count,
            RegenerationFlags.All.Select(flag => flag.Variable).Distinct(StringComparer.Ordinal).Count());

        foreach (var flag in RegenerationFlags.All)
        {
            Assert.StartsWith(RegenerationFlags.Prefix, flag.Variable, StringComparison.Ordinal);
            Assert.Matches("^[A-Z0-9_]+$", flag.Variable[RegenerationFlags.Prefix.Length..]);
            Assert.False(string.IsNullOrWhiteSpace(flag.Regenerates), $"{flag} must say what it regenerates.");
        }
    }

    // ── Opt-in semantics ────────────────────────────────────────────────────

    [Theory]
    [InlineData(null, false)]
    [InlineData("", false)]
    [InlineData("0", false)]
    [InlineData("false", false)]
    [InlineData("true", false)]
    [InlineData("yes", false)]
    [InlineData("01", false)]
    [InlineData(" 1", false)]
    [InlineData("1 ", false)]
    [InlineData("\t1", false)]
    [InlineData("1", true)]
    public void IsRequested_IsTrueOnlyForTheExactOptInValue(string? value, bool expected)
    {
        var flag = RegenerationFlags.All[0];
        var environment = new Dictionary<string, string?>(StringComparer.Ordinal) { [flag.Variable] = value };

        Assert.Equal(expected, ArtifactRegeneration.IsRequested(flag, name => environment.GetValueOrDefault(name)));
    }

    [Fact]
    public void IsRequested_ReadsOnlyTheFlagsOwnCanonicalName()
    {
        var flag = RegenerationFlags.All[0];
        var environment = new Dictionary<string, string?>(StringComparer.Ordinal)
        {
            [flag.Variable.ToLowerInvariant()] = "1",
            [RegenerationFlags.Prefix] = "1",
        };

        // The helper reads the canonical spelling only (Linux environments are
        // case-sensitive); Windows' case-insensitive matching happens in the OS,
        // and validate-all.ps1 clears the namespace case-insensitively for it.
        Assert.False(ArtifactRegeneration.IsRequested(flag, name => environment.GetValueOrDefault(name)));
    }

    // ── The policy, against a scratch path ──────────────────────────────────

    [Fact]
    public void VerificationMode_ComparesOnly_AndNeverWrites()
    {
        using var scratch = new ScratchArtifact();
        var verified = false;

        ArtifactRegeneration.Run(
            regenerationRequested: false,
            RegenerationFlags.All[0],
            scratch.DisplayPath,
            scratch.Path,
            regenerate: () => throw new InvalidOperationException("verification must not generate for writing"),
            verify: () => verified = true,
            afterRegenerating: null);

        Assert.True(verified);
        Assert.False(File.Exists(scratch.Path), "verification mode wrote an artifact");
        Assert.Empty(Directory.EnumerateFileSystemEntries(scratch.Directory));
    }

    [Fact]
    public void RegenerationMode_WritesTheArtifact_ThenFailsByDesign()
    {
        using var scratch = new ScratchArtifact();
        var flag = RegenerationFlags.All[0];

        var failure = Assert.Throws<ArtifactRegeneratedException>(() => ArtifactRegeneration.Run(
            regenerationRequested: true,
            flag,
            scratch.DisplayPath,
            scratch.Path,
            regenerate: () => "generated\n",
            verify: () => throw new InvalidOperationException("regeneration must not fall through to verification"),
            afterRegenerating: "run `lake build Something`"));

        Assert.Equal("generated\n", File.ReadAllText(scratch.Path));
        Assert.Same(flag, failure.Flag);
        Assert.Equal(scratch.Path, failure.ArtifactPath);

        // Actionable: artifact, variable, review, the extra step, clear, rerun.
        Assert.Contains(scratch.DisplayPath, failure.Message, StringComparison.Ordinal);
        Assert.Contains($"{flag.Variable}=1", failure.Message, StringComparison.Ordinal);
        Assert.Contains("(created)", failure.Message, StringComparison.Ordinal);
        Assert.Contains("fails by design", failure.Message, StringComparison.Ordinal);
        Assert.Contains($"git diff -- {scratch.DisplayPath}", failure.Message, StringComparison.Ordinal);
        Assert.Contains("run `lake build Something`", failure.Message, StringComparison.Ordinal);
        Assert.Contains($"Remove-Item Env:{flag.Variable}", failure.Message, StringComparison.Ordinal);
        Assert.Contains($"unset {flag.Variable}", failure.Message, StringComparison.Ordinal);
        Assert.Contains("rerun the normal verification", failure.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("generated\n", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RegenerationMode_ReplacesStaleContentBeforeFailing()
    {
        using var scratch = new ScratchArtifact();
        File.WriteAllText(scratch.Path, "stale\n");

        var failure = Assert.Throws<ArtifactRegeneratedException>(() => ArtifactRegeneration.Run(
            regenerationRequested: true,
            RegenerationFlags.All[0],
            scratch.DisplayPath,
            scratch.Path,
            regenerate: () => "fresh\n",
            verify: () => throw new InvalidOperationException("unreachable"),
            afterRegenerating: null));

        // The write precedes the failure: the intentional failure is useless if
        // the artifact was not updated first.
        Assert.Equal("fresh\n", File.ReadAllText(scratch.Path));
        Assert.Contains("(updated)", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RegenerationMode_FailsEvenWhenTheArtifactWasAlreadyUpToDate()
    {
        using var scratch = new ScratchArtifact();
        File.WriteAllText(scratch.Path, "same\n");

        // Requested regeneration IS the meaning of the command; a run that
        // happened to produce identical bytes must still not report success, or
        // the mode of the run would be ambiguous from its result.
        var failure = Assert.Throws<ArtifactRegeneratedException>(() => ArtifactRegeneration.Run(
            regenerationRequested: true,
            RegenerationFlags.All[0],
            scratch.DisplayPath,
            scratch.Path,
            regenerate: () => "same\n",
            verify: () => throw new InvalidOperationException("unreachable"),
            afterRegenerating: null));

        Assert.Equal("same\n", File.ReadAllText(scratch.Path));
        Assert.Contains("(rewritten with identical content)", failure.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("old\r\nlines\r\n", "new\nlines\n", "new\r\nlines\r\n")]
    [InlineData("old\nlines\n", "new\r\nlines\r\n", "new\nlines\n")]
    public void RegenerationMode_PreservesAnExistingArtifactsLineEndingConvention(
        string previous, string generated, string expected)
    {
        using var scratch = new ScratchArtifact();
        File.WriteAllText(scratch.Path, previous);

        Assert.Throws<ArtifactRegeneratedException>(() => ArtifactRegeneration.Run(
            regenerationRequested: true,
            RegenerationFlags.All[0],
            scratch.DisplayPath,
            scratch.Path,
            regenerate: () => generated,
            verify: () => throw new InvalidOperationException("unreachable"),
            afterRegenerating: null));

        Assert.Equal(expected, File.ReadAllText(scratch.Path));
    }

    [Fact]
    public void RegenerationMode_LeavesNoStagingFileBehind_EvenWhenTheWriteFails()
    {
        using var scratch = new ScratchArtifact();

        Assert.Throws<ArtifactRegeneratedException>(() => ArtifactRegeneration.Run(
            regenerationRequested: true,
            RegenerationFlags.All[0],
            scratch.DisplayPath,
            scratch.Path,
            regenerate: () => "content\n",
            verify: () => throw new InvalidOperationException("unreachable"),
            afterRegenerating: null));
        Assert.Equal([scratch.Path], Directory.GetFileSystemEntries(scratch.Directory));

        // A failed move (the artifact path is a directory here) must propagate
        // the real I/O failure rather than the intentional success-after-write
        // exception, and must not strand its staging file. Windows reports the
        // refused move as UnauthorizedAccessException, Unix as IOException.
        var blocked = System.IO.Path.Combine(scratch.Directory, "blocked");
        Directory.CreateDirectory(blocked);
        var refused = Record.Exception(() => ArtifactRegeneration.Run(
            regenerationRequested: true,
            RegenerationFlags.All[0],
            "scratch/blocked",
            blocked,
            regenerate: () => "content\n",
            verify: () => throw new InvalidOperationException("unreachable"),
            afterRegenerating: null));
        Assert.True(refused is IOException or UnauthorizedAccessException,
            $"expected the move onto a directory to be refused, got {refused?.GetType().Name ?? "no exception"}");
        Assert.IsNotType<ArtifactRegeneratedException>(refused);
        Assert.Equal(
            new[] { blocked, scratch.Path }.OrderBy(p => p, StringComparer.Ordinal),
            Directory.GetFileSystemEntries(scratch.Directory).OrderBy(p => p, StringComparer.Ordinal));
    }

    [Fact]
    public void RegenerationMode_DoesNotWrite_WhenGenerationItselfFails()
    {
        using var scratch = new ScratchArtifact();
        File.WriteAllText(scratch.Path, "previous\n");

        Assert.Throws<InvalidOperationException>(() => ArtifactRegeneration.Run(
            regenerationRequested: true,
            RegenerationFlags.All[0],
            scratch.DisplayPath,
            scratch.Path,
            regenerate: () => throw new InvalidOperationException("generator bug"),
            verify: () => throw new InvalidOperationException("unreachable"),
            afterRegenerating: null));

        Assert.Equal("previous\n", File.ReadAllText(scratch.Path));
    }

    // ── Architecture: no flag escapes the discipline ────────────────────────

    [Fact]
    public void EveryRegenerationVariableInTheRepository_IsRegistered()
    {
        var registered = RegenerationFlags.All.Select(flag => flag.Variable).ToHashSet(StringComparer.Ordinal);
        var offenders = new List<string>();

        foreach (var file in EnumerateRepositoryTextFiles().Where(IsLiveRegenerationPolicyFile))
        {
            foreach (var token in UnregisteredTokens(File.ReadAllText(file), registered))
                offenders.Add($"{Relative(file)}: {token}");
        }

        Assert.True(offenders.Count == 0,
            "Unregistered regeneration variables (register them in RegenerationFlags so the write-then-fail " +
            "contract and validate-all neutralization govern them):\n" + string.Join("\n", offenders.Distinct()));
    }

    [Fact]
    public void UnregisteredTokenScan_DetectsAnUnknownFlag_AndAcceptsTheBarePrefix()
    {
        var registered = RegenerationFlags.All.Select(flag => flag.Variable).ToHashSet(StringComparer.Ordinal);
        // Assembled at runtime so the repository scan above never sees an
        // unregistered token in the source of this file.
        var unknown = RegenerationFlags.Prefix + string.Concat("NOT_", "REGISTERED");

        var text = $"{RegenerationFlags.All[0]} then {RegenerationFlags.Prefix}* then {unknown} and {RegenerationFlags.Prefix}";

        Assert.Equal([unknown], UnregisteredTokens(text, registered));
    }

    [Fact]
    public void RegistryScan_TreatsDocumentationExamplesAsDocumentation_NotLiveConsumers()
    {
        Assert.True(IsLiveRegenerationPolicyFile("tests/ArtifactTest.cs"));
        Assert.True(IsLiveRegenerationPolicyFile("scripts/regenerate.ps1"));
        Assert.True(IsLiveRegenerationPolicyFile(".github/workflows/validate.yml"));
        Assert.False(IsLiveRegenerationPolicyFile("docs/example.md"));
        Assert.False(IsLiveRegenerationPolicyFile("generated-prompt.txt"));
        Assert.False(IsLiveRegenerationPolicyFile("lean/Generated.lean"));
    }

    [Fact]
    public void NoTestReadsARegenerationFlag_OutsideTheSharedHelper()
    {
        var root = RepoRoot.Find();
        var sanctioned = SanctionedReaderFiles
            .Select(relative => System.IO.Path.GetFullPath(System.IO.Path.Combine(root, relative)))
            .ToHashSet(StringComparer.OrdinalIgnoreCase);
        foreach (var file in sanctioned)
            Assert.True(File.Exists(file), $"sanctioned reader {file} does not exist");

        var offenders = new List<string>();
        foreach (var file in EnumerateRepositoryTextFiles(System.IO.Path.Combine(root, "tests"), ".cs"))
        {
            if (sanctioned.Contains(System.IO.Path.GetFullPath(file)))
                continue;

            var text = File.ReadAllText(file);
            var readsEnvironment = text.Contains("GetEnvironmentVariable", StringComparison.Ordinal);
            var namesAFlag = text.Contains(RegenerationFlags.Prefix, StringComparison.Ordinal)
                || text.Contains(nameof(RegenerationFlags), StringComparison.Ordinal);
            if (readsEnvironment && namesAFlag)
                offenders.Add(Relative(file));
        }

        Assert.True(offenders.Count == 0,
            "These test files read the environment AND name a regeneration flag; a test must obtain " +
            "regeneration mode only through ArtifactRegeneration.VerifyOrRegenerate (write, then fail):\n" +
            string.Join("\n", offenders));
    }

    [Fact]
    public void ValidateAll_NeutralizesTheWholeRegenerationNamespace_BeforeAnyBuildOrTest()
    {
        var script = File.ReadAllText(System.IO.Path.Combine(RepoRoot.Find(), "scripts", "validate-all.ps1"))
            .ReplaceLineEndings("\n");

        var prefixAssignment = $"$regenerationFlagPrefix = \"{RegenerationFlags.Prefix}\"";
        const string PrefixMatch = ".StartsWith($regenerationFlagPrefix, [System.StringComparison]::OrdinalIgnoreCase)";
        const string Removal = "Remove-Item -LiteralPath \"Env:$($entry.Name)\"";
        const string FirstDotnet = "Invoke-Native -FilePath \"dotnet\"";

        Assert.Contains(prefixAssignment, script, StringComparison.Ordinal);
        Assert.Contains(PrefixMatch, script, StringComparison.Ordinal);
        Assert.Contains(Removal, script, StringComparison.Ordinal);

        var neutralization = script.IndexOf(prefixAssignment, StringComparison.Ordinal);
        var removal = script.IndexOf(Removal, StringComparison.Ordinal);
        var firstBuild = script.IndexOf(FirstDotnet, StringComparison.Ordinal);
        Assert.True(firstBuild > removal && removal > neutralization,
            "validate-all.ps1 must remove every KATLANG_REGENERATE_* variable before its first dotnet invocation.");
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    internal static IReadOnlyList<string> UnregisteredTokens(string text, IReadOnlySet<string> registered)
        => FlagToken.Matches(text)
            .Select(match => match.Value)
            .Where(token => token.Length > RegenerationFlags.Prefix.Length && !registered.Contains(token))
            .Distinct(StringComparer.Ordinal)
            .ToList();

    internal static bool IsLiveRegenerationPolicyFile(string file)
        => LiveRegenerationPolicyExtensions.Contains(System.IO.Path.GetExtension(file));

    internal static IEnumerable<string> EnumerateRepositoryTextFiles(string? root = null, string? onlyExtension = null)
    {
        var pending = new Stack<string>();
        pending.Push(root ?? RepoRoot.Find());
        while (pending.Count > 0)
        {
            var directory = pending.Pop();
            foreach (var child in Directory.EnumerateDirectories(directory))
            {
                if (!ExcludedDirectories.Contains(System.IO.Path.GetFileName(child)))
                    pending.Push(child);
            }

            foreach (var file in Directory.EnumerateFiles(directory))
            {
                var extension = System.IO.Path.GetExtension(file);
                var selected = onlyExtension is null
                    ? ScannedExtensions.Contains(extension)
                    : string.Equals(extension, onlyExtension, StringComparison.OrdinalIgnoreCase);
                if (selected)
                    yield return file;
            }
        }
    }

    private static string Relative(string file)
        => System.IO.Path.GetRelativePath(RepoRoot.Find(), file).Replace('\\', '/');

    private sealed class ScratchArtifact : IDisposable
    {
        public ScratchArtifact()
        {
            Directory = System.IO.Path.Combine(
                System.IO.Path.GetTempPath(), "katlang-regeneration-policy", Guid.NewGuid().ToString("N"));
            System.IO.Directory.CreateDirectory(Directory);
            Path = System.IO.Path.Combine(Directory, "artifact.txt");
        }

        public string Directory { get; }
        public string Path { get; }
        public string DisplayPath => "scratch/artifact.txt";

        public void Dispose()
        {
            try { System.IO.Directory.Delete(Directory, recursive: true); }
            catch (IOException) { }
            catch (UnauthorizedAccessException) { }
        }
    }
}
