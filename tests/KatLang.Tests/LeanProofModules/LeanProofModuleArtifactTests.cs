using Xunit.Sdk;

namespace KatLang.Tests.LeanProofModules;

/// <summary>
/// Pins the primitives the Lean proof-module generators of this folder are built from
/// (<see cref="LeanProofModuleArtifact"/>): verification that compares and never writes, template filling
/// that cannot leave or invent a placeholder, and rewrites of copied proof text that are refused when they
/// stop applying as reviewed.
/// </summary>
public class LeanProofModuleArtifactTests
{
    private const string Module = "theorem a : True := trivial\ntheorem b : True := trivial\n";

    [Fact]
    public void Verification_PassesOnTheGeneratedText_WhateverTheCheckoutsLineEndings()
    {
        using var scratch = new ScratchModule(Module);
        LeanProofModuleArtifact.Verify(RegenerationFlags.MemberRereadInstances, ScratchModule.DisplayPath, scratch.Path, Module);

        File.WriteAllText(scratch.Path, Module.Replace("\n", "\r\n", StringComparison.Ordinal));
        LeanProofModuleArtifact.Verify(RegenerationFlags.MemberRereadInstances, ScratchModule.DisplayPath, scratch.Path, Module);
    }

    [Fact]
    public void Verification_FailsOnADifference_SaysWhereAndWhatToDo_AndNeverWrites()
    {
        using var scratch = new ScratchModule(Module);
        var flag = RegenerationFlags.MemberRereadInstances;
        var generated = Module.Replace("theorem b", "theorem c", StringComparison.Ordinal);

        var failure = Assert.ThrowsAny<XunitException>(
            () => LeanProofModuleArtifact.Verify(flag, ScratchModule.DisplayPath, scratch.Path, generated));

        Assert.Contains($"{ScratchModule.DisplayPath} differs from its generator's output", failure.Message, StringComparison.Ordinal);
        Assert.Contains("never edited by hand", failure.Message, StringComparison.Ordinal);
        Assert.Contains($"{flag.Variable}=1", failure.Message, StringComparison.Ordinal);
        Assert.Contains($"lake build {LeanProofModuleArtifact.LeanTarget}", failure.Message, StringComparison.Ordinal);
        Assert.Contains("First difference at line 2, column 9", failure.Message, StringComparison.Ordinal);
        Assert.Contains("Generated: theorem c : True := trivial", failure.Message, StringComparison.Ordinal);
        Assert.Contains("Tracked:   theorem b : True := trivial", failure.Message, StringComparison.Ordinal);

        // Verification is observational: the differing module is left exactly as it was, with nothing beside it.
        Assert.Equal(Module, File.ReadAllText(scratch.Path));
        Assert.Equal([scratch.Path], Directory.GetFileSystemEntries(scratch.Directory));
    }

    [Fact]
    public void Verification_FailsOnAMissingModule_AndDoesNotCreateIt()
    {
        using var scratch = new ScratchModule(Module);
        File.Delete(scratch.Path);

        var failure = Assert.ThrowsAny<XunitException>(() => LeanProofModuleArtifact.Verify(
            RegenerationFlags.MemberRereadInstances, ScratchModule.DisplayPath, scratch.Path, Module));

        Assert.Contains($"{ScratchModule.DisplayPath} is missing", failure.Message, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFileSystemEntries(scratch.Directory));
    }

    [Fact]
    public void DescribeFirstDifference_WindowsALongLine_AndReportsAMissingTail()
    {
        var prefix = new string('x', 500);
        var description = LeanProofModuleArtifact.DescribeFirstDifference($"{prefix}A{prefix}\n", $"{prefix}B{prefix}\n");

        Assert.Contains("line 1, column 501", description, StringComparison.Ordinal);
        Assert.Contains("…" + new string('x', 60) + "A" + new string('x', 99) + "…", description, StringComparison.Ordinal);
        Assert.DoesNotContain(prefix, description, StringComparison.Ordinal);

        var truncated = LeanProofModuleArtifact.DescribeFirstDifference("a\nb\nc", "a\nb");
        Assert.Contains("line 3, column 1", truncated, StringComparison.Ordinal);
        Assert.Contains("Generated: c", truncated, StringComparison.Ordinal);
        Assert.Contains("Tracked:   <end of file>", truncated, StringComparison.Ordinal);
    }

    [Fact]
    public void Fill_ReplacesEveryPlaceholderInOnePass_AndLeavesLeanAtSignsAlone()
    {
        // A value that looks like a placeholder is text: it is not filled a second time.
        Assert.Equal(
            "a @B@ and b, then a @B@",
            LeanProofModuleArtifact.Fill("@A@ and @B@, then @A@", ("A", "a @B@"), ("B", "b")));

        const string Lean = "@[simp] theorem t (h : wired@ x) : @id Nat 1 = 1 := rfl -- a@b, A@B, @lower@";
        Assert.Equal(Lean, LeanProofModuleArtifact.Fill(Lean));
    }

    [Fact]
    public void Fill_RefusesATemplateAndATableThatDisagree()
    {
        var missing = Assert.Throws<InvalidOperationException>(() => LeanProofModuleArtifact.Fill("@A@ @B@", ("A", "a")));
        Assert.Contains("@B@", missing.Message, StringComparison.Ordinal);

        var unused = Assert.Throws<InvalidOperationException>(() => LeanProofModuleArtifact.Fill("@A@", ("A", "a"), ("B", "b")));
        Assert.Contains("@B@", unused.Message, StringComparison.Ordinal);

        var twice = Assert.Throws<InvalidOperationException>(() => LeanProofModuleArtifact.Fill("@A@", ("A", "a"), ("A", "b")));
        Assert.Contains("@A@", twice.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ReplaceExactly_AppliesOnlyAtTheReviewedNumberOfSites()
    {
        Assert.Equal("y-y", LeanProofModuleArtifact.ReplaceExactly("x-x", "x", "y", expectedCount: 2));
        Assert.Equal(2, LeanProofModuleArtifact.CountOccurrences("aaaa", "aa"));

        foreach (var text in new[] { "", "x", "x-x-x" })
        {
            var refused = Assert.Throws<InvalidOperationException>(
                () => LeanProofModuleArtifact.ReplaceExactly(text, "x", "y", expectedCount: 2));
            Assert.Contains("Expected 2 occurrence(s)", refused.Message, StringComparison.Ordinal);
        }
    }

    private sealed class ScratchModule : IDisposable
    {
        public const string DisplayPath = "scratch/Module.lean";

        public ScratchModule(string content)
        {
            Directory = System.IO.Path.Combine(
                System.IO.Path.GetTempPath(), "katlang-lean-proof-module", Guid.NewGuid().ToString("N"));
            System.IO.Directory.CreateDirectory(Directory);
            Path = System.IO.Path.Combine(Directory, "Module.lean");
            File.WriteAllText(Path, content);
        }

        public string Directory { get; }
        public string Path { get; }

        public void Dispose()
        {
            try { System.IO.Directory.Delete(Directory, recursive: true); }
            catch (IOException) { }
            catch (UnauthorizedAccessException) { }
        }
    }
}
