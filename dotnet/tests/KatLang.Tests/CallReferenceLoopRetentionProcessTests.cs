using System.Diagnostics;
using System.Globalization;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// The retention pin of call references kept in loop state (NEED-10 and § Call references in
/// <c>docs/design/language-rules/call-by-need.md</c>; documentation, no rule change). A reference retains its
/// plan's captured caller context: the capturing owner's activation with all of its parameter bindings, and every
/// argument cell reachable from it, whose suspensions are never cleared. In the REFERENCE program each round's
/// <c>Cap(Inc(n))</c> is captured in the activation that binds the previous round's reference as <c>r</c>, so every
/// earlier round stays reachable and peak memory grows with the rounds (about 1.2 KiB per round, measured
/// 2026-11-14). That growth is documented, NOT asserted: a future precise-retention change may remove it.
/// <para>The two CONTROLS are asserted to stay flat: the same loop storing the plain value
/// <c>Cap(Inc(n)).Invoke()</c>, and the same loop handing each round's call to a <c>meta</c> parameter that never
/// stores it (<c>G(meta r) = 1</c>). Each program runs in a fresh <see cref="SubprocessProbe"/> child on the
/// default engine (<see cref="KatLangEngine.Run"/>), which reports its peak working set; the parent compares
/// <see cref="FewRounds"/> with four times as many rounds. To measure the reference program with the same child,
/// run <see cref="PeakChild"/> with the variant <c>reference</c>; no test runs it.</para>
/// </summary>
public sealed class CallReferenceLoopRetentionProcessTests(ITestOutputHelper output)
{
    private const string Child = "KATLANG_CALL_REFERENCE_RETENTION_CHILD";
    private const string Variant = "KATLANG_CALL_REFERENCE_RETENTION_VARIANT";
    private const string Rounds = "KATLANG_CALL_REFERENCE_RETENTION_ROUNDS";
    private const string Marker = "KATLANG_CALL_REFERENCE_RETENTION_MARKER";
    private const int FewRounds = 50_000;
    private const int ManyRounds = 4 * FewRounds;
    // The reference program grows by about 175 MiB between the two sizes; the controls by a few MiB.
    private const long AllowedGrowthBytes = 40L * 1024 * 1024;

    /// <summary>The reference program (<c>reference</c>) and its two controls, over <paramref name="rounds"/> rounds.</summary>
    internal static string Program(string variant, int rounds)
    {
        var step = variant switch
        {
            // The reference itself is the loop state: each round's plan retains the round before it.
            "reference" => "Cap(meta r) = r\nInc(y) = y + 1\nStep(n, r) = n + 1, Cap(Inc(n))",
            // Control: the state carries the reference's result, a plain value.
            "stored-value" => "Cap(meta r) = r\nInc(y) = y + 1\nStep(n, r) = n + 1, Cap(Inc(n)).Invoke()",
            // Control: each round's call is captured by a plan that never stores its reference.
            "never-stored" => "G(meta r) = 1\nInc(y) = y + 1\nStep(n, r) = n + 1, G(Inc(n))",
            _ => throw new ArgumentOutOfRangeException(nameof(variant), variant, "Unknown retention variant."),
        };
        return step + "\nS = Step(0, 0).repeat(" + rounds.ToString(CultureInfo.InvariantCulture) + ")\nS[0]";
    }

    [Theory]
    [InlineData("stored-value")]
    [InlineData("never-stored")]
    public async Task Control_PeakWorkingSet_StaysWithinFortyMiBAcrossFourTimesTheRounds(string variant)
    {
        var few = await PeakWorkingSetAsync(variant, FewRounds);
        var many = await PeakWorkingSetAsync(variant, ManyRounds);
        var summary = $"{variant}: peak working set {few / 1048576.0:F1} MiB at {FewRounds} rounds, "
            + $"{many / 1048576.0:F1} MiB at {ManyRounds} rounds";
        output.WriteLine(summary);
        Assert.True(many - few < AllowedGrowthBytes, summary);
    }

    [Fact]
    public void PeakChild()
    {
        if (Environment.GetEnvironmentVariable(Child) != "1")
            return;

        var rounds = int.Parse(Environment.GetEnvironmentVariable(Rounds)!, CultureInfo.InvariantCulture);
        var source = Program(Environment.GetEnvironmentVariable(Variant)!, rounds);
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        // S[0] is the round counter.
        Assert.Equal(rounds.ToString(CultureInfo.InvariantCulture), success.ToDisplayString());

        using var process = Process.GetCurrentProcess();
        process.Refresh();
        File.WriteAllText(
            Environment.GetEnvironmentVariable(Marker)!,
            process.PeakWorkingSet64.ToString(CultureInfo.InvariantCulture));
    }

    private static async Task<long> PeakWorkingSetAsync(string variant, int rounds)
    {
        var marker = Path.Combine(Path.GetTempPath(), $"katlang-call-reference-retention-{Guid.NewGuid():N}.txt");
        var start = SubprocessProbe.StartInfo(typeof(CallReferenceLoopRetentionProcessTests), nameof(PeakChild));
        start.Environment[Child] = "1";
        start.Environment[Variant] = variant;
        start.Environment[Rounds] = rounds.ToString(CultureInfo.InvariantCulture);
        start.Environment[Marker] = marker;
        try
        {
            using var process = Process.Start(start)!;
            var output = process.StandardOutput.ReadToEndAsync();
            var error = process.StandardError.ReadToEndAsync();
            await process.WaitForExitAsync();
            var text = await output + await error;
            Assert.True(process.ExitCode == 0, text);
            Assert.True(File.Exists(marker), text);
            return long.Parse(await File.ReadAllTextAsync(marker), CultureInfo.InvariantCulture);
        }
        finally
        {
            File.Delete(marker);
        }
    }
}
