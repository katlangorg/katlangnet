using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests.RootOutputRowCounts;

/// <summary>
/// Shared helpers of the <see cref="RunResult.Success.OutputRowCounts"/> suites: the contract every
/// success must satisfy, the walk a host performs over the partition, and the host operation that
/// forces (and, when called, really suspends) the async twin.
/// </summary>
internal static class OutputRowCountsTestSupport
{
    internal static readonly IReadOnlyList<(string Id, string Source)> CorpusSources = BuildCorpusSources();

    private static IReadOnlyList<(string, string)> BuildCorpusSources()
    {
        var sources = new List<(string, string)>();
        foreach (var specCase in LanguageSpecCorpus.AllCases())
        {
            sources.Add(("spec:" + specCase.Id, specCase.Source));
            for (var i = 0; i < specCase.Probes.Count; i++)
                sources.Add(($"spec:{specCase.Id}#probe{i}", specCase.Probes[i].Probe));
        }

        foreach (var explorerCase in SemanticExplorerCorpus.AllCases())
            sources.Add(("explorer:" + explorerCase.Id, explorerCase.Source));
        return sources;
    }

    /// <summary>
    /// The contract of the member on one success: one entry per row of the elaborated root's
    /// output, no negative entry, a sum equal to the presented output rows, and exactly one entry
    /// for every row that is not a spread.
    /// </summary>
    internal static void AssertPartition(RunResult.Success success)
    {
        var problem = PartitionProblem(success);
        Assert.True(problem is null, problem);
    }

    /// <summary>What <see cref="AssertPartition"/> would report, or null when the contract holds.</summary>
    internal static string? PartitionProblem(RunResult.Success success)
    {
        var counts = success.OutputRowCounts;
        if (counts is null)
            return "OutputRowCounts is null";

        var rows = success.Root.Output;
        if (counts.Count != rows.Count)
            return $"{counts.Count} counts for {rows.Count} root output rows";

        long sum = 0;
        for (var row = 0; row < counts.Count; row++)
        {
            if (counts[row] < 0)
                return $"row {row} has the negative count {counts[row]}";
            if (rows[row] is not Expr.SequenceSpread && counts[row] != 1)
                return $"the non-spread row {row} has count {counts[row]}, not 1";
            sum += counts[row];
        }

        return sum == success.OutputRows.Count
            ? null
            : $"the counts [{string.Join(", ", counts)}] sum to {sum} for {success.OutputRows.Count} output rows";
    }

    /// <summary>
    /// The entries of <see cref="RunResult.Success.OutputRows"/> each root row produced, obtained
    /// the way a host labels values: row <c>i</c> takes the next <c>OutputRowCounts[i]</c> entries.
    /// </summary>
    internal static IReadOnlyList<IReadOnlyList<Result>> Slices(RunResult.Success success)
    {
        var slices = new List<IReadOnlyList<Result>>();
        var outputRows = success.OutputRows;
        var next = 0;
        foreach (var count in success.OutputRowCounts)
        {
            var slice = new Result[count];
            for (var i = 0; i < count; i++)
                slice[i] = outputRows[next + i];
            slices.Add(slice);
            next += count;
        }

        Assert.Equal(outputRows.Count, next);
        return slices;
    }

    /// <summary><c>spread</c> or <c>plain</c> per row of the elaborated root's output, comma-separated.</summary>
    internal static string RowKinds(Algorithm.User root)
        => string.Join(", ", root.Output.Select(static row => row is Expr.SequenceSpread ? "spread" : "plain"));

    /// <summary>The numbers <paramref name="first"/>, <paramref name="first"/> + 1, … as atoms.</summary>
    internal static Result[] Atoms(int first, int count)
    {
        var atoms = new Result[count];
        for (var i = 0; i < count; i++)
            atoms[i] = new Result.Atom(first + i);
        return atoms;
    }

    /// <summary>
    /// A zero-argument asynchronous host operation <c>pause()</c> returning 0. Configuring it makes
    /// <see cref="KatLangEngine.RunAsync"/> evaluate on the async twin whether or not the program
    /// calls it; a call really suspends the run (<see cref="Task.Yield"/>) and is counted.
    /// </summary>
    internal sealed class Pause
    {
        private int _calls;

        public int Calls => Volatile.Read(ref _calls);

        public HostOperations Operations()
            => HostOperations.Create(HostOperation.CreateAsync("pause", async (_, _) =>
            {
                Interlocked.Increment(ref _calls);
                await Task.Yield();
                return new Result.Atom(0);
            }));
    }
}
