namespace KatLang.Tests.RootPropertyObservations;

/// <summary>
/// Shared helpers of the IV-1/IV-2 property-observation suites: legal-source engine runs with
/// observation on, and a compact rendering of a snapshot (<c>Name=value#emitted</c>, in
/// publication order) that renders every available value through the public
/// <see cref="RunResult.RenderPropertyValue"/> helper.
/// </summary>
internal static class PropertyObservationTestSupport
{
    /// <summary>A counting <c>tick()</c> host operation returning 0, 1, 2, … and logging each call.</summary>
    internal sealed class TickLog
    {
        private int _next;
        private readonly object _gate = new();

        public List<string> Calls { get; } = [];

        public HostOperations Operations(bool suspending = false)
            => HostOperations.Create(
                suspending
                    ? HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return Tick(); })
                    : HostOperation.Create("tick", (_, _) => Tick()),
                suspending
                    ? HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return Trace(args[0]); }, "x")
                    : HostOperation.Create("trace", (args, _) => Trace(args[0]), "x"));

        private Result Tick()
        {
            lock (_gate)
            {
                Calls.Add("tick:" + _next);
                return new Result.Atom(_next++);
            }
        }

        private Result Trace(Result value)
        {
            lock (_gate)
                Calls.Add("trace:" + value.AsNum());
            return value;
        }
    }

    /// <summary>Asserts <paramref name="source"/> is legal (with the given host operations) and runs it with observation on.</summary>
    internal static RunResult Run(string source, HostOperations? operations = null, long? randomSeed = null)
    {
        AssertLegal(source, operations);
        return KatLangEngine.Run(source, Options(observe: true, operations, randomSeed));
    }

    internal static Task<RunResult> RunAsync(string source, HostOperations? operations = null, long? randomSeed = null)
    {
        AssertLegal(source, operations);
        return KatLangEngine.RunAsync(source, Options(observe: true, operations, randomSeed));
    }

    internal static RunOptions Options(bool observe, HostOperations? operations = null, long? randomSeed = null)
        => new() { ObservePropertyValues = observe, HostOperations = operations, RandomSeed = randomSeed };

    internal static void AssertLegal(string source, HostOperations? operations = null)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(
            parsed.HasErrors,
            "test source must parse cleanly:\n" + string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
    }

    /// <summary><c>Name=text#emitted</c> per observation, <c>Name=&lt;withheld&gt;#emitted</c> when withheld.</summary>
    internal static string Describe(RunResult result)
    {
        var observations = result.PropertyObservations;
        Assert.NotNull(observations);
        return string.Join("; ", observations.Select(o => o.Status == PropertyValueStatus.Available
            ? $"{o.Name}={result.RenderPropertyValue(o).Text}#{o.EmittedCount}"
            : $"{o.Name}=<withheld>#{o.EmittedCount}"));
    }

    /// <summary>
    /// The structural outcome of a run, comparable ACROSS runs (record equality of two runs'
    /// results compares their payload lists by reference): variant, bounded display text, and
    /// structured error codes and spans.
    /// </summary>
    internal static string Outcome(RunResult result)
        => result.GetType().Name + " | " + result.ToDisplayString() + " | " + string.Join(", ", result switch
        {
            RunResult.EvalFailure failure => failure.Errors.Select(static e => $"{e.Code}@{e.Span}"),
            RunResult.ParseFailure failure => failure.Errors.Select(static e => $"{e.Code}@{e.Span}"),
            RunResult.NoProgramOutput noOutput => [$"{noOutput.Diagnostic.Code}@{noOutput.Diagnostic.Span}"],
            _ => [],
        });

    internal static PropertyValueObservation Single(RunResult result, string name)
        => Assert.Single(result.PropertyObservations!, o => o.Name == name);
}
