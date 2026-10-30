using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// ALIAS-UNIFY-1-IMPL R12 through a GENUINELY SUSPENDED run: an asynchronous host operation
/// <c>gate(x)</c> held on an externally completed gate, so each test asserts what has — and has not —
/// happened while the run is incomplete, then releases it. Pins the group-aware NEED-04 anchor-first
/// schedule (a pending reference's VALUE is not demanded while its value-only anchor is suspended), OD-E
/// publication through a carrier and a reference (the explicit call publishes under the TARGET's entry,
/// which later bare reads reuse) and the runtime target lifetime (a computed target is established once,
/// even when establishing it suspends).
/// </summary>
public sealed class AliasUnifyHeldGateTests
{
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    /// <summary>The held host operation plus a shared, ordered event log (<c>trace</c> writes to it too).</summary>
    private sealed class Fixture
    {
        private readonly TaskCompletionSource _release = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private readonly TaskCompletionSource _reached = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private readonly List<string> _log = [];
        private int _gateEntries;
        private int _ticks;

        public int GateEntries => Volatile.Read(ref _gateEntries);

        public Task Reached => _reached.Task;

        public void Release() => _release.TrySetResult();

        public string[] Log()
        {
            lock (_log) return [.. _log];
        }

        private void Record(string entry)
        {
            lock (_log) _log.Add(entry);
        }

        public RunOptions Options() => new()
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("gate", async (args, _) =>
                {
                    Interlocked.Increment(ref _gateEntries);
                    Record("gate " + Format(args[0]));
                    _reached.TrySetResult();
                    await _release.Task;
                    return args[0];
                }, "x"),
                HostOperation.Create("trace", (args, _) =>
                {
                    Record("trace " + Format(args[0]));
                    return args[0];
                }, "x"),
                HostOperation.Create("tick", (_, _) => new Result.Atom(Interlocked.Increment(ref _ticks)))),
        };

        private static string Format(Result value) => value is Result.Atom atom ? atom.Value.ToString() : value.ToString()!;
    }

    private static async Task<RunResult> RunHeld(Fixture fixture, string source, params string[] logWhileSuspended)
    {
        var options = fixture.Options();
        await SourceProvenance.ParseValidAsync(source, options);
        var run = KatLangEngine.RunAsync(source, options);
        await fixture.Reached.WaitAsync(WaitLimit);
        Assert.False(run.IsCompleted);
        Assert.Equal(logWhileSuspended, fixture.Log());
        fixture.Release();
        return await run.WaitAsync(WaitLimit);
    }

    private static void AssertValues(RunResult result, params int[] expected)
    {
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(expected.Select(static n => (Decimal128)n).ToArray(), success.Atoms.ToArray());
    }

    // ── NEED-04: the anchor is demanded first; the pending reference waits ──

    [Fact]
    public async Task APendingReference_IsNotDemandedWhileItsValueAnchorIsSuspended()
    {
        var fixture = new Fixture();
        var result = await RunHeld(fixture, "A = trace(10) - 3\nSame(x, x) = 0\nSame(A, gate(7))", "gate 7");
        AssertValues(result, 0);
        Assert.Equal(["gate 7", "trace 10"], fixture.Log());
    }

    [Fact]
    public async Task APendingReferencesOwnValue_IsCheckedAfterTheAnchorResumes()
    {
        var fixture = new Fixture();
        var result = await RunHeld(fixture, "A = trace(10) - 2\nSame(x, x) = 0\nSame(A, gate(7))", "gate 7");
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Equal(KatLangErrorCode.ArityMismatch, Assert.Single(failure.Errors).Code);
        Assert.Equal(["gate 7", "trace 10"], fixture.Log());
    }

    // ── OD-E: an explicit call through an alias publishes under the TARGET ──

    [Theory]
    [InlineData("B = { P }\nB(), B, P")]
    [InlineData("B = P\nB(), B, P")]
    public async Task ASuspendedCallThroughAnAlias_EstablishesTheTargetsEntry(string rows)
    {
        var fixture = new Fixture();
        var result = await RunHeld(fixture, "P = gate(tick())\n" + rows, "gate 1");
        AssertValues(result, 1, 1, 1);
        Assert.Equal(1, fixture.GateEntries);
        Assert.Equal(["gate 1"], fixture.Log());
    }

    // ── Runtime lifetime: a computed target is established once, even across a suspension ──

    [Fact]
    public async Task ASuspendedComputedTarget_IsEstablishedOnce_AndCalledFreshly()
    {
        var fixture = new Fixture();
        const string source =
            "Capture(meta op) = op\n" +
            "Z(y) = tick()\n" +
            "Mk(n) = if(gate(n) == n, Capture(Z(n)), 0)\n" +
            "A = Mk(5).Algorithm\n" +
            "A(1), A(2), A(3)";
        var result = await RunHeld(fixture, source, "gate 5");
        AssertValues(result, 1, 2, 3);
        Assert.Equal(1, fixture.GateEntries);
    }
}
