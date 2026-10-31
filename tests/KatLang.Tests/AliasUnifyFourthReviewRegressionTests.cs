using static KatLang.Tests.RootPropertyObservations.PropertyObservationTestSupport;

namespace KatLang.Tests;

/// <summary>
/// ALIAS-UNIFY-1 (M4★) fourth independent-review regressions: the exact FU2 witnesses of OD-E over braced
/// structural forwarding carriers — a carrier owns no entry, its bare read is its target's bare view and an explicit
/// call through it is the target's fresh call, re-entrant under the target's outermost owner (Q-37, CACHE-PUB-1) —
/// pinned on the six routes of <see cref="SixRouteAgreement"/>, with the run's ordered root publications
/// (<see cref="RunOptions.ObservePropertyValues"/>; <c>tock()</c> there counts from 0).
/// </summary>
public sealed class AliasUnifyFourthReviewRegressionTests
{
    private static async Task OkAsync(string source, string value, params string[] hostCalls)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(value, outcome.Value);
        Assert.Equal(hostCalls, outcome.HostCalls);
    }

    private static string Publications(string source)
    {
        var log = new TickLog();
        return Describe(Run(source, log.Operations()));
    }

    private static readonly string[] ThreeTicks = ["tock#1", "tock#2", "tock#3"];

    [Fact]
    public async Task ABracedCarrierInsideARecursiveCall_IsItsTargetsFreshCall_UnderTheTargetsOneOwner()
    {
        // FU2 C-RC-F5: A() owns A's entry; B() forwards to the fresh A(), re-entrant under that owner, so A's one
        // publication is the outermost result and the bare B reads it (formerly B owned an entry of its own: (2, 2, 1)).
        const string source = "A = if(tock() < 3, B() + 1, 0)\nB = {\n    A\n}\nA(), A, B";
        await OkAsync(source, "S[2, 2, 2]", ThreeTicks);
        Assert.Equal("A=3#1", Publications(source));
    }

    [Fact]
    public async Task ABracedCarrierReadInsideItsTargetsEvaluation_IsTheTargetsReentrantRead()
    {
        // FU2 C-RC-F5b: the bare B inside A's owning evaluation is A's re-entrant read, never a publication of its own.
        const string source = "A = if(tock() < 3, B + 1, 0)\nB = {\n    A\n}\nA, B";
        await OkAsync(source, "S[2, 2]", ThreeTicks);
        Assert.Equal("A=3#1", Publications(source));
    }

    [Fact]
    public async Task ACarrierOfAHostOperation_CallsItFreshly_AndReadsItsUnpublishedView()
    {
        // FU2 C-RC-F7: B() is tock()'s fresh call; the bare B is tock's bare view, which a host operation never
        // publishes, so it runs again (formerly B's own entry held 1: (1, 1)).
        const string source = "B = {\n    tock\n}\nB(), B";
        await OkAsync(source, "S[1, 2]", "tock#1", "tock#2");
        Assert.Equal(string.Empty, Publications(source));
    }

    [Fact]
    public async Task ACarrierPassedToACallback_IsCalledFreshly_UnderItsTargetsOrigin()
    {
        // FU2 I8: each f() through the carrier is P's fresh call; the first finds P's entry empty and establishes it
        // (CACHE-PUB-1), so the bare B reads that first value.
        const string source = "P = tock()\nB = {\n    P\n}\nCall0(f) = f()\nCall0(B), Call0(B), Call0(P), B";
        await OkAsync(source, "S[1, 2, 3, 1]", ThreeTicks);
        Assert.Equal("P=0#1", Publications(source));
    }

    [Fact]
    public async Task AReferenceAndACarrier_InStringAndInterpolationConsumers_ReadTheTargetsOneEntry()
    {
        // FU2 J8: `.string` and an interpolation hole are VALUE consumers of the target's one entry; the explicit calls
        // stay fresh.
        const string source = "P = tock()\nA = P\nD = {\n    P\n}\nA.string, D.string, \"{A}{D}\", A(), D()";
        await OkAsync(source, "S['1', '1', '11', 2, 3]", ThreeTicks);
        Assert.Equal("P=0#1", Publications(source));
    }

    [Fact]
    public async Task ACalledCycleOfBracedCarriers_IsNoAlias_AndRunsOutOfDepth()
    {
        // FU2 J5: A = { B } / B = { A } is an OD-D cycle, so neither is an alias; calling A recurses until the depth
        // limit, an ordinary terminal error on every route. The limit is set low, so no route meets its host-stack
        // backstop first (where that fires is not promised, Q-09a).
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("A = {\n    B\n}\nB = {\n    A\n}\nA()", limits: new EvaluationLimits { MaxDepth = 12 });
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith(nameof(KatLangErrorCode.EvaluationDepthExceeded), outcome.Errors[0], StringComparison.Ordinal);
    }
}
