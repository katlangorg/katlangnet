using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Publication through runtime-target aliases under M4★ (ALIAS-UNIFY-1, OD-E and the runtime target
/// lifetime, superseding the CACHE-PUB-1 D4 extension): an alias owns NO zero-argument entry. A runtime
/// alias's binding cell is established once per declaring activation; a VALUE-ONLY target (its row
/// projects no callable identity) answers a zero-supply call with that cell's VALUE — never a rerun —
/// and is no callable identity when passed on; a callable target is invoked FRESHLY and publishes under
/// the TARGET's own origin (Q-37 outermost ownership per key), which a later bare read of the alias then
/// reads. Every case agrees on all six routes.
/// </summary>
public class RuntimeAliasPublicationTests
{
    private const string ValueOnly =
        "Capture(meta c) = c\nCall0(f) = f()\nForward(f) = Call0(f)\nG(o) = tick()\n"
        + "Use(b) = {\n A = b.G\n B = A\n R = Capture(A())\n";

    [Theory]
    [InlineData("A(), A, A(), A", "S[1, 1, 1, 1]")]
    [InlineData("A([]*), A", "S[1, 1]")]
    [InlineData("R.Invoke(), A, R.Invoke(), A", "S[1, 1, 1, 1]")]
    [InlineData("B(), B, A, B(), B", "S[1, 1, 1, 1, 1]")]
    public async Task ValueOnlyTargets_AnswerZeroSupplyCallsWithTheirBindingCell(string rows, string expected)
        => await AssertRoutes(ValueOnly + rows + "\n}\nUse(5)", expected, 1);

    [Theory]
    [InlineData("Call0(A), A")]
    [InlineData("Forward(A), A")]
    [InlineData("R.Algorithm(), A")]
    [InlineData("Call0(R.Algorithm), A")]
    public async Task ValueOnlyTargets_AreNoCallableIdentityWhenPassedOn(string rows)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(ValueOnly + rows + "\n}\nUse(5)");
        Assert.Equal("err", outcome.Kind);
        Assert.Contains("NotAnAlgorithm", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Empty(outcome.HostCalls);
    }

    [Fact]
    public async Task LocalBindingCells_BelongToTheirDeclaringActivation()
        => await AssertRoutes(
            "G(o) = o * 100 + tick()\nUse(b) = {\n A = b.G\n A(), A, A(), A\n}\nUse(1), Use(2), Use(1)",
            "S[S[101, 101, 101, 101], S[202, 202, 202, 202], S[103, 103, 103, 103]]", 3);

    [Fact]
    public async Task SiblingAliases_KeepSeparateBindingCells()
        => await AssertRoutes(
            "G(o) = o * 100 + tick()\nUse(b) = {\n A = b.G\n B = b.G\n A(), B, A, B(), B\n}\nUse(1)",
            "S[101, 102, 101, 102, 102]", 2);

    [Fact]
    public async Task StructuralMemberAlias_EstablishesItsTargetOnce()
        => await AssertRoutes(
            "Capture(meta c) = c\nZ = 9\nMk(n) = if(tick() > 0, Capture(Z()), 0)\n"
            + "Box = { public A = Mk(5).Algorithm }\nBox.A(), Box.A, Box.A(), Box.A",
            "S[9, 9, 9, 9]", 1);

    [Theory]
    [InlineData("Use(f) = {\n A = f\n A(), A\n}\nUse(Only)", "S[1, 1]", 1)]
    [InlineData("R = Capture(Only())\nA = R.Algorithm\nA(), Only", "S[1, 1]", 1)]
    [InlineData("R = Capture(Only())\nA = R.Algorithm\nA(), A, A(), A", "S[1, 1, 2, 1]", 2)]
    public async Task ParameterizedRuntimeTargets_PublishUnderTheirTarget(string body, string expected, int ticks)
        => await AssertRoutes("Capture(meta c) = c\nOnly(*xs) = tick()\n" + body, expected, ticks);

    [Fact]
    public async Task TerminalAlias_PublishesUnderItsZeroParameterTarget()
        => await AssertRoutes(
            "Capture(meta c) = c\nZ = tick()\nMk(n) = if(n == n, Capture(Z()), 0)\nA = Mk(5).Algorithm\nA(), Z(), A, Z",
            "S[1, 2, 1, 1]", 2);

    [Fact]
    public async Task ReentrantCallsThroughAReference_PublishTheOuterOwnersResult()
        => await AssertRoutes(
            "Use(b) = {\n Z = if(tick() < 3, A() + 1, 0)\n A = Z\n A(), A\n}\nUse(5)",
            "S[2, 2]", 3);

    [Fact]
    public async Task AValueOnlyTargetReenteringItsOwnBindingCell_IsADemandCycle()
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(
            "Use(b) = {\n G(o) = if(tick() < 3, A() + 1, 0)\n A = b.G\n A(), A\n}\nUse(5)");
        Assert.Equal("err", outcome.Kind);
        Assert.Contains("DemandCycle", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Equal(["tick#1"], outcome.HostCalls);
    }

    [Fact]
    public async Task ReentrantSuccessUnderFailedOwner_PublishesNothing()
    {
        const string source = "Use(b) = {\n Z = if(tick() == 1, A() + 1 / 0, 5)\n A = Z\n A(), A\n}\nUse(5)";
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", outcome.Kind);
        Assert.Contains("DivisionByZero", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Equal(["tick#1", "tick#2"], outcome.HostCalls);

        var ticks = 0;
        var operations = HostOperations.Create(HostOperation.Create("tick", (_, _) => new Result.Atom(++ticks)));
        var program = new Expr.AlgorithmExpr((await SourceProvenance.ParseValidAsync(source,
            new RunOptions { HostOperations = operations })).Root);
        var cache = new RunScopedZeroArgPropertyResultCache();
        var result = Evaluator.RunCountedObserved(program, zeroArgPropertyResultCache: cache, hostOperations: operations).Result;
        Assert.True(result.IsError);
        Assert.Equal(0, cache.GetSnapshot().Stores);
        Assert.Equal(0, cache.ActiveOwnerCount);
    }

    private static async Task AssertRoutes(string source, string expected, int ticks)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(expected, outcome.Value);
        Assert.Equal(Enumerable.Range(1, ticks).Select(i => $"tick#{i}"), outcome.HostCalls);
    }
}
