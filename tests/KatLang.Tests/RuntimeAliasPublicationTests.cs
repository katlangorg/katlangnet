using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

public class RuntimeAliasPublicationTests
{
    [Theory]
    [InlineData("A(), A, A(), A", "S[1, 1, 2, 1]", 2)]
    [InlineData("A([]*), A", "S[1, 1]", 1)]
    [InlineData("Call0(A), A, Call0(A), A", "S[1, 1, 2, 1]", 2)]
    [InlineData("Forward(A), A, Forward(A), A", "S[1, 1, 2, 1]", 2)]
    [InlineData("R.Invoke(), A, R.Invoke(), A", "S[1, 1, 2, 1]", 2)]
    [InlineData("R.Algorithm(), A, (R.Algorithm)(), A", "S[1, 1, 2, 1]", 2)]
    [InlineData("Call0(R.Algorithm), A, Call0(R.Algorithm), A", "S[1, 1, 2, 1]", 2)]
    [InlineData("B(), B, A, B(), B", "S[1, 1, 2, 3, 1]", 3)]
    public async Task TerminalCalls_EstablishTheirOwnBinding_AndRemainFresh(string rows, string expected, int ticks)
    {
        var source = "Capture(meta c) = c\nCall0(f) = f()\nForward(f) = Call0(f)\nG(o) = tick()\n"
            + "Use(b) = {\n A = b.G\n B = A\n R = Capture(A())\n" + rows + "\n}\nUse(5)";
        await AssertRoutes(source, expected, ticks);
    }

    [Fact]
    public async Task LocalAliasEntries_BelongToTheirDeclaringActivation()
        => await AssertRoutes(
            "G(o) = o * 100 + tick()\nUse(b) = {\n A = b.G\n A(), A, A(), A\n}\nUse(1), Use(2), Use(1)",
            "S[S[101, 101, 102, 101], S[203, 203, 204, 203], S[105, 105, 106, 105]]", 6);

    [Fact]
    public async Task SiblingAliases_KeepSeparateEntries()
        => await AssertRoutes(
            "G(o) = o * 100 + tick()\nUse(b) = {\n A = b.G\n B = b.G\n A(), B, A, B(), B\n}\nUse(1)",
            "S[101, 102, 101, 103, 102]", 3);

    [Fact]
    public async Task StructuralMemberAlias_UsesTheSameEntryAsItsBareRead()
        => await AssertRoutes(
            "Capture(meta c) = c\nZ = 9\nMk(n) = if(tick() > 0, Capture(Z()), 0)\n"
            + "Box = { public A = Mk(5).Algorithm }\nBox.A(), Box.A, Box.A(), Box.A",
            "S[9, 9, 9, 9]", 2);

    [Theory]
    [InlineData("Use(f) = {\n A = f\n A(), A\n}\nUse(Only)", "S[1, 2]", 2)]
    [InlineData("R = Capture(Only())\nA = R.Algorithm\nA(), Only", "S[1, 2]", 2)]
    [InlineData("R = Capture(Only())\nA = R.Algorithm\nA(), A, A(), A", "S[1, 2, 3, 2]", 3)]
    public async Task ParameterizedRuntimeTargets_PublishNeitherAliasNorTarget(string body, string expected, int ticks)
        => await AssertRoutes("Capture(meta c) = c\nOnly(*xs) = tick()\n" + body, expected, ticks);

    [Fact]
    public async Task TerminalAliasAndZeroParameterTarget_KeepIndependentEntries()
        => await AssertRoutes(
            "Capture(meta c) = c\nZ = tick()\nMk(n) = if(n == n, Capture(Z()), 0)\nA = Mk(5).Algorithm\nA(), Z(), A, Z",
            "S[1, 2, 1, 1]", 2);

    [Fact]
    public async Task ReentrantTerminalCalls_PublishTheOuterOwnersResult()
        => await AssertRoutes(
            "Use(b) = {\n G(o) = if(tick() < 3, A() + 1, 0)\n A = b.G\n A(), A\n}\nUse(5)",
            "S[2, 2]", 3);

    [Fact]
    public async Task ReentrantSuccessUnderFailedOwner_PublishesNothing()
    {
        const string source = "Use(b) = {\n G(o) = if(tick() == 1, A() + 1 / 0, 5)\n A = b.G\n A(), A\n}\nUse(5)";
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
