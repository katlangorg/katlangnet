using System.Numerics;

namespace KatLang.Tests;

/// <summary>Shared-authority replacements, before the coherent default cutover.</summary>
public sealed class StaticStructureConsolidationTests
{
    private static StaticQueryKey Invocation(StaticScopeKey scope)
        => StaticQueryKey.Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.InvocationTarget);

    [Theory]
    [InlineData("X=UB+0\nUB=UA\nUA=U\nU(0)=X\nU(1)=1\n5", "UB", 5)]
    [InlineData("X=L.UA+0\nL={public UA=U\nX+0}\nU(0)=1\nU(1)=1\n5", "L.UA", 7)]
    public void UnsettledInvocationConsumersRetainTheTerminalFamilyDiagnostic(string source, string written, int endColumn)
    {
        var compiled = FrontEndPipeline.Process(source);
        var diagnostic = Assert.Single(compiled.Diagnostics, d => d.Code == DiagnosticCode.UnliftableClauseFamily);
        Assert.Equal($"'{written}' is used as a value here, but '{written}', an alias of clause family 'U', has no formula-lifting signature: no clause binds argument position 1 with a plain parameter.{Environment.NewLine}"
            + $"Formula lifting forwards arguments by parameter name, and literal, structural and binderless clause patterns name nothing. Call '{written}' with explicit arguments, or bind that position with one plain parameter name in the clauses that bind it.", diagnostic.Message);
        Assert.Equal(1, diagnostic.Span!.Value.Start.Line);
        Assert.Equal(3, diagnostic.Span.Value.Start.Column);
        Assert.Equal(endColumn, diagnostic.Span.Value.End.Column);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InvocationFollowsCarriersButNamespaceSelectionKeepsTheirOwnIdentity(bool inputFirst)
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("A=B\nB={public V=7\nC}\nC=abs\n0");
        var queries = new StaticStructureQueries(raw, new(1_000_000, 4, 100_000, 4_000_000));
        var scopes = raw.Properties.ToDictionary(p => p.Name, p => queries.BodyIn(queries.Root, p.Value));
        if (inputFirst) queries.Get(StaticQueryKey.Inputs(scopes["A"]));
        var invocation = queries.Get(Invocation(scopes["A"]));
        Assert.Equal(StaticFactKind.Structure, invocation.Kind);
        Assert.Same(queries.BodyOf(queries.Keys.Root).Properties.Single(p => p.Name == "abs").Value,
            queries.BodyOf(invocation.Scope!));
        Assert.Equal("abs", Assert.IsType<Expr.Resolve>(invocation.Data).Name);
        Assert.Same(scopes["B"], queries.Get(StaticQueryKey.TargetWalk(scopes["A"], StaticCycleCheck.Formation)).Scope);
        Assert.Same(invocation, queries.Get(Invocation(scopes["A"])));
    }

    [Theory]
    [InlineData("A=A\n0", "A")]
    [InlineData("A=B\nB=A\n0", "A")]
    [InlineData("A(x)=abs\n0", "A")]
    [InlineData("A=unknown\n0", "A")]
    public void InvocationKeepsAnIneligibleOrCyclicDeclaration(string source, string name)
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot(source);
        var queries = new StaticStructureQueries(raw, new(1_000_000, 4, 100_000, 4_000_000));
        var scope = queries.BodyIn(queries.Root, raw.Properties.Single(p => p.Name == name).Value);
        var result = queries.Get(Invocation(scope));
        Assert.Equal(StaticFactKind.Structure, result.Kind);
        Assert.Same(scope, result.Scope);
        Assert.Null(result.Data);
    }

    [Fact]
    public void InvocationSharesATailBeyondTheOld4096HopLimit()
    {
        const int length = 4200;
        const int readers = 32;
        var source = string.Join('\n', Enumerable.Range(0, length).Select(i => $"A{i}=" + (i + 1 == length ? "abs" : $"A{i + 1}")))
            + "\n" + string.Join('\n', Enumerable.Range(0, readers).Select(i => $"R{i}=A0")) + "\n0";
        var raw = SourceProvenance.ParseSyntaxValidRoot(source);
        var queries = new StaticStructureQueries(raw, new(2_000_000, 4, 500_000, 16_000_000));
        StaticScopeKey? terminal = null;
        foreach (var reader in raw.Properties.Skip(length))
        {
            var result = queries.Get(Invocation(queries.BodyIn(queries.Root, reader.Value)));
            terminal ??= result.Scope;
            Assert.Same(terminal, result.Scope);
            Assert.Equal("abs", Assert.IsType<Expr.Resolve>(result.Data).Name);
        }
        Assert.Same(queries.BodyOf(queries.Keys.Root).Properties.Single(p => p.Name == "abs").Value,
            queries.BodyOf(terminal!));
        Assert.True(queries.Statistics.Reads < 500L * (length + readers), queries.Statistics.ToString());
    }

    [Theory]
    [InlineData("A=B\nB={public V=7\nC}\nC=abs\nA(-42)", 42)]
    [InlineData("Use=Lib.A\nLib={public A=B\nB=abs\n0}\nUse(-42)", 42)]
    [InlineData("Lib={public A=B\nB=abs\n0}\nUse=Lib.A\nUse(-42)", 42)]
    [InlineData("Lib={public A=abs\n0}\nA=Lib\nA.A(-42)", 42)]
    [InlineData("A={public V=7\nabs}\nA.V", 7)]
    [InlineData("A=B.K\nB={V(x)=x*10\nK=V\nU=A}\nZ=A+1\nZ(4)", 41)]
    [InlineData("B={V(x)=x*10\nK=V\nU=A}\nA=B.K\nZ=A+1\nZ(4)", 41)]
    public async Task InvocationAndMemberConsumersPreserveProcessedProjection(string source, int expected)
    {
        var result = FrontEndPipeline.Process(source);
        Assert.False(result.HasErrors, string.Join('\n', result.Diagnostics.Select(d => d.Message)));
        var value = Evaluator.RunFlat(new Expr.AlgorithmExpr(result.ElaboratedRoot));
        Assert.False(value.IsError, value.IsError ? value.Error.ToString() : "");
        Assert.Equal(new[] { (Decimal128)expected }, value.Value);
        var asyncValue = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(result.ElaboratedRoot));
        Assert.False(asyncValue.IsError, asyncValue.IsError ? asyncValue.Error.ToString() : "");
        Assert.Equal(new[] { (Decimal128)expected }, asyncValue.Value);
    }
}
