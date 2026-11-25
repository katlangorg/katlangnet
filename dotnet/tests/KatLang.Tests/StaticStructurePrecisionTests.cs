using System.Numerics;

namespace KatLang.Tests;

/// <summary>Precision pins use independent semantic outcomes, rather than accepting a captured dependency cycle.</summary>
public sealed class StaticStructurePrecisionTests
{
    private static readonly string[] CarrierDeclarations =
    [
        "Settings = Config",
        "Config = { public Rate = 0.2\nDefault }",
        "Default = Settings.Rate",
    ];

    public static TheoryData<int, int, int> DeclarationOrders => new()
    {
        { 0, 1, 2 }, { 0, 2, 1 }, { 1, 0, 2 }, { 1, 2, 0 }, { 2, 0, 1 }, { 2, 1, 0 },
    };

    [Fact]
    public void CarrierTargetCycleStillRefusesTransparentMemberTransport()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot(
            "Settings=Config\nConfig={public Rate=0.2\nSettings}\nDefault=Settings.Rate\n0");
        var queries = new StaticStructureQueries(raw, new(1_000_000, 4, 100_000, 4_000_000));
        var scopes = raw.Properties.ToDictionary(p => p.Name, p => queries.BodyIn(queries.Root, p.Value));
        var target = queries.Get(StaticQueryKey.TargetWalk(scopes["Settings"], StaticCycleCheck.Formation));
        Assert.Equal(StaticFactKind.Structure, target.Kind);
        Assert.Same(scopes["Settings"], target.Scope);
        Assert.Equal(StaticFactKind.Yes, queries.Get(StaticQueryKey.IsInput(scopes["Default"], "Rate")).Kind);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ModuleCalleeSignatureDemandActivatesTheWrittenHolder(bool ownerFirst)
    {
        const string owner = "Lib={M=load('https://modules.example/u.kat')\n0}";
        const string reader = "S=Lib.M.F(abs)";
        var source = (ownerFirst ? owner + "\n" + reader : reader + "\n" + owner) + "\nS(-5)";
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["modules.example"],
            DownloadCode = async (_, _) => { await Task.Yield(); downloads++; return "F=abs\n0"; },
        };
        var compiled = await FrontEndPipeline.ProcessAsync(source, options);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        Assert.Equal(1, downloads);
        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(new[] { (Decimal128)5 }, result.Value);
    }

    [Theory]
    [MemberData(nameof(DeclarationOrders))]
    public async Task CarrierMemberDoesNotDependOnTheCarriersForwardedValue(int first, int second, int third)
    {
        var source = string.Join('\n', new[] { first, second, third }.Select(i => CarrierDeclarations[i])) + "\nSettings";
        var raw = SourceProvenance.ParseSyntaxValidRoot(source);
        // A member read navigates Config's own structure. The forwarded Default value cannot change Rate's
        // declaration, and Default either has no inputs or is ineligible for a target cycle: both are acyclic.
        foreach (var demandInputFirst in new[] { false, true })
        {
            var queries = new StaticStructureQueries(raw, new(1_000_000, 4, 100_000, 4_000_000));
            var scopes = raw.Properties.ToDictionary(p => p.Name, p => queries.BodyIn(queries.Root, p.Value));
            if (demandInputFirst) queries.Get(StaticQueryKey.IsInput(scopes["Default"], "Rate"));
            foreach (var stratum in Enum.GetValues<StaticCycleCheck>().Reverse())
            {
                var target = queries.Get(StaticQueryKey.TargetWalk(scopes["Settings"], stratum));
                Assert.Equal(StaticFactKind.Structure, target.Kind);
                Assert.Same(scopes["Config"], target.Scope);
            }
            Assert.Equal(StaticFactKind.No, queries.Get(StaticQueryKey.IsInput(scopes["Default"], "Rate")).Kind);
        }

        var compiled = FrontEndPipeline.Process(source);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        foreach (var optimized in new[] { false, true })
        {
            var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null,
                enableOptimizations: optimized);
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
            Assert.Equal(Decimal128.Parse("0.2"), Assert.IsType<Result.Atom>(result.Value.Value).Value);
        }
        var asynchronous = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot));
        Assert.False(asynchronous.IsError, asynchronous.IsError ? asynchronous.Error.ToString() : "");
        Assert.Equal(new[] { Decimal128.Parse("0.2") }, asynchronous.Value);
    }
}
