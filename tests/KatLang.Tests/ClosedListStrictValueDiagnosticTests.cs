using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>Q-15: closed heads block lifting, and the ordinary VALUE rejection
/// belongs to the first executed demand. Static roles do not prove execution.</summary>
public class ClosedListStrictValueDiagnosticTests
{
    public static IEnumerable<object[]> Demands()
    {
        foreach (var expression in new[]
        {
            "Math.Abs(A)", "abs(A)", "Math.Abs((A))", "Math.Abs(((A)))",
            "Math.Abs(Math.Abs(A))", "Math.Pow(A, 2)", "Math.Round(A, 2)",
            "Math.Sin(A)", "sqrt(A)", "A.abs", "(A).abs",
            "Id(Math.Abs(A))", "Alias(A)", "M.Abs(A)", "sum(A)", "A + 0",
            "[A]:0", "(A, A):0", "A.string",
        }) yield return [expression];
    }

    private const string Definitions = "A=q+1\nId(v)=v\nAlias=Math.Abs\nM={public Abs=Math.Abs}\n";

    [Theory]
    [MemberData(nameof(Demands))]
    public async Task ClosedHeadRefusalIsRejectedOnlyWhenTheConsumerDemands(string expression)
    {
        var selected = Definitions + $"F(x)={expression}\nF(7)";
        var unused = Definitions + $"F(x)=if(true,0,{expression})\nF(7)";
        var ignored = Definitions + $"Ignore(v)=0\nF(x)=Ignore({expression})\nF(7)";
        var family = Definitions + $"Choose(true,yes,no)=yes\nChoose(false,yes,no)=no\nChoose(c,yes,no)=not(c)\nF(x)=Choose(true,0,{expression})\nF(7)";
        foreach (var source in new[] { selected, unused, ignored, family })
            SourceProvenance.ParseValid(source);
        for (var route = 0; route < 6; route++)
        {
            Assert.Equal(KatLangErrorCode.ArityMismatch, (await ModelCProductionTests.Observe(selected, route)).Error);
            foreach (var source in new[] { unused, ignored, family })
            {
                var observation = await ModelCProductionTests.Observe(source, route);
                Assert.Null(observation.Error);
                Assert.Equal("0", observation.Value);
            }
        }
    }

    [Fact]
    public void SupplyingTheBindingOrInferringTheSignatureStillLifts()
    {
        foreach (var head in new[] { "F(q)", "F" })
        {
            var source = $"A=q+1\n{head}=Math.Abs(A)\nF(7)";
            SourceProvenance.ParseValid(source);
            Assert.Equal("8", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
        }
    }

    [Fact]
    public void DirectUndeclaredClosedNamesRemainStaticEvenInAnUnusedArgument()
    {
        var parsed = Parser.Parse("Ignore(v)=0\nF(x)=Ignore(missing)\nF(7)");
        Assert.Contains(parsed.Diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.UndeclaredIdentifier);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void HostSharedNode_ReachedNeutrallyAndStrictly_KeepsSharingIndependentlyOfOrder(
        bool strictRowFirst)
    {
        var sharedReference = new Expr.Resolve("A");
        var strictRow = new Expr.DotCall(new Expr.Resolve("Math"), "Abs", new OutputBundle([sharedReference]));
        Expr neutralRow = sharedReference;

        var parameterized = new Algorithm.User(
            null, Algorithm.NormalParameters(["q"]), [], [], [new Expr.Param("q")]);
        var closedCaller = new Algorithm.User(
            null,
            Algorithm.NormalParameters(["x"]),
            [],
            [],
            strictRowFirst ? [strictRow, neutralRow] : [neutralRow, strictRow])
        {
            HasExplicitParameterList = true,
        };
        var root = new Algorithm.User(
            null,
            [],
            [],
            [new Property("A", parameterized), new Property("F", closedCaller)],
            []);

        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(root, observations: null, diagnostics);

        Assert.Empty(diagnostics);

        // Whatever the order, the rewrite is the safe one in BOTH positions and the sharing
        // survives: no invented call, no invented parameter.
        var f = resolved.Properties.Single(p => p.Name == "F").Value;
        Assert.Equal(["x"], f.Params);
        var rewrittenRows = f.Output.ToList();
        var rewrittenStrictArgument = Assert.Single(
            Assert.IsType<Expr.DotCall>(rewrittenRows[strictRowFirst ? 0 : 1]).Args!);
        var rewrittenNeutralRow = rewrittenRows[strictRowFirst ? 1 : 0];
        Assert.IsType<Expr.Resolve>(rewrittenStrictArgument);
        Assert.IsType<Expr.Resolve>(rewrittenNeutralRow);
        Assert.Same(rewrittenStrictArgument, rewrittenNeutralRow);
    }

    /// <summary>
    /// A neutral memo hit for a shared COMPOSITE must replay strict observation through its
    /// children, not merely inspect a shared reference when that reference is the memo key.
    /// </summary>
    [Fact]
    public void HostSharedComposite_ReachedNeutrallyBeforeStrictly_KeepsItsBlockedChildUndemanded()
    {
        var sharedReference = new Expr.Resolve("A");
        Expr sharedValue = new Expr.Unary(UnaryOp.Minus, sharedReference);
        var strictRow = new Expr.DotCall(new Expr.Resolve("Math"), "Abs", new OutputBundle([sharedValue]));

        var parameterized = new Algorithm.User(
            null, Algorithm.NormalParameters(["q"]), [], [], [new Expr.Param("q")]);
        var closedCaller = new Algorithm.User(
            null,
            Algorithm.NormalParameters(["x"]),
            [],
            [],
            [sharedValue, strictRow])
        {
            HasExplicitParameterList = true,
        };
        var root = new Algorithm.User(
            null,
            [],
            [],
            [new Property("A", parameterized), new Property("F", closedCaller)],
            []);

        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(root, observations: null, diagnostics);

        Assert.Empty(diagnostics);
        var f = resolved.Properties.Single(p => p.Name == "F").Value;
        var rewrittenRows = f.Output.ToList();
        var rewrittenStrictArgument = Assert.Single(Assert.IsType<Expr.DotCall>(rewrittenRows[1]).Args!);
        Assert.Same(rewrittenRows[0], rewrittenStrictArgument);
        Assert.Same(
            Assert.IsType<Expr.Unary>(rewrittenRows[0]).Operand,
            Assert.IsType<Expr.Unary>(rewrittenStrictArgument).Operand);
    }

}
