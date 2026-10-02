using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;

namespace KatLang.Tests;

public class ModelCProductionTests
{
    [Theory]
    [InlineData("F(x,y)=x\nF(trace(1),1/0)", "1", "1")]
    [InlineData("F(x)=10\nF(trace(1)/0)", "10", "")]
    [InlineData("F(x)=x+x\nF(tick())", "2", "tick#1")]
    [InlineData("F(x,y)=y+x\nF(trace(1),trace(2))", "3", "2,1")]
    [InlineData("G(x)=x+x\nF(x)=G(x)\nF(tick())", "2", "tick#1")]
    [InlineData("G(x)=10\nF(x)=G\nF(trace(1)/0)", "10", "")]
    [InlineData("G(x,y)=y+x\nF(x,y)=G\nF(trace(1),trace(2))", "3", "2,1")]
    [InlineData("F(*xs)=10\nF(trace(1),1/0)", "10", "")]
    [InlineData("G(*xs)=10\nF(*xs)=G\nF(trace(1),1/0)", "10", "")]
    [InlineData("G(xs)=10\nF(*xs)=G\nF(trace(1),1/0)", "10", "")]
    [InlineData("F(0,x)=7\nF(n,0)=8\nF(trace(0),1/0)", "7", "0")]
    [InlineData("F(0,x)=7\nF(n,0)=8\nF(trace(1),trace(0))", "8", "1,0")]
    [InlineData("F(x,x,0)=7\nF(a,b,c)=b\nF(trace(1),trace(2),1/0)", "2", "1,2")]
    [InlineData("Apply(f,x)=f(x)\nInc(x)=x+1\nApply(Inc,trace(4))", "5", "4")]
    [InlineData("Z=tick()\nF(x)=10\nF(Z)\nZ", "(10, 1)", "tick#1")]
    [InlineData("Z=tick()\nF(x)=x+x\nF(Z())\nF(Z())", "(2, 4)", "tick#1,tick#2")]
    [InlineData("Step(x)=7\nrepeat(Step,1,trace(1)/0)", "7", "")]
    [InlineData("Step(x)=x+x\nrepeat(Step,1,tick())", "2", "tick#1")]
    [InlineData("Inc(x)=x+1\nF(q)=if(true,0,abs(Inc))\nF(0)", "0", "")]
    [InlineData("Choose(true,yes,no)=yes\nChoose(false,yes,no)=no\nChoose(condition,yes,no)=not(condition)\nInc(x)=x+1\nF(q)=Choose(true,0,abs(Inc))\nF(0)", "0", "")]
    [InlineData("Choose(true,yes,no)=yes\nChoose(false,yes,no)=no\nChoose(condition,yes,no)=not(condition)\nW(condition,yes,no)=Choose\nW(false,1/0,tick())", "1", "tick#1")]
    [InlineData("W(condition,whenTrue,whenFalse)=if\nW(true,tick(),trace(2)/0)", "1", "tick#1")]
    [InlineData("F(x)={G(n)=n+x\nmap([1,2],G)}\nF(tick())", "[2, 3]", "tick#1")]
    [InlineData("map([],1/0)", "[]", "")]
    [InlineData("filter([],trace(1)/0)", "[]", "")]
    [InlineData("reduce([],1/0,tick())", "1", "tick#1")]
    [InlineData("[].filter(trace(1)/0).count", "0", "")]
    [InlineData("count([].filter(trace(1)/0))", "0", "")]
    [InlineData("F(x)=if(true,x,x)+x\nF(tick())", "2", "tick#1")]
    [InlineData("G(x)=x+x\nAlias=G\nF(x)=Alias(x)+x\nF(tick())", "3", "tick#1")]
    public async Task SupplyDemandsAndTransportAgreeAcrossSixRoutes(string source, string expected, string effects)
    {
        for (var route = 0; route < 6; route++)
        {
            var observation = await Observe(source, route);
            Assert.True(observation.Error is null, $"route {route}: {observation.Error}");
            Assert.Equal(expected, observation.Value);
            Assert.Equal(effects, observation.Effects);
        }
    }

    [Theory]
    [InlineData("A={}\nA(trace(1)/0)", KatLangErrorCode.ArityMismatch, "")]
    [InlineData("F(x)=x\nF(trace(1)/0,2)", KatLangErrorCode.ArityMismatch, "")]
    [InlineData("count(trace(1)/0,2)", KatLangErrorCode.ArityMismatch, "")]
    [InlineData("abs(trace(1)/0,2)", KatLangErrorCode.ArityMismatch, "")]
    [InlineData("trace(trace(1)/0,2)", KatLangErrorCode.ArityMismatch, "")]
    [InlineData("F(0)=7\nF(1)=8\nF(trace(1)/0,2)", KatLangErrorCode.ArityMismatch, "")]
    [InlineData("F(x,x,(a,b))=7\nF(trace(1),trace(2),1/0)", KatLangErrorCode.ArityMismatch, "1,2")]
    [InlineData("F(x,x,x)=7\nF(trace(1),trace(2),1/0)", KatLangErrorCode.ArityMismatch, "1,2")]
    [InlineData("F(*xs)=xs.first\nF(trace(1),1/0)", KatLangErrorCode.DivisionByZero, "1")]
    [InlineData("F(0,x)=7\nF(n,0)=8\nF(1/0,0)", KatLangErrorCode.DivisionByZero, "")]
    [InlineData("F(x)=7\nF(trace(1),[trace(2)/0]*)", KatLangErrorCode.DivisionByZero, "2")]
    [InlineData("F(x)=x.string(trace(1)/0)\nF(7)", KatLangErrorCode.ArityMismatch, "")]
    public async Task DemandPhasesAndEarlyConflictAreUniform(string source, KatLangErrorCode expected, string effects)
    {
        for (var route = 0; route < 6; route++)
        {
            var observation = await Observe(source, route);
            Assert.Equal(expected, observation.Error);
            Assert.Equal(effects, observation.Effects);
        }
    }

    [Theory]
    [InlineData("true", "tick()", "trace(2)/0")]
    [InlineData("false", "trace(1)/0", "tick()")]
    [InlineData("trace(true)", "trace(1)+trace(2)", "trace(3)")]
    [InlineData("trace(false)", "trace(1)", "trace(2)+trace(3)")]
    [InlineData("1", "tick()", "trace(2)/0")]
    [InlineData("[]", "tick()", "trace(2)/0")]
    [InlineData("true", "1/0", "tick()")]
    [InlineData("false", "tick()", "1/0")]
    [InlineData("true", "{ }", "tick()")]
    [InlineData("false", "tick()", "{ }")]
    public async Task BuiltinIfAndOrdinaryChooseHaveTheSameDemandOracle(string condition, string yes, string no)
    {
        const string definitions = "Choose(true,yes,no)=yes\nChoose(false,yes,no)=no\nChoose(condition,yes,no)=not(condition)\n";
        for (var route = 0; route < 6; route++)
        {
            var expected = await Observe($"if({condition},{yes},{no})", route);
            string[] spellings =
            [
                definitions + $"Choose({condition},{yes},{no})",
                definitions + $"Alias=Choose\nAlias({condition},{yes},{no})",
                definitions + $"W(condition,yes,no)=Choose\nW({condition},{yes},{no})",
                definitions + $"Apply(selector,c,a,b)=selector(c,a,b)\nApply(Choose,{condition},{yes},{no})",
                definitions + $"({condition}).Choose({yes},{no})",
                $"Alias=if\nAlias({condition},{yes},{no})",
                $"W(condition,whenTrue,whenFalse)=if\nW({condition},{yes},{no})",
                $"Apply(selector,c,a,b)=selector(c,a,b)\nApply(if,{condition},{yes},{no})",
            ];
            foreach (var spelling in spellings)
            {
                var actual = await Observe(spelling, route);
                Assert.Equal(expected.Value, actual.Value);
                Assert.Equal(expected.Error, actual.Error);
                Assert.Equal(expected.Effects, actual.Effects);
            }
        }
    }

    internal static async Task<(string? Value, KatLangErrorCode? Error, string Effects)> Observe(string source, int route)
    {
        var log = new List<string>();
        var ticks = 0;
        Result Tick() { log.Add($"tick#{++ticks}"); return new Result.Atom((Decimal128)ticks); }
        Result Trace(IReadOnlyList<Result> args) { log.Add(Render(args[0])); return args[0]; }
        var hosts = route is 2 or 5
            ? HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return Trace(args); }, "x"))
            : HostOperations.Create(HostOperation.Create("tick", (_, _) => Tick()), HostOperation.Create("trace", (args, _) => Trace(args), "x"));
        var options = new RunOptions { HostOperations = hosts };
        var parsed = Parser.Parse(source, options);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        if (route < 3)
        {
            var run = route == 0 ? KatLangEngine.Run(source, options) : await KatLangEngine.RunAsync(source, options);
            return run switch
            {
                RunResult.Success success => (Render(success.Value), null, string.Join(",", log)),
                RunResult.EvalFailure failure => (null, Assert.Single(failure.Errors).Code, string.Join(",", log)),
                _ => throw new InvalidOperationException(run.ToString()),
            };
        }
        var expression = new Expr.AlgorithmExpr(parsed.Root);
        var (result, _) = route == 5
            ? await Evaluator.RunCountedObservedAsync(expression, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: hosts)
            : Evaluator.RunCountedObserved(expression, enableOptimizations: route == 4, hostOperations: hosts);
        return result.IsError ? (null, result.Error.Code, string.Join(",", log)) : (Render(result.Value.Value), null, string.Join(",", log));
    }

    private static string Render(Result value) => value switch
    {
        Result.Atom atom => ValueTextRenderer.FormatNumberInvariant(atom.Value),
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.Str text => text.Value,
        Result.SequenceValue sequence => "(" + string.Join(", ", sequence.Items.Select(Render)) + ")",
        Result.ListValue list => "[" + string.Join(", ", list.Items.Select(Render)) + "]",
    };
}
