using KatLang.Semantics;

namespace KatLang.Tests;

public class NameResolutionHostileReviewTests
{
    [Theory]
    [InlineData("A = q + 1\nF = (Math.Abs)(A)\nF(1)")]
    [InlineData("F = (Math.Abs)(A)\nA = B + 1\nB = q\nF(1)")]
    [InlineData("A = q + 1\nF = ((Math.Abs))(A)\nF(1)")]
    [InlineData("A = q + 1\nF = abs(A)\nF(1)")]
    [InlineData("A = q + 1\nF = Math.Abs(A)\nF(1)")]
    [InlineData("open Math\nA = q + 1\nF = (Abs)(A)\nF(1)")]
    [InlineData("A = q + 1\nF = (Math.Pow)(A, 1)\nF(1)")]
    public void QualifiedMathCallableInOrdinaryCall_PreservesConsumerIdentity(string source)
    {
        var parsed = SourceProvenance.ParseValid(source);
        Assert.Equal(["q"], parsed.Root.Properties.Single(p => p.Name == "F").Value.Params);
        Assert.Equal("2", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Theory]
    [InlineData("Math = { public Abs(x) = x }\nA = q + 1\nF(z) = (Math.Abs)(A)\nF(1)")]
    [InlineData("A = q + 1\nF(Math) = (Math.Abs)(A)\nF(1)")]
    [InlineData("A = q + 1\nF(z) = (Math.Pi)(A)\nF(1)")]
    [InlineData("A = q + 1\nF(z) = (Math.Abs(-2))(A)\nF(1)")]
    public void OrdinaryCall_OnlyTheSelectedMathFunctionHasStrictArguments(string source)
    {
        var parsed = SourceProvenance.ParseValid(source);
        var call = Assert.IsType<Expr.Call>(Assert.Single(parsed.Root.Properties.Single(p => p.Name == "F").Value.Output));
        Assert.IsType<Expr.Resolve>(Assert.Single(call.Args));
    }

    [Fact]
    public async Task QualifiedMathOrdinaryCall_RetainsItsArgumentAcrossSuspension()
    {
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("Gate", (_, _) =>
            {
                calls++;
                return new ValueTask<Result>(gate.Task);
            })),
        };
        const string source = "A = Gate() + q\nF = (Math.Abs)(A)\nF(1)";
        var parsed = Parser.Parse(source, options);
        Assert.Empty(parsed.Diagnostics);
        Assert.Equal(["q"], parsed.Root.Properties.Single(p => p.Name == "F").Value.Params);
        var pending = KatLangEngine.RunAsync(source, options);
        Assert.Equal(1, calls);
        Assert.False(pending.IsCompleted);
        gate.SetResult(new Result.Atom(1));
        Assert.Equal("2", Assert.IsType<RunResult.Success>(await pending).ToDisplayString());
        Assert.Equal(1, calls);
    }

    [Fact]
    public void QualifiedMathCallableInClosedOrdinaryCall_ReportsTheDemandedArgument()
    {
        const string source = "A = q + 1\nF(x) = (Math.Abs)(A)\nF(1)";
        var diagnostic = Assert.Single(Parser.Parse(source).Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Contains("'A' is required as a value here", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(2, 19, 2, 20), diagnostic.Span);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void DistinctLongOpenTargets_RemainAmbiguous(bool dotted, bool reverse)
    {
        var prefix = new string('N', 520);
        var first = dotted ? prefix + ".Left" : prefix + "Left";
        var second = dotted ? prefix + ".Right" : prefix + "Right";
        var declarations = dotted
            ? $"{prefix} = {{\n public Left = {{ public X = 1 }}\n public Right = {{ public X = 2 }}\n}}"
            : $"{first} = {{ public X = 1 }}\n{second} = {{ public X = 2 }}";
        var targets = reverse ? $"{second}, {first}" : $"{first}, {second}";
        var source = $"open {targets}\n{declarations}\nX";
        var parsed = SourceProvenance.ParseValid(source);
        Assert.Empty(parsed.Root.Params);
        var scope = ElaboratedScopeLookup.CreateScope(parsed.Root);
        Assert.Equal(2, scope.GetResolvedOpenProviders().Count);
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var resolution = model.FindResolutionAt(new SourcePosition(source.Split('\n').Length, 1));
        Assert.Equal(IdentifierClassification.Unresolved, Assert.IsType<IdentifierResolution>(resolution).Classification);
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.AmbiguousOpen, Assert.Single(failure.Errors).Code);
    }

    [Fact]
    public void RepeatedLongOpenTarget_IsStillOneProvider()
    {
        var name = new string('N', 520);
        var source = $"open {name}, ({name})\n{name} = {{ public X = 7 }}\nX";
        var parsed = SourceProvenance.ParseValid(source);
        Assert.Single(ElaboratedScopeLookup.CreateScope(parsed.Root).GetResolvedOpenProviders());
        Assert.Equal("7", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LongAmbiguousProviders_ChargeNeitherCapture(bool reverse)
    {
        var prefix = new string('N', 520);
        var targets = reverse ? $"{prefix}B, {prefix}A" : $"{prefix}A, {prefix}B";
        var source = $"Outer(p) = {{\n {prefix}A = {{ public X = p }}\n {prefix}B = {{ public X = 7 }}\n public Y = {{ open {targets}\n X }}\n 0\n}}\nOuter.Y";
        var parsed = SourceProvenance.ParseValid(source);
        var y = parsed.Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single(p => p.Name == "Y");
        Assert.Equal(PropertyExposure.Exported, y.Exposure);
        Assert.Equal(KatLangErrorCode.AmbiguousOpen,
            Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors).Code);
    }

    [Theory]
    [InlineData("A, B")]
    [InlineData("B, A")]
    public void InnerOpenAmbiguity_DoesNotFallThroughToOuterProvider(string targets)
    {
        var source = $"open Outside\nOutside = {{ public X = 9 }}\nOuter(p) = {{\n A = {{ public X = p }}\n B = {{ public X = 7 }}\n public Y = {{\n open {targets}\n Inner = X\n Inner\n }}\n 0\n}}\nOuter.Y";
        var parsed = SourceProvenance.ParseValid(source);
        var y = parsed.Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single(p => p.Name == "Y");
        Assert.Equal(PropertyExposure.Exported, y.Exposure);
        Assert.Equal(KatLangErrorCode.AmbiguousOpen,
            Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors).Code);
    }
}
