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
    // A computed dot value is no Math member (a call written directly after an argument-bearing
    // edge, `(Math.Abs(-2))(A)`, no longer parses at all — SYN-09, Q-18 C-B3).
    [InlineData("A = q + 1\nF(z) = (2.abs)(A)\nF(1)")]
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
        var parsed = SourceProvenance.ParseValid(source);
        var error = parsed.ExpectEvaluationError<EvalError.ArityMismatch>();
        Assert.Equal((1, 0), (error.Expected, error.Actual));
        Assert.Equal(new SourceSpan(2, 19, 2, 20),
            Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors).Span);
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
        // Two declarations are two providers (Q-19 D-I), so the WRITTEN `X` they both
        // provide is the front end's ambiguity at the occurrence (Q-29 A-U).
        var source = $"open {targets}\n{declarations}\nX";
        var line = source.Split('\n').Length;
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code);
        Assert.Equal(new SourceSpan(line, 1, line, 2), diagnostic.Span);
        Assert.Empty(parsed.Root.Params);
        var scope = ElaboratedScopeLookup.CreateScope(parsed.Root);
        Assert.Equal(2, scope.GetResolvedOpenProviders().Count);
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var resolution = model.FindResolutionAt(new SourcePosition(line, 1));
        Assert.Equal(IdentifierClassification.Unresolved, Assert.IsType<IdentifierResolution>(resolution).Classification);
        var rejected = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.AmbiguousOpen, Assert.Single(rejected.Errors).Code);

        // A lookup only evaluation decides (a fallback on a parameter receiver) stays the
        // evaluators' run-time ambiguity, whatever the targets' length.
        var fallback = $"{declarations}\nK(q) = {{\n open {targets}\n q.X\n}}\nK(10)";
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(fallback));
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
        // The read is a fallback on a parameter receiver — a lookup only evaluation decides —
        // so the two providers charge nothing (Y stays exported) and the evaluators report it.
        var source = $"Outer(p) = {{\n {prefix}A = {{ public X(v) = p }}\n {prefix}B = {{ public X(v) = 7 }}\n public Y = {{ open {targets}\n K(q) = q.X\n K(10) }}\n 0\n}}\nOuter.Y";
        var parsed = SourceProvenance.ParseValid(source);
        var y = parsed.Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single(p => p.Name == "Y");
        Assert.Equal(PropertyExposure.Exported, y.Exposure);
        Assert.Equal(KatLangErrorCode.AmbiguousOpen,
            Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors).Code);

        // A WRITTEN X there is the front end's ambiguity at the occurrence (Q-29 A-U).
        var written = $"Outer(p) = {{\n {prefix}A = {{ public X = p }}\n {prefix}B = {{ public X = 7 }}\n public Y = {{ open {targets}\n X }}\n 0\n}}\nOuter.Y";
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(written));
        Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code);
        Assert.Equal(new SourceSpan(5, 2, 5, 3), diagnostic.Span);
    }

    [Theory]
    [InlineData("A, B")]
    [InlineData("B, A")]
    public void InnerOpenAmbiguity_DoesNotFallThroughToOuterProvider(string targets)
    {
        // The deciding level is Y's: its two providers select nothing, and the root's
        // `Outside` provider is never consulted — for the written name (the front end's
        // ambiguity, Q-29 A-U) and for a lookup only evaluation decides (the evaluators').
        var written = $"open Outside\nOutside = {{ public X = 9 }}\nOuter(p) = {{\n A = {{ public X = p }}\n B = {{ public X = 7 }}\n public Y = {{\n open {targets}\n Inner = X\n Inner\n }}\n 0\n}}\nOuter.Y";
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(written));
        Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code);
        Assert.Equal(new SourceSpan(8, 10, 8, 11), diagnostic.Span);

        var source = $"open Outside\nOutside = {{ public X(v) = 9 }}\nOuter(p) = {{\n A = {{ public X(v) = p }}\n B = {{ public X(v) = 7 }}\n public Y = {{\n open {targets}\n Inner(q) = q.X\n Inner(10)\n }}\n 0\n}}\nOuter.Y";
        var parsed = SourceProvenance.ParseValid(source);
        var y = parsed.Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single(p => p.Name == "Y");
        Assert.Equal(PropertyExposure.Exported, y.Exposure);
        Assert.Equal(KatLangErrorCode.AmbiguousOpen,
            Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors).Code);
    }
}
