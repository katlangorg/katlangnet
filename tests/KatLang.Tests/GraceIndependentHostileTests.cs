using System.Numerics;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Permanent Q-16 review regressions for owner-sensitive DAG rewriting, captured
/// hoisted names, written coordinates, and deferred acquisition/validation ordering.
/// </summary>
public class GraceIndependentHostileTests
{
    [Theory]
    [InlineData("\n", "~x")]
    [InlineData("\r\n", "x~~")]
    [InlineData("\n", "~x~")]
    [InlineData("\r\n", "~~x")]
    public void CoordinatesAndEditor_UseTheWrittenMarkerAndCapturedIdentifier(string newline, string marker)
    {
        var source = "Apply(f) = f(1)" + newline + "F(x) = Apply({" + newline +
            "\t'😀λ'" + newline + "\t# Unicode precedes the occurrence" + newline +
            "\t( # multiline grouping" + newline + "\t    '😀λ', " + marker + newline + "\t)" + newline + "})";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source).Parsed;
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(new SourceSpan(6, 13, 6, 13 + marker.Length), diagnostic.Span);
        Assert.Contains("parameter of an enclosing algorithm", diagnostic.Message);

        var nameColumn = 13 + marker.IndexOf('x');
        var model = SemanticModelBuilder.Build(parsed);
        var resolution = model.FindResolutionAt(new SourcePosition(6, nameColumn));
        Assert.NotNull(resolution);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, resolution.Classification);
        Assert.Equal(new SourceSpan(2, 3, 2, 4), resolution.ResolvedDeclaration!.Span);
        Assert.Equal(
            model.IdentifierResolutions.Select(r => (r.Occurrence, r.Classification, r.ResolvedDeclaration, r.ResolvedProperty?.Name)),
            SemanticModelBuilder.Build(parsed).IdentifierResolutions.Select(r =>
                (r.Occurrence, r.Classification, r.ResolvedDeclaration, r.ResolvedProperty?.Name)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EnclosingHoistedCapture_IsNotTheNamedDescendantsOwn(bool family)
    {
        var source = "Apply(f) = f(1)\nF = {\n    a, b = (x, 2)\n" +
            (family ? "    H(0) = 0\n    H(k) = { B = y - ~x\n        Apply(B) }\n    a + H(1)\n}" :
                "    B = y - ~x\n    a + Apply(B)\n}");
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Contains("parameter of an enclosing algorithm", diagnostic.Message);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task NestedFamilyAndMultipleHoists_RetainOwnInference(bool sibling)
    {
        var source = "Apply(f) = f(2, 13)\n" + (sibling ? "F(0) = 0\n" : "") +
            "F(k) = { H(0) = 0\n    H(m) = {\n        P = { a, b = (y, ~x)\n" +
            "            c, d = (a, b)\n            c - d }\n        Apply(P) + m\n    }\n    H(k)\n}\nF(1)";
        var result = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", result.Kind);
        Assert.Equal("12", result.Value);
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        Assert.Equal(["x", "y"], Assert.Single(model.FindProperties("P")).Parameters.Select(p => p.Name));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DeferredClassification_UsesLoadedProviderOnlyWhenSelected(bool selected)
    {
        var fetches = 0;
        var source = "F(0) = 5\nF(n) = { open load('https://mods.test/hostile.kat')\n" +
            "    P = y + ~x\n    P(1)\n}\nF(" + (selected ? "1" : "0") + ")";
        var result = await KatLangEngine.RunAsync(source, new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = async (_, _) => { fetches++; await Task.Yield(); return "public x = 7"; },
        });
        Assert.Equal(selected ? 1 : 0, fetches);
        if (!selected)
        {
            Assert.Equal((Decimal128)5, Assert.IsType<RunResult.Success>(result).Value.AsNum());
        }
        else
        {
            var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
            Assert.Equal(KatLangErrorCode.InvalidGraceMarker, error.Code);
            Assert.Contains("opened property", error.Message);
            Assert.Equal(new SourceSpan(3, 13, 3, 15), error.Span);
        }
    }

    [Fact]
    public async Task DeferredUnit_CancellationDuringAcquisitionPrecedesGraceValidation()
    {
        using var cancellation = new CancellationTokenSource();
        var acquired = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var run = KatLangEngine.RunAsync(
            "F(0) = 0\nF(n) = { M = load('https://mods.test/cancel.kat')\n    ~n + M.V\n}\nF(1)",
            new RunOptions
            {
                AllowedHosts = ["mods.test"],
                EvaluationCancellationToken = cancellation.Token,
                DownloadCode = async (_, token) =>
                {
                    acquired.SetResult();
                    await Task.Delay(Timeout.Infinite, token);
                    return "public V = 7";
                },
            });
        try
        {
            await acquired.Task.WaitAsync(TimeSpan.FromSeconds(10));
        }
        finally
        {
            cancellation.Cancel();
        }
        await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => run.WaitAsync(TimeSpan.FromSeconds(10)));
    }

    [Fact]
    public async Task DeferredUnit_AcquisitionFailurePrecedesGraceValidation()
    {
        var result = await KatLangEngine.RunAsync(
            "F(0) = 0\nF(n) = { M = load('https://mods.test/failure.kat')\n    ~n + M.V\n}\nF(1)",
            new RunOptions
            {
                AllowedHosts = ["mods.test"],
                DownloadCode = (_, _) => throw new InvalidOperationException("independent-download-failure"),
            });
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, error.Code);
        Assert.Contains("independent-download-failure", error.Message);
    }

    [Fact]
    public async Task SameModule_SeveralMaterializationsShareItsOwnBindingAndOneFetch()
    {
        var fetches = 0;
        const string source = "Apply(f) = f(2, 13)\nF(0) = 0\nF(n) = { M = load('https://mods.test/repeat.kat')\n" +
            "    Apply(M.P) + n\n}\nF(1), F(2)";
        var result = await KatLangEngine.RunAsync(source, new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = async (_, _) => { fetches++; await Task.Yield(); return "public P = y - ~x"; },
        });
        Assert.Equal(1, fetches);
        Assert.Equal("S[12, 13]", SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(result).Value));
    }

    [Fact]
    public void SharedOwnerDag_KeepsEachParentsCaptureClassification()
    {
        Algorithm.User Owner(params Expr[] output) => new(null, [], [], [], output);
        var marker = new Expr.Grace(new Expr.Resolve("x"), -1) { Span = new SourceSpan(1, 1, 1, 3) };
        var shared = Owner(new Expr.Binary(BinaryOp.Sub, new Expr.Resolve("y"), marker));
        var a = Owner(new Expr.Resolve("x"), new Expr.AlgorithmExpr(shared));
        var b = Owner(new Expr.AlgorithmExpr(shared));
        var root = Owner() with { Properties = [new Property("A", a), new Property("B", b)] };

        // The same AST node is a capture under A and an own inferred name under B.
        // A cache shared across these rewrite regions incorrectly gives both the (y) signature.
        var (detected, diagnostics) = ParameterDetector.Detect(root);
        var report = Assert.Single(diagnostics.ToArray());
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, report.Code);
        Assert.Contains("parameter of an enclosing algorithm", report.Message);
        var da = Assert.Single(detected.Properties, p => p.Name == "A").Value;
        var db = Assert.Single(detected.Properties, p => p.Name == "B").Value;
        var innerA = Assert.IsType<Expr.AlgorithmExpr>(da.Output[1]).Algorithm;
        var innerB = Assert.IsType<Expr.AlgorithmExpr>(db.Output[0]).Algorithm;
        Assert.Equal(["x"], da.Params);
        Assert.Empty(db.Params);
        Assert.Equal(["y"], innerA.Params);
        Assert.Equal(["x", "y"], innerB.Params);
        Assert.NotSame(innerA, innerB);
    }
}
