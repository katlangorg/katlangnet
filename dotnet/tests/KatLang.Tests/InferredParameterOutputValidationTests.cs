using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// AN ALGORITHM WITH INFERRED PARAMETERS AND NO OUTPUT IS A FRONT-END ERROR (X-07, October 2026).
///
/// <para>An algorithm that has parameters must define an output (<see cref="EvalError.ExplicitParametersRequireOutput"/>;
/// Lean <c>validateExplicitParamOutputInvariant</c>, run before evaluation). The parser enforces it on
/// every WRITTEN parameter list, but an open body's parameters are final only after inference — the
/// names its definition uses that nothing in scope declares, and the arguments the callables it uses
/// need — so <c>F = { a, b = x, 1 }</c> / <c>trace(5)</c> used to pass the front end and fail as an
/// UNPOSITIONED evaluation error of the whole program, reading "declares explicit parameters". The
/// front end now re-checks the completed signatures (<see cref="InferredParameterOutputValidator"/>)
/// with the evaluator gate's own test and reports the same error kind before evaluation: positioned
/// at the first occurrence of the first parameter inferred from a written name, else at the
/// definition (the forwarded parameter of a lifted callable has no occurrence of its own), else at
/// the import site of the module content it lies in; worded for inferred parameters; never twice.
/// A deferred module region's provisional body is judged when it materializes — not by the evaluator
/// gate at the start of the run, which used to reject a program whose deferred module supplied the
/// very name it took for a parameter.</para>
/// </summary>
public sealed class InferredParameterOutputValidationTests
{
    private const string Canonical = "F = { a, b = x, 1 }\ntrace(5)";

    private const string CanonicalMessage =
        "This algorithm takes the implicit parameter 'x' but does not define an output. "
        + "Implicit parameters are inferred from what an algorithm's definition uses (a name that nothing in scope declares, "
        + "or an argument that a callable it uses needs), and an algorithm with parameters must define an output. "
        + "Define an algorithm output, or, if the algorithm is only a container, declare the names its definition uses "
        + "and call the callables it uses with explicit arguments, so that it takes no parameters.";

    private const string ExplicitMessage =
        "This algorithm declares explicit parameters but does not define an output. Remove the algorithm parameters if it is only a container, declare parameters on the relevant property instead, or define an algorithm output.";

    private static Diagnostic SingleOutputDiagnostic(string source)
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError(source);
        return Assert.Single(diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.ExplicitParametersRequireOutput);
    }

    [Fact]
    public async Task TheCanonicalProgram_IsAPositionedFrontEndError_OnEveryRoute_AndNothingRuns()
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(Canonical);

        Assert.Equal("parse", observation.Kind);
        Assert.Equal([$"ExplicitParametersRequireOutput: {CanonicalMessage} @ [1:14, 1:15)"], observation.Errors);
        Assert.Empty(observation.HostCalls);

        var diagnostic = Assert.Single(Parser.Parse(Canonical).Diagnostics);
        Assert.Equal(DiagnosticCode.ExplicitParametersRequireOutput, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(new SourceSpan(1, 14, 1, 15), diagnostic.Span);

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(Canonical));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.ExplicitParametersRequireOutput, error.Code);
        Assert.DoesNotContain("declares explicit parameters", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("F(y) = { public V = 1 }\ntrace(5)", 1, 3, 1, 4)]
    [InlineData("F(x) = {\n  public V = 1\n}\ntrace(5)", 1, 3, 1, 4)]
    [InlineData("F(*xs) = { public V = 1 }\ntrace(5)", 1, 4, 1, 6)]
    public async Task AWrittenParameterList_KeepsItsParseTimeDiagnostic_Once(string source, int line, int column, int endLine, int endColumn)
    {
        var diagnostic = SingleOutputDiagnostic(source);
        Assert.Equal(ExplicitMessage, diagnostic.Message);
        Assert.Equal(new SourceSpan(line, column, endLine, endColumn), diagnostic.Span);

        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", observation.Kind);
        Assert.Single(observation.Errors);
        Assert.Empty(observation.HostCalls);
    }

    /// <summary>
    /// Every way an open body gets parameters, wherever it is written — the position is where the
    /// inference is written (the first parameter's first occurrence, in signature order), or the
    /// definition when the first parameter was forwarded to a callable it uses.
    /// </summary>
    [Theory]
    // One inferred name, from a deconstruction's right-hand side.
    [InlineData("F = {\n  a, b = x, 1\n}\ntrace(5)", 2, 10, "the implicit parameter 'x'")]
    // Several names: the first in signature order — Grace reorders it.
    [InlineData("F = { a, b = x, y }\ntrace(5)", 1, 14, "the implicit parameters 'x' and 'y'")]
    [InlineData("F = { a, b = y - ~x, 1 }\ntrace(5)", 1, 19, "the implicit parameters 'x' and 'y'")]
    [InlineData("F = { a, b, c = x, y, z }\ntrace(5)", 1, 17, "the implicit parameters 'x', 'y', and 'z'")]
    [InlineData("F = { a, b, c, d = w, x, y, z }\ntrace(5)", 1, 20, "the implicit parameters 'w', 'x', 'y', and 1 more")]
    // Formula lifting forwards a callee's parameter: no occurrence of its own, so the definition.
    [InlineData("G(p) = p + 1\nF = { a, b = G + 0, 1 }\ntrace(5)", 2, 1, "the implicit parameter 'p'")]
    [InlineData("G(p) = p + 1\nF = { a, b = x + G, 1 }\ntrace(5)", 2, 14, "the implicit parameters 'x' and 'p'")]
    // Nested algorithms nothing reads, a branch body's and a closed body's members, a block literal,
    // an inline open target's member.
    [InlineData("Outer = {\n  F = { a, b = x, 1 }\n  5\n}\ntrace(Outer)", 2, 16, "the implicit parameter 'x'")]
    [InlineData("F(0) = {\n  G = { a, b = x, 1 }\n  5\n}\nF(n) = n\ntrace(F(1))", 2, 16, "the implicit parameter 'x'")]
    [InlineData("F(y) = {\n  G = { a, b = x, 1 }\n  y\n}\ntrace(F(1))", 2, 16, "the implicit parameter 'x'")]
    [InlineData("Apply(f) = 7\ntrace(Apply({ a, b = x, 1 }))", 2, 22, "the implicit parameter 'x'")]
    [InlineData("open { public M = { a, b = x, 1 } }\ntrace(5)", 1, 28, "the implicit parameter 'x'")]
    // The program root, which no definition writes: its first written row when nothing else.
    [InlineData("a, b = x, 1", 1, 8, "the implicit parameter 'x'")]
    [InlineData("G(p) = p + 1\na, b = G + 0, 1", 2, 8, "the implicit parameter 'p'")]
    public async Task InferredParameters_AreReportedBeforeEvaluation_WhereTheirInferenceIsWritten(
        string source, int line, int column, string parameters)
    {
        var diagnostic = SingleOutputDiagnostic(source);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(new SourcePosition(line, column), diagnostic.Span?.Start);
        Assert.StartsWith($"This algorithm takes {parameters} but does not define an output.", diagnostic.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("explicit parameters", diagnostic.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("This algorithm declares", diagnostic.Message, StringComparison.Ordinal);

        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", observation.Kind);
        Assert.Empty(observation.HostCalls);
    }

    [Fact]
    public async Task AWrittenAndAnInferredViolation_AreEachReportedOnce()
    {
        const string Source = "F(p) = { public V = 1 }\nG = { a, b = x, 1 }\ntrace(5)";
        var diagnostics = SourceProvenance.ExpectFrontEndError(Source);
        Assert.Equal(2, diagnostics.Count);
        Assert.All(diagnostics, static diagnostic => Assert.Equal(DiagnosticCode.ExplicitParametersRequireOutput, diagnostic.Code));
        Assert.Equal(ExplicitMessage, diagnostics[0].Message);
        Assert.Equal(new SourceSpan(1, 3, 1, 4), diagnostics[0].Span);
        Assert.StartsWith("This algorithm takes the implicit parameter 'x'", diagnostics[1].Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(2, 14, 2, 15), diagnostics[1].Span);

        var observation = await SixRouteAgreement.OnEveryRouteAsync(Source);
        Assert.Equal(2, observation.Errors.Count);
        Assert.Empty(observation.HostCalls);
    }

    [Theory]
    // A parameterless container, a function with an output, and a callee that accepts zero supplied
    // arguments (its bare name is its cached value, never lifted: the container takes no parameter).
    [InlineData("A = { public X = 1 }\ntrace(A.X)", "1")]
    [InlineData("F = { a, b = x, 1\n  a + b }\ntrace(F(2))", "3")]
    [InlineData("Cnt(*xs) = xs.count\nF = { a, b = Cnt + 0, 1 }\ntrace(F.a)", "0")]
    public async Task ContainersFunctionsAndZeroSupplyCallees_StayValid(string source, string value)
    {
        SourceProvenance.ParseValid(source);
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", observation.Kind);
        Assert.Equal(value, observation.Value);
        Assert.Equal([$"trace({value})"], observation.HostCalls);
    }

    [Fact]
    public void TheEditorModel_BuildsForTheRejectedProgram_AndForARecoveryTree()
    {
        var model = Semantics.SemanticModelBuilder.Build(Parser.Parse(Canonical));
        var property = Assert.Single(model.FindProperties("F"));
        Assert.Equal(new SourceSpan(1, 1, 1, 2), property.Declaration?.Span);
        Assert.Equal(["x"], property.Parameters.Select(static parameter => parameter.DisplayName));

        const string Recovery = "F = { a, b = x, 1 }\nG = (1, 2]\ntrace(5)";
        var parsed = Parser.Parse(Recovery);
        Assert.Contains(parsed.Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.UnexpectedToken);
        var output = Assert.Single(parsed.Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.ExplicitParametersRequireOutput);
        Assert.Equal(new SourceSpan(1, 14, 1, 15), output.Span);
        Assert.NotNull(Semantics.SemanticModelBuilder.Build(parsed));
    }

    [Fact]
    public void AHostBuiltTree_WithNoPosition_IsLeftToTheEvaluatorGate()
    {
        // A parameterized, output-less algorithm nothing positions (no written occurrence, definition,
        // or import site): the front-end pass reports nothing, and the evaluator's pre-evaluation gate
        // still rejects the tree before evaluation, as it always has.
        var inferred = new Algorithm.User(null, Algorithm.NormalParameters(["x"]), [], [new Property("V", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))], []);
        var root = new Algorithm.User(null, [], [], [new Property("F", inferred)], [new Expr.Num(5)]);

        var diagnostics = new DiagnosticBag();
        InferredParameterOutputValidator.ValidateProgram(root, diagnostics);
        Assert.Empty(diagnostics);

        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.True(result.IsError);
        Assert.IsType<EvalError.ExplicitParametersRequireOutput>(result.Error);
    }

    // ── Imported and deferred module content ────────────────────────────────────────────

    private const string Inferred = "https://mods.test/inferred.kat";
    private const string Plain = "https://mods.test/plain.kat";
    private const string SuppliesQ = "https://mods.test/supplies-q.kat";

    private static RunOptions ModuleOptions(bool suspending, List<string>? log = null)
    {
        var modules = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [Inferred] = "public F = { a, b = x, 1 }\npublic K = 1",
            [Plain] = "public K = 7",
            [SuppliesQ] = "public q = 3\npublic K = 7",
        };
        log ??= [];
        return new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (url, _) => ValueTask.FromResult(modules[url]),
            HostOperations = suspending
                ? HostOperations.Create(HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); lock (log) log.Add($"trace({SixRouteAgreement.Neutral(args[0])})"); return args[0]; }, "x"))
                : HostOperations.Create(HostOperation.Create("trace", (args, _) => { lock (log) log.Add($"trace({SixRouteAgreement.Neutral(args[0])})"); return args[0]; }, "x")),
        };
    }

    [Theory]
    [InlineData($"M = load('{Inferred}')\ntrace(5)", 1, 1, 1, 2)]
    [InlineData($"open '{Inferred}'\ntrace(K)", 1, 6, 1, 38)]
    public async Task ImportedContent_IsReportedAtItsImportSite(string source, int line, int column, int endLine, int endColumn)
    {
        foreach (var suspending in new[] { false, true })
        {
            var log = new List<string>();
            var failure = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, ModuleOptions(suspending, log)));
            var error = Assert.Single(failure.Errors);
            Assert.Equal(KatLangErrorCode.ExplicitParametersRequireOutput, error.Code);
            Assert.StartsWith("This algorithm takes the implicit parameter 'x'", error.Message, StringComparison.Ordinal);
            Assert.Equal(new SourceSpan(line, column, endLine, endColumn), error.Span);
            Assert.Empty(log);
        }
    }

    /// <summary>
    /// A deferred branch body is judged when its region materializes: a name its module supplies is
    /// no parameter (the evaluator gate used to reject this program at the start of every run, the
    /// branch selected or not), a branch never selected cannot fail, and a selected body that IS
    /// invalid fails with the positioned front-end diagnostic.
    /// </summary>
    [Theory]
    [InlineData(SuppliesQ, "K + n + G.a", "F(1)", "ok", "11", null)]
    [InlineData(SuppliesQ, "K + n", "F(0)", "ok", "0", null)]
    [InlineData(Plain, "K + n", "F(0)", "ok", "0", null)]
    [InlineData(Plain, "K + n", "F(1)", "err", null, "[4:16, 4:17)")]
    public async Task ADeferredBody_IsJudgedWhenItMaterializes(string module, string row, string call, string kind, string? value, string? span)
    {
        var source = $"F(0) = 0\nF(n) = {{\n  open '{module}'\n  G = {{ a, b = q, 1 }}\n  {row}\n}}\ntrace({call})";

        foreach (var suspending in new[] { false, true })
        {
            var log = new List<string>();
            var result = await KatLangEngine.RunAsync(source, ModuleOptions(suspending, log));
            if (kind == "ok")
            {
                var success = Assert.IsType<RunResult.Success>(result);
                Assert.Equal(value, SixRouteAgreement.Neutral(success.Value));
                Assert.Equal([$"trace({value})"], log);
                continue;
            }

            var failure = Assert.IsType<RunResult.EvalFailure>(result);
            var error = Assert.Single(failure.Errors);
            Assert.Equal(KatLangErrorCode.ExplicitParametersRequireOutput, error.Code);
            Assert.Contains("This algorithm takes the implicit parameter 'q' but does not define an output.", error.Message, StringComparison.Ordinal);
            Assert.Equal(span, error.Span?.ToString());
            Assert.Empty(log);
        }
    }

    [Fact]
    public async Task ADeferredModuleWithAnInferredViolation_FailsAtItsImportSite_WhenSelected()
    {
        var source = $"F(0) = 0\nF(n) = {{\n  open '{Inferred}'\n  K + n\n}}\ntrace(F(1))";
        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source, ModuleOptions(suspending: false)));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.ExplicitParametersRequireOutput, error.Code);
        Assert.Contains("This algorithm takes the implicit parameter 'x'", error.Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(3, 8, 3, 40), error.Span);
    }
}
