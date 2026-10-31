namespace KatLang.Tests;

/// <summary>
/// X-36 / Q-62 (2026-10-31): a written bare reference to <c>load</c> that no property, parameter or
/// opened member binds is the front-end error <see cref="DiagnosticCode.UnboundLoadReference"/>, never
/// a run-time <c>UnknownName</c>; a real binding named <c>load</c> stays an ordinary binding, and a
/// written call <c>load(...)</c> stays the spelling-recognized static module directive (MOD-07).
/// Module acquisition uses deterministic in-memory downloaders — no network.
/// </summary>
public class UnboundLoadReferenceTests
{
    private const string ModuleA = "https://katlang.org/bare-load/a.kat";
    private const string LoadProvider = "https://katlang.org/bare-load/provider.kat";
    private const string InvalidModule = "https://katlang.org/bare-load/invalid.kat";

    private sealed class CountingModules
    {
        private readonly Dictionary<string, string> _files = new(StringComparer.Ordinal)
        {
            [ModuleA] = "public A = 1",
            [LoadProvider] = "public load = 5",
            [InvalidModule] = "public X = load",
        };

        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int this[string url] => Fetches.GetValueOrDefault(url);

        public int Total => Fetches.Values.Sum();

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            Fetches[url] = this[url] + 1;
            return _files.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : throw new Exception($"404: {url}");
        }

        public RunOptions Options => new() { DownloadCode = Download };
    }

    private static string Display(RunResult result) => result.ToDisplayString().ReplaceLineEndings("\n");

    private static KatLangError AssertUnboundLoad(RunResult result, int line, int column)
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        var error = Assert.Single(failure.Errors);
        AssertUnboundLoad(error, line, column);
        return error;
    }

    private static void AssertUnboundLoad(KatLangError error, int line, int column)
    {
        Assert.Equal(KatLangErrorCode.UnboundLoadReference, error.Code);
        Assert.Equal(ParameterDetector.UnboundLoadReferenceMessage, error.Message);
        var span = Assert.NotNull(error.Span);
        Assert.Equal((line, column), (span.Start.Line, span.Start.Column));
    }

    // ── Unbound bare references are front-end errors ────────────────────────

    [Fact]
    public void HistoricalWitness_IsRejectedBeforeEvaluation_AtTheBareReference()
    {
        // Formerly: source processing passed and evaluation failed with `Unknown name: load` at [1:5].
        var result = KatLangEngine.Run("X = load\nX");
        var error = AssertUnboundLoad(result, line: 1, column: 5);
        Assert.Contains("load('url')", error.Message, StringComparison.Ordinal);

        var parsed = Parser.Parse("X = load\nX");
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UnboundLoadReference, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
    }

    [Theory]
    [InlineData("load", 1, 1)]
    [InlineData("load + 1", 1, 1)]
    [InlineData("X = (load)\nX", 1, 6)]
    [InlineData("X = ((load))\nX", 1, 7)]
    [InlineData("Unused = load\n1", 1, 10)]
    [InlineData("F(a) = 1\nF(load)", 2, 3)]
    [InlineData("Ignore(x) = 42\nIgnore(load)", 2, 8)]
    [InlineData("F(x) = load\n1", 1, 8)]
    [InlineData("F(x) = x + load\n1", 1, 12)]
    [InlineData("Y = \"{load}\"\n1", 1, 7)]
    [InlineData("Y = [load, 1]\n1", 1, 6)]
    [InlineData("F = {\n  G(y) = y\n  G(load)\n}\n1", 3, 5)]
    [InlineData("F(0) = 1\nF(n) = load\nF(0)", 2, 8)]
    [InlineData("Y = 5.load\n1", 1, 7)]
    public void UnboundBareUse_IsRejectedInSourceProcessing(string source, int line, int column)
    {
        AssertUnboundLoad(KatLangEngine.Run(source), line, column);
    }

    [Fact]
    public void UnboundBareUse_NeverBecomesAnInferredParameter()
    {
        // The directive placeholder keeps `load` out of inference: rejecting the reference must not
        // turn it into a parameter of F (or of the root) or change F's other parameters.
        var parsed = Parser.Parse("F = x + load\nF(1)");
        Assert.Equal(DiagnosticCode.UnboundLoadReference, Assert.Single(parsed.Diagnostics).Code);
        var f = Assert.Single(parsed.Root.Properties, property => property.Name == "F");
        Assert.Equal(["x"], f.Value.Params);
        Assert.Empty(parsed.Root.Params);
    }

    [Fact]
    public void EveryOccurrenceIsReported_InSourceOrder()
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("X = load\nY = load + load\n1"));
        Assert.Equal(3, failure.Errors.Count);
        AssertUnboundLoad(failure.Errors[0], 1, 5);
        AssertUnboundLoad(failure.Errors[1], 2, 5);
        AssertUnboundLoad(failure.Errors[2], 2, 12);
    }

    [Theory]
    [InlineData("directive", true)]
    [InlineData("directive", false)]
    [InlineData("member", true)]
    [InlineData("member", false)]
    [InlineData("runtime-receiver", true)]
    [InlineData("runtime-receiver", false)]
    public void SharedReference_InSpecialAndValuePositions_IsReportedOnce(string specialPosition, bool specialFirst)
    {
        // A suppressed occurrence cannot hide a later value use of the same host-DAG node.
        var reference = new Expr.Resolve("load") { Span = new SourceSpan(1, 1, 1, 5) };
        var member = new Algorithm.User(null, [], [],
            [new Property("load", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]), IsPublic: true)], []);
        Expr special = specialPosition switch
        {
            "directive" => new Expr.Call(reference, new OutputBundle([])),
            "member" => new Expr.DotCall(new Expr.AlgorithmExpr(member), "load", null) { LexicalFallback = reference },
            _ => new Expr.DotCall(new Expr.Resolve("receiver"), "load", null) { LexicalFallback = reference },
        };
        var root = new Algorithm.User(null, [], [], [],
            specialFirst ? [special, reference, reference] : [reference, reference, special]);

        var (_, diagnostics) = ParameterDetector.Detect(root);

        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.UnboundLoadReference, diagnostic.Code);
        Assert.Equal(reference.Span, diagnostic.Span);
    }

    [Fact]
    public void SharedBody_UnderBoundAndUnboundOwners_KeepsDistinctVerdicts()
    {
        var reference = new Expr.Resolve("load") { Span = new SourceSpan(1, 1, 1, 5) };
        var shared = new Algorithm.User(null, [], [], [], [reference]);
        var bound = new Algorithm.User(null, [], [], [], [new Expr.AlgorithmExpr(shared)]).WithParams(["load"]);
        var unbound = new Algorithm.User(null, [], [], [], [new Expr.AlgorithmExpr(shared)]);
        var root = new Algorithm.User(null, [], [],
            [new Property("Bound", bound), new Property("Unbound", unbound)], []);

        var (detected, diagnostics) = ParameterDetector.Detect(root);

        Assert.Equal(DiagnosticCode.UnboundLoadReference, Assert.Single(diagnostics).Code);
        var boundBody = Assert.IsType<Expr.AlgorithmExpr>(detected.Properties[0].Value.Output[0]).Algorithm;
        Assert.IsType<Expr.Param>(Assert.Single(boundBody.Output));
        var unboundBody = Assert.IsType<Expr.AlgorithmExpr>(detected.Properties[1].Value.Output[0]).Algorithm;
        Assert.IsType<Expr.Resolve>(Assert.Single(unboundBody.Output));
    }

    [Fact]
    public void GraceDiagnostic_PrecedesTheUnboundNameDiagnostic()
    {
        var parsed = Parser.Parse("~load");
        Assert.Equal([DiagnosticCode.InvalidGraceMarker, DiagnosticCode.UnboundLoadReference],
            parsed.Diagnostics.Select(diagnostic => diagnostic.Code));
    }

    [Fact]
    public void SharedGrace_FirstUsedAsAMember_StillReportsItsBareName()
    {
        var reference = new Expr.Resolve("load");
        var grace = new Expr.Grace(reference, 1);
        var member = new Algorithm.User(null, [], [],
            [new Property("load", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]), IsPublic: true)], []);
        var dot = new Expr.DotCall(new Expr.AlgorithmExpr(member), "load", null) { LexicalFallback = grace };
        var root = new Algorithm.User(null, [], [], [], [dot, grace, grace]);

        var (_, diagnostics) = ParameterDetector.Detect(root);

        Assert.Single(diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.UnboundLoadReference);
    }

    [Fact]
    public void DiagnosticCapacity_KeepsTheSameOrderedPrefix()
    {
        const string source = "load, load, load, load";
        var complete = Parser.Parse(source);
        var bounded = Parser.Parse(source, new RunOptions
        {
            SourceProcessingLimits = new SourceProcessingLimits { MaxDiagnosticCount = 2 },
        });

        Assert.Equal(4, complete.Diagnostics.Count);
        Assert.All(complete.Diagnostics, diagnostic => Assert.Equal(DiagnosticCode.UnboundLoadReference, diagnostic.Code));
        Assert.Equal(complete.Diagnostics.Take(2), bounded.Diagnostics.Take(2));
        Assert.Equal(3, bounded.Diagnostics.Count);
        Assert.Equal(DiagnosticCode.DiagnosticCountExceeded, bounded.Diagnostics[2].Code);
    }

    [Theory]
    [InlineData("Mk(x).Algorithm")]
    [InlineData("Mk.Algorithm")]
    public void FallbackThatBecomesCertainAfterLifting_IsValidated(string receiver)
    {
        // R keeps the input lifted from Mk, so it is a calculation, not a runtime link.
        AssertUnboundLoad(KatLangEngine.Run($"Mk(n) = n + 1\nR = {receiver}\nUnused = R.load\n1"), 3, 12);
    }

    [Fact]
    public void LateCertainFallback_KeepsDiagnosticOrderAndCapacity()
    {
        const string source = "Mk(n) = n + 1\nR = Mk.Algorithm\nUnused = R.load + load\n1";
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Equal(2, failure.Errors.Count);
        AssertUnboundLoad(failure.Errors[0], 3, 12);
        AssertUnboundLoad(failure.Errors[1], 3, 19);

        var bounded = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, new RunOptions
        {
            SourceProcessingLimits = new SourceProcessingLimits { MaxDiagnosticCount = 1 },
        }));
        Assert.Equal(2, bounded.Errors.Count);
        AssertUnboundLoad(bounded.Errors[0], 3, 12);
        Assert.Equal(KatLangErrorCode.DiagnosticCountExceeded, bounded.Errors[1].Code);
    }

    [Fact]
    public void ARealBinding_KeepsItsOwnDeclarationError()
    {
        var parsed = Parser.Parse("load(x) = missing + x\nload");
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, Assert.Single(parsed.Diagnostics).Code);
    }

    [Fact]
    public void ABindingInAnUnrelatedScope_DoesNotBindTheReference()
    {
        // `A`'s own `load` binds A's reference only; the root's reference is unbound.
        AssertUnboundLoad(KatLangEngine.Run("A = {\n  load = 1\n  X = load\n}\nB = load\nA.X"), line: 5, column: 5);
    }

    [Fact]
    public void InvalidEagerSource_HasNoRuntimeEffects()
    {
        // Rejected before evaluator entry: no output, no random draw, no evaluation charges.
        var result = KatLangEngine.Run(
            "Unused = load\nP = randomInt(0, 1000)\nP",
            new RunOptions { RandomSeed = 7, ObservePropertyValues = true });
        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Equal(KatLangErrorCode.UnboundLoadReference, Assert.Single(failure.Errors).Code);
        Assert.Null(result.PropertyObservations);
    }

    // ── Real bindings named load are ordinary ───────────────────────────────

    [Theory]
    [InlineData("load(x) = x + 1\nmap([1, 2], load)", "[2, 3]")]
    [InlineData("load(x) = x + 1\nF(f) = f(5)\nF(load)", "6")]
    [InlineData("load = 3\nload + 1", "4")]
    [InlineData("F(load) = load + 1\nF(2)", "3")]
    [InlineData("F(load) = 1\nF(2)", "1")]
    [InlineData("X = load\nload = 4\nX", "4")]
    [InlineData("A = { X = load }\nload = 4\nA.X", "4")]
    [InlineData("load = 1\nA = {\n  load = 2\n  X = load\n}\nA.X + load", "3")]
    [InlineData("load(x) = x * 2\nA = load\nA(4)", "8")]
    [InlineData("M = { public load = 7 }\nM.load", "7")]
    [InlineData("M = { public load(x) = x * 3 }\nM.load(3)", "9")]
    [InlineData("M = { public load = 7 }\nY = M.load\n1", "1")]
    [InlineData("G(x) = x.load\n1", "1")]
    [InlineData("Cap(meta op) = op\nInc(x) = x + 1\nR = Cap(Inc(1)).Algorithm\nUnused = R.load\n1", "1")]
    [InlineData("X = 'load'\n# load\nX", "load")]
    public async Task RealBinding_KeepsOrdinaryBehavior_WithAndWithoutLoadingCapability(string source, string expected)
    {
        Assert.Equal(expected, Display(Assert.IsType<RunResult.Success>(KatLangEngine.Run(source))));

        var modules = new CountingModules();
        Assert.Equal(expected, Display(Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, modules.Options))));
        Assert.Equal(0, modules.Total);
    }

    [Theory]
    [InlineData("open M\nM = { public load = 5 }\nload + 1", "6")]
    [InlineData("open M\nM = { public load(x) = x * 10 }\nG(f) = f(2)\nG(load)", "20")]
    [InlineData("open M, M\nM = { public load = 5 }\nload", "5")]
    [InlineData("open { public load = 5 }\nload", "5")]
    [InlineData("open M\nM = { public load = 5 }\nF = {\n  load = 1\n  load\n}\nF", "1")]
    [InlineData("M = { public load = 5 }\nF = {\n  open M\n  load + 1\n}\nF", "6")]
    public void OpenedBinding_IsJudgedByRuntimeVisibility_NotHiddenByThePlaceholder(string source, string expected)
    {
        Assert.Equal(expected, Display(Assert.IsType<RunResult.Success>(KatLangEngine.Run(source))));
    }

    [Fact]
    public void AmbiguousOpenedBinding_KeepsItsExistingResolutionResult()
    {
        var result = KatLangEngine.Run("open M, N\nM = { public load = 5 }\nN = { public load = 6 }\nload");
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
        Assert.Equal(KatLangErrorCode.AmbiguousOpen, error.Code);
    }

    // ── The written directive stays spelling-recognized ─────────────────────

    [Theory]
    [InlineData("load(x) = x + 1\nload(2)", 2, 1)]
    [InlineData("F(load) = load(2)\nF(1)", 1, 11)]
    [InlineData("X = load(1 + 1)\n1", 1, 5)]
    [InlineData("X = (load)('https://katlang.org/a.kat')\n1", 1, 6)]
    [InlineData("load(x) = x\nX = (load)(2)\n1", 2, 6)]
    // A missing module makes the elaboration provisional: its pass diagnostics, this one
    // included, are withheld behind the directive's own report.
    [InlineData("X = load\nY = load('https://katlang.org/a.kat')\n1", 2, 5)]
    public void DirectlySpelledDirective_IsInterceptedDespiteShadowing_WithoutLoading(string source, int line, int column)
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.LoadElaborationUnavailable, error.Code);
        var span = Assert.NotNull(error.Span);
        Assert.Equal((line, column), (span.Start.Line, span.Start.Column));
    }

    [Theory]
    [InlineData("load(x) = x + 1\nload(2)")]
    [InlineData("F(load) = load(2)\nF(1)")]
    [InlineData("X = load(1 + 1)\n1")]
    [InlineData("X = 1 + load('https://katlang.org/bare-load/a.kat')\nX")]
    [InlineData("X = load('https://katlang.org/bare-load/a.kat', 2)\n1")]
    public async Task DirectlySpelledDirective_KeepsItsDirectiveDiagnostic_WithLoading(string source)
    {
        var modules = new CountingModules();
        var failure = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, modules.Options));
        Assert.Contains(failure.Errors, error => error.Code == KatLangErrorCode.InvalidLoadDirective);
        Assert.DoesNotContain(failure.Errors, error => error.Code == KatLangErrorCode.UnboundLoadReference);
        Assert.Equal(0, modules.Total);
    }

    // ── Loading capability and loaded units ─────────────────────────────────

    [Fact]
    public async Task UnboundBareUse_WithADownloader_IsRejectedWithoutAcquisition()
    {
        var modules = new CountingModules();
        AssertUnboundLoad(await KatLangEngine.RunAsync("X = load\nX", modules.Options), line: 1, column: 5);
        Assert.Equal(0, modules.Total);
    }

    [Fact]
    public async Task ValidLoading_StillMaterializesTheModule()
    {
        var modules = new CountingModules();
        Assert.Equal("2", Display(Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync($"M = load('{ModuleA}')\nM.A + 1", modules.Options))));
        Assert.Equal(1, modules[ModuleA]);

        modules = new CountingModules();
        Assert.Equal("1", Display(Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync($"open '{ModuleA}'\nM = load('{ModuleA}')\nA * M.A", modules.Options))));
        Assert.Equal(1, modules[ModuleA]);
    }

    [Fact]
    public async Task ImportedBinding_ResolvesTheBareName()
    {
        var modules = new CountingModules();
        Assert.Equal("6", Display(Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync($"open '{LoadProvider}'\nload + 1", modules.Options))));
        Assert.Equal(1, modules[LoadProvider]);
    }

    [Fact]
    public async Task RequiredLoadedModule_WithAnUnboundBareUse_CannotRun()
    {
        // The module's `X = load` is reported for the module even though nothing reads X. Module
        // content carries no locations, so it is positioned at the import site: the declaration of
        // the property whose value holds the load (ImportSite.OfProperty).
        var modules = new CountingModules();
        var source = $"M = load('{InvalidModule}')\n1";
        AssertUnboundLoad(await KatLangEngine.RunAsync(source, modules.Options), line: 1, column: 1);
        Assert.Equal(1, modules[InvalidModule]);

        modules = new CountingModules();
        var opened = Assert.IsType<RunResult.ParseFailure>(
            await KatLangEngine.RunAsync($"open '{InvalidModule}'\n1", modules.Options));
        Assert.Equal(KatLangErrorCode.UnboundLoadReference, Assert.Single(opened.Errors).Code);
        Assert.Equal(1, modules[InvalidModule]);
    }

    [Fact]
    public async Task DeferredUnit_IsValidatedOnlyWhenSelected()
    {
        var branch = $"F(0) = 42\nF(n) = {{\n  open '{ModuleA}'\n  Unread = load\n  A\n}}\n";

        // Never selected: no acquisition and no early diagnostic for its unresolved source.
        var modules = new CountingModules();
        Assert.Equal("42", Display(Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(branch + "F(0)", modules.Options))));
        Assert.Equal(0, modules.Total);

        // Selected: the unread invalid sibling rejects the materialized unit at its written span,
        // through the existing deferred EvalFailure provenance (the selecting call's context).
        modules = new CountingModules();
        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(branch + "F(1)", modules.Options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UnboundLoadReference, error.Code);
        Assert.Equal("while evaluating call to F: " + ParameterDetector.UnboundLoadReferenceMessage, error.Message);
        var span = Assert.NotNull(error.Span);
        Assert.Equal((4, 12), (span.Start.Line, span.Start.Column));
        Assert.Equal(1, modules[ModuleA]);
    }

    [Fact]
    public async Task DeferredUnit_WithAnImportedLoadBinding_IsNotValidatedPrematurely()
    {
        var branch = $"F(0) = 42\nF(n) = {{\n  open '{LoadProvider}'\n  load + n\n}}\n";
        var modules = new CountingModules();
        Assert.Equal("42", Display(Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(branch + "F(0)", modules.Options))));
        Assert.Equal(0, modules.Total);
        Assert.Equal("6", Display(Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(branch + "F(1)", modules.Options))));
        Assert.Equal(1, modules[LoadProvider]);
    }

    // ── The low-level evaluator keeps its defensive runtime behavior ────────

    [Fact]
    public void HostBuiltAst_KeepsTheRuntimeUnknownName()
    {
        var root = new Algorithm.User(null, [], [], [], [new Expr.Resolve("load")]);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.True(result.IsError);
        Assert.Equal("load", Assert.IsType<EvalError.UnknownName>(result.Error).Name);
    }
}
