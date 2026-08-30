namespace KatLang.Tests;

/// <summary>
/// M6 front-end elaboration boundary: the individual elaboration passes
/// (<see cref="ParameterDetector"/>, <see cref="ImplicitArgumentResolver"/>) are
/// implementation stages of the one authoritative pipeline
/// (<see cref="FrontEndPipeline"/>), not a host-composable API. A host that ran
/// only Detect → Resolve obtained an AST whose <see cref="Property.Exposure"/>
/// metadata was never finalized by <see cref="PropertyExposureResolver"/> — every
/// property kept the constructor default <see cref="PropertyExposure.Exported"/> —
/// and the evaluator trusts that stored flag, so the partial route observably
/// diverged from the engine (most sharply: <c>open</c> exposed a local-only
/// property the language hides). Since v0.8.187 the passes are internal, and
/// since v0.8.188 the same rule covers <see cref="ModuleLoader"/> — load
/// elaboration alone is an even more incomplete stage (section 4). This suite
/// pins the authoritative behavior, keeps the divergences visible as the reason
/// the routes must stay internal, and — by compiling against the internal
/// passes at all — proves test consumers keep access through the existing
/// <c>InternalsVisibleTo</c> friend mechanism.
/// </summary>
public class FrontEndElaborationBoundaryTests
{
    /// <summary>
    /// `Value` is written public but captures the ancestor-owned parameter `a`,
    /// so the authoritative pipeline classifies it
    /// <see cref="PropertyExposure.LocalOnlyCapturedAncestorParameters"/> and
    /// `open Lib` must not expose it: the engine fails the bare `Value` lookup.
    /// </summary>
    private const string OpenExposureProgram = """
        F(a) = {
            Lib = {
                public Value = a + 1
            }
            Inner = {
                open Lib
                Value
            }
            Inner
        }
        F(41)
        """;

    /// <summary>
    /// Structural dot access refuses local-only properties by reading the stored
    /// exposure flag; the authoritative engine reports the dedicated
    /// <see cref="EvalError.LocalOnlyProperty"/> error.
    /// </summary>
    private const string DotAccessProgram = """
        Algo(x) = {
            Prop = x + 1
            x
        }
        Algo.Prop
        """;

    /// <summary>
    /// The exact route a host could publicly compose before v0.8.187: raw tree →
    /// parameter detection → implicit-argument resolution, with NO property
    /// exposure finalization. Kept callable here through friend access only.
    /// </summary>
    private static Algorithm ElaborateWithoutExposureFinalization(string source)
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        var (detected, diagnostics) = ParameterDetector.Detect(root);
        Assert.DoesNotContain(diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        return ImplicitArgumentResolver.Resolve(detected);
    }

    private static Property NestedProperty(Algorithm root, params string[] path)
    {
        var current = root;
        Property? property = null;
        foreach (var name in path)
        {
            property = Assert.Single(current.Properties, candidate => candidate.Name == name);
            current = property.Value;
        }

        return property!;
    }

    // ── 1. The authoritative pipeline finalizes local-only exposure ──────────

    [Fact]
    public void AuthoritativeParse_FinalizesCapturedExposure_AndOpenHidesTheProperty()
    {
        var parsed = SourceProvenance.ParseValid(OpenExposureProgram);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            NestedProperty(parsed.Root, "F", "Lib", "Value").Exposure);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(OpenExposureProgram));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UnknownName, error.Code);
    }

    [Fact]
    public void AuthoritativeParse_FinalizesCapturedExposure_AndDotAccessReportsLocalOnly()
    {
        var parsed = SourceProvenance.ParseValid(DotAccessProgram);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            NestedProperty(parsed.Root, "Algo", "Prop").Exposure);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(DotAccessProgram));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, error.Code);
    }

    // ── 2. The concrete divergence that motivated internalizing the passes ──

    [Fact]
    public void PartialElaboration_LeavesExposureUnfinalized_SoOpenExposesTheLocalOnlyProperty()
    {
        var partialRoot = ElaborateWithoutExposureFinalization(OpenExposureProgram);

        // The exposure pass never ran: the flag is still the constructor default.
        Assert.Equal(
            PropertyExposure.Exported,
            NestedProperty(partialRoot, "F", "Lib", "Value").Exposure);

        // The evaluator trusts the stored flag, so the partially elaborated tree
        // SUCCEEDS where the authoritative engine correctly fails: `open Lib`
        // exposes the local-only `Value`, and F(41) returns 42.
        var partialRun = Evaluator.Run(new Expr.AlgorithmExpr(partialRoot));
        Assert.False(partialRun.IsError);
        Assert.Equal(new Result.Atom(42), partialRun.Value);

        Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(OpenExposureProgram));
    }

    [Fact]
    public void PartialElaboration_LeavesExposureUnfinalized_SoDotAccessMissesTheLocalOnlyRefusal()
    {
        var partialRoot = ElaborateWithoutExposureFinalization(DotAccessProgram);

        Assert.Equal(
            PropertyExposure.Exported,
            NestedProperty(partialRoot, "Algo", "Prop").Exposure);

        // The dot access is admitted (wrong) and only then fails on the unbound
        // parameter — a different structured failure than the engine's
        // authoritative LocalOnlyProperty refusal.
        var partialRun = Evaluator.Run(new Expr.AlgorithmExpr(partialRoot));
        Assert.True(partialRun.IsError);
        Assert.Equal(KatLangErrorCode.UnknownName, KatLangError.FromEvalError(partialRun.Error).Code);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(DotAccessProgram));
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, Assert.Single(failure.Errors).Code);
    }

    // ── 3. The supported public entry points perform COMPLETE elaboration ────

    /// <summary>
    /// One parse, all three passes observable on its output: parameter detection
    /// (an unresolved name became an implicit parameter), implicit-argument
    /// resolution (a bare reference to a parametrized algorithm became an
    /// explicit call), and property-exposure finalization (a capturing property
    /// is local-only). Guards against a future entry point quietly skipping a
    /// stage the way the removed public composition could.
    /// </summary>
    [Fact]
    public void PublicParse_RunsDetectionResolutionAndExposureFinalization()
    {
        var parsed = SourceProvenance.ParseValid("""
            Algo(x) = {
                Prop = x + 1
                x
            }
            Doubled = Algo + Algo
            seed
            """);

        // Parameter detection: the unresolved `seed` was promoted to an
        // implicit root parameter and its occurrence rewritten to a Param.
        Assert.Contains(parsed.Root.Parameters, parameter => parameter.Name == "seed");
        Assert.Contains(parsed.Root.Output, row => row is Expr.Param { Name: "seed" });

        // Implicit-argument resolution: the bare value-position references to
        // the parametrized `Algo` became explicit calls, lifting `x` into
        // Doubled's parameter list.
        var doubled = NestedProperty(parsed.Root, "Doubled").Value;
        Assert.Contains("x", doubled.Params);
        var binary = Assert.IsType<Expr.Binary>(Assert.Single(doubled.Output));
        var call = Assert.IsType<Expr.Call>(binary.Left);
        Assert.IsType<Expr.Param>(Assert.Single(call.Args));

        // Property-exposure finalization ran on the same tree.
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            NestedProperty(parsed.Root, "Algo", "Prop").Exposure);
    }

    [Fact]
    public async Task AsyncParse_FinalizesExposureLikeSynchronousParse()
    {
        var parsedAsync = await Parser.ParseAsync(OpenExposureProgram);
        Assert.False(parsedAsync.HasErrors);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            NestedProperty(parsedAsync.Root, "F", "Lib", "Value").Exposure);

        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(OpenExposureProgram));
        Assert.Equal(KatLangErrorCode.UnknownName, Assert.Single(failure.Errors).Code);
    }

    // ── 4. Load elaboration alone is even more incomplete ────────────────────

    private const string ModuleUrl = "https://katlang.org/m6/exposure-lib.kat";

    private const string LoadingProgram = """
        open 'https://katlang.org/m6/exposure-lib.kat'
        Run(41)
        """;

    /// <summary>
    /// The loaded module is the <see cref="OpenExposureProgram"/> witness wrapped
    /// as a public member, so the same local-only classification must reach it
    /// THROUGH the module boundary in the authoritative pipeline.
    /// </summary>
    private const string LoadedModuleSource = """
        public Run(a) = {
            Lib = {
                public Value = a + 1
            }
            Inner = {
                open Lib
                Value
            }
            Inner
        }
        """;

    private const string IncrementModuleUrl = "https://katlang.org/m6/inc-lib.kat";

    private const string IncrementLoadingProgram = """
        open 'https://katlang.org/m6/inc-lib.kat'
        Increment(4)
        """;

    private const string IncrementModuleSource = "public Increment(n) = n + 1";

    private const string ImplicitModuleUrl = "https://katlang.org/m6/implicit-lib.kat";

    private const string ImplicitLoadingProgram = """
        open 'https://katlang.org/m6/implicit-lib.kat'
        Twice(4)
        """;

    private const string ImplicitModuleSource = """
        public Increment(n) = n + 1
        public Twice(n) = Increment + Increment
        """;

    private static ValueTask<string> DownloadModule(string url, CancellationToken cancellationToken)
        => url switch
        {
            ModuleUrl => ValueTask.FromResult(LoadedModuleSource),
            IncrementModuleUrl => ValueTask.FromResult(IncrementModuleSource),
            ImplicitModuleUrl => ValueTask.FromResult(ImplicitModuleSource),
            _ => ValueTask.FromException<string>(new InvalidOperationException($"unexpected URL: {url}")),
        };

    private static Property SplicedModuleProperty(Algorithm root, params string[] path)
    {
        var moduleAlgorithm = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(root.Opens)).Algorithm;
        return NestedProperty(moduleAlgorithm, path);
    }

    [Fact]
    public async Task AuthoritativeAsyncParse_FinalizesExposureInsideLoadedModules()
    {
        var options = new RunOptions { DownloadCode = DownloadModule };

        var parsed = await Parser.ParseAsync(LoadingProgram, options);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            SplicedModuleProperty(parsed.Root, "Run", "Lib", "Value").Exposure);

        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(LoadingProgram, options));
        Assert.Equal(KatLangErrorCode.UnknownName, Assert.Single(failure.Errors).Code);
    }

    /// <summary>
    /// The load-elaboration-only route a host could publicly compose before
    /// v0.8.188 (<see cref="ModuleLoader"/> construction +
    /// <see cref="ModuleLoader.ElaborateAsync"/>, kept callable here through
    /// friend access only): it splices modules but runs NO parameter detection,
    /// NO implicit-argument resolution, and NO property-exposure resolution —
    /// strictly less of the pipeline than the Detect → Resolve composition
    /// removed in v0.8.187. Here the missing DETECTION pass is the crispest
    /// observable: the spliced module's declared parameter reference is still a
    /// raw <see cref="Expr.Resolve"/> (never rewritten to
    /// <see cref="Expr.Param"/>), so the simplest parametrized module function
    /// FAILS on the partially elaborated tree where the authoritative engine
    /// computes it — and its exposure metadata equally stays at the constructor
    /// default, the v0.8.187 hole, one stage earlier.
    /// </summary>
    [Fact]
    public async Task PartialLoadElaboration_SkipsEveryFinalizationPass_SoModuleFunctionsDoNotEvenBindParameters()
    {
        var syntaxRoot = SourceProvenance.ParseSyntaxValidRoot(IncrementLoadingProgram);

        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(diagnostics, DownloadModule);
        var loadedOnly = await loader.ElaborateAsync(syntaxRoot);
        Assert.DoesNotContain(diagnostics, d => d.Severity == DiagnosticSeverity.Error);

        // The un-elaborated smoking gun: `n` inside `Increment(n) = n + 1` is
        // still a Resolve node, so runtime lexical lookup cannot see the bound
        // parameter.
        var increment = SplicedModuleProperty(loadedOnly, "Increment");
        var body = Assert.IsType<Expr.Binary>(Assert.Single(increment.Value.Output));
        Assert.IsType<Expr.Resolve>(body.Left);

        var partialRun = Evaluator.Run(new Expr.AlgorithmExpr(loadedOnly));
        Assert.True(partialRun.IsError);
        Assert.Equal(KatLangErrorCode.UnknownName, KatLangError.FromEvalError(partialRun.Error).Code);

        var authoritative = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync(IncrementLoadingProgram, new RunOptions { DownloadCode = DownloadModule }));
        Assert.Equal("5", authoritative.ToDisplayString());
    }

    [Fact]
    public async Task AuthoritativeAsyncParse_FinalizesDetectionAndImplicitResolutionInsideLoadedModules()
    {
        var parsed = await Parser.ParseAsync(
            ImplicitLoadingProgram,
            new RunOptions { DownloadCode = DownloadModule });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));

        var increment = SplicedModuleProperty(parsed.Root, "Increment");
        var incrementBody = Assert.IsType<Expr.Binary>(Assert.Single(increment.Value.Output));
        Assert.IsType<Expr.Param>(incrementBody.Left);

        var twice = SplicedModuleProperty(parsed.Root, "Twice");
        var twiceBody = Assert.IsType<Expr.Binary>(Assert.Single(twice.Value.Output));
        var leftCall = Assert.IsType<Expr.Call>(twiceBody.Left);
        var rightCall = Assert.IsType<Expr.Call>(twiceBody.Right);
        Assert.IsType<Expr.Param>(Assert.Single(leftCall.Args));
        Assert.IsType<Expr.Param>(Assert.Single(rightCall.Args));
    }

    [Fact]
    public async Task PartialLoadElaboration_LeavesImplicitAlgorithmReferencesUnresolved()
    {
        var syntaxRoot = SourceProvenance.ParseSyntaxValidRoot(ImplicitLoadingProgram);
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(diagnostics, DownloadModule);
        var loadedOnly = await loader.ElaborateAsync(syntaxRoot);
        Assert.DoesNotContain(diagnostics, d => d.Severity == DiagnosticSeverity.Error);

        // Loader-only output is still raw syntax: no implicit-argument pass has
        // turned these value-position references to a parametrized algorithm into
        // explicit calls carrying Twice's `n` parameter.
        var twice = SplicedModuleProperty(loadedOnly, "Twice");
        var twiceBody = Assert.IsType<Expr.Binary>(Assert.Single(twice.Value.Output));
        Assert.IsType<Expr.Resolve>(twiceBody.Left);
        Assert.IsType<Expr.Resolve>(twiceBody.Right);

        var authoritative = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync(ImplicitLoadingProgram, new RunOptions { DownloadCode = DownloadModule }));
        Assert.Equal("10", authoritative.ToDisplayString());
    }

    /// <summary>
    /// And the v0.8.187 exposure hole is equally present on this route: the
    /// spliced exposure-witness module keeps every property at the constructor
    /// default, where <see cref="AuthoritativeAsyncParse_FinalizesExposureInsideLoadedModules"/>
    /// shows the complete pipeline classifying it local-only.
    /// </summary>
    [Fact]
    public async Task PartialLoadElaboration_AlsoLeavesExposureUnfinalized()
    {
        var syntaxRoot = SourceProvenance.ParseSyntaxValidRoot(LoadingProgram);

        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(diagnostics, DownloadModule);
        var loadedOnly = await loader.ElaborateAsync(syntaxRoot);
        Assert.DoesNotContain(diagnostics, d => d.Severity == DiagnosticSeverity.Error);

        Assert.Equal(
            PropertyExposure.Exported,
            SplicedModuleProperty(loadedOnly, "Run", "Lib", "Value").Exposure);
    }
}
