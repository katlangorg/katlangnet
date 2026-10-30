using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>Actual private pipeline and selected deferred units, using the loader's real registry and gate.</summary>
public sealed class StaticStructureDeferredConsumerTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ConfiguredSourceAdmissionIsIdenticalWithOrWithoutADownloader(bool downloader)
    {
        var options = new RunOptions
        {
            SourceProcessingLimits = new SourceProcessingLimits { MaxSourceLength = 4 },
            DownloadCode = downloader ? (_, _) => throw new InvalidOperationException("Source must be refused before acquisition.") : null,
        };
        var ordinary = await FrontEndPipeline.ProcessAsync("12345", options);
        var candidate = await FrontEndPipeline.ProcessAsync("12345", options);
        Assert.True(candidate.HasErrors);
        Assert.Equal(DiagnosticCode.SourceLengthExceeded, Assert.Single(candidate.Diagnostics).Code);
        Assert.Equal(ordinary.Diagnostics.Select(d => (d.Code, d.Message)), candidate.Diagnostics.Select(d => (d.Code, d.Message)));
    }

    [Fact]
    public async Task SelectedBranchCompilesWithSharedQueries_AndAnUnselectedBranchStaysInert()
    {
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = async (_, token) => { downloads++; await Task.Yield(); token.ThrowIfCancellationRequested(); return "public V=42\n0"; },
        };
        const string source = "F(0)=0\nF(n)={open 'https://mods.test/a.kat'\nV}\nF(0)+F(1)";
        var compiled = await FrontEndPipeline.ProcessAsync(source, options);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        Assert.Equal(0, downloads);
        var model = SemanticModelBuilder.Build(compiled.ToParseResult(null));
        Assert.NotNull(model);
        Assert.Equal(0, downloads);
        var family = Assert.IsType<Algorithm.Conditional>(compiled.ElaboratedRoot.Properties.Single(p => p.Name == "F").Value);
        var region = Assert.IsType<DeferredModuleRegion>(family.Branches[1].Body.DeferredRegion);
        Assert.NotNull(region.Structure);
        Assert.NotNull(region.Structure.Forwardable);
        var (actual, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null);
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal((Decimal128)42, Assert.IsType<Result.Atom>(actual.Value.Value).Value);
        Assert.Equal(1, downloads);
        Assert.True(region.IsMaterialized);
    }

    [Fact]
    public async Task SeparatelySelectedOccurrencesReuseTheCompletedModuleDeclaration()
    {
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult("public V=21\n0"); },
        };
        const string source = "F(0)=0\nF(n)={M=load('https://mods.test/a.kat')\nM.V}\nG(0)=0\nG(n)={M=load('https://mods.test/a.kat')\nM.V}\nF(1)+G(1)";
        var compiled = await FrontEndPipeline.ProcessAsync(source, options);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var (actual, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null);
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal((Decimal128)42, Assert.IsType<Result.Atom>(actual.Value.Value).Value);
        Assert.Equal(1, downloads);
        var first = Region(compiled.ElaboratedRoot, "F");
        var second = Region(compiled.ElaboratedRoot, "G");
        Assert.True(first.TryGetMaterialized(out var f));
        Assert.True(second.TryGetMaterialized(out var g));
        Assert.Same(f.Properties.Single(p => p.Name == "M").Value, g.Properties.Single(p => p.Name == "M").Value);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ReusedModuleCalleeReadsItsCompletedSignatureInEitherSelectionOrder(bool calleeFirst)
    {
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult("F=abs\n0"); },
        };
        var source = "G(0)={M=load('https://mods.test/a.kat')\nK=M.F(abs)\nK(-5)}\nG(n)={M=load('https://mods.test/a.kat')\nn}\n"
            + (calleeFirst ? "G(0),G(1)" : "G(1),G(0)");
        var compiled = await FrontEndPipeline.ProcessAsync(source, options);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var (actual, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null);
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal(calleeFirst ? new Decimal128[] { 5, 1 } : new Decimal128[] { 1, 5 }, actual.Value.Value.ToAtoms());
        Assert.Equal(1, downloads);
    }

    [Fact]
    public async Task CapturedOwnerParameterStillPrecedesTheMaterializedOpen()
    {
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (_, _) => ValueTask.FromResult("public V=99\n0"),
        };
        var compiled = await FrontEndPipeline.ProcessAsync(
            "Outer(V)={F(0)=0\nF(n)={open 'https://mods.test/a.kat'\nV+n}\nF(1)}\nOuter(7)", options);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var (actual, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null);
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal((Decimal128)8, Assert.IsType<Result.Atom>(actual.Value.Value).Value);
    }

    [Fact]
    public async Task NestedDeferredOccurrenceGetsAFreshCompilationAndPublishesItsModule()
    {
        var downloads = new List<string>();
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (url, _) => { downloads.Add(url); return ValueTask.FromResult(url.EndsWith("a.kat", StringComparison.Ordinal) ? "public A=20" : "public B=22"); },
        };
        var compiled = await FrontEndPipeline.ProcessAsync(
            "F(0)=0\nF(n)={open 'https://mods.test/a.kat'\nG(0)=0\nG(m)={open 'https://mods.test/b.kat'\nA+B}\nG(n)}\nF(1)", options);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        Assert.Empty(downloads);
        var (actual, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null);
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal((Decimal128)42, Assert.IsType<Result.Atom>(actual.Value.Value).Value);
        Assert.Equal(new[] { "https://mods.test/a.kat", "https://mods.test/b.kat" }, downloads);
    }

    [Fact]
    public async Task InvalidUnreadModuleSiblingIsRejectedByA1BeforeTheBodyRuns()
    {
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (_, _) => ValueTask.FromResult(StaticStructureWitnessSources.Cases["A.3.1"]),
        };
        var compiled = await FrontEndPipeline.ProcessAsync(
            "F(0)=0\nF(n)={M=load('https://mods.test/a.kat')\n42}\nF(1)", options);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var region = Region(compiled.ElaboratedRoot, "F");
        var before = region.Structure!.Registry.StructuralContinuation;
        var (actual, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null);
        Assert.True(actual.IsError);
        Assert.Equal(KatLangErrorCode.SelfDependentInferredParameters, actual.Error.Code);
        Assert.False(region.IsMaterialized);
        Assert.Same(before, region.Structure.Registry.StructuralContinuation);
    }

    [Fact]
    public async Task CancelledSelectionPublishesNothing_AndRetryUsesAFreshOperation()
    {
        var started = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var exited = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = async (_, token) =>
            {
                if (++downloads != 1) return "public V=42\n0";
                started.SetResult();
                try { await Task.Delay(Timeout.Infinite, token); }
                finally { exited.SetResult(); }
                return "public V=0";
            },
        };
        var compiled = await FrontEndPipeline.ProcessAsync(
            "F(0)=0\nF(n)={open 'https://mods.test/a.kat'\nV}\nF(1)", options);
        Assert.False(compiled.HasErrors);
        var region = Region(compiled.ElaboratedRoot, "F");
        var before = region.Structure!.Registry.StructuralContinuation;
        using var cancellation = new CancellationTokenSource();
        var evaluation = Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null,
            cancellationToken: cancellation.Token).AsTask();
        await started.Task.WaitAsync(TimeSpan.FromSeconds(10));
        cancellation.Cancel();
        await exited.Task.WaitAsync(TimeSpan.FromSeconds(10));
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => evaluation);
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.False(region.IsMaterialized);
        Assert.Same(before, region.Structure.Registry.StructuralContinuation);
        var (retry, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null);
        Assert.False(retry.IsError, retry.IsError ? retry.Error.ToString() : "");
        Assert.Equal((Decimal128)42, Assert.IsType<Result.Atom>(retry.Value.Value).Value);
        Assert.Equal(2, downloads);
        Assert.True(region.IsMaterialized);
    }

    [Fact]
    public void CompiledDeferredTreeDoesNotRetainTheEagerQueryOperationOrToken()
    {
        var compiled = CompileAndRelease();
        GC.Collect(); GC.WaitForPendingFinalizers(); GC.Collect();
        Assert.False(compiled.Operation.IsAlive);
        Assert.False(compiled.Token.IsAlive);
        GC.KeepAlive(compiled.Root);
    }

    [Theory]
    [InlineData(64)]
    [InlineData(1024)]
    public async Task MaterializationDoesNotCopyEveryOuterSignature(int width)
    {
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (_, _) => ValueTask.FromResult("public V=42\n0"),
        };
        var source = string.Join('\n', Enumerable.Range(0, width).Select(i => $"P{i}={i}"))
            + "\nF(0)=0\nF(n)={open 'https://mods.test/a.kat'\nV+P0}\nF(1)";
        var compiled = await FrontEndPipeline.ProcessAsync(source, options);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var observations = new FrontEndTraversalObservations();
        Region(compiled.ElaboratedRoot, "F").Loader.TraversalObservations = observations;
        var (actual, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null);
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal((Decimal128)42, Assert.IsType<Result.Atom>(actual.Value.Value).Value);
        Assert.InRange(observations.ContextEntriesWritten, 0, 64);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (Algorithm Root, WeakReference Operation, WeakReference Token) CompileAndRelease()
    {
        var diagnostics = new DiagnosticBag();
        var loader = new ModuleLoader(diagnostics, (_, _) => ValueTask.FromResult("public V=42"), ["mods.test"], new SourceProcessingBudget(null), default);
        var expansion = loader.ElaborateAsync(SourceProvenance.ParseSyntaxValidRoot("F(0)=0\nF(n)={open 'https://mods.test/a.kat'\nV}\nF(0)"));
        Assert.True(expansion.IsCompletedSuccessfully);
        var raw = expansion.GetAwaiter().GetResult();
        using var token = new CancellationTokenSource();
        var operation = new StaticStructureOperation(raw, new(20_000_000, 4, 2_000_000, 80_000_000), cancellationToken: token.Token);
        var modules = loader.ModuleUnits.BeginOperation();
        var detectedInput = ParameterDetector.DetectPrevalidated(raw, diagnostics: diagnostics, modules: modules, structuralOperation: operation);
        var (detected, _) = detectedInput;
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics, modules: modules, structuralOperation: operation);
        new ParameterPropertyCollisionValidator(diagnostics).VisitAlgorithm(resolved);
        var exposed = PropertyExposureResolver.Resolve(resolved, observations: null, hostOperations: null, modules: modules);
        Assert.Empty(diagnostics);
        modules.Publish(operation.Freeze());
        return (exposed, new(operation), new(token));
    }

    private static DeferredModuleRegion Region(Algorithm root, string family)
        => Assert.IsType<DeferredModuleRegion>(Assert.IsType<Algorithm.Conditional>(root.Properties.Single(p => p.Name == family).Value).Branches[1].Body.DeferredRegion);
}
