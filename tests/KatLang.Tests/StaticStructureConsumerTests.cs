using System.Numerics;
using System.Runtime.CompilerServices;

namespace KatLang.Tests;

/// <summary>The production passes share one admitted structural operation.</summary>
public sealed class StaticStructureConsumerTests
{
    [Theory]
    [InlineData(1000)]
    [InlineData(2000)]
    public void DeterministicAdmission_OriginalWideSourceWitness(int size)
    {
        var source = "a=1\nb=2\nc=3\n" + string.Join('\n', Enumerable.Range(0, size)
            .Select(i => $"P{i}=a+b+c+{i}")) + $"\nP{size - 1}";
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join('\n', parsed.Diagnostics));
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal((Decimal128)(size + 5), Assert.IsType<Result.Atom>(result.Value).Value);
        var raw = SourceProvenance.ParseSyntaxValidRoot(source);
        var measurement = StaticStructureAdmission.Create(raw).Measurement;
        Assert.Equal(1024L * 1024 * 1024, measurement.GraphBytes);
        Assert.InRange(measurement.Limits.MaxEntries, 1, 1_048_576);
        Assert.InRange(measurement.Limits.MaxStorageUnits, 1, 16_777_216);
        Assert.InRange(measurement.Limits.MaxReads, 1, long.MaxValue - 1);
        Assert.InRange(measurement.Limits.MaxEvaluations, 1, long.MaxValue - 1);
    }

    [Theory]
    [InlineData("A=1\nA")]
    [InlineData("Lib={public V=7\n0}\nA=Lib\nB=A\nB.V")]
    [InlineData("Lib={public V=7\n0}\nA=Lib\nB=A\nP={open Lib,A,B\nV+0}\nP")]
    public async Task ExplicitAdmissionBudget_RefusesWithoutCompletedPublication(string source)
    {
        var options = new RunOptions { SourceProcessingLimits = new() { MaxStaticStructureBytes = 1024 } };
        foreach (var parsed in new[] { Parser.Parse(source, options), await Parser.ParseAsync(source, options) })
        {
            Assert.True(parsed.HasErrors);
            Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.StaticStructureLimitExceeded);
            Assert.DoesNotContain(parsed.Diagnostics, d => d.Code == DiagnosticCode.SelfDependentInferredParameters);
            Assert.Null(parsed.Root.CompletedStructure);
            Assert.Empty(parsed.Root.Properties);
        }
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
        Assert.Contains(failure.Errors, e => e.Code == KatLangErrorCode.StaticStructureLimitExceeded);
        Assert.False(Parser.Parse(source).HasErrors);
    }

    [Fact]
    public void ExplicitAdmissionBudget_ClampsWithoutOverflowAndRejectsInvalidValues()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("A=1\nA");
        var baseline = StaticStructureAdmission.Create(raw).Measurement;
        var clamped = StaticStructureAdmission.Create(raw, sourceProcessingLimits: new() { MaxStaticStructureBytes = long.MaxValue }).Measurement;
        Assert.Equal(baseline, clamped);
        Assert.Throws<ArgumentOutOfRangeException>(() => new SourceProcessingLimits { MaxStaticStructureBytes = 0 });
        Assert.Throws<ArgumentOutOfRangeException>(() => new SourceProcessingLimits { MaxStaticStructureBytes = -1 });
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        Assert.Throws<OperationCanceledException>(() => StaticStructureAdmission.Create(raw,
            sourceProcessingLimits: new() { MaxStaticStructureBytes = 1 }, cancellationToken: cts.Token));
        var error = Assert.Throws<OperationCanceledException>(() => Parser.Parse("A=1\nA", new RunOptions
        {
            SourceProcessingLimits = new() { MaxStaticStructureBytes = 1 }, SourceProcessingCancellationToken = cts.Token,
        }));
        Assert.Equal(cts.Token, error.CancellationToken);
    }

    [Fact]
    public void ExplicitAdmissionBudget_SharedDagCountsEdgesAndDistinctNodes()
    {
        var shared = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var root = new Algorithm.User(null, [], [], Enumerable.Range(0, 256)
            .Select(i => new Property($"P{i}", shared)).ToArray(), []);
        var admitted = StaticStructureAdmission.Create(root, sourceProcessingLimits: new() { MaxStaticStructureBytes = 1024 * 1024 }, phase: StaticAstPhase.Resolved);
        Assert.True(admitted.Measurement.Edges > admitted.Measurement.Nodes);
        Assert.Throws<StaticQueryLimitExceededException>(() => StaticStructureAdmission.Create(root,
            sourceProcessingLimits: new() { MaxStaticStructureBytes = 1024 }, phase: StaticAstPhase.Resolved));
        Assert.Null(root.CompletedStructure);
    }

    [Fact]
    public async Task ExplicitAdmissionBudget_IsInheritedByEagerAndDeferredModuleCompilation()
    {
        var downloads = 0;
        var module = string.Join('\n', Enumerable.Range(0, 1000).Select(i => $"public P{i}={i}+0")) + "\npublic V=7\n0";
        var options = new RunOptions
        {
            SourceProcessingLimits = new() { MaxStaticStructureBytes = 4 * 1024 * 1024 },
            AllowedHosts = ["modules.example"],
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult(module); },
        };
        var eager = await Parser.ParseAsync("open 'https://modules.example/large.kat'\nV+0", options);
        Assert.Contains(eager.Diagnostics, d => d.Code == DiagnosticCode.StaticStructureLimitExceeded);
        Assert.Null(eager.Root.CompletedStructure);
        const string family = "F(true)={open 'https://modules.example/large.kat'\nV+0}\nF(false)=0\n";
        downloads = 0;
        Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(family + "F(false)", options));
        Assert.Equal(0, downloads);
        var refused = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(family + "F(true)", options));
        Assert.Contains(refused.Errors, e => e.Code == KatLangErrorCode.StaticStructureLimitExceeded);
        Assert.Equal(1, downloads);
    }

    [Theory]
    [InlineData(false, true)]
    [InlineData(true, false)]
    public void OrderingOnlyChargesTheLevelOpen_WhenNoNestedOpenCanIntervene(bool nestedOpen, bool expectedEdge)
    {
        var root = Assert.IsType<Algorithm.User>(SourceProvenance.ParseSyntaxValidRoot(
            "Provider={public X=1}\nQ={public X=2}\nReader={" + (nestedOpen ? "open Q\n" : "") + "X+0}\n0"));
        var graph = PropertyDependencyGraphBuilder.BuildDependencyOrder(root,
            lookup: new SiblingOrderLookup(_ => LiftingCallee.Dynamic, name => name == "X" ? 0 : null));
        var reader = root.Properties.Select((p,i) => (p,i)).Single(t => t.p.Name == "Reader").i;
        Assert.Equal(expectedEdge, graph[reader].SiblingDependencyIndices.Contains(0));
    }

    private static (Algorithm Root, DiagnosticBag Diagnostics, StaticStructureOperation Operation) Process(string source, bool reverse = false)
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot(source);
        if (reverse) raw = raw with { Properties = raw.Properties.Reverse().ToArray() };
        var operation = new StaticStructureOperation(raw, new(20_000_000, 4, 2_000_000, 80_000_000));
        var diagnostics = new DiagnosticBag();
        var modules = new ModuleUnits();
        var detectedInput = ParameterDetector.DetectPrevalidated(raw, diagnostics: diagnostics, modules: modules, structuralOperation: operation);
        var (detected, _) = detectedInput;
        if (diagnostics.Any(d => d.Code == DiagnosticCode.SelfDependentInferredParameters)) return (detected, diagnostics, operation);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics, modules: modules, structuralOperation: operation);
        var exposed = PropertyExposureResolver.Resolve(resolved, observations: null, hostOperations: null, modules: modules);
        return (exposed, diagnostics, operation);
    }

    [Theory]
    [InlineData("F = x + 1\nF(41)", 42)]
    [InlineData("Lib = { public V = 42\n0 }\nA = Lib\nA.V", 42)]
    [InlineData("F(v)=0\nK(v)=7\nA=A.F\nP=A.x\nP(K)", 7)]
    [InlineData("P(x) = { A = x.Q\n5 }\nP(9)", 5)]
    [InlineData("F(0)=1\nF(x)=x+1\nF(41)", 42)]
    [InlineData("Mk(n)=n+1\nCnt(k)=k\nF(x)=x\nH=if(true,1,A.repeat(Cnt))\nA=Mk(F+0).Algorithm\nH(1)", 1)]
    [InlineData("Mk(n)=n+1\nCnt(k)=k\nF(x)=x\nLib={public Me=Lib\npublic A=Mk(F+0).Algorithm\npublic H=if(true,1,Me.A.repeat(Cnt))\n0}\nLib.H(1)", 1)]
    public void ActualPassesShareStructuralFacts(string source, int expected)
    {
        foreach (var reversed in new[] { false, true })
        {
            var result = Process(source, reversed);
            Assert.Empty(result.Diagnostics);
            var actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(result.Root));
            Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
            Assert.Equal(new Decimal128[] { expected }, actual.Value);
        }
    }

    [Theory]
    [InlineData("A.3.1")]
    [InlineData("A.3.2")]
    [InlineData("A.3.3a")]
    [InlineData("A.3.3b")]
    public void ApprovedSelfDependentCases_ReportA1ThroughActualDetection(string witness)
    {
        foreach (var reversed in new[] { false, true })
        {
            var result = Process(StaticStructureWitnessSources.Cases[witness], reversed);
            var diagnostic = Assert.Single(result.Diagnostics, d => d.Code == DiagnosticCode.SelfDependentInferredParameters
                && d.Message.Contains("'P'", StringComparison.Ordinal));
            Assert.Contains("Declare the parameters explicitly", diagnostic.Message);
            Assert.NotNull(diagnostic.Span);
        }
    }

    [Fact]
    public void StrataZeroGet_Reaches42ThroughTheActualPasses()
    {
        var result = Process(StaticStructureWitnessSources.Cases["strata0-get"]);
        Assert.Empty(result.Diagnostics);
        var actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(result.Root));
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 42 }, actual.Value);
    }

    [Fact]
    public void StrataZeroAmbiguity_IsAStaticDiagnosticFromActualDetection()
    {
        var result = Process(StaticStructureWitnessSources.Cases["strata0-ambiguous"]);
        Assert.Contains(result.Diagnostics, d => d.Code == DiagnosticCode.AmbiguousOpen);
    }

    [Fact]
    public void PrivatePipelineRunsTheSharedProductionPassesAndCompletedValidators()
    {
        var result = FrontEndPipeline.Process(StaticStructureWitnessSources.Cases["strata0-get"]);
        Assert.False(result.HasErrors, string.Join('\n', result.Diagnostics.Select(d => d.Message)));
        var actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(result.ElaboratedRoot));
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 42 }, actual.Value);
    }

    [Fact]
    public void PrivatePipelineStopsBeforeLiftingAfterA1()
    {
        var result = FrontEndPipeline.Process(StaticStructureWitnessSources.Cases["A.3.1"]);
        Assert.Contains(result.Diagnostics, d => d.Code == DiagnosticCode.SelfDependentInferredParameters);
        Assert.True(result.HasErrors);
    }

    [Fact]
    public void AdmissionIsScaledAndResourceFailuresRemainDistinctFromA1()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("P = x + y\nP(1,2)");
        var admitted = StaticStructureAdmission.Create(raw, sourceProcessingLimits: new() { MaxStaticStructureBytes = 256 * 1024 * 1024 });
        Assert.True(admitted.Measurement.Nodes > 0);
        Assert.True(admitted.Measurement.Limits.MaxEntries > 4096);
        var refused = Assert.Throws<StaticQueryLimitExceededException>(() => StaticStructureAdmission.Create(raw, sourceProcessingLimits: new() { MaxStaticStructureBytes = 1024 }));
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, StaticStructureAdmission.Rejection(refused).Code);
    }

    [Fact]
    public void PublishedAliasesDoNotRetainTheQueryOperation()
    {
        var result = CompileAndReleaseOperation();
        GC.Collect(); GC.WaitForPendingFinalizers(); GC.Collect();
        Assert.False(result.Operation.IsAlive);
        GC.KeepAlive(result.Root);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (Algorithm Root, WeakReference Operation) CompileAndReleaseOperation()
    {
        var result = Process("Lib={public V=42\n0}\nA=Lib\nA.V");
        Assert.Empty(result.Diagnostics);
        return (result.Root, new(result.Operation));
    }

    [Fact]
    public void SelfPathSignatureChain_PreservesTheExistingFortyMemberProgram()
    {
        var source = "open M\nM={public fam(0)=0\npublic fam(n)=n}\nF(x)=x\nLib={\n"
            + string.Join('\n', Enumerable.Range(1, 39).Select(i => $"public A{i}=fam(Lib.A{i+1})+0"))
            + "\npublic A40=F+0\n0}\nLib.A1(3)";
        var result = FrontEndPipeline.Process(source);
        Assert.False(result.HasErrors, string.Join('\n', result.Diagnostics.Select(d => d.Message)));
        var actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(result.ElaboratedRoot));
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 3 }, actual.Value);
    }

    [Fact]
    public void ExplicitParametersEscapeTheApprovedCircularInferenceWitness()
    {
        var source = StaticStructureWitnessSources.Cases["A.3.1"].Replace("P = {", "P(x,y) = {", StringComparison.Ordinal)
            .Replace("P(K)", "P(5,6)", StringComparison.Ordinal);
        var result = FrontEndPipeline.Process(source);
        Assert.False(result.HasErrors, string.Join('\n', result.Diagnostics.Select(d => d.Message)));
        var actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(result.ElaboratedRoot));
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 11 }, actual.Value);
    }

    [Fact]
    public async Task PrivateCandidateRunsGenericOptimizedAndSuspendingAsync()
    {
        const string source = "F=x+1\nPause()+F(41)";
        var operations = HostOperations.Create(HostOperation.Create("Pause", (_, _) => new Result.Atom(0)));
        var compiled = FrontEndPipeline.Process(source, new RunOptions { HostOperations = operations });
        Assert.False(compiled.HasErrors);
        foreach (var optimized in new[] { false, true })
        {
            var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null,
                enableOptimizations: optimized, hostOperations: operations);
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
            Assert.Equal((Decimal128)42, Assert.IsType<Result.Atom>(result.Value.Value).Value);
        }
        var suspending = HostOperations.Create(HostOperation.CreateAsync("Pause", async (_, _) => { await Task.Yield(); return new Result.Atom(0); }));
        compiled = FrontEndPipeline.Process(source, new RunOptions { HostOperations = suspending });
        Assert.False(compiled.HasErrors);
        var (asynchronous, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null, hostOperations: suspending);
        Assert.False(asynchronous.IsError, asynchronous.IsError ? asynchronous.Error.ToString() : "");
        Assert.Equal((Decimal128)42, Assert.IsType<Result.Atom>(asynchronous.Value.Value).Value);
    }

    [Fact]
    public async Task EagerModulesShareIdentityAndRemainHygienicThroughThePrivateConsumers()
    {
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult("public V=21\n0"); },
        };
        var result = await FrontEndPipeline.ProcessAsync(
            "M1=load('https://mods.test/a.kat')\nM2=load('https://mods.test/a.kat')\nA=M1\nA.V+M2.V", options);
        Assert.False(result.HasErrors, string.Join('\n', result.Diagnostics.Select(d => d.Message)));
        Assert.Equal(1, downloads);
        var actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(result.ElaboratedRoot));
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 42 }, actual.Value);
        result = await FrontEndPipeline.ProcessAsync(
            "M=load('https://mods.test/a.kat')\nP(V)={open M\nV+0}\nP(7)", options);
        Assert.False(result.HasErrors, string.Join('\n', result.Diagnostics.Select(d => d.Message)));
        actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(result.ElaboratedRoot));
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 7 }, actual.Value);
    }

    [Fact]
    public void BlockHeadedRuntimeLinkUsesItsRawQueryDefinitionAfterQ8RewritesTheBlock()
    {
        var result = FrontEndPipeline.Process(
            "Mk(n)=n+1\nF(x)=x\nH={public A=Mk(F+0).Algorithm}.A.abs+0\nH(3)");
        Assert.False(result.HasErrors, string.Join('\n', result.Diagnostics.Select(d => d.Message)));
        var actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(result.ElaboratedRoot));
        Assert.True(actual.IsError);
        Assert.Equal(KatLangErrorCode.TypeMismatch, actual.Error.Code);
    }

    [Fact]
    public void AdmissionBoundsRepeatedEdges_WithoutQueuingEveryOccurrence()
    {
        var shared = new Expr.Num(0);
        var raw = new Algorithm.User(null, [], [], [], Enumerable.Repeat<Expr>(shared, 1_000_000).ToArray());
        var before = GC.GetAllocatedBytesForCurrentThread();
        var error = Assert.Throws<StaticQueryLimitExceededException>(() => StaticStructureAdmission.Create(raw, sourceProcessingLimits: new() { MaxStaticStructureBytes = 1024 * 1024 }));
        Assert.Contains("edge-work", error.Message);
        Assert.InRange(GC.GetAllocatedBytesForCurrentThread() - before, 1, 2 * 1024 * 1024);
    }

    [Fact]
    public void NeverCalledRootInputsDoNotBecomeCallableOpenHeads()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("Q.X\nP={open Q\n0}\n0");
        var operation = new StaticStructureOperation(raw, new(1_000_000, 4, 200_000, 4_000_000));
        var rootLevel = ElaboratedScopeLookup.CreateScope(raw, operation.CreatePreludeScope());
        var bindings = ParameterOwnership.Empty.Extend(rootLevel, new[] { "Q", "X" }, ownerIsNeverCalled: true);
        Assert.Equal(OwnedDeclarationKind.Parameter, ElaboratedScopeLookup.SelectOwnedDeclaration(rootLevel, "Q", bindings).Kind);
        Assert.Equal(OwnedDeclarationKind.None, ElaboratedScopeLookup.SelectOwnedDeclaration(rootLevel, "Q", bindings.CallableBindings).Kind);
        var ordinary = FrontEndPipeline.Process("Q.X\nP={open Q\n0}\n0");
        var candidate = FrontEndPipeline.Process("Q.X\nP={open Q\n0}\n0");
        Assert.Equal(ordinary.Diagnostics.Select(d => (d.Code, d.Message)), candidate.Diagnostics.Select(d => (d.Code, d.Message)));
    }

    [Fact]
    public async Task NestedOpenLinkHead_DoesNotInventAnOuterProviderCycle()
    {
        const string prefix = "open P2\nMk(n)=n+1\nF(x)=x\nG(g)=g\nfam(0)=0\nfam(n)=n\n";
        string[] declarations = [
            "P2={public X2=Mk(F+0).Algorithm\npublic V=P1+0\n0}",
            "P1={open Q\npublic X1=Mk(X2.fam+0).Algorithm\nG+0}",
            "Q={public X2=Mk(y).Algorithm}"];
        int[][] orders = [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]];
        foreach (var order in orders)
        {
            var source = prefix + string.Join('\n', order.Select(i => declarations[i])) + "\nP2.V(7)";
            var compiled = FrontEndPipeline.Process(source);
            Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
            var p2 = Assert.IsType<Algorithm.User>(compiled.ElaboratedRoot.Properties.Single(p => p.Name == "P2").Value);
            Assert.Equal(new[] { "g" }, p2.Properties.Single(p => p.Name == "V").Value.Params);
            foreach (var optimized in new[] { false, true })
            {
                var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null,
                    enableOptimizations: optimized);
                Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
                Assert.Equal((Decimal128)7, Assert.IsType<Result.Atom>(result.Value.Value).Value);
            }
            var (asyncResult, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null);
            Assert.False(asyncResult.IsError, asyncResult.IsError ? asyncResult.Error.ToString() : "");
            Assert.Equal((Decimal128)7, Assert.IsType<Result.Atom>(asyncResult.Value.Value).Value);

            var pauses = 0;
            var host = HostOperations.Create(HostOperation.CreateAsync("Pause", async (_, _) =>
            {
                await Task.Yield();
                pauses++;
                return new Result.Atom(0);
            }));
            var suspendedSource = source.Replace("\nP2.V(7)", "\nPause()+P2.V(7)", StringComparison.Ordinal);
            var suspended = FrontEndPipeline.Process(suspendedSource, new RunOptions { HostOperations = host });
            Assert.False(suspended.HasErrors, string.Join('\n', suspended.Diagnostics.Select(d => d.Message)));
            var (suspendedResult, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(suspended.ElaboratedRoot), null, hostOperations: host);
            Assert.False(suspendedResult.IsError, suspendedResult.IsError ? suspendedResult.Error.ToString() : "");
            Assert.Equal((Decimal128)7, Assert.IsType<Result.Atom>(suspendedResult.Value.Value).Value);
            Assert.Equal(1, pauses);
        }
    }
}
