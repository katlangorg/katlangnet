using System.Numerics;
using KatLang.Semantics;
using static KatLang.Tests.ModuleRouteAgreement;

namespace KatLang.Tests;

/// <summary>Independent source witnesses for the committed module/open identity laws.</summary>
public class ModuleLawPostCommitReviewTests
{
    private const string Url = "https://mods.test/unit.kat";

    [Fact]
    public async Task SkippingTheExpandedModuleOwner_StillSettlesItsMembersAtThePrelude()
    {
        var source = $"Outer(p) = {{ sum(xs) = p + 999\nM = load('{Url}')\npublic R = M.V + 0\nR }}\nOuter(1), Outer(2), Outer.R";
        var server = () => new Modules((Url, "public V = sum((1, 2))"));
        var observed = await OnEveryRouteAsync(source, server);
        Assert.Equal("ok S[3, 3, 3]", $"{observed.Kind} {observed.Value}");
        var parsed = await Parser.ParseAsync(source, server().Options());
        Assert.Empty(parsed.Diagnostics);
        var outer = Assert.IsType<Algorithm.User>(Assert.Single(parsed.Root.Properties).Value);
        var r = Assert.Single(outer.Properties, p => p.Name == "R");
        Assert.Equal(PropertyExposure.Exported, r.Exposure);
        Assert.Empty(r.RequiredAncestorParameters);
    }

    [Fact]
    public async Task RecursiveQualifiedSummaryPaths_RetainCapturesOfTwoDeclaringOwners()
    {
        const string source = "Outer(p) = { Middle(q) = { Lib = { public A = { open B, Lib.A.B\npublic B = { public Y = p + q }\npublic X = Y + 0 }\npublic R = { open A, Lib.A\nX + 0 } }\nLib.R }\nMiddle(1), Middle(2) }\nOuter(10), Outer(20)";
        var observed = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("S[S[11, 12], S[21, 22]]", observed.Value);
        var outer = Assert.IsType<Algorithm.User>(Assert.Single(SourceProvenance.ParseValid(source).Root.Properties).Value);
        var middle = Assert.IsType<Algorithm.User>(Assert.Single(outer.Properties).Value);
        var lib = Assert.IsType<Algorithm.User>(Assert.Single(middle.Properties).Value);
        var r = Assert.Single(lib.Properties, p => p.Name == "R");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, r.Exposure);
        Assert.Equal(["p", "q"], r.RequiredAncestorParameters);
    }

    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, true, false)]
    [InlineData(true, false, false)]
    [InlineData(true, true, false)]
    [InlineData(false, false, true)]
    [InlineData(true, true, true)]
    public async Task NestedQualifiedProviders_KeepOneOwnerExpansionAndAllCaptures(bool nestedProvider, bool reversed, bool consumerFirst)
    {
        var qualified = nestedProvider ? "Lib.A.B" : "Lib.B";
        var innerOpens = reversed ? $"{qualified}, B" : $"B, {qualified}";
        var outerOpens = reversed ? "Lib.A, A" : "A, Lib.A";
        var binder = "public B = { public Y = p }";
        var read = "public X = Y + 0";
        var aBody = nestedProvider ? (consumerFirst ? read + "\n" + binder : binder + "\n" + read) : read;
        var a = $"public A = {{ open {innerOpens}\n{aBody} }}";
        var r = $"public R = {{ open {outerOpens}\nX + 0 }}";
        var providers = a + (nestedProvider ? "" : "\n" + binder);
        var source = $"Outer(p) = {{ Lib = {{ {(consumerFirst ? r + "\n" + providers : providers + "\n" + r)} }}\nLib.R }}\nOuter(5), Outer(6)";
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("S[5, 6]", observation.Value);
        var root = SourceProvenance.ParseValid(source).Root;
        var outer = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties).Value);
        var lib = Assert.IsType<Algorithm.User>(Assert.Single(outer.Properties).Value);
        var member = Assert.Single(lib.Properties, p => p.Name == "R");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, member.Exposure);
        Assert.Equal(["p"], member.RequiredAncestorParameters);
        Assert.Empty(Assert.IsType<Algorithm.User>(member.Value).Params);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task DirectAndNestedModulePaths_AreOneOpenProvider(bool reverseOpens, bool reverseLoads)
    {
        const string nested = "https://mods.test/nested.kat";
        var server = () => new Modules((Url, "public X = 5"), (nested, $"public S = load('{Url}')"));
        var loads = $"A = load('{Url}')\nN = load('{nested}')";
        if (reverseLoads) loads = $"N = load('{nested}')\nA = load('{Url}')";
        var source = $"open {(reverseOpens ? "N.S, A" : "A, N.S")}\n{loads}\nX + 0";
        var observed = await OnEveryRouteAsync(source, server);
        Assert.Equal("ok 5", $"{observed.Kind} {observed.Value}");
        var parsed = await Parser.ParseAsync(source, server().Options());
        Assert.Empty(parsed.Diagnostics);
        var a = Assert.Single(parsed.Root.Properties, p => p.Name == "A").Value;
        var n = Assert.Single(parsed.Root.Properties, p => p.Name == "N").Value;
        Assert.Same(a, Assert.Single(n.Properties, p => p.Name == "S").Value);
        Assert.Single(ElaboratedScopeLookup.CreateScope(parsed.Root).GetResolvedOpenProviders());
    }

    [Theory]
    [InlineData("F(1)")]
    [InlineData("Unused = F(1)\n1")]
    [InlineData("if(true, 1, F(1))")]
    [InlineData("2.F()")]
    [InlineData("Unused = 2.F()\n1")]
    [InlineData("map([], F)")]
    public void CallableNameAndExplicitMustFallback_DoNotEscapeStaticAmbiguity(string use)
    {
        var parsed = Parser.Parse($"open A, B\nA = {{ public F(x) = x }}\nB = {{ public F(x) = x + 1 }}\n{use}");
        Assert.Equal(DiagnosticCode.AmbiguousOpen, Assert.Single(parsed.Diagnostics).Code);
    }

    [Fact]
    public async Task ReusingOneCompiledDocument_DoesNotReuseAMemberValueAcrossRuns()
    {
        var ticks = 0;
        var host = HostOperations.Create(HostOperation.Create("tick", (_, _) => new Result.Atom((Decimal128)(++ticks))));
        var parsed = await Parser.ParseAsync($"A = load('{Url}')\nB = load('{Url}')\nA.X, B.X",
            new Modules((Url, "public X = tick()")).Options(host));
        Assert.Empty(parsed.Diagnostics);
        var program = new Expr.AlgorithmExpr(parsed.Root);
        for (var run = 1; run <= 2; run++)
        {
            var (result, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false, hostOperations: host);
            Assert.False(result.IsError);
            Assert.Equal($"S[{run}, {run}]", SixRouteAgreement.Neutral(result.Value.Value));
        }
        Assert.Equal(2, ticks);
    }

    [Theory]
    [InlineData("Sub, Lib.Sub", false)]
    [InlineData("Lib.Sub, Sub", false)]
    [InlineData("Sub, (Sub), Lib.Sub", false)]
    [InlineData("Sub, Lib.Sub", true)]
    [InlineData("Lib.Sub, Sub", true)]
    [InlineData("Sub, (Sub), Lib.Sub", true)]
    public async Task CapturingNonModuleProvider_SettlesChargesAndLiftingAcrossRepeatedPaths(string opens, bool siblingFirst)
    {
        var sub = "public Sub = { public X = p\npublic F(x) = x + p }";
        var reads = "public R = X + 0\npublic K = F + 0";
        var source = $"Outer(p) = {{ Lib = {{ open {opens}\n{(siblingFirst ? reads + "\n" + sub : sub + "\n" + reads)} }}\nLib.R, Lib.K(2) }}\nOuter(5), Outer(6)";
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("S[S[5, 7], S[6, 8]]", observation.Value);
        var parsed = SourceProvenance.ParseValid(source);
        var outer = Assert.IsType<Algorithm.User>(Assert.Single(parsed.Root.Properties).Value);
        var lib = Assert.IsType<Algorithm.User>(Assert.Single(outer.Properties).Value);
        Assert.All(lib.Properties.Where(p => p.Name is "R" or "K"), p =>
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, p.Exposure));
        Assert.Equal(["x"], Assert.IsType<Algorithm.User>(lib.Properties.Single(p => p.Name == "K").Value).Params);
    }

    public static TheoryData<string, DiagnosticCode, bool> InvalidAliasModules => new()
    {
        { "open F\nF(x) = x\nabs", DiagnosticCode.IllegalInOpen, false },
        { "open Missing\nabs", DiagnosticCode.UnresolvedOpenTarget, false },
        { "open count\nabs", DiagnosticCode.IllegalInOpen, false },
        { "F(x) = { x = 1\nx }\nabs", DiagnosticCode.ParameterPropertyCollision, false },
        { "open F\nF(x) = x\nabs", DiagnosticCode.IllegalInOpen, true },
        { "open Missing\nabs", DiagnosticCode.UnresolvedOpenTarget, true },
        { "open count\nabs", DiagnosticCode.IllegalInOpen, true },
        { "F(x) = { x = 1\nx }\nabs", DiagnosticCode.ParameterPropertyCollision, true },
    };

    [Theory]
    [MemberData(nameof(InvalidAliasModules))]
    public async Task AliasModuleValidation_IsPositionedAtItsImportSite(string module, DiagnosticCode code, bool expression)
    {
        var server = new Modules((Url, module));
        var source = expression ? $"M(z) = load('{Url}')\n1" : $"M = load('{Url}')\n1";
        var parsed = await Parser.ParseAsync(source, server.Options());
        Assert.True(parsed.HasErrors, $"Expected {code}; got {string.Join(" | ", parsed.Diagnostics)}");
        var report = Assert.Single(parsed.Diagnostics);
        Assert.Equal(code, report.Code);
        var expected = expression ? new SourceSpan(1, 8, 1, Url.Length + 16) : new SourceSpan(1, 1, 1, 2);
        Assert.Equal(expected, report.Span);
        var result = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, new Modules((Url, module)).Options()));
        Assert.Equal(KatLangError.FromDiagnostic(report).Code, Assert.Single(result.Errors).Code);
    }

    [Theory]
    [MemberData(nameof(InvalidAliasModules))]
    public async Task DeferredAliasModule_IsValidatedOnlyWhenItsUnitIsSelected(string module, DiagnosticCode code, bool expression)
    {
        var body = expression ? $"M(z) = load('{Url}')\n1" : $"M = load('{Url}')\n1";
        var source = $"F(0) = 0\nF(k) = {{ {body} }}\nF(0)";
        var server = new Modules((Url, module));
        var parsed = await Parser.ParseAsync(source, server.Options());
        Assert.Empty(parsed.Diagnostics);
        Assert.Empty(server.Fetches);
        Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, server.Options()));
        Assert.Empty(server.Fetches);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        var region = Assert.IsType<DeferredModuleRegion>(family.Branches[1].Body.DeferredRegion);
        var failed = await region.MaterializeAsync(default);
        Assert.True(failed.IsError);
        var error = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(failed.Error);
        Assert.Contains(error.Diagnostics, d => d.Code == code && d.Span is not null);
    }

    [Fact]
    public async Task AliasModuleMembers_RetainTheirLocationlessWrittenParameterSignature()
    {
        var parsed = await Parser.ParseAsync($"M = load('{Url}')\nM.F(3)",
            new Modules((Url, "public F(x) = x + 1\nabs")).Options());
        Assert.Empty(parsed.Diagnostics);
        Assert.IsType<Algorithm.Alias>(Assert.Single(parsed.Root.Properties).Value);
        var model = SemanticModelBuilder.Build(parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(2, 3)));
        Assert.Equal("F", resolution.Occurrence.Name);
        Assert.Null(resolution.ResolvedDeclaration);
        Assert.Equal(["x"], resolution.ResolvedProperty!.Parameters.Select(p => p.Name));
        Assert.All(resolution.ResolvedProperty.Parameters, p => Assert.Null(p.Span));
    }

    public static TheoryData<string, string> PreludeReads => new()
    {
        { "sum", "sum([1, 2])" }, { "count", "count([1, 2, 3])" },
        { "map", "sum(map([1, 2], { x + 1 }))" },
        { "filter", "sum(filter([1, 2], { x > 1 }))" },
        { "reduce", "reduce([1, 2], { a + b }, 0)" },
        { "first", "first([3, 4])" }, { "last", "last([3, 4])" },
        { "range", "sum(range(1, 3))" }, { "repeat", "repeat({ x + 1 }, 2, 1)" },
        { "while", "while({ x + 1, x < 2 }, 1)" },
        { "random", "random(0, 1)" }, { "randomInt", "randomInt(1, 1000000)" },
        { "Math", "Math.Abs(-3)" }, { "abs", "abs(-3)" },
        { "sqrt", "sqrt(9)" }, { "round", "round(3.4, 0)" }, { "pi", "pi" },
        { "trace", "trace(3)" }, { "tick", "tick()" },
    };

    [Theory]
    [MemberData(nameof(PreludeReads))]
    public async Task EveryPreludeLookupClass_IsIsolatedFromImporterShadows(string name, string expression)
    {
        var text = $"public V = {expression}";
        var server = () => new Modules((Url, text));
        var oracle = await OnEveryRouteAsync($"M = load('{Url}')\nM.V", server);
        Assert.Equal("ok", oracle.Kind);
        foreach (var shadow in new[] { $"{name} = 999", $"{name}(x) = 999" })
        {
            var observed = await OnEveryRouteAsync($"{shadow}\nG(k) = {{ M = load('{Url}')\nM.V + k * 0 }}\nG(1)", server);
            Assert.True(oracle.AgreesWith(observed), $"{name}: {observed}");
        }
        var deferred = await OnEveryRouteAsync($"{name} = 999\nG(0) = 0\nG(k) = {{ M = load('{Url}')\nM.V + k * 0 }}\nG(1)", server, AsyncRoutes);
        Assert.True(oracle.AgreesWith(deferred), deferred.ToString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task SequentialAndOverlappingDeferredOperations_ReuseOnePublishedChain(bool overlapping)
    {
        var server = new Modules((Url, "public X = 5\npublic F(x) = x + 1"));
        var parsed = await Parser.ParseAsync($"F(0) = {{ M = load('{Url}')\nM.X }}\nF(k) = {{ N = load('{Url}')\nN.X + k * 0 }}\n1", server.Options());
        Assert.Empty(parsed.Diagnostics);
        Assert.Empty(server.Fetches);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        var regions = family.Branches.Select(b => Assert.IsType<DeferredModuleRegion>(b.Body.DeferredRegion)).ToArray();
        EvalResult<Algorithm>[] results;
        if (overlapping)
            results = await Task.WhenAll(regions.Select(r => r.MaterializeAsync(default).AsTask()));
        else
            results = [await regions[1].MaterializeAsync(default), await regions[0].MaterializeAsync(default)];
        Assert.All(results, r => Assert.False(r.IsError));
        var modules = results.Select(r => Assert.Single(r.Value.Properties).Value).ToArray();
        Assert.Same(modules[0], modules[1]);
        Assert.Same(modules[0].Declaration, modules[1].Declaration);
        Assert.Same(modules[0].Properties[1], modules[1].Properties[1]);
        Assert.Equal(1, Assert.Single(server.Fetches).Value);
    }

    [Theory]
    [InlineData("Bad(x) = missing", DiagnosticCode.UndeclaredIdentifier)]
    [InlineData("A(y) = y\nBad(x) = A", DiagnosticCode.UnforwardableParameter)]
    [InlineData("open Missing", DiagnosticCode.UnresolvedOpenTarget)]
    [InlineData("Bad(x) = { x = 1\nx }", DiagnosticCode.ParameterPropertyCollision)]
    public async Task FailedOperation_CannotPublishOrReplaceASuccessfulModuleChain(string bad, DiagnosticCode code)
    {
        var server = new Modules((Url, "public X = 5"));
        var parsed = await Parser.ParseAsync($"F(0) = {{ {bad}\nM = load('{Url}')\nM.X }}\nF(k) = {{ N = load('{Url}')\nN.X + k * 0 }}\n1", server.Options());
        Assert.Empty(parsed.Diagnostics);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        var failedRegion = Assert.IsType<DeferredModuleRegion>(family.Branches[0].Body.DeferredRegion);
        var goodRegion = Assert.IsType<DeferredModuleRegion>(family.Branches[1].Body.DeferredRegion);
        var failed = await failedRegion.MaterializeAsync(default);
        Assert.True(failed.IsError);
        Assert.Contains(Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(failed.Error).Diagnostics, d => d.Code == code);
        Assert.False(failedRegion.IsMaterialized);
        var good = await goodRegion.MaterializeAsync(default);
        Assert.False(good.IsError);
        var first = Assert.Single(good.Value.Properties).Value;
        var retry = await failedRegion.MaterializeAsync(default);
        Assert.True(retry.IsError);
        Assert.Contains(Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(retry.Error).Diagnostics, d => d.Code == code);
        Assert.Same(first, Assert.Single((await goodRegion.MaterializeAsync(default)).Value.Properties).Value);
        Assert.Equal(2, failedRegion.MaterializationAttempts);
        Assert.Equal(1, goodRegion.MaterializationAttempts);
        Assert.Equal(1, Assert.Single(server.Fetches).Value);
    }

    [Fact]
    public async Task NestedDeferredUnitAndRootDeferredUnit_ShareTheEagerMembersBinding()
    {
        const string outer = "https://mods.test/outer.kat";
        var server = () => new Modules((Url, "public X = tick()"),
            (outer, $"public F(0) = 0\npublic F(k) = {{ S = load('{Url}')\nS.X + k * 0 }}"));
        var source = $"E = load('{Url}')\nO = load('{outer}')\nF(0) = 0\nF(k) = {{ M = load('{Url}')\nM.X + k * 0 }}\nO.F(1), F(1), E.X, O.F(2), F(2)";
        var observed = await OnEveryRouteAsync(source, server, AsyncRoutes);
        Assert.Equal("ok S[1, 1, 1, 1, 1]", $"{observed.Kind} {observed.Value}");
        Assert.Equal(["tick#1"], observed.HostCalls);
    }

    [Fact]
    public async Task SeparateDocumentsAndRuns_NeverShareModuleDeclarationsOrMemberCaches()
    {
        var server = new Modules((Url, "public X = 5"));
        var source = $"M = load('{Url}')\nM.X";
        var documents = await Task.WhenAll(Parser.ParseAsync(source, server.Options()), Parser.ParseAsync(source, server.Options()));
        Assert.All(documents, p => Assert.Empty(p.Diagnostics));
        Assert.NotSame(documents[0].Root.Properties[0].Value.Declaration, documents[1].Root.Properties[0].Value.Declaration);
        Assert.NotSame(documents[0].Root.Properties[0].Value.Properties[0], documents[1].Root.Properties[0].Value.Properties[0]);
        Assert.Equal(2, server.Fetches[Url]);
    }

    [Fact]
    public async Task InternalParameterizedOwnerCache_RemainsActivationSensitiveAcrossHolders()
    {
        var server = () => new Modules((Url, "public F(k) = { R = tick() + k\nR, R }\npublic A = tick()\npublic B = tick()"));
        var source = $"M = load('{Url}')\nN = load('{Url}')\nM.F(10), N.F(20), M.A, N.A, N.B, M.B, M.A(), N.A";
        var observed = await OnEveryRouteAsync(source, server);
        Assert.Equal("ok S[S[11, 11], S[22, 22], 3, 3, 4, 4, 5, 3]", $"{observed.Kind} {observed.Value}");
        Assert.Equal(["tick#1", "tick#2", "tick#3", "tick#4", "tick#5"], observed.HostCalls);
    }

    [Fact]
    public async Task ModuleArgumentsAndCallbackAliases_KeepHygieneAndIdentity()
    {
        var server = () => new Modules((Url, "public X = tick()\npublic V = Base + 1\npublic F(x) = abs(x)"));
        var source = $"Base = 999\nabs(x) = 888\nM = load('{Url}')\nN = load('{Url}')\nRead(m) = m.X\nUse(m, Base) = m.V(Base)\nAlias = M.F\nRead(M), Read(N), Use(M, 4), sum(map([-3, -4], Alias))";
        var observed = await OnEveryRouteAsync(source, server);
        Assert.Equal("ok S[1, 1, 5, 7]", $"{observed.Kind} {observed.Value}");
        Assert.Equal(["tick#1"], observed.HostCalls);
    }

    [Theory]
    [InlineData("X < X < X", 3)]
    [InlineData("not X or X", 2)]
    [InlineData("[X*]:X", 2)]
    [InlineData("if(false, X(1), 5)", 1)]
    [InlineData("map([], { X + 0 })", 1)]
    [InlineData("F(0) = X\nF(k) = k\nF(1)", 1)]
    public void StaticAmbiguity_RejectsEveryWrittenOccurrenceWithoutDemandingIt(string body, int occurrences)
    {
        var source = "open A, B\nA = { public X = tick() }\nB = { public X = trace(2) }\n" + body;
        var effects = 0;
        var operations = HostOperations.Create(HostOperation.Create("tick", (_, _) => { effects++; return new Result.Atom(1); }),
            HostOperation.Create("trace", (args, _) => { effects++; return args[0]; }, "x"));
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.Equal(occurrences, parsed.Diagnostics.Count(d => d.Code == DiagnosticCode.AmbiguousOpen));
        Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.AmbiguousOpen, d.Code));
        Assert.Equal(0, effects);
    }

    [Fact]
    public void GenuineInternalModuleAliasCycle_IsStillRejected()
    {
        var module = new Algorithm.User(null, [], [],
            [new Property("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("B"))),
             new Property("B", new Algorithm.Alias(null, [], [], new Expr.Resolve("A")))], []) { IsModuleElaborated = true };
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("M", module)], [new Expr.Num(1)]));
        Assert.IsType<PreEvaluationAstViolation.AliasCycle>(AlgorithmValidation.FindFirstPreEvaluationViolation(program, observations: null));
    }

    [Theory]
    [InlineData("public Bad(x) = missing\npublic X = 5", DiagnosticCode.UndeclaredIdentifier)]
    [InlineData("A(y) = y\npublic Bad(x) = A\npublic X = 5", DiagnosticCode.UnforwardableParameter)]
    [InlineData("open Missing\npublic X = 5\nabs", DiagnosticCode.UnresolvedOpenTarget)]
    public async Task InvalidModuleInFailedOperation_IsValidatedAgainAtTheNextReach(string module, DiagnosticCode code)
    {
        var server = new Modules((Url, module));
        var parsed = await Parser.ParseAsync($"F(0) = {{ M = load('{Url}')\n1 }}\nF(k) = {{ N = load('{Url}')\n1 }}\n1", server.Options());
        Assert.Empty(parsed.Diagnostics);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        foreach (var branch in family.Branches)
        {
            var region = Assert.IsType<DeferredModuleRegion>(branch.Body.DeferredRegion);
            var result = await region.MaterializeAsync(default);
            Assert.True(result.IsError);
            var report = Assert.Single(Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(result.Error).Diagnostics);
            Assert.Equal(code, report.Code);
            Assert.False(region.IsMaterialized);
        }
        Assert.Equal(1, server.Fetches[Url]);
    }

    [Theory]
    [InlineData(10)]
    [InlineData(100)]
    [InlineData(500)]
    public async Task ManyHolders_CostOneModuleAcquisitionAndOneElaboratedMember(int count)
    {
        var source = string.Join("\n", Enumerable.Range(0, count).Select(i => $"M{i} = load('{Url}')")) + "\nM0.X";
        var server = new Modules((Url, "public X = 5\npublic F(x) = x + 1"));
        var parsed = await Parser.ParseAsync(source, server.Options());
        Assert.Empty(parsed.Diagnostics);
        var first = parsed.Root.Properties[0].Value;
        Assert.All(parsed.Root.Properties, p => Assert.Same(first, p.Value));
        Assert.Equal(1, server.Fetches[Url]);
    }

    [Fact]
    public async Task SharedDeclarations_DoNotRefundWrittenSpliceSourceCharges()
    {
        const string module = "public X = 5";
        var source = $"A = load('{Url}')\nB = load('{Url}')\nA.X";
        var server = new Modules((Url, module));
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            DownloadCode = server.Download,
            AllowedHosts = ["mods.test"],
            SourceProcessingLimits = new SourceProcessingLimits { MaxAggregateSourceLength = source.Length + module.Length },
        });
        Assert.Equal(DiagnosticCode.AggregateSourceLengthExceeded, Assert.Single(parsed.Diagnostics).Code);
        Assert.Equal(1, server.Fetches[Url]);
    }

    [Fact]
    public async Task CancelledDeferredAcquisition_CanRetryWithoutPublishingAnIncompleteUnit()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var attempts = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = async (_, token) =>
            {
                if (Interlocked.Increment(ref attempts) == 1)
                {
                    entered.SetResult();
                    await Task.Delay(Timeout.Infinite, token);
                }
                return "public X = 5";
            },
        };
        var parsed = await Parser.ParseAsync($"F(0) = 0\nF(k) = {{ M = load('{Url}')\nM.X }}\n1", options);
        Assert.Empty(parsed.Diagnostics);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        var region = Assert.IsType<DeferredModuleRegion>(family.Branches[1].Body.DeferredRegion);
        using var cancellation = new CancellationTokenSource();
        var pending = region.MaterializeAsync(cancellation.Token).AsTask();
        await entered.Task;
        cancellation.Cancel();
        var rejection = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => pending);
        Assert.Equal(cancellation.Token, rejection.CancellationToken);
        Assert.False(region.IsMaterialized);
        var result = await region.MaterializeAsync(default);
        Assert.False(result.IsError);
        Assert.Equal(2, attempts);
        Assert.True(region.IsMaterialized);
    }
}
