using System.Diagnostics;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>Independent boundary probes for the X-04/X-07/X-09 final review.</summary>
public sealed class FinalCandidateBoundaryTests(ITestOutputHelper output)
{
    private static IEnumerable<T[]> DeclarationOrders<T>(IReadOnlyList<T> items)
    {
        if (items.Count == 0)
        {
            yield return [];
            yield break;
        }
        for (var i = 0; i < items.Count; i++)
            foreach (var tail in DeclarationOrders(items.Where((_, j) => i != j).ToArray()))
                yield return [items[i], .. tail];
    }

    [Fact]
    public void BuiltinAcceptanceMatchesTheLeanTableIncludingEveryFixedBuiltin()
    {
        // Hand-transcribed from builtinAcceptsArity in lean/KatLang.lean, not registry facts.
        var exact = new Dictionary<BuiltinId, int>
        {
            [BuiltinId.@if] = 3, [BuiltinId.atoms] = 1, [BuiltinId.range] = 2,
            [BuiltinId.filter] = 2, [BuiltinId.map] = 2, [BuiltinId.order] = 1,
            [BuiltinId.orderDesc] = 1, [BuiltinId.count] = 1, [BuiltinId.contains] = 2,
            [BuiltinId.first] = 1, [BuiltinId.last] = 1, [BuiltinId.distinct] = 1,
            [BuiltinId.take] = 2, [BuiltinId.skip] = 2, [BuiltinId.min] = 1,
            [BuiltinId.max] = 1, [BuiltinId.sum] = 1, [BuiltinId.avg] = 1,
            [BuiltinId.reduce] = 3,
        };
        Assert.Equal(Enum.GetValues<BuiltinId>().Order(), exact.Keys.Append(BuiltinId.@repeat).Append(BuiltinId.@while).Order());
        foreach (var id in Enum.GetValues<BuiltinId>())
        {
            var descriptor = BuiltinRegistry.GetBuiltin(id);
            for (var count = 0; count <= 20; count++)
                Assert.Equal(id == BuiltinId.@repeat ? count >= 3 : id == BuiltinId.@while ? count >= 2 : count == exact[id], descriptor.AcceptsArity(count));
        }
    }

    [Fact]
    public void ArityRenderingMetadataSurvivesCopiesAndContextsWithoutChangingEquality()
    {
        var signature = BuiltinRegistry.GetBuiltin(BuiltinId.@repeat).PlainSignature;
        var plain = new EvalError.ArityMismatch(0, 2) { Signature = signature };
        var annotated = plain with { AcceptedArity = BuiltinRegistry.GetBuiltin(BuiltinId.@repeat).ArityFacts };
        Assert.Equal(plain, annotated);
        Assert.Equal(plain.GetHashCode(), annotated.GetHashCode());
        var copy = annotated with { Span = new SourceSpan(2, 3, 2, 9) };
        Assert.Same(annotated.AcceptedArity, copy.AcceptedArity);
        Assert.Contains("expects at least 3 arguments", KatLangError.FromEvalError(copy).Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(2, 3, 2, 9), KatLangError.FromEvalError(copy).Span);
    }

    [Theory]
    [InlineData("G(p) = p\nF = { a, b = G + 0, 1 }", "'p'")]
    [InlineData("M = { public G(p) = p }\nF = { open M\n a, b = G + 0, 1 }", "'p'")]
    [InlineData("M = { public G(p) = p }\nF = { a, b = M.G + 0, 1 }", "'p'")]
    [InlineData("G(0) = 0\nG(p) = p\nF = { a, b = G + 0, 1 }", "'p'")]
    [InlineData("F = { a, b = count + 0, 1 }", "'collection'")]
    [InlineData("G((p, q)) = p + q\nF = { a, b = G + 0, 1 }", "'(p, q)'")]
    public async Task OutputRuleCoversEachLiftingSignatureSourceBeforeAnyEffect(string definitions, string parameter)
    {
        foreach (var source in new[] { definitions + "\ntrace(5)", "trace(5)\n" + definitions })
        {
            var observed = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.Equal("parse", observed.Kind);
            Assert.Empty(observed.HostCalls);
            var error = Assert.Single(observed.Errors);
            Assert.StartsWith("ExplicitParametersRequireOutput:", error, StringComparison.Ordinal);
            Assert.Contains(parameter, error, StringComparison.Ordinal);
            Assert.Contains("@ [", error, StringComparison.Ordinal);
        }
    }

    [Fact]
    public async Task ReusingAnAncestorBindingDoesNotMakeAContainerParameterized()
    {
        const string Source = "G(p) = p + 1\nOuter(p) = { F = { a, b = G + 0, 1 }\n F.a }\ntrace(Outer(4))";
        var observed = await SixRouteAgreement.OnEveryRouteAsync(Source);
        Assert.Equal("ok", observed.Kind);
        Assert.Equal("5", observed.Value);
        Assert.Equal(["trace(5)"], observed.HostCalls);
    }

    [Fact]
    public void SharedInvalidAlgorithmIsReportedOnceAndRecoveryModelStillBuilds()
    {
        var parsed = Parser.Parse("F = { a, b = x, 1 }");
        var shared = Assert.Single(parsed.Root.Properties, p => p.Name == "F").Value;
        var root = new Algorithm.User(null, [], [], [new Property("Left", shared), new Property("Right", shared)], []);
        var diagnostics = new DiagnosticBag();
        InferredParameterOutputValidator.ValidateProgram(root, diagnostics);
        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.ExplicitParametersRequireOutput, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 14, 1, 15), diagnostic.Span);
        Assert.NotNull(Semantics.SemanticModelBuilder.Build(parsed));
    }

    [Theory]
    [InlineData(0, false)]
    [InlineData(1, false)]
    [InlineData(1, true)]
    public async Task NestedDeferredOutputValidationFollowsOnlySelectedMaterializations(int selected, bool suppliesName)
    {
        const string Outer = "https://mods.test/outer.kat";
        const string Inner = "https://mods.test/inner.kat";
        var downloads = new List<string>();
        var effects = new List<string>();
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = async (url, _) =>
            {
                await Task.Yield();
                downloads.Add(url);
                return url == Outer ? "public K = 7" : suppliesName ? "public q = 3" : "public Other = 3";
            },
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("trace", async (args, _) =>
            {
                await Task.Yield();
                effects.Add(SixRouteAgreement.Neutral(args[0]));
                return args[0];
            }, "x")),
        };
        var source = $"F(0) = 0\nF(n) = {{\n open '{Outer}'\n H(0) = 0\n H(m) = {{\n  open '{Inner}'\n  G = {{ a, b = q, 1 }}\n  G.a + K + m\n }}\n H(n)\n}}\ntrace(F({selected}))";
        var result = await KatLangEngine.RunAsync(source, options);
        if (selected == 0 || suppliesName)
        {
            var success = Assert.IsType<RunResult.Success>(result);
            Assert.Equal(selected == 0 ? "0" : "11", SixRouteAgreement.Neutral(success.Value));
            Assert.Equal([selected == 0 ? "0" : "11"], effects);
        }
        else
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(result);
            var error = Assert.Single(failure.Errors);
            Assert.Equal(KatLangErrorCode.ExplicitParametersRequireOutput, error.Code);
            Assert.Equal(new SourceSpan(7, 16, 7, 17), error.Span);
            Assert.Empty(effects);
        }
        Assert.Equal(selected == 0 ? Array.Empty<string>() : [Outer, Inner], downloads);
    }

    [Fact]
    public void DemandRefusalSetMatchesIndependentReachabilityForHardAndSoftCycles()
    {
        var random = new Random(5901);
        for (var sample = 0; sample < 300; sample++)
        {
            var count = random.Next(2, 14);
            var nodes = Enumerable.Range(0, count).Select(i =>
            {
                var hard = Enumerable.Range(0, count).Where(j => j != i && random.Next(6) == 0).ToArray();
                var soft = Enumerable.Range(0, count).Where(j => j != i && !hard.Contains(j) && random.Next(6) == 0).ToArray();
                return new PropertyDependencyNode(i, hard) { SoftSiblingDependencyIndices = soft };
            }).ToArray();
            var properties = Enumerable.Range(0, count).Select(i => new Property($"P{i}", new Algorithm.User(null, [], [], [], [new Expr.Num(0)]))).ToArray();
            var graph = new PropertyDependencyGraph(properties, properties.Select((p, i) => (p.Name, i)).ToDictionary(p => p.Name, p => p.i), nodes);
            var reach = new bool[count, count];
            for (var i = 0; i < count; i++)
                foreach (var j in nodes[i].SiblingDependencyIndices.Concat(nodes[i].SoftSiblingDependencyIndices)) reach[i, j] = true;
            for (var k = 0; k < count; k++)
                for (var i = 0; i < count; i++)
                    for (var j = 0; j < count; j++) reach[i, j] |= reach[i, k] && reach[k, j];
            var expected = Enumerable.Range(0, count).Where(i => reach[i, i]).ToHashSet();
            bool changed;
            do
            {
                changed = false;
                for (var i = 0; i < count; i++)
                    if (nodes[i].SiblingDependencyIndices.Any(expected.Contains)) changed |= expected.Add(i);
            } while (changed);
            Assert.Equal(expected.Order(), graph.CyclicIndices.Order());
        }
    }

    [Fact]
    public void ManyComponentsAndDemandRefusalsStayStackSafeAndBounded()
    {
        const int Count = 100_000;
        // 25,000 hard two-member components and tails; a soft back edge absorbs the first tail
        // node into each combined component, exercising the final settlement pass at scale.
        var nodes = Enumerable.Range(0, Count).Select(i => new PropertyDependencyNode(i,
            (i % 4) switch { 0 => [i + 1], 1 => [i - 1], _ => [i - 1] })
            { SoftSiblingDependencyIndices = i % 4 == 0 ? [i + 2] : [] }).ToArray();
        var properties = Enumerable.Range(0, Count).Select(i => new Property($"P{i}", new Algorithm.User(null, [], [], [], [new Expr.Num(0)]))).ToArray();
        var graph = new PropertyDependencyGraph(properties, properties.Select((p, i) => (p.Name, i)).ToDictionary(p => p.Name, p => p.i), nodes);
        IReadOnlyList<int>? order = null;
        IReadOnlySet<int>? refusals = null;
        var timer = Stopwatch.StartNew();
        var thread = new Thread(() => { order = graph.TopologicalOrder; refusals = graph.CyclicIndices; }, maxStackSize: 1024 * 1024);
        thread.Start();
        thread.Join();
        output.WriteLine($"100,000 nodes in 25,000 SCCs and tails, both graph projections: {timer.ElapsedMilliseconds} ms");
        Assert.Equal(Enumerable.Range(0, Count), order);
        Assert.NotNull(refusals);
        Assert.Equal(Count, refusals.Count);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public async Task OpenedConsumerOutsideAMixedCycleReadsTheSettledMemberSignature(bool hardCycle)
    {
        string[] definitions = ["C = { open A\n V + z }", "A = { open D\n public V = B + x\n 0 }", hardCycle ? "B = { H = A.V + 0\n y + 1 }" : "B(p) = p + 1", "D = { open A\n public W = 1\n 0 }"];
        var finalName = hardCycle ? "y" : "p";
        foreach (var declared in DeclarationOrders(definitions))
        {
            var source = string.Join("\n", declared) + "\ntrace(C(1, 2, 3))";
            var parsed = SourceProvenance.ParseValid(source);
            var consumer = Assert.Single(parsed.Root.Properties, p => p.Name == "C");
            Assert.Equal($"C(z, x, {finalName})", CallableSignature.FromAlgorithm("C", consumer.Value).DisplayText);
            var model = Semantics.SemanticModelBuilder.Build(parsed.Parsed);
            Assert.Equal(["z", "x", finalName], Assert.Single(model.FindProperties("C")).Parameters.Select(p => p.DisplayName));
            var observed = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.Equal("ok", observed.Kind);
            Assert.Equal("7", observed.Value);
            Assert.Equal(["trace(7)"], observed.HostCalls);
        }
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public async Task OutputlessOpenedConsumerOfAMixedCycleIsRejectedAfterSettlement(bool hardCycle)
    {
        string[] definitions = ["F = { open A\n a, b = V + 0, 1 }", "A = { open D\n public V = B + x\n 0 }", hardCycle ? "B = { H = A.V + 0\n y + 1 }" : "B(p) = p + 1", "D = { open A\n public W = 1\n 0 }"];
        foreach (var declared in DeclarationOrders(definitions))
        {
            var source = string.Join("\n", declared) + "\ntrace(5)";
            var observed = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.Equal("parse", observed.Kind);
            Assert.Empty(observed.HostCalls);
            var error = Assert.Single(observed.Errors);
            Assert.StartsWith("ExplicitParametersRequireOutput:", error, StringComparison.Ordinal);
            Assert.Contains($"the implicit parameters 'x' and '{(hardCycle ? "y" : "p")}'", error, StringComparison.Ordinal);
            var line = Array.IndexOf(source.Split('\n'), "F = { open A") + 1;
            Assert.EndsWith($"@ [{line}:1, {line}:2)", error, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void LargeSourceCycleAndConsumersDoNotGrowTheSiblingCallStack()
    {
        const int Count = 2_000;
        var source = string.Join("\n", Enumerable.Range(0, Count).Select(i => $"C{i} = P{i} + 0")
            .Concat(Enumerable.Range(0, Count).Select(i => $"P{i} = {{ H = P{(i + 1) % Count} + 0\n x + 1 }}"))) + "\n0";
        ParseResult? parsed = null;
        Exception? error = null;
        var timer = Stopwatch.StartNew();
        var thread = new Thread(() =>
        {
            try { parsed = Parser.Parse(source); }
            catch (Exception exception) { error = exception; }
        }, maxStackSize: 1024 * 1024);
        thread.Start();
        thread.Join();
        output.WriteLine($"2,000 source cycle members + 2,000 consumers: {timer.ElapsedMilliseconds} ms");
        Assert.Null(error);
        Assert.NotNull(parsed);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        Assert.Equal(Count * 2, parsed.Root.Properties.Count);
        Assert.All(parsed.Root.Properties.Where(p => p.Name.StartsWith('C')), p => Assert.Equal(["x"], p.Value.Params));
    }
}
