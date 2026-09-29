using KatLang.Semantics;

namespace KatLang.Tests;

public class Fe3HostileReviewTests
{
    private static Algorithm.User Body(params Expr[] rows) => new(null, [], [], [], new OutputBundle(rows));

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LiftingTemplateWithEmptyGroups_MatchesOrdinaryPatternMerge(bool nested)
    {
        var interner = new ImplicitSignatureTemplateInterner(null);
        ParameterPattern empty = new SequenceValueParameterPattern([]);
        var head = nested ? new SequenceValueParameterPattern([empty, new CaptureParameterPattern("h")]) : empty;
        var tail = interner.InternFlat([new CaptureParameterPattern("v")]);
        var template = ImplicitSignatureTemplate.Compose([interner.Freeze(head)], tail);
        Algorithm Resolve(IReadOnlyList<ParameterPattern> patterns)
        {
            var owner = Body(new Expr.Param("v")) with { ParameterPatterns = patterns };
            return ImplicitArgumentResolver.ResolvePrevalidated(Body(new Expr.Num(1)) with
            {
                Properties = [new Property("A", owner), new Property("B", Body(new Expr.Resolve("A")))],
            });
        }

        // Empty structural patterns are host-constructible. Lifting omits empty
        // groups recursively; compact storage must use the same merge as a list.
        var ordinary = Resolve(template.ToArray()).Properties.Single(p => p.Name == "B").Value;
        var compact = Resolve(template).Properties.Single(p => p.Name == "B").Value;
        Assert.Equal(ordinary.ParameterPatterns.Select(p => p.DisplayName), compact.ParameterPatterns.Select(p => p.DisplayName));
        Assert.Equal(ordinary.Params, compact.Params);
    }

    [Theory]
    [InlineData(16, 16)]
    [InlineData(32, 32)]
    [InlineData(64, 64)]
    [InlineData(64, 8)]
    [InlineData(8, 64)]
    public void WrappedOwners_KeepTheirComposedSignatureAndForwardingTail(int owners, int width)
    {
        var source = $"G = {string.Join(", ", Enumerable.Range(0, width).Select(i => $"v{i}"))}\n"
            + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = abs(G) + w{i}\nB{i} = abs(A{i})\n")) + "1";
        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(diagnostics);
        var observed = new FrontEndTraversalObservations();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observed);
        for (var i = 0; i < owners; i++)
            Assert.Same(resolved.Properties.Single(p => p.Name == $"A{i}").Value.ParameterPatterns,
                resolved.Properties.Single(p => p.Name == $"B{i}").Value.ParameterPatterns);
        Assert.InRange(observed.SignatureTemplateSlotsBuilt, 0, width + owners);
        Assert.InRange(observed.ImplicitArgumentSlotsBuilt, 0, 2 * width + owners);
        var preflight = new FrontEndTraversalObservations();
        Assert.Null(AstStructuralPreflight.Check(resolved, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive, preflight));
        Assert.InRange(preflight.StructuralPreflightEdges, 0, 24L * (owners + width));
        var exposure = new FrontEndTraversalObservations();
        PropertyExposureResolver.Resolve(resolved, exposure);
        // Completed seeds of at most eight entries deliberately copy their small
        // payload. This bounded per-owner delta is independent of unbounded width.
        var smallCopies = width <= PropertyDependencyGraphBuilder.SummarySeed.CopiedCompletedEntries ? (long)owners * width : 0;
        Assert.InRange(exposure.SummaryResidualNameProbes, 0, 4L * (owners + width) + smallCopies);
    }

    [Fact]
    public void LiftedNestedPatterns_AreSnapshotsWithNoPublicMutationRoute()
    {
        var parsed = SourceProvenance.ParseValid("G((a, b)) = a + b\nA = G + 1\nB = G + 2\nA((3, 4)), B((5, 6))");
        var g = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(p => p.Name == "G").Value);
        var a = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(p => p.Name == "A").Value);
        var b = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(p => p.Name == "B").Value);
        Assert.Same(a.ParameterPatterns, b.ParameterPatterns);
        Assert.Equal(2, a.ParameterCount);
        var lifted = Assert.IsType<SequenceValueParameterPattern>(Assert.Single(a.ParameterPatterns));
        if (lifted.Items is IList<ParameterPattern> items)
            Assert.Throws<NotSupportedException>(() => items[0] = new CaptureParameterPattern("poison"));
        var original = Assert.IsType<SequenceValueParameterPattern>(Assert.Single(g.ParameterPatterns));
        if (original.Items is IList<ParameterPattern> originalItems && !originalItems.IsReadOnly)
            originalItems[0] = new CaptureParameterPattern("changed");
        Assert.Equal(["a", "b"], a.Params);
        Assert.Equal(a.Params, b.Params);
        Assert.Equal(2, a.ParameterCount);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task TemplateOwners_AreIndependentCallables_AndEveryCallIsFresh(bool async)
    {
        var events = new List<string>();
        var gates = Enumerable.Range(0, 4).Select(_ => new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
        var entered = Enumerable.Range(0, 4).Select(_ => new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
        using var cancellation = new CancellationTokenSource();
        Result Tick(IReadOnlyList<Result> values)
        {
            events.Add(Assert.IsType<Result.Atom>(values[0]).Value.ToString());
            return new Result.Atom(events.Count);
        }
        var operations = async
            ? HostOperations.Create(HostOperation.CreateAsync("Tick", async (values, token) =>
            {
                Assert.Equal(cancellation.Token, token);
                var result = Tick(values);
                var index = events.Count - 1;
                entered[index].SetResult();
                await gates[index].Task.WaitAsync(token);
                return result;
            }, "owner"))
            : HostOperations.Create(HostOperation.Create("Tick", (values, _) => Tick(values), "owner"));
        // Two owners of one shared nonempty template are two callables: every explicit call is
        // fresh. Since Q-03 an owner LIFTS only from a callee that requires a supplied argument,
        // so a root-level lifting owner, which has no enclosing parameter binding to reuse (Q-04),
        // requires one itself — a shared template's owners are called, never property-cached (a
        // collecting-only `G` would be read as a value, lifting nothing). Each owner's `Tick`
        // runs once per call, and the calls are independent.
        const string source = "G(t, *xs) = t + xs.count\nA = G + Tick(10)\nB = G + Tick(20)\nA(0), B(0), A(0, 5), B(0, 5, 6)";
        var options = new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token };
        var parsed = async ? await Parser.ParseAsync(source, options) : Parser.Parse(source, options);
        Assert.Empty(parsed.Diagnostics);
        Assert.Same(parsed.Root.Properties.Single(p => p.Name == "A").Value.ParameterPatterns,
            parsed.Root.Properties.Single(p => p.Name == "B").Value.ParameterPatterns);
        Assert.Equal(["t", "xs"], parsed.Root.Properties.Single(p => p.Name == "A").Value.Params);
        var run = async ? KatLangEngine.RunAsync(source, options) : Task.FromResult(KatLangEngine.Run(source, options));
        if (async)
            for (var i = 0; i < 4; i++)
            {
                await entered[i].Task.WaitAsync(TimeSpan.FromSeconds(15));
                Assert.False(run.IsCompleted);
                gates[i].SetResult(new Result.Atom(0));
            }
        Assert.Equal("1\n2\n4\n6", (await run).ToDisplayString().ReplaceLineEndings("\n"));
        Assert.Equal(["10", "20", "10", "20"], events);
    }

    [Fact]
    public async Task CancelledTemplateOwner_DoesNotPoisonOtherOwnersOrFreshRuns()
    {
        using var cancellation = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var block = true;
        var operations = HostOperations.Create(HostOperation.CreateAsync("Tick", async (_, token) =>
        {
            var index = ++calls;
            if (block && index == 2)
            {
                Assert.Equal(cancellation.Token, token);
                entered.SetResult();
                return await gate.Task.WaitAsync(token);
            }
            return new Result.Atom(index);
        }, "x"));
        var parsed = await Parser.ParseAsync("G = Tick(x)\nA = G + 10\nB = G + 20\nA(1), B(2), A(3)", new RunOptions { HostOperations = operations });
        Assert.Empty(parsed.Diagnostics);
        Assert.Same(parsed.Root.Properties.Single(p => p.Name == "A").Value.ParameterPatterns,
            parsed.Root.Properties.Single(p => p.Name == "B").Value.ParameterPatterns);
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var run = Evaluator.RunCountedObservedAsync(program, hostOperations: operations, cancellationToken: cancellation.Token).AsTask();
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(15));
        Assert.False(run.IsCompleted);
        cancellation.Cancel();
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await run);
        Assert.Equal(cancellation.Token, error.CancellationToken);
        calls = 0;
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedObservedAsync(program, hostOperations: operations, cancellationToken: cancellation.Token));
        Assert.Equal(0, calls);
        block = false;
        var retry = await Evaluator.RunCountedObservedAsync(program, hostOperations: operations);
        Assert.False(retry.Result.IsError);
        Assert.Equal([11m, 22m, 13m], retry.Result.Value.Value.ToAtoms());
        Assert.Equal(3, calls);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EditorMetadata_ComposesGroupedAndCollectingHeads(bool grouped)
    {
        var interner = new ImplicitSignatureTemplateInterner(null);
        var tail = interner.InternFlat(Enumerable.Range(0, 32).Select(i => (ParameterPattern)new CaptureParameterPattern($"v{i}")).ToArray());
        var properties = Enumerable.Range(0, 12).Select(i =>
        {
            ParameterPattern head = grouped
                ? new SequenceValueParameterPattern([new CaptureParameterPattern($"h{i}"), new CaptureParameterPattern($"j{i}")])
                : new CaptureParameterPattern($"h{i}", Kind: ParameterKind.Collecting);
            var owner = Body(new Expr.Param($"h{i}")) with { ParameterPatterns = ImplicitSignatureTemplate.Compose([interner.Freeze(head)], tail) };
            return new Property($"A{i}", owner) { DeclarationSpans = [new SourceSpan(i + 1, 1, i + 1, 3)] };
        }).ToArray();
        var model = SemanticModelBuilder.Build(Body() with { Properties = properties });
        var infos = model.PropertyInfos.Where(p => p.Name.StartsWith('A')).ToArray();
        Assert.Equal(12, infos.Length);
        var first = infos[0].Parameters.Single(p => p.Name == "v31");
        Assert.All(infos, info => Assert.Same(first, info.Parameters.Single(p => p.Name == "v31")));
        var baseline = SemanticModelBuilder.Build(Body() with { Properties = properties.Select(p => p.WithValue(
            ((Algorithm.User)p.Value) with { ParameterPatterns = p.Value.ParameterPatterns.ToArray() })).ToArray() });
        Assert.Equal(baseline.PropertyInfos.Select(p => p.DisplaySignature), model.PropertyInfos.Select(p => p.DisplaySignature));
        Assert.Equal(baseline.PropertyInfos.Select(p => p.GetDisplaySignature(PropertyCallStyle.Dot)), model.PropertyInfos.Select(p => p.GetDisplaySignature(PropertyCallStyle.Dot)));
    }

    /// <summary>
    /// The collision validator is the one context that meets completed (lifted) signatures, and it
    /// extends a context by ONE layer for a shared template of at least
    /// <c>TemplateLayerMinimum</c> names — entries otherwise, and a composed signature's owner-local
    /// head as entries ABOVE its layer (FE-3). Whatever the mix, its lookup must answer exactly like a
    /// nearest-declaration dictionary: a property collides iff a parameter of its own or an enclosing
    /// owner has its name, and the report names the NEAREST such declaration. (Until Q-04 this test
    /// pinned the same law for the detector's parameter-ownership map, which no longer layers: detection
    /// runs before any signature is lifted.)
    /// </summary>
    [Theory]
    [InlineData(7)]
    [InlineData(8)]
    [InlineData(9)]
    public void CollisionBindingLayers_MatchNearestDeclarationDictionary(int width)
    {
        const int levels = 16;
        var interner = new ImplicitSignatureTemplateInterner(null);
        var visible = new Dictionary<string, SourceSpan>(StringComparer.Ordinal);
        var signatures = new IReadOnlyList<ParameterPattern>[levels];
        var probes = new List<(int Level, string Name, SourceSpan Span, SourceSpan? Nearest)>();
        for (var level = 0; level < levels; level++)
        {
            // Level `level` declares p{level}..p{level + width - 1} (overlapping the enclosing levels'
            // names) as a shared template; an even level also declares `q` as a composed head.
            var tailCaptures = Enumerable.Range(0, width)
                .Select(i => new CaptureParameterPattern($"p{level + i}", new SourceSpan(100 + level, 1 + i, 100 + level, 2 + i)))
                .ToArray();
            var tail = interner.InternFlat(tailCaptures);
            foreach (var capture in tailCaptures)
                visible[capture.Name] = capture.Parameter.Span!.Value;
            if (level % 2 == 0)
            {
                var head = new CaptureParameterPattern("q", new SourceSpan(300 + level, 1, 300 + level, 2));
                signatures[level] = ImplicitSignatureTemplate.Compose([interner.Freeze(head)], tail);
                visible["q"] = head.Parameter.Span!.Value;
            }
            else
            {
                signatures[level] = tail;
            }

            // A property for every name visible here, plus two that are not: the next level's first
            // new name and a name nothing declares.
            var names = visible.Keys.Append($"p{level + width}").Append("missing").ToArray();
            for (var k = 0; k < names.Length; k++)
            {
                SourceSpan? nearest = visible.TryGetValue(names[k], out var span) ? span : null;
                probes.Add((level, names[k], new SourceSpan(1000 + level, 1 + k, 1000 + level, 2 + k), nearest));
            }
        }

        Algorithm.User? inner = null;
        for (var level = levels - 1; level >= 0; level--)
        {
            var properties = probes
                .Where(probe => probe.Level == level)
                .Select(probe => new Property(probe.Name, Body(new Expr.Num(0))) { DeclarationSpans = [probe.Span] })
                .ToList();
            if (inner is not null)
                properties.Add(new Property($"N{level}", inner));
            inner = Body() with { ParameterPatterns = signatures[level], Properties = properties };
        }

        var diagnostics = new DiagnosticBag();
        var observed = new FrontEndTraversalObservations();
        new ParameterPropertyCollisionValidator(diagnostics) { TraversalObservations = observed }.VisitAlgorithm(inner!);

        Assert.Equal(width >= ParameterPropertyCollisionValidator.ParameterBindings.TemplateLayerMinimum ? levels : 0, observed.ContextTemplateLayers);
        Assert.All(diagnostics, diagnostic => Assert.Equal(DiagnosticCode.ParameterPropertyCollision, diagnostic.Code));
        var reported = diagnostics.ToDictionary(diagnostic => diagnostic.Span!.Value, diagnostic => diagnostic.Message);
        foreach (var probe in probes)
        {
            if (probe.Nearest is { } declared)
            {
                Assert.True(reported.TryGetValue(probe.Span, out var message), $"'{probe.Name}' at level {probe.Level} was not reported.");
                Assert.EndsWith($"The parameter is declared at line {declared.Start.Line}, column {declared.Start.Column}.", message);
            }
            else
            {
                Assert.False(reported.ContainsKey(probe.Span), $"'{probe.Name}' at level {probe.Level} was reported.");
            }
        }

        Assert.Equal(probes.Count(probe => probe.Nearest is not null), diagnostics.Count);
    }

    private sealed class SlowReach : AstWalker
    {
        public bool Found;
        public override void VisitAlgorithm(Algorithm algorithm) => Found = true;
    }

    [Fact]
    public void NestedReachIndex_MatchesIndependentWalkerOnGeneratedDags()
    {
        var leaf = new Expr.Num(0);
        var wrappers = new Func<Expr, Expr>[] {
            e => new Expr.Unary(UnaryOp.Minus, e), e => new Expr.Binary(BinaryOp.Add, leaf, e),
            e => new Expr.Comparison(leaf, [new ComparisonLink(ComparisonOp.Eq, e)]),
            e => new Expr.Index(leaf, e), e => new Expr.SequenceConstruct(leaf, e),
            e => new Expr.SequenceSpread(e), e => new Expr.ListLiteral([leaf, e]),
            e => new Expr.DotCall(leaf, "F", [e]), e => new Expr.DotCall(e, "F"),
            e => new Expr.Grace(e, 1), e => new Expr.Capture([leaf, e]),
            e => new Expr.Call(leaf, [e]), e => new Expr.Call(e, [leaf]) };
        var rng = new Random(17391);
        for (var seed = 0; seed < 40; seed++)
        {
            var index = new NestedReachIndex();
            var nodes = new List<Expr>(ExprVariantCatalog.Samples.Values);
            nodes.Add(new Expr.AlgorithmExpr(Body()));
            for (var i = 0; i < 70; i++) nodes.Add(wrappers[rng.Next(wrappers.Length)](nodes[rng.Next(nodes.Count)]));
            foreach (var node in nodes) { var oracle = new SlowReach(); oracle.VisitExpr(node); Assert.Equal(oracle.Found, index.Reaches(node)); }
        }
    }
}
