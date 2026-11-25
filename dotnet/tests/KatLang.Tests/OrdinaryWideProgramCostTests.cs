using System.Collections.Concurrent;
using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// Ordinary wide source programs pay for their declarations, not for repeated whole-program setup. Each fact a fast path
/// here relies on has a control that fails if the path skipped real work: the raw gate's height decides the elaboration
/// gate only because it IS that gate's rejection test; an admitted graph without an open skips the provider validator only
/// because no pass introduces one; an empty summary seed expands to itself at any level; a forked key table is isolated
/// from its source in both directions. The allocation slopes back these with a design-independent bound per shape.
/// Run the matching timings with <c>--filter "*FrontEndOrdinaryWidthBenchmarks*"</c>.
/// </summary>
public class OrdinaryWideProgramCostTests
{
    private static string Flat(int width)
        => string.Concat(Enumerable.Range(0, width).Select(i => $"V{i} = {i}\n")) + $"V{width - 1}\n";

    private static string Chain(int width)
        => "V0 = 1\n" + string.Concat(Enumerable.Range(1, width - 1).Select(i => $"V{i} = V{i - 1} + 1\n")) + $"V{width - 1}\n";

    private static string Wide(int width)
        => string.Concat(Enumerable.Range(0, width).Select(i => $"W{i}(y{i}) = {{\nInner{i} = y{i} * 2\nInner{i} + 1\n}}\n")) + $"W{width - 1}(3)\n";

    private static long Allocation(string source)
    {
        // The first parse settles lazily created statics; the measured one is this source's own work.
        SourceProvenance.ParseValid(source);
        var before = GC.GetAllocatedBytesForCurrentThread();
        Parser.Parse(source);
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    // ── Allocation per declaration, by shape ─────────────────────────────────

    /// <summary>
    /// The slope of one more declaration over a 400-declaration window, so fixed setup cancels. Measured on this Debug build
    /// the repaired front end allocates 19.9, 44.2 and 76.3 KB; the pre-repair front end allocated 26.1, 49.7 and 88.0 KB and
    /// exceeds every bound: its pure key tables paid persistent nodes per key, the query table stored each key twice, every
    /// empty summary seed built a content string, and a program without an <c>open</c> still paid a presence memo per node.
    /// The three shapes keep the cost from moving between per-declaration, local-body and dependency work.
    /// </summary>
    [Theory]
    [InlineData("flat", 23_000)]
    [InlineData("chain", 47_000)]
    [InlineData("wide", 82_000)]
    public void AllocationPerDeclaration_StaysWithinItsShapesBound(string shape, long bytesPerDeclaration)
    {
        Func<int, string> source = shape switch { "flat" => Flat, "chain" => Chain, _ => Wide };

        var slope = (Allocation(source(800)) - Allocation(source(400))) / 400;

        Assert.True(slope <= bytesPerDeclaration, $"{shape}: one more declaration allocated {slope} bytes (bound {bytesPerDeclaration}).");
    }

    // ── The elaboration gate reuses the raw gate's measurement ───────────────

    private static Expr Nested(int depth)
    {
        Expr current = new Expr.Num(1m);
        for (var i = 1; i < depth; i++)
            current = new Expr.Unary(UnaryOp.Minus, current);
        return current;
    }

    /// <summary>The fact the reuse rests on: the measured height is exactly the walk's rejection test, at every limit near it.</summary>
    [Theory]
    [InlineData(1)]
    [InlineData(299)]
    [InlineData(300)]
    [InlineData(301)]
    [InlineData(639)]
    public void MeasuredHeight_DecidesEveryLowerLimitLikeTheWalk(int depth)
    {
        var root = Nested(depth);

        Assert.Null(AstStructuralPreflight.CheckMeasuringHeight(root, 640, AstConsumerProfile.FullyRecursive, out var height));

        Assert.Equal(depth, height);
        foreach (var limit in new[] { depth - 1, depth, depth + 1, EvaluationLimits.MaxSupportedAstDepth })
        {
            var rejected = limit >= 1 && AstStructuralPreflight.Check(root, limit, AstConsumerProfile.FullyRecursive) is not null;
            Assert.Equal(limit >= 1 && height > limit, rejected);
        }
    }

    [Fact]
    public void MeasuredHeight_IsUnavailableWhenTheRawGateRejects()
    {
        Assert.NotNull(AstStructuralPreflight.CheckMeasuringHeight(Nested(50), 10, AstConsumerProfile.FullyRecursive, out var height));
        Assert.Equal(-1, height);
    }

    /// <summary>
    /// A source between the elaboration ceiling and the raw cap passes the raw gate and must still be refused at elaboration:
    /// reusing the height never turns the lower gate off.
    /// </summary>
    [Fact]
    public void ASourceBetweenTheGates_IsStillRefusedAtElaboration()
    {
        var source = AstStructuralDepthTests.BracketChainComposition(levels: 22, chainOps: 28);
        Assert.False(Parser.ParseSyntax(source).HasErrors);

        var result = Parser.Parse(source);

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic => diagnostic.Message.Contains(
            $"structural AST depth limit of {EvaluationLimits.MaxSupportedAstDepth}", StringComparison.Ordinal));
        Assert.Empty(Assert.IsType<Algorithm.User>(result.Root).Properties);
    }


    /// <summary>
    /// The reuse must not keep what it measured: the pipeline holds its tree only in the hand-off, so the raw syntax tree
    /// stays collectible once the pass that took it has finished. The gate's answer is the last use of the reference.
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void TheRawGateMeasurement_DoesNotRetainTheRawTree(bool gateBeforeHandoff)
    {
        var input = FrontEndPipeline.ElaborationInput.Parse("A = 1\nA\n", new DiagnosticBag());
        var raw = ReplaceRawTree(input, gateBeforeHandoff);

        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();

        Assert.False(raw.IsAlive);
        GC.KeepAlive(input);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static WeakReference ReplaceRawTree(FrontEndPipeline.ElaborationInput input, bool gateBeforeHandoff)
    {
        // Ordinary elaboration gates first. With a downloader, the loader takes and may replace the raw tree first.
        if (gateBeforeHandoff)
            Assert.True(input.ConsumeRawGateMeasurement(EvaluationLimits.MaxSupportedAstDepth));
        var raw = new WeakReference(input.Take());
        input.Put(new Algorithm.User(null, [], [], [], []));
        return raw;
    }

    /// <summary>A replaced tree was never measured: the gate walks it even when the raw tree it replaced would have passed.</summary>
    [Fact]
    public void TheRawGateMeasurement_DoesNotCoverAReplacedTree()
    {
        var input = FrontEndPipeline.ElaborationInput.Parse("A = 1\nA\n", new DiagnosticBag());

        input.Put(new Algorithm.User(null, [], [], [], []));

        Assert.False(input.ConsumeRawGateMeasurement(EvaluationLimits.MaxSupportedAstDepth));
    }

    [Fact]
    public void TheRawGateMeasurement_IsOneShot_AndHonorsTheLimit()
    {
        var input = FrontEndPipeline.ElaborationInput.Parse("A = 1\nA\n", new DiagnosticBag());
        Assert.False(input.ConsumeRawGateMeasurement(maxDepth: 1));
        Assert.False(input.ConsumeRawGateMeasurement(EvaluationLimits.MaxSupportedAstDepth));
    }

    // ── A program without open needs no provider validation ──────────────────

    [Theory]
    [InlineData("open Nope\n1", true)]
    [InlineData("A = {\nopen Nope\n1\n}\nA", true)]
    [InlineData("F(x) = {\nG = {\nopen Nope\nx\n}\nG\n}\nF(1)", true)]
    [InlineData("F(0) = 1\nF(n) = {\nopen Nope\nn\n}\nF(2)", true)]
    [InlineData("F({\nopen Nope\n1\n})\nF(x) = x", true)]
    [InlineData("A = 1\nA", false)]
    [InlineData("F(x) = {\nG = x\nG\n}\nF(1)", false)]
    public void AdmissionSeesAnOpenWhereverItIsWritten(string source, bool hasOpen)
    {
        var syntax = Parser.ParseSyntax(source);
        Assert.False(syntax.HasErrors);

        var (operation, _) = StaticStructureAdmission.Create(syntax.Root);

        Assert.Equal(hasOpen, !operation.AdmittedWithoutOpens);
        Assert.Equal(hasOpen, Parser.Parse(source).Diagnostics.Any(diagnostic => diagnostic.Code == DiagnosticCode.UnresolvedOpenTarget));
    }


    private static bool ReachesAnOpen(Algorithm root)
    {
        var walker = new OpenWalker();
        walker.VisitAlgorithm(root);
        return walker.Found;
    }

    // Use the validator's traversal family rather than admission's child enumerator.
    private sealed class OpenWalker : AstWalker
    {
        private readonly HashSet<object> _seen = new(ReferenceEqualityComparer.Instance);
        public bool Found { get; private set; }
        protected override bool VisitsExplicitParameterDeclarations => false;

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            Found |= algorithm.Opens.Count > 0;
            if (!Found && _seen.Add(algorithm)) base.VisitAlgorithm(algorithm);
        }

        public override void VisitExpr(Expr expression)
        {
            if (!Found && _seen.Add(expression)) base.VisitExpr(expression);
        }
    }

    /// <summary>
    /// The law behind the skip, over every program of the executable specification: the admitted tree and the finished tree
    /// agree on whether any open exists, so no elaboration pass introduces (or a skip could miss) a provider question.
    /// </summary>
    [Fact]
    public void AdmissionsAnswerAboutOpens_HoldsForTheFinishedTree_AcrossTheSpecification()
    {
        var withOpens = 0;
        var withoutOpens = 0;

        foreach (var specCase in LanguageSpecCorpus.AllCases())
        {
            var syntax = Parser.ParseSyntax(specCase.Source);
            var finished = Parser.Parse(specCase.Source);
            if (syntax.HasErrors || finished.Root is not Algorithm.User { Properties.Count: > 0 } and not Algorithm.User { Output.Count: > 0 })
                continue;

            var admittedWithoutOpens = StaticStructureAdmission.Create(syntax.Root).Operation.AdmittedWithoutOpens;

            Assert.Equal(admittedWithoutOpens, !ReachesAnOpen(syntax.Root));
            if (admittedWithoutOpens || !finished.HasErrors)
                Assert.True(admittedWithoutOpens == !ReachesAnOpen(finished.Root), specCase.Id);
            if (admittedWithoutOpens) withoutOpens++; else withOpens++;
        }

        Assert.True(withOpens > 10 && withoutOpens > 100, $"The corpus no longer exercises both answers: {withOpens}, {withoutOpens}.");
    }

    /// <summary>
    /// A module's open is not written in the main source: the pipeline admits the composed tree, so a refused open inside a
    /// loaded module is still validated, with the exact diagnostic a local one gets, at its import site.
    /// </summary>
    [Fact]
    public async Task AnOpenOnlyInALoadedModule_IsStillValidated()
    {
        const string url = "https://mods.test/unit.kat";
        const string source = $"M = load('{url}')\nM.V\n";
        var modules = new ModuleRouteAgreement.Modules((url, "\n\nopen Nope\npublic V = 1\n"));

        var parsed = await Parser.ParseAsync(source, modules.Options());

        Assert.False(ReachesAnOpen(SourceProvenance.ParseSyntaxValidRoot(source)));
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 1, 1, 2), diagnostic.Span);
        Assert.Contains("Nope", diagnostic.Message, StringComparison.Ordinal);
    }

    /// <summary>A valid and an invalid open keep their answers, in the order and number the validator reports them.</summary>
    [Fact]
    public void OpenValidationKeepsItsDiagnosticsWhenAnOpenExists()
    {
        var source = "open Lib\nLib = {\npublic X = 1\n2\n}\nA = {\nopen Nope\n1\n}\nB = {\nopen Gone\n1\n}\nA + B + X\n";

        Assert.False(Parser.ParseSyntax(source).HasErrors);
        var parsed = Parser.Parse(source);
        var opens = parsed.Diagnostics.Where(diagnostic => diagnostic.Code == DiagnosticCode.UnresolvedOpenTarget).ToList();

        Assert.Equal(2, parsed.Diagnostics.Count);
        Assert.Equal(2, opens.Count);
        Assert.Contains("Nope", opens[0].Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(7, 6, 7, 10), opens[0].Span);
        Assert.Contains("Gone", opens[1].Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(11, 6, 11, 10), opens[1].Span);
    }

    // ── Releasing the operation before exposure ──────────────────────────────

    [Fact]
    public void ExposureReceivesCompletedFactsWithoutTheEagerProducer()
    {
        var input = FrontEndPipeline.ElaborationInput.Parse("Base = 10\nScale(x) = x * Base\nScale(4)\n", new DiagnosticBag());
        Assert.True(input.ConsumeRawGateMeasurement(EvaluationLimits.MaxSupportedAstDepth));
        var modules = new ModuleUnits();

        var rejection = FrontEndPipeline.CompleteBeforeExposure(input, input.Diagnostics, hostOperations: null, modules,
            hasDeferredModuleRegions: false, sourceProcessingLimits: null, out var producer, CancellationToken.None);

        Assert.Null(rejection);
        Assert.Null(producer);
        Assert.False(input.Diagnostics.HasReportedErrors);
        AssertProducerFreeFacts(input.Current);

        var exposed = PropertyExposureResolver.Resolve(input.Take(), observations: null, modules: modules);
        Assert.True(Assert.IsType<CompletedStaticStructures>(exposed.CompletedStructure!.Facts).IsSealed);
    }

    private static IEnumerable<Type> ReachableTypes(object root)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance) { root };
        var pending = new Stack<object>([root]);
        while (pending.TryPop(out var node))
        {
            var type = node.GetType();
            yield return type;
            if (type.IsPrimitive || node is string or Type or Pointer or MemberInfo or Delegate { Target: null }) continue;
            if (node is Array array && type.GetElementType()!.IsPrimitive) continue;
            if (node is Array items)
            {
                foreach (var item in items)
                    if (item is not null && seen.Add(item)) pending.Push(item);
                continue;
            }

            for (var at = type; at is not null; at = at.BaseType)
                foreach (var field in at.GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly))
                    if (!field.FieldType.IsPointer && !field.FieldType.IsPrimitive && !field.FieldType.IsByRefLike
                        && field.GetValue(node) is { } value && seen.Add(value))
                        pending.Push(value);
        }
    }

    /// <summary>
    /// The operation is released before exposure on the ground that the tree and its completed facts, all exposure reads,
    /// do not need it: they stand alone. A back-reference to the producer would make that release silently keep the query
    /// graph alive, and would break the B3-2★ rule that completed facts retain no producer engine.
    /// </summary>
    [Theory]
    [InlineData("Base = 10\nScale(x) = x * Base\nScale(4) + Scale(5)\n")]
    [InlineData("open Lib\nLib = {\npublic X = 1\n2\n}\nF(y) = {\nInner = y + X\nInner\n}\nF(1)\n")]
    public void TheFinishedProgram_ReachesNoProducerOfItsFacts(string source)
        => AssertProducerFreeFacts(SourceProvenance.ParseValid(source));

    private static void AssertProducerFreeFacts(object root)
    {
        var types = ReachableTypes(root).ToHashSet();

        Assert.Contains(types, type => type == typeof(CompletedStaticStructures));
        Assert.DoesNotContain(types, type => type == typeof(StaticStructureOperation)
            || type == typeof(StaticStructureQueries) || type == typeof(StaticKeyTable)
            || type.IsGenericType && type.GetGenericTypeDefinition() == typeof(StaticQueryEngine<,>));
    }

    // ── The shared default prelude stays program-free ────────────────────────

    private static void AssertPreludeCarriesNoPublication()
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance) { BuiltinRegistry.SharedSemanticPreludeAlgorithm };
        var pending = new Stack<object>(seen);
        while (pending.TryPop(out var node))
        {
            if (node is Algorithm algorithm) Assert.Null(algorithm.CompletedStructure);
            for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++)
                if (seen.Add(child)) pending.Push(child);
        }
    }

    /// <summary>
    /// The default prelude is read by every host-free parse, so no compilation may leave anything on it: every program of
    /// the executable specification runs, including the ones that reach into <c>Math</c> and its aliases, and each algorithm
    /// variant at every depth is checked.
    /// </summary>
    [Fact]
    public void SharedPrelude_CarriesNoProgramPublication_AndIsOneObject()
    {
        var prelude = BuiltinRegistry.SharedSemanticPreludeAlgorithm;

        var first = SourceProvenance.ParseValid("Base = 10\nScale(x) = x * Base\nScale(sum(1, 2))\n");
        var second = SourceProvenance.ParseValid("sum = 1\nsum\n");
        var math = SourceProvenance.ParseValid("open Math\nF(x) = Abs(x) + Math.Floor(x) + sqrt(x)\nF(4)\n");
        foreach (var specCase in LanguageSpecCorpus.AllCases()) Parser.Parse(specCase.Source);

        Assert.Same(prelude, first.Root.CompletedStructure!.Facts.Prelude);
        Assert.Same(prelude, second.Root.CompletedStructure!.Facts.Prelude);
        Assert.Same(prelude, math.Root.CompletedStructure!.Facts.Prelude);
        AssertPreludeCarriesNoPublication();
        Assert.NotSame(first.Root, second.Root);
    }

    [Fact]
    public void SharedPrelude_ParsesConcurrentlyWithIndependentAnswers()
    {
        var failures = new ConcurrentBag<string>();

        Parallel.For(0, 64, i =>
        {
            var result = Parser.Parse($"sum = {i}\nF(x) = x + sum\nF(1) + count([1, 2])\n");
            var property = Assert.IsType<Algorithm.User>(result.Root).Properties[0];
            if (result.HasErrors || property.Name != "sum") failures.Add($"{i}: {result.Diagnostics.Count}");
        });

        Assert.Empty(failures);
    }

    // ── Empty summary seeds ──────────────────────────────────────────────────

    [Fact]
    public void AnEmptySeedsContentKey_IsTheKeyOfFourEmptySets_WithoutMaterializingThem()
    {
        var empty = new PropertyDependencyGraphBuilder.SummarySeed();

        Assert.Equal(PendingReference.KeyParts(["", "", "", ""]), empty.ContentKey);
        Assert.NotEqual(empty.ContentKey, new PropertyDependencyGraphBuilder.SummarySeed(["a"]).ContentKey);
        Assert.NotEqual(
            new PropertyDependencyGraphBuilder.SummarySeed(["a"]).ContentKey,
            new PropertyDependencyGraphBuilder.SummarySeed(visiblePropertyDependencyNames: ["a"]).ContentKey);
    }

    [Theory]
    [InlineData(new string[0], "")]
    [InlineData(new[] { "b" }, "1:b")]
    [InlineData(new[] { "b", "a", "B", "ab" }, "1:B1:a2:ab1:b")]
    public void NameSetKeys_AreOrdinalAndOrderIndependent(string[] names, string expected)
    {
        Assert.Equal(expected, FrontEndRegionKeys.NameSet(names));
        Assert.Equal(expected, FrontEndRegionKeys.NameSet(names.Reverse()));
    }

    /// <summary>
    /// The neighbors of an empty seed: a reader of a parameter-free sibling stays exported, while a capturing sibling still
    /// makes its readers local-only, through a chain that passes through an empty member.
    /// </summary>
    [Fact]
    public void ExposureDistinguishesEmptySeedsFromCapturingOnes()
    {
        var root = SourceProvenance.ParseValid("""
            F(p) = {
                Free = 1
                Reader = Free + 1
                Capturing = p + 1
                Through = Capturing + Free
                Through
            }
            F(1)
            """).Root;

        var body = Assert.IsType<Algorithm.User>(Assert.Single(Assert.IsType<Algorithm.User>(root).Properties).Value);
        PropertyExposure Exposure(string name) => body.Properties.Single(property => property.Name == name).Exposure;

        Assert.Equal(PropertyExposure.Exported, Exposure("Free"));
        Assert.Equal(PropertyExposure.Exported, Exposure("Reader"));
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Exposure("Capturing"));
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Exposure("Through"));
    }

    // ── Forking the key table ────────────────────────────────────────────────

    [Fact]
    public void AForkKeepsInternedIdentities_AndIsIsolatedInBothDirections()
    {
        var table = new StaticKeyTable();
        var before = new object();
        var parentLater = new object();
        var forkLater = new object();
        var key = table.Inside(table.Root, before);

        var fork = table.Fork();
        var sibling = table.Fork();

        Assert.Same(key, fork.Inside(fork.Root, before));
        Assert.Same(key, sibling.Inside(sibling.Root, before));
        Assert.Same(key, table.Inside(table.Root, before));
        Assert.Equal(table.Count, fork.Count);

        var inFork = fork.Inside(fork.Root, forkLater);
        var inParent = table.Inside(table.Root, parentLater);

        Assert.NotSame(inFork, table.Inside(table.Root, forkLater));
        Assert.NotSame(inFork, sibling.Inside(sibling.Root, forkLater));
        Assert.NotSame(inParent, fork.Inside(fork.Root, parentLater));
    }

    [Fact]
    public void AnUnwrittenFork_CanBeForkedConcurrently()
    {
        var table = new StaticKeyTable();
        var declarations = Enumerable.Range(0, 64).Select(_ => new object()).ToArray();
        var keys = declarations.Select(declaration => table.Inside(table.Root, declaration)).ToArray();
        var frozen = table.Fork();

        Parallel.For(0, 64, i =>
        {
            var fork = frozen.Fork();
            Assert.Same(keys[i], fork.Inside(fork.Root, declarations[i]));
        });
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void ForkStopsDuringTransferAndKeepsTheSourceRetryable(bool cancelOperation)
    {
        using var cancelled = new CancellationTokenSource();
        var comparer = new TransferComparer();
        var map = new StaticKeyTable.ForkableMap<string, object>(comparer);
        var value = new object();
        map.Add("first", value);
        map.Add("second", new object());
        map.Add("third", new object());
        var hashed = 0;
        comparer.OnHash = () => { hashed++; cancelled.Cancel(); };

        var error = Assert.Throws<OperationCanceledException>(() => map.Fork(
            cancelOperation ? cancelled.Token : CancellationToken.None,
            cancelOperation ? CancellationToken.None : cancelled.Token));

        Assert.Equal(cancelled.Token, error.CancellationToken);
        Assert.Equal(1, hashed);
        comparer.OnHash = null;
        var retry = map.Fork(CancellationToken.None, CancellationToken.None);
        Assert.Equal(3, retry.Count);
        Assert.True(retry.TryGetValue("first", out var retained));
        Assert.Same(value, retained);
    }

    private sealed class TransferComparer : IEqualityComparer<string>
    {
        internal Action? OnHash { get; set; }
        public bool Equals(string? left, string? right) => StringComparer.Ordinal.Equals(left, right);
        public int GetHashCode(string key)
        {
            OnHash?.Invoke();
            return StringComparer.Ordinal.GetHashCode(key);
        }
    }

    // ── The query table's key comparer ───────────────────────────────────────

    private sealed class Echo : IStaticQueryDefinition<string, int>
    {
        public int Computed;

        public StaticQueryStep<int> Compute(string key, StaticQueryReader<string, int> reader)
        {
            Computed++;
            return StaticQueryStep.Complete(key.Length);
        }

        public int Initial(string key) => 0;
        public int PathCycleValue => -1;
        public bool ValueEquals(int left, int right) => left == right;
        public bool IsRefinement(int before, int after) => true;
    }

    /// <summary>Self-indexed entries answer through the supplied key comparer, for reads, final reads and enumeration alike.</summary>
    [Fact]
    public void TheEntryTable_HonorsTheKeyComparer_AndKeepsDiscoveryOrder()
    {
        var definition = new Echo();
        var engine = new StaticQueryEngine<string, int>(definition, StringComparer.OrdinalIgnoreCase);

        Assert.Equal(3, engine.Get("abc"));
        Assert.Equal(3, engine.Get("ABC"));
        Assert.Equal(2, engine.Get("zz"));

        Assert.Equal(2, definition.Computed);
        Assert.True(engine.TryGetFinal("Abc", out var read));
        Assert.Equal(3, read);
        Assert.False(engine.TryGetFinal("missing", out _));
        Assert.Equal(["abc", "zz"], engine.EnumerateFinalValues().Select(entry => entry.Key));
        Assert.Equal(2, engine.Statistics.Entries);
    }
}
