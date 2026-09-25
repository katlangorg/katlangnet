using KatLang.Optimizations.Loops;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// FE-2: implicit lifting rewrites each of K lifted references to a callable with L implicit
/// parameters into a call that forwards L synthesized arguments. The arguments are a pure function
/// of the callee's parameter patterns and the caller's rewrite context, so every lifted reference
/// to one callee in one resolver rewrite region shares ONE immutable argument bundle; each
/// reference keeps its own call node (and callee name), which carries its source span and its
/// origin entry. The elaborated representation is therefore O(K + L), not K × L, and every later
/// pass — exposure (rewrite and summary channel), collision and open-provider validation, the
/// structural preflight, pre-evaluation validation, the load guard, and the editor semantic
/// model — processes the shared bundle once per context instead of once per call edge.
///
/// <para>These pins count the representation (a reference-identity census of the elaborated
/// graph) and the work (the per-pass observation counters) exactly, at several sizes, and pin
/// that sharing is SYNTAX only: provenance stays per reference, every call binds and evaluates
/// independently (randomness, host operations, async suspension, the property cache, planned
/// loops), and a bundle is never reused across callees, caller contexts, or parses.</para>
/// </summary>
public class ImplicitArgumentSharingTests
{
    private static string Names(string prefix, int count)
        => string.Join(", ", Enumerable.Range(0, count).Select(i => $"{prefix}{i}"));

    /// <summary><c>G = v0, …, v(L-1)</c> and <c>H = abs(G), …</c> (K lifted references); root <c>1</c>.</summary>
    private static string Canonical(int references, int parameters)
        => $"G = {Names("v", parameters)}\nH = {string.Join(", ", Enumerable.Repeat("abs(G)", references))}\n1";

    // ── Reference-identity census of an elaborated graph ─────────────────────

    private sealed class Census
    {
        private readonly HashSet<object> _seen = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<object, long> _treeSlots = new(ReferenceEqualityComparer.Instance);

        public List<Expr.Call> Calls { get; } = [];
        public long DistinctExpressions { get; private set; }
        public long DistinctCallArgumentSlots { get; private set; }
        public long TreeExpandedCallArgumentSlots { get; private set; }

        private readonly HashSet<OutputBundle> _argumentBundles = new(ReferenceEqualityComparer.Instance);

        public static Census Of(Algorithm root)
        {
            var census = new Census();
            census.TreeExpandedCallArgumentSlots = census.Walk(root);
            return census;
        }

        public IReadOnlyList<Expr.Call> CallsTo(string name)
            => Calls.Where(call => call.Function is Expr.Resolve(var callee) && callee == name).ToList();

        private long Walk(object node)
        {
            if (_treeSlots.TryGetValue(node, out var known))
                return known;

            if (_seen.Add(node) && node is Expr expr)
            {
                DistinctExpressions++;
                if (expr is Expr.Call call)
                    Calls.Add(call);
            }

            long slots = 0;
            switch (node)
            {
                case Algorithm.User user:
                    foreach (var open in user.Opens) slots += Walk(open);
                    foreach (var property in user.Properties) slots += Walk(property.Value);
                    foreach (var row in user.Output) slots += Walk(row);
                    break;
                case Algorithm.Conditional conditional:
                    foreach (var open in conditional.Opens) slots += Walk(open);
                    foreach (var branch in conditional.Branches) slots += Walk(branch.Body);
                    break;
                case Expr.Call(var function, var args):
                    if (_argumentBundles.Add(args))
                        DistinctCallArgumentSlots += args.Count;
                    slots += args.Count + Walk(function);
                    foreach (var arg in args) slots += Walk(arg);
                    break;
                case Expr.DotCall dotCall:
                    slots += Walk(dotCall.Target);
                    if (dotCall.Args is { } dotArgs)
                    {
                        if (_argumentBundles.Add(dotArgs))
                            DistinctCallArgumentSlots += dotArgs.Count;
                        slots += dotArgs.Count;
                        foreach (var arg in dotArgs) slots += Walk(arg);
                    }
                    break;
                case Expr.Binary(_, var left, var right): slots += Walk(left) + Walk(right); break;
                case Expr.Unary(_, var operand): slots += Walk(operand); break;
                case Expr.Comparison(var first, var links):
                    slots += Walk(first);
                    foreach (var link in links) slots += Walk(link.Operand);
                    break;
                case Expr.Index(var target, var selector): slots += Walk(target) + Walk(selector); break;
                case Expr.SequenceSpread(var operand): slots += Walk(operand); break;
                case Expr.SequenceConstruct(var left, var right): slots += Walk(left) + Walk(right); break;
                case Expr.ListLiteral(var items): foreach (var item in items) slots += Walk(item); break;
                case Expr.Capture(var body): foreach (var row in body) slots += Walk(row); break;
                case Expr.AlgorithmExpr(var nested): slots += Walk(nested); break;
                case Expr.Grace(var inner, _): slots += Walk(inner); break;
            }

            _treeSlots[node] = slots;
            return slots;
        }
    }

    private static OutputBundle SharedArguments(Census census, string callee)
    {
        var calls = census.CallsTo(callee);
        Assert.NotEmpty(calls);
        var bundle = calls[0].Args;
        Assert.All(calls, call => Assert.Same(bundle, call.Args));
        return bundle;
    }

    // ── Representation ───────────────────────────────────────────────────────

    /// <summary>
    /// The canonical workload: K = L = n. The K synthesized calls are distinct nodes sharing ONE
    /// bundle of L slots, so the distinct call-argument slots are K (the written <c>abs</c> calls)
    /// plus L, and the whole elaborated graph has 4K + 2L + 1 distinct expressions. The
    /// tree-expanded view — what the former representation materialized — is still n² + n.
    /// </summary>
    [Theory]
    [InlineData(8)]
    [InlineData(16)]
    [InlineData(32)]
    [InlineData(64)]
    public void CanonicalLifting_ElaboratesToOneSharedArgumentBundle(int n)
    {
        var census = Census.Of(SourceProvenance.ParseValid(Canonical(n, n)).Root);

        var calls = census.CallsTo("G");
        Assert.Equal(n, calls.Count);
        Assert.Equal(n, calls.Distinct(ReferenceEqualityComparer.Instance).Count());
        var shared = SharedArguments(census, "G");
        Assert.Equal(
            Enumerable.Range(0, n).Select(i => $"v{i}"),
            shared.Select(slot => Assert.IsType<Expr.Param>(slot).Name));
        Assert.Equal(2 * n, census.DistinctCallArgumentSlots);
        Assert.Equal(6 * n + 1, census.DistinctExpressions);
        Assert.Equal(n * n + n, census.TreeExpandedCallArgumentSlots);
    }

    /// <summary>
    /// The slots keep the callee's parameter order exactly — first occurrence adjusted by Grace,
    /// never a sorted or set order — however many references share them.
    /// </summary>
    [Fact]
    public void SharedBundle_ForwardsInTheCalleesParameterOrder()
    {
        var root = SourceProvenance.ParseValid("G = zeta - alpha * ~mid\nH = G, G, G\nH(10, 2, 3)").Root;
        var g = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, p => p.Name == "G").Value);
        var names = SharedArguments(Census.Of(root), "G").Select(slot => Assert.IsType<Expr.Param>(slot).Name).ToArray();
        Assert.Equal(g.Params, names);
        Assert.NotEqual(names.Order(StringComparer.Ordinal), names);
    }

    /// <summary>The empty and single cases add no sharing machinery and keep their results.</summary>
    [Theory]
    [InlineData("G = 5\nH = G + G\nH", 0, "10")]
    [InlineData("G = a\nH = 1\nH", 0, "1")]
    [InlineData("G = x * 2\nH = G\nH(4)", 1, "8")]
    [InlineData("G = x * 2\nH = G + G\nH(4)", 2, "16")]
    public void EmptyAndSingleCases_AreOrdinary(string source, int lifted, string display)
    {
        var parsed = SourceProvenance.ParseValid(source);
        var census = Census.Of(parsed.Root);
        Assert.Equal(lifted, census.CallsTo("G").Count);
        if (lifted > 0)
            Assert.Single(SharedArguments(census, "G"));
        Assert.Equal(display, KatLangEngine.Run(source).ToDisplayString());
    }

    // ── Work: every later pass pays the shared bundle once ───────────────────

    private sealed record PassObservations(
        FrontEndTraversalObservations Resolve,
        FrontEndTraversalObservations Collision,
        FrontEndTraversalObservations OpenProviders,
        FrontEndTraversalObservations Exposure,
        FrontEndTraversalObservations Preflight,
        FrontEndTraversalObservations Validation,
        FrontEndTraversalObservations LoadGuard,
        FrontEndTraversalObservations Semantic);

    /// <summary>The pipeline's passes in order, each observed on its own.</summary>
    private static PassObservations ObservePasses(string source)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var origins = new ImplicitArgumentResolver.ResolutionOrigins();
        var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(syntax, graceOrigins: origins.Grace);
        Assert.Empty(detectorDiagnostics);
        var observed = new PassObservations(new(), new(), new(), new(), new(), new(), new(), new());
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observed.Resolve, diagnostics, origins);
        if (origins.HasLiftedParameters)
            Assert.False(ParameterDetector.CompleteOwnership(resolved, origins).Changed);
        new ParameterPropertyCollisionValidator(diagnostics, programRoot: resolved) { TraversalObservations = observed.Collision }
            .VisitAlgorithm(resolved);
        OpenProviderValidator.Validate(resolved, diagnostics, (HostOperations?)null, observed.OpenProviders);
        var exposed = PropertyExposureResolver.Resolve(resolved, observed.Exposure);
        Assert.Empty(diagnostics);
        var program = new Expr.AlgorithmExpr(exposed);
        Assert.Null(AstStructuralPreflight.Check(
            program, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines, observed.Preflight));
        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(program, observed.Validation));
        Assert.Empty(LoadElaborationGuard.CreateUnavailableDiagnostics(exposed, observed.LoadGuard));
        SemanticModelBuilder.Build(exposed, observed.Semantic);
        return observed;
    }

    /// <summary>
    /// K lifted references to a callable of L parameters: the resolver builds ONE bundle of L slots
    /// and K call edges; every walker dispatches K + L call-argument slots (the K written
    /// <c>abs</c> slots and the shared L once); exposure rewrites and summarizes K + 1 bundles; the
    /// structural preflight enumerates 6K + 4L + 4 edges. Each count was K × L-shaped before.
    /// </summary>
    [Theory]
    [InlineData(16, 24)]
    [InlineData(32, 48)]
    [InlineData(48, 16)]
    public void LaterPasses_ProcessTheSharedBundleOncePerContext(int references, int parameters)
    {
        var observed = ObservePasses(Canonical(references, parameters));

        Assert.Equal(references, observed.Resolve.ImplicitCallsSynthesized);
        Assert.Equal(1, observed.Resolve.ImplicitArgumentBundlesBuilt);
        Assert.Equal(parameters, observed.Resolve.ImplicitArgumentSlotsBuilt);

        var slots = references + parameters;
        Assert.Equal(slots, observed.Collision.WalkerCallArgumentSlots);
        Assert.Equal(slots, observed.OpenProviders.WalkerCallArgumentSlots);
        Assert.Equal(slots, observed.Validation.WalkerCallArgumentSlots);
        Assert.Equal(slots, observed.LoadGuard.WalkerCallArgumentSlots);
        Assert.Equal(slots, observed.Semantic.SemanticModelCallArgumentSlots);
        Assert.Equal(slots, observed.Semantic.WalkerCallArgumentSlots);

        Assert.Equal(references + 1, observed.Exposure.ExposureArgumentBundleRewrites);
        Assert.Equal(references + 1, observed.Exposure.DependencyArgumentBundleSummaries);
        Assert.Equal(6L * references + 4L * parameters + 4, observed.Preflight.StructuralPreflightEdges);
    }

    /// <summary>
    /// The open-provider validator walks a body only when it contains an <c>open</c>: with the
    /// lifted references inside such a body, both its open-presence scan and the validation walk
    /// dispatch the K written <c>abs</c> slots and the shared L once each.
    /// </summary>
    [Theory]
    [InlineData(16, 24)]
    [InlineData(32, 48)]
    public void OpenProviderValidation_OverLiftedReferences_WalksTheSharedBundleOnce(int references, int parameters)
    {
        var source = $"Lib = {{\n    public X = 1\n}}\nG = {Names("v", parameters)}\nH = {{\n    open Lib\n    "
            + string.Join(", ", Enumerable.Repeat("abs(G)", references)) + "\n}\n1";
        var observed = ObservePasses(source);
        Assert.Equal(2 * (references + parameters), observed.OpenProviders.WalkerCallArgumentSlots);
    }

    /// <summary>
    /// The dot-member provenance finalizer walks the whole classified tree when a promotion came
    /// from a missing member (<c>Lib.Missing</c>): it too dispatches the shared bundle once.
    /// </summary>
    [Theory]
    [InlineData(16, 24)]
    [InlineData(32, 48)]
    public void ProvenanceFinalizer_OverLiftedReferences_WalksTheSharedBundleOnce(int references, int parameters)
    {
        var source = $"Lib = {{\n    public X = 1\n}}\nG = {Names("v", parameters)}\nH = "
            + string.Join(", ", Enumerable.Repeat("abs(G)", references)) + ", Lib.Missing\n1";
        var observed = ObservePasses(source);
        Assert.Equal(references + parameters, observed.Exposure.WalkerCallArgumentSlots);
    }

    /// <summary>
    /// A design-independent guard over the whole public path (parse, editor model, run): doubling
    /// K = L roughly doubles the allocation. The former K × L representation quadrupled it.
    /// </summary>
    [Fact]
    public void PublicPipelineAllocation_GrowsLinearlyInReferencesAndParameters()
    {
        static long Allocation(string source)
        {
            void Pass()
            {
                var parsed = Parser.Parse(source);
                Assert.False(parsed.HasErrors);
                SemanticModelBuilder.Build(parsed);
                Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
            }

            Pass();
            var before = GC.GetAllocatedBytesForCurrentThread();
            Pass();
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        var small = Allocation(Canonical(256, 256));
        var large = Allocation(Canonical(512, 512));
        var ratio = (double)large / small;
        Assert.True(ratio < 2.6, $"Doubling K = L grew the allocation {ratio:F2}x ({small} -> {large} bytes).");
    }

    // ── Exactness of the sharing scope ───────────────────────────────────────

    /// <summary>Two callees with the same parameter names keep their own bundles.</summary>
    [Fact]
    public void DifferentCallees_WithTheSameParameterNames_KeepTheirOwnBundles()
    {
        const string source = "G1 = x + 1\nG2 = x * 10\nH = G1 + G2 + G1 + G2\nH(2)";
        var census = Census.Of(SourceProvenance.ParseValid(source).Root);
        Assert.NotSame(SharedArguments(census, "G1"), SharedArguments(census, "G2"));
        Assert.Equal("46", KatLangEngine.Run(source).ToDisplayString());
    }

    /// <summary>
    /// A bundle belongs to ONE resolver rewrite region: the same callee referenced twice from each
    /// of two properties is two bundles — one per owner — each shared by its region's two calls.
    /// Pinned on the resolver's own output (exposure rewrites every bundle per region anyway, so
    /// the final tree alone could not show a bundle leaking across owners).
    /// </summary>
    [Fact]
    public void SameCallee_InTwoRegions_KeepsOneBundlePerRegion()
    {
        const string source = "G = a + b\nA = G + G\nB = G * G\nA(1, 2) + B(1, 2)";
        var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(detectorDiagnostics);
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();

        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations, diagnostics);

        Assert.Empty(diagnostics);
        Assert.Equal(4, observations.ImplicitCallsSynthesized);
        Assert.Equal(2, observations.ImplicitArgumentBundlesBuilt);
        static OutputBundle BundleIn(Algorithm root, string property)
            => SharedArguments(Census.Of(Assert.Single(root.Properties, p => p.Name == property).Value), "G");
        Assert.NotSame(BundleIn(resolved, "A"), BundleIn(resolved, "B"));
        var parsed = SourceProvenance.ParseValid(source).Root;
        Assert.NotSame(BundleIn(parsed, "A"), BundleIn(parsed, "B"));
        Assert.Equal("15", KatLangEngine.Run(source).ToDisplayString());
    }

    /// <summary>
    /// The caller context is part of the bundle: a closed collecting caller forwards its own
    /// collected list (<c>ys*</c>) where an open caller lifts the callee's (<c>xs*</c>). Reusing one
    /// bundle across the two regions would leave <c>B</c> reading a name it does not bind.
    /// </summary>
    [Fact]
    public void Forwarding_ThatDiffersByCallerContext_IsNeverShared()
    {
        const string source = "G(*xs) = xs.count\nA(*ys) = G + G\nB = G + G\nA(1, 2) + B(1, 2, 3)";
        var root = SourceProvenance.ParseValid(source).Root;
        Expr ForwardedIn(string property)
            => Assert.Single(SharedArguments(Census.Of(Assert.Single(root.Properties, p => p.Name == property).Value), "G"));
        Assert.Equal(new Expr.SequenceSpread(new Expr.Param("ys")), ForwardedIn("A"));
        Assert.Equal(new Expr.SequenceSpread(new Expr.Param("xs")), ForwardedIn("B"));
        Assert.Equal("10", KatLangEngine.Run(source).ToDisplayString());
    }

    /// <summary>The same spelling in two owners is two declarations, and two bundles.</summary>
    [Fact]
    public void SameSpelling_DifferentDeclarations_AreNeverShared()
    {
        const string source = "G = x + 1\nH = G + G\nK = {\n    G = y * 10\n    M = G + G\n    M(3)\n}\nH(1) + K";
        var root = SourceProvenance.ParseValid(source).Root;
        var outer = SharedArguments(Census.Of(Assert.Single(root.Properties, p => p.Name == "H").Value), "G");
        var inner = SharedArguments(Census.Of(Assert.Single(root.Properties, p => p.Name == "K").Value), "G");
        Assert.NotSame(outer, inner);
        Assert.Equal(new Expr.Param("x"), Assert.Single(outer));
        Assert.Equal(new Expr.Param("y"), Assert.Single(inner));
        Assert.Equal("64", KatLangEngine.Run(source).ToDisplayString());
    }

    /// <summary>Grouped and collecting callee shapes share their whole bundle, nested capture included.</summary>
    [Theory]
    [InlineData("G((a, b), c) = a * b + c\nH = G + G + G\nH((2, 3), 4)", "30")]
    [InlineData("G(x, *rest) = x + rest.count\nH = G * G\nH(10, 1, 1)", "144")]
    public void GroupedAndCollectingShapes_ShareTheirBundle(string source, string display)
    {
        var census = Census.Of(SourceProvenance.ParseValid(source).Root);
        var shared = SharedArguments(census, "G");
        Assert.Equal(2, shared.Count);
        Assert.Equal(display, KatLangEngine.Run(source).ToDisplayString());
    }

    /// <summary>The Math alias and the bare canonical <c>Math.X</c> arms share within their callee too.</summary>
    [Fact]
    public void MathArms_ShareWithinTheirCallee()
    {
        const string source = "H = pow + pow + Math.Pow + Math.Pow\nH(2, 3)";
        var root = SourceProvenance.ParseValid(source).Root;
        var census = Census.Of(root);
        var alias = SharedArguments(census, "pow");
        var dotCalls = new List<Expr.DotCall>();
        void Collect(Expr expr)
        {
            switch (expr)
            {
                case Expr.DotCall { Name: "Pow", Args: not null } dot: dotCalls.Add(dot); break;
                case Expr.Binary(_, var left, var right): Collect(left); Collect(right); break;
            }
        }

        foreach (var row in Assert.Single(root.Properties, p => p.Name == "H").Value.Output)
            Collect(row);
        Assert.Equal(2, alias.Count);
        Assert.Equal(2, dotCalls.Count);
        Assert.Same(dotCalls[0].Args, dotCalls[1].Args);
        Assert.Equal("32", KatLangEngine.Run(source).ToDisplayString());
    }

    /// <summary>Two parses never share a bundle: the memo is run-local, never static.</summary>
    [Fact]
    public void Parses_NeverShareBundles_AndTheSharedBundleHasNoMutationRoute()
    {
        var first = SharedArguments(Census.Of(SourceProvenance.ParseValid(Canonical(4, 4)).Root), "G");
        var second = SharedArguments(Census.Of(SourceProvenance.ParseValid(Canonical(4, 4)).Root), "G");
        Assert.NotSame(first, second);
        // The shared bundle is an immutable snapshot: no collection interface that could mutate it.
        Assert.DoesNotContain(typeof(ICollection<Expr>), typeof(OutputBundle).GetInterfaces());
        Assert.DoesNotContain(typeof(System.Collections.IList), typeof(OutputBundle).GetInterfaces());
        Assert.All(first, slot => Assert.Null(slot.Span));
    }

    // ── Provenance stays per written reference ───────────────────────────────

    /// <summary>
    /// Every lifted reference keeps its own call node and callee name, both at the span of the
    /// reference the program wrote; the shared arguments carry no span (never a fabricated one).
    /// </summary>
    [Fact]
    public void EachLiftedReference_KeepsItsOwnSpannedCallNode()
    {
        var calls = Census.Of(SourceProvenance.ParseValid("G = a + b\nH = G + G + G\nH(1, 2)").Root).CallsTo("G");
        Assert.Equal(3, calls.Count);
        Assert.Equal(
            [new SourceSpan(2, 5, 2, 6), new SourceSpan(2, 9, 2, 10), new SourceSpan(2, 13, 2, 14)],
            calls.Select(call => call.Span!.Value).OrderBy(span => span.Start).ToArray());
        Assert.All(calls, call => Assert.Equal(call.Span, call.Function.Span));
        Assert.All(calls[0].Args, slot => Assert.Null(slot.Span));
    }

    /// <summary>
    /// A budget exhausted inside the n-th lifted call is blamed at the n-th written reference —
    /// sharing the arguments never makes every failure point at the first call site.
    /// </summary>
    [Theory]
    [InlineData("H = pow + pow + pow\nH(2, 3)", 2, 1, 11)]
    [InlineData("H = pow + pow + pow\nH(2, 3)", 3, 1, 17)]
    [InlineData("G = a * b\nH = G + G + G\nH(2, 3)", 2, 2, 9)]
    [InlineData("G = a * b\nH = G + G + G\nH(2, 3)", 3, 2, 13)]
    public void StepLimitFailure_IsBlamedAtTheExactReference(string source, long steps, int line, int column)
    {
        var run = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = steps } });
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(run).Errors);
        Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, error.Code);
        Assert.Equal(new SourcePosition(line, column), error.Span!.Value.Start);
    }

    /// <summary>The editor model reports each written reference, and no synthesized one.</summary>
    [Fact]
    public void SemanticModel_ReportsEveryWrittenReference_AndNoSynthesizedSite()
    {
        const string source = "G = a + b\nH = G + G + G\nH(1, 2)";
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        var declaration = Assert.Single(model.FindDeclarations("G"));
        foreach (var column in new[] { 5, 9, 13 })
        {
            var resolution = model.FindResolutionAt(new SourcePosition(2, column));
            Assert.NotNull(resolution);
            Assert.Equal("G", resolution.Occurrence.Name);
            Assert.Equal(declaration, resolution.ResolvedDeclaration);
        }

        Assert.Equal(3, model.IdentifierOccurrences.Count(o => o.Name == "G" && o.Kind == OccurrenceKind.ResolveReference));
        Assert.DoesNotContain(model.IdentifierOccurrences, o => o.Name is "a" or "b" && o.Span.Start.Line == 2);
    }

    // ── Sharing is syntax: every call binds and evaluates on its own ─────────

    /// <summary>
    /// Seeded draws: each lifted call draws afresh exactly like the written forwarding call, a cached
    /// zero-parameter read is drawn once, and an explicit <c>R()</c> draws per call.
    /// </summary>
    [Theory]
    [InlineData("G = random(0, 100) + a\nH = G, G, G\nH(1)", "G = random(0, 100) + a\nH(a) = G(a), G(a), G(a)\nH(1)", 3)]
    [InlineData("R = random(0, 100)\nG = R + a\nH = G, G, G\nH(1)", "R = random(0, 100)\nG = R + a\nH(a) = G(a), G(a), G(a)\nH(1)", 1)]
    [InlineData("R = random(0, 100)\nG = R() + a\nH = G, G\nH(1)", "R = random(0, 100)\nG = R() + a\nH(a) = G(a), G(a)\nH(1)", 2)]
    public void SeededDraws_MatchTheWrittenForwardingCalls(string lifted, string written, int distinctValues)
    {
        var options = new RunOptions { RandomSeed = 20260926 };
        var liftedResult = Assert.IsType<RunResult.Success>(KatLangEngine.Run(lifted, options));
        var writtenResult = Assert.IsType<RunResult.Success>(KatLangEngine.Run(written, options));
        Assert.Equal(writtenResult.ToDisplayString(), liftedResult.ToDisplayString());
        Assert.Equal(distinctValues, Assert.IsType<Result.SequenceValue>(liftedResult.Value).Items.Distinct().Count());
    }

    /// <summary>A host operation reached through K lifted calls runs K times, in order, like the written form.</summary>
    [Fact]
    public void HostOperation_RunsOncePerLiftedCall_InOrder()
    {
        List<string> Log(string source)
        {
            var log = new List<string>();
            var options = new RunOptions
            {
                HostOperations = HostOperations.Create(HostOperation.Create("Tick", (args, _) =>
                {
                    log.Add(((Result.Atom)args[0]).Value.ToString());
                    return new Result.Atom(((Result.Atom)args[0]).Value + log.Count);
                }, "v")),
            };
            Assert.Equal("(1, 2, 3)", KatLangEngine.Run(source, options).ToDisplayString());
            return log;
        }

        var lifted = Log("G = Tick(a) + b\nH = G, G, G\nH(0, 0)");
        var written = Log("G = Tick(a) + b\nH(a, b) = G(a, b), G(a, b), G(a, b)\nH(0, 0)");
        Assert.Equal(["0", "0", "0"], lifted);
        Assert.Equal(written, lifted);
    }

    /// <summary>
    /// Genuine suspension: each of the K lifted calls reaches the asynchronous operation and waits
    /// for its own release, observes the supplied cancellation token, and the results arrive in
    /// release order.
    /// </summary>
    [Fact]
    public async Task AsyncHostOperation_SuspendsOncePerLiftedCall_WithTheSuppliedToken()
    {
        const int calls = 3;
        var gates = Enumerable.Range(0, calls).Select(_ => new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
        var reached = Enumerable.Range(0, calls).Select(_ => new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
        var invocations = 0;
        using var cancellation = new CancellationTokenSource();
        var tokens = new List<CancellationToken>();
        var options = new RunOptions
        {
            EvaluationCancellationToken = cancellation.Token,
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("Wait", async (args, token) =>
            {
                var index = Interlocked.Increment(ref invocations) - 1;
                lock (tokens) tokens.Add(token);
                reached[index].TrySetResult();
                return await gates[index].Task;
            }, "v")),
        };

        var run = KatLangEngine.RunAsync("G = Wait(a) + b\nH = G, G, G\nH(1, 2)", options);
        for (var i = 0; i < calls; i++)
        {
            var completed = await Task.WhenAny(reached[i].Task, Task.Delay(TimeSpan.FromSeconds(30)));
            Assert.Same(reached[i].Task, completed);
            Assert.False(run.IsCompleted);
            Assert.Equal(i + 1, Volatile.Read(ref invocations));
            gates[i].SetResult(new Result.Atom((i + 1) * 100));
        }

        Assert.Equal("(102, 202, 302)", (await run).ToDisplayString());
        Assert.Equal(calls, invocations);
        Assert.All(tokens, token => Assert.Equal(cancellation.Token, token));
    }

    /// <summary>
    /// The shared slots read the CURRENT activation's bindings: two activations of the caller, and
    /// two callers with the same shape, each forward their own arguments.
    /// </summary>
    [Theory]
    [InlineData("G = a * 10\nH = G, G\nH(1), H(2)", "(10, 10)\n(20, 20)")]
    [InlineData("G = a * 10\nH = G, G\nK = G + G + 1\nH(3), K(4)", "(30, 30)\n81")]
    public void SeparateActivations_ForwardTheirOwnArguments(string source, string display)
        => Assert.Equal(display, KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));

    /// <summary>A planned loop step made of lifted calls agrees with generic execution, and the plan ran.</summary>
    [Fact]
    public void PlannedLoop_OverLiftedCalls_MatchesGenericExecution()
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("G = x * 2\nStep(x) = G + G + x\nrepeat(Step, 3, 1)").Root);
        var diagnostics = new LoopOptimizationDiagnostics();

        var optimized = Evaluator.RunCountedObserved(program, enableOptimizations: true, loopDiagnostics: diagnostics).Result;
        var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false).Result;

        Assert.False(optimized.IsError);
        Assert.False(generic.IsError);
        Assert.Equal(generic.Value.Value, optimized.Value.Value);
        Assert.Equal([125m], optimized.Value.Value.ToAtoms());
        Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
    }

    // ── Structural preflight: a shared argument bundle is a DAG, not a cycle ─

    private static Expr.Call CallOf(string callee, OutputBundle arguments, SourceSpan? span = null)
        => new(new Expr.Resolve(callee), arguments) { Span = span };

    private static Algorithm.User Adder()
        => new(null, [new CaptureParameterPattern("x"), new CaptureParameterPattern("y")], [], [],
            new OutputBundle([new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Param("y"))]));

    /// <summary>Two calls sharing one argument bundle are accepted and evaluate independently.</summary>
    [Fact]
    public void SharedArgumentBundle_IsAcceptedByThePreflight_AndEvaluates()
    {
        var shared = new OutputBundle([new Expr.Num(2), new Expr.Num(3)]);
        var root = new Algorithm.User(null, [], [], [new Property("F", Adder())],
            new OutputBundle([CallOf("F", shared), CallOf("F", shared)]));
        var observations = new FrontEndTraversalObservations();

        Assert.Null(AstStructuralPreflight.Check(
            new Expr.AlgorithmExpr(root), EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines, observations));
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));

        Assert.False(result.IsError);
        Assert.Equal([5m, 5m], result.Value.ToAtoms());
        // The root expression's algorithm (1); its property value and two rows (3); the value's row
        // and two parameter patterns (3) and the row's operands (2); each call's callee and ONE
        // bundle edge (2 + 2); and the shared bundle's two slots, walked once (2).
        Assert.Equal(15, observations.StructuralPreflightEdges);
    }

    /// <summary>
    /// A shared bundle reached again at a DEEPER position is re-judged without re-walking it, and a
    /// crossing there is reported at the slot the slot-by-slot walk reports — never at the bundle's
    /// enclosing call.
    /// </summary>
    [Fact]
    public void SharedArgumentBundle_ReachedDeeper_IsRejectedAtTheCrossingSlot()
    {
        Expr deep = new Expr.Num(1);
        for (var i = 0; i < 10; i++)
            deep = new Expr.Unary(UnaryOp.Minus, deep);
        var slotSpan = new SourceSpan(7, 1, 7, 2);
        var callSpan = new SourceSpan(9, 1, 9, 2);
        var shared = new OutputBundle([new Expr.Num(0) { Span = new SourceSpan(5, 1, 5, 2) }, deep with { Span = slotSpan }]);
        Expr second = CallOf("F", shared, callSpan);
        for (var i = 0; i < 8; i++)
            second = new Expr.Unary(UnaryOp.Minus, second);
        var root = new Expr.Binary(BinaryOp.Add, CallOf("F", shared), second);

        var rejection = AstStructuralPreflight.Check(root, maxDepth: 20, AstConsumerProfile.FullyRecursive);

        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);
        Assert.Equal(slotSpan, rejection.Span);
    }

    /// <summary>
    /// A cycle closed THROUGH a shared bundle (via a caller-owned property list) is reported at the
    /// slot still on the path, exactly where the slot-by-slot walk reports it.
    /// </summary>
    [Fact]
    public void CycleThroughASharedBundle_IsRejectedAtTheSlotOnThePath()
    {
        var properties = new List<Property>();
        var owner = new Algorithm.User(null, [], [], properties, new OutputBundle([new Expr.Num(0)]));
        var slotSpan = new SourceSpan(3, 1, 3, 4);
        var shared = new OutputBundle([new Expr.Num(7) { Span = new SourceSpan(2, 1, 2, 2) }, new Expr.AlgorithmExpr(owner) { Span = slotSpan }]);
        var inner = CallOf("G", shared, new SourceSpan(4, 1, 4, 2));
        properties.Add(new Property("P", new Algorithm.User(null, [], [], [], new OutputBundle([inner]))));
        var root = CallOf("F", shared, new SourceSpan(1, 1, 1, 2));

        var rejection = AstStructuralPreflight.Check(root, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive);

        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.CycleDetected, rejection.Kind);
        Assert.Equal(slotSpan, rejection.Span);
    }

    // ── Deferred regions share at materialization ────────────────────────────

    /// <summary>
    /// Lifted references inside a deferred module region are elaborated when the branch is
    /// selected; the materialized body shares its bundle like any other region, and the value is
    /// the eager program's.
    /// </summary>
    [Fact]
    public async Task DeferredRegion_SharesItsBundle_WhenMaterialized()
    {
        const string url = "https://katlang.org/fe2/g.kat";
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult("public G = a * 10 + b"),
            AllowedHosts = ["katlang.org"],
        };
        var parsed = await SourceProvenance.ParseValidAsync(
            $"F(0) = {{\n    open '{url}'\n    K = G(a, b)\n    H = K + K + K\n    H(1, 2)\n}}\nF(n) = n\nF(0)",
            options);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties, p => p.Name == "F").Value);
        var region = Assert.IsType<DeferredModuleRegion>(family.Branches[0].Body.DeferredRegion);

        var result = await Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root));

        Assert.False(result.IsError);
        Assert.Equal([36m], result.Value.ToAtoms());
        Assert.True(region.TryGetMaterialized(out var materialized));
        var h = Assert.Single(materialized.Properties, p => p.Name == "H").Value;
        var bundle = SharedArguments(Census.Of(h), "K");
        Assert.Equal(["a", "b"], bundle.Select(slot => Assert.IsType<Expr.Param>(slot).Name));
    }
}
