using KatLang.Optimizations.Loops;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// FE-3: K distinct owners that each lift the same L-wide callee hold K × L LOGICAL
/// (owner, slot) bindings — each owner's parameters are its own declarations, bound in its own
/// activations. The front end represents them as ONE shared, immutable signature TEMPLATE (the
/// lifted pattern list, whose capture records lifting already shared with the callee) plus, per
/// owner, only what is genuinely the owner's: its identity and its own parameters (a head composed
/// over the shared tail). Every later pass derives template facts once per template and owner facts
/// per owner, so the physical representation and the work are O(K + L), never K × L.
///
/// <para>These pins count the representation (reference identity) and the work (the per-pass
/// observation counters), prove owner identity is never collapsed (declarations, activations,
/// ownership completion through each owner's own layer, blame, editor metadata), and prove that
/// runtime behavior — randomness, host operations, genuine async suspension, planned loops — is
/// exactly the written form's.</para>
/// </summary>
public class ImplicitSignatureTemplateTests
{
    private static string Names(string prefix, int count, string separator = ", ")
        => string.Join(separator, Enumerable.Range(0, count).Select(i => $"{prefix}{i}"));

    private static string Arguments(int count, int offset = 0)
        => string.Join(", ", Enumerable.Range(offset, count));

    /// <summary><c>G = v0 + … + v(L-1)</c> and K owners <c>A(i) = abs(G)</c>; root <c>1</c>.</summary>
    private static string Owners(int owners, int width, string separator = " + ")
        => $"G = {Names("v", width, separator)}\n"
            + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = abs(G)\n"))
            + "1";

    /// <summary>Like <see cref="Owners"/>, each owner also owning one implicit parameter: <c>A(i) = abs(G) + w(i)</c>.</summary>
    private static string OwnersWithOwnParameter(int owners, int width, string separator = " + ")
        => $"G = {Names("v", width, separator)}\n"
            + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = abs(G) + w{i}\n"))
            + "1";

    private static IReadOnlyList<Algorithm.User> OwnerAlgorithms(Algorithm root)
        => [.. root.Properties.Where(p => p.Name.StartsWith('A')).Select(p => Assert.IsType<Algorithm.User>(p.Value))];

    private static IEnumerable<Expr.Call> CallsTo(Algorithm algorithm, string callee)
    {
        var pending = new Stack<object>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        pending.Push(algorithm);
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node))
                continue;
            switch (node)
            {
                case Algorithm.User user:
                    foreach (var property in user.Properties) pending.Push(property.Value);
                    foreach (var row in user.Output) pending.Push(row);
                    break;
                case Algorithm.Conditional conditional:
                    foreach (var branch in conditional.Branches) pending.Push(branch.Body);
                    break;
                case Expr.Call call:
                    if (call.Function is Expr.Resolve(var name) && name == callee)
                        yield return call;
                    pending.Push(call.Function);
                    foreach (var argument in call.Args) pending.Push(argument);
                    break;
                case Expr.Binary binary:
                    pending.Push(binary.Left);
                    pending.Push(binary.Right);
                    break;
                case Expr.Unary unary:
                    pending.Push(unary.Operand);
                    break;
                case Expr.AlgorithmExpr block:
                    pending.Push(block.Algorithm);
                    break;
            }
        }
    }

    // ── Passes, each observed on its own ─────────────────────────────────────

    private sealed record PassObservations(
        FrontEndTraversalObservations Resolve,
        FrontEndTraversalObservations Completion,
        FrontEndTraversalObservations Collision,
        FrontEndTraversalObservations OpenProviders,
        FrontEndTraversalObservations Exposure,
        FrontEndTraversalObservations Preflight,
        FrontEndTraversalObservations Semantic);

    private static PassObservations ObservePasses(string source)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var origins = new ImplicitArgumentResolver.ResolutionOrigins();
        var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(syntax, graceOrigins: origins.Grace);
        Assert.Empty(detectorDiagnostics);
        var observed = new PassObservations(new(), new(), new(), new(), new(), new(), new());
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observed.Resolve, diagnostics, origins);
        Assert.True(origins.HasLiftedParameters);
        var completed = ParameterDetector.CompleteOwnership(resolved, origins, observations: observed.Completion);
        Assert.False(completed.Changed);
        Assert.Empty(completed.Diagnostics);
        new ParameterPropertyCollisionValidator(diagnostics, programRoot: resolved) { TraversalObservations = observed.Collision }
            .VisitAlgorithm(resolved);
        OpenProviderValidator.Validate(resolved, diagnostics, (HostOperations?)null, observed.OpenProviders);
        var exposed = PropertyExposureResolver.Resolve(resolved, observed.Exposure);
        Assert.Empty(diagnostics);
        Assert.Null(AstStructuralPreflight.Check(
            new Expr.AlgorithmExpr(exposed), EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines, observed.Preflight));
        SemanticModelBuilder.Build(exposed, observed.Semantic);
        return observed;
    }

    // ── Representation ───────────────────────────────────────────────────────

    /// <summary>
    /// K owners of one L-wide callee: every owner stores the SAME template instance (L patterns — the
    /// callee's own capture records), so the tree holds K × L logical bindings in L physical pattern
    /// slots; the K lifted calls are K distinct, spanned call nodes sharing ONE argument bundle.
    /// </summary>
    [Theory]
    [InlineData(16, 24)]
    [InlineData(32, 48)]
    [InlineData(64, 8)]
    [InlineData(8, 64)]
    public void ManyOwners_ShareOneTemplate_AndOneArgumentBundle(int owners, int width)
    {
        var root = SourceProvenance.ParseValid(Owners(owners, width)).Root;
        var ownerAlgorithms = OwnerAlgorithms(root);
        Assert.Equal(owners, ownerAlgorithms.Count);

        var template = Assert.IsType<ImplicitSignatureTemplate>(ownerAlgorithms[0].ParameterPatterns);
        Assert.False(template.IsComposed);
        Assert.Equal(width, template.Count);
        Assert.All(ownerAlgorithms, owner => Assert.Same(template, owner.ParameterPatterns));
        Assert.Equal((long)owners * width, ownerAlgorithms.Sum(owner => (long)owner.ParameterCount));

        // The template's patterns ARE the callee's capture records (no per-owner copy of any leaf).
        var callee = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, p => p.Name == "G").Value);
        Assert.Equal(width, callee.ParameterPatterns.Count);
        for (var i = 0; i < width; i++)
            Assert.Same(callee.ParameterPatterns[i], template[i]);

        var calls = ownerAlgorithms.SelectMany(owner => CallsTo(owner, "G")).ToList();
        Assert.Equal(owners, calls.Count);
        Assert.All(calls, call => Assert.Same(calls[0].Args, call.Args));
        Assert.Equal(owners, calls.Select(call => call.Span).Distinct().Count());
        Assert.All(calls[0].Args, slot => Assert.Null(slot.Span));
    }

    /// <summary>
    /// The resolver builds the template once and gives each owner an instance costing only its own
    /// head; no owner materializes a signature of its own, and one bundle of L slots is built.
    /// </summary>
    [Theory]
    [InlineData(16, 24, false)]
    [InlineData(48, 16, false)]
    [InlineData(16, 24, true)]
    [InlineData(48, 16, true)]
    public void Resolver_BuildsOneTemplate_AndOwnerInstancesCostTheirHeads(int owners, int width, bool ownParameter)
    {
        var observed = ObservePasses(ownParameter ? OwnersWithOwnParameter(owners, width) : Owners(owners, width)).Resolve;

        Assert.Equal(1, observed.SignatureTemplatesBuilt);
        Assert.Equal(width, observed.SignatureTemplateSlotsBuilt);
        Assert.Equal(owners, observed.OwnerSignatureInstances);
        Assert.Equal(ownParameter ? owners : 0, observed.OwnerSignatureHeadSlots);
        Assert.Equal(0, observed.OwnerSignaturesMaterialized);
        Assert.Equal(owners, observed.ImplicitCallsSynthesized);
        Assert.Equal(1, observed.ImplicitArgumentBundlesBuilt);
        Assert.Equal(width, observed.ImplicitArgumentSlotsBuilt);
    }

    /// <summary>
    /// An owner with a parameter of its own composes its OWN head over the shared tail: the heads are
    /// distinct (each owner's own capture record), the tail is one instance, the order is the
    /// owner's own parameters first, and the lifted callee's bundle is still shared.
    /// </summary>
    [Fact]
    public void OwnersWithOwnParameters_ComposeTheirHead_OverTheSharedTail()
    {
        const int owners = 12;
        const int width = 16;
        var root = SourceProvenance.ParseValid(OwnersWithOwnParameter(owners, width)).Root;
        var ownerAlgorithms = OwnerAlgorithms(root);
        var tail = Assert.IsType<ImplicitSignatureTemplate>(ownerAlgorithms[0].ParameterPatterns).Tail;
        Assert.NotNull(tail);
        for (var i = 0; i < owners; i++)
        {
            var signature = Assert.IsType<ImplicitSignatureTemplate>(ownerAlgorithms[i].ParameterPatterns);
            Assert.True(signature.IsComposed);
            Assert.Same(tail, signature.Tail);
            Assert.Equal($"w{i}", Assert.IsType<CaptureParameterPattern>(Assert.Single(signature.Head)).Name);
            Assert.Equal([$"w{i}", .. Enumerable.Range(0, width).Select(j => $"v{j}")], ownerAlgorithms[i].Params);
        }

        Assert.Equal(owners, ownerAlgorithms.Select(owner => ((ImplicitSignatureTemplate)owner.ParameterPatterns).Head[0]).Distinct(ReferenceEqualityComparer.Instance).Count());
        var calls = ownerAlgorithms.SelectMany(owner => CallsTo(owner, "G")).ToList();
        Assert.All(calls, call => Assert.Same(calls[0].Args, call.Args));
        Assert.Equal("29", KatLangEngine.Run($"G = v0 + v1\nA = G + w\nA(10, {Arguments(2, 9)})").ToDisplayString());
    }

    /// <summary>
    /// Every pass that was K × L-shaped for many owners of one wide callee is now bounded by a linear
    /// function of K and L — ownership completion, declaration validation, exposure and its summary
    /// channel, the structural preflight, and the editor model's own FE-3 work — with and without an
    /// owner-local parameter per owner.
    /// </summary>
    [Theory]
    [InlineData(64, 64, false)]
    [InlineData(128, 32, false)]
    [InlineData(32, 128, false)]
    [InlineData(64, 64, true)]
    [InlineData(128, 32, true)]
    [InlineData(32, 128, true)]
    public void LaterPasses_CostOwnersPlusWidth_NotTheirProduct(int owners, int width, bool ownParameter)
    {
        var observed = ObservePasses(ownParameter ? OwnersWithOwnParameter(owners, width) : Owners(owners, width));
        long Linear(int factor) => (long)factor * (owners + width) + 64;

        // Ownership completion extends by one template layer per owner, never L entries per owner.
        Assert.Equal(owners, observed.Completion.ContextTemplateLayers);
        Assert.InRange(observed.Completion.ContextEntriesWritten, 0, Linear(4));
        // Declaration validation: one layer for the shared tail under the one enclosing context.
        Assert.Equal(1, observed.Collision.ContextTemplateLayers);
        Assert.InRange(observed.Collision.ContextEntriesWritten, 0, Linear(4));
        Assert.InRange(observed.Collision.ContextNamesCanonicalized, 0, Linear(4));
        Assert.InRange(observed.Collision.WalkerExpressionExpansions, 0, Linear(4));
        // Exposure: owner names come from the template (the callee's own list is materialized once),
        // and the owners' shared bundle seed is never folded, qualified, and stripped per owner.
        Assert.Equal(width, observed.Exposure.OwnerParameterNamesMaterialized);
        Assert.Equal(0, observed.Exposure.SummaryQualificationProbes);
        Assert.InRange(observed.Exposure.SummaryResidualNameProbes, 0, Linear(4));
        Assert.InRange(observed.Exposure.DependencySeedExpansions, 0, Linear(4));
        Assert.Equal(0, observed.Exposure.ExposureArgumentBundleRewrites);
        // Preflight: the template is one grouping child of every owner, walked once.
        Assert.InRange(observed.Preflight.StructuralPreflightEdges, 0, Linear(12));
        // Editor: the shared bundle is never re-analyzed per owner frame.
        Assert.Equal(owners, observed.Semantic.SemanticModelCallArgumentSlots);
        Assert.InRange(observed.Semantic.SemanticModelExpressionVisits, 0, Linear(8));
    }

    /// <summary>
    /// Owners that each declare their own <c>open</c> are validated in their own scope regions, but
    /// the validator walks only toward nested algorithms: the owners' shared bundle is never
    /// re-walked per region (the validator's open-presence scan still reads it once).
    /// </summary>
    [Theory]
    [InlineData(64, 64)]
    [InlineData(128, 32)]
    public void OwnersWithTheirOwnOpens_AreValidatedWithoutRewalkingTheSharedBundle(int owners, int width)
    {
        var source = $"G = {Names("v", width)}\nLib = {{\n    public X = 1\n}}\n"
            + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = {{\n    open Lib\n    abs(G) + X\n}}\n")) + "1";
        var observed = ObservePasses(source);
        Assert.Equal(owners + width, observed.OpenProviders.WalkerCallArgumentSlots);
        Assert.InRange(observed.OpenProviders.WalkerExpressionExpansions, 0, 16L * (owners + width) + 64);
    }

    /// <summary>
    /// Owners nested in K DISTINCT enclosing contexts (each parent owns a parameter of its own) still
    /// cost one template layer per context: ownership completion and declaration validation never write
    /// the template's L names per context.
    /// </summary>
    [Theory]
    [InlineData(64, 64)]
    [InlineData(128, 32)]
    public void OwnersInDistinctParentContexts_ExtendEachContextByOneLayer(int owners, int width)
    {
        var source = $"G = {Names("v", width)}\n"
            + string.Concat(Enumerable.Range(0, owners).Select(i => $"B{i} = {{\n    A = abs(G)\n    A + w{i}\n}}\n")) + "1";
        var observed = ObservePasses(source);
        long Linear(int factor) => (long)factor * (owners + width) + 64;
        Assert.Equal(2L * owners, observed.Completion.ContextTemplateLayers);
        Assert.InRange(observed.Completion.ContextEntriesWritten, 0, Linear(4));
        Assert.Equal(owners + 1L, observed.Collision.ContextTemplateLayers);
        Assert.InRange(observed.Collision.ContextEntriesWritten, 0, Linear(4));
        Assert.InRange(observed.Collision.ContextNamesCanonicalized, 0, Linear(4));
        Assert.Equal(0, observed.Exposure.SummaryQualificationProbes);
        Assert.Equal(owners, observed.Semantic.SemanticModelCallArgumentSlots);
    }

    /// <summary>
    /// A design-independent guard over the public parse and run path: doubling K = L roughly doubles
    /// the allocation (the former per-owner representation quadrupled it). The editor model is left
    /// out: its per-scope visible-symbol snapshots are the separate K × W representation (FE-4b).
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PublicParseAndRun_AllocationGrowsLinearly(bool ownParameter)
    {
        static long Allocation(string source)
        {
            void Pass()
            {
                var parsed = Parser.Parse(source);
                Assert.False(parsed.HasErrors);
                Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
            }

            Pass();
            var before = GC.GetAllocatedBytesForCurrentThread();
            Pass();
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        // G's names as output rows: a long `+` chain would exceed the structural depth gate.
        string Source(int n) => ownParameter ? OwnersWithOwnParameter(n, n, ", ") : Owners(n, n, ", ");
        var small = Allocation(Source(256));
        var large = Allocation(Source(512));
        var ratio = (double)large / small;
        Assert.True(ratio < 2.6, $"Doubling K = L grew the allocation {ratio:F2}x ({small} -> {large} bytes).");
    }

    // ── Owner identity is never shared ───────────────────────────────────────

    /// <summary>
    /// Two owners over one template are two declarations with their own activations: each binds its
    /// own arguments, and the same owner called twice binds each call afresh.
    /// </summary>
    [Fact]
    public void OwnersSharingATemplate_AreDistinctDeclarations_WithOwnActivations()
    {
        var source = $"G = {Names("v", 10, " + ")}\nA = G + 1000\nB = G * 2\nA({Arguments(10)}), B({Arguments(10, 1)}), A({Arguments(10, 2)})";
        var root = SourceProvenance.ParseValid(source).Root;
        var a = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, p => p.Name == "A").Value);
        var b = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, p => p.Name == "B").Value);
        Assert.Same(a.ParameterPatterns, b.ParameterPatterns);
        Assert.NotNull(a.Declaration);
        Assert.NotSame(a.Declaration, b.Declaration);
        Assert.Equal("1045\n110\n1065", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// A closed branch body inside each owner reads a name only the owner's LIFTED signature binds:
    /// ownership completion resolves it through the owner's own template layer — A's to A's
    /// argument, B's to B's — so a layer is never answered by another owner of the same template.
    /// </summary>
    [Fact]
    public void LiftedNameReadInsideTheOwner_BindsToThatOwner()
    {
        var source = $"G = {Names("v", 10, " + ")}\nA = {{\n    F(0) = v0\n    F(n) = n\n    F(0) + abs(G)\n}}\n"
            + $"B = {{\n    F(0) = v1 * 10\n    F(n) = n\n    F(0) + abs(G)\n}}\nA({Arguments(10, 1)}), B({Arguments(10, 1)})";
        var parsed = SourceProvenance.ParseValid(source);
        var a = Assert.IsType<Algorithm.User>(Assert.Single(parsed.Root.Properties, p => p.Name == "A").Value);
        var b = Assert.IsType<Algorithm.User>(Assert.Single(parsed.Root.Properties, p => p.Name == "B").Value);
        Assert.Same(a.ParameterPatterns, b.ParameterPatterns);
        Assert.Equal("56\n75", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>The same spelling in two owners is two owner-local captures over one shared tail.</summary>
    [Fact]
    public void SameSpellingInTwoOwners_StaysTwoDeclarations()
    {
        var source = $"G = {Names("v", 10, " + ")}\nA = abs(G) + x\nB = abs(G) * x\nA(1, {Arguments(10)}), B(2, {Arguments(10)})";
        var root = SourceProvenance.ParseValid(source).Root;
        var a = Assert.IsType<ImplicitSignatureTemplate>(Assert.Single(root.Properties, p => p.Name == "A").Value.ParameterPatterns);
        var b = Assert.IsType<ImplicitSignatureTemplate>(Assert.Single(root.Properties, p => p.Name == "B").Value.ParameterPatterns);
        Assert.Same(a.Tail, b.Tail);
        Assert.NotSame(a.Head[0], b.Head[0]);
        Assert.Equal("x", Assert.IsType<CaptureParameterPattern>(a.Head[0]).Name);
        Assert.Equal("x", Assert.IsType<CaptureParameterPattern>(b.Head[0]).Name);
        Assert.Equal("46\n90", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// Signatures with the same names but another order, another collecting/fixed kind, or another
    /// pattern shape are different templates.
    /// </summary>
    [Theory]
    [InlineData("G1 = a + b\nG2 = b - a\nA = G1 + G2\nB = G2 + G1\nA(1, 2), B(1, 2)", "4\n2")]
    [InlineData("G1(*xs) = xs.count\nG2 = xs + 0\nA = G1 + 1\nB = G2 + 1\nA(5, 6), B(5)", "3\n6")]
    [InlineData("G1((p, q)) = p + q\nG2 = p + q\nA = G1 + 1\nB = G2 + 1\nA((1, 2)), B(1, 2)", "4\n4")]
    public void DifferentOrderKindOrShape_NeverShareATemplate(string source, string display)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var a = Assert.Single(root.Properties, p => p.Name == "A").Value;
        var b = Assert.Single(root.Properties, p => p.Name == "B").Value;
        Assert.NotSame(a.ParameterPatterns, b.ParameterPatterns);
        Assert.Equal(display, KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// The same signature reached through different derivations — a lifting chain, a nested owner,
    /// and a diamond of two owners of one callee — is one template: identity is exact content, never
    /// the derivation path.
    /// </summary>
    [Fact]
    public void SameTemplateReachedDifferently_IsShared()
    {
        var source = $"G = {Names("v", 10, " + ")}\nA = abs(G)\nB = abs(A)\nC = abs(B)\nD = {{\n    E = abs(G)\n    E\n}}\n"
            + $"P = abs(G)\nQ = abs(G)\nR = P + Q\nR({Arguments(10)}) + C({Arguments(10)}) + D({Arguments(10)})";
        var root = SourceProvenance.ParseValid(source).Root;
        var template = Assert.IsType<ImplicitSignatureTemplate>(Assert.Single(root.Properties, p => p.Name == "A").Value.ParameterPatterns);
        foreach (var name in new[] { "B", "C", "D", "P", "Q", "R" })
            Assert.Same(template, Assert.Single(root.Properties, p => p.Name == name).Value.ParameterPatterns);
        Assert.Equal("180", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// Two OPEN owners reach one collecting callee with different forwarding SOURCES: A's <c>x</c> is
    /// lifted from a collecting capture, so the callee's <c>*x</c> re-collects A's items (<c>C(x*)</c>),
    /// while B's <c>x</c> is a fixed capture, forwarded as one argument (<c>C(x)</c>). Their bundles are
    /// different pure functions of their inputs and are never shared: a bundle key blind to the
    /// caller's binding kinds would hand B A's spread.
    /// </summary>
    [Fact]
    public void OwnersForwardingDifferently_NeverShareABundle()
    {
        const string source = "G1(*x) = x.count\nG2(x) = 0\nC(*x) = x.count\nA = G1 + C\nB = G2 + C\nA(1, 2, 3), B((1, 2, 3))";
        var root = SourceProvenance.ParseValid(source).Root;
        var a = Assert.Single(CallsTo(Assert.Single(root.Properties, p => p.Name == "A").Value, "C"));
        var b = Assert.Single(CallsTo(Assert.Single(root.Properties, p => p.Name == "B").Value, "C"));
        Assert.NotSame(a.Args, b.Args);
        Assert.IsType<Expr.SequenceSpread>(Assert.Single(a.Args));
        Assert.IsType<Expr.Param>(Assert.Single(b.Args));
        Assert.Equal("6\n1", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// An owner whose own name is also lifted keeps its own order — its capture first, the lifted one
    /// filtered — so its signature is genuinely its own (materialized for that owner, never shared).
    /// </summary>
    [Fact]
    public void OwnNameAlsoLifted_KeepsTheOwnersOwnOrder()
    {
        const string source = "G = a + b\nA = G + a\nB = G * b\nA(1, 2), B(3, 4)";
        var syntaxRoot = SourceProvenance.ParseSyntaxValidRoot(source);
        var (detected, _) = ParameterDetector.DetectPrevalidated(syntaxRoot);
        var observations = new FrontEndTraversalObservations();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations);
        Assert.Equal(2, observations.OwnerSignaturesMaterialized);
        Assert.Equal(["a", "b"], Assert.Single(resolved.Properties, p => p.Name == "A").Value.Params);
        Assert.Equal(["b", "a"], Assert.Single(resolved.Properties, p => p.Name == "B").Value.Params);
        Assert.Equal("4\n21", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    // ── Runtime behavior is the written form's ───────────────────────────────

    /// <summary>Seeded draws through template owners equal the explicitly written owners' draws.</summary>
    [Fact]
    public void SeededDraws_AcrossOwners_MatchTheWrittenForm()
    {
        var parameters = Names("v", 10);
        var body = $"G = random(0, 100) + {Names("v", 10, " + ")}\n";
        var lifted = body + $"A = G + 0\nB = G + 0\nA({Arguments(10)}), B({Arguments(10)}), A({Arguments(10)})";
        var written = body + $"A({parameters}) = G({parameters}) + 0\nB({parameters}) = G({parameters}) + 0\nA({Arguments(10)}), B({Arguments(10)}), A({Arguments(10)})";
        var options = new RunOptions { RandomSeed = 20260926 };
        var liftedResult = Assert.IsType<RunResult.Success>(KatLangEngine.Run(lifted, options));
        var writtenResult = Assert.IsType<RunResult.Success>(KatLangEngine.Run(written, options));
        Assert.Equal(writtenResult.ToDisplayString(), liftedResult.ToDisplayString());
        Assert.Equal(3, Assert.IsType<Result.SequenceValue>(liftedResult.Value).Items.Distinct().Count());
    }

    /// <summary>A host operation reached through several template owners runs once per call, in order, with the owner's own arguments.</summary>
    [Fact]
    public void HostOperation_AcrossOwners_RunsPerCallInOrder()
    {
        List<string> Log(string source)
        {
            var log = new List<string>();
            var options = new RunOptions
            {
                HostOperations = HostOperations.Create(HostOperation.Create("Tick", (args, _) =>
                {
                    log.Add(((Result.Atom)args[0]).Value.ToString());
                    return args[0];
                }, "v")),
            };
            Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, options));
            return log;
        }

        var parameters = Names("v", 10);
        var body = $"G = Tick(v0) + {Names("v", 10, " + ")}\n";
        var lifted = Log(body + $"A = G + 1\nB = G + 2\nA({Arguments(10, 5)}), B({Arguments(10, 7)}), A({Arguments(10, 9)})");
        var written = Log(body + $"A({parameters}) = G({parameters}) + 1\nB({parameters}) = G({parameters}) + 2\nA({Arguments(10, 5)}), B({Arguments(10, 7)}), A({Arguments(10, 9)})");
        Assert.Equal(["5", "7", "9"], lifted);
        Assert.Equal(written, lifted);
    }

    /// <summary>
    /// Genuine suspension through two template owners: each call reaches the asynchronous operation
    /// with its OWN owner's argument, waits for its own release, observes the supplied token, and
    /// the results arrive in release order.
    /// </summary>
    [Fact]
    public async Task AsyncHostOperation_AcrossOwners_SuspendsPerCall_WithTheSuppliedToken()
    {
        const int calls = 3;
        var gates = Enumerable.Range(0, calls).Select(_ => new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
        var reached = Enumerable.Range(0, calls).Select(_ => new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
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
                reached[index].TrySetResult(((Result.Atom)args[0]).Value.ToString());
                return await gates[index].Task;
            }, "v")),
        };

        var source = $"G = Wait(v0) + {Names("v", 10, " + ")}\nA = G + 1000\nB = G + 2000\nA({Arguments(10, 1)}), B({Arguments(10, 2)}), A({Arguments(10, 3)})";
        var run = KatLangEngine.RunAsync(source, options);
        var expectedArguments = new[] { "1", "2", "3" };
        for (var i = 0; i < calls; i++)
        {
            var completed = await Task.WhenAny(reached[i].Task, Task.Delay(TimeSpan.FromSeconds(30)));
            Assert.Same(reached[i].Task, completed);
            Assert.Equal(expectedArguments[i], await reached[i].Task);
            Assert.False(run.IsCompleted);
            gates[i].SetResult(new Result.Atom((i + 1) * 100));
        }

        Assert.Equal("1155\n2265\n1375", (await run).ToDisplayString().ReplaceLineEndings("\n"));
        Assert.Equal(calls, invocations);
        Assert.All(tokens, token => Assert.Equal(cancellation.Token, token));
    }

    /// <summary>A failure inside a shared callee is blamed on the owner whose call raised it, never the first owner.</summary>
    [Fact]
    public void Failures_AreBlamedOnTheirOwnOwner()
    {
        var division = KatLangEngine.Run($"G = v0 / v1 + {Names("v", 10, " + ")}\nA = G + 1\nB = G + 2\nA({Arguments(10, 1)}), B(1, 0, 3, 4, 5, 6, 7, 8, 9, 10)");
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(division).Errors);
        Assert.Equal(KatLangErrorCode.DivisionByZero, error.Code);
        Assert.Contains("call to B", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("call to A", error.Message, StringComparison.Ordinal);

        var arity = KatLangEngine.Run($"G = {Names("v", 10, " + ")}\nA = G + 1\nB = G + 2\nA({Arguments(10)}), B(1)");
        var arityError = Assert.Single(Assert.IsType<RunResult.EvalFailure>(arity).Errors);
        Assert.Equal(KatLangErrorCode.ArityMismatch, arityError.Code);
        Assert.Contains("B(", arityError.Message, StringComparison.Ordinal);
        Assert.Equal(new SourcePosition(4, 34), arityError.Span!.Value.Start);
    }

    /// <summary>A planned loop over a template owner agrees with generic execution, and the plan ran.</summary>
    [Fact]
    public void PlannedLoop_OverATemplateOwner_MatchesGenericExecution()
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(
            "G = x * 2\nK = G + 1\nStep(x) = K(x) + G(x) + x\nrepeat(Step, 3, 1)").Root);
        var diagnostics = new LoopOptimizationDiagnostics();

        var optimized = Evaluator.RunCountedObserved(program, enableOptimizations: true, loopDiagnostics: diagnostics).Result;
        var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false).Result;

        Assert.False(optimized.IsError);
        Assert.False(generic.IsError);
        Assert.Equal(generic.Value.Value, optimized.Value.Value);
        Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
    }

    // ── Editor metadata stays owner-specific ─────────────────────────────────

    /// <summary>
    /// Each owner keeps its own declaration, display signature, and receiver-injected signature, while
    /// the owners' parameter metadata — owner-independent — is one shared immutable list; references to
    /// each owner resolve to that owner's declaration.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EditorModel_OwnersSharingATemplate_KeepOwnerSpecificMetadata(bool ownParameter)
    {
        const int owners = 6;
        const int width = 10;
        var source = (ownParameter ? OwnersWithOwnParameter(owners, width) : Owners(owners, width)).TrimEnd('1')
            + $"A3({(ownParameter ? "7, " : "")}{Arguments(width)})";
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var model = SemanticModelBuilder.Build(parsed);

        IReadOnlyList<PropertyParameterInfo>? sharedTail = null;
        for (var i = 0; i < owners; i++)
        {
            var declaration = Assert.Single(model.FindDeclarations($"A{i}"));
            var info = Assert.IsType<PropertyInfo>(model.FindResolutionAt(declaration.Span.Start)?.ResolvedProperty);
            var names = (ownParameter ? [$"w{i}"] : Array.Empty<string>()).Concat(Enumerable.Range(0, width).Select(j => $"v{j}")).ToArray();
            Assert.Equal($"A{i}({string.Join(", ", names)})", info.DisplaySignature);
            Assert.Equal($"{names[0]}.A{i}({string.Join(", ", names.Skip(1))})", info.GetDisplaySignature(PropertyCallStyle.Dot));
            Assert.Equal(names, info.Parameters.Select(parameter => parameter.Name));
            Assert.All(info.Parameters, parameter => Assert.Equal(PropertyParameterKind.Implicit, parameter.Kind));
            Assert.True(info.SupportsLexicalDotCall);
            if (!ownParameter)
            {
                sharedTail ??= info.Parameters;
                Assert.Same(sharedTail, info.Parameters);
            }
        }

        var use = model.FindResolutionAt(new SourcePosition(owners + 2, 1));
        Assert.NotNull(use);
        Assert.Equal("A3", use.Occurrence.Name);
        Assert.Equal(Assert.Single(model.FindDeclarations("A3")), use.ResolvedDeclaration);
    }

    /// <summary>A composed owner's completion inside its body lists its own head and the shared tail, as implicit parameters.</summary>
    [Fact]
    public void EditorModel_CompletionInsideAnOwner_ListsItsOwnParameters()
    {
        var source = $"G = {Names("v", 10, " + ")}\nA = {{\n    abs(G) + x\n}}\nB = {{\n    abs(G) * y\n}}\nA(1, {Arguments(10)}) + B(2, {Arguments(10)})";
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        var insideA = model.GetVisibleSymbolsAt(new SourcePosition(3, 6)).Where(s => s.Classification is IdentifierClassification.ImplicitParameterReference).Select(s => s.Name).ToHashSet();
        var insideB = model.GetVisibleSymbolsAt(new SourcePosition(6, 6)).Where(s => s.Classification is IdentifierClassification.ImplicitParameterReference).Select(s => s.Name).ToHashSet();
        Assert.Contains("x", insideA);
        Assert.DoesNotContain("y", insideA);
        Assert.Contains("y", insideB);
        Assert.DoesNotContain("x", insideB);
        Assert.All(Enumerable.Range(0, 10), j => Assert.Contains($"v{j}", insideA));
        Assert.All(Enumerable.Range(0, 10), j => Assert.Contains($"v{j}", insideB));
    }

    /// <summary>A lazily composed signature text is the eager one: equal values, equal hashes, equal text.</summary>
    [Fact]
    public void LazySignatureText_IsValueEqualToTheEagerOne()
    {
        var parameters = new SharedPropertyParameterList([new PropertyParameterInfo("v0", PropertyParameterKind.Implicit, null)]);
        var composed = 0;
        var lazy = new PropertySignatureInfo(PropertyCallStyle.Plain, () => { composed++; return "A(v0)"; }, parameters);
        var eager = new PropertySignatureInfo(PropertyCallStyle.Plain, "A(v0)", parameters);
        Assert.Same(lazy.Parameters, eager.Parameters);
        Assert.Equal(0, composed);
        Assert.Equal(eager, lazy);
        Assert.Equal(eager.GetHashCode(), lazy.GetHashCode());
        Assert.Equal("A(v0)", lazy.DisplayText);
        Assert.Equal(1, composed);
        Assert.Equal(eager.ToString(), lazy.ToString());
        Assert.NotEqual(eager, new PropertySignatureInfo(PropertyCallStyle.Plain, () => "B(v0)", lazy.Parameters));
    }

    // ── Lifetime, immutability, concurrency ─────────────────────────────────

    /// <summary>Templates are run-local: two parses never share one, and a dropped parse result releases its template.</summary>
    [Fact]
    public void Templates_AreRunLocal_AndReleasedWithTheirTree()
    {
        var first = Assert.IsType<ImplicitSignatureTemplate>(OwnerAlgorithms(SourceProvenance.ParseValid(Owners(4, 10)).Root)[0].ParameterPatterns);
        var second = Assert.IsType<ImplicitSignatureTemplate>(OwnerAlgorithms(SourceProvenance.ParseValid(Owners(4, 10)).Root)[0].ParameterPatterns);
        Assert.NotSame(first, second);

        var weak = ParseAndReleaseTemplate();
        for (var i = 0; i < 5 && weak.IsAlive; i++)
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();
        }

        Assert.False(weak.IsAlive);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static WeakReference ParseAndReleaseTemplate()
    {
        var template = OwnerAlgorithms(SourceProvenance.ParseValid(Owners(8, 12)).Root)[0].ParameterPatterns;
        Assert.IsType<ImplicitSignatureTemplate>(template);
        _ = ((ImplicitSignatureTemplate)template).Facts.NameSet.Count;
        return new WeakReference(template);
    }

    /// <summary>A shared template has no mutation route, and the public projections stay fresh per read.</summary>
    [Fact]
    public void SharedTemplate_HasNoMutationRoute_AndProjectionsStayFresh()
    {
        var owner = OwnerAlgorithms(SourceProvenance.ParseValid(Owners(3, 10)).Root)[0];
        Assert.IsType<ImplicitSignatureTemplate>(owner.ParameterPatterns);
        Assert.DoesNotContain(typeof(ICollection<ParameterPattern>), owner.ParameterPatterns.GetType().GetInterfaces());
        Assert.DoesNotContain(typeof(System.Collections.IList), owner.ParameterPatterns.GetType().GetInterfaces());
        Assert.NotSame(owner.Params, owner.Params);
        Assert.NotSame(owner.Parameters, owner.Parameters);
        Assert.Equal(owner.Parameters.Select(parameter => parameter.Name), owner.Params);
    }

    /// <summary>Concurrent readers of one parsed tree — editor models and evaluations — observe identical results.</summary>
    [Fact]
    public void ConcurrentReaders_OfOneParsedTree_ObserveTheSameFacts()
    {
        var source = OwnersWithOwnParameter(24, 16).TrimEnd('1') + $"A5(1, {Arguments(16)}) + A9(2, {Arguments(16)})";
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var results = new string[16];
        Parallel.For(0, results.Length, i =>
        {
            var model = SemanticModelBuilder.Build(parsed);
            var signatures = string.Join(";", model.PropertyInfos.Select(info => info.DisplaySignature + "|" + info.GetDisplaySignature(PropertyCallStyle.Dot)));
            var run = Evaluator.RunFlat(program);
            results[i] = signatures + "=" + string.Join(",", run.Value);
        });
        Assert.All(results, result => Assert.Equal(results[0], result));
        Assert.EndsWith("=243", results[0], StringComparison.Ordinal);
    }

    // ── Modules and deferred regions ─────────────────────────────────────────

    private const string ModuleUrl = "https://katlang.org/fe3/owners.kat";

    private static readonly string OwnersModule =
        $"public G = {Names("v", 10, " + ")}\npublic A = G + 1\npublic B = G * 2\npublic C = G + w";

    /// <summary>Owners declared in a module lift through shared templates at every import site, with importer-correct values.</summary>
    [Fact]
    public async Task ModuleOwners_LiftThroughSharedTemplates_AtEveryImportSite()
    {
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult(OwnersModule),
            AllowedHosts = ["katlang.org"],
        };
        var source = $"P = {{\n    open '{ModuleUrl}'\n    A({Arguments(10)}) + B({Arguments(10)})\n}}\nQ = {{\n    open '{ModuleUrl}'\n    C(7, {Arguments(10)})\n}}\nP + Q";
        var parsed = await SourceProvenance.ParseValidAsync(source, options);
        Assert.Empty(parsed.Parsed.Diagnostics);
        Assert.Equal("188", (await KatLangEngine.RunAsync(source, options)).ToDisplayString());
    }

    /// <summary>An unselected deferred region never materializes; a selected one elaborates its owners through templates.</summary>
    [Fact]
    public async Task DeferredRegion_UnselectedNeverMaterializes_SelectedElaboratesItsOwners()
    {
        var downloads = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                Interlocked.Increment(ref downloads);
                return ValueTask.FromResult(OwnersModule);
            },
            AllowedHosts = ["katlang.org"],
        };
        var family = $"F(0) = {{\n    open '{ModuleUrl}'\n    A({Arguments(10)}) + C(1, {Arguments(10)})\n}}\nF(n) = n\n";
        Assert.Equal("5", (await KatLangEngine.RunAsync(family + "F(5)", options)).ToDisplayString());
        Assert.Equal(0, downloads);
        Assert.Equal("92", (await KatLangEngine.RunAsync(family + "F(0)", options)).ToDisplayString());
        Assert.Equal(1, downloads);
    }

    // ── Structural preflight over shared templates ──────────────────────────

    /// <summary>
    /// A template shared by several owners is one grouping child of each, walked once; a crossing
    /// inside it is reported at the pattern the pattern-by-pattern walk reports.
    /// </summary>
    [Fact]
    public void SharedTemplate_IsWalkedOnce_AndACrossingInsideItIsPositionedAtThePattern()
    {
        ParameterPattern deep = new CaptureParameterPattern("p");
        for (var i = 0; i < 12; i++)
            deep = new SequenceValueParameterPattern([deep]);
        var template = ImplicitSignatureTemplate.Flat([new CaptureParameterPattern("a"), deep]);
        Algorithm.User Owner() => new(null, template, [], [], new OutputBundle([new Expr.Num(1)]));
        var root = new Algorithm.User(null, [], [], [new Property("A", Owner()), new Property("B", Owner()), new Property("C", Owner())], new OutputBundle([new Expr.Num(0)]));

        var observations = new FrontEndTraversalObservations();
        Assert.Null(AstStructuralPreflight.Check(root, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive, observations));
        // Root: 3 property values and 1 row; each owner: 1 row and 1 template edge; the template's 2
        // patterns and the 12 nested groups' single items, once.
        Assert.Equal(4 + 3 * 2 + 2 + 12, observations.StructuralPreflightEdges);

        var rejection = AstStructuralPreflight.Check(root, maxDepth: 8, AstConsumerProfile.FullyRecursive);
        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);
    }
}
