using KatLang.Semantics;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// FAITHFUL ORIGINS (R1, owner direction 2026-11-05). A capture of a recursive completion records a determined origin, or
/// one generated cycle origin holding the cycle's members and every source that supplies the name. Everything here reads
/// what real consumers read: the published capture records, diagnostic notes and the semantic model. Sources are named by
/// the line they are written on, so an arbitrary root, a stale record or a position-picked root fails an exact set.
/// </summary>
public sealed class CycleOriginConsumerTests(ITestOutputHelper output)
{
    private static Algorithm.User Body(Algorithm root, string path)
    {
        var body = root;
        foreach (var name in path.Split('.'))
            body = body.Properties.Single(property => property.Name == name).Value;
        return (Algorithm.User)body;
    }

    private static ParameterDeclaration Capture(Algorithm root, string path, string name)
        => ParameterPattern.FlattenCaptures(Body(root, path).ParameterPatterns).First(capture => capture.Name == name);

    /// <summary>The first word of the line a position is on, or the declaring name for a location-free source.</summary>
    private static string Label(string source, SourceSpan? span, string fallback)
    {
        if (span is not { } at)
            return fallback;
        var line = source.Split('\n')[at.Start.Line - 1].Trim();
        return line[..line.IndexOfAny(['(', ' '])];
    }

    /// <summary>The origin of a capture, read from the published record: <c>shared P Q</c> or <c>single P</c>.</summary>
    private static string Origin(string source, string path, string name)
        => Origin(source, Parser.Parse(source), path, name);

    private static string Origin(string source, ParseResult parsed, string path, string name)
    {
        Assert.False(parsed.HasErrors, string.Join("; ", parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        var capture = Capture(parsed.Root, path, name);
        if (capture.InferredProvenance?.CycleOrigin is { } cycle)
        {
            Assert.Null(capture.Span);
            return "shared " + string.Join(" ", cycle.Roots.Select(root => Label(source, root.Span, root.Provider)).Order(StringComparer.Ordinal));
        }

        return "single " + Label(source, capture.OriginSpan, "-");
    }

    private const string Rotation = "P(p) = p\nQ(p) = p\nA = B + P\nB = A + Q\n0";

    // ── the law ─────────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The rotation: <c>A</c>'s first provider is <c>B</c> and <c>B</c>'s is <c>A</c>, so the two sources are shared by both
    /// members. In all 24 declaration orders neither source is singled out.
    /// </summary>
    [Fact]
    public void ARotation_SharesBothSources_InEveryDeclarationOrder()
    {
        foreach (var declared in RecursiveParameterInferenceTests.Permutations(["P(p) = p", "Q(p) = p", "A = B + P", "B = A + Q"]))
        {
            var source = string.Join("\n", declared) + "\n0";
            foreach (var member in new[] { "A", "B" })
                Assert.Equal("shared P Q", Origin(source, member, "p"));
        }
    }

    /// <summary>Renaming a source never moves anything: an alphabetical tie-break would.</summary>
    [Fact]
    public void ARenamedSource_ChangesNothingButItsName()
        => Assert.Equal("shared Q Z", Origin("Z(p) = p\nQ(p) = p\nA = B + Z\nB = A + Q\n0", "A", "p"));

    [Fact]
    public void OneSource_CollapsesToThatDeclaration()
    {
        foreach (var declared in RecursiveParameterInferenceTests.Permutations(["P(p) = p", "A = B + P", "B = A + P"]))
        {
            var source = string.Join("\n", declared) + "\n0";
            Assert.Equal("single P", Origin(source, "A", "p"));
            Assert.Equal("single P", Origin(source, "B", "p"));
        }
    }

    [Fact]
    public void AChainEnteringACycle_InheritsItsOrigin()
    {
        const string Source = "P(p) = p\nQ(p) = p\nA = B + P\nB = A + Q\nC = A + 0\n0";
        Assert.Equal("shared P Q", Origin(Source, "C", "p"));
        var parsed = Parser.Parse(Source);
        Assert.Same(Capture(parsed.Root, "A", "p").InferredProvenance, Capture(parsed.Root, "C", "p").InferredProvenance);
    }

    /// <summary>A chain inside the component that enters the cycle inherits it too, through the same generated note.</summary>
    [Fact]
    public void AMemberWhoseChainEntersTheCycle_InheritsItsOrigin()
    {
        const string Source = "P(p) = p\nQ(p) = p\nA = B + P\nB = A + Q\nC = A + D\nD = C + 0\n0";
        Assert.Equal("shared P Q", Origin(Source, "D", "p"));
    }

    [Fact]
    public void ThreeSources_AreAllShared()
        => Assert.Equal("shared P Q R", Origin("P(p) = p\nQ(p) = p\nR(p) = p\nA = B + P\nB = C + Q\nC = A + R\n0", "B", "p"));

    /// <summary>
    /// A determined chain inside a completed component: <c>B</c>'s first provider of <c>p</c> is <c>A</c>'s own implicit
    /// parameter, although the closed gate met <c>P</c>'s first. The stale first-round record is the refuted behaviour.
    /// </summary>
    [Fact]
    public void ADeterminedChainInsideACompletion_KeepsNoStaleRecord()
    {
        const string Source = "P(p) = p\nA = p + B + 0\nB = A + P\n0";
        var parsed = Parser.Parse(Source);
        Assert.Equal("single A", Origin(Source, parsed, "B", "p"));
        Assert.Same(Capture(parsed.Root, "A", "p").InferredProvenance, Capture(parsed.Root, "B", "p").InferredProvenance);
    }

    /// <summary>A group that keeps its shape around a cycle: each of its names is shared, and each has its own node.</summary>
    [Fact]
    public void AGroupedCallee_EachNameHasItsOwnOrigin()
    {
        const string Source = "P((p, q)) = p\nQ((p, q)) = q\nR(r) = r\nA = B + P + R\nB = A + Q\n0";
        Assert.Equal("shared P Q", Origin(Source, "A", "p"));
        Assert.Equal("shared P Q", Origin(Source, "A", "q"));
        Assert.Equal("single R", Origin(Source, "B", "r"));
        Assert.Equal("A((p, q), r)", RecursiveParameterInferenceTests.Signature(Source, "A"));
    }

    /// <summary>A META declaration is the source of the plain capture lifted from it.</summary>
    [Fact]
    public void AMetaDeclaration_IsTheSourceOfItsPlainCopy()
    {
        var parsed = Parser.Parse("P(meta p) = p\nQ(p) = p\nA = B + P\nB = A + Q\n0");
        Assert.Equal(ParameterKind.Normal, Capture(parsed.Root, "A", "p").Kind);
        Assert.Equal(["P", "Q"], Capture(parsed.Root, "A", "p").InferredProvenance!.CycleOrigin!.Roots.Select(static root => root.Provider).Order(StringComparer.Ordinal));
    }

    [Fact]
    public void AShadowingDeclaration_IsTheInnerSource()
    {
        const string Source = "P(p) = p\nQ(p) = p\nOuter(r) = {\n    P(p) = p + r\n    A = B + P\n    B = A + Q\n    0\n}\n0";
        var cycle = Capture(SourceProvenance.ParseValid(Source).Root, "Outer.A", "p").InferredProvenance!.CycleOrigin!;
        Assert.Equal([2, 4], cycle.Roots.Select(static root => root.Span!.Value.Start.Line).Order());
        Assert.Equal(["A", "B"], cycle.Members.Select(static member => member.Path));
    }

    /// <summary>Q-04: the enclosing binding filters <c>s</c> before anything is a provider, so it is no node and no root.</summary>
    [Fact]
    public void AFilteredName_IsNoSource()
    {
        const string Source = "P(p, s) = p\nQ(p) = p\nOuter(s) = {\n    A = B + P\n    B = A + Q\n    0\n}\n0";
        var parsed = Parser.Parse(Source);
        Assert.Equal(["p"], ParameterPattern.FlattenCaptures(Body(parsed.Root, "Outer.A").ParameterPatterns).Select(static capture => capture.Name));
        Assert.Equal("shared P Q", Origin(Source, parsed, "Outer.A", "p"));
    }

    [Fact]
    public void TwoDeclaringContexts_KeepTheirOwnMembers()
    {
        const string Source = "P(p, r) = p\nQ(p) = p\nOuter(r) = {\n    A = B + P\n    B = A + Q\n    0\n}\nOther = {\n    A = B + P\n    B = A + Q\n    0\n}\n0";
        var parsed = Parser.Parse(Source);
        var (outer, other) = (Capture(parsed.Root, "Outer.A", "p").InferredProvenance!.CycleOrigin!, Capture(parsed.Root, "Other.A", "p").InferredProvenance!.CycleOrigin!);
        Assert.Equal([4, 5], outer.Members.Select(static member => member.Span!.Value.Start.Line));
        Assert.Equal([9, 10], other.Members.Select(static member => member.Span!.Value.Start.Line));
        Assert.False(Capture(parsed.Root, "Outer.A", "p").InferredProvenance!.CycleOrigin!.SameContent(Capture(parsed.Root, "Other.A", "p").InferredProvenance!.CycleOrigin!));
    }

    /// <summary>
    /// Two owners whose lists could be one template hold different records, so they are different lists: <c>C</c> reads the
    /// cycle and <c>D</c> reads <c>Q</c>, with one name and one shape. FE-3 sharing is by record, so it cannot conflate them.
    /// </summary>
    [Fact]
    public void OwnersWithDifferentOrigins_NeverShareAList()
    {
        const string Source = "P(p) = p\nQ(p) = p\nA = B + P\nB = A + Q\nC = A + 0\nD = Q + 0\nE = A + 1\n0";
        var parsed = Parser.Parse(Source);
        Assert.NotSame(Body(parsed.Root, "C").ParameterPatterns, Body(parsed.Root, "D").ParameterPatterns);
        Assert.Same(Body(parsed.Root, "C").ParameterPatterns, Body(parsed.Root, "E").ParameterPatterns);
        Assert.Equal("shared P Q", Origin(Source, parsed, "C", "p"));
        Assert.Equal("single Q", Origin(Source, parsed, "D", "p"));
    }

    /// <summary>
    /// The cycle's providers depend on the link: the reading where <c>L</c> is a runtime reference sees only <c>R</c> and
    /// <c>Q</c>, and it is refuted because it leaves <c>L</c> a calculation. The selected reading adds <c>P</c>. Each reading
    /// seals its own cycle, so the rejected one's origin must not reach the tree.
    /// </summary>
    [Fact]
    public void ARejectedClassification_LeavesNoOrigin()
    {
        const string Source = "Cap(meta op) = op\nId(v) = v\nP(p) = p\nQ(p) = p\nR(p) = p\nOuter(a) = {\n    L = Cap(Id(A + 0)).Algorithm\n    A = B + L.repeat(P) + R\n    B = A + Q\n    0\n}\n0";
        Assert.Equal("shared P Q R", Origin(Source, "Outer.A", "p"));
    }

    /// <summary>An alias reads as its target: origins and the shared flag reach it, with a local span set.</summary>
    [Fact]
    public void ALocalAlias_KeepsItsTargetsOrigins()
    {
        var model = SemanticModelBuilder.Build(Parser.Parse(Rotation.Replace("\n0", "\nZ = A\n0", StringComparison.Ordinal)));
        var parameter = Assert.Single(Assert.Single(model.FindProperties("Z")).Parameters);
        Assert.True(parameter.HasSharedCycleOrigin);
        Assert.Equal([1, 2], parameter.OriginSpans.Select(static span => span.Start.Line).Order());
    }

    /// <summary>A module's alias keeps the shared flag, and its location-free sources give no span from another document.</summary>
    [Fact]
    public async Task AModuleAlias_HasNoForeignSpans()
    {
        var parsed = await Parser.ParseAsync($"M = load('{ModuleUrl}')\nZ = M.A\n0", Serve(Rotation.Replace("A = B", "public A = B", StringComparison.Ordinal)));
        Assert.False(parsed.HasErrors, string.Join("; ", parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        var parameter = Assert.Single(Assert.Single(SemanticModelBuilder.Build(parsed).FindProperties("Z")).Parameters);
        Assert.True(parameter.HasSharedCycleOrigin);
        Assert.Empty(parameter.OriginSpans);
    }

    /// <summary>
    /// One host-built body served to two contexts is one record. Its cycle origin must hold in both, so it names no context:
    /// the report through either path is the same and true.
    /// </summary>
    [Fact]
    public void ASharedBody_NamesItsMembersWithinTheBody()
    {
        const string Body = "{\n        public A = B + P\n        public B = A + Q\n        0\n    }";
        var source = "P(p) = p\nQ(p) = p\nLeft = {\n    public S = " + Body + "\n    0\n}\nRight = {\n    public S = " + Body + "\n    0\n}\nRight.S.A(1, 2)";
        var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(detected.Diagnostics);
        var root = (Algorithm.User)detected.Root;
        var shared = root.Properties.Single(static property => property.Name == "Left").Value.Properties.Single(static property => property.Name == "S").Value;
        var right = (Algorithm.User)root.Properties.Single(static property => property.Name == "Right").Value;
        var host = root with { Properties = [.. root.Properties.Select(property => property.Name == "Right" ? property with { Value = right with { Properties = [right.Properties.Single() with { Value = shared }] } } : property)] };

        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(host, diagnostics: diagnostics);
        Assert.Equal(0, diagnostics.ReportedCount);
        var exposed = PropertyExposureResolver.Resolve(resolved, observations: null);
        foreach (var path in new[] { "Left.S.A", "Right.S.A", "Left.S.B", "Right.S.B" })
        {
            var cycle = Capture(exposed, path, "p").InferredProvenance!.CycleOrigin!;
            Assert.Equal(["A", "B"], cycle.Members.Select(static member => member.Path));
            Assert.Equal(["P", "Q"], cycle.Roots.Select(static root => root.Provider).Order(StringComparer.Ordinal));
        }

        var report = Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed));
        Assert.True(report.IsError);
        Assert.Contains("Parameter 'p' is inferred around the recursive group 'A', 'B'; it comes from 'P' at [1:3], 'Q' at [2:3].",
            KatLangError.FromEvalError(report.Error).Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// A kind-correct view of a source: the completed capture is ORDINARY although its one source is a META declaration, and
    /// collapsing a cycle must not restore the mode.
    /// </summary>
    [Fact]
    public void ACollapsedMetaSource_StaysAPlainCapture()
    {
        var parsed = Parser.Parse("M(meta op) = 0\nA = A + M\n0");
        var capture = Capture(parsed.Root, "A", "op");
        Assert.Equal(ParameterKind.Normal, capture.Kind);
        Assert.Equal(ParameterOriginKey.Of(Capture(parsed.Root, "M", "op")), ParameterOriginKey.Of(capture));
    }

    /// <summary>
    /// A later collector stays the recovered plain capture and keeps its source, and the violation is reported from the
    /// final recomposition, naming both collectors.
    /// </summary>
    [Fact]
    public void ARecoveredCapture_KeepsItsKindAndItsSource()
    {
        var parsed = Parser.Parse("C1(a, *p) = a\nC2(b, *q) = b\nA = C1 + C2 + A\n0");
        var capture = Capture(parsed.Root, "A", "q");
        Assert.Equal(ParameterKind.Normal, capture.Kind);
        Assert.Equal(ParameterOriginKey.Of(Capture(parsed.Root, "C2", "q")), ParameterOriginKey.Of(capture));
        var report = Assert.Single(parsed.Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.InvalidCollectingBinding);
        Assert.Contains("'*p' (needed by 'C1') and '*q' (needed by 'C2')", report.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// A completed group nested under a shared occurrence: <c>Right.M</c> is served from <c>Left.M</c>, so <c>Right.M.S.A</c>
    /// is a lazy projection in the earlier unit's sealed table, and a later unit that inherits the table reads the same
    /// context. The report built from what that inherited projection holds keeps the group and every source.
    /// </summary>
    [Fact]
    public void ALaterUnit_ReadsACompletedGroupBelowASharedOccurrence()
    {
        const string Group = "{\n            public A = B + P\n            public B = A + Q\n            0\n        }";
        const string Middle = "{\n        public S = " + Group + "\n        0\n    }";
        var source = "P(p) = p\nQ(p) = p\nLeft = {\n    public M = " + Middle + "\n    0\n}\nRight = {\n    public M = " + Middle + "\n    0\n}\n0";
        var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(detected.Diagnostics);
        var root = (Algorithm.User)detected.Root;
        var shared = root.Properties.Single(static property => property.Name == "Left").Value.Properties.Single(static property => property.Name == "M").Value;
        var right = (Algorithm.User)root.Properties.Single(static property => property.Name == "Right").Value;
        var host = root with { Properties = [.. root.Properties.Select(property => property.Name == "Right" ? property with { Value = right with { Properties = [right.Properties.Single() with { Value = shared }] } } : property)] };

        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(host, diagnostics: diagnostics);
        Assert.Equal(0, diagnostics.ReportedCount);
        var exposed = PropertyExposureResolver.Resolve(resolved, observations: null);
        var publication = exposed.CompletedStructure!;
        var earlier = publication.Facts;
        var rightMiddle = earlier.Member(earlier.Member(publication.Entry!, "Right")!, "M")!;
        Assert.True(earlier.IsReach(rightMiddle));
        var key = earlier.Member(earlier.Member(rightMiddle, "S")!, "A")!;

        var prelude = publication.Entry!;
        while (prelude.Parent is { } parent)
            prelude = parent;
        var later = new CompletedStaticStructures(prelude, earlier);
        later.Seal();
        var inherited = later.Member(later.Member(rightMiddle, "S")!, "A")!;
        Assert.Same(later.Facts(key), later.Facts(inherited));
        var body = Assert.IsType<Algorithm.User>(later.Facts(inherited)!.Body);
        var capture = ParameterPattern.FlattenCaptures(body.ParameterPatterns).Single();
        var cycle = capture.InferredProvenance!.CycleOrigin!;
        Assert.Equal(["A", "B"], cycle.Members.Select(static member => member.Path));
        Assert.Equal(["P", "Q"], cycle.Roots.Select(static root => root.Provider).Order(StringComparer.Ordinal));

        var report = KatLangError.FromEvalError(new EvalError.ArityMismatch(1, 2)
        {
            Signature = CallableSignature.FromAlgorithm("A", body),
            InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(body.Parameters),
        });
        Assert.Contains("Parameter 'p' is inferred around the recursive group 'A', 'B'; it comes from 'P' at [1:3], 'Q' at [2:3].", report.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// The output validator anchors at a parameter's own occurrence, and a generated capture has none. Given a body that
    /// holds a generated capture and no output, it reports at the written definition, never at a position picked from a root.
    /// </summary>
    [Fact]
    public void TheOutputValidator_AnchorsAtTheDefinition_ForAGeneratedCapture()
    {
        var root = (Algorithm.User)SourceProvenance.ParseValid(Rotation).Root;
        var outputless = root with
        {
            Properties = [.. root.Properties.Select(static property => property.Name == "A"
                ? property with { Value = (Algorithm.User)property.Value with { Output = OutputBundle.Empty } }
                : property)],
        };
        Assert.NotNull(Capture(outputless, "A", "p").InferredProvenance!.CycleOrigin);
        var diagnostics = new DiagnosticBag();
        InferredParameterOutputValidator.ValidateProgram(outputless, diagnostics);
        var report = Assert.Single(diagnostics);
        Assert.Equal(3, report.Span!.Value.Start.Line);
    }

    // ── rootless settled cycles ─────────────────────────────────────────────────────────────────

    /// <summary>
    /// A first-provider cycle with no source. <c>T</c>'s list is <c>[n]</c> in round one and the zero-accepting <c>[*n]</c>
    /// afterwards (Q-04 drops <c>w</c> from <c>V</c>'s collector signature), so <c>I</c> and <c>J</c> acquire <c>n</c> from
    /// <c>T</c> and then stop lifting it while each still reads the other. The settled state is authoritative (no withdrawal
    /// refusal), and R1 states the fact: the shared origin names the group and no source. No root is invented.
    /// </summary>
    private const string Rootless = """
        Vs(*n, w) = 0
        U(n) = n
        Outer(w) = {
            public T = V + U + I + 0
            public I = J + T + 0
            public J = I + T + 0
            0
        }
        V = Vs + Outer.T + 0
        0
        """;

    /// <summary>The same fact, through a collector list reaching the group a round later (independent review's trace).</summary>
    private const string RootlessLater = """
        P(n) = n
        Q(k, *n) = 0
        Outer(k) = {
            public C = D + P
            0
        }
        A = B + Outer.C
        B = A + 0
        D = E + P
        E = Q + A
        0
        """;

    [Fact]
    public void ALaterRootlessCycle_NamesItsGroup()
    {
        var parsed = Parser.Parse(RootlessLater);
        Assert.False(parsed.HasErrors, string.Join("; ", parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        var cycle = Capture(parsed.Root, "A", "n").InferredProvenance!.CycleOrigin!;
        Assert.Empty(cycle.Roots);
        Assert.Equal(["A", "B"], cycle.Members.Select(static member => member.Path));
    }

    /// <summary>Tooling and reports say what is true of it: shared, no span, no source.</summary>
    [Fact]
    public void ARootlessCycle_ReachesItsConsumers()
    {
        var parameter = Assert.Single(Assert.Single(SemanticModelBuilder.Build(Parser.Parse(RootlessLater)).FindProperties("A")).Parameters);
        Assert.True(parameter.HasSharedCycleOrigin);
        Assert.Empty(parameter.OriginSpans);
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(RootlessLater.Replace("\n0", "\nA(1, 2)", StringComparison.Ordinal)));
        Assert.Contains("Parameter 'n' is inferred around the recursive group 'A', 'B'; no declaration outside the group supplies it.",
            failure.Errors[0].Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ASettledCycleWithNoSource_NamesTheGroupAndNoRoot()
    {
        var parsed = Parser.Parse(Rootless);
        Assert.False(parsed.HasErrors, string.Join("; ", parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        Assert.Equal("T(*n)", SemanticModelBuilder.Build(parsed).FindProperties("T").Single().DisplaySignature);
        foreach (var member in new[] { "Outer.I", "Outer.J" })
        {
            var capture = Capture(parsed.Root, member, "n");
            Assert.Null(capture.Span);
            var cycle = capture.InferredProvenance!.CycleOrigin!;
            Assert.Empty(cycle.Roots);
            Assert.Equal(["I", "J"], cycle.Members.Select(static m => m.Path));
        }
    }

    // ── locationless content ────────────────────────────────────────────────────────────────────

    private const string ModuleUrl = "https://modules.example/m.kat";

    private static RunOptions Serve(string module) => new()
    {
        AllowedHosts = ["modules.example"],
        DownloadCode = (_, _) => ValueTask.FromResult(module),
    };

    /// <summary>Imported content has no position: its origin is the declaration record, with no fictitious span.</summary>
    [Fact]
    public async Task ImportedContent_KeepsItsRecords_WithoutASpan()
    {
        var parsed = await Parser.ParseAsync($"M = load('{ModuleUrl}')\n0", Serve("P(p) = p\nQ(p) = p\nA = B + P\nB = A + Q\n0"));
        var capture = Capture(parsed.Root, "M.A", "p");
        Assert.Null(capture.Span);
        var cycle = capture.InferredProvenance!.CycleOrigin!;
        Assert.Equal(["P", "Q"], cycle.Roots.Select(static root => root.Provider).Order(StringComparer.Ordinal));
        Assert.All(cycle.Roots, static root => Assert.Null(root.Span));
        Assert.Equal(2, cycle.Roots.Select(static root => ParameterOriginKey.Of(root.Declaration)).Distinct().Count());
    }

    /// <summary>A location-free META copy and its declaration are one origin: nothing else can identify them.</summary>
    [Fact]
    public async Task AnImportedMetaCopy_IsItsDeclaration()
    {
        var parsed = await Parser.ParseAsync($"M = load('{ModuleUrl}')\n0", Serve("P(meta p) = 0\nA = B + P\nB = A + P\nC = P + 0\n0"));
        var declared = Capture(parsed.Root, "M.P", "p");
        Assert.Equal(ParameterOriginKey.Of(declared), ParameterOriginKey.Of(Capture(parsed.Root, "M.A", "p")));
        Assert.Equal(ParameterOriginKey.Of(declared), ParameterOriginKey.Of(Capture(parsed.Root, "M.C", "p")));
        Assert.Null(Capture(parsed.Root, "M.A", "p").InferredProvenance);
    }

    // ── consumers ───────────────────────────────────────────────────────────────────────────────

    /// <summary>An arity report names the group and both sources, and singles out neither.</summary>
    [Fact]
    public void AnArityReport_NamesTheCycleAndEverySource()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("P(p) = p\nQ(p) = p\nA = if(tick() > 2, 0, B + P)\nB = A + Q\nA(1, 2)"));
        Assert.Contains("Parameter 'p' is inferred around the recursive group 'A', 'B'; it comes from 'P' at [1:3], 'Q' at [2:3].",
            failure.Errors[0].Message, StringComparison.Ordinal);
    }

    /// <summary>A report keeps each promotion's own note and position: a cycle hides neither source.</summary>
    [Fact]
    public void AnUnresolvedReport_KeepsEveryPromotionNote()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("value = 1\nP = valeu + 1\nQ = valeu + 2\nA = if(tick() > 2, 0, B + P)\nB = A + Q\nA"));
        var message = failure.Errors[0].Message;
        Assert.Contains("Parameter 'valeu' is inferred around the recursive group 'A', 'B'; it comes from 'P' at [2:5], 'Q' at [3:5].", message, StringComparison.Ordinal);
        Assert.Contains("An implicit parameter 'valeu' was inferred at [2:5].", message, StringComparison.Ordinal);
        Assert.Contains("An implicit parameter 'valeu' was inferred at [3:5].", message, StringComparison.Ordinal);
    }

    /// <summary>A single-origin completion reports exactly as an ordinary lift does: no cycle sentence.</summary>
    [Fact]
    public void ACollapsedOrigin_ReportsAsAnOrdinaryLift()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("P = valeu + 1\nvalue = 1\nA = if(tick() > 2, 0, B + P)\nB = A + P\nA"));
        Assert.DoesNotContain("recursive group", failure.Errors[0].Message, StringComparison.Ordinal);
        Assert.Contains("Did you mean 'value'?", failure.Errors[0].Message, StringComparison.Ordinal);
    }

    /// <summary>An editor gets a set for a shared parameter, one span for a determined one and never a single arbitrary one.</summary>
    [Fact]
    public void TheSemanticModel_ExposesTheOriginSet()
    {
        const string Source = "P(p) = p\nQ(p) = p\nA = B + P\nB = A + Q\nC = P + 0\n0";
        var model = SemanticModelBuilder.Build(Parser.Parse(Source));
        var shared = Assert.Single(Assert.Single(model.FindProperties("A")).Parameters);
        Assert.True(shared.HasSharedCycleOrigin);
        Assert.Null(shared.Span);
        Assert.Equal([1, 2], shared.OriginSpans.Select(static span => span.Start.Line).Order());

        var determined = Assert.Single(Assert.Single(model.FindProperties("C")).Parameters);
        Assert.False(determined.HasSharedCycleOrigin);
        Assert.Equal(1, Assert.Single(determined.OriginSpans).Start.Line);
        Assert.Empty(Assert.Single(Assert.Single(model.FindProperties("P")).Parameters).OriginSpans);
    }

    /// <summary>Grouped signatures reach editors through the flat parameter list.</summary>
    [Fact]
    public void TheSemanticModel_ExposesGroupedOrigins()
    {
        var parameters = Assert.Single(SemanticModelBuilder.Build(Parser.Parse("P((p, q)) = p\nQ((p, q)) = q\nR(r) = r\nA = B + P + R\nB = A + Q\n0")).FindProperties("A")).Parameters;
        Assert.True(parameters.Single(static parameter => parameter.Name == "p").HasSharedCycleOrigin);
        Assert.False(parameters.Single(static parameter => parameter.Name == "r").HasSharedCycleOrigin);
    }

    /// <summary>Two models of one document compare equal: an origin set has value equality.</summary>
    [Fact]
    public void OriginSpans_CompareByValue()
    {
        var first = Assert.Single(SemanticModelBuilder.Build(Parser.Parse(Rotation)).FindProperties("A")).Parameters[0];
        var second = Assert.Single(SemanticModelBuilder.Build(Parser.Parse(Rotation)).FindProperties("A")).Parameters[0];
        Assert.Equal(first, second);
    }

    private static (string Source, string Left, string Right) SharedCyclePathFixture(int width, int nameLength)
    {
        var left = "A" + new string('a', nameLength);
        var right = "B" + new string('b', nameLength);
        var parameters = string.Join(", ", Enumerable.Range(0, width).Select(static i => $"p{i}"));
        return ($"P({parameters}) = 0\nQ({parameters}) = 0\n"
            + $"{left} = {{\n    public X = {right}.Y + P\n    0\n}}\n"
            + $"{right} = {{\n    public Y = {left}.X + Q\n    0\n}}\n0", left, right);
    }

    /// <summary>
    /// Many names can have the same cycle members. Doubling both the names and the written path length must not copy
    /// those paths once per name: their logical membership grows, while their immutable backing can be shared.
    /// </summary>
    [Fact]
    public void SharedCycleMemberPaths_AllocationTracksTheSourceRatherThanItsProduct()
    {
        static long Measure((string Source, string Left, string Right) fixture, int width)
        {
            var before = GC.GetAllocatedBytesForCurrentThread();
            var parsed = Parser.Parse(fixture.Source);
            var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.False(parsed.HasErrors, string.Join("; ", parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));
            var member = parsed.Root.Properties.Single(property => property.Name == fixture.Left).Value.Properties.Single().Value;
            var captures = ParameterPattern.FlattenCaptures(member.ParameterPatterns);
            Assert.Equal(width, captures.Count);
            foreach (var capture in new[] { captures[0], captures[^1] })
            {
                var cycle = Assert.IsType<ParameterCycleOrigin>(capture.InferredProvenance?.CycleOrigin);
                Assert.Equal([fixture.Left + ".X", fixture.Right + ".Y"], cycle.Members.Select(static item => item.Path));
                Assert.Equal(["P", "Q"], cycle.Roots.Select(static root => root.Provider));
                Assert.All(cycle.Roots, root => Assert.Equal(capture.Name, root.Declaration.Name));
            }

            GC.KeepAlive(parsed);
            return allocated;
        }

        var small = SharedCyclePathFixture(64, 32768);
        var large = SharedCyclePathFixture(128, 65536);
        _ = Measure(small, 64);
        _ = Measure(large, 128);
        var smallBytes = Measure(small, 64);
        var largeBytes = Measure(large, 128);
        output.WriteLine($"Cycle member path allocation: {smallBytes} -> {largeBytes} bytes ({(double)largeBytes / smallBytes:F3}x).");
        Assert.True(largeBytes < 2.8 * smallBytes, $"Cycle member paths grew {smallBytes} -> {largeBytes} bytes.");
    }

    /// <summary>
    /// Long joined paths occupy structural metadata, even when there are only two captures. A ceiling sufficient for
    /// short paths must refuse this preparation, leave the input untouched, and allow a funded retry of that same tree.
    /// </summary>
    [Fact]
    public void JoinedCycleMemberPaths_RequireFundedStorageBeforePublication()
    {
        static Algorithm Input(string source)
        {
            var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
            Assert.Empty(detected.Diagnostics);
            return detected.Root;
        }

        static StaticStructureOperation Operation(Algorithm input, long? storage = null)
        {
            var prelude = BuiltinRegistry.CreateSemanticPreludeAlgorithm();
            var limits = StaticStructureAdmission.Measure(input, prelude).Limits;
            var operation = new StaticStructureOperation(input, storage is { } bound ? limits with { MaxStorageUnits = bound } : limits,
                prelude, phase: StaticAstPhase.NameResolved);
            operation.RegisterNameResolvedInput(input);
            return operation;
        }

        var shortInput = Input(SharedCyclePathFixture(2, 1).Source);
        var shortOperation = Operation(shortInput);
        _ = ImplicitArgumentResolver.ResolvePrevalidated(shortInput, structuralOperation: shortOperation);
        const int LongLength = 16384;
        var fixture = SharedCyclePathFixture(2, LongLength);
        var longInput = Input(fixture.Source);
        var restricted = Operation(longInput, shortOperation.Queries.Resources.PeakStorageUnits + 1);
        var observations = new FrontEndTraversalObservations();
        Assert.Throws<StaticQueryLimitExceededException>(
            () => ImplicitArgumentResolver.ResolvePrevalidated(longInput, observations, structuralOperation: restricted));
        Assert.True(observations.SignatureSelectionSteps > 0);
        Assert.True(restricted.Queries.Resources.IsFailed);
        Assert.Null(longInput.CompletedStructure);
        Assert.Empty(longInput.Properties.Single(property => property.Name == fixture.Left).Value.Properties.Single().Value.Params);

        var funded = Operation(longInput);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(longInput, structuralOperation: funded);
        Assert.True(funded.Queries.Resources.MetadataUnits >= shortOperation.Queries.Resources.MetadataUnits + LongLength / 32);
        var member = resolved.Properties.Single(property => property.Name == fixture.Left).Value.Properties.Single().Value;
        var origin = ParameterPattern.FlattenCaptures(member.ParameterPatterns)[0].InferredProvenance!.CycleOrigin!;
        Assert.Equal([fixture.Left + ".X", fixture.Right + ".Y"], origin.Members.Select(static item => item.Path));
        Assert.Equal(["P", "Q"], origin.Roots.Select(static item => item.Provider));
    }

}
