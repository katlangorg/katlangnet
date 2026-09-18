using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// One coordinate space per result (Task 3a). Every source span exposed in the result
/// of processing a document belongs to that document's coordinate space: a module a
/// document loads is parsed as its own document, but the tree that crosses into the
/// loading document is the module's LOCATIONLESS import view
/// (<c>ModuleLoader.ToImportView</c>), so a module-relative line/column can never be
/// presented as a position in the document. A construct inside the view is later
/// reported at a location the current document supplies: the evaluator's
/// attach-if-missing rule at the demanding expression, the front end's import-site
/// anchor (<see cref="ImportSite"/>), or the load site for nested module loads. None of
/// this relies on <see cref="SourceSpan"/> object identity, and none of it fabricates a
/// sentinel coordinate for a removed module span.
/// </summary>
public class ModuleCoordinateSpaceTests
{
    private const string Lib = "https://katlang.org/lib.kat";
    private const string ModuleB = "https://katlang.org/b.kat";
    private const string ModuleC = "https://katlang.org/c.kat";

    // The failing expression sits on module line 4, columns 15-20 — coordinates that
    // exist in no caller below (every caller is at most three lines long, or places
    // something else there), so a leak is never masked by coincidence.
    private const string BoomModule = "# module comment line 1\n\n\npublic Boom = 10 / 0\npublic Fine = 7";
    private static readonly SourceSpan ModuleBoomSpan = new(4, 15, 4, 20);

    private static RunOptions Options(params (string Url, string Source)[] modules)
    {
        var files = modules.ToDictionary(module => module.Url, module => module.Source, StringComparer.Ordinal);
        return new RunOptions
        {
            DownloadCode = (url, _) => files.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : throw new InvalidOperationException($"404: {url}"),
        };
    }

    private static KatLangError SingleEvalError(RunResult result)
        => Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);

    private static void AssertSpan(KatLangError error, int line, int column, int endLine, int endColumn)
        => Assert.Equal(new SourceSpan(line, column, endLine, endColumn), error.Span);

    private static void AssertNotTheModuleSpan(KatLangError error)
        => Assert.NotEqual(ModuleBoomSpan, error.Span);

    private static Algorithm.User ImportedModule(Algorithm.User root, string propertyName)
        => Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, p => p.Name == propertyName).Value);

    private static Algorithm.User OpenedModule(Algorithm.User root, int index = 0)
        => Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(root.Opens[index]).Algorithm);

    // ── 1–2. Module runtime error: the local demand, never module coordinates ──

    [Fact]
    public async Task ModuleRuntimeError_OpenedProvider_IsReportedAtTheLocalDemandNotAtModuleCoordinates()
    {
        // Before Task 3a this reported [4:15-4:20] — the module's own coordinates — in a
        // two-line document. The error originates inside the locationless import view,
        // so the attach-if-missing rule positions it at the demanding reference `Boom`.
        var error = SingleEvalError(await KatLangEngine.RunAsync("open '" + Lib + "'\nBoom", Options((Lib, BoomModule))));
        Assert.Equal(KatLangErrorCode.DivisionByZero, error.Code);
        AssertSpan(error, 2, 1, 2, 5);
        AssertNotTheModuleSpan(error);
        // The attachment happened on the error itself: no context frame supplied it.
        Assert.Equal(new SourceSpan(2, 1, 2, 5), Innermost(error.Source!).Span);
    }

    [Fact]
    public async Task ModuleRuntimeError_StructuralMemberAccess_IsReportedAtTheLocalDotCall()
    {
        var error = SingleEvalError(await KatLangEngine.RunAsync("M = load('" + Lib + "')\nM.Boom", Options((Lib, BoomModule))));
        Assert.Equal(KatLangErrorCode.DivisionByZero, error.Code);
        AssertSpan(error, 2, 1, 2, 7);
        AssertNotTheModuleSpan(error);
    }

    [Fact]
    public async Task ModuleRuntimeError_DemandedFromANestedLocalBlock_IsReportedAtTheNearestLocalExpression()
    {
        var source = "M = load('" + Lib + "')\nG = {\n  H = M.Boom + 1\n  H }\nG";
        var error = SingleEvalError(await KatLangEngine.RunAsync(source, Options((Lib, BoomModule))));
        Assert.Equal(KatLangErrorCode.DivisionByZero, error.Code);
        AssertSpan(error, 3, 7, 3, 13);
    }

    [Fact]
    public async Task ImportedCallableArityError_KeepsTheLocalCallSite()
    {
        var error = SingleEvalError(await KatLangEngine.RunAsync(
            "open '" + Lib + "'\nFine(1)", Options((Lib, "\n\n\npublic Fine(a, b) = a + b"))));
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        AssertSpan(error, 2, 1, 2, 8);
    }

    // ── 3. Nested module chain: A's result stays in A's coordinate space ────

    [Fact]
    public async Task NestedModuleChain_RuntimeError_IsReportedInTheDocumentsCoordinateSpace()
    {
        // C's failing expression is on C's line 13; B opens C on B's line 6; A opens B on
        // A's line 1 and demands `FromB` on line 2. Neither B's nor C's coordinates exist in A.
        var options = Options(
            (ModuleB, "\n\n\n\n\nopen '" + ModuleC + "'\npublic FromB = FromC + 1"),
            (ModuleC, "\n\n\n\n\n\n\n\n\n\n\n\n        public FromC = 10 / 0"));
        var error = SingleEvalError(await KatLangEngine.RunAsync("open '" + ModuleB + "'\nFromB", options));
        Assert.Equal(KatLangErrorCode.DivisionByZero, error.Code);
        AssertSpan(error, 2, 1, 2, 6);
    }

    [Fact]
    public async Task NestedModuleChain_LoadFailureInsideAModule_IsReportedAtTheDocumentsLoadSite()
    {
        // B's own `open 'c'` (B line 6) fails to fetch. The load written inside B has no span
        // in A's result; the loader positions its diagnostic at A's load site — never at B's
        // line 6, never at a sentinel.
        var parsed = await Parser.ParseAsync(
            "open '" + ModuleB + "'\nFromB",
            Options((ModuleB, "\n\n\n\n\nopen '" + ModuleC + "'\npublic FromB = FromC + 1")));
        var failure = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.LoadFetchFailed);
        Assert.Equal(new SourceSpan(1, 6, 1, 33), failure.Span);
        Assert.Contains(ModuleC, failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task NestedModuleChain_LoadCycleInsideAModule_IsReportedAtTheDocumentsLoadSite()
    {
        var parsed = await Parser.ParseAsync(
            "open '" + ModuleB + "'\n1",
            Options(
                (ModuleB, "\n\n\n\nopen '" + ModuleC + "'\npublic FromB = 1"),
                (ModuleC, "\n\n\n\n\n\nopen '" + ModuleB + "'\npublic FromC = 2")));
        var cycle = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.LoadCycle);
        Assert.Equal(new SourceSpan(1, 6, 1, 33), cycle.Span);
    }

    // ── 4. Deferred materialization ─────────────────────────────────────────

    [Fact]
    public async Task DeferredBranch_MaterializedModuleError_IsReportedAtTheLocalDemand_AndTheRegionStaysLocationless()
    {
        var source = "F(0) = 1\nF(x) = { open '" + Lib + "'\n Boom }\nF(3)";
        var options = Options((Lib, BoomModule));
        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties, p => p.Name == "F").Value);
        var placeholder = family.Branches[1].Body;
        var region = placeholder.DeferredRegion;
        Assert.NotNull(region);
        Assert.Null(region.ImportSite); // The branch body is the document's own text.

        var first = SingleEvalError(await KatLangEngine.RunAsync(source, options));
        Assert.Equal(KatLangErrorCode.DivisionByZero, first.Code);
        AssertSpan(first, 3, 2, 3, 6);
        AssertNotTheModuleSpan(first);

        // The same parsed tree evaluated twice: the region materializes once and is reused;
        // the reused body is the same object, its module content stays locationless, and
        // the second run acquires the same local span.
        var run1 = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        var run2 = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(run1.IsError);
        Assert.True(run2.IsError);
        Assert.Equal(new SourceSpan(3, 2, 3, 6), run1.Error.Span);
        Assert.Equal(run1.Error.Span, run2.Error.Span);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.True(region.TryGetMaterialized(out var materialized));
        Assert.Same(placeholder.Declaration, materialized.Declaration);
        var openedModule = OpenedModule(Assert.IsType<Algorithm.User>(materialized));
        Assert.True(openedModule.IsModuleElaborated);
        LocationlessAssertion.AssertLocationless(openedModule);
        // The branch's own open target keeps its LOCAL span on the wrapper node.
        Assert.Equal(new SourceSpan(2, 15, 2, 44), Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(materialized.Opens)).Span);
    }

    [Fact]
    public async Task DeferredBranchInsideAModule_RecordsTheDocumentsImportSite_AndUsesItForItsDiagnostics()
    {
        // The family lives inside module B (B's text); its selected branch loads module C,
        // whose front-end validity fails (a parameter/property collision at C line 3). The
        // region records A's import site (the `load('…b.kat')` call) and every demand-time
        // diagnostic is positioned there — in A's coordinate space.
        var source = "\n\nM = load('" + ModuleB + "')\nM.F(1)";
        var options = Options(
            (ModuleB, "public F(0) = 0\npublic F(x) = { open '" + ModuleC + "'\n  Bad }"),
            (ModuleC, "\n\npublic Bad = K(2)\nK(a) = { a = 3\n a }"));
        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(ImportedModule(parsed.Root, "M").Properties).Value);
        var region = family.Branches[1].Body.DeferredRegion;
        Assert.NotNull(region);
        Assert.Equal(new SourceSpan(3, 5, 3, 38), region.ImportSite);

        var error = SingleEvalError(await KatLangEngine.RunAsync(source, options));
        Assert.Equal(KatLangErrorCode.ParameterPropertyCollision, error.Code);
        AssertSpan(error, 3, 5, 3, 38);
        Assert.DoesNotContain("line 4", error.Message, StringComparison.Ordinal);
    }

    // ── 5. Same module, several demands: no caller location is retained ─────

    [Fact]
    public async Task SameModuleSplicedTwice_IsOneLocationlessInstance_AndEachDemandAcquiresItsOwnLocalSpan()
    {
        const string source = "A = load('" + Lib + "')\n\nB = load('" + Lib + "')\n\n   B.Boom";
        var options = Options((Lib, BoomModule));
        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors);
        var a = ImportedModule(parsed.Root, "A");
        var b = ImportedModule(parsed.Root, "B");
        Assert.Same(a, b);
        LocationlessAssertion.AssertLocationless(a);

        // The second splice — a cache hit — reports at ITS demand, on line 5.
        var viaB = SingleEvalError(await KatLangEngine.RunAsync(source, options));
        AssertSpan(viaB, 5, 4, 5, 10);

        // The first splice, demanded in its own run, reports at ITS demand, on line 6.
        const string demandA = "A = load('" + Lib + "')\n\nB = load('" + Lib + "')\n\n\nA.Boom";
        var viaA = SingleEvalError(await KatLangEngine.RunAsync(demandA, options));
        AssertSpan(viaA, 6, 1, 6, 7);
    }

    [Fact]
    public async Task SameModuleDemandedFromTwoLocalSites_ReportsWhicheverSiteFailsFirst()
    {
        const string source = "open '" + Lib + "'\nA = Fine\n\n\n      B = Boom\nA + B";
        var error = SingleEvalError(await KatLangEngine.RunAsync(source, Options((Lib, BoomModule))));
        AssertSpan(error, 5, 11, 5, 15);
        AssertNotTheModuleSpan(error);
    }

    // ── 6. Provenance notes ─────────────────────────────────────────────────

    [Fact]
    public async Task ImportedProvenance_CarriesNoModuleCoordinate_InTheStructuredNoteOrTheMessage()
    {
        // The dot member `Ceiling` is at module column 20; the promotion's note records no
        // span at all (its occurrence is imported), so the rendered message states the
        // inference without a coordinate while keeping the receiver-aware suggestion.
        var error = SingleEvalError(await KatLangEngine.RunAsync(
            "open '" + Lib + "'\nFine", Options((Lib, "\n\n\npublic Fine = Math.Ceiling(2.1)"))));
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        AssertSpan(error, 2, 1, 2, 5);
        Assert.Contains("An implicit parameter 'Ceiling' was inferred from an unresolved name.", error.Message, StringComparison.Ordinal);
        Assert.Contains("Did you mean 'Math.Ceil'?", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("[4:", error.Message, StringComparison.Ordinal);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error.Source!));
        var note = Assert.Single(arity.InferredImplicitParameters!);
        Assert.Null(note.Span);
        Assert.Equal("Math.Ceil", note.SuggestedName);
    }

    [Fact]
    public async Task LocalProvenance_StillRendersItsLocalCoordinate()
    {
        var error = SingleEvalError(await KatLangEngine.RunAsync("\nFine = Math.Ceiling(2.1)\nFine", Options()));
        Assert.Contains("was inferred at [2:13]", error.Message, StringComparison.Ordinal);
    }

    // ── 7. Front-end diagnostics inside an import view: the import site ─────

    public static TheoryData<string, string, DiagnosticCode> ImportedFrontEndFailures() => new()
    {
        { "collision", "\n\n\npublic Fine = 7\nK(a) = { a = 3\n a }", DiagnosticCode.ParameterPropertyCollision },
        { "closed list", "\n\n\npublic Fine = 7\nK(a) = a + zz", DiagnosticCode.UndeclaredIdentifier },
        { "closed branch", "\n\n\npublic Fine = 7\nK(0) = zz\nK(x) = x", DiagnosticCode.UndeclaredIdentifier },
        { "illegal open", "\n\n\nopen count\npublic Fine = 7", DiagnosticCode.IllegalInOpen },
        { "parameter open head", "\n\n\npublic Fine = 7\nK(p) = { open p\n 1 }", DiagnosticCode.OpenTargetIsParameter },
        { "ineffective grace", "\n\n\npublic Fine = 7\nK(p) = ~p", DiagnosticCode.InvalidGraceMarker },
    };

    [Theory]
    [MemberData(nameof(ImportedFrontEndFailures))]
    public async Task ImportedFrontEndFailure_OpenedModule_IsReportedAtTheOpenTarget(string shape, string module, DiagnosticCode code)
    {
        Assert.NotNull(shape);
        var parsed = await Parser.ParseAsync("open '" + Lib + "'\nFine", Options((Lib, module)));
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(code, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 6, 1, 35), diagnostic.Span);
        Assert.DoesNotContain("line 4", diagnostic.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("line 5", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(ImportedFrontEndFailures))]
    // Refused strict-value forwarding is reported by implicit-argument resolution, which
    // walks open-target regions without a diagnostics sink (an opened module's refusal is
    // left to evaluation, exactly as before); a property-held module is an ordinary nested
    // body, so the front end reports it — at the import site.
    [InlineData("blocked forwarding", "\n\n\npublic Fine = 7\nHelper = base + 1\nK(a) = a + Math.Abs(Helper)", DiagnosticCode.UndeclaredIdentifier)]
    public async Task ImportedFrontEndFailure_PropertyHeldModule_IsReportedAtTheDeclaringProperty(string shape, string module, DiagnosticCode code)
    {
        Assert.NotNull(shape);
        // The load call is unwrapped into the property's direct value, so the site the
        // document offers is the declaring name `M` on line 3.
        var parsed = await Parser.ParseAsync("\n\nM = load('" + Lib + "')\nM.Fine", Options((Lib, module)));
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(code, diagnostic.Code);
        Assert.Equal(new SourceSpan(3, 1, 3, 2), diagnostic.Span);
    }

    [Theory]
    [MemberData(nameof(ImportedFrontEndFailures))]
    public async Task ImportedFrontEndFailure_InAModuleAModuleImports_IsReportedAtTheDocumentsOwnSite(string shape, string module, DiagnosticCode code)
    {
        Assert.NotNull(shape);
        // B (imported on A's line 2) imports C on B's line 4; C's failure lands at A's site.
        var parsed = await Parser.ParseAsync(
            "\nopen '" + ModuleB + "'\nFromB",
            Options((ModuleB, "\n\n\nopen '" + ModuleC + "'\npublic FromB = Fine"), (ModuleC, module)));
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(code, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 6, 2, 33), diagnostic.Span);
    }

    [Fact]
    public async Task ImportedFrontEndFailure_ModuleInExpressionPosition_IsReportedAtTheLoadCall()
    {
        var parsed = await Parser.ParseAsync(
            "P = { 1, load('" + Lib + "') }\nP",
            Options((Lib, "\n\n\nopen count\n5")));
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.IllegalInOpen, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 10, 1, 45), diagnostic.Span);
    }

    [Fact]
    public async Task ImportedCollision_WithALocalParameter_NamesTheLocalParameterPosition()
    {
        // The module's property `a` collides with the DOCUMENT's parameter `a` of F: the
        // report sits at the import site and names the parameter's local position only.
        var parsed = await Parser.ParseAsync(
            "F(a) = {\n  M = load('" + Lib + "')\n  M.a }\nF(1)",
            Options((Lib, "\n\n\npublic a = 3")));
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.ParameterPropertyCollision, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 3, 2, 4), diagnostic.Span);
        Assert.Contains("declared at line 1, column 3", diagnostic.Message, StringComparison.Ordinal);
    }

    // ── 8. The import view is structurally locationless ─────────────────────

    [Fact]
    public async Task ImportView_CarriesNoSourceLocationAnywhere_WhileLocalWrappersKeepTheirs()
    {
        // Every location-bearing syntax at once: explicit and nested parameter patterns with
        // a collect marker, clause-head binders, a deconstruction, a dot member, a spread
        // marker, list and index syntax, and a nested open.
        var module = "open Math\npublic F(x, (y, *z)) = x + y\npublic G(0) = 'a'\npublic G(n) = n.count\nH = { a, *b = 1, 2, 3\n a + b.count }\nF(1, (2, 3))*\n[H]:0";
        var parsed = await Parser.ParseAsync(
            "open '" + Lib + "'\nM = load('" + Lib + "')\n1",
            Options((Lib, module)));
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Span + " " + d.Code + " " + d.Message)));
        var held = ImportedModule(parsed.Root, "M");
        var opened = OpenedModule(parsed.Root);
        Assert.True(held.IsModuleElaborated);
        Assert.True(opened.IsModuleElaborated);
        LocationlessAssertion.AssertLocationless(held);
        LocationlessAssertion.AssertLocationless(opened);
        // The document's own wrapper of the opened module keeps the local open-target span,
        // and the document's own declaration keeps its span.
        Assert.Equal(new SourceSpan(1, 6, 1, 35), Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(parsed.Root.Opens)).Span);
        Assert.Equal([new SourceSpan(2, 1, 2, 2)], Assert.Single(parsed.Root.Properties, p => p.Name == "M").DeclarationSpans);
    }

    [Fact]
    public async Task ImportView_KeepsTheWrittenOrderOfHoistedDeconstructionRows()
    {
        // The hoisted right-hand side `G(p, q)` is written before the output row `a + r`,
        // so F's implicit signature is (p, q, r) — recovered structurally, never from spans.
        const string module = "public F = { a, b = G(p, q)\n a + r }\nG(x, y) = x, y";
        var parsed = await Parser.ParseAsync("open '" + Lib + "'\nF(1, 2, 3)", Options((Lib, module)));
        Assert.False(parsed.HasErrors);
        var imported = Assert.IsType<Algorithm.User>(Assert.Single(OpenedModule(parsed.Root).Properties, p => p.Name == "F").Value);
        Assert.Equal(["p", "q", "r"], imported.Params);
        var local = SourceProvenance.ParseValid("F(1, 2, 3)\n" + module.Replace("public ", "", StringComparison.Ordinal));
        Assert.Equal(["p", "q", "r"], Assert.IsType<Algorithm.User>(Assert.Single(local.Root.Properties, p => p.Name == "F").Value).Params);
        Assert.Equal([4m], await KatLangEngine.EvaluateToAtomsAsync("open '" + Lib + "'\nF(1, 2, 3)", Options((Lib, module))));
        Assert.Equal([4m], KatLangEngine.EvaluateToAtoms(local.Source));
    }

    [Theory]
    [MemberData(nameof(ExprVariantCatalog.VariantNames), MemberType = typeof(ExprVariantCatalog))]
    public void ImportView_StripsEveryVariantsSpan_AndPreservesASpanlessVariantByReference(string variant)
    {
        var sample = ExprVariantCatalog.Samples[variant];
        var spanned = sample with { Span = new SourceSpan(7, 1, 7, 10) };
        var root = new Algorithm.User(null, [], [], [], [spanned, sample]);

        var view = InvokeToImportView(root);

        // The spanned occurrence loses exactly its location — it is structurally the
        // spanless sample — while the already-spanless occurrence is the same instance.
        var stripped = Assert.Single(view.Output.Take(1));
        Assert.Null(stripped.Span);
        Assert.Equal(sample, stripped);
        Assert.Same(sample, view.Output[1]);
        Assert.Same(root.Declaration, view.Declaration);
    }

    [Fact]
    public void ImportView_ClearsEveryLocationBearingField_AndPreservesSharingAndIdentity()
    {
        var span = new SourceSpan(9, 9, 9, 10);
        var sharedLeaf = new Expr.Resolve("shared") { Span = span };
        var dot = new Expr.DotCall(sharedLeaf, "m", [sharedLeaf]) { Span = span, MemberSpan = span, LexicalFallback = new Expr.Resolve("m") { Span = span } };
        var spread = new Expr.SequenceSpread(dot) { Span = span, SpreadMarkerSpan = span };
        var capture = new CaptureParameterPattern("c", span, ParameterKind.Collecting) { CollectMarkerSpan = span };
        var nested = new Algorithm.User(null, [new SequenceValueParameterPattern([capture])], [], [], [spread])
        {
            HasExplicitParameterList = true,
        };
        var bind = new Pattern.Bind("b") { NameSpan = span, CollectMarkerSpan = span };
        var family = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.SequenceValue([bind, new Pattern.LitInt(1)]), nested)]);
        var root = new Algorithm.User(
            null,
            [],
            [sharedLeaf],
            [new Property("P", family, IsPublic: true) { DeclarationSpans = [span, span] }, new Property("Q", nested) { DeclarationSpans = [span] }],
            [sharedLeaf, spread]);

        var view = InvokeToImportView(root);

        LocationlessAssertion.AssertLocationless(view);
        // Sharing: the leaf referenced from the open list and both output rows is one node in
        // the view; the nested algorithm held by the family branch and by Q is one node too.
        var viewLeaf = Assert.Single(view.Opens);
        Assert.Same(viewLeaf, view.Output[0]);
        var viewSpread = Assert.IsType<Expr.SequenceSpread>(view.Output[1]);
        var viewDot = Assert.IsType<Expr.DotCall>(viewSpread.Operand);
        Assert.Same(viewLeaf, viewDot.Target);
        Assert.Same(viewLeaf, Assert.Single(viewDot.Args!));
        var viewFamily = Assert.IsType<Algorithm.Conditional>(view.Properties[0].Value);
        Assert.Same(viewFamily.Branches[0].Body, view.Properties[1].Value);
        // Identity and non-location payload survive the copy.
        Assert.Same(family.Declaration, viewFamily.Declaration);
        Assert.Same(nested.Declaration, view.Properties[1].Value.Declaration);
        Assert.True(view.Properties[0].IsPublic);
        var viewNested = Assert.IsType<Algorithm.User>(view.Properties[1].Value);
        Assert.True(viewNested.HasExplicitParameterList);
        var viewCapture = Assert.IsType<CaptureParameterPattern>(Assert.Single(Assert.IsType<SequenceValueParameterPattern>(Assert.Single(viewNested.ParameterPatterns)).Items));
        Assert.Equal(ParameterKind.Collecting, viewCapture.Kind);
        Assert.Equal("c", viewCapture.Name);
        var viewBind = Assert.IsType<Pattern.Bind>(Assert.IsType<Pattern.SequenceValue>(viewFamily.Branches[0].Pattern).Items[0]);
        Assert.Equal("b", viewBind.Name);
        Assert.Equal("m", Assert.IsType<Expr.Resolve>(viewDot.LexicalFallback).Name);
    }

    [Fact]
    public void ImportView_IsTheIdentityOnALocationlessTree()
    {
        var leaf = new Expr.Num(1);
        var root = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [new Property("P", new Algorithm.User(null, [], [], [], [leaf]))], [leaf]);
        Assert.Same(root, InvokeToImportView(root));
    }

    private static Algorithm.User InvokeToImportView(Algorithm.User root)
        => (Algorithm.User)typeof(ModuleLoader)
            .GetMethod("ToImportView", System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Static)!
            .Invoke(null, [root])!;

    // ── 9. Local diagnostics keep their positions exactly ───────────────────

    [Theory]
    [InlineData("A = (1, 2\nA", DiagnosticCode.UnexpectedToken, 2, 2, 2, 2)]
    [InlineData("F(a) = a + zz\nF(1)", DiagnosticCode.UndeclaredIdentifier, 1, 12, 1, 14)]
    [InlineData("F(a) = { a = 3\n a }\nF(1)", DiagnosticCode.ParameterPropertyCollision, 1, 10, 1, 11)]
    [InlineData("open count\n1", DiagnosticCode.IllegalInOpen, 1, 6, 1, 11)]
    [InlineData("K(p) = ~p\nK(1)", DiagnosticCode.InvalidGraceMarker, 1, 8, 1, 10)]
    public void LocalFrontEndDiagnostics_KeepTheirExactPositions(string source, DiagnosticCode code, int line, int column, int endLine, int endColumn)
    {
        var parsed = Parser.Parse(source);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(code, diagnostic.Code);
        Assert.Equal(new SourceSpan(line, column, endLine, endColumn), diagnostic.Span);
    }

    [Fact]
    public void LocalCollision_StillNamesTheLocalParameterPosition()
    {
        var diagnostic = Assert.Single(Parser.Parse("F(a) = { a = 3\n a }\nF(1)").Diagnostics);
        Assert.Contains("The parameter is declared at line 1, column 3.", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("10 / 0", KatLangErrorCode.DivisionByZero, 1, 1, 1, 7)]
    [InlineData("\nBoom = 10 / 0\nBoom", KatLangErrorCode.DivisionByZero, 2, 8, 2, 14)]
    [InlineData("Fine = Math.Ceiling(2.1)\nFine", KatLangErrorCode.ArityMismatch, 2, 1, 2, 5)]
    [InlineData("Lib = { public Double(x) = x * 2 }\nLib.Dubel(4)", KatLangErrorCode.UnresolvedImplicitParams, 2, 5, 2, 10)]
    [InlineData("F(a, b) = a + b\nF(1)", KatLangErrorCode.ArityMismatch, 2, 1, 2, 5)]
    public void LocalEvaluationErrors_KeepTheirExactPositions(string source, KatLangErrorCode code, int line, int column, int endLine, int endColumn)
    {
        var error = SingleEvalError(KatLangEngine.Run(source));
        Assert.Equal(code, error.Code);
        AssertSpan(error, line, column, endLine, endColumn);
    }

    // ── 10. The error attachment law ────────────────────────────────────────

    [Fact]
    public void ErrorAttachment_KeepsAnInnerSpan_AttachesAnOuterOneOnlyWhenMissing_AndStaysAbsentOtherwise()
    {
        var inner = new SourceSpan(3, 3, 3, 9);
        var outer = new SourceSpan(1, 1, 1, 13);
        var positioned = new EvalError.DivByZero { Span = inner };
        var unpositioned = new EvalError.DivByZero();

        Assert.Equal(inner, Evaluator.WithSpan(outer, EvalResult<Result>.Err(positioned)).Error.Span);
        Assert.Equal(outer, Evaluator.WithSpan(outer, EvalResult<Result>.Err(unpositioned)).Error.Span);
        Assert.Null(Evaluator.WithSpan(null, EvalResult<Result>.Err(unpositioned)).Error.Span);
        Assert.Equal(inner, Evaluator.WithSpan(null, EvalResult<Result>.Err(positioned)).Error.Span);
        // A value-equal outer span attaches by value, not by any object identity.
        Assert.Equal(new SourceSpan(1, 1, 1, 13), Evaluator.WithSpan(new SourceSpan(1, 1, 1, 13), EvalResult<Result>.Err(unpositioned)).Error.Span);
        Assert.True(Evaluator.WithSpan(outer, EvalResult<Result>.Ok(new Result.Atom(1))).IsOk);
    }

    // ── 11. No reliance on SourceSpan reference identity ────────────────────

    [Fact]
    public void CollisionValidator_ReportsEachDeclarationNode_EvenWhenTwoShareOneSpanObject()
    {
        // Two distinct declarations (in one owner, under a parameter of that name) whose
        // declaration spans are the SAME object: each declaration is one report, so a
        // value-type span (which has no identity) changes nothing here.
        var span = new SourceSpan(2, 1, 2, 2);
        var value = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var owner = new Algorithm.User(
            null,
            [new CaptureParameterPattern("v", new SourceSpan(1, 3, 1, 4))],
            [],
            [new Property("v", value) { DeclarationSpans = [span] }, new Property("v", value with { }) { DeclarationSpans = [span] }],
            [new Expr.Num(0)]);
        var diagnostics = new List<Diagnostic>();
        new ParameterPropertyCollisionValidator(diagnostics).VisitAlgorithm(owner);
        Assert.Equal(2, diagnostics.Count);
        Assert.All(diagnostics, d => Assert.Equal(span, d.Span));
        Assert.All(diagnostics, d => Assert.Equal(DiagnosticCode.ParameterPropertyCollision, d.Code));
    }

    [Fact]
    public void OpenProviderValidator_ReportsEachTargetNode_EvenWhenTwoShareOneSpanObject()
    {
        var span = new SourceSpan(1, 6, 1, 11);
        var root = new Algorithm.User(
            null,
            [],
            [new Expr.Resolve("count") { Span = span }, new Expr.Resolve("sum") { Span = span }],
            [],
            [new Expr.Num(0)]);
        var diagnostics = new List<Diagnostic>();
        OpenProviderValidator.Validate(root, diagnostics, hostOperations: null);
        Assert.Equal(2, diagnostics.Count);
        Assert.All(diagnostics, d => Assert.Equal(DiagnosticCode.IllegalInOpen, d.Code));
        Assert.All(diagnostics, d => Assert.Equal(span, d.Span));
    }

    [Fact]
    public void NoProductionCodeKeysSourceSpansByReferenceIdentity()
    {
        var sources = Directory.EnumerateFiles(
            Path.Combine(RepositoryRoot(), "src", "KatLang"), "*.cs", SearchOption.AllDirectories)
            .Where(path => !path.Contains($"{Path.DirectorySeparatorChar}obj{Path.DirectorySeparatorChar}", StringComparison.Ordinal)
                && !path.Contains($"{Path.DirectorySeparatorChar}bin{Path.DirectorySeparatorChar}", StringComparison.Ordinal));
        var offenders = new List<string>();
        foreach (var path in sources)
        {
            var text = File.ReadAllText(path);
            if (text.Contains("HashSet<SourceSpan>", StringComparison.Ordinal)
                || text.Contains("Dictionary<SourceSpan", StringComparison.Ordinal)
                || System.Text.RegularExpressions.Regex.IsMatch(text, @"ReferenceEquals\([^)]*[sS]pan\b"))
            {
                offenders.Add(Path.GetFileName(path));
            }
        }

        Assert.Empty(offenders);
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext withContext)
            error = withContext.Inner;
        return error;
    }

    private static string RepositoryRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "KatLang.slnx")))
            directory = directory.Parent;
        return directory?.FullName ?? throw new InvalidOperationException("Repository root not found.");
    }

    // ── 12. Module-local parse outcomes are caller-local load failures ──────

    [Fact]
    public async Task ModuleParseError_IsOneLoadFailureAtTheLoadSite_NeverTheModulesOwnDiagnostic()
    {
        // The module's parse error is on ITS line 6; the loading document sees exactly one
        // diagnostic, at its load site.
        var parsed = await Parser.ParseAsync(
            "M = load('" + Lib + "')\nM",
            Options((Lib, "\n\n\n\n\nX = (1, 2\nX")));
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidLoadedSource, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 5, 1, 40), diagnostic.Span);
    }

    // ── 13. The semantic model over an import view ──────────────────────────

    [Fact]
    public async Task SemanticModel_ImportedNodesAreLocationless_AndTheLocalSiteIsUntouched()
    {
        var parsed = await Parser.ParseAsync(
            "open '" + Lib + "'\nFine",
            Options((Lib, "public Fine = 7\nFine")));
        Assert.False(parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);
        var reference = Assert.Single(model.IdentifierResolutions);
        Assert.Equal(new SourceSpan(2, 1, 2, 5), reference.Occurrence.Span);
        Assert.Null(reference.ResolvedDeclaration);
        var target = Assert.IsType<PropertyInfo>(reference.ResolvedProperty);
        Assert.Equal("Fine", target.Name);
        Assert.Null(target.Declaration);
        Assert.Empty(model.Declarations);
    }
}

/// <summary>Asserts that a subtree carries no source location in any location-bearing field.</summary>
internal sealed class LocationlessAssertion : AstWalker
{
    private readonly List<string> _found = [];

    private LocationlessAssertion()
    {
    }

    public static void AssertLocationless(Algorithm algorithm)
    {
        var walker = new LocationlessAssertion();
        walker.VisitAlgorithm(algorithm);
        Assert.True(walker._found.Count == 0, "Source locations found inside an import view: " + string.Join("; ", walker._found));
    }

    private void Note(string what, SourceSpan? span)
    {
        if (span is not null)
            _found.Add($"{what} {span}");
    }

    protected override void VisitUserAlgorithm(Algorithm.User algorithm)
    {
        foreach (var pattern in algorithm.ParameterPatterns)
            VisitParameterPattern(pattern);
        base.VisitUserAlgorithm(algorithm);
    }

    private void VisitParameterPattern(ParameterPattern pattern)
    {
        switch (pattern)
        {
            case CaptureParameterPattern capture:
                Note($"parameter {capture.Name}", capture.Span);
                Note($"collect marker of {capture.Name}", capture.CollectMarkerSpan);
                break;
            case SequenceValueParameterPattern sequence:
                foreach (var item in sequence.Items)
                    VisitParameterPattern(item);
                break;
        }
    }

    protected override void VisitProperty(Property property)
    {
        foreach (var span in property.DeclarationSpans)
            Note($"property {property.Name}", span);
        VisitAlgorithm(property.Value);
    }

    public override void VisitPattern(Pattern pattern)
    {
        if (pattern is Pattern.Bind bind)
        {
            Note($"binder {bind.Name}", bind.NameSpan);
            Note($"collect marker of binder {bind.Name}", bind.CollectMarkerSpan);
        }

        base.VisitPattern(pattern);
    }

    // The stored lexical-fallback identity is a real child that the base walker treats as a
    // name occurrence rather than an expression; its span is checked like every other.
    protected override void VisitDotCallLexicalFallback(Expr.DotCall expr, Expr lexicalFallback)
        => VisitExpr(lexicalFallback);

    public override void VisitExpr(Expr expr)
    {
        Note(expr.GetType().Name, expr.Span);
        switch (expr)
        {
            case Expr.DotCall dotCall:
                Note($"member {dotCall.Name}", dotCall.MemberSpan);
                break;
            case Expr.SequenceSpread spread:
                Note("spread marker", spread.SpreadMarkerSpan);
                break;
        }

        base.VisitExpr(expr);
    }
}
