using KatLang.ParserFuzz;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// A MISSING MODULE IS AN ANALYSIS STATE (September 2026). A <c>load</c> directive whose module
/// is not elaborated — UNAVAILABLE because the parse had no downloader, or REFUSED by module
/// elaboration (a failed fetch, a refused target, a cycle, a budget limit, invalid module
/// source) — is reported once at its site and kept in the published tree AS WRITTEN; the
/// program around it is elaborated PROVISIONALLY (<c>FrontEndPipeline.FinalizeElaboration</c>:
/// the same passes, their diagnostics withheld), so <see cref="ParseResult.Root"/> is always an
/// elaborated tree and <see cref="SemanticModelBuilder.Build(ParseResult)"/> models it with no
/// module I/O, no invented module member, names a missing module could supply classified
/// <see cref="IdentifierClassification.DeferredModuleReference"/>, and every unaffected part
/// modeled exactly as usual.
/// <para>Before this contract the no-downloader pipeline published the RAW syntax root and
/// <c>Build</c> threw <see cref="InvalidOperationException"/> ("requires module-elaborated
/// AST"), which editor hosts had to catch, while a FAILED load was replaced by a <c>Num(0)</c>
/// stand-in that made every name the module would supply read as undeclared (a cascading
/// <c>UndeclaredIdentifier</c> error and <c>Unresolved</c> classifications). C# front end and
/// editor tooling only: Lean models neither source loading nor the editor, and its
/// post-elaboration invariant describes a SUCCESSFUL load elaboration, which a result with a
/// missing module never is (it is never evaluated).</para>
/// </summary>
public class MissingModuleAnalysisTests
{
    private const string LibUrl = "https://katlang.org/lib.kat";
    private const string OtherUrl = "https://katlang.org/other.kat";

    /// <summary>
    /// The canonical document: a root <c>open</c> of one module, a property load of another in
    /// the middle, and declarations before and after it. Directive spans: <c>[1:6, 1:35)</c> and
    /// <c>[4:7, 4:44)</c>.
    /// </summary>
    private const string Document =
        "open 'https://katlang.org/lib.kat'\n"
        + "Known = 5\n"
        + "Twice(a) = a * 2\n"
        + "Lib = load('https://katlang.org/other.kat')\n"
        + "Scaled(x) = Twice(x) + Lib.Offset(x) + Imported\n"
        + "Scaled(Known) + Free";

    private static readonly SourceSpan OpenDirective = new(1, 6, 1, 35);
    private static readonly SourceSpan PropertyDirective = new(4, 7, 4, 44);

    /// <summary>Names only the two modules can supply (or the directive itself spells).</summary>
    private static readonly HashSet<string> ModuleDependentNames = new(StringComparer.Ordinal)
    {
        "load", "Imported", "Free", "Offset",
    };

    private static readonly IReadOnlyDictionary<string, string> BothModules = new Dictionary<string, string>
    {
        [LibUrl] = "public Imported = 10\npublic Free = 20",
        [OtherUrl] = "public Offset(v) = v + 1",
    };

    private static RunOptions Downloading(IReadOnlyDictionary<string, string> modules, Action<string>? onFetch = null) => new()
    {
        DownloadCode = (url, _) =>
        {
            onFetch?.Invoke(url);
            return modules.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : throw new InvalidOperationException($"404 {url}");
        },
    };

    private static IdentifierResolution At(SemanticModel model, int line, int column)
        => Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(line, column)));

    /// <summary>A structural fingerprint of one resolution: site, kinds, and target site.</summary>
    private static string Describe(IdentifierResolution resolution)
        => $"{resolution.Occurrence.Name}|{resolution.Occurrence.Span}|{resolution.Occurrence.Kind}|"
            + $"{resolution.Classification}|{resolution.ResolvedDeclaration?.Span.ToString() ?? "-"}|"
            + $"{resolution.ResolvedProperty?.DisplaySignature ?? "-"}";

    private static List<string> Describe(SemanticModel model, Func<IdentifierResolution, bool>? include = null)
        => model.IdentifierResolutions.Where(resolution => include?.Invoke(resolution) ?? true).Select(Describe).ToList();

    private static void AssertExactlyUnavailable(ParseResult parsed, params SourceSpan[] directives)
    {
        Assert.Equal(directives.Length, parsed.Diagnostics.Count);
        for (var index = 0; index < directives.Length; index++)
        {
            var diagnostic = parsed.Diagnostics[index];
            Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, diagnostic.Code);
            Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
            Assert.Equal(LoadElaborationGuard.ModuleElaborationUnavailableDiagnostic, diagnostic.Message);
            Assert.Equal(directives[index], diagnostic.Span);
        }
    }

    public static TheoryData<string> NoDownloaderEntryPoints() => new()
    {
        "Parse", "Parse(options)", "ParseAsync", "ParseAsync(options)",
    };

    private static async Task<ParseResult> ParseWithoutDownloader(string entryPoint, string source) => entryPoint switch
    {
        "Parse" => Parser.Parse(source),
        "Parse(options)" => Parser.Parse(source, new RunOptions()),
        "ParseAsync" => await Parser.ParseAsync(source),
        "ParseAsync(options)" => await Parser.ParseAsync(source, new RunOptions()),
        _ => throw new ArgumentOutOfRangeException(nameof(entryPoint), entryPoint, null),
    };

    // ── 1–3. No downloader: the ordinary result, one diagnostic per directive, a model ───────

    [Theory]
    [MemberData(nameof(NoDownloaderEntryPoints))]
    public async Task WithoutADownloader_EveryEntryPoint_PublishesAnElaboratedRoot_ThatBuildModels(string entryPoint)
    {
        var parsed = await ParseWithoutDownloader(entryPoint, Document);

        // One LoadElaborationUnavailable per directive, in document order, and NOTHING else: the
        // provisional elaboration's own diagnostics are withheld.
        AssertExactlyUnavailable(parsed, OpenDirective, PropertyDirective);

        // The root is the ELABORATED tree, never raw syntax: parameter detection inferred the
        // root's free name, which raw syntax never carries, and the directives stay in place.
        Assert.Equal(["Free"], parsed.Root.Params);
        Assert.Empty(SourceProvenance.ParseSyntaxValidRoot(Document).Params);
        Assert.True(LoadElaborationGuard.TryFindFirstUnresolvedLoad(parsed.Root, out var firstDirective));
        Assert.Equal(OpenDirective, firstDirective);

        // Both public Build overloads model it; they agree, and nothing throws.
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Equal(Describe(model), Describe(SemanticModelBuilder.Build(parsed.Root)));
        Assert.NotEmpty(model.IdentifierResolutions);
    }

    [Fact]
    public async Task AResultWithAMissingModule_IsNeverEvaluated()
    {
        var parsed = Parser.Parse(Document);

        foreach (var result in new[] { KatLangEngine.Run(Document), await KatLangEngine.RunAsync(Document) })
        {
            var failure = Assert.IsType<RunResult.ParseFailure>(result);
            Assert.Equal(2, failure.Errors.Count);
            Assert.All(failure.Errors, error => Assert.Equal(KatLangErrorCode.LoadElaborationUnavailable, error.Code));
        }

        // The provisional root is a well-formed AST: evaluated directly (which discards the source
        // gate), it fails as an ordinary evaluation instead of crashing the host.
        Assert.True(Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root)).IsError);
    }

    // ── 4–6. Queries around the directive, unrelated declarations, visibility ──────────────

    [Fact]
    public void NamesAMissingModuleCouldSupply_AreIndeterminate_EverythingElseKeepsItsMeaning()
    {
        var model = SemanticModelBuilder.Build(Parser.Parse(Document));

        // Module-dependent names: indeterminate, locationless, never invented as declarations.
        foreach (var name in new[] { "Imported", "Free", "Offset" })
        {
            var resolution = Assert.Single(model.FindResolutions(name));
            Assert.Equal(IdentifierClassification.DeferredModuleReference, resolution.Classification);
            Assert.Null(resolution.ResolvedDeclaration);
            Assert.Null(resolution.ResolvedProperty);
            Assert.Empty(model.FindDeclarations(name));
        }

        // The directive's own name is the front-end `load` prelude entry.
        Assert.Equal(IdentifierClassification.Builtin, At(model, 4, 7).Classification);

        // Unrelated declarations and references — before and after the directive.
        Assert.Equal(IdentifierClassification.PropertyDefinition, At(model, 2, 1).Classification);
        Assert.Equal(IdentifierClassification.ExplicitParameterDefinition, At(model, 3, 7).Classification);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, At(model, 3, 12).Classification);
        Assert.Equal(IdentifierClassification.PropertyDefinition, At(model, 4, 1).Classification);
        var twice = At(model, 5, 13);
        Assert.Equal(IdentifierClassification.PropertyReference, twice.Classification);
        Assert.Equal(new SourceSpan(3, 1, 3, 6), twice.ResolvedDeclaration?.Span);
        var lib = At(model, 5, 24);
        Assert.Equal(IdentifierClassification.PropertyReference, lib.Classification);
        Assert.Equal(new SourceSpan(4, 1, 4, 4), lib.ResolvedDeclaration?.Span);
        var known = At(model, 6, 8);
        Assert.Equal(IdentifierClassification.PropertyReference, known.Classification);
        Assert.Equal(new SourceSpan(2, 1, 2, 6), known.ResolvedDeclaration?.Span);
        Assert.Equal(new SourceSpan(5, 1, 5, 7), At(model, 6, 1).ResolvedDeclaration?.Span);

        // Nothing the document wrote is reported as a hard unresolved name.
        Assert.DoesNotContain(model.IdentifierResolutions, resolution => resolution.Classification == IdentifierClassification.Unresolved);

        // Property metadata before and after the directive.
        Assert.Equal("Twice(a)", Assert.IsType<PropertyInfo>(model.FindPropertyAt(new SourcePosition(3, 1))).DisplaySignature);
        Assert.Equal("Scaled(x)", Assert.IsType<PropertyInfo>(model.FindPropertyAt(new SourcePosition(5, 1))).DisplaySignature);
        Assert.Equal("Lib", Assert.IsType<PropertyInfo>(model.FindPropertyAt(new SourcePosition(4, 1))).DisplaySignature);
    }

    [Fact]
    public void Completion_OffersTheDocumentsNames_AndMarksModuleDependentOnesIndeterminate()
    {
        var model = SemanticModelBuilder.Build(Parser.Parse(Document));

        // Inside Scaled's body, after the directive.
        var visible = model.GetVisibleSymbolsAt(new SourcePosition(5, 20)).ToDictionary(symbol => symbol.Name, StringComparer.Ordinal);
        foreach (var name in new[] { "Known", "Twice", "Lib", "Scaled" })
        {
            Assert.Equal(IdentifierClassification.PropertyReference, visible[name].Classification);
            Assert.NotNull(visible[name].Declaration);
        }

        Assert.Equal(IdentifierClassification.ExplicitParameterReference, visible["x"].Classification);
        // The root's provisionally inferred parameter sits under the root's missing-module open.
        Assert.Equal(IdentifierClassification.DeferredModuleReference, visible["Free"].Classification);
        // Prelude names stay offered, and the missing module invents no member.
        Assert.Equal(IdentifierClassification.Builtin, visible["count"].Classification);
        Assert.False(visible.ContainsKey("Imported"));
        Assert.False(visible.ContainsKey("Offset"));

        // The scope query answers on both sides of the directive.
        Assert.NotNull(model.FindScopeAt(new SourcePosition(2, 1)));
        Assert.NotNull(model.FindScopeAt(new SourcePosition(6, 1)));
    }

    [Fact]
    public void AGenuineTypo_StaysUnresolved_WhenNoMissingModuleCouldSupplyIt()
    {
        // No `open` of the missing module reaches `Typo`, and it is not a member of the
        // placeholder, so the model keeps the ordinary verdict; `X` IS a member of the
        // missing module and stays indeterminate.
        const string source = "Lib = load('https://katlang.org/lib.kat')\nF(a) = a + Typo\nF(1) + Lib.X";
        var model = SemanticModelBuilder.Build(Parser.Parse(source));

        Assert.Equal(IdentifierClassification.Unresolved, Assert.Single(model.FindResolutions("Typo")).Classification);
        Assert.Equal(IdentifierClassification.DeferredModuleReference, Assert.Single(model.FindResolutions("X")).Classification);
    }

    [Fact]
    public async Task UnaffectedParts_AreModeledExactlyAsWithTheModulesLoaded()
    {
        // Metamorphic: the same document without a downloader and with one that supplies both
        // modules. Every site that does not depend on a module resolves identically — name, span,
        // kind, classification, declaration site, and property signature.
        var missing = SemanticModelBuilder.Build(Parser.Parse(Document));
        var loadedParse = await Parser.ParseAsync(Document, Downloading(BothModules));
        Assert.Empty(loadedParse.Diagnostics);
        var loaded = SemanticModelBuilder.Build(loadedParse);

        bool Unaffected(IdentifierResolution resolution) => !ModuleDependentNames.Contains(resolution.Occurrence.Name);
        Assert.Equal(Describe(loaded, Unaffected), Describe(missing, Unaffected));
        Assert.Equal(
            loaded.Declarations.Select(declaration => $"{declaration.Name}|{declaration.Span}|{declaration.Kind}"),
            missing.Declarations.Select(declaration => $"{declaration.Name}|{declaration.Span}|{declaration.Kind}"));
        Assert.Equal(
            loaded.PropertyInfos.Where(property => property.Declaration is not null).Select(property => property.DisplaySignature),
            missing.PropertyInfos.Where(property => property.Declaration is not null).Select(property => property.DisplaySignature));
    }

    [Fact]
    public void TheProvisionalElaboration_WithholdsItsPassDiagnostics_ButTheModelStaysPrecise()
    {
        // `b` is undeclared in a closed list: the same program WITHOUT a load reports it, while a
        // program with a missing module withholds every pass diagnostic (any of them could depend
        // on the module). The model still knows `b` resolves nowhere.
        const string body = "F(a) = a + b\nF(1)";
        var complete = Parser.Parse(body);
        Assert.Contains(complete.Diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.UndeclaredIdentifier);

        var provisional = Parser.Parse("Lib = load('https://katlang.org/lib.kat')\n" + body);
        AssertExactlyUnavailable(provisional, new SourceSpan(1, 7, 1, 42));

        Assert.Equal(IdentifierClassification.Unresolved, Assert.Single(SemanticModelBuilder.Build(complete).FindResolutions("b")).Classification);
        Assert.Equal(IdentifierClassification.Unresolved, Assert.Single(SemanticModelBuilder.Build(provisional).FindResolutions("b")).Classification);
    }

    // ── 7. Malformed load directives ──────────────────────────────────────────────────────

    public static TheoryData<string, int, DiagnosticCode, string?> MalformedLoads() => new()
    {
        // source, directives written, the code module elaboration reports, a name the model resolves
        { "X = load()\nX", 1, DiagnosticCode.InvalidLoadDirective, "X" },
        { "X = load('https://katlang.org/a.kat', 'https://katlang.org/b.kat')\nX", 1, DiagnosticCode.InvalidLoadDirective, "X" },
        { "Url = 'https://katlang.org/lib.kat'\nX = load(Url)\nX", 1, DiagnosticCode.InvalidLoadDirective, "Url" },
        { "1 + load('https://katlang.org/lib.kat')", 1, DiagnosticCode.InvalidLoadDirective, null },
        // The loader refuses the OUTER directive; the inner one is part of the refused construct.
        { "X = load(load('https://katlang.org/lib.kat'))\nX", 2, DiagnosticCode.InvalidLoadDirective, "X" },
        { "open 'http://katlang.org/insecure.kat'\n1", 1, DiagnosticCode.InvalidLoadUrl, null },
        { "open 'https://evil.example/x.kat'\n1", 1, DiagnosticCode.InvalidLoadUrl, null },
    };

    [Theory]
    [MemberData(nameof(MalformedLoads))]
    public async Task MalformedLoads_AreReportedAndModeled_WithAndWithoutADownloader(
        string source, int directives, DiagnosticCode refusal, string? resolvedName)
    {
        // Without a downloader every written directive is one unavailable site.
        var unavailable = Parser.Parse(source);
        Assert.Equal(directives, unavailable.Diagnostics.Count);
        Assert.All(unavailable.Diagnostics, diagnostic => Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, diagnostic.Code));
        AssertModeled(unavailable);

        // With one, module elaboration refuses the directive before any fetch, keeps it as
        // written, and reports exactly one refusal: no stand-in value, no internal error.
        var fetches = 0;
        var refused = await Parser.ParseAsync(source, Downloading(BothModules, _ => fetches++));
        Assert.Equal(0, fetches);
        Assert.Equal(refusal, Assert.Single(refused.Diagnostics).Code);
        Assert.True(LoadElaborationGuard.TryFindFirstUnresolvedLoad(refused.Root, out _));
        AssertModeled(refused);
        Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, Downloading(BothModules)));

        void AssertModeled(ParseResult parsed)
        {
            var model = SemanticModelBuilder.Build(parsed);
            if (resolvedName is not null)
                Assert.Contains(model.FindResolutions(resolvedName), resolution => resolution.Classification == IdentifierClassification.PropertyReference);
            Assert.All(model.FindResolutions("load"), resolution => Assert.Equal(IdentifierClassification.Builtin, resolution.Classification));
        }
    }

    // ── 8–9. With a downloader: success, and a failure that is a missing module ─────────────

    [Fact]
    public async Task DownloaderSuccess_ModelsTheLoadedModules_WithLocationlessTargets()
    {
        var parsed = await Parser.ParseAsync(Document, Downloading(BothModules));
        Assert.Empty(parsed.Diagnostics);
        Assert.False(LoadElaborationGuard.TryFindFirstUnresolvedLoad(parsed.Root, out _));
        Assert.Empty(parsed.Root.Params);

        var model = SemanticModelBuilder.Build(parsed);
        foreach (var name in new[] { "Imported", "Free", "Offset" })
        {
            var resolution = Assert.Single(model.FindResolutions(name));
            Assert.Equal(IdentifierClassification.PropertyReference, resolution.Classification);
            Assert.Null(resolution.ResolvedDeclaration);
            Assert.NotNull(resolution.ResolvedProperty);
        }

        Assert.DoesNotContain(model.IdentifierResolutions, resolution => resolution.Classification
            is IdentifierClassification.DeferredModuleReference or IdentifierClassification.Unresolved);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DownloaderFailure_IsAMissingModule_NotAStandInValue(bool invalidSource)
    {
        // lib.kat fails — its fetch throws, or it returns source that does not parse — while
        // other.kat loads. The failure is the ONE diagnostic: no cascade for the names the
        // missing module would supply (the former Num(0) stand-in reported `Imported` as an
        // undeclared identifier and classified it Unresolved) and no internal error for the
        // directive the loader deliberately kept.
        var modules = invalidSource
            ? new Dictionary<string, string>(BothModules) { [LibUrl] = "public Imported = (" }
            : new Dictionary<string, string> { [OtherUrl] = BothModules[OtherUrl] };
        var options = Downloading(modules);
        var parsed = await Parser.ParseAsync(Document, options);

        var failure = Assert.Single(parsed.Diagnostics);
        Assert.Equal(invalidSource ? DiagnosticCode.InvalidLoadedSource : DiagnosticCode.LoadFetchFailed, failure.Code);
        Assert.Equal(OpenDirective, failure.Span);
        Assert.True(LoadElaborationGuard.TryFindFirstUnresolvedLoad(parsed.Root, out var kept));
        Assert.Equal(OpenDirective, kept);

        var model = SemanticModelBuilder.Build(parsed);
        foreach (var name in new[] { "Imported", "Free" })
            Assert.Equal(IdentifierClassification.DeferredModuleReference, Assert.Single(model.FindResolutions(name)).Classification);
        // The module that DID load is modeled as loaded.
        Assert.Equal(IdentifierClassification.PropertyReference, Assert.Single(model.FindResolutions("Offset")).Classification);
        Assert.DoesNotContain(model.IdentifierResolutions, resolution => resolution.Classification == IdentifierClassification.Unresolved);

        var run = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(Document, options));
        Assert.Equal(invalidSource ? KatLangErrorCode.InvalidLoadedSource : KatLangErrorCode.LoadFetchFailed, Assert.Single(run.Errors).Code);
    }

    [Fact]
    public async Task ACycle_IsAMissingModule_Too()
    {
        var modules = new Dictionary<string, string>
        {
            [LibUrl] = $"public Imported = 1\nNext = load('{OtherUrl}')",
            [OtherUrl] = $"public Back = load('{LibUrl}')",
        };
        var parsed = await Parser.ParseAsync(Document, Downloading(modules));

        Assert.Contains(parsed.Diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.LoadCycle);
        Assert.DoesNotContain(parsed.Diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.InternalError);
        Assert.NotNull(SemanticModelBuilder.Build(parsed));
    }

    // ── 10. Multiple and nested directives ────────────────────────────────────────────────

    private const string Nested =
        "open 'https://katlang.org/a.kat', 'https://katlang.org/b.kat'\n"
        + "Outer = {\n"
        + "  open 'https://katlang.org/c.kat'\n"
        + "  Lib = load('https://katlang.org/d.kat')\n"
        + "  Lib.FromD + FromC\n"
        + "}\n"
        + "F(0) = { open 'https://katlang.org/e.kat'\n"
        + "  FromE }\n"
        + "F(n) = FromA + n\n"
        + "Outer + F(0) + FromB";

    [Fact]
    public async Task MultipleAndNestedDirectives_AreEachReported_AndEveryDependentNameIsIndeterminate()
    {
        var unavailable = Parser.Parse(Nested);
        AssertExactlyUnavailable(
            unavailable,
            new SourceSpan(1, 6, 1, 33),
            new SourceSpan(1, 35, 1, 62),
            new SourceSpan(3, 8, 3, 35),
            new SourceSpan(4, 9, 4, 42),
            new SourceSpan(7, 15, 7, 42));
        AssertIndeterminate(SemanticModelBuilder.Build(unavailable));

        // A failing downloader: the four EAGER directives fail at parse time; the branch-owned one
        // is a deferred region, fetched only if evaluation selects its branch.
        var fetched = new List<string>();
        var failing = await Parser.ParseAsync(Nested, Downloading(new Dictionary<string, string>(), fetched.Add));
        Assert.Equal(4, failing.Diagnostics.Count);
        Assert.All(failing.Diagnostics, diagnostic => Assert.Equal(DiagnosticCode.LoadFetchFailed, diagnostic.Code));
        Assert.DoesNotContain("https://katlang.org/e.kat", fetched);
        AssertIndeterminate(SemanticModelBuilder.Build(failing));

        static void AssertIndeterminate(SemanticModel model)
        {
            foreach (var name in new[] { "FromA", "FromB", "FromC", "FromD", "FromE" })
                Assert.Equal(IdentifierClassification.DeferredModuleReference, Assert.Single(model.FindResolutions(name)).Classification);
            foreach (var name in new[] { "Outer", "Lib", "F" })
                Assert.Contains(model.FindResolutions(name), resolution => resolution.Classification == IdentifierClassification.PropertyReference);
            Assert.DoesNotContain(model.IdentifierResolutions, resolution => resolution.Classification == IdentifierClassification.Unresolved);
        }
    }

    // ── 11. The structural gate still applies, and the root is never raw ──────────────────

    [Fact]
    public void ADeepProgramWithADirective_GetsTheElaborationGateDiagnostic_AndAnEmptyElaboratedRoot()
    {
        // Depth 640 parses as raw syntax but exceeds the elaboration ceiling (300). The raw tree
        // used to be published as the root, so Build threw ArgumentException for a parser result;
        // the provisional elaboration applies the one elaboration gate like every other parse.
        var source = $"Lib = load('{LibUrl}')\n" + AstStructuralDepthTests.BracketChainComposition(levels: 22, chainOps: 28);
        var parsed = Parser.Parse(source);

        Assert.Equal(
            [DiagnosticCode.LoadElaborationUnavailable, DiagnosticCode.AstDepthLimitExceeded],
            parsed.Diagnostics.Select(diagnostic => diagnostic.Code));
        Assert.Empty(parsed.Root.Properties);
        Assert.Empty(parsed.Root.Output);
        Assert.Empty(SemanticModelBuilder.Build(parsed).IdentifierResolutions);
    }

    // ── 12. Repeated builds of one result ─────────────────────────────────────────────────

    [Fact]
    public async Task RepeatedAndConcurrentBuilds_AreIdentical_AndLeaveTheResultUntouched()
    {
        var parsed = Parser.Parse(Document);
        var root = parsed.Root;
        var diagnostics = parsed.Diagnostics.ToList();
        var tree = FrontEndFingerprint.ComputeParseResult(root, []);

        var first = Describe(SemanticModelBuilder.Build(parsed));
        Assert.Equal(first, Describe(SemanticModelBuilder.Build(parsed)));
        var concurrent = await Task.WhenAll(Enumerable.Range(0, 4).Select(_ => Task.Run(() => Describe(SemanticModelBuilder.Build(parsed)))));
        Assert.All(concurrent, model => Assert.Equal(first, model));

        Assert.Same(root, parsed.Root);
        Assert.Equal(diagnostics, parsed.Diagnostics);
        Assert.Equal(tree, FrontEndFingerprint.ComputeParseResult(root, []));
    }
}
