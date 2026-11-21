using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// An algorithm written inside an open target the front end REJECTS (adversarial performance and reliability
/// investigation, 2026-11-21, baseline <c>8947d21e</c>, finding #3).
/// <para>
/// Every algorithm written in an open target is declared at the PRELUDE: static admission keys it there, and parameter
/// detection, implicit-argument resolution, open-provider validation and the exposure rewrite elaborate it there. Two
/// consumers walked a rejected target in the OPENER's context instead. Dependency analysis
/// (<c>PropertyDependencyGraphBuilder.CollectOpenTargetSeeds</c>) handed a block-headed path inside it to the block-head
/// recognizer, whose completed-body invariant (da209fa0) found no key for the block under the opener and threw
/// "A completed block-head requirement body is unavailable." out of <see cref="Parser.Parse(string)"/>,
/// <see cref="KatLangEngine.Run"/> and <see cref="KatLangEngine.RunAsync"/> for any such target inside a declaration,
/// a clause branch or a load-bearing branch. The semantic model (<c>SemanticModelBuilder.VisitOpenExpression</c>) gave such a
/// block no completed context: its member references stayed unresolved, and a lookup through the block's own
/// <c>open</c> threw "Standalone structural lookup requires explicit source phase/admission provenance." out of
/// <see cref="SemanticModelBuilder.Build(ParseResult)"/>, at the root too. Now the dependency walk treats such an
/// algorithm as charging nothing, and the model visits the whole target in the prelude-rooted region, as it always did
/// for a capture row and an inline block.
/// </para>
/// <para>
/// Distinct from the exceptions a SELECTED load-bearing branch can raise while its deferred unit compiles
/// (<c>DeferredModuleRegion.CompileLoadedBody</c>, where shared blocks and modules are received from the eager program):
/// every shape here threw in the eager front end or in the editor model, before any unit materialized, and involves no
/// shared block or module. Diagnostics, spans, the parser's recovery of the neighboring declarations, valid inline and
/// module opens, and the invariant on admitted rows are unchanged.
/// </para>
/// </summary>
public class RejectedOpenTargetBlockTests
{
    private const string ModuleUrl = "https://mods.test/lib.kat";

    private static RunOptions ModuleOptions() => new()
    {
        AllowedHosts = ["mods.test"],
        DownloadCode = (url, _) => url == ModuleUrl
            ? ValueTask.FromResult("public Sub = { public Q = 9 }")
            : throw new InvalidOperationException($"404: {url}"),
    };

    /// <summary>A run refused the source with exactly the diagnostics the parse reported, in order.</summary>
    private static void AssertRefusedLike(ParseResult parsed, RunResult run)
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(run);
        Assert.Equal(
            parsed.Diagnostics.Select(static d => (d.Code.ToString(), d.Message, d.Span)),
            failure.Errors.Select(static e => (e.Code.ToString(), e.Message, e.Span)));
    }

    /// <summary>The model's site for the member <paramref name="name"/> written after a block, resolved to the block's own declaration.</summary>
    private static void AssertBlockMemberResolves(SemanticModel model, string name, SourceSpan declaration, SourceSpan member,
        OccurrenceKind kind = OccurrenceKind.DotMemberReference)
    {
        var declared = Assert.Single(model.FindDeclarations(name), d => d.Span == declaration);
        var site = Assert.Single(model.IdentifierResolutions, r => r.Occurrence.Span == member);
        Assert.Equal(kind, site.Occurrence.Kind);
        Assert.Equal(kind == OccurrenceKind.OpenTargetMemberReference
            ? IdentifierClassification.OpenTarget
            : IdentifierClassification.PropertyReference, site.Classification);
        Assert.Same(declared, site.ResolvedDeclaration);
    }

    // ── Inside a declaration: every entry point used to throw ──

    [Theory]
    [InlineData("[{ public X = 1 }.X]", "Invalid open form: 'listLiteral' is not allowed in open declarations.", OccurrenceKind.DotMemberReference)]
    [InlineData("({ public X = 1 }.X + 1)", "Invalid open form: 'binary' is not allowed in open declarations.", OccurrenceKind.DotMemberReference)]
    [InlineData("-{ public X = 1 }.X", "Invalid open form: 'unary' is not allowed in open declarations.", OccurrenceKind.DotMemberReference)]
    [InlineData("({ public X = 1 }.X < 2)", "Invalid open form: 'comparison' is not allowed in open declarations.", OccurrenceKind.DotMemberReference)]
    [InlineData("({ public X = 1, 2 }.X[0])", "Invalid open form: 'index' is not allowed in open declarations.", OccurrenceKind.DotMemberReference)]
    [InlineData("F({ public X = 1 }.X)", "Invalid open form: 'call' is not allowed in open declarations.", OccurrenceKind.DotMemberReference)]
    [InlineData("({ public X = 1 }.X, 2)", Parser.CapturedOpenTargetDiagnostic, OccurrenceKind.DotMemberReference)]
    [InlineData("{ public X = 1 }.X*", "Invalid open form: 'spread' is not allowed in open declarations.", OccurrenceKind.OpenTargetMemberReference)]
    public async Task RejectedTargetHoldingABlockPath_InADeclaration_IsReportedOnEveryEntryPoint(string target, string message,
        OccurrenceKind memberKind)
    {
        var source = $"A = {{\n    open {target}\n    1\n}}\nF(x) = x\nA";

        var parsed = Parser.Parse(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.BadOpenForm, diagnostic.Code);
        Assert.Equal(message, diagnostic.Message);
        Assert.Equal(new SourceSpan(2, 10, 2, 10 + target.Length), diagnostic.Span);
        // The parser's recovery keeps the declarations after the refused target.
        Assert.Equal(["A", "F"], parsed.Root.Properties.Select(static p => p.Name));

        AssertRefusedLike(parsed, KatLangEngine.Run(source));
        AssertRefusedLike(parsed, await KatLangEngine.RunAsync(source));

        var model = SemanticModelBuilder.Build(parsed);
        var declaration = 10 + target.IndexOf("X =", StringComparison.Ordinal);
        var member = 10 + target.IndexOf("}.X", StringComparison.Ordinal) + 2;
        AssertBlockMemberResolves(model, "X", new SourceSpan(2, declaration, 2, declaration + 1),
            new SourceSpan(2, member, 2, member + 1), memberKind);
        var reference = Assert.Single(model.IdentifierResolutions, r => r.Occurrence.Span == new SourceSpan(6, 1, 6, 2));
        Assert.Same(Assert.Single(model.FindDeclarations("A")), reference.ResolvedDeclaration);
    }

    [Fact]
    public async Task RejectedTargetHoldingABlockPath_InAClauseBranch_IsReportedOnEveryEntryPoint()
    {
        const string source = "F(0) = {\n    open [{ public X = 1 }.X]\n    1\n}\nF(n) = n\nF(0)";

        var parsed = Parser.Parse(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.BadOpenForm, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 10, 2, 30), diagnostic.Span);
        AssertRefusedLike(parsed, KatLangEngine.Run(source));
        AssertRefusedLike(parsed, await KatLangEngine.RunAsync(source));
        AssertBlockMemberResolves(SemanticModelBuilder.Build(parsed), "X", new SourceSpan(2, 20, 2, 21), new SourceSpan(2, 28, 2, 29));
    }

    // ── At the root: the model used to throw for a block with its own open ──

    [Theory]
    // The block's own `open L` is validated in the block's prelude-rooted region, where the root's `L` is not visible.
    [InlineData("[{ open L\n    public X = 1 }.X]", "Invalid open form: 'listLiteral' is not allowed in open declarations.", 22)]
    [InlineData("({ open L\n    public X = 1 }.X + 1)", "Invalid open form: 'binary' is not allowed in open declarations.", 26)]
    // The capture row was already modeled in that region: the control.
    [InlineData("({ open L\n    public X = 1 }.X, 2)", Parser.CapturedOpenTargetDiagnostic, 25)]
    public async Task RejectedTargetHoldingABlockWithItsOwnOpen_AtTheRoot_IsModeledAtThePrelude(string target, string message, int endColumn)
    {
        var source = $"open {target}\nL = {{ public Y = 2 }}\n1";

        var parsed = Parser.Parse(source);
        Assert.Collection(parsed.Diagnostics,
            badForm =>
            {
                Assert.Equal(DiagnosticCode.BadOpenForm, badForm.Code);
                Assert.Equal(message, badForm.Message);
                Assert.Equal(new SourceSpan(1, 6, 2, endColumn), badForm.Span);
            },
            unresolved =>
            {
                Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, unresolved.Code);
                Assert.Equal("'L' cannot be opened because no property named 'L' is visible here; the first name of an open "
                    + "target resolves through the enclosing declarations and the prelude, never through another open.", unresolved.Message);
                Assert.Equal(new SourceSpan(1, 14, 1, 15), unresolved.Span);
            });
        AssertRefusedLike(parsed, KatLangEngine.Run(source));
        AssertRefusedLike(parsed, await KatLangEngine.RunAsync(source));

        var model = SemanticModelBuilder.Build(parsed);
        AssertBlockMemberResolves(model, "X", new SourceSpan(2, 12, 2, 13), new SourceSpan(2, 20, 2, 21));
        var head = Assert.Single(model.IdentifierResolutions, r => r.Occurrence.Span == new SourceSpan(1, 14, 1, 15));
        Assert.Equal(OccurrenceKind.OpenTargetReference, head.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, head.Classification);
        Assert.Null(head.ResolvedDeclaration);
    }

    // ── Incomplete editor input ──

    [Theory]
    [InlineData("A = {\n    open [{ public X = 1 }.X\n    1\n}\nA", new[] { "UnexpectedToken", "BadOpenForm" }, 2, 10, 3, 6, 28)]
    [InlineData("A = {\n    open ({ public X = 1 }.X +\n", new[] { "UnexpectedToken", "UnexpectedToken", "BadOpenForm", "UnexpectedToken" }, 2, 10, 2, 31, 28)]
    [InlineData("A = {\n    open [{ public X = 1 }.X.", new[] { "UnexpectedToken", "UnexpectedToken", "BadOpenForm", "UnexpectedToken" }, 2, 10, 2, 30, 28)]
    public async Task IncompleteRejectedTarget_IsDiagnosed_AndModeled(string source, string[] codes,
        int startLine, int startColumn, int endLine, int endColumn, int memberColumn)
    {
        var parsed = Parser.Parse(source);
        Assert.Equal(codes, parsed.Diagnostics.Select(static d => d.Code.ToString()));
        var badForm = Assert.Single(parsed.Diagnostics, static d => d.Code == DiagnosticCode.BadOpenForm);
        Assert.Equal(new SourceSpan(startLine, startColumn, endLine, endColumn), badForm.Span);
        AssertRefusedLike(parsed, KatLangEngine.Run(source));
        AssertRefusedLike(parsed, await KatLangEngine.RunAsync(source));

        AssertBlockMemberResolves(SemanticModelBuilder.Build(parsed), "X", new SourceSpan(2, 20, 2, 21),
            new SourceSpan(2, memberColumn, 2, memberColumn + 1));
    }

    // ── A load directive whose argument holds a block path ──

    [Fact]
    public async Task LoadDirectiveHoldingABlockPath_IsTheLoadDiagnostic_WithOrWithoutADownloader()
    {
        const string source = "A = {\n    open load({ public X = 1 }.X)\n    1\n}\nA";
        var declaration = new SourceSpan(2, 24, 2, 25);
        var member = new SourceSpan(2, 32, 2, 33);

        var unavailable = Parser.Parse(source);
        var diagnostic = Assert.Single(unavailable.Diagnostics);
        Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 10, 2, 34), diagnostic.Span);
        AssertRefusedLike(unavailable, KatLangEngine.Run(source));
        AssertRefusedLike(unavailable, await KatLangEngine.RunAsync(source));
        AssertBlockMemberResolves(SemanticModelBuilder.Build(unavailable), "X", declaration, member);

        var options = ModuleOptions();
        var refused = await Parser.ParseAsync(source, options);
        diagnostic = Assert.Single(refused.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidLoadDirective, diagnostic.Code);
        Assert.Equal("load URL must be a literal (non-dynamic).", diagnostic.Message);
        Assert.Equal(new SourceSpan(2, 10, 2, 34), diagnostic.Span);
        AssertRefusedLike(refused, await KatLangEngine.RunAsync(source, options));
        AssertBlockMemberResolves(SemanticModelBuilder.Build(refused), "X", declaration, member);
    }

    // ── A load-bearing branch: one deferred unit ──

    [Fact]
    public async Task RejectedTargetHoldingABlockPath_InALoadBearingBranch_IsReportedAtParse()
    {
        // The branch also opens a member of a module, so it is a deferred compilation unit; its rejected target is still
        // the document's parse error. Its block, written in the unit's placeholder, used to throw like the eager ones.
        var source = $"F(0) = {{\n    open load('{ModuleUrl}').Sub, [{{ public X = 1 }}.X]\n    Q\n}}\nF(n) = n\nF(3)";
        var options = ModuleOptions();

        var parsed = await Parser.ParseAsync(source, options);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.BadOpenForm, diagnostic.Code);
        Assert.Equal("Invalid open form: 'listLiteral' is not allowed in open declarations.", diagnostic.Message);
        Assert.Equal(new SourceSpan(2, 49, 2, 69), diagnostic.Span);
        AssertRefusedLike(parsed, await KatLangEngine.RunAsync(source, options));
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Single(model.FindDeclarations("X"), d => d.Span == new SourceSpan(2, 59, 2, 60));
    }

    [Fact]
    public async Task LoadDirectiveHoldingABlockPath_InALoadBearingBranch_FailsOnlyWhenSelected()
    {
        // A deferred unit is validated when it is selected; the directive's refusal is then the selection's error.
        const string source = "F(0) = {\n    open load({ public X = 1 }.X)\n    1\n}\nF(n) = n\n";
        var options = ModuleOptions();
        Assert.Empty((await Parser.ParseAsync(source + "F(3)", options)).Diagnostics);
        Assert.Equal("3", Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source + "F(3)", options)).ToDisplayString());

        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source + "F(0)", options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.InvalidLoadDirective, error.Code);
        Assert.Equal(new SourceSpan(2, 10, 2, 34), error.Span);
    }

    // ── The corresponding valid targets are unchanged ──

    [Theory]
    [InlineData("open { public S = { public Q = 3 } }.S\nQ", 1, 15, 38, 28, 2, 1)]
    [InlineData("A = {\n    open { public S = { public Q = 3 } }.S\n    Q\n}\nA", 2, 19, 42, 32, 3, 5)]
    public async Task ValidInlineHeadedTarget_RunsAndResolvesOnEveryEntryPoint(string source, int line, int sColumn,
        int sMemberColumn, int qColumn, int qReferenceLine, int qReferenceColumn)
    {
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        Assert.Equal("3", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
        Assert.Equal("3", Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source)).ToDisplayString());

        var model = SemanticModelBuilder.Build(parsed);
        AssertBlockMemberResolves(model, "S", new SourceSpan(line, sColumn, line, sColumn + 1),
            new SourceSpan(line, sMemberColumn, line, sMemberColumn + 1), OccurrenceKind.OpenTargetMemberReference);
        var q = Assert.Single(model.IdentifierResolutions,
            r => r.Occurrence.Span == new SourceSpan(qReferenceLine, qReferenceColumn, qReferenceLine, qReferenceColumn + 1));
        Assert.Equal(IdentifierClassification.PropertyReference, q.Classification);
        Assert.Same(Assert.Single(model.FindDeclarations("Q"), d => d.Span == new SourceSpan(line, qColumn, line, qColumn + 1)),
            q.ResolvedDeclaration);
    }

    [Fact]
    public async Task ValidModuleOpens_InADeclarationAndInALoadBearingBranch_RunUnchanged()
    {
        var options = ModuleOptions();
        var declaration = $"A = {{\n    open load('{ModuleUrl}').Sub\n    Q\n}}\nA";
        var parsed = await SourceProvenance.ParseValidAsync(declaration, options);
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var imported = Assert.Single(model.IdentifierResolutions, r => r.Occurrence.Name == "Q");
        Assert.Equal(new SourceSpan(3, 5, 3, 6), imported.Occurrence.Span);
        Assert.Equal(IdentifierClassification.PropertyReference, imported.Classification);
        Assert.Null(imported.ResolvedDeclaration);
        Assert.Equal("9", Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(declaration, options)).ToDisplayString());

        var branch = $"F(0) = {{\n    open load('{ModuleUrl}').Sub, {{ public S = {{ public X = 2 }} }}.S\n    Q + X\n}}\nF(n) = n\nF(3), F(0)";
        await SourceProvenance.ParseValidAsync(branch, options);
        Assert.Equal("3\n11", Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(branch, options)).ToDisplayString()
            .ReplaceLineEndings("\n"));
    }

    // ── Exposure: such a block charges nothing; an admitted block row beside it still does ──

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedArgumentBundle_KeepsTheRequirementsOfEachOccurrence(bool ordinaryFirst)
    {
        // The same block and argument bundle occur in a recovery target and in an ordinary call.
        // Two argument bundles within the target also share their expression, exercising a local memo hit.
        var block = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [new Expr.Param("p")]));
        var argument = new Expr.Binary(BinaryOp.Add, block, new Expr.Num(1));
        OutputBundle shared = [argument];
        var callee = new Expr.Resolve("abs");
        var call = new Expr.Call(callee, shared);
        var rejectedTarget = new Expr.ListLiteral([new Expr.Call(callee, [argument]), call]);
        var ordinary = new Property("Ordinary", new Algorithm.User(null, [], [], [], [call]));
        var rejected = new Property("Rejected", new Algorithm.User(null, [], [rejectedTarget], [], []));
        var root = new Algorithm.User(null, [], [], ordinaryFirst ? [ordinary, rejected] : [rejected, ordinary], []);

        var graph = StandaloneSummaries.Build(root);
        Assert.Equal(["p"], graph[ordinaryFirst ? 0 : 1].RequiredAncestorOwnedParameterNames);
        Assert.Empty(graph[ordinaryFirst ? 1 : 0].RequiredAncestorOwnedParameterNames);
    }

    [Fact]
    public void BlockInARejectedTarget_ChargesNothing_WhileAnAdmittedBlockRowBesideItIsStillCharged()
    {
        // The block is declared at the prelude: its `L` is the implicit parameter of its own `X`, never the opener's `L`,
        // so nothing in it requires Outer's `p`.
        var rejected = SourceProvenance.ExpectFrontEndError(
            "Outer(p) = {\n    L = p + 1\n    public Y = {\n        open [{ public X = L }.X]\n        1\n    }\n    1\n}\nOuter.Y");
        Assert.Equal(DiagnosticCode.BadOpenForm, Assert.Single(rejected).Code);
        Assert.Equal(PropertyExposure.Exported, ExposureOfY(
            "Outer(p) = {\n    L = p + 1\n    public Y = {\n        open [{ public X = L }.X]\n        1\n    }\n    1\n}\nOuter.Y"));

        // The level's own row keeps its admitted block-head path, charged exactly as without the rejected target.
        const string Row = "        { public Q = p + 0 }.Q\n";
        var withRejected = "Outer(p) = {\n    public Y = {\n        open [{ public X = 1 }.X]\n" + Row + "    }\n    1\n}\nOuter.Y";
        var valid = "Outer(p) = {\n    public Y = {\n" + Row + "    }\n    1\n}\nOuter.Y";
        Assert.Equal(DiagnosticCode.BadOpenForm, Assert.Single(SourceProvenance.ExpectFrontEndError(withRejected)).Code);
        SourceProvenance.ParseValid(valid);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, ExposureOfY(withRejected));
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, ExposureOfY(valid));
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty,
            Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(valid)).Errors).Code);

        // Exposure metadata of the recovery tree is the subject here, so the parse may report diagnostics.
        static PropertyExposure ExposureOfY(string source)
            => SourceProvenance.ParseAllowingDiagnostics(source).Root.Properties.Single(static p => p.Name == "Outer").Value
                .Properties.Single(static p => p.Name == "Y").Exposure;
    }
}
