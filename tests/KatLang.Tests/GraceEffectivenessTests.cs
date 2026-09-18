using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// F10 — the Grace effectiveness boundary. Grace `~` is meaningful on exactly one
/// kind of occurrence: a FREE bare name that implicit-signature collection promotes
/// to a parameter of the enclosing algorithm — that is the one place its weight is
/// consumed (<c>ParameterDetector.CollectFreeParams</c>, then
/// <c>ApplyGraceReordering</c>). On every other occurrence the marker could reorder
/// nothing and used to be silently ignored; it is now the front-end error
/// <see cref="DiagnosticCode.InvalidGraceMarker"/> naming what fixed the binding:
/// an explicit parameter, a parameter of an enclosing algorithm, a visible
/// property, a builtin, an opened property, a dot member that always resolves
/// structurally, or any occurrence under a closed explicit parameter list. Valid
/// Grace is unchanged (the positive controls at the end).
/// </summary>
public class GraceEffectivenessTests
{
    private static Diagnostic AssertIneffective(string source, string name, string reasonFragment, SourceSpan? span = null)
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.StartsWith(
            $"Grace has no effect on '{name}' because {reasonFragment}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.EndsWith("remove the marker.", diagnostic.Message, StringComparison.Ordinal);
        if (span is { } expected)
            Assert.Equal(expected, diagnostic.Span);
        return diagnostic;
    }

    private static IReadOnlyList<string> ParamsOf(string source, string propertyName = "K")
    {
        var root = SourceProvenance.ParseValid(source).Root;
        return Assert.Single(root.Properties, p => p.Name == propertyName).Value.Params;
    }

    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString().Replace("\r\n", "\n");
    }

    // ── Rejected: the occurrence's binding is already fixed ─────────────────

    [Theory]
    [InlineData("K(b, a) = b, ~a\nK(1, 2)", 1, 14, 1, 15)]
    [InlineData("K(b, a) = b, a~\nK(1, 2)", 1, 14, 1, 15)]
    [InlineData("K(b, a) = b, ~~a\nK(1, 2)", 1, 14, 1, 16)]
    [InlineData("K(b, a) = (b, ~a)\nK(1, 2)", 1, 15, 1, 16)]
    [InlineData("F(v) = v\nK(b, a) = F(~a)\nK(1, 2)", 2, 13, 2, 14)]
    [InlineData("K(b, a) = b, [~a]\nK(1, 2)", 1, 15, 1, 16)]
    public void GraceOnAnExplicitParameter_IsRejected(string source, int line, int column, int endLine, int endColumn)
        => AssertIneffective(
            source, "a", "it already resolves to an explicit parameter", new SourceSpan(line, column, endLine, endColumn));

    [Fact]
    public void GraceOnAnExplicitParameter_InsideARedundantGroup_IsRejectedAtTheOccurrence()
    {
        // `(~a)` keeps the plain name's capture boundary (`(a)` is a capture, never an
        // unwrapped name — final audit, September 2026), so the marked occurrence inside
        // the group is what the report locates, exactly as in `(b, ~a)`.
        AssertIneffective(
            "K(b, a) = b, (~a)\nK(1, 2)", "a", "it already resolves to an explicit parameter", new SourceSpan(1, 15, 1, 16));
    }

    [Theory]
    [InlineData("X = 1\nK = ~X + 2\nK", "X")]
    [InlineData("X = 1\nK = X~ + 2\nK", "X")]
    [InlineData("X = 1\nK = ~X(2)\nK", "X")]
    [InlineData("Outer = {\n    X = 1\n    Inner = ~X + y\n    Inner(1)\n}\nOuter", "X")]
    [InlineData("Obj = {\n    public V = 42\n    0\n}\nObj~.V", "Obj")]
    public void GraceOnAVisibleProperty_IsRejected(string source, string name)
        => AssertIneffective(source, name, "it already resolves to a property");

    [Fact]
    public void GraceOnABuiltin_IsRejected()
    {
        AssertIneffective("K = ~count((1, 2)) + x\nK(1)", "count", "it already resolves to the builtin 'count'");
        AssertIneffective("S = 1, 2, 3\nS.~count", "count", "it already resolves to the builtin 'count'");
        AssertIneffective("K = ~pi * r\nK(2)", "pi", "it already resolves to the builtin 'pi'");
    }

    [Fact]
    public void GraceOnAnOpenedProperty_IsRejected()
        => AssertIneffective(
            "Lib = { public V = 1 }\nK = {\n    open Lib\n    ~V + x\n}\nK(1)",
            "V",
            "it already resolves to an opened property");

    [Theory]
    [InlineData("F(x) = {\n    Inner = ~x + y\n    Inner(1)\n}\nF(2)", "x")]
    [InlineData("F(x) = {\n    Inner = x~ + y\n    Inner(1)\n}\nF(2)", "x")]
    [InlineData("Outer(a, t) = {\n    P = a~.t\n    P\n}\nOuter(1, {x+1})", "a")]
    [InlineData("Outer(a, t) = {\n    P = a.~t\n    P\n}\nOuter(1, {x+1})", "t")]
    [InlineData("F(x) = {\n    Inner = {\n        Deep = ~x + y\n        Deep(1)\n    }\n    Inner\n}\nF(2)", "x")]
    public void GraceOnAParameterOfAnEnclosingAlgorithm_IsRejected(string source, string name)
        => AssertIneffective(source, name, "it already resolves to a parameter of an enclosing algorithm");

    [Theory]
    [InlineData("K(a, t) = a~.t\nK(7, {a+1})", "a")]
    [InlineData("K(a, t) = a.~t\nK(7, {a+1})", "t")]
    [InlineData("K(a, t) = a~.t.string\nK(7, {a+1})", "a")]
    public void GraceUnderAClosedExplicitList_IsRejectedForBothDotForms(string source, string name)
        => AssertIneffective(source, name, "it already resolves to an explicit parameter");

    [Fact]
    public void GraceOnAnUndeclaredNameUnderAClosedList_ReportsBothProblems()
    {
        // The name is undeclared (the closed-list rule) AND the marker cannot reorder
        // anything (nothing is inferred under an explicit list): both facts are
        // reported, once each.
        var diagnostics = SourceProvenance.ExpectFrontEndError("K(b) = b + ~a\nK(1)");
        Assert.Equal(2, diagnostics.Count);
        Assert.Contains(diagnostics, d => d.Code == DiagnosticCode.UndeclaredIdentifier);
        var grace = Assert.Single(diagnostics, d => d.Code == DiagnosticCode.InvalidGraceMarker);
        Assert.Contains(
            "because the enclosing explicit parameter list fixes the parameter order, so nothing is inferred",
            grace.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void GraceOnAStructurallyResolvedMember_IsRejected()
    {
        // The receiver's statically known algorithm declares `V`, so the member never
        // joins the implicit parameters and the marker is meaningless — while an
        // OPAQUE receiver keeps the member occurrence effective (positive controls).
        AssertIneffective(
            "Obj = {\n    public V = 42\n    0\n}\nObj.~V",
            "V",
            "the member 'V' always resolves structurally on its receiver");
        AssertIneffective("K = x.~string\nK(5)", "string", "'.string' is the dot-only intrinsic");
        AssertIneffective("v = 5\nK = v.~string\nK", "string", "'.string' is the dot-only intrinsic");
    }

    [Fact]
    public void EachIneffectiveOccurrence_IsReportedAtItsOwnSpan()
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError("X = 1\nK = ~X + X~\nK");
        Assert.Equal(2, diagnostics.Count);
        Assert.All(diagnostics, d => Assert.Equal(DiagnosticCode.InvalidGraceMarker, d.Code));
        Assert.Equal(new SourceSpan(2, 5, 2, 6), diagnostics[0].Span);
        Assert.Equal(new SourceSpan(2, 10, 2, 11), diagnostics[1].Span);
    }

    [Fact]
    public void CompletionRun_ReportsEachOccurrenceExactlyOnce()
    {
        // `Need = v` gives Need an implicit parameter that Q's bare `Need` read lifts
        // into Q's own signature, which drives the ownership completion run. The
        // completion replays rewriting but never inference, so the report must live
        // in the rewrite pass — and be issued exactly once.
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError("Need = v\nQ = {\n    X = 1\n    ~X + Need\n}\nQ(1)"));
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.StartsWith("Grace has no effect on 'X' because it already resolves to a property", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(4, 5, 4, 6), diagnostic.Span);
    }

    [Fact]
    public void CompletionRun_KeepsAnEffectiveMarkerSilent()
    {
        // The same lifting shape with an EFFECTIVE marker: `b` is a free name of Q,
        // so the completion run — which keeps Q's inferred (not explicit) signature —
        // must report nothing and keep the reordered signature.
        var parsed = Parser.Parse("Need = v\nQ = {\n    a + ~b + Need\n}\nQ(1, 2, 3)");
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));
        var q = Assert.Single(parsed.Root.Properties, p => p.Name == "Q").Value;
        Assert.Equal("b", q.Params[0]);
        Assert.Equal("a", q.Params[1]);
        Assert.Contains("v", q.Params);
    }

    [Theory]
    [InlineData("K(a) = ~a~", "a", "it already resolves to an explicit parameter")]
    [InlineData("X = 1\nK = ~~X~~", "X", "it already resolves to a property")]
    [InlineData("K = ~count~(1)", "count", "it already resolves to the builtin 'count'")]
    public void CancellingMarkers_StillValidateTheirBinding(string source, string name, string reason)
        => AssertIneffective(source, name, reason);

    [Fact]
    public void CompletionThatChangesOwnership_RevalidatesGraceAgainstTheFinalOwner()
    {
        // Lifting Need's v into Outer replaces Inner's opened-property binding with
        // the enclosing parameter. Completion must keep the error and update its reason.
        const string source = "Lib = { public v = 99 }\nOuter = {\nInner = { open Lib\n~v }\nNeed = v\nInner + Need\n}\nOuter(7)";
        AssertIneffective(source, "v", "it already resolves to a parameter of an enclosing algorithm",
            new SourceSpan(4, 1, 4, 2));
        var model = SemanticModelBuilder.Build(Parser.Parse(source));
        Assert.Equal(IdentifierClassification.ImplicitParameterReference,
            model.FindResolutionAt(4, 2)!.Classification);
    }

    [Theory]
    [InlineData("Other(w) = ~w", "explicit parameter")]
    [InlineData("Other(w) = 1.~w", "explicit parameter")]
    [InlineData("~count(1)", "builtin 'count'")]
    [InlineData("Obj.~V", "always resolves structurally")]
    public void UnrelatedOwnershipChange_CannotEraseAnotherGraceError(string occurrence, string reason)
    {
        const string prefix = "Lib = { public v = 99 }\nObj = { V = 1 }\nOuter = {\nInner = { open Lib\nv }\nNeed = v\n";
        var parsed = Parser.Parse(prefix + occurrence + "\nInner + Need\n}\nOuter(7)");
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Contains(reason, diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SharedMemberMarker_IsReportedOnceAndKeepsRewriteSharing()
    {
        var name = new Expr.Resolve("V") { Span = new SourceSpan(2, 4, 2, 4) };
        var grace = new Expr.Grace(name, -1) { Span = new SourceSpan(2, 3, 2, 4) };
        var first = new Expr.DotCall(new Expr.Num(1), "V", null) { LexicalFallback = grace };
        var second = new Expr.DotCall(new Expr.Num(2), "V", null) { LexicalFallback = grace };
        var syntax = Parser.ParseSyntax("V(x) = x");
        Assert.False(syntax.HasErrors);
        var root = syntax.Root with { Output = [first, second, grace, name] };
        var detected = ParameterDetector.Detect(root);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, Assert.Single(detected.Diagnostics).Code);
        Assert.Same(Assert.IsType<Expr.DotCall>(detected.Root.Output[0]).LexicalFallback,
            Assert.IsType<Expr.DotCall>(detected.Root.Output[1]).LexicalFallback);
    }

    [Fact]
    public async Task LoadedModule_GraceValidationUsesCompletedOwnership()
    {
        const string module = "Lib = { public v = 99 }\nOuter = {\nInner = { open Lib\n~v }\nNeed = v\nInner + Need\n}\nOuter(7)";
        var options = new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult(module) };
        var parsed = await Parser.ParseAsync("M = load('https://katlang.org/grace.kat')\nM", options);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Contains("parameter of an enclosing algorithm", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task DeferredLoadedModule_RevalidatesGraceOnlyWhenSelected()
    {
        const string module = "Lib = { public v = 99 }\nOuter = {\nInner = { open Lib\n~v }\nNeed = v\nInner + Need\n}\nOuter(7)";
        const string source = "F(0) = 0\nF(n) = { M = load('https://katlang.org/grace.kat')\nM }\n";
        var fetches = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) => { fetches++; return ValueTask.FromResult(module); },
        };
        Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source + "F(0)", options));
        Assert.Equal(0, fetches);
        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source + "F(1)", options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.InvalidGraceMarker, error.Code);
        Assert.Contains("parameter of an enclosing algorithm", error.Message, StringComparison.Ordinal);
        // The marker sits on the module's line 4, which is no position in this document:
        // the report is positioned at the import site, the declaring `M` of the branch body.
        Assert.Equal((2, 10, 2, 10), (error.StartLine, error.StartColumn, error.EndLine, error.EndColumn));
        Assert.Equal(1, fetches);
    }

    [Theory]
    [InlineData("")]
    [InlineData("Lib = { public V = 1 }\n")]
    public void ParameterOwnedOpen_AndGraceAgreeWithoutSearchingFarther(string prefix)
    {
        var parsed = Parser.Parse(prefix + "F(Lib) = {\nopen Lib\n~Lib\n}");
        Assert.Equal(2, parsed.Diagnostics.Count);
        Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.OpenTargetIsParameter);
        var grace = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.InvalidGraceMarker);
        Assert.Contains("explicit parameter", grace.Message, StringComparison.Ordinal);
        var model = SemanticModelBuilder.Build(parsed);
        var line = prefix.Length == 0 ? 3 : 4;
        Assert.Equal(IdentifierClassification.ExplicitParameterReference,
            model.FindResolutionAt(line, 2)!.Classification);
    }

    [Fact]
    public void GraceNextToASplitDeclarationHead_HasOnlyItsOwnBindingError()
    {
        var free = Parser.Parse("~q\n= 1\nKeep = 2\nKeep");
        Assert.Equal(DiagnosticCode.UnexpectedToken, Assert.Single(free.Diagnostics).Code);
        var bound = Parser.Parse("q = 0\n~q\n= 1\nKeep = 2\nKeep");
        Assert.Equal(2, bound.Diagnostics.Count);
        Assert.Single(bound.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken);
        var grace = Assert.Single(bound.Diagnostics, d => d.Code == DiagnosticCode.InvalidGraceMarker);
        Assert.Equal(new SourceSpan(2, 1, 2, 2), grace.Span);
    }

    [Theory]
    [InlineData("K = y, ~x~", "(2, 1)")]
    [InlineData("K = y, (~x~)", "(2, 1)")]
    public void CancellingFreeMarkers_PreserveOrderAndGrouping(string declaration, string expected)
    {
        Assert.Equal(["y", "x"], ParamsOf(declaration));
        Assert.Equal(expected, Display(declaration + "\nK(2, 1)"));
        var syntax = Parser.ParseSyntax("(~x~)");
        Assert.False(syntax.HasErrors);
        var group = Assert.IsType<Expr.Capture>(syntax.Root.Output[0]);
        Assert.Equal(0, Assert.IsType<Expr.Grace>(Assert.Single(group.Body)).Weight);
    }

    [Fact]
    public void Engine_ReportsTheStructuredFrontEndCode()
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("K(b, a) = b, ~a\nK(1, 2)"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.InvalidGraceMarker, error.Code);
        Assert.Equal((1, 14, 1, 15), (error.StartLine, error.StartColumn, error.EndLine, error.EndColumn));
    }

    [Fact]
    public void RecoveryTree_StripsTheMarkerLikeEveryOtherGrace()
    {
        // The rejected program still elaborates for tooling: the marker is stripped and
        // the occurrence classifies as the explicit parameter it already was, so the
        // recovery tree is exactly the ungraced program's tree.
        var graced = Parser.Parse("K(b, a) = b, ~a");
        Assert.True(graced.HasErrors);
        var k = Assert.Single(graced.Root.Properties).Value;
        Assert.Equal(["b", "a"], k.Params);
        Assert.Equal("a", Assert.IsType<Expr.Param>(k.Output[1]).Name);
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(graced.Root));
    }

    [Theory]
    [InlineData("K(b, a) = b, ~a", 1, 15, IdentifierClassification.ExplicitParameterReference, "explicit parameter")]
    [InlineData("X = 1\nK = ~X + 2", 2, 6, IdentifierClassification.PropertyReference, "a property")]
    [InlineData("K = ~count((1, 2)) + x", 1, 6, IdentifierClassification.Builtin, "the builtin 'count'")]
    public void Diagnostic_AgreesWithTheSemanticModelsResolution(
        string source, int line, int column, IdentifierClassification classification, string reasonFragment)
    {
        // The report's reason comes from the SAME owner walk the editor resolves with,
        // so the graced occurrence classifies exactly as the reason says.
        var parsed = Parser.Parse(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Contains(reasonFragment, diagnostic.Message, StringComparison.Ordinal);

        var model = SemanticModelBuilder.Build(parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(line, column));
        Assert.Equal(classification, resolution.Classification);
    }

    // ── Positive controls: effective Grace is unchanged ─────────────────────

    [Theory]
    [InlineData("Divide = y / ~x\nDivide(2, 10)", "5")]
    [InlineData("Divide = y~ / x\nDivide(2, 10)", "5")]
    [InlineData("Divide = y / ~~x\nDivide(2, 10)", "5")]
    [InlineData("K = a~.t\nK({a+1}, 7)", "8")]
    [InlineData("K = a.~t\nK({a+1}, 7)", "8")]
    [InlineData("K = a~.~t\nK({a+1}, 7)", "8")]
    [InlineData("Fib = b~, a + b\nFib.repeat(10, 0, 1) : 0", "55")]
    [InlineData("K = {\n  a\n  ~b\n}\nK(10, 20)", "(20, 10)")]
    [InlineData("F(v, w) = w\nK = F(y, ~x)\nK(1, 2)", "1")]
    [InlineData("K = (y, ~x)\nK(1, 2)", "(2, 1)")]
    [InlineData("K = [y, ~x]\nK(1, 2)", "[2, 1]")]
    // With a lexical `V` the member is bound and only the free receiver `o` is
    // graced; without one the member occurrence itself is free and participates.
    [InlineData("V(x) = 99\nObj = { public V = 42 }\nRead = o~.V\nRead(Obj)", "42")]
    [InlineData("Obj = { public V = 42 }\nRead = o.~V\nRead({x}, Obj)", "42")]
    [InlineData("t(x) = x + 1\nK = a~.t\nK(7)", "8")]
    [InlineData("S = 1, 2, 3\nK = S.~t\nK({a:0 + 100})", "101")]
    [InlineData("Outer = {\n    t(a) = a + 1\n    K = a~.t\n    K(41)\n}\nOuter", "42")]
    public void EffectiveGrace_StaysValidAndUnchanged(string source, string expected)
    {
        Assert.False(Parser.Parse(source).HasErrors);
        Assert.Equal(expected, Display(source));
    }

    [Fact]
    public void EffectiveGrace_ReordersExactlyAsBefore()
    {
        Assert.Equal(["x", "y"], ParamsOf("K = y / ~x"));
        Assert.Equal(["t", "a"], ParamsOf("K = a~.t"));
        Assert.Equal(["t", "a"], ParamsOf("K = a.~t"));
        Assert.Equal(["x", "c", "b"], ParamsOf("K = c + b + ~~x"));
        Assert.Equal(["o"], ParamsOf("V(x) = 99\nObj = { public V = 42 }\nK = o~.V"));
        Assert.Equal(["V", "o"], ParamsOf("Obj = { public V = 42 }\nK = o.~V"));
        Assert.Equal(["t"], ParamsOf("S = 1, 2, 3\nK = S.~t"));
        Assert.Equal(["v"], ParamsOf("K = v~.string"));
    }

    [Fact]
    public void GraceAtTheProgramRoot_OrdersTheRootsPhantomSignature()
    {
        // The root infers its own (never-called) signature like any body, so a free
        // graced name at the root is effective — no diagnostic, reordered signature.
        var parsed = Parser.Parse("y / ~x");
        Assert.False(parsed.HasErrors);
        Assert.Equal(["x", "y"], parsed.Root.Params);
    }

    [Fact]
    public void GraceInsideAConditionalBranchBody_KeepsTheParsersOneReport()
    {
        // The parser already rejects Grace in conditional branch bodies; the detector
        // strips it for recovery and never adds a second report.
        var diagnostics = SourceProvenance.ExpectFrontEndError("F(0) = 0\nF(x) = ~x + 1\nF(2)");
        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Contains("conditional branch bodies", diagnostic.Message, StringComparison.Ordinal);
    }
}
