using KatLang.Semantics;

namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// SYN-12B — executable contracts behind the tutorial's high-risk semantic
/// explanations. <see cref="TutorialResultSweepTests"/> proves that every
/// documented example prints what the tutorial claims; the tests here prove
/// the FACT the prose teaches — which declaration a name binds to, which
/// algorithm owns a property, which parameter order was inferred, which
/// structured error a rejected program reports — through the elaborated AST,
/// the editor semantic model, and the public error codes, so a documented
/// example can no longer print the right number for the wrong semantic reason.
/// Every source here is either a tutorial example or its documented control.
/// </summary>
public class TutorialSemanticContractTests
{
    private static RunResult.Success RunSuccess(string source) =>
        Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

    private static string Display(string source) =>
        RunSuccess(source).ToDisplayString().ReplaceLineEndings("\n");

    private static KatLangError RunFailure(string source, KatLangErrorCode code)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = failure.Errors.FirstOrDefault(e => e.Code == code);
        Assert.True(error is not null,
            $"Expected {code} but got: {string.Join(" | ", failure.Errors.Select(e => $"{e.Code}: {e.Message}"))}");
        return error!;
    }

    private static Property PropertyOf(Algorithm owner, string name) =>
        Assert.Single(owner.Properties, p => p.Name == name);

    // ── Lexical ownership ("A Parameter Always Means This Call's Argument", "Parameters take part in the walk") ──

    private const string BraceOwnedInner =
        "Outer(v) = {\n    Inner = v + 1\n    Inner\n}\n\nOuter(7)";

    [Fact]
    public void NestedProperty_IsOwnedByTheBraceAlgorithm_AndReadsItsParameter()
    {
        var parsed = SourceProvenance.ParseValid(BraceOwnedInner);
        var root = parsed.Root;

        // Ownership: Inner is Outer's property, not the root's, and infers no parameter of its own.
        Assert.DoesNotContain(root.Properties, p => p.Name == "Inner");
        var outer = PropertyOf(root, "Outer").Value;
        Assert.Equal(["v"], outer.Params);
        var inner = PropertyOf(outer, "Inner");
        Assert.Empty(inner.Value.Params);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, inner.Exposure);

        // Binding: the `v` in Inner's body (line 2, column 13) is Outer's explicit parameter, declared at (1, 7).
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var reference = model.FindResolutionAt(2, 13);
        Assert.NotNull(reference);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, reference.Classification);
        Assert.Equal(new SourceSpan(1, 7, 1, 7), reference.ResolvedDeclaration!.Span);

        Assert.Equal("8", Display(BraceOwnedInner));

        // Controls: a genuinely local Inner is neither a root callable nor a structural member.
        RunFailure(BraceOwnedInner + "\nInner(7)", KatLangErrorCode.UnresolvedImplicitParams);
        RunFailure("Outer(v) = {\n    Inner = v + 1\n    Inner\n}\n\nOuter.Inner", KatLangErrorCode.LocalOnlyProperty);
    }

    [Fact]
    public void IndentationDoesNotNest_TheIndentedSpellingDeclaresARootProperty()
    {
        // The pre-SYN-12 tutorial example: right number, wrong reason.
        const string indented = "Outer(v) = Inner\n  Inner = v + 1\n\nOuter(7)";
        var parsed = SourceProvenance.ParseValid(indented);
        var root = parsed.Root;

        var inner = PropertyOf(root, "Inner");
        Assert.Equal(["v"], inner.Value.Params);                 // Inner's OWN implicit parameter
        Assert.Empty(PropertyOf(root, "Outer").Value.Properties);  // Outer owns nothing

        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var reference = model.FindResolutionAt(2, 11);
        Assert.NotNull(reference);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, reference.Classification);

        // Same printed number, but Outer merely forwards its v to a root sibling ...
        Assert.Equal("8", Display(indented));
        // ... which is therefore callable from the root, unlike the brace-owned Inner.
        Assert.Equal("8\n8", Display(indented + "\nInner(7)"));
    }

    // ── "Functions: Algorithms Without Properties": the label is property ownership, and owning properties never limits callability ──

    private const string FunctionAndAlgorithm =
        "F(x) = (x + 1)^2\n\nG(x) = {\n    Y = x + 1\n    Y^2\n}\n\nF(3)\nG(3)";

    private const string PropertyOwningCallback =
        "G(x) = {\n    Y = x + 1\n    Y^2\n}\nApply(f) = f(3)\n\nApply(G)\n[1, 2].map(G)";

    [Fact]
    public void FunctionLabel_IsPropertyOwnership_AndOwningPropertiesKeepsAnAlgorithmCallable()
    {
        var root = SourceProvenance.ParseValid(FunctionAndAlgorithm).Root;

        // F and G are root properties with the same parameter list; F owns no properties (a function), G owns Y.
        var f = PropertyOf(root, "F").Value;
        var g = PropertyOf(root, "G").Value;
        Assert.Equal(["x"], f.Params);
        Assert.Empty(f.Properties);
        Assert.Equal(["x"], g.Params);
        var y = PropertyOf(g, "Y");
        Assert.DoesNotContain(root.Properties, p => p.Name == "Y");

        // Y is G's property and itself a function: it owns nothing, infers no parameter, and reads G's x — hence local-only.
        Assert.Empty(y.Value.Properties);
        Assert.Empty(y.Value.Params);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, y.Exposure);

        Assert.Equal("16\n16", Display(FunctionAndAlgorithm));
        RunFailure(FunctionAndAlgorithm + "\nG.Y", KatLangErrorCode.LocalOnlyProperty);

        // Owning a property does not restrict higher-order use: G is passable and usable as a callback like any function.
        Assert.Equal("16\n[4, 9]", Display(PropertyOwningCallback));
    }

    // ── Visibility: private = not exported; structural access checks exposure only ──

    private const string Library = "Lib = {\n    public Area = 4\n    Helper = Area / 2\n}";

    [Fact]
    public void PrivateMember_IsReachableStructurally_ButNotExportedThroughOpen()
    {
        var lib = PropertyOf(SourceProvenance.ParseValid(Library + "\n\nLib.Helper").Root, "Lib").Value;
        var area = PropertyOf(lib, "Area");
        var helper = PropertyOf(lib, "Helper");
        Assert.True(area.IsPublic);
        Assert.False(helper.IsPublic);
        Assert.Equal(PropertyExposure.Exported, area.Exposure);
        Assert.Equal(PropertyExposure.Exported, helper.Exposure); // exposure is about the value, not `public`

        Assert.Equal("4\n2", Display(Library + "\n\nLib.Area\nLib.Helper"));
        Assert.Equal("4", Display("open Lib\n" + Library + "\n\nArea"));
        Assert.Equal("2", Display("open Lib\n" + Library + "\n\nLib.Helper"));
        RunFailure("open Lib\n" + Library + "\n\nHelper", KatLangErrorCode.UnresolvedImplicitParams);
    }

    [Fact]
    public void PublicLocalOnlyMember_IsRefusedOutsideItsOwner_AndAParameterizedProviderCannotBeOpened()
    {
        const string library = "Lib(r) = {\n    public Area = r * r\n    Area\n}";
        var lib = PropertyOf(SourceProvenance.ParseValid(library + "\n\nLib(3)").Root, "Lib").Value;
        var area = PropertyOf(lib, "Area");
        Assert.True(area.IsPublic);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, area.Exposure);
        Assert.Equal(["r"], area.RequiredAncestorParameters);

        Assert.Equal("9", Display(library + "\n\nLib(3)"));
        // Structural access from the root selects Area and refuses it: the root is not
        // inside `Lib`, the owner of the `r` that Area captures.
        RunFailure(library + "\n\nLib.Area", KatLangErrorCode.LocalOnlyProperty);
        // `open Lib` is refused at the open itself: Lib requires arguments, and open never
        // creates the activation its members would read (a front-end rejection).
        FrontEndRejection("open Lib\n" + library + "\n\nArea", DiagnosticCode.IllegalInOpen, KatLangErrorCode.IllegalInOpen);
        // Inside `Lib` the captured member is usable through both channels — one output row
        // with two slots, so the two reads appear as one sequence value.
        Assert.Equal("(9, 9)", Display("Lib(r) = {\n    open Helper\n    Helper = {\n        public Area = r * r\n    }\n    Area, Helper.Area\n}\n\nLib(3)"));
    }

    // ── Conditional families: branch-selection dimensions and the shared-arity rule ──

    private static Diagnostic FrontEndRejection(string source, DiagnosticCode code, KatLangErrorCode publicCode)
    {
        // The rule is a front-end check: the program never reaches evaluation.
        var diagnostic = Assert.Single(SourceProvenance.ParseAllowingDiagnostics(source).Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(code, diagnostic.Code);
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Equal(publicCode, Assert.Single(failure.Errors).Code);
        return diagnostic;
    }

    [Fact]
    public void ClauseFamily_RejectsDisagreeingTopLevelArities_BeforeAnythingRuns()
    {
        // F(0) would match the first clause; the family is rejected regardless, at the clause that disagrees.
        var pattern = FrontEndRejection(
            "F(0) = 1\nF(x, y) = 2\n\nF(0)",
            DiagnosticCode.BranchArityMismatch, KatLangErrorCode.BranchArityMismatch);
        Assert.Equal(2, pattern.Span.StartLineNumber);
        Assert.Equal(1, pattern.Span.StartColumn);

        var output = FrontEndRejection(
            "F(0) = 1\nF(x) = 1, 2\n\nF(5)",
            DiagnosticCode.BranchOutputArityMismatch, KatLangErrorCode.BranchOutputArityMismatch);
        Assert.Equal(2, output.Span.StartLineNumber);

        // A captured pair is one written output slot, so it is legal beside a scalar branch.
        Assert.Equal("(1, 2)", Display("F(0) = 1\nF(x) = (1, 2)\n\nF(5)"));
    }

    [Fact]
    public void SequenceValuePattern_OpensLoneListsInOrdinaryDefinitions_ButMatchesSequenceValuesOnlyInFamilies()
    {
        // Ordinary definition: one clause, no family — an explicit sequence-value parameter pattern.
        var pairSum = PropertyOf(SourceProvenance.ParseValid("PairSum((x, y)) = x + y\nPairSum([2, 3])").Root, "PairSum").Value;
        Assert.Empty(pairSum.Branches);
        var pairSumWritten = Assert.IsType<Algorithm.User>(pairSum);
        Assert.True(pairSumWritten.HasExplicitParameterList);
        Assert.Single(pairSumWritten.ParameterPatterns);
        Assert.Equal("5\n5", Display("PairSum((x, y)) = x + y\nPairSum((2, 3))\nPairSum([2, 3])"));
        RunFailure("PairSum((x, y)) = x + y\nPairSum([1, 2, 3])", KatLangErrorCode.ArityMismatch);
        RunFailure("PairSum((x, y)) = x + y\nPairSum(7)", KatLangErrorCode.ArityMismatch);

        // Clause family: the same written pattern matches sequence values only.
        var family = PropertyOf(SourceProvenance.ParseValid("F((x, y)) = x + y\nF(z) = 0\n\nF([2, 3])").Root, "F").Value;
        Assert.Equal(2, family.Branches.Count);
        Assert.Equal("5\n0", Display("F((x, y)) = x + y\nF(z) = 0\n\nF((2, 3))\nF([2, 3])"));
        RunFailure("F((x, y)) = x + y\nF((x, y, z)) = 0\n\nF([2, 3])", KatLangErrorCode.NoMatchingBranch);
        // The singleton pattern matches any ONE argument whole, never opening it.
        Assert.Equal("[2, 3]", Display("F((x)) = x\nF(z) = 0\n\nF([2, 3])"));
    }

    // ── Dot-call: structural member selection is not the lexical rewrite `B(A, C)` ──

    private const string StructuralMember =
        "B(a, c) = a * 100 + c\nObj = {\n    public B(c) = c + 1\n}\n\nObj.B(5)";

    private const string LexicalFallback =
        "B(a, c) = a * 100 + c\nObj = {\n    public B(c) = c + 1\n}\n\n3.B(5)";

    [Fact]
    public void DotCall_StructuralMemberWins_AndIsNotRewrittenToTheLexicalCall()
    {
        // The member `B` of `Obj.B(5)` (line 6, column 5) resolves to Obj's own declaration (line 3, column 12) ...
        var parsed = SourceProvenance.ParseValid(StructuralMember);
        var member = SemanticModelBuilder.Build(parsed.Parsed).FindResolutionAt(6, 5);
        Assert.NotNull(member);
        Assert.Equal(IdentifierClassification.PropertyReference, member.Classification);
        Assert.Equal(new SourceSpan(3, 12, 3, 12), member.ResolvedDeclaration!.Span);
        Assert.Equal("6", Display(StructuralMember));

        // ... whereas a receiver without the member reaches the root `B` (line 1, column 1) through the fallback.
        var fallbackParsed = SourceProvenance.ParseValid(LexicalFallback);
        var fallback = SemanticModelBuilder.Build(fallbackParsed.Parsed).FindResolutionAt(6, 3);
        Assert.NotNull(fallback);
        Assert.Equal(IdentifierClassification.PropertyReference, fallback.Classification);
        Assert.Equal(new SourceSpan(1, 1, 1, 1), fallback.ResolvedDeclaration!.Span);
        Assert.Equal("305", Display(LexicalFallback));

        // The fallback injects the receiver as ONE argument; it never spreads a sequence receiver.
        RunFailure("B(a, c) = a * 100 + c\n(3, 4).B(5)", KatLangErrorCode.TypeMismatch);
    }

    // ── "Calls Return One Value": the boundary, its two edge cases, and the consumers that are not boundaries ──

    [Fact]
    public void CallBoundary_ReturnsOneValue_NeverASilentEmptySequenceForAMissingOutput()
    {
        Assert.Equal("2", Display("F = 1, 2\nG(x) = x.count\nG(F())"));

        var empty = RunSuccess("Empty = ()\nEmpty()");
        Assert.Equal("()", empty.ToDisplayString());
        Assert.Single(empty.OutputRows);

        RunFailure("Nothing = {}\nNothing()", KatLangErrorCode.MissingOutput);
        RunFailure("D(x) = x, x\n[1].map(D)", KatLangErrorCode.ArityMismatch);

        // Loop state is not a value boundary at the root; a property boundary captures it as one value.
        Assert.Equal(2, RunSuccess("Step = a + 1, b + 1\nStep.repeat(1, 0, 0)").OutputRows.Count);
        var captured = RunSuccess("Step = a + 1, b + 1\nR = Step.repeat(1, 0, 0)\nR");
        Assert.Single(captured.OutputRows);
        Assert.Equal("(1, 1)", captured.ToDisplayString());
    }

    // ── Grace: the contract is the inferred parameter list, not a computed number ──

    private static IReadOnlyList<string> InferredParams(string definition) =>
        Assert.Single(SourceProvenance.ParseValid(definition).Root.Properties).Value.Params;

    [Theory]
    [InlineData("Weighted = a + 10 * b + 100 * ~~c", new[] { "c", "a", "b" })]
    [InlineData("Weighted = a + 10 * b + 100 * ~c", new[] { "a", "c", "b" })]
    [InlineData("Weighted = a + 10 * b + 100 * ~c~", new[] { "a", "b", "c" })]
    [InlineData("Weighted = a + 10 * b + 100 * ~c + ~c", new[] { "c", "a", "b" })]
    [InlineData("Weighted = a + 10 * b + 100 * ~~~~~c", new[] { "c", "a", "b" })]
    [InlineData("Weighted = a~~ + 10 * b + 100 * c", new[] { "b", "c", "a" })]
    [InlineData("Divide = y / ~x", new[] { "x", "y" })]
    [InlineData("Tie = ~b + ~a", new[] { "b", "a" })]
    public void Grace_WeightsAccumulatePerName_AndReorderTheInferredSignature(string definition, string[] expected)
    {
        Assert.Equal(expected, InferredParams(definition));
    }

    [Fact]
    public void Grace_TheInferredSignatureIsWhatAnArityErrorReports()
    {
        var error = RunFailure("Weighted = a + 10 * b + 100 * ~~c\n\nWeighted(1)", KatLangErrorCode.ArityMismatch);
        Assert.Contains("Weighted(c, a, b)", error.Message);
        Assert.Equal("132", Display("Weighted = a + 10 * b + 100 * ~~c\n\nWeighted(1, 2, 3)"));
    }

    [Fact]
    public void Grace_OnAnExplicitParameter_IsAStructuredFrontEndError_AtTheMarker()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("K(b, a) = b, ~a\nK(1, 2)");
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(1, diagnostic.Span.StartLineNumber);
        Assert.Equal(14, diagnostic.Span.StartColumn);
    }
}
