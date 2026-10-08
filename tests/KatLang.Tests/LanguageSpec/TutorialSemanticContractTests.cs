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
/// Most sources here are tutorial examples or their documented controls; the
/// rest pin facts that earlier editions of the tutorial explained and that the
/// language still guarantees.
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

    // ── Lexical ownership ("How Names Are Found", "Local Definitions") ──

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
        var reference = model.FindResolutionAt(new SourcePosition(2, 13));
        Assert.NotNull(reference);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, reference.Classification);
        Assert.Equal(new SourceSpan(1, 7, 1, 8), reference.ResolvedDeclaration!.Span);

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
        var reference = model.FindResolutionAt(new SourcePosition(2, 11));
        Assert.NotNull(reference);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, reference.Classification);

        // Same printed number, but Outer merely forwards its v to a root sibling ...
        Assert.Equal("8", Display(indented));
        // ... which is therefore callable from the root, unlike the brace-owned Inner.
        Assert.Equal("8\n8", Display(indented + "\nInner(7)"));
    }

    // ── Property ownership (the earlier tutorial's "function" label): owning properties never limits callability ──

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

    // ── Visibility ("Public Members and open"): private = not exported; structural access checks exposure only ──

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
        Assert.Equal(2, Assert.NotNull(pattern.Span).Start.Line);
        Assert.Equal(1, Assert.NotNull(pattern.Span).Start.Column);

        var output = FrontEndRejection(
            "F(0) = 1\nF(x) = 1, 2\n\nF(5)",
            DiagnosticCode.BranchOutputArityMismatch, KatLangErrorCode.BranchOutputArityMismatch);
        Assert.Equal(2, Assert.NotNull(output.Span).Start.Line);

        // A captured pair is one written output slot, so it is legal beside a scalar branch.
        Assert.Equal("(1, 2)", Display("F(0) = 1\nF(x) = (1, 2)\n\nF(5)"));
    }

    [Fact]
    public void StructuralPatterns_MatchOnlyTheirOwnKind_InOrdinaryDefinitionsAndFamiliesAlike()
    {
        // Ordinary definition: one clause, no family — an explicit sequence parameter pattern.
        var pairSum = PropertyOf(SourceProvenance.ParseValid("PairSum((x, y)) = x + y\nPairSum((2, 3))").Root, "PairSum").Value;
        Assert.Empty(pairSum.Branches);
        var pairSumWritten = Assert.IsType<Algorithm.User>(pairSum);
        Assert.True(pairSumWritten.HasExplicitParameterList);
        Assert.IsType<SequenceValueParameterPattern>(Assert.Single(pairSumWritten.ParameterPatterns));
        Assert.Equal("5", Display("PairSum((x, y)) = x + y\nPairSum((2, 3))"));
        // The sequence pattern opens a SEQUENCE only: a list or a scalar is its kind mismatch,
        // a sequence of the wrong length its arity mismatch.
        RunFailure("PairSum((x, y)) = x + y\nPairSum([2, 3])", KatLangErrorCode.TypeMismatch);
        RunFailure("PairSum((x, y)) = x + y\nPairSum(7)", KatLangErrorCode.TypeMismatch);
        RunFailure("PairSum((x, y)) = x + y\nPairSum((1, 2, 3))", KatLangErrorCode.ArityMismatch);
        // The list pattern is the list twin, and a single list clause is an ordinary callable too.
        var listSum = PropertyOf(SourceProvenance.ParseValid("ListSum([x, y]) = x + y\nListSum([2, 3])").Root, "ListSum").Value;
        Assert.IsType<ListValueParameterPattern>(Assert.Single(Assert.IsType<Algorithm.User>(listSum).ParameterPatterns));
        Assert.Equal("5", Display("ListSum([x, y]) = x + y\nListSum([2, 3])"));
        RunFailure("ListSum([x, y]) = x + y\nListSum((2, 3))", KatLangErrorCode.TypeMismatch);

        // Clause family: the same kind law, where a mismatch only rejects the clause.
        var family = PropertyOf(SourceProvenance.ParseValid("F((x, y)) = x + y\nF(z) = 0\n\nF([2, 3])").Root, "F").Value;
        Assert.Equal(2, family.Branches.Count);
        Assert.Equal("5\n0", Display("F((x, y)) = x + y\nF(z) = 0\n\nF((2, 3))\nF([2, 3])"));
        RunFailure("F((x, y)) = x + y\nF((x, y, z)) = 0\n\nF([2, 3])", KatLangErrorCode.NoMatchingBranch);
        // The one-element list pattern matches a one-element list only; a plain binder takes
        // any ONE argument whole, never opening it.
        Assert.Equal("7\n0", Display("F([x]) = x\nF(z) = 0\n\nF([7])\nF([2, 3])"));
        Assert.Equal("[2, 3]", Display("F(0) = 0\nF(z) = z\n\nF([2, 3])"));

        // A literal keeps even a single definition a clause, and the tutorial's shape-matching
        // family likewise refuses the list spelling of a shape it accepts as a sequence.
        Assert.Equal("5", Display("F((0, x)) = x\n\nF((0, 5))"));
        RunFailure("F((0, x)) = x\n\nF([0, 5])", KatLangErrorCode.NoMatchingBranch);
        const string area = "Area(('circle', r)) = pi * r ^ 2\nArea(('rect', w, h)) = w * h\n\n";
        Assert.Equal("12", Display(area + "Area(('rect', 3, 4))"));
        RunFailure(area + "Area(['rect', 3, 4])", KatLangErrorCode.NoMatchingBranch);
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
        var member = SemanticModelBuilder.Build(parsed.Parsed).FindResolutionAt(new SourcePosition(6, 5));
        Assert.NotNull(member);
        Assert.Equal(IdentifierClassification.PropertyReference, member.Classification);
        Assert.Equal(new SourceSpan(3, 12, 3, 13), member.ResolvedDeclaration!.Span);
        Assert.Equal("6", Display(StructuralMember));

        // ... whereas a receiver without the member reaches the root `B` (line 1, column 1) through the fallback.
        var fallbackParsed = SourceProvenance.ParseValid(LexicalFallback);
        var fallback = SemanticModelBuilder.Build(fallbackParsed.Parsed).FindResolutionAt(new SourcePosition(6, 3));
        Assert.NotNull(fallback);
        Assert.Equal(IdentifierClassification.PropertyReference, fallback.Classification);
        Assert.Equal(new SourceSpan(1, 1, 1, 2), fallback.ResolvedDeclaration!.Span);
        Assert.Equal("305", Display(LexicalFallback));

        // The fallback injects the receiver as ONE argument; it never spreads a sequence receiver.
        RunFailure("B(a, c) = a * 100 + c\n(3, 4).B(5)", KatLangErrorCode.TypeMismatch);
    }

    // ── Dot receivers and collecting parameters ("Values Stay Values", "Passing Items with *"): dot-call passes a value, spread opens a value ──

    [Fact]
    public void DottedReceiver_IsTheWrittenArgument_AndOnlyTheSpreadMarkerOpensIt()
    {
        // The headline example: the spread receiver supplies the items of `Mean(1, 2, 3)`,
        // while the unspread group is ONE sequence value — one argument, collected as one
        // non-numeric element exactly like a list receiver — so the numeric sum rejects it as
        // an element of the wrong KIND (Q-27).
        const string mean = "Mean(*Vector) = Vector.sum / Vector.count\n";
        Assert.Equal("2\n2", Display(mean + "Mean(1, 2, 3)\n(1, 2, 3)*.Mean"));
        RunFailure(mean + "(1, 2, 3).Mean", KatLangErrorCode.TypeMismatch);
        RunFailure(mean + "[1, 2, 3].Mean", KatLangErrorCode.TypeMismatch);
        Assert.Equal("2", Display(mean + "[1, 2, 3]*.Mean"));

        // The receiver's origin never matters, `()` included: the dotted spelling and the
        // written call are the same call — one argument, collected as one visible `()` item
        // alone or beside another argument — and only the spread supplies nothing.
        const string collect = "E = ()\nCollectMany(*items) = items\n";
        Assert.Equal("[()]\n[()]\n[]\n[(), 1]",
            Display(collect + "E.CollectMany\nCollectMany(E)\nE*.CollectMany\nE.CollectMany(1)"));
        Assert.Equal("[()]", Display(collect + "().CollectMany"));
        Assert.Equal("()", Display("E = ()\nCollect(list) = list\nE.Collect"));
        Assert.Equal("0", Display("E = ()\nE.count"));

        // A fixed parameter binds the receiver whole; the spread receiver fills fixed slots.
        Assert.Equal("(1, 2)", Display("F(first, *middle, last) = first\n(1, 2).F(9)"));
        RunFailure("F(first, *middle, last) = first\n(1, 2).F", KatLangErrorCode.ArityMismatch);
        Assert.Equal("1", Display("F(first, *middle, last) = first\n(1, 2)*.F"));

        // Written and spread receivers keep the grouped/spread contrast for a sequence
        // and a list alike: a named receiver and a captured spread are ONE argument each,
        // and only the spread supplies the items.
        Assert.Equal("1\n3\n1", Display(
            "Arg = 1, 2, 3\nCollectMany(*list) = list\n"
            + "Arg.CollectMany.count\nArg*.CollectMany.count\n(Arg*).CollectMany.count"));
        Assert.Equal("3\n1\n3\n1", Display(
            "ArgList = [1, 2, 3]\nCollect(list) = list\nCollectMany(*list) = list\n"
            + "ArgList.Collect.count\nArgList.CollectMany.count\nArgList*.CollectMany.count\n(ArgList*).CollectMany.count"));

        // Beside another written argument the receiver is collected exactly, and a
        // spread-produced item is never reopened, even when it is the lone item.
        Assert.Equal("[(1, 2), 3]\n[(1, 2)]", Display(
            "CollectMany(*items) = items\n(1, 2).CollectMany(3)\n[(1, 2)]*.CollectMany"));
    }

    // ── "Several Outputs Become One Value": the call boundary, its two edge cases, and the consumers that are not boundaries ──

    [Fact]
    public void CallBoundary_ReturnsOneValue_NeverASilentEmptySequenceForAMissingOutput()
    {
        Assert.Equal("2", Display("F = 1, 2\nG(x) = x.count\nG(F())"));

        var empty = RunSuccess("Empty = ()\nEmpty()");
        Assert.Equal("()", empty.ToDisplayString());
        Assert.Single(empty.OutputRows);

        RunFailure("Nothing = {}\nNothing()", KatLangErrorCode.MissingOutput);
        RunFailure("D(x) = x, x\n[1].map(D)", KatLangErrorCode.ArityMismatch);

        // A completed loop is a value boundary like every call (Q-26): its multi-slot final state
        // reaches the root as ONE row, exactly like the same loop read through a property ...
        var lone = RunSuccess("Step = a + 1, b + 1\nStep.repeat(1, 0, 0)");
        Assert.Single(lone.OutputRows);
        Assert.Equal("(1, 1)", lone.ToDisplayString());
        var captured = RunSuccess("Step = a + 1, b + 1\nR = Step.repeat(1, 0, 0)\nR");
        Assert.Single(captured.OutputRows);
        Assert.Equal("(1, 1)", captured.ToDisplayString());

        // ... and only the explicit spread opens it into rows.
        Assert.Equal(2, RunSuccess("Step = a + 1, b + 1\nStep.repeat(1, 0, 0)*").OutputRows.Count);
    }

    // ── "Formulas That Use Formulas": forwarded inputs follow the formula's own names and are handed on by name ──

    private const string ForwardingFormulas =
        "Speed = distance / time\nKineticEnergy = mass * Speed ^ 2 / 2\n\nKineticEnergy(2, 10, 5)";

    [Fact]
    public void ForwardedParameters_FollowTheOwnNames_AndAreHandedOnByName()
    {
        // The documented signature is the inferred parameter list itself, not just the printed number.
        var root = SourceProvenance.ParseValid(ForwardingFormulas).Root;
        Assert.Equal(["distance", "time"], PropertyOf(root, "Speed").Value.Params);
        Assert.Equal(["mass", "distance", "time"], PropertyOf(root, "KineticEnergy").Value.Params);
        Assert.Equal("4", Display(ForwardingFormulas));

        // Own names first, forwarded names after them — not the order in which the body reaches
        // them: this body reaches Speed's inputs before it mentions `mass`, yet `mass` still comes
        // first (as (distance, time, mass), the same call would compute 0.1).
        const string speedFirst = "Speed = distance / time\nKineticEnergy = Speed ^ 2 * mass / 2\n\nKineticEnergy(2, 10, 5)";
        Assert.Equal(["mass", "distance", "time"], PropertyOf(SourceProvenance.ParseValid(speedFirst).Root, "KineticEnergy").Value.Params);
        Assert.Equal("4", Display(speedFirst));

        // An explicit list hands the inputs on by NAME, not by position: declared in another order
        // they still reach Speed's `distance` and `time` (matched by position, Speed would read 5
        // as its distance, and the result would be 0.25) ...
        Assert.Equal("4", Display(
            "Speed = distance / time\nKineticEnergy(mass, distance, time) = mass * Speed ^ 2 / 2\n\nKineticEnergy(2, 10, 5)"));
        Assert.Equal("4", Display(
            "Speed = distance / time\nKineticEnergy(mass, time, distance) = Speed ^ 2 * mass / 2\n\nKineticEnergy(2, 5, 10)"));

        // ... so renamed inputs, even with the right number of parameters, leave Speed without its inputs.
        var renamed = RunFailure(
            "Speed = distance / time\nKineticEnergy(m, d, t) = m * Speed ^ 2 / 2\n\nKineticEnergy(2, 10, 5)",
            KatLangErrorCode.ArityMismatch);
        Assert.Contains("'Speed'", renamed.Message);
    }

    // ── "Formulas That Use Formulas" and "Equal Arguments": one name is one input, however often it appears ──

    private const string RepeatedNameFormula = "Common(x, x) = x\n";

    [Fact]
    public void OneNameIsOneInput_WithinAndAcrossFormulas_WhileSeparateArgumentsMustBeEqual()
    {
        // "`H = F + G` means `H(x) = F(x) + G(x)`": one input `x`, handed to both formulas.
        var composed = SourceProvenance.ParseValid("F(x) = x + 1\nG(x) = x * 2\nH = F + G\n\nH(3)").Root;
        var h = Assert.IsType<Algorithm.User>(PropertyOf(composed, "H").Value);
        Assert.Equal(["x"], h.Params);
        var sum = Assert.IsType<Expr.Binary>(Assert.Single(h.Output));
        Assert.Equal("x", Assert.IsType<Expr.Param>(Assert.Single(Assert.IsType<Expr.Call>(sum.Left).Args)).Name);
        Assert.Equal("x", Assert.IsType<Expr.Param>(Assert.Single(Assert.IsType<Expr.Call>(sum.Right).Args)).Name);
        Assert.Equal("10", Display("F(x) = x + 1\nG(x) = x * 2\nH = F + G\n\nH(3)"));

        // "in the same way `Twice = Common * 2` means `Twice(x) = Common(x, x) * 2`: `Twice` takes one
        // input and hands it to both places where `Common` names `x`, so `Twice` is called with one argument".
        var twice = Assert.IsType<Algorithm.User>(
            PropertyOf(SourceProvenance.ParseValid(RepeatedNameFormula + "Twice = Common * 2\n\nTwice(7)").Root, "Twice").Value);
        Assert.Equal(["x"], twice.Params);
        var call = Assert.IsType<Expr.Call>(Assert.IsType<Expr.Binary>(Assert.Single(twice.Output)).Left);
        Assert.Equal(["x", "x"], call.Args.Select(static argument => Assert.IsType<Expr.Param>(argument).Name));
        Assert.Equal("14", Display(RepeatedNameFormula + "Twice = Common * 2\n\nTwice(7)"));
        RunFailure(RepeatedNameFormula + "Twice = Common * 2\n\nTwice(7, 7)", KatLangErrorCode.ArityMismatch);

        // "`Common(7, 8)` supplies two separate arguments, and two arguments for the same name must
        // be equal, so it is an error" — and a wrapper with two parameters of its own keeps them
        // separate, so it fails exactly like the direct call.
        var direct = RunFailure(RepeatedNameFormula + "\nCommon(7, 8)", KatLangErrorCode.ArityMismatch);
        var wrapped = RunFailure(RepeatedNameFormula + "Both(a, b) = Common(a, b)\n\nBoth(7, 8)", KatLangErrorCode.ArityMismatch);
        Assert.Equal("while evaluating call to Both: " + direct.Message, wrapped.Message);

        // "both places receive that same input, so they cannot differ — and if that input fails, or
        // is a function that needs arguments, the error is that input's own".
        var failing = RunFailure("Bad = 1 / 0\n" + RepeatedNameFormula + "Twice = Common * 2\n\nTwice(Bad)", KatLangErrorCode.DivisionByZero);
        Assert.Contains("while evaluating call to Twice:", failing.Message);
        var callable = RunFailure("Inc(y) = y + 1\n" + RepeatedNameFormula + "Twice = Common * 2\n\nTwice(Inc)", KatLangErrorCode.ArityMismatch);
        Assert.Contains("Property 'Inc' expects 1 parameter, but was called with 0 arguments.", callable.Message);

        // "An alias is different: `Same = Common` takes two separate arguments, exactly like `Common`."
        Assert.Equal("7", Display(RepeatedNameFormula + "Same = Common\n\nSame(7, 7)"));
        var aliasDirect = RunFailure(RepeatedNameFormula + "Same = Common\n\nSame(7, 8)", KatLangErrorCode.ArityMismatch);
        Assert.Equal("while evaluating call to Same: " + direct.Message.Replace("while evaluating call to Common: ", "", StringComparison.Ordinal), aliasDirect.Message);

        // Calling `Common` with its arguments, or passing `Common` itself to another function, is unchanged.
        Assert.Equal("7", Display(RepeatedNameFormula + "\nCommon(7, 7)"));
        Assert.Equal("5", Display(RepeatedNameFormula + "Apply(f) = f(5, 5)\n\nApply(Common)"));
    }

    // ── "Aliases, Forwarding, and Explicit Calls": the signature of each form, and what forwarding by name cannot do ──

    private const string SingleFormula = "Single([x]) = x\n";

    private static string Signature(Algorithm algorithm)
        => string.Join(", ", Assert.IsType<Algorithm.User>(algorithm).ParameterPatterns.Select(static pattern => pattern.DisplayName));

    /// <summary>A callable alias's parameters: its target's own, since the alias IS its target's callable.</summary>
    private static string AliasTargetSignature(Algorithm algorithm)
        => string.Join(", ", Assert.IsType<Algorithm.Alias>(algorithm).ResolvedTarget!.Signature.Signature!.ParameterPatterns.Select(static pattern => pattern.DisplayName));

    [Fact]
    public void AliasesForwardingAndExplicitCalls_EachFormHasTheSignatureTheTutorialStates()
    {
        const string formulas = "Double(x) = x * 2\nOther(y) = y * 2\n";
        var root = SourceProvenance.ParseValid(formulas
            + "Alias = Double\nForward(x) = Double\nExplicit(x) = Other(x)\nFormula = Double + 1\n\n0").Root;

        // "`Alias = Double` ... is `Double` under another name, with Double's parameters": a callable
        // alias — a binding of its own whose callable IS Double (binding indirection), never a wrapper.
        var alias = Assert.IsType<Algorithm.Alias>(PropertyOf(root, "Alias").Value);
        Assert.Equal("Double", Assert.IsType<Expr.Resolve>(alias.Target).Name);
        Assert.Equal(
            "x",
            string.Join(", ", alias.ResolvedTarget!.Signature.Signature!.ParameterPatterns.Select(static pattern => pattern.DisplayName)));

        // "`Forward(x) = Double` ... `Double` receives the parameter of the same name", and
        // "`Explicit(x) = Other(x)` ... the arguments are passed exactly as written": both keep their
        // own written signature, and each call reads the definition's own `x`.
        foreach (var name in new[] { "Forward", "Explicit" })
        {
            var algorithm = Assert.IsType<Algorithm.User>(PropertyOf(root, name).Value);
            Assert.Equal("x", Signature(algorithm));
            Assert.Null(algorithm.ForwardingParameterStart);
            var call = Assert.IsType<Expr.Call>(Assert.Single(algorithm.Output));
            Assert.Equal("x", Assert.IsType<Expr.Param>(Assert.Single(call.Args)).Name);
        }

        // "`Formula = Double + 1` ... means `Formula(x) = Double(x) + 1`".
        Assert.Equal(["x"], PropertyOf(root, "Formula").Value.Params);

        // "Nothing is added to the list, and nothing is renamed: `Bad(x) = Other` is an error".
        FrontEndRejection(formulas + "Bad(x) = Other\n\nBad(5)",
            DiagnosticCode.UnforwardableParameter, KatLangErrorCode.UnforwardableParameter);

        // "a parameter the called formula does not need simply stays unused (with `Ten = 10`,
        // `Always(p) = Ten` is `10` whatever it is given)".
        Assert.Equal("10", Display("Ten = 10\nAlways(p) = Ten\n\nAlways(999)"));

        // "`G(x, y) = Sub` ... `G(10, 3)` is ... `-7`, while `G(x, y) = Sub(x, y)` ... gives `7`".
        Assert.Equal("-7", Display("Sub(y, x) = y - x\nG(x, y) = Sub\n\nG(10, 3)"));
        Assert.Equal("7", Display("Sub(y, x) = y - x\nG(x, y) = Sub(x, y)\n\nG(10, 3)"));
    }

    [Fact]
    public void AliasesForwardingAndExplicitCalls_StructuralParametersAreMatchedWhole()
    {
        var root = SourceProvenance.ParseValid(SingleFormula
            + "Alias = Single\nSameShape([x]) = Single\nExplicit(x) = Single(x)\nConstruct = Single([x])\n\n0").Root;

        // "`Alias = Single` has Single's parameter `[x]` ... `Alias(7)` is an error, just like `Single(7)`".
        Assert.Equal("[x]", AliasTargetSignature(PropertyOf(root, "Alias").Value));
        RunFailure(SingleFormula + "Alias = Single\n\nAlias(7)", KatLangErrorCode.TypeMismatch);
        RunFailure(SingleFormula + "\nSingle(7)", KatLangErrorCode.TypeMismatch);

        // "`SameShape([x]) = Single` forwards by name ... `Single` receives it as the list it matched".
        Assert.Equal("[x]", Signature(PropertyOf(root, "SameShape").Value));
        var sameShape = Assert.IsType<Expr.Call>(Assert.Single(PropertyOf(root, "SameShape").Value.Output));
        Assert.IsType<Expr.ListLiteral>(Assert.Single(sameShape.Args));

        // "`Explicit(x) = Single(x)` passes its whole argument `x` as Single's list argument".
        Assert.Equal("x", Signature(PropertyOf(root, "Explicit").Value));
        var explicitCall = Assert.IsType<Expr.Call>(Assert.Single(PropertyOf(root, "Explicit").Value.Output));
        Assert.Equal("x", Assert.IsType<Expr.Param>(Assert.Single(explicitCall.Args)).Name);

        // "`Construct = Single([x])` ... its parameter `x` comes from the `[x]` written in it, and it
        // builds the list before calling `Single`".
        Assert.Equal("x", Signature(PropertyOf(root, "Construct").Value));
        var construct = Assert.IsType<Expr.Call>(Assert.Single(PropertyOf(root, "Construct").Value.Output));
        Assert.IsType<Expr.ListLiteral>(Assert.Single(construct.Args));

        // "`Bad(x) = Single` is an error ... write `Bad(x) = Single(x)` ... or ... `Bad([x]) = Single`".
        FrontEndRejection(SingleFormula + "Bad(x) = Single\n\nBad([7])",
            DiagnosticCode.UnforwardableParameter, KatLangErrorCode.UnforwardableParameter);
        Assert.Equal("7", Display(SingleFormula + "Bad(x) = Single(x)\n\nBad([7])"));
        Assert.Equal("7", Display(SingleFormula + "Bad([x]) = Single\n\nBad([7])"));

        // "`Pair(a, b) = Add` is an error ... `Pair((a, b)) = Add` forwards the pair, and
        // `Pair(a, b) = Add((a, b))` builds it".
        const string add = "Add((a, b)) = a + b\n";
        FrontEndRejection(add + "Pair(a, b) = Add\n\nPair(2, 3)",
            DiagnosticCode.UnforwardableParameter, KatLangErrorCode.UnforwardableParameter);
        Assert.Equal("5", Display(add + "Pair((a, b)) = Add\n\nPair((2, 3))"));
        Assert.Equal("5", Display(add + "Pair(a, b) = Add((a, b))\n\nPair(2, 3)"));

        // "`Many(*vs) = Coll` with `Coll(*vs) = vs` means `Coll(vs*)`".
        Assert.Equal("[1, 2]", Display("Coll(*vs) = vs\nMany(*vs) = Coll\n\nMany(1, 2)"));
    }

    [Fact]
    public void AliasesForwardingAndExplicitCalls_RenamingAffectsEachFormAsTheTutorialStates()
    {
        const string original = "Double(x) = x * 2\n";
        const string renamed = "Double(value) = value * 2\n";

        // "An alias takes the new names with it, and a formula that uses it takes them as its inputs."
        Assert.Equal("value", AliasTargetSignature(PropertyOf(SourceProvenance.ParseValid(renamed + "Alias = Double\n\n0").Root, "Alias").Value));
        Assert.Equal(["value"], PropertyOf(SourceProvenance.ParseValid(renamed + "Formula = Double + 1\n\n0").Root, "Formula").Value.Params);

        // "Forwarding by name must be updated to match, or it becomes an error."
        Assert.Equal("10", Display(original + "Forward(x) = Double\n\nForward(5)"));
        FrontEndRejection(renamed + "Forward(x) = Double\n\nForward(5)",
            DiagnosticCode.UnforwardableParameter, KatLangErrorCode.UnforwardableParameter);

        // "An explicit call is unaffected ... renaming `Add`'s parameters to `left` and `right` changes
        // nothing about `G`".
        foreach (var callee in new[] { original, renamed })
            Assert.Equal("10", Display(callee + "Explicit(x) = Double(x)\n\nExplicit(5)"));
        foreach (var callee in new[] { "Add((a, b)) = a + b\n", "Add((left, right)) = left + right\n" })
        {
            var g = PropertyOf(SourceProvenance.ParseValid(callee + "G = Add((x, y))\n\nG(2, 3)").Root, "G").Value;
            Assert.Equal(["x", "y"], g.Params);
            Assert.Equal("5", Display(callee + "G = Add((x, y))\n\nG(2, 3)"));
        }
    }

    // ── "Members Come First", "Callbacks Receive One Element": which names an inferred signature takes ──

    [Fact]
    public void InferredParameters_NameInsideBracesBelongsToTheBraces_AndAnUndefinedMemberOfAnInferredReceiverIsInferred()
    {
        // `factor` appears only inside the callback, so it is the callback's parameter, never Scale's ...
        const string inferredScale = "Scale = values.map{n * factor}\n\nScale([1, 2, 3], 10)";
        Assert.Equal(["values"], PropertyOf(SourceProvenance.ParseValid(inferredScale).Root, "Scale").Value.Params);
        RunFailure(inferredScale, KatLangErrorCode.ArityMismatch);
        RunFailure("Scale = values.map{n * factor}\n\nScale([1, 2, 3])", KatLangErrorCode.ArityMismatch);
        // ... and once the outer list declares it, the name inside the braces is that parameter.
        Assert.Equal("[10, 20, 30]", Display("Scale(values, factor) = values.map{n * factor}\n\nScale([1, 2, 3], 10)"));

        // An inferred receiver might lack the member, so an otherwise undefined member name is inferred too ...
        const string box = "Box = {\n    public V = 5\n}\n\n";
        const string inferredArea = "Area = shape.V * 2\n" + box + "Area(Box)";
        Assert.Equal(["shape", "V"], PropertyOf(SourceProvenance.ParseValid(inferredArea).Root, "Area").Value.Params);
        RunFailure(inferredArea, KatLangErrorCode.ArityMismatch);
        // ... but not when something named `V` is defined, nor under an explicit list, which settles
        // only the signature (the next test shows that the dot rule is unchanged).
        Assert.Equal(["shape"], PropertyOf(SourceProvenance.ParseValid("V = 3\nArea = shape.V * 2\n" + box + "Area(Box)").Root, "Area").Value.Params);
        Assert.Equal("10", Display("Area(shape) = shape.V * 2\n" + box + "Area(Box)"));
    }

    [Fact]
    public void ExplicitParameterList_KeepsTheMemberNameOutOfTheSignature_WithoutMakingTheDotMemberOnly()
    {
        // `V` is not a parameter of Area, yet `shape.V` keeps the ordinary dot rule: a receiver without
        // the member falls back to the lexical `V` (`5.V` is `V(5)`, so `Area(5)` is 12, where a
        // member-only dot would fail), and a receiver with the member still takes the member.
        const string source =
            "V(x) = x + 1\nArea(shape) = shape.V * 2\nBox = {\n    public V = 5\n}\n\nArea(5)\nArea(Box)";
        Assert.Equal(["shape"], PropertyOf(SourceProvenance.ParseValid(source).Root, "Area").Value.Params);
        Assert.Equal("12\n10", Display(source));
    }

    // ── "How Names Are Found", "Public Members and open": own definitions, then built-ins, then opened names ──

    [Fact]
    public void LookupOrder_OwnDefinitionsThenBuiltinNamesThenOpenedNames()
    {
        const string library = "Lib = {\n    public pi = 3\n    public Tau = 6\n}\n";

        // An opened name never overrides a built-in one ...
        Assert.Equal(Display("pi"), Display("open Lib\n" + library + "pi"));
        // ... it only supplies a name that nothing else provides ...
        Assert.Equal("6", Display("open Lib\n" + library + "Tau"));
        // ... while a definition of your own takes precedence over the built-in name.
        Assert.Equal("3\n8", Display("pi = 3\ncount(x) = x + 1\n\npi\ncount(7)"));
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
    // "Reordering Parameters with Grace": equal-weight runs among zero-weight names (X-49).
    [InlineData("Prefixed = s * 100 + ~x * 10 + ~y", new[] { "x", "y", "s" })]
    [InlineData("Postfixed = s~ * 100 + x~ * 10 + y", new[] { "y", "s", "x" })]
    [InlineData("K = a~ * 1000 + b~ * 100 + ~c * 10 + ~d", new[] { "c", "a", "d", "b" })]
    public void Grace_WeightsAccumulatePerName_AndReorderTheInferredSignature(string definition, string[] expected)
    {
        Assert.Equal(expected, InferredParams(definition));
    }

    [Fact]
    public void Grace_OtherMovingNamesCanSplitEqualWeightRuns()
        => Assert.Equal("2413", Display("K = a~ * 1000 + b~ * 100 + ~c * 10 + ~d\nK(1, 2, 3, 4)"));

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
        Assert.Equal(1, Assert.NotNull(diagnostic.Span).Start.Line);
        Assert.Equal(14, Assert.NotNull(diagnostic.Span).Start.Column);
    }

    // "Reordering Parameters with Grace": a marker on an inferred parameter is legal even when
    // the name cannot move (Q-16(1) E) — the contract is the inferred list, which keeps its order.
    [Theory]
    [InlineData("F = ~x + 1", new[] { "x" })]
    [InlineData("K = ~a + b * 10", new[] { "a", "b" })]
    [InlineData("K = a + b~ * 10", new[] { "a", "b" })]
    public void Grace_ThatCannotMoveItsName_IsLegal_AndKeepsTheOrder(string definition, string[] expected)
    {
        Assert.Equal(expected, InferredParams(definition));
    }

    [Fact]
    public void Grace_NeverCrossesIntoTheNamesAFormulaLifts()
    {
        // A formula's own inferred names always come first; Grace orders only those.
        var root = SourceProvenance.ParseValid("A = p - q\nG = A - z~").Root;
        Assert.Equal(["z", "p", "q"], PropertyOf(root, "G").Value.Params);
    }

    // "Reordering Parameters with Grace" — clauses (Q-16(2) O): a clause branch's own level
    // infers nothing, but a `{ … }` algorithm inside the branch infers — and orders — its own.
    [Fact]
    public void Grace_InABlockInsideAClause_OrdersTheBlocksOwnParameters_NotTheClauses()
    {
        var root = SourceProvenance.ParseValid("Apply(f) = f(1, 10)\nF(0) = Apply({ y - ~x })").Root;
        var family = Assert.IsType<Algorithm.Conditional>(PropertyOf(root, "F").Value);
        var branch = Assert.IsType<Algorithm.User>(Assert.Single(family.Branches).Body);
        Assert.Empty(branch.Params);
        var call = Assert.IsType<Expr.Call>(Assert.Single(branch.Output));
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(call.Args));
        Assert.Equal(["x", "y"], block.Algorithm.Params);
        Assert.Equal("9", Display("Apply(f) = f(1, 10)\nF(0) = Apply({ y - ~x })\nF(0)"));
    }

    [Fact]
    public void Grace_OnAClausesOwnLevel_IsAStructuredFrontEndError_AtTheMarker()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("F(0) = 0\nF(n) = ~n + 1\nF(1)");
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 8, 2, 10), diagnostic.Span);
    }
}
