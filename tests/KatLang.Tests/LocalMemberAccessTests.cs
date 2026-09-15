using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// K1-08 (September 2026): a <see cref="PropertyExposure.LocalOnlyCapturedAncestorParameters"/>
/// member is LOCAL-CONTEXT-DEPENDENT, never universally hidden. The ONE accessibility law
/// (<c>Evaluator.IsAccessibleFrom</c>, Lean <c>memberAccessible?</c>) admits an access exactly
/// when the site — the algorithm whose body is being evaluated — lies inside the owner of every
/// parameter the member captures (<see cref="Property.RequiredAncestorParameters"/>), the owner
/// retained by semantic identity across shadowing and repeated activations. Structural dot access, dotted <c>open</c> paths, and <c>open</c>-provided names
/// SELECT by declaration/visibility alone and apply the law afterwards, so the front end, the
/// editor, the sync evaluator, and the async twin all agree on what a name selects.
///
/// <para>The open PROVIDER rule is separate: an algorithm that requires arguments (explicit or
/// inferred parameters, or a clause family) cannot be opened at all — a front-end
/// <see cref="DiagnosticCode.IllegalInOpen"/> at the open target, and <c>illegalInOpen</c> at
/// open resolution in both engines.</para>
/// </summary>
public class LocalMemberAccessTests
{
    [Theory]
    [InlineData("n")]
    [InlineData("m")]
    public async Task NavigatedOpenCapture_PreservesOwnerAndCallBoundary(string outerParameter)
    {
        var source = $"Outer({outerParameter}) = {{\n Mid(n) = {{ public Lib = {{ public X = n }}\n 0 }}\n P = if(0, {{ open Mid.Lib\n X }}, 10)\n Read = Outer.P\n Read\n}}\nOuter(5)";
        RunFailure(source, KatLangErrorCode.LocalOnlyProperty);
        await AssertSyncAndAsyncAgree(source);
        var inside = $"Outer({outerParameter}) = {{\n public Mid(n) = {{ public Lib = {{ public X = n }}\n Read = {{ open Outer.Mid.Lib\n X }}\n Read }}\n Mid(7)\n}}\nOuter(5)";
        Assert.Equal("7", Display(inside));
        await AssertSyncAndAsyncAgree(inside);
    }

    [Theory]
    [InlineData("n")]
    [InlineData("m")]
    public async Task NavigatedCapture_CannotBeReownedByAnUnusedSameNamedParameter(string outerParameter)
    {
        var source = $"Outer({outerParameter}) = {{\n Mid(n) = {{ public X = n\n 0 }}\n P = if(0, Mid.X, 10)\n Read = Outer.P\n Read\n}}\nOuter(5)";
        var p = NestedProperty(SourceProvenance.ParseValid(source).Root, "Outer", "P");
        Assert.Equal([new CapturedParameterRequirement("n", -1)], p.CaptureRequirements);
        RunFailure(source, KatLangErrorCode.LocalOnlyProperty);
        await AssertSyncAndAsyncAgree(source);

        var inside = $"Outer({outerParameter}) = {{\n Mid(n) = {{ public X = n\n Read = Outer.Mid.X\n Read }}\n Mid(7)\n}}\nOuter(5)";
        Assert.Equal("7", Display(inside));
        await AssertSyncAndAsyncAgree(inside);
    }

    [Theory]
    [InlineData("n")]
    [InlineData("0")]
    public async Task PrivateDottedOpenMember_IsRejectedByVisibility(string output)
    {
        var source = $"open Outer.Lib, Pub\nOuter(n) = {{\n Lib = {{ public X = 1\n {output} }}\n 0\n}}\nPub = {{ public Y = 2 }}\nY";
        RunFailure(source, KatLangErrorCode.NotPublicProperty);
        await AssertSyncAndAsyncAgree(source);
    }

    [Fact]
    public async Task OpenAndDot_DoNotEvaluateTheNamedProvidersOutput()
    {
        const string source = "Outer(n) = {\n Lib = { public X = 10\n n }\n P = { open Lib\n X }\n Q = Lib.X\n 0\n}\nOuter.P, Outer.Q";
        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(PropertyExposure.Exported, NestedProperty(root, "Outer", "P").Exposure);
        Assert.Equal(PropertyExposure.Exported, NestedProperty(root, "Outer", "Q").Exposure);
        Assert.Equal("10\n10", Display(source));
        await AssertSyncAndAsyncAgree(source);
    }

    [Fact]
    public void PropertyValueRewrite_PreservesTransitiveCaptureOwner()
    {
        const string source = "Outer(n) = {\n Q = n\n Mid(n) = { public X = Q\n 0 }\n Mid.X\n}\nOuter(5)";
        static Algorithm Rewrite(Algorithm algorithm) => algorithm is Algorithm.User user
            ? user with { Properties = user.Properties.Select(p => p.WithValue(Rewrite(p.Value))).ToArray() }
            : algorithm;
        var rewritten = Rewrite(SourceProvenance.ParseValid(source).Root);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(rewritten));
        Assert.False(result.IsError);
        Assert.Equal(new Result.Atom(5), result.Value);
    }

    [Theory]
    [InlineData("Outer(n) = {\n Lib = { public X = n }\n Step(n) = Lib.X + n\n repeat(Step, 2, 0)\n}\nOuter(5), Outer(7)", "10\n14")]
    [InlineData("Inc(x) = x + 1\nTen(x) = x * 10\nOuter(f) = {\n Lib = { public X = f(2) }\n Read(f) = Lib.X\n Read(Ten)\n}\nOuter(Inc)", "3")]
    public async Task CaptureOwnerBinding_SurvivesLoopsAndAlgorithmChannelShadowing(string source, string expected)
    {
        Assert.Equal(expected, Display(source));
        await AssertSyncAndAsyncAgree(source);
    }

    [Theory]
    [InlineData("Mid.X")]
    [InlineData("Mid(7)")]
    public async Task TransitiveCapture_RetainsOwnerAcrossSameNamedBinder(string access)
    {
        var source = $"Outer(n) = {{\n Q = n\n Mid(n) = {{\n public X = Q\n X\n }}\n {access}\n}}\nOuter(5), Outer(9)";
        Assert.Equal("5\n9", Display(source));
        var member = NestedProperty(SourceProvenance.ParseValid(source).Root, "Outer", "Mid", "X");
        Assert.Equal([new CapturedParameterRequirement("n", 1)], member.CaptureRequirements);
        await AssertSyncAndAsyncAgree(source);
    }

    [Fact]
    public async Task CaptureOfTwoSameNamedOwners_RequiresBothActivations()
    {
        const string prefix = "Outer(n) = {\n Q = n\n Mid(n) = {\n public X = Q + n\n X\n }\n";
        Assert.Equal("12", Display(prefix + "Mid(7)\n}\nOuter(5)"));
        var source = prefix + "Mid.X\n}\nOuter(5)";
        RunFailure(source, KatLangErrorCode.LocalOnlyProperty);
        var member = NestedProperty(SourceProvenance.ParseValid(source).Root, "Outer", "Mid", "X");
        Assert.Equal([new CapturedParameterRequirement("n", 0), new CapturedParameterRequirement("n", 1)], member.CaptureRequirements);
        await AssertSyncAndAsyncAgree(source);
    }

    [Theory]
    [InlineData("Inner.X")]
    [InlineData("{ open Inner\n X }")]
    public async Task ShadowingCallee_CannotReplaceCapturedOwnerBinding(string access)
    {
        var source = $"Outer(n) = {{\n Inner = {{ public X = n }}\n Read(n) = {access}\n Read(7)\n}}\nOuter(5), Outer(9)";
        Assert.Equal("5\n9", Display(source));
        await AssertSyncAndAsyncAgree(source);
    }

    [Theory]
    [InlineData("H(f, k) = {\n F(0) = 0\n F(n) = H({ public X = n }, 0)\n G(0) = 0\n G(n) = f.X\n if(k, F(k), G(7))\n}\nH({ public X = 0 }, 5)")]
    [InlineData("H(f, n) = if(n, H({ public X = n }, 0), f.X)\nH({ public X = 0 }, 5)")]
    public async Task CapturedProvider_CannotEnterAnotherOwnerActivation(string source)
    {
        RunFailure(source, KatLangErrorCode.LocalOnlyProperty);
        await AssertSyncAndAsyncAgree(source);
    }

    private static string Display(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n");

    private static KatLangError RunFailure(string source, KatLangErrorCode code)
    {
        SourceProvenance.ParseValid(source);
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(code, error.Code);
        return error;
    }

    private static Diagnostic FrontEndRejection(string source, DiagnosticCode code)
    {
        var diagnostic = Assert.Single(SourceProvenance.ParseAllowingDiagnostics(source).Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(code, diagnostic.Code);
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Equal(KatLangError.MapDiagnosticCode(code), Assert.Single(failure.Errors).Code);
        return diagnostic;
    }

    private static Property NestedProperty(Algorithm root, params string[] path)
    {
        var current = root;
        Property? property = null;
        foreach (var name in path)
        {
            property = Assert.Single(current.Properties, candidate => candidate.Name == name);
            current = property.Value;
        }

        return property!;
    }

    private static async Task AssertSyncAndAsyncAgree(string source)
    {
        var sync = KatLangEngine.Run(source);
        var asyncResult = await KatLangEngine.RunAsync(source);
        Assert.Equal(sync.GetType(), asyncResult.GetType());
        Assert.Equal(sync.ToDisplayString(), asyncResult.ToDisplayString());
    }

    // ── A/B: the decisive programs ──────────────────────────────────────────

    private const string DirectStructuralCapture = "Outer(n) = {\n    Inner = {\n        public X = n\n    }\n\n    Inner.X\n}\n\nOuter(5)";

    private const string DirectOpenCapture = "Outer(n) = {\n    open Inner\n\n    Inner = {\n        public X = n\n    }\n\n    X + 0\n}\n\nOuter(5)";

    [Fact]
    public async Task DirectLocalStructuralCapture_IsValidInsideTheOwner()
    {
        var root = SourceProvenance.ParseValid(DirectStructuralCapture).Root;
        var x = NestedProperty(root, "Outer", "Inner", "X");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, x.Exposure);
        Assert.Equal(["n"], x.RequiredAncestorParameters);
        // Inner has no output that reads n: it is a self-contained namespace.
        Assert.Equal(PropertyExposure.Exported, NestedProperty(root, "Outer", "Inner").Exposure);

        Assert.Equal("5", Display(DirectStructuralCapture));
        await AssertSyncAndAsyncAgree(DirectStructuralCapture);
    }

    [Fact]
    public async Task DirectLocalOpenCapture_IsValidInsideTheOwner()
    {
        var root = SourceProvenance.ParseValid(DirectOpenCapture).Root;
        Assert.Equal(["n"], NestedProperty(root, "Outer", "Inner", "X").RequiredAncestorParameters);
        // The reference stays an ordinary lexical resolution; nothing is promoted.
        Assert.Equal(["n"], NestedProperty(root, "Outer").Value.Params);

        Assert.Equal("5", Display(DirectOpenCapture));
        await AssertSyncAndAsyncAgree(DirectOpenCapture);
    }

    // ── C: ordinary exported provider is unchanged ───────────────────────────

    [Fact]
    public void OrdinaryExportedProvider_IsUnchanged()
        => Assert.Equal("10", Display("Lib = {\n    public X = 10\n}\n\nA = {\n    open Lib\n    X\n}\n\nA"));

    // ── D/E/F: a provider that requires arguments cannot be opened ───────────

    [Theory]
    [InlineData("Lib(p) = {\n    public X = p + 101\n    X\n}\n\nA = {\n    open Lib\n    X\n}\n\nA", "'Lib' cannot be opened because it requires arguments (p)")]
    [InlineData("Lib(p, q) = {\n    public X = p + q\n    X\n}\n\nA = {\n    open Lib\n    X\n}\n\nA", "'Lib' cannot be opened because it requires arguments (p, q)")]
    [InlineData("Lib(p) = p\nAlias = Lib\nA = { open Alias\n 1 }\nA", "'Alias' cannot be opened because it requires arguments (p)")]
    [InlineData("Lib(p) = p\nA(p) = { open Lib\n p }\nA(1)", "'Lib' cannot be opened because it requires arguments (p)")]
    [InlineData("Lib = { public Sub(p) = p }\nA = { open Lib.Sub\n 1 }\nA", "'Lib.Sub' cannot be opened because it requires arguments (p)")]
    // Inferred: Lib's output row makes `p` Lib's own parameter.
    [InlineData("Lib = {\n    public X = 1\n    p + 1\n}\n\nA = {\n    open Lib\n    X\n}\n\nA", "'Lib' cannot be opened because it requires arguments (p)")]
    // A clause family always takes arguments.
    [InlineData("F(0) = 1\nF(n) = 2\nA = {\n    open F\n    7\n}\nA", "'F' cannot be opened because it is a clause family that requires arguments")]
    // The rule holds without any member being referenced.
    [InlineData("Lib(p) = {\n    public X = p + 101\n    X\n}\n\nA = {\n    open Lib\n    7\n}\n\nA", "'Lib' cannot be opened because it requires arguments (p)")]
    public void ParameterizedProvider_IsRefusedAtTheOpenTarget(string source, string fragment)
    {
        var diagnostic = FrontEndRejection(source, DiagnosticCode.IllegalInOpen);
        Assert.Contains(fragment, diagnostic.Message, StringComparison.Ordinal);
        // Reported at the open target's own span, never at a later member.
        Assert.Contains("open ", source.Split('\n')[diagnostic.Span.StartLineNumber - 1], StringComparison.Ordinal);
    }

    [Fact]
    public void ParameterizedProvider_IsRefusedByTheEvaluatorToo()
    {
        // The unelaborated tree reaches the evaluator's own open resolution.
        var raw = SourceProvenance.ParseSyntaxValidRoot("Lib(p) = {\n    public X = p + 101\n    X\n}\nA = {\n    open Lib\n    X\n}\nA");
        var result = Evaluator.Run(new Expr.AlgorithmExpr(raw));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context) error = context.Inner;
        Assert.Contains("cannot be opened because it requires arguments", Assert.IsType<EvalError.IllegalInOpen>(error).Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void ParameterizedHead_OfADottedTarget_IsNavigatedByIdentity()
    {
        // Only the RESOLVED provider is judged: `Sub` needs no call, so `open Lib.Sub` is legal
        // and its self-contained X is provided...
        const string selfContained = "Lib(p) = {\n    public Sub = {\n        public X = 1\n    }\n    p\n}\n\nA = {\n    open Lib.Sub\n    X\n}\n\nA";
        Assert.Equal("1", Display(selfContained));

        // ...while a member of Sub that captures Lib's p is selected and refused at the access.
        const string capturing = "Lib(p) = {\n    public Sub = {\n        public X = 1\n        public Y = p\n    }\n    p\n}\n\nA = {\n    open Lib.Sub\n    Y\n}\n\nA";
        var error = RunFailure(capturing, KatLangErrorCode.LocalOnlyProperty);
        Assert.Contains("Property 'Y' on `Lib.Sub` is local-only because it depends on parameter 'p'", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("Mid(q) =", "q", "Lib.Mid.Sub.X")]
    [InlineData("Mid =", "q", "{ open Lib.Mid.Sub\n X }")]
    [InlineData("Mid(q) =", "q", "{ open Lib.Mid.Sub\n X }")]
    public async Task NestedParameterizedIntermediates_AreStaticNavigation(string mid, string output, string access)
    {
        var source = $"Lib(p) = {{\n public {mid} {{\n public Sub = {{ public X = 10 }}\n {output}\n }}\n p\n}}\n{access}";
        Assert.Equal("10", Display(source));
        await AssertSyncAndAsyncAgree(source);
    }

    // ── G: private members stay unavailable through open ────────────────────

    [Fact]
    public void PrivateMember_IsStillNotProvidedByOpen()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("Outer(n) = {\n    open Inner\n    Inner = {\n        X = n\n    }\n    X\n}\n\nOuter(5)");
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
    }

    // ── H: the external boundary ─────────────────────────────────────────────

    [Theory]
    [InlineData("Outer(n) = {\n    Inner = {\n        public X = n\n    }\n    Inner.X\n}\n\nOuter.Inner.X")]
    [InlineData("Outer(n) = {\n    public Inner = {\n        public X = n\n    }\n    Inner.X\n}\n\nopen Outer.Inner\nX")]
    // A live binding of the same name in an unrelated algorithm never counts: the rule is lexical.
    [InlineData("Outer(n) = {\n    Inner = {\n        public X = n\n    }\n    G(7)\n}\nG(n) = Outer.Inner.X\n\nOuter(5)")]
    // Handing the container out on the algorithm channel to a body outside Outer.
    [InlineData("Apply(f) = f.X\nOuter(n) = {\n    Inner = { public X = n }\n    Apply(Inner)\n}\nOuter(5)")]
    // Forwarded one hop further out: the reading body is still written outside Outer.
    [InlineData("Apply(f) = Read(f)\nRead(g) = g.X\nOuter(n) = {\n    Inner = { public X = n }\n    Apply(Inner)\n}\nOuter(5)")]
    public async Task CapturedMember_CannotEscapeItsOwner(string source)
    {
        var error = RunFailure(source, KatLangErrorCode.LocalOnlyProperty);
        Assert.Contains("depends on parameter 'n', and a required owner activation is unavailable in this lexical context", error.Message, StringComparison.Ordinal);
        await AssertSyncAndAsyncAgree(source);
    }

    [Fact]
    public void CapturedMember_OwnerIsTheNearestBinderOfTheCapturedName()
    {
        // X inside Mid(n) captures MID's n. A site inside Outer but outside Mid is refused even
        // though Outer binds a same-named n; a site inside Mid is admitted.
        const string outsideMid = "Outer(n) = {\n    Mid(n) = {\n        Inner = {\n            public X = n\n        }\n        0\n    }\n    Mid.Inner.X\n}\n\nOuter(5)";
        RunFailure(outsideMid, KatLangErrorCode.LocalOnlyProperty);

        const string insideMid = "Outer(n) = {\n    Mid(n) = {\n        Inner = {\n            public X = n\n        }\n        Inner.X\n    }\n    Mid(3)\n}\n\nOuter(5)";
        Assert.Equal("3", Display(insideMid));
    }

    [Fact]
    public async Task CapturedBlockMember_CannotEscapeIntoASameShapedCallee()
    {
        // A block captures its writer's declaration and activation, never a same-shaped callee.
        const string source = "Take(n, m) = n.X\nOuter(n, m) = {\n    Take({ public X = m }, n)\n}\nOuter(5, 7)";
        var error = RunFailure(source, KatLangErrorCode.LocalOnlyProperty);
        Assert.Contains("depends on parameter 'm', and a required owner activation is unavailable", error.Message, StringComparison.Ordinal);
        await AssertSyncAndAsyncAgree(source);

        // The one-parameter twin, where the callee's own binding of the captured name is the
        // container itself.
        RunFailure("Read(n) = n.X\nOuter(n) = {\n    Read({ public X = n })\n}\nOuter(5)", KatLangErrorCode.LocalOnlyProperty);

        // The control: written INSIDE Outer, the same block-captured member is reachable.
        Assert.Equal("7", Display("Outer(n, m) = {\n    Take(f, k) = f.X\n    Take({ public X = m }, n)\n}\nOuter(5, 7)"));
    }

    [Fact]
    public async Task StaticNestedProvider_KeepsItsCapturedAncestorActivation()
    {
        const string source = "Outer(f, k) = {\n    Lib(n) = {\n        public X = n\n        f.X\n    }\n    if(k, Outer(Lib, 0), Lib(7))\n}\nOuter({ public X = 0 }, 1)";
        RunFailure(source, KatLangErrorCode.LocalOnlyProperty);
        await AssertSyncAndAsyncAgree(source);
    }

    // ── I: transitive capture ────────────────────────────────────────────────

    [Fact]
    public async Task TransitiveCapture_KeepsProvenance()
    {
        const string inside = "Outer(n) = {\n    Helper = n + 1\n    Inner = {\n        public X = Helper\n    }\n\n    Inner.X, { open Inner\n        X }\n}\n\nOuter(5)";
        var root = SourceProvenance.ParseValid(inside).Root;
        Assert.Equal(["n"], NestedProperty(root, "Outer", "Inner", "X").RequiredAncestorParameters);
        Assert.Equal("(6, 6)", Display(inside));
        await AssertSyncAndAsyncAgree(inside);

        RunFailure("Outer(n) = {\n    Helper = n + 1\n    Inner = {\n        public X = Helper\n    }\n    Inner.X\n}\nOuter(5), Outer.Inner.X", KatLangErrorCode.LocalOnlyProperty);
    }

    // ── J: sibling scopes under the same activation ──────────────────────────

    [Theory]
    [InlineData("Outer(n) = {\n    Left = {\n        public X = n\n    }\n\n    Right = {\n        open Left\n        X\n    }\n\n    Right\n}\n\nOuter(5)")]
    [InlineData("Outer(n) = {\n    Left = {\n        public X = n\n    }\n\n    Right = {\n        Left.X\n    }\n\n    Right\n}\n\nOuter(5)")]
    // A callee written INSIDE Outer is inside the owner even when handed the container.
    [InlineData("Outer(n) = {\n    Inner = { public X = n }\n    Apply(f) = f.X\n    Apply(Inner)\n}\nOuter(5)")]
    // A block literal and a callback block are wired under the body that writes them.
    [InlineData("Outer(n) = {\n    Inner = { public X = n }\n    { Inner.X }\n}\nOuter(5)")]
    [InlineData("Outer(n) = {\n    Inner = { public X = n }\n    [1].map({ Inner.X * e })*\n}\nOuter(5)")]
    public async Task SiblingAndNestedScopes_UnderTheSameActivation_ReachTheMember(string source)
    {
        Assert.Equal("5", Display(source));
        await AssertSyncAndAsyncAgree(source);
    }

    [Fact]
    public void BranchBinderCapture_IsReachableInsideTheBranch_AndRefusedOutsideIt()
    {
        Assert.Equal("10", Display("F(0) = 0\nF(n) = {\n    Lib = { public X = n }\n    G = {\n        open Lib\n        X\n    }\n    G + Lib.X\n}\nF(5)"));
        // Outside the branch a family exposes no members at all (unchanged).
        RunFailure("F(0) = 0\nF(n) = {\n    public Lib = { public X = n }\n    Lib.X\n}\nF.Lib", KatLangErrorCode.LocalOnlyProperty);
    }

    // ── K/L: precedence and provider selection are unchanged ─────────────────

    [Fact]
    public void OwnedDeclarations_StillBeatProvidedMembers()
        => Assert.Equal("100", Display("Outer(n) = {\n    open Inner\n    X = 100\n    Inner = { public X = n }\n    X\n}\nOuter(5)"));

    [Fact]
    public void NearerAndFartherProviders_KeepTheirOrder()
        => Assert.Equal("(5, 7)", Display("Far = { public X = 7 }\nOuter(n) = {\n    open Far\n    Inner = { public X = n }\n    Q = { open Inner\n        X }\n    Q, X\n}\nOuter(5)"));

    [Fact]
    public void PublicLocalOnlyMember_IsASecondProvider()
        // Selection is by visibility: the local-only X is provided and makes the name ambiguous.
        => RunFailure("Pub = {\n    public X = 101\n}\nOuter(p) = {\n    public Lib = {\n        public X = p + 202\n    }\n    0\n}\nA = {\n    open Pub, Outer.Lib\n    X\n}\nA", KatLangErrorCode.AmbiguousOpen);

    // ── Exposure of containers that read captured members ────────────────────

    [Fact]
    public void ContainerReadingACapturedMember_IsLocalOnly_SoActivationsNeverShareIt()
    {
        const string source = "Outer(n) = {\n    Inner = {\n        public X = n\n    }\n    P = Inner.X\n    Q = { open Inner\n        X }\n    P, Q\n}\n\nOuter(1), Outer(2)";
        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(["n"], NestedProperty(root, "Outer", "P").RequiredAncestorParameters);
        Assert.Equal(["n"], NestedProperty(root, "Outer", "Q").RequiredAncestorParameters);
        Assert.Equal("(1, 1)\n(2, 2)", Display(source));
    }

    [Fact]
    public void BlockLocalProvider_ChargesTheCaptureThroughItsOpen()
    {
        const string source = "Outer(n) = {\n    P = {\n        open Inner\n        Inner = { public X = n }\n        X\n    }\n    P\n}\nOuter(1), Outer(2)";
        Assert.Equal(["n"], NestedProperty(SourceProvenance.ParseValid(source).Root, "Outer", "P").RequiredAncestorParameters);
        Assert.Equal("1\n2", Display(source));
    }

    /// <summary>
    /// Final audit (September 2026): a SIBLING property reading a captured member through an
    /// <c>open</c> declared at the property's own declaring level (or an ancestor level) —
    /// not inside the property's value — was classified Exported, so the run-scoped cache
    /// returned the first activation's value to every later one (`4, 4` instead of `4, 5`).
    /// A bare opened name is settled exactly like a dotted path or an open written inside the
    /// value: the provided member's requirements make the reader local-only.
    /// </summary>
    [Theory]
    [InlineData("Outer(p) = {\n    open Lib\n    Lib = { public X = p }\n    Y = X\n    Y\n}\nOuter(4), Outer(5)")]
    [InlineData("Outer(p) = {\n    open Lib\n    Lib = { public X = p }\n    Y = X + 0\n    Y\n}\nOuter(4), Outer(5)")]
    [InlineData("Outer(p) = {\n    open Lib\n    Lib = { public X = p }\n    Y = { X }\n    Y\n}\nOuter(4), Outer(5)")]
    [InlineData("Outer(p) = {\n    open Lib\n    Lib = { public X = p }\n    Y = X\n    Z = Y\n    Z\n}\nOuter(4), Outer(5)")]
    public async Task SiblingReadingAnOpenProvidedCapturedMember_IsLocalOnly(string source)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var reader = NestedProperty(root, "Outer", "Y");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, reader.Exposure);
        Assert.Equal(["p"], reader.RequiredAncestorParameters);
        Assert.Equal("4\n5", Display(source));
        await AssertSyncAndAsyncAgree(source);
        await AssertCaptureRepairThroughSuspendingTwin(source);
    }

    /// <summary>
    /// Final hostile pass (September 2026): an <c>open</c> target whose head is declared at a
    /// level BETWEEN the opener and the settling level. The opener (Inner) carries the head
    /// outward unresolved; the level that declares it (Mid) must settle it there — exactly as
    /// the opener would have settled its own head — so the provided member's capture of
    /// <c>p</c> charges Inner and Mid. The candidate used to be carried PAST its declaration,
    /// Mid was classified exported, and the run cache served the first activation's value to
    /// every later call (<c>Outer(1), Outer(2)</c> displayed <c>1 1</c>).
    /// </summary>
    [Theory]
    [InlineData("Outer(p) = {\n    Mid = {\n        Lib = { public X = p }\n        Inner = {\n            open Lib\n            X\n        }\n        Inner\n    }\n    Mid\n}\nOuter(1), Outer(2)")]
    // Dotted target: the head is at Mid, the public step selects the provider.
    [InlineData("Outer(p) = {\n    Mid = {\n        Lib = { public Sub = { public X = p } }\n        Inner = {\n            open Lib.Sub\n            X\n        }\n        Inner\n    }\n    Mid\n}\nOuter(1), Outer(2)")]
    // A sibling reading the opened name inside the opener.
    [InlineData("Outer(p) = {\n    Mid = {\n        Lib = { public X = p }\n        Inner = {\n            open Lib\n            Y = X\n            Y\n        }\n        Inner\n    }\n    Mid\n}\nOuter(1), Outer(2)")]
    // One level deeper between the opener and the head.
    [InlineData("Outer(p) = {\n    Mid = {\n        Lib = { public X = p }\n        Deep = {\n            Inner = {\n                open Lib\n                X\n            }\n            Inner\n        }\n        Deep\n    }\n    Mid\n}\nOuter(1), Outer(2)")]
    // The head is declared AFTER the opener in the same body.
    [InlineData("Outer(p) = {\n    Mid = {\n        Inner = {\n            open Lib\n            X\n        }\n        Lib = { public X = p }\n        Inner\n    }\n    Mid\n}\nOuter(1), Outer(2)")]
    public async Task OpenTargetHeadDeclaredBetweenTheOpenerAndTheSettlingLevel_ChargesTheCapture(string source)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var mid = NestedProperty(root, "Outer", "Mid");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, mid.Exposure);
        Assert.Equal(["p"], mid.RequiredAncestorParameters);
        Assert.Equal("1\n2", Display(source));
        await AssertSyncAndAsyncAgree(source);
        await AssertCaptureRepairThroughSuspendingTwin(source);
    }

    private static async Task AssertCaptureRepairThroughSuspendingTwin(string source)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var sync = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        var cache = new AsyncEvaluation.SuspendingAsyncZeroArgPropertyResultCache();
        var twin = await AsyncEvaluation.AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: cache));
        Assert.False(sync.Result.IsError);
        Assert.False(twin.Result.IsError);
        Assert.True(Result.ValueComparer.Equals(sync.Result.Value.Value, twin.Result.Value.Value));
        Assert.Equal(sync.Result.Value.EmittedCount, twin.Result.Value.EmittedCount);
        Assert.True(cache.AsyncAccesses > 0);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Equal(sync.Budget.ConsumedSteps, twin.Budget.ConsumedSteps);
        Assert.Equal(sync.Budget.PeakDepth, twin.Budget.PeakDepth);
        Assert.Equal(sync.Budget.MaterializedItems, twin.Budget.MaterializedItems);
        Assert.Equal(sync.Budget.MaterializedStringChars, twin.Budget.MaterializedStringChars);
        Assert.Equal(0, twin.Budget.CurrentDepth);
    }

    [Fact]
    public async Task OpenTargetHeadDeclaredBetweenTheOpenerAndTheSettlingLevel_NearestDeclarationProvides()
    {
        // The mirror: Mid's own self-contained Lib is the opener's provider (the direct chain
        // reaches it first), never Outer's capturing Lib — so Mid stays exported and is
        // readable from outside the owner.
        const string source = "Outer(p) = {\n    Lib = { public X = p }\n    Mid = {\n        Lib = { public X = 100 }\n        Inner = {\n            open Lib\n            X\n        }\n        Inner\n    }\n    Mid\n}\nOuter.Mid";
        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(PropertyExposure.Exported, NestedProperty(root, "Outer", "Mid").Exposure);
        Assert.Equal("100", Display(source));
        await AssertSyncAndAsyncAgree(source);
    }

    [Fact]
    public async Task NestedSiblingReadingAnAncestorLevelOpenProvidedCapturedMember_IsLocalOnly()
    {
        // The open lives one level ABOVE the reader's declaring level.
        const string source = "Outer(p) = {\n    open Lib\n    Lib = { public X = p }\n    Inner = {\n        Y = X\n        Y\n    }\n    Inner\n}\nOuter(4), Outer(5)";
        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(["p"], NestedProperty(root, "Outer", "Inner", "Y").RequiredAncestorParameters);
        Assert.Equal(["p"], NestedProperty(root, "Outer", "Inner").RequiredAncestorParameters);
        Assert.Equal("4\n5", Display(source));
        await AssertSyncAndAsyncAgree(source);
    }

    [Fact]
    public void SiblingReadingAnOpenProvidedCapturedMember_IsRefusedOutsideTheOwner()
    {
        // The accessibility law applies to the reader exactly as to the provided member:
        // a public sibling that depends on the capture is refused from outside Outer.
        RunFailure(
            "Outer(p) = {\n    open Lib\n    Lib = { public X = p }\n    public Y = X\n    Y\n}\nOuter(4), Outer.Y",
            KatLangErrorCode.LocalOnlyProperty);
    }

    [Fact]
    public void SiblingReadingASelfContainedOpenProvidedMember_StaysExported()
    {
        // The inverse: an opened member that captures nothing charges nothing.
        const string source = "Outer(p) = {\n    open Lib\n    Lib = { public X = 7 }\n    Y = X + p\n    Z = X\n    Y, Z\n}\nOuter(4), Outer(5)";
        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(PropertyExposure.Exported, NestedProperty(root, "Outer", "Z").Exposure);
        Assert.Equal(["p"], NestedProperty(root, "Outer", "Y").RequiredAncestorParameters);
        Assert.Equal("(11, 7)\n(12, 7)", Display(source));
    }

    [Fact]
    public void IdentityNavigation_DoesNotChargeTheReceiversOutput()
    {
        // Inner's OUTPUT captures n, but P only navigates to the self-contained X.
        const string source = "Outer(n) = {\n    Inner = {\n        public X = 1\n        n\n    }\n    P = Inner.X\n    P\n}\nOuter(5)";
        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, NestedProperty(root, "Outer", "Inner").Exposure);
        Assert.Equal(PropertyExposure.Exported, NestedProperty(root, "Outer", "P").Exposure);
        Assert.Equal("1", Display(source));
    }

    // ── Editor and front end select the same declaration ─────────────────────

    [Fact]
    public void Editor_ResolvesTheSelectedDeclaration_InsideAndOutsideTheOwner()
    {
        var inside = SourceProvenance.ParseValid(DirectOpenCapture);
        var model = SemanticModelBuilder.Build(inside.Parsed);
        var reference = model.FindResolutionAt(8, 5);
        Assert.NotNull(reference);
        Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
        Assert.Equal(new SourceSpan(5, 16, 5, 16), reference.ResolvedDeclaration?.Span);

        var outside = SourceProvenance.ParseValid("Outer(n) = {\n    Inner = {\n        public X = n\n    }\n    Inner.X\n}\n\nOuter.Inner.X");
        var outsideModel = SemanticModelBuilder.Build(outside.Parsed);
        var escaped = outsideModel.FindResolutionAt(8, 13);
        Assert.NotNull(escaped);
        Assert.Equal(IdentifierClassification.PropertyReference, escaped.Classification);
        Assert.Equal(new SourceSpan(3, 16, 3, 16), escaped.ResolvedDeclaration?.Span);
    }

    // ── Host-built trees ─────────────────────────────────────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FamilyOwnedOpen_ChargesSelectedMembersInsteadOfProviderOutput(bool captures)
    {
        static Algorithm.User Body(params Expr[] output) => new(null, [], [], [], output);
        var lib = Body(captures ? new Expr.Num(0) : new Expr.Param("n")) with
        {
            Properties = [new Property("X", Body(captures ? new Expr.Param("n") : new Expr.Num(10)), true)],
        };
        var family = new Algorithm.Conditional(null, [new Expr.Resolve("Lib")],
            [new CondBranch(new Pattern.LitInt(0), Body(new Expr.Num(10))),
             new CondBranch(new Pattern.Bind("k"), Body(new Expr.Resolve("X")))]);
        var outer = (Algorithm.User)Body(new Expr.Num(0)).WithParams(["n"]) with
        {
            Properties = [new Property("Lib", lib), new Property("F", family)],
        };
        var root = Body(new Expr.DotCall(new Expr.Resolve("Outer"), "F", [new Expr.Num(0)])) with
        {
            Properties = [new Property("Outer", outer)],
        };
        var elaborated = PropertyExposureResolver.Resolve(root);
        Assert.Equal(captures ? PropertyExposure.LocalOnlyCapturedAncestorParameters : PropertyExposure.Exported,
            NestedProperty(elaborated, "Outer", "F").Exposure);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(elaborated));
        if (captures)
        {
            Assert.True(result.IsError);
            var error = result.Error;
            while (error is EvalError.WithContext context) error = context.Inner;
            Assert.Equal("F", Assert.IsType<EvalError.LocalOnlyProperty>(error).PropertyName);
        }
        else
        {
            Assert.False(result.IsError);
            Assert.Equal(new Result.Atom(10), result.Value);
        }
    }

    [Fact]
    public void SharedOpenBody_IsValidatedInEachLexicalContext()
    {
        var span = new SourceSpan(1, 6, 1, 13);
        var shared = new Algorithm.User(null, [], [new Expr.Resolve("Provider") { Span = span }], [], [new Expr.Num(0)]);
        Algorithm Owner(Algorithm provider) => new Algorithm.User(null, [], [],
            [new Property("Provider", provider), new Property("Body", shared)], [new Expr.Num(0)]);
        var zero = new Algorithm.User(null, [], [], [], [new Expr.Num(0)]);
        var parameterized = new Algorithm.User(null, [new ParameterDeclaration("n")], [], [], [new Expr.Param("n")]);
        var root = new Algorithm.User(null, [], [],
            [new Property("A", Owner(zero)), new Property("B", Owner(parameterized))], [new Expr.Num(0)]);
        var diagnostics = new List<Diagnostic>();
        OpenProviderValidator.Validate(root, diagnostics, (HostOperations?)null);
        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.IllegalInOpen, diagnostic.Code);
        Assert.Equal(span, diagnostic.Span);
    }

    [Fact]
    public void SharedBodyComponents_DoNotMergeDistinctParameterOwners()
    {
        var member = new Property("X", new Algorithm.User(null, [], [], [], [new Expr.Param("n")]), true,
            PropertyExposure.LocalOnlyCapturedAncestorParameters) { RequiredAncestorParameters = ["n"] };
        IReadOnlyList<Property> properties = [member];
        OutputBundle output = [new Expr.DotCall(new Expr.Resolve("G"), "X")];
        var f = new Algorithm.User(null, [new ParameterDeclaration("n")], [], properties, output);
        var g = new Algorithm.User(null, [new ParameterDeclaration("n")], [], properties, output);
        var root = new Algorithm.User(null, [], [], [new Property("F", f), new Property("G", g)],
            [new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(5)])]);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context) error = context.Inner;
        Assert.IsType<EvalError.LocalOnlyProperty>(error);
    }

    [Fact]
    public void HostBuiltLocalOnlyMember_WithoutRequiredNames_StatesNoRequirement()
    {
        // A host that declares LocalOnly but names nothing keeps the local-only cache scope
        // and is accessible everywhere (vacuous requirement).
        var x = new Property("X", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]), IsPublic: true,
            PropertyExposure.LocalOnlyCapturedAncestorParameters);
        var inner = new Property("Inner", new Algorithm.User(null, [], [], [x], []));
        var root = new Algorithm.User(null, [], [], [inner], [new Expr.DotCall(new Expr.Resolve("Inner"), "X")]);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.False(result.IsError);
        Assert.Equal(new Result.Atom(7), result.Value);

        // Naming a parameter nothing binds refuses the access (fail-safe).
        var strict = x with { RequiredAncestorParameters = ["n"] };
        var strictRoot = new Algorithm.User(null, [], [], [new Property("Inner", new Algorithm.User(null, [], [], [strict], []))],
            [new Expr.DotCall(new Expr.Resolve("Inner"), "X")]);
        var refused = Evaluator.Run(new Expr.AlgorithmExpr(strictRoot));
        Assert.True(refused.IsError);
        var error = refused.Error;
        while (error is EvalError.WithContext context) error = context.Inner;
        Assert.Equal(["n"], Assert.IsType<EvalError.LocalOnlyProperty>(error).RequiredParameters);
    }
}
