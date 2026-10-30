namespace KatLang.Tests;

/// <summary>
/// ALIAS-UNIFY-1 (M4★) twelfth independent-review regressions. Source cases run on the six routes of
/// <see cref="SixRouteAgreement"/>; modules run through the engine with an in-memory downloader; the scaling facts compare
/// the passes' own observations (<see cref="FrontEndTraversalObservations"/>) at two sizes. The sibling-order channel
/// orders only the reads it can classify and never one the rewrite does not make; the rewrite processes on demand what
/// the channel leaves unordered (a read that reaches a pending property processes it first), so declaration order is
/// unobservable outside a sibling cycle: implicit-argument resolution reads a MAY edge's receiver only where its
/// verdict could decide (since the thirteenth review from its input, a link receiver processed only where a certain
/// miss would give a slot a VALUE role); a static read that ends at a written member of an owner still in progress
/// processes that member on demand; the channel adds what the refined verdict reads, never for a parameter's member; an
/// open target whose path cannot be followed records that answer; and a provisional miss lets go of both passes' state
/// once its checks are made.
/// </summary>
public sealed class AliasUnifyTwelfthReviewRegressionTests
{
    private static async Task OkAsync(string source, string value)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(value, outcome.Value);
    }

    private static async Task ErrAsync(string source, string code)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith(code + ":", outcome.Errors[0], StringComparison.Ordinal);
    }

    /// <summary>The front end's diagnostics, each as its code, the start of its message and its span — in order.</summary>
    private static async Task ParseErrorsAsync(string source, params (string Start, string Span)[] expected)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", outcome.Kind);
        Assert.Equal(expected.Length, outcome.Errors.Count);
        for (var i = 0; i < expected.Length; i++)
        {
            Assert.StartsWith(expected[i].Start, outcome.Errors[i], StringComparison.Ordinal);
            Assert.EndsWith("@ " + expected[i].Span, outcome.Errors[i], StringComparison.Ordinal);
        }
    }

    private static void AssertLinear(long small, long large, string what)
    {
        Assert.True(small > 0, $"No {what} was observed.");
        var ratio = (double)large / small;
        Assert.True(ratio < 2.6, $"Doubling the size grew the {what} {ratio:F2}x ({small} -> {large}).");
    }

    private static FrontEndTraversalObservations Detect(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var (_, diagnostics) = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source), observations: observations);
        Assert.Empty(diagnostics);
        return observations;
    }

    private static (Algorithm Root, FrontEndTraversalObservations Observations) Resolve(string source)
    {
        var detectedInput = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        var (detected, detection) = detectedInput;
        Assert.Empty(detection);
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detectedInput, observations, diagnostics);
        Assert.Equal(0, diagnostics.ReportedCount);
        return (resolved, observations);
    }

    // ── A refinement that decides a lift reads its receiver processed, whatever the channel could classify ──

    private const string LocalFamilyReader = "H = {\n    f(0) = 0\n    f(n) = n\n    Lib.A.f + 0\n}\n";
    private const string LinkLib = "Lib = {\n    F(x) = x\n    public A = Mk(F + 0).Algorithm\n    0\n}\n";

    [Theory]
    // The fallback `f` is a family H itself declares (the channel cannot classify it), `Lib.A` a path (no soft edge):
    // A(x) is a calculation, so `Lib.A.f` is f(Lib.A) and Lib.A lifts — `.Algorithm` on 4 — in both orders.
    [InlineData("Mk(n) = n + 1\n" + LocalFamilyReader + LinkLib + "H(3)")]
    [InlineData("Mk(n) = n + 1\n" + LinkLib + LocalFamilyReader + "H(3)")]
    // The family only a root open provides, and a lone-path alias of it.
    [InlineData("open M\nM = {\n    public fam(0) = 0\n    public fam(n) = n\n}\nMk(n) = n + 1\nH = Lib.A.fam + 0\n" + LinkLib + "H(3)")]
    [InlineData("open M\nM = {\n    public fam(0) = 0\n    public fam(n) = n\n}\nMk(n) = n + 1\n" + LinkLib + "H = Lib.A.fam + 0\nH(3)")]
    [InlineData("M = {\n    public fam(0) = 0\n    public fam(n) = n\n}\ng = M.fam\nMk(n) = n + 1\nH = Lib.A.g + 0\n" + LinkLib + "H(3)")]
    // A bare receiver behind the lone-path alias: the channel reads `g` as a user callee (no edge, no soft preference),
    // so H comes first and its refinement processes A on demand.
    [InlineData("M = {\n    public fam(0) = 0\n    public fam(n) = n\n}\ng = M.fam\nMk(n) = n + 1\nF(x) = x\nH = A.g + 0\nA = Mk(F + 0).Algorithm\nH(3)")]
    public async Task ACertainMissTheChannelCannotClassify_IsDecidedFromTheProcessedReceiver_InEveryOrder(string source)
        => await ErrAsync(source, "TypeMismatch");

    [Theory]
    // `A.repeat(Cnt)`: the certain miss's receiver is a META step slot (CALLABLE), its count a VALUE: the refinement reads
    // A to decide whether Cnt lifts, in both orders — H(k), so `H(1)` binds the step `A`, no call: NotAnAlgorithm.
    [InlineData("Mk(n) = n + 1\nCnt(k) = k\nF(x) = x\nH = A.repeat(Cnt)\nA = Mk(F + 0).Algorithm\nH(1)", "NotAnAlgorithm")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nCnt(k) = k\nH = A.repeat(Cnt)\nA = Mk(F + 0).Algorithm\nH(1)", "NotAnAlgorithm")]
    public async Task ARefinedRepeatMiss_ReadsItsStepReceiver_InEveryOrder(string source, string code)
        => await ErrAsync(source, code);

    [Theory]
    [InlineData("Mk(n) = n + 1\nCnt(k) = k\nF(x) = x\nH = if(true, 1, A.repeat(Cnt))\nA = Mk(F + 0).Algorithm\nH(1)")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nCnt(k) = k\nH = if(true, 1, A.repeat(Cnt))\nA = Mk(F + 0).Algorithm\nH(1)")]
    public async Task ARefinedRepeatMiss_InAnUnselectedBranch_LiftsInEveryOrder(string source)
        => await OkAsync(source, "1");

    /// <summary>`Ai = Mk(A(i+1).repeat(Cnt)).Algorithm` … `AK = Mk(F + 0).Algorithm`: each refinement decides whether Cnt lifts.</summary>
    private static string RefinedRepeatChain(int size)
        => "Mk(n) = n + 1\nCnt(k) = k\nF(x) = x\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size
                ? $"A{i} = Mk(A{i + 1}.repeat(Cnt)).Algorithm\n"
                : $"A{i} = Mk(F + 0).Algorithm\n"))
            + "0";

    [Fact]
    public async Task AChainOfRefinedRepeatMisses_IsOrderedWithoutNesting()
    {
        // The receiver of each `.repeat` miss is a META step (CALLABLE), yet the refinement reads it to decide whether the
        // count lifts: the channel orders that read, so A40 … A1 are processed in turn — no demand nests in another.
        await OkAsync(RefinedRepeatChain(40), "0");
        var (root, _) = Resolve(RefinedRepeatChain(3));
        Assert.All(root.Properties.Where(p => p.Name is "A1" or "A2"), property =>
            Assert.Contains("k", Assert.IsType<Algorithm.User>(property.Value).Params));
    }

    [Fact]
    public void ALinkReceiverARefinementReads_IsProcessedBeforeTheEdge_AndReadOnce()
    {
        // The channel orders A — the link body H's refinement of `A.repeat(Cnt)` reads (repeat's count is a value) — before
        // H, so the dependency walk and the rewrite read A processed alike, whatever `B(1)` reads after: H(k), with the k
        // it synthesizes bound by H.
        var (root, _) = Resolve("Mk(n) = n + 1\nCnt(k) = k\nF(x) = x\nH = A.repeat(Cnt) + B(1)\nB = A\nA = Mk(F + 0).Algorithm\n0");
        var h = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "H").Value);
        Assert.Equal(new[] { "k" }, h.Params);
    }

    private const string LaterOperandOpensTheOwner =
        "open Lib\nMk(n) = n + 1\nH = {\n    f(0) = 0\n    f(n) = n\n    Lib.A.f + K(1) + 0\n}\nLib = {\n    F(x) = x\n    public A = Mk(F + 0).Algorithm\n    public K = F\n    0\n}\nH";

    [Fact]
    public async Task OneEdgesRefinement_ReadsItsReceiverProcessed_WhenALaterOperandOpensItsOwner()
    {
        // The channel cannot classify H's own family f, so H comes first: its refinement of `Lib.A.f` processes Lib — the
        // owner of the link body A it reads — on demand before `K(1)` reaches it through the root's open. A(x) is a
        // calculation, so `Lib.A.f` is f(Lib.A) and x lifts: H(x), whose bare root row is its zero-argument demand.
        var (root, _) = Resolve(LaterOperandOpensTheOwner);
        var h = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "H").Value);
        Assert.Equal(new[] { "x" }, h.Params);
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(LaterOperandOpensTheOwner);
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith("ArityMismatch: Property 'H' expects 1 parameter, but was called with 0 arguments.", outcome.Errors[0], StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nA1 = A2.Algorithm\nA2 = Mk(F + 0).Algorithm\nA1(3)")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nA2 = Mk(F + 0).Algorithm\nA1 = A2.Algorithm\nA1(3)")]
    public async Task ACertainAlgorithmIntrinsic_ReadsItsProcessedReceiver_InEveryOrder(string source)
        => await ErrAsync(source, "TypeMismatch");

    // ── A refinement that decides no lift reads nothing: chains through opens stay flat ──

    /// <summary>`Pi = { public Xi = Mk(x).Algorithm ⏎ Yi = X(i+1).G }` under one root `open P1, …, PK`.</summary>
    private static string OpenedLinkChain(int size)
        => "open " + string.Join(", ", Enumerable.Range(1, size).Select(i => $"P{i}")) + "\nMk(n) = n + 1\nG(v) = v\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size
                ? $"P{i} = {{\n    public X{i} = Mk(x).Algorithm\n    Y{i} = X{i + 1}.G\n}}\n"
                : $"P{i} = {{\n    public X{i} = Mk(x).Algorithm\n}}\n"))
            + "0";

    /// <summary>`Li = { public Ai = Mk(A(i+1).foo).Algorithm }` under one root `open L1, …, LK`.</summary>
    private static string OpenedNeutralLinkChain(int size)
        => "open " + string.Join(", ", Enumerable.Range(1, size).Select(i => $"L{i}")) + "\nMk(n) = n + 1\nfoo(v) = 7\nY = { public z = 1 }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size
                ? $"L{i} = {{ public A{i} = Mk(A{i + 1}.foo).Algorithm }}\n"
                : $"L{i} = {{ public A{i} = Mk(Y.foo).Algorithm }}\n"))
            + "0";

    /// <summary>Inside L, `Uj = { public Xj = Mk(x).Algorithm ⏎ public Yj = Mk(X(j+1).foo) }` under L's `open U1, …, UK`.</summary>
    private static string NestedOpenedLinkReceivers(int size)
        => "Mk(n) = n + 1\nfoo(v) = 7\nL = {\n    open " + string.Join(", ", Enumerable.Range(1, size).Select(j => $"U{j}")) + "\n"
            + string.Concat(Enumerable.Range(1, size).Select(j => $"    U{j} = {{\n        public X{j} = Mk(x).Algorithm\n"
                + (j < size ? $"        public Y{j} = Mk(X{j + 1}.foo)\n" : $"        public Y{j} = 0\n") + "    }\n"))
            + "    0\n}\nL";

    [Theory]
    [InlineData("opened-link-chain")]
    [InlineData("opened-neutral-link-chain")]
    [InlineData("nested-opened-link-receivers")]
    public async Task AChainOfOpenedLinkReceivers_InNeutralSlots_IsResolvedWithoutNesting(string shape)
    {
        // Each edge's certain miss would give its receiver a CALLABLE role (a user callee), so the verdict decides no lift
        // and the refinement reads nothing: no provider is processed on demand inside another.
        var source = shape switch
        {
            "opened-link-chain" => OpenedLinkChain(40),
            "opened-neutral-link-chain" => OpenedNeutralLinkChain(40),
            _ => NestedOpenedLinkReceivers(40),
        };
        await OkAsync(source, "0");
    }

    // ── A merely pending path head is processed on demand ──

    private const string OpenedFamily = "open M\nM = {\n    public fam(0) = 0\n    public fam(n) = n\n}\n";
    private const string FormulaLib = "Lib = {\n    F(x) = x\n    public A = F + 0\n    0\n}\n";

    [Theory]
    // No alias, no link row: `Lib.A` fills a family's value slot the channel cannot classify (only an open provides
    // `fam`); the lift reads A processed in both orders, as HEAD does.
    [InlineData(OpenedFamily + "Q = fam(Lib.A) + 0\n" + FormulaLib + "Q(3)")]
    [InlineData(OpenedFamily + FormulaLib + "Q = fam(Lib.A) + 0\nQ(3)")]
    public async Task APathWithAPendingHead_ReadsTheProcessedMember_InEveryOrder(string source)
        => await OkAsync(source, "3");

    // ── A path through the owner reads the processed member wherever it stands ──

    private const string NestedOpenOwner = "    public H = {\n        open Q\n        Self.B + 0\n    }\n    Q = {\n        public Self = Lib\n    }\n";
    private const string NestedOpenMembers = "    C = 1\n    public B = F + C\n";

    [Theory]
    // `Self` reaches the owner only through H's own open: its member B is processed on demand, in both orders.
    [InlineData("F(x) = x\nLib = {\n" + NestedOpenOwner + NestedOpenMembers + "    0\n}\nLib.H(3)")]
    [InlineData("F(x) = x\nLib = {\n" + NestedOpenMembers + NestedOpenOwner + "    0\n}\nLib.H(3)")]
    public async Task AnOwnerReferenceOnlyANestedOpenProvides_ReadsTheProcessedMember_InEveryOrder(string source)
        => await OkAsync(source, "4");

    [Theory]
    // A self path in a CALLEE position names the member its bare name names: A is an alias of abs, so G fills a value
    // slot and lifts (identity never spelling, X-45).
    [InlineData("G(y) = y\nLib = {\n    public A = abs\n    public H = Lib.A(G) + 0\n    0\n}\nLib.H(-3)")]
    [InlineData("G(y) = y\nLib = {\n    public A = abs\n    public H = A(G) + 0\n    0\n}\nLib.H(-3)")]
    [InlineData("G(y) = y\nLib = {\n    public H = Lib.A(G) + 0\n    public A = abs\n    0\n}\nLib.H(-3)")]
    public async Task ASelfPathCallee_HasTheRolesOfItsMember(string source)
        => await OkAsync(source, "3");

    [Theory]
    // `Lib.A` fills an opened family's value slot the channel cannot classify: since the thirteenth review that self path
    // is a soft preference for A, as the bare `A` is, and the static read of the in-progress owner's member processes A
    // on demand where the order did not — A(x), H(x), in both orders.
    [InlineData("open M\nM = {\n    public fam(0) = 0\n    public fam(n) = n\n}\nF(x) = x\nLib = {\n    public H = fam(Lib.A) + 0\n    public A = F + 0\n    0\n}\nLib.H(3)")]
    [InlineData("open M\nM = {\n    public fam(0) = 0\n    public fam(n) = n\n}\nF(x) = x\nLib = {\n    public A = F + 0\n    public H = fam(Lib.A) + 0\n    0\n}\nLib.H(3)")]
    public async Task ASelfPathInASlotTheChannelCannotClassify_ReadsTheProcessedMember_InEveryOrder(string source)
        => await OkAsync(source, "3");

    [Fact]
    public async Task APathThroughAReferenceToTheOwner_ReadsTheProcessedMember()
        => await OkAsync("H(z) = z\nLib = {\n    public Me = Lib\n    public F = Me.G + 0\n    public K = 1\n    public G = H + K\n    0\n}\nLib.F(5)", "6");

    [Fact]
    public async Task APathWhoseHeadANestedBodyDeclares_IsNoReadOfTheOwnersMember()
    {
        // P's own `Lib` shadows the owner: `Lib.G` inside P is that body's member, so G does not depend on P twice — no
        // spurious cycle, G reads P processed.
        await OkAsync("H(z) = z\nLib = {\n    public G = P + 1\n    public P = {\n        Lib = { public G = 7 }\n        Lib.G + H\n    }\n    0\n}\nLib.G(5)", "13");
    }

    [Fact]
    public async Task APathWhoseHeadOnlyAnOpenProvides_IsReadFromItsOwnScope()
    {
        // Inside F, `Self` is R's (F's own open, consulted before Lib's): F does not read Lib's G, so G and F form no cycle
        // and G reads F processed — G(k), whatever Lib's own open Q provides under the same name.
        await OkAsync(
            "K(k) = k\nLib = {\n    open Q\n    public G = F + 0\n    public F = {\n        open R\n        Self.G + K\n    }\n    Q = { public Self = Lib }\n    R = { public Self = { public G = 7 } }\n    0\n}\nLib.G(5)",
            "12");
    }

    // ── The certain miss's reads are dependencies only where resolution may refine the miss ──

    [Theory]
    // `p.abs(G)` / `q.if(1, B)`: a parameter's member is the runtime's, never refined — its arguments are never read, so
    // they close no sibling cycle, in either order.
    [InlineData("K(k) = k\nG = H + 0\nH = if(true, K, p.abs(G))\nG(1, 2)", "2")]
    [InlineData("K(k) = k\nH = if(true, K, p.abs(G))\nG = H + 0\nG(1, 2)", "2")]
    [InlineData("F(z) = z\nH(w) = w\nB = F + G\nG = q.if(1, B) + H\nB(1, true, 3)", "5")]
    [InlineData("F(z) = z\nH(w) = w\nG = q.if(1, B) + H\nB = F + G\nB(1, true, 3)", "5")]
    public async Task AParametersMemberMiss_OrdersNothing(string source, string value)
        => await OkAsync(source, value);

    [Fact]
    public async Task AParametersMemberMiss_KeepsTheResolversReportOrder()
        => await ParseErrorsAsync(
            "U(0) = 0\nU(1) = 1\nC1(a, *p) = a\nC2(b, *q) = b\nP1 = r.if(1, P2) + U\nP2 = C1 + C2\n0",
            ("UnliftableClauseFamily:", "[5:20, 5:21)"),
            ("InvalidCollectingBinding:", "[6:11, 6:13)"));

    // ── An open target whose path cannot be followed records that answer ──

    /// <summary>
    /// Owners `Oi = O(i+1).m` over a miss (`OK = B.zz`), each opened by a body `Qj = { open O1, Lib ⏎ R = w ⏎ R + z }`
    /// whose alias R names what only an open provides (its static target chase consults O1's provider).
    /// </summary>
    private static string OpensOfNestedOwnersOverAMiss(int size)
        => "m(v) = v\nzz(v) = v\nB = { public y = 1 }\nLib = { public w = 1 }\n"
            + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"O{i} = O{i + 1}.m\n")) + $"O{size} = B.zz\n"
            + string.Concat(Enumerable.Range(1, size).Select(j => $"Q{j} = {{\n    open O1, Lib\n    R = w\n    R + z\n}}\n")) + "0";

    [Fact]
    public async Task OpensOfNestedOwnersOverAMiss_AreElaboratedInLinearWork()
    {
        await OkAsync(OpensOfNestedOwnersOverAMiss(3), "0");
        AssertLinear(Detect(OpensOfNestedOwnersOverAMiss(100)).StaticQueryEvaluationCount, Detect(OpensOfNestedOwnersOverAMiss(200)).StaticQueryEvaluationCount, "detection work");
        AssertLinear(
            Resolve(OpensOfNestedOwnersOverAMiss(100)).Observations.StaticQueryEvaluationCount,
            Resolve(OpensOfNestedOwnersOverAMiss(200)).Observations.StaticQueryEvaluationCount,
            "resolver query computations");
    }

    // ── A deferred check is made for every family and positioned in imported content ──

    [Fact]
    public void ADeferredCheck_OfABranchBodyTwoFamiliesShare_IsMadeForEach()
    {
        var parsed = Parser.ParseSyntax("Mk(n) = n + 1\nA = Mk(x).Algorithm\nF(0) = A.bar + 1\nF(1) = 0\n5");
        Assert.False(parsed.HasErrors);
        var syntax = parsed.SyntaxRoot;
        var body = Assert.IsType<Algorithm.Conditional>(Assert.Single(syntax.Properties, p => p.Name == "F").Value).Branches[0].Body;
        Algorithm.Conditional Family() => new(null, [], [new CondBranch(new Pattern.LitInt(0), body)]);
        var root = new Algorithm.User(
            null,
            [],
            [],
            [syntax.Properties.Single(p => p.Name == "Mk"), syntax.Properties.Single(p => p.Name == "A"), new Property("Left", Family()), new Property("Right", Family())],
            OutputBundle.Empty);

        var diagnostics = new DiagnosticBag();
        var detectedInput = ParameterDetector.DetectPrevalidated(root, diagnostics: diagnostics);
        var (detected, _) = detectedInput;
        _ = ImplicitArgumentResolver.ResolvePrevalidated(detectedInput, observations: null, diagnostics);

        Assert.Equal(2, diagnostics.Count);
        Assert.All(diagnostics, d => Assert.Equal(DiagnosticCode.UndeclaredIdentifier, d.Code));
        Assert.Contains("conditional branch 'Left'", diagnostics[0].Message, StringComparison.Ordinal);
        Assert.Contains("conditional branch 'Right'", diagnostics[1].Message, StringComparison.Ordinal);
        Assert.All(diagnostics, d => Assert.Contains("Property 'bar' was not found on `A`", d.Message, StringComparison.Ordinal));
    }

    [Theory]
    // A closed body of imported content whose check waits on a miss resolution decides: reported at the import site.
    [InlineData("Mk(n) = n + 1\nA = Mk(x).Algorithm\npublic G(p) = A.bar + p", "'bar'")]
    // A parameter's member also defers the check (its miss is the runtime's): the undeclared name still reported there.
    [InlineData("\n\n\npublic Fine = 7\nK(obj) = obj.width + zz", "'zz'")]
    public async Task ADeferredCheckInImportedContent_IsReportedAtTheImportSite(string module, string name)
    {
        const string Url = "https://katlang.org/lazy/m.kat";
        var options = new RunOptions
        {
            DownloadCode = (url, _) => url == Url ? ValueTask.FromResult(module) : throw new InvalidOperationException(url),
        };
        var result = await KatLangEngine.RunAsync($"open '{Url}'\n5", options);
        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UndeclaredIdentifier, error.Code);
        Assert.Contains(name, error.Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(new SourcePosition(1, 6), new SourcePosition(1, 6 + Url.Length + 2)), error.Span);
    }

    // ── A provisional miss keeps no pass state in the published tree ──

    [Fact]
    public void AProvisionalMiss_LetsGoOfThePassesState_OnceItsChecksAreMade()
    {
        // SEC-S1: the edge keeps its cell into the published tree, whose decider and checks held both passes' state.
        var parsed = SourceProvenance.ParseValid("Area(shape) = shape.width * shape.height\nBox = {\n    public width = 2\n    public height = 3\n}\nArea(Box)");
        var area = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(p => p.Name == "Area").Value);
        var edge = Assert.IsType<Expr.DotCall>(Assert.IsType<Expr.Binary>(area.Output[0]).Left);
        var miss = Assert.IsType<ProvisionalMiss>(edge.ProvisionalMiss);
        Assert.False(miss.HoldsPassState);
    }
}
