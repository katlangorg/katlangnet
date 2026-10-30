namespace KatLang.Tests;

/// <summary>
/// ALIAS-UNIFY-1 (M4★) thirteenth independent-review regressions. Source cases run on the six routes of
/// <see cref="SixRouteAgreement"/>; modules run through the engine with an in-memory downloader; the scaling facts compare
/// the passes' own observations (<see cref="FrontEndTraversalObservations"/>) at two sizes. Implicit-argument resolution
/// decides a MAY edge from its INPUT — every declaration as written, a reference followed to its target — with nothing
/// processed, except an <c>.Algorithm</c> link receiver, which only its processing decides and which it processes only
/// where a certain miss would give a slot a VALUE role; a parameter's member, a runtime reference's and an unresolved
/// name's read nothing. The sibling-order channel orders exactly those reads: a certain miss's, and a link receiver read
/// where its own classification gives a slot a VALUE role. A member path is read statically through every reference to
/// the member its name reads, every owner on the way processed with it; and the published tree reaches none of the
/// resolver's input.
/// </summary>
public sealed class AliasUnifyThirteenthReviewRegressionTests
{
    private static async Task OkAsync(string source, string value)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(value, outcome.Value);
    }

    private static async Task ErrAsync(string source, string start)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith(start, outcome.Errors[0], StringComparison.Ordinal);
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

    private static Algorithm.User Member(Algorithm owner, string name)
        => Assert.IsType<Algorithm.User>(owner.Properties.Single(p => p.Name == name).Value);

    private const string OpenedFamily = "open M\nM = {\n    public fam(0) = 0\n    public fam(n) = n\n}\n";

    // ── A member call's callee is the member its path selects, read through every reference ──

    [Theory]
    // `Me.A(G)` through a reference to the owner, in both orders: A is an alias of abs, so G fills a value slot.
    [InlineData("G(y) = y\nLib = {\n    public H = Me.A(G) + 0\n    public Me = Lib\n    public A = abs\n    0\n}\nLib.H(-3)", "3")]
    [InlineData("G(y) = y\nLib = {\n    public Me = Lib\n    public H = Me.A(G) + 0\n    public A = abs\n    0\n}\nLib.H(-3)", "3")]
    // `R.f(G)` through an unprocessed reference to a family, and `Lib.A.f(G)` through the owner's member reference.
    [InlineData("G(g) = g\nLib = {\n    public f(0) = 0\n    public f(n) = n\n    0\n}\nC = {\n    public H = R.f(G) + R2(1)\n    public R2 = R.f\n    public R = Lib\n    0\n}\nC.H(5)", "6")]
    [InlineData("G(y) = y\nSub = {\n    public f(0) = 0\n    public f(n) = n\n    0\n}\nLib = {\n    public A = Sub\n    public H = Lib.A.f(G) + 0\n    0\n}\nLib.H(5)", "5")]
    public async Task AMemberCallsCallee_IsReadThroughEveryReference_InEveryOrder(string source, string value)
        => await OkAsync(source, value);

    [Fact]
    public void AMemberCallsCallee_IsOneReadForTheWalkAndTheRewrite()
    {
        // `R2(1)` processes R on demand after H's dependency walk met `R.f(G)`: both read f through R statically, so the
        // g the rewrite synthesizes is H's own.
        var (root, _) = Resolve("G(g) = g\nLib = {\n    public f(0) = 0\n    public f(n) = n\n    0\n}\nC = {\n    public H = R.f(G) + R2(1)\n    public R2 = R.f\n    public R = Lib\n    0\n}\n0");
        Assert.Equal(new[] { "g" }, Member(Member(root, "C"), "H").Params);
    }

    // ── A refinement reads its receiver from the input, through a reference to the owner too ──

    [Theory]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nLib = {\n    public Me = Lib\n    public A = Mk(F + 0).Algorithm\n    public H = Me.A.abs + 0\n    0\n}\nLib.H(3)")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nLib = {\n    public Me = Lib\n    public A = Mk(F + 0).Algorithm\n    public H = Lib.A.abs + 0\n    0\n}\nLib.H(3)")]
    public async Task ARefinementThroughAReferenceToTheOwner_IsDecidedAsThroughTheOwner(string source)
        // A(x) is a calculation, so `.abs` certainly misses and abs's value receiver lifts A: H(x), whose `.Algorithm` is on 4.
        => await ErrAsync(source, "TypeMismatch:");

    [Theory]
    // `A = x` is a navigated body detection could not decide (an enclosing edge is named x), whose input decides it: A(x),
    // a calculation, so `Lib.A.repeat(Cnt)` is a certain miss and Cnt lifts — read with nothing processed, so the guard
    // closes no cycle with Lib's own read of F.
    [InlineData("Lib = {\n    Cfg = { public x = 1 }\n    public A = x\n    Cfg.x + F\n}\nF = if(true, 1, Lib.A.repeat(Cnt))\nCnt(k) = k\nLib(5)")]
    [InlineData("F = if(true, 1, Lib.A.repeat(Cnt))\nLib = {\n    Cfg = { public x = 1 }\n    public A = x\n    Cfg.x + F\n}\nCnt(k) = k\nLib(5)")]
    [InlineData("Lib = {\n    public A = x\n    1 + F\n}\nF = if(true, 1, Lib.A.repeat(Cnt))\nCnt(k) = k\nLib(5)")]
    public async Task AReceiverTheInputDecides_IsReadWithNothingProcessed_InEveryOrder(string source)
    {
        await OkAsync(source, "2");
        var (root, _) = Resolve(source.Replace("Lib(5)", "0", StringComparison.Ordinal));
        Assert.Equal(new[] { "k" }, Member(root, "Lib").Params);
    }

    // ── A miss only the runtime decides orders no argument read ──

    [Theory]
    // A runtime link (`Cap(Inc(1)).Algorithm` lifts nothing) and a runtime reference to a parameter: the miss stays MAY,
    // its arguments CALLABLE and never read, so they close no cycle with the edge's body, in either order.
    [InlineData("K(k) = k\nG = H + 0\nH = if(true, K, A.if(1, G))\nA = Cap(Inc(1)).Algorithm\nCap(meta op) = op\nInc(x) = x + 1\nG(7)", "7")]
    [InlineData("K(k) = k\nH = if(true, K, A.if(1, G))\nG = H + 0\nA = Cap(Inc(1)).Algorithm\nCap(meta op) = op\nInc(x) = x + 1\nG(7)", "7")]
    [InlineData("F(z) = z\nH(w) = w\nG(p) = {\n    R = p\n    B = F + C\n    C = R.if(1, B) + H\n    B(1, 2)\n}\nG(true)", "4")]
    [InlineData("F(z) = z\nH(w) = w\nG(p) = {\n    R = p\n    C = R.if(1, B) + H\n    B = F + C\n    B(1, 2)\n}\nG(true)", "4")]
    public async Task AMissOnARuntimeReference_OrdersNoArgumentRead_InEveryOrder(string source, string value)
        => await OkAsync(source, value);

    [Theory]
    // H's `A.foo(G)` reads the link A only where a certain miss would give a slot a VALUE role; `foo` is a user callee, so
    // H never reads A — while A reads H (its `Mk(H + 0)`): no cycle, so H comes first and A lifts H's z, in both orders.
    [InlineData("Mk(n) = n + 1\nZ(z) = z\nfoo(v, w) = 7\nG(g) = g\nA = Mk(H + 0).Algorithm\nH = A.foo(G) + Z\n0")]
    [InlineData("Mk(n) = n + 1\nZ(z) = z\nfoo(v, w) = 7\nG(g) = g\nH = A.foo(G) + Z\nA = Mk(H + 0).Algorithm\n0")]
    public void ALinkReceiverInNeutralSlots_IsNoSiblingDependency(string source)
    {
        var (root, _) = Resolve(source);
        Assert.Equal(new[] { "z" }, Member(root, "H").Params);
        Assert.Equal(new[] { "z" }, Member(root, "A").Params);
    }

    [Fact]
    public async Task AnUnresolvedReceiversMiss_KeepsTheResolversReportOrder()
        // `u` is undeclared in P1's closed list: its miss reads nothing, so P1 and P2 keep the declaration order.
        => await ParseErrorsAsync(
            "U(0) = 0\nU(1) = 1\nC1(a, *p) = a\nC2(b, *q) = b\nP1(z) = {\n    W = U + 0\n    u.if(1, P2) + W + z\n}\nP2 = C1 + C2\n0",
            ("UndeclaredIdentifier:", "[7:5, 7:6)"),
            ("UnliftableClauseFamily:", "[6:9, 6:10)"),
            ("InvalidCollectingBinding:", "[9:11, 9:13)"));

    /// <summary>`Bi(p) = p.g(i+1)` / `g(i+1) = B(i+1)` … `BK(p) = p`: each miss is a parameter's member.</summary>
    private static string ParameterMemberChain(int size)
        => string.Concat(Enumerable.Range(1, size - 1).Select(i => $"B{i}(p) = p.g{i + 1}\ng{i + 1} = B{i + 1}\n")) + $"B{size}(p) = p\n0";

    /// <summary>`Pi = q.gi(5) + 0` / `gi = P(i+1)` … `P(K+1) = 0`: each miss is a parameter's member in a formula.</summary>
    private static string ParameterReceiverChain(int size)
        => string.Concat(Enumerable.Range(1, size).Select(i => $"P{i} = q.g{i}(5) + 0\ng{i} = P{i + 1}\n")) + $"P{size + 1} = 0\n0";

    [Fact]
    public async Task AParametersMemberMiss_SettlesNoFallbackCallee()
    {
        // Its verdict is the runtime's, so nothing is asked of it: no fallback callee is processed on demand, and chains
        // of alias-shaped fallback callees stay flat.
        await OkAsync(ParameterMemberChain(41), "0");
        await OkAsync(ParameterReceiverChain(40), "0");
    }

    // ── A path through the owner reads every member it passes processed ──

    [Theory]
    [InlineData(OpenedFamily + "F(x) = x\nLib = {\n    public H = fam(Lib.Y.W) + 0\n    public Y = {\n        public W = F + 0\n        0\n    }\n    0\n}\nLib.H(3)", "3")]
    [InlineData(OpenedFamily + "F(x) = x\nLib = {\n    public Y = {\n        public W = F + 0\n        0\n    }\n    public H = fam(Lib.Y.W) + 0\n    0\n}\nLib.H(3)", "3")]
    [InlineData(OpenedFamily + "F(x) = x\nLib = {\n    public H = fam(Lib.Y.W) + K(1)\n    public K = Y.G\n    public Y = {\n        public W = F + 0\n        public G(z) = z\n        0\n    }\n    0\n}\nLib.H(3)", "4")]
    public async Task ATwoStepSelfPath_ReadsTheProcessedMember_InEveryOrder(string source, string value)
        => await OkAsync(source, value);

    [Fact]
    public void ATwoStepSelfPath_IsOneReadForTheWalkAndTheRewrite()
    {
        var (root, _) = Resolve(OpenedFamily + "F(x) = x\nLib = {\n    public H = fam(Lib.Y.W) + K(1)\n    public K = Y.G\n    public Y = {\n        public W = F + 0\n        public G(z) = z\n        0\n    }\n    0\n}\n0");
        Assert.Equal(new[] { "x" }, Member(Member(root, "Lib"), "H").Params);
    }

    /// <summary>Inside one Lib, `Ai = fam(Lib.A(i+1)) + 0` … `AK = F + 0`, with `fam` only the root's open provides.</summary>
    private static string SelfPathChain(int size)
        => OpenedFamily + "F(x) = x\nLib = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"    public A{i} = fam(Lib.A{i + 1}) + 0\n" : $"    public A{i} = F + 0\n"))
            + "    0\n}\n0";

    [Fact]
    public async Task AChainOfSelfPathsInSlotsTheChannelCannotClassify_IsOrderedWithoutNesting()
    {
        // The channel cannot classify `fam` (only an open provides it), so each path is a soft preference for the sibling
        // it reads, as a bare name is: A40 … A1 are processed in turn, every one A(x).
        await OkAsync(SelfPathChain(40), "0");
        var (root, _) = Resolve(SelfPathChain(3));
        var lib = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "Lib").Value);
        Assert.All(new[] { "A1", "A2", "A3" }, name => Assert.Equal(new[] { "x" }, Member(lib, name).Params));
    }

    // ── A link receiver only an open of the level provides is ordered before its reader ──

    /// <summary>`Pi = { public Xi = Mk(X(i+1).fam + 0).Algorithm }` … under one root `open P1, …, PK`.</summary>
    private static string OpenedValueLinkChain(int size)
        => "open " + string.Join(", ", Enumerable.Range(1, size).Select(i => $"P{i}")) + "\nMk(n) = n + 1\nF(x) = x\nfam(0) = 0\nfam(n) = n\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size
                ? $"P{i} = {{\n    public X{i} = Mk(X{i + 1}.fam + 0).Algorithm\n}}\n"
                : $"P{i} = {{\n    public X{i} = Mk(F + 0).Algorithm\n}}\n"))
            + "0";

    [Fact]
    public async Task AChainOfOpenedLinkReceivers_InValueSlots_IsOrderedWithoutNesting()
    {
        // Each `X(i+1).fam` fills a family's value slot: the refinement processes the link body X(i+1), and the channel
        // orders its provider P(i+1) first — every X a calculation X(x).
        await OkAsync(OpenedValueLinkChain(40), "0");
        var (root, _) = Resolve(OpenedValueLinkChain(3));
        Assert.All(new[] { 1, 2, 3 }, i => Assert.Equal(new[] { "x" }, Member(Member(root, $"P{i}"), $"X{i}").Params));
    }

    /// <summary>`Pi = A.gi(5) + 0` / `gi = P(i+1)` … over one runtime link `A = Cap(Inc(1)).Algorithm`.</summary>
    private static string LinkReceiverAliasCalleeChain(int size)
        => "Cap(meta op) = op\nInc(x) = x + 1\nA = Cap(Inc(1)).Algorithm\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"P{i} = A.g{i}(5) + 0\ng{i} = P{i + 1}\n")) + $"P{size + 1} = 0\n0";

    [Fact]
    public async Task ALinkReceiversFallbackCallee_IsClassifiedWithNothingProcessed()
        // Whether a certain miss would give a slot a VALUE role is asked of the fallback callee read from the input: `gi`
        // is an alias of a user formula (every slot CALLABLE), so A is never processed for it, and no `gi` is either — the
        // chain stays flat (HEAD read `A.gi` as a certain miss and settled each callee on demand: AstDepthLimitExceeded).
        => await OkAsync(LinkReceiverAliasCalleeChain(40), "0");

    /// <summary>`Pi = Xi.if(true, 1, P(i+1))` / `Xi = Mk(x).Algorithm` …: certain misses over link bodies with an input of their own.</summary>
    private static string CertainMissLinkChain(int size)
        => "Mk(n) = n + 1\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"P{i} = X{i}.if(true, 1, {(i < size ? $"P{i + 1}" : "G")})\nX{i} = Mk(x).Algorithm\n"))
            + "G(g) = g\n0";

    [Fact]
    public async Task AChainOfCertainMissesTheInputDecides_IsOrderedWithoutNesting()
    {
        // `Xi` keeps its own input x, so `Xi.if(…)` is a certain miss read from the input, with nothing processed: the
        // channel orders what a certain miss reads, as for detection's own MUST — P40 … P1 in turn, no demand nested.
        await OkAsync(CertainMissLinkChain(40), "0");
        var (root, _) = Resolve(CertainMissLinkChain(2));
        Assert.Equal(new[] { "x", "g" }, Member(root, "P2").Params);
    }

    [Theory]
    // X2 in P1 is the link Q's open provides (an input of its own: a certain miss), never the root's P2.X2 (a runtime
    // link): the channel reads nothing through the root's opens for a body with opens of its own, so P1 does not depend
    // on P2 and V lifts P1's g in both orders.
    [InlineData("open P2\nMk(n) = n + 1\nF(x) = x\nG(g) = g\nfam(0) = 0\nfam(n) = n\nP2 = {\n    public X2 = Mk(F + 0).Algorithm\n    public V = P1 + 0\n    0\n}\nP1 = {\n    open Q\n    public X1 = Mk(X2.fam + 0).Algorithm\n    G + 0\n}\nQ = { public X2 = Mk(y).Algorithm }\nP2.V(7)")]
    [InlineData("open P2\nMk(n) = n + 1\nF(x) = x\nG(g) = g\nfam(0) = 0\nfam(n) = n\nP1 = {\n    open Q\n    public X1 = Mk(X2.fam + 0).Algorithm\n    G + 0\n}\nP2 = {\n    public X2 = Mk(F + 0).Algorithm\n    public V = P1 + 0\n    0\n}\nQ = { public X2 = Mk(y).Algorithm }\nP2.V(7)")]
    public async Task AHeadANestedBodysOwnOpenProvides_IsReadNowhereElse_InEveryOrder(string source)
        => await OkAsync(source, "7");

    /// <summary>Inside one Lib, `Bi = { public W = abs(Lib.B(i+1).W) + 0 }` … `BK = { public W = F + 0 }`.</summary>
    private static string TwoStepValueChain(int size, string row)
        => "F(x) = x\nLib = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    public B{i} = {{\n        public W = {(i < size ? $"abs(Lib.B{i + 1}.W)" : "F")} + 0\n        0\n    }}\n"))
            + "    0\n}\n" + row;

    [Fact]
    public async Task AChainOfTwoStepSelfPathsInValueSlots_IsOrderedWithoutNesting()
    {
        // `Lib.B(i+1).W` reads B(i+1)'s member W: the value-role path depends on the sibling B(i+1) it passes, so B40 … B1
        // are processed in turn, every W(x).
        await OkAsync(TwoStepValueChain(40, "0"), "0");
        await OkAsync(TwoStepValueChain(3, "Lib.B1.W(-3)"), "3");
    }

    /// <summary>Inside one Lib, `Bi = { public W = fam(Lib.B(i+1).W) + 0 }` … with `fam` only the root's open provides.</summary>
    private static string TwoStepUnclassifiedChain(int size)
        => OpenedFamily + "F(x) = x\nLib = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    public B{i} = {{\n        public W = {(i < size ? $"fam(Lib.B{i + 1}.W)" : "F")} + 0\n        0\n    }}\n"))
            + "    0\n}\n0";

    [Fact]
    public async Task AChainOfTwoStepSelfPathsInSlotsTheChannelCannotClassify_IsOrderedWithoutNesting()
    {
        // A path in a slot the channel cannot classify is a soft preference for the sibling it passes (B(i+1), whose
        // processing processes W), not only for a member it ends at: B40 … B1 in turn, no demand nested.
        await OkAsync(TwoStepUnclassifiedChain(40), "0");
        var (root, _) = Resolve(TwoStepUnclassifiedChain(3));
        var lib = Member(root, "Lib");
        Assert.All(new[] { "B1", "B2", "B3" }, name => Assert.Equal(new[] { "x" }, Member(Member(lib, name), "W").Params));
    }

    [Fact]
    public async Task AnAliasOfATwoStepSelfPath_ReadsTheProcessedMember()
        // K's target is W, read through Y, which the formation of K processes on demand with W: K is W(x), so abs lifts it.
        => await OkAsync("F(x) = x\nLib = {\n    public K = Lib.Y.W\n    public H = abs(K) + 0\n    public Y = {\n        public W = F + 0\n        0\n    }\n    0\n}\nLib.H(-3)", "3");

    [Fact]
    public async Task ABlockHeadedLinkReceiver_IsDecidedFromItsProcessedBlock()
        // The block written in H's row is processed to decide its link member A: A(x), a calculation, so `.abs` certainly
        // misses and abs's value receiver lifts it — H(x), whose `.Algorithm` is on 4.
        => await ErrAsync("Mk(n) = n + 1\nF(x) = x\nH = { public A = Mk(F + 0).Algorithm }.A.abs + 0\nH(3)", "TypeMismatch:");

    [Theory]
    // A braced link body is a carrier, its own structure: `A.if(…)` certainly misses, so G lifts (H(g)). An unbraced one
    // is a runtime reference, whose miss only the run decides: H().
    [InlineData("G(g) = g\nH = A.if(1, G)\nA = { Cap(Inc(1)).Algorithm }\nCap(meta op) = op\nInc(x) = x + 1\n0", new[] { "g" })]
    [InlineData("G(g) = g\nH = A.if(1, G)\nA = Cap(Inc(1)).Algorithm\nCap(meta op) = op\nInc(x) = x + 1\n0", new string[0])]
    public void ABracedLinkCarrier_IsItsOwnStructure(string source, string[] parameters)
        => Assert.Equal(parameters, Member(Resolve(source).Root, "H").Params);

    // ── Two holders of one module read like one ──

    [Theory]
    [InlineData("    public H = fam(Lib.M1) + 0\n    public M1 = load('{0}')\n    public M2 = load('{0}')\n")]
    [InlineData("    public M1 = load('{0}')\n    public M2 = load('{0}')\n    public H = fam(Lib.M1) + 0\n")]
    [InlineData("    public H = fam(Lib.M1) + 0\n    public M1 = load('{0}')\n")]
    // An alias of the holder (a lone row, which the channel orders nothing for): its formation processes the shared module
    // on demand, so H lifts it as K(x).
    [InlineData("    public K = Lib.M1\n    public H = fam(K) + 0\n    public M1 = load('{0}')\n    public M2 = load('{0}')\n")]
    public async Task ASelfPathToAModuleHolder_ReadsTheProcessedModule_HoweverManyHoldersShareIt(string members)
    {
        const string Url = "https://katlang.org/lazy/u.kat";
        var options = new RunOptions
        {
            DownloadCode = (url, _) => url == Url ? ValueTask.FromResult("F(x) = x\nF + 0") : throw new InvalidOperationException(url),
        };
        var source = OpenedFamily + "Lib = {\n" + string.Format(System.Globalization.CultureInfo.InvariantCulture, members, Url) + "    0\n}\nLib.H(3)";
        var success = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, options));
        Assert.Equal("3", success.ToDisplayString().ReplaceLineEndings("\n"));
    }

    // ── The published tree reaches none of the resolver's input ──

    [Fact]
    public void APublishedAlias_ReachesNoLevelOfTheResolversInput()
    {
        // SEC-S1: an alias's recorded target is its target's processed entry, which names the level that declares it —
        // whose input entries and written opens are let go of once the run ends.
        var root = SourceProvenance.ParseValid("F(x) = x + 1\nA = F\nLib = {\n    open Q\n    public B = F\n    Q = { public z = 1 }\n    0\n}\nA(2)").Root;
        foreach (var alias in new[] { root.Properties.Single(p => p.Name == "A").Value, Member(root, "Lib").Properties.Single(p => p.Name == "B").Value })
        {
            var target = Assert.IsType<Algorithm.Alias>(alias).ResolvedTarget;
            Assert.NotNull(target);
            var identity = Assert.IsType<ImplicitArgumentResolver.VisibleProperty>(target.Identity);
            for (var level = identity.Level; level is not null; level = level.Outer)
            {
                Assert.Null(level.Entries);
                Assert.Empty(level.Opens);
            }
        }
    }

    // ── An open target over an unknown receiver records that answer for every owner waiting on it ──

    /// <summary>
    /// Owners `Oi = O(i+1).m` over `OK = w.zz`, whose head only the root's open provides (no direct declaration, so the
    /// open target's last receiver is unknown), each opened by a body `Qj = { open O1, Lib ⏎ R = w ⏎ R + z }`.
    /// </summary>
    private static string OpensOfNestedOwnersOverAnUnprovidedHead(int size)
        => "open Lib\nm(v) = v\nzz(v) = v\nLib = { public w = 1 }\n"
            + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"O{i} = O{i + 1}.m\n")) + $"O{size} = w.zz\n"
            + string.Concat(Enumerable.Range(1, size).Select(j => $"Q{j} = {{\n    open O1, Lib\n    R = w\n    R + z\n}}\n")) + "0";

    [Fact]
    public async Task OpensOfNestedOwnersOverAnUnprovidedHead_AreElaboratedInLinearWork()
    {
        await OkAsync(OpensOfNestedOwnersOverAnUnprovidedHead(3), "0");
        AssertLinear(
            Detect(OpensOfNestedOwnersOverAnUnprovidedHead(100)).StaticQueryEvaluationCount,
            Detect(OpensOfNestedOwnersOverAnUnprovidedHead(200)).StaticQueryEvaluationCount,
            "detection work");
        AssertLinear(
            Resolve(OpensOfNestedOwnersOverAnUnprovidedHead(100)).Observations.StaticQueryEvaluationCount,
            Resolve(OpensOfNestedOwnersOverAnUnprovidedHead(200)).Observations.StaticQueryEvaluationCount,
            "resolver query computations");
    }
}
