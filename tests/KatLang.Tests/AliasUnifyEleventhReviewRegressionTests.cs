using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// ALIAS-UNIFY-1 (M4★) eleventh independent-review regressions. Source cases run on the six routes of
/// <see cref="SixRouteAgreement"/>; a deferred unit runs through the engine with an in-memory downloader; the scaling
/// facts compare the passes' own observations (<see cref="FrontEndTraversalObservations"/>) at two sizes. Detection
/// leaves a miss on a receiver whose structure only implicit-argument resolution decides (a link-row body, a navigated
/// body whose head an enclosing body may infer) to the runtime (MAY); nothing observable may depend on it: resolution's
/// one verdict per edge is read from its input, a link receiver processed where the verdict decides a lift, the
/// sibling-order channel records the reads that verdict makes, and a member path through the level's own owner
/// (<c>Lib.A</c> inside <c>Lib</c>) is a read of that sibling, so the verdict is the same whatever the declaration order
/// (since the thirteenth review; see <c>AliasUnifyThirteenthReviewRegressionTests</c>); the checks a certain miss makes — a closed list's names, an ambiguous
/// open, a Grace marker on an intrinsic — are decided once resolution has processed every body and reported where
/// detection would have reported them; and the receiver-aware provenance of an inferred fallback name is claimed as
/// written and kept exactly when the elaborated receiver certainly lacks the member. Both static chases record every
/// stable answer, unknown ones included, and agree on a member path that misses.
/// </summary>
public sealed class AliasUnifyEleventhReviewRegressionTests
{
    private static async Task OkAsync(string source, string value)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(value, outcome.Value);
    }

    private static async Task<SixRouteAgreement.Observation> ErrAsync(string source, string code)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith(code + ":", outcome.Errors[0], StringComparison.Ordinal);
        return outcome;
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

    private static FrontEndTraversalObservations Detect(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var (_, diagnostics) = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source), observations: observations);
        Assert.Empty(diagnostics);
        return observations;
    }

    private static FrontEndTraversalObservations Resolve(string source)
    {
        var detectedInput = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        var (detected, detection) = detectedInput;
        Assert.Empty(detection);
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();
        _ = ImplicitArgumentResolver.ResolvePrevalidated(detectedInput, observations, diagnostics);
        Assert.Equal(0, diagnostics.ReportedCount);
        return observations;
    }

    private static void AssertLinear(long small, long large, string what)
    {
        Assert.True(small > 0, $"No {what} was observed.");
        var ratio = (double)large / small;
        Assert.True(ratio < 2.6, $"Doubling the size grew the {what} {ratio:F2}x ({small} -> {large}).");
    }

    // ── A certain miss through an enclosing body in progress is decided from the processed receiver ──

    [Theory]
    // The closed G(p) reads `Lib.B.bar` / `Lib.A.bar` while Lib is in progress; A(x) — from its own x or lifted from F —
    // is a calculation, so `bar` is a certain miss, whichever member Lib declares first.
    [InlineData("Mk(n) = n + 1\nLib = {\n    public H = {\n        G(p) = Lib.B.bar + p\n        0\n    }\n    public B = A\n    public A = Mk(x).Algorithm\n    0\n}\n5", "Lib.B", "[4:22, 4:25)")]
    [InlineData("Mk(n) = n + 1\nLib = {\n    public B = A\n    public A = Mk(x).Algorithm\n    public H = {\n        G(p) = Lib.B.bar + p\n        0\n    }\n    0\n}\n5", "Lib.B", "[6:22, 6:25)")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nLib = {\n    public H = {\n        G(p) = Lib.A.bar + p\n        0\n    }\n    public A = Mk(F + 0).Algorithm\n    0\n}\n5", "Lib.A", "[5:22, 5:25)")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nLib = {\n    public A = Mk(F + 0).Algorithm\n    public H = {\n        G(p) = Lib.A.bar + p\n        0\n    }\n    0\n}\n5", "Lib.A", "[6:22, 6:25)")]
    // Lib reads G, so G is processed before Lib: the check waits until A is processed too.
    [InlineData("Mk(n) = n + 1\nF(x) = x\nLib = {\n    public A = Mk(F + 0).Algorithm\n    G + 0\n}\nG(p) = Lib.A.bar + p\n5", "Lib.A", "[7:14, 7:17)")]
    public async Task ACertainMissThroughABodyInProgress_IsChecked_InEveryMemberOrder(string source, string receiver, string span)
        => await ParseErrorsAsync(source, ($"UndeclaredIdentifier: Property 'bar' was not found on `{receiver}`, so `{receiver}.bar` is the call `bar({receiver})`", span));

    [Theory]
    // H lifts A's lifted input through the certain `abs` fallback whichever member comes first: Lib.H(3) projects
    // `.Algorithm` from Mk(3) = 4.
    [InlineData("Mk(n) = n + 1\nF(x) = x\nLib = {\n    public H = Lib.A.abs + 0\n    public A = Mk(F + 0).Algorithm\n    0\n}\nLib.H(3)")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nLib = {\n    public A = Mk(F + 0).Algorithm\n    public H = Lib.A.abs + 0\n    0\n}\nLib.H(3)")]
    public async Task ACertainMissThroughABodyInProgress_IsLifted_InEveryMemberOrder(string source)
    {
        var outcome = await ErrAsync(source, "TypeMismatch");
        Assert.Contains("`Algorithm` requires a call reference, got numeric value 4", outcome.Errors[0], StringComparison.Ordinal);
    }

    [Theory]
    // A(x) through B: H(x), and Lib.H(3) projects Cap's captured call Only(3).
    [InlineData("Cap(meta op) = op\nOnly(*xs) = 5\nLib = {\n    public H = Lib.B.abs + 0\n    public B = A\n    public A = Cap(Only(x)).Algorithm\n    0\n}\nLib.H(3)", "5")]
    // A(foo) is a calculation: `A.abs` lifts it into H(foo), and A(3) projects Cap's captured call Only(X.foo).
    [InlineData("Cap(meta op) = op\nOnly(*xs) = 5\nX = {\n    public Y = 1\n}\nA = Cap(Only(X.foo)).Algorithm\nH = A.abs + 0\nH(3)", "5")]
    public async Task ALinkCalculation_IsLiftedIntoItsCertainFallback(string source, string value)
        => await OkAsync(source, value);

    [Theory]
    // The dependency walk and the rewrite of H read ONE verdict for `Lib.B.abs`, whatever the operands' order: H(x) and
    // Lib(x), never a synthesized x nothing binds.
    [InlineData("Mk(n) = n + 1\nLib = {\n    public H = Lib.B.abs + B(1)\n    public B = A\n    public A = Mk(x).Algorithm\n    H + 0\n}\nLib(3)", "4")]
    [InlineData("Mk(n) = n + 1\nLib = {\n    public H = B(1) + Lib.B.abs\n    public B = A\n    public A = Mk(x).Algorithm\n    H + 0\n}\nLib(3)", "2")]
    public async Task OneEdge_HasOneVerdict_ForTheDependencyWalkAndTheRewrite(string source, string projected)
    {
        var outcome = await ErrAsync(source, "TypeMismatch");
        Assert.Contains($"`Algorithm` requires a call reference, got numeric value {projected}", outcome.Errors[0], StringComparison.Ordinal);

        var parsed = SourceProvenance.ParseValid(source);
        var lib = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(p => p.Name == "Lib").Value);
        Assert.Equal(["x"], lib.Params);
        var h = Assert.IsType<Algorithm.User>(lib.Properties.Single(p => p.Name == "H").Value);
        Assert.Equal(["x"], h.Params);
    }

    // ── A deferred check is reported where detection would have reported it ──

    [Fact]
    public async Task DeferredChecks_KeepDetectionsOrder_AndTheirCodes()
        => await ParseErrorsAsync(
            "L1 = { public bar(v) = 1 }\nL2 = { public bar(v) = 2 }\nMk(n) = n + 1\nA = Mk(x).Algorithm\nG = {\n    open L1, L2\n    K1(p) = A.bar + p\n    K2(p) = q + p\n    0\n}\n5",
            ("AmbiguousOpen: 'bar' is ambiguous: 2 different opened algorithms provide it at the same open level (L1, L2)", "[7:15, 7:18)"),
            ("UndeclaredIdentifier: Identifier 'q' is used in an explicitly parameterized algorithm", "[8:13, 8:14)"));

    [Fact]
    public async Task DeferredChecks_OfOneBodyAndOfSeveral_KeepTheirFirstOccurrenceOrder()
    {
        // The first occurrence of a name decides where it is reported, a certain fallback included (Q-75 F-A) …
        await ParseErrorsAsync(
            "Mk(n) = n + 1\nA = Mk(x).Algorithm\nG(p) = A.bar.bar + p\n5",
            ("UndeclaredIdentifier: Property 'bar' was not found on `A`, so `A.bar` is the call `bar(A)`", "[3:10, 3:13)"));
        await ParseErrorsAsync(
            "Mk(n) = n + 1\nA = Mk(x).Algorithm\nG(p) = A.bar + bar\n5",
            ("UndeclaredIdentifier: Property 'bar' was not found on `A`, so `A.bar` is the call `bar(A)`", "[3:10, 3:13)"));
        await ParseErrorsAsync(
            "Mk(n) = n + 1\nA = Mk(x).Algorithm\nG(p) = u + A.foo + v + A.bar + foo + p\n5",
            ("UndeclaredIdentifier: Identifier 'u'", "[3:8, 3:9)"),
            ("UndeclaredIdentifier: Property 'foo' was not found on `A`", "[3:14, 3:17)"),
            ("UndeclaredIdentifier: Identifier 'v'", "[3:20, 3:21)"),
            ("UndeclaredIdentifier: Property 'bar' was not found on `A`", "[3:26, 3:29)"));

        // … and bodies report in declaration order, whatever order resolution processes them in (G1 reads G2).
        await ParseErrorsAsync(
            "Mk(n) = n + 1\nA = Mk(x).Algorithm\nG1(p) = A.foo + G2\nG2(p) = A.bar + p\n5",
            ("UndeclaredIdentifier: Property 'foo' was not found on `A`", "[3:11, 3:14)"),
            ("UndeclaredIdentifier: Property 'bar' was not found on `A`", "[4:11, 4:14)"));

        // Detection's reports, an ambiguous certain fallback and a Grace marker on an intrinsic interleave as written.
        await ParseErrorsAsync(
            "L1 = { public bar(v) = 1 }\nL2 = { public bar(v) = 2 }\nMk(n) = n + 1\nA = Mk(x).Algorithm\nG = {\n    open L1, L2\n    K0(p) = qq + p\n    K1(p) = A.bar + A.~string + p\n    K2(p) = q + p\n    0\n}\n5",
            ("UndeclaredIdentifier: Identifier 'qq'", "[7:13, 7:15)"),
            ("AmbiguousOpen: 'bar' is ambiguous", "[8:15, 8:18)"),
            ("InvalidGraceMarker: Grace cannot reorder 'string' because '.string' is the dot-only intrinsic on this receiver", "[8:23, 8:30)"),
            ("UndeclaredIdentifier: Identifier 'q'", "[9:13, 9:14)"));
    }

    [Theory]
    // A certain structural hit beside the navigated body (`Cfg.x`) leaves A = x its own input: the miss is certain.
    [InlineData("Lib = {\n    Cfg = { public x = 1 }\n    public A = x\n    Cfg.x + 0\n}\nG(p) = Lib.A.bar + q\n5", "[6:14, 6:17)", "q", "[6:20, 6:21)")]
    [InlineData("Cfg = {\n    public x = 1\n}\nLib = {\n    public A = x\n    Cfg.x + 0\n}\nG(p) = Lib.A.bar + p\nK(q) = qq\n5", "[8:14, 8:17)", "qq", "[9:8, 9:10)")]
    public async Task ACertainMissOnANavigatedBody_IsReportedInDetectionsOrder(string source, string barSpan, string other, string otherSpan)
        => await ParseErrorsAsync(
            source,
            ("UndeclaredIdentifier: Property 'bar' was not found on `Lib.A`", barSpan),
            ($"UndeclaredIdentifier: Identifier '{other}'", otherSpan));

    [Fact]
    public async Task ACertainFallbackBeforeAWrittenName_IsReportedAtItsMemberToken()
        => await ParseErrorsAsync(
            "Cfg = {\n    public x = 1\n}\nLib = {\n    public A = x\n    Cfg.x + 0\n}\nG(p) = Lib.A.bar + bar\n5",
            ("UndeclaredIdentifier: Property 'bar' was not found on `Lib.A`, so `Lib.A.bar` is the call `bar(Lib.A)`", "[8:14, 8:17)"));

    [Theory]
    // A link body with an input of its own (its x, or one lifted from F): the checks a certain miss makes, worded for it.
    [InlineData("L1 = { public bar(v) = 1 }\nL2 = { public bar(v) = 2 }\nMk(n) = n + 1\nF(x) = x\nA = Mk(F + 0).Algorithm\nG = {\n    open L1, L2\n    K(p) = A.bar + p\n    0\n}\n5", "AmbiguousOpen: 'bar' is ambiguous", "[8:14, 8:17)")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nA = Mk(F + 0).Algorithm\nH = A.~string\n5", "InvalidGraceMarker: Grace cannot reorder 'string' because '.string' is the dot-only intrinsic on this receiver", "[4:7, 4:14)")]
    [InlineData("Mk(n) = n + 1\nA = Mk(x).Algorithm\nH = A.~string\n5", "InvalidGraceMarker: Grace cannot reorder 'string' because '.string' is the dot-only intrinsic on this receiver", "[3:7, 3:14)")]
    [InlineData("Cfg = {\n    public x = 1\n}\nLib = {\n    public A = x\n    Cfg.x + 0\n}\nF = Lib.A.~string\n5", "InvalidGraceMarker: Grace cannot reorder 'string' because '.string' is the dot-only intrinsic on this receiver", "[8:11, 8:18)")]
    // A clause branch's closed check, worded for its family.
    [InlineData("Mk(n) = n + 1\nA = Mk(x).Algorithm\nPick(0) = 0\nPick(n) = A.bar + n\nPick(1)", "UndeclaredIdentifier: Property 'bar' was not found on `A`, so `A.bar` is the call `bar(A)`; 'bar' is not declared in the pattern of conditional branch 'Pick'", "[4:13, 4:16)")]
    public async Task TheChecksOfACertainMiss_AreMade_WithItsWording(string source, string start, string span)
        => await ParseErrorsAsync(source, (start, span));

    [Theory]
    // A link with no input of its own is a runtime reference: its `.bar` is the runtime's, so a written `bar` is the
    // body's first undeclared occurrence (M4★).
    [InlineData("Cap(meta op) = op\nInc(x) = x + 1\nA = Cap(Inc(1)).Algorithm\nG(p) = A.bar + bar\n5", "UndeclaredIdentifier: Identifier 'bar'", "[4:16, 4:19)")]
    public async Task AMissTheRuntimeDecides_IsNeverChecked(string source, string start, string span)
        => await ParseErrorsAsync(source, (start, span));

    [Fact]
    public async Task ADeferredUnit_MakesItsDeferredChecks()
    {
        // MOD-10: a load-bearing branch elaborates as the eager one does — its closed check of a certain miss waits for its
        // own resolution and stops the evaluation.
        const string Module = "https://katlang.org/lazy/a.kat";
        var options = new RunOptions
        {
            DownloadCode = (url, _) => url == Module ? ValueTask.FromResult("public M = 1") : throw new InvalidOperationException(url),
        };
        var result = await KatLangEngine.RunAsync(
            $"Mk(n) = n + 1\nA = Mk(x).Algorithm\nPick(0) = 0\nPick(n) = {{\n    open '{Module}'\n    G(p) = A.bar + p\n    M + n\n}}\nPick(1)",
            options);
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UndeclaredIdentifier, error.Code);
        Assert.Contains("Property 'bar' was not found on `A`, so `A.bar` is the call `bar(A)`", error.Message, StringComparison.Ordinal);
    }

    // ── An inferred fallback name on a receiver resolution decides keeps its receiver-aware provenance ──

    [Theory]
    [InlineData("Mk(n) = n + 1\nA = Mk(x).Algorithm\nA.X", "X", "A", "[3:3, 3:4)")]
    [InlineData("Lib = {\n    Cfg = {\n        public x = 1\n    }\n    public A = x\n    Cfg.x + 0\n}\nLib.A.W", "W", "Lib.A", "[8:7, 8:8)")]
    [InlineData("Lib = {\n    public A = x\n    0\n}\nLib.A.W", "W", "Lib.A", "[5:7, 5:8)")]
    [InlineData("Cfg = {\n    public x = 1\n}\nLib = {\n    public A = x\n    Cfg.x + 0\n}\nLib.A.zzz", "zzz", "Lib.A", "[8:7, 8:10)")]
    // The twins agree on a member path that misses: R.a's structure is O, its own (a fallback calculation).
    [InlineData("B = { public z = 1 }\nR = {\n    public a = R.O\n    public O = B.count\n    0\n}\nR.a.x", "x", "R.a", "[7:5, 7:6)")]
    public async Task ARootFallbackOnACertainMiss_IsWordedForItsReceiver(string source, string member, string receiver, string span)
    {
        var outcome = await ErrAsync(source, "UnresolvedImplicitParams");
        Assert.StartsWith(
            $"UnresolvedImplicitParams: Property '{member}' was not found on `{receiver}`, so the dotted call fell back to a lexical callable named '{member}'.",
            outcome.Errors[0],
            StringComparison.Ordinal);
        Assert.EndsWith("@ " + span, outcome.Errors[0], StringComparison.Ordinal);
    }

    [Fact]
    public async Task AnInferredFallbackNameOnALinkCalculation_KeepsItsReceiverNote()
    {
        var outcome = await ErrAsync("Mk(n) = n + 1\nA = Mk(x).Algorithm\nH = A.foo + 0\nH()", "ArityMismatch");
        Assert.Contains("An implicit parameter 'foo' was inferred at [3:7].", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Contains("Property 'foo' was not found on `A`, so the dotted call fell back to a lexical callable named 'foo'.", outcome.Errors[0], StringComparison.Ordinal);
    }

    [Fact]
    public async Task AFallbackOnARuntimeReference_HasNoReceiverClaim()
    {
        // A runtime reference's members are its target's (M4★): no claim survives about what it lacks.
        var outcome = await ErrAsync("Cap(meta op) = op\nInc(x) = x + 1\nA = Cap(Inc(1)).Algorithm\nA.foo", "UnresolvedImplicitParams");
        Assert.StartsWith("UnresolvedImplicitParams: Identifier 'foo' does not resolve to a property or other visible name here", outcome.Errors[0], StringComparison.Ordinal);
    }

    // ── The sibling order records what a certain miss reads and what a path through the owner selects ──

    [Fact]
    public async Task ACertainMissesRead_IsASiblingDependency_ThatClosesACycle()
    {
        // F's `Lib.A.abs` reads Lib (a certain miss: A is A(x)) and Lib reads F: one cycle, processed in declaration order,
        // so Lib reads F unprocessed and lifts nothing.
        var outcome = await ErrAsync("Cfg = {\n    public x = 1\n}\nLib = {\n    public A = x\n    Cfg.x + F\n}\nF = Lib.A.abs + 0\nLib(-3)", "ArityMismatch");
        Assert.Contains("Callable `Lib` expects 0 arguments, but was called with 1 argument.", outcome.Errors[0], StringComparison.Ordinal);
        await OkAsync("Cfg = {\n    public x = 1\n}\nF = Lib.A.abs + 0\nLib = {\n    public A = x\n    Cfg.x + F\n}\nLib(-3)", "4");
    }

    private static string LinkAliasChain(int size, bool reversed)
    {
        var rows = Enumerable.Range(1, size).Select(i => i < size ? $"A{i} = A{i + 1}.Algorithm\n" : $"A{i} = Y.Algorithm\n");
        return "Y = { public z = 1 }\n" + string.Concat(reversed ? rows.Reverse() : rows) + "0";
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AChainOfLinkAliases_IsProcessedInDependencyOrder_WithoutNesting(bool reversed)
    {
        // `Ai = A(i+1).Algorithm`: each certain intrinsic reads its receiver, so the order processes the receivers first —
        // no read is processed on demand, nested, at any length.
        var source = LinkAliasChain(60, reversed);
        await OkAsync(source, "0");
        var parsed = SourceProvenance.ParseValid(source);
        Assert.All(
            parsed.Root.Properties.Where(p => p.Name.StartsWith('A')),
            property => Assert.True(property.Value is Algorithm.Alias { HasRuntimeTarget: true }, property.Name));
    }

    private static string NeutralLinkChain(int size, bool reversed)
    {
        var rows = Enumerable.Range(1, size).Select(i => i < size ? $"A{i} = Mk(A{i + 1}.foo).Algorithm\n" : $"A{i} = Mk(Y.foo).Algorithm\n");
        return "Mk(n) = n + 1\nfoo(v) = 7\nY = { public z = 1 }\n" + string.Concat(reversed ? rows.Reverse() : rows) + "0";
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ARefinementThatDecidesNoLift_NeverProcessesItsReceiverOnDemand(bool reversed)
    {
        // `A(i+1).foo` reads a link body as MAY in a NEUTRAL slot (Mk's argument): no sibling edge orders it, and a certain
        // miss would give no slot a VALUE role (`foo` is a user callee), so the refinement reads nothing — reading would
        // process the receiver on demand, nested once per link.
        await OkAsync(NeutralLinkChain(60, reversed), "0");
    }

    [Theory]
    // `Lib.G` read inside Lib is the sibling G, whatever the spelling: F lifts G's processed z in either order — exactly
    // as the bare `G` does.
    [InlineData("H(z) = z\nLib = {\n    public G = H + 1\n    public F = Lib.G + 0\n    0\n}\nLib.F(5)", "6")]
    [InlineData("H(z) = z\nLib = {\n    public F = Lib.G + 0\n    public G = H + 1\n    0\n}\nLib.F(5)", "6")]
    [InlineData("H(z) = z\nLib = {\n    public F = G + 0\n    public G = H + 1\n    0\n}\nLib.F(5)", "6")]
    // Through a sibling reference to the owner, and through an outer owner.
    [InlineData("H(z) = z\nLib = {\n    public Me = Lib\n    public F = Me.G + 0\n    public G = H + 1\n    0\n}\nLib.F(5)", "6")]
    [InlineData("H(z) = z\nOuter = {\n    public Lib = {\n        public F = Outer.Lib.G + 0\n        public G = H + 1\n        0\n    }\n    0\n}\nOuter.Lib.F(5)", "6")]
    // E lifts F's x, and C, which reads `R.E`, lifts it from E's processed signature in either order.
    [InlineData("F(x) = x\nR = {\n    public C = R.E + 0\n    public E = F + 0\n    0\n}\nR.C(7)", "7")]
    [InlineData("F(x) = x\nR = {\n    public E = F + 0\n    public C = R.E + 0\n    0\n}\nR.C(7)", "7")]
    public async Task AMemberPathThroughTheOwner_ReadsTheProcessedSibling_InEveryOrder(string source, string value)
        => await OkAsync(source, value);

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AnAliasOfARuntimeMember_ThroughTheOwner_IsARuntimeAlias_InEveryOrder(bool memberFirst)
    {
        // E = p.m is a runtime member reference; C = R.E names it, so C is a runtime-target alias in either order — never a
        // static alias of E's written body.
        var members = memberFirst ? "    public E = p.m\n    public C = R.E\n" : "    public C = R.E\n    public E = p.m\n";
        var source = "R(p) = {\n" + members + "    0\n}\nR({ public m = 5 })";
        var parsed = SourceProvenance.ParseValid(source);
        var r = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(p => p.Name == "R").Value);
        Assert.True(r.Properties.Single(p => p.Name == "C").Value is Algorithm.Alias { HasRuntimeTarget: true });

        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var c = Assert.IsType<PropertyInfo>(model.FindPropertyAt(new SourcePosition(memberFirst ? 3 : 2, 12)));
        Assert.Equal("C", c.Name);
        Assert.True(c.HasUnknownRuntimeSignature);
        Assert.Null(c.AliasTarget);
        Assert.True(c.SupportsLexicalDotCall);
    }

    // ── Both static chases record every stable answer, unknown ones included ──

    private static string NestedRuntimeLinkOwners(int size, bool reversed) => LinkAliasChain(size, reversed);

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task NestedRuntimeLinkOwners_AreDetectedInLinearWork(bool reversed)
    {
        await OkAsync(NestedRuntimeLinkOwners(3, reversed), "0");
        AssertLinear(Detect(NestedRuntimeLinkOwners(100, reversed)).StaticQueryEvaluationCount, Detect(NestedRuntimeLinkOwners(200, reversed)).StaticQueryEvaluationCount, "detection work");
    }

    /// <summary>Owners `Oi = O(i+1).m` over a link-row receiver, or over a link path that misses before its last step.</summary>
    private static string NestedOwnersOverALink(int size, bool missedPath)
        => "Cap(meta op) = op\nInc(x) = x + 1\nfoo(v) = 0\n" + (missedPath ? "X = { public Y = 1 }\n" : "") + "F = {\n"
            + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"    O{i} = O{i + 1}.m\n"))
            + (missedPath ? $"    O{size} = X.foo.Algorithm\n" : $"    O{size} = Cap(Inc(1)).Algorithm\n") + "    O1.foo\n}\nF";

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task NestedOwnersOverALinkReceiver_AreDetectedInLinearWork(bool missedPath)
    {
        await OkAsync(NestedOwnersOverALink(3, missedPath), "0");
        AssertLinear(Detect(NestedOwnersOverALink(100, missedPath)).StaticQueryEvaluationCount, Detect(NestedOwnersOverALink(200, missedPath)).StaticQueryEvaluationCount, "detection work");
    }

    /// <summary>Owners `Oi = O(i+1).m` over a member miss (`OK = B.m`), each named by an alias `Zj = Oj`.</summary>
    private static string AliasesOfNestedOwnersOverAMiss(int size)
        => "m(v) = v\nB = { public z = 1 }\n"
            + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"O{i} = O{i + 1}.m\n")) + $"O{size} = B.m\n"
            + string.Concat(Enumerable.Range(1, size).Select(j => $"Z{j} = O{j}\n")) + "0";

    [Fact]
    public async Task AliasesOfNestedOwnersOverAMiss_AreResolvedInLinearWork()
    {
        // The resolver's chase reads a member path that misses as its owner's own structure (the detector's reading) and
        // records it, so the K aliases' cycle checks cost O(K) together.
        await OkAsync(AliasesOfNestedOwnersOverAMiss(3), "0");
        AssertLinear(Resolve(AliasesOfNestedOwnersOverAMiss(100)).StaticQueryEvaluationCount, Resolve(AliasesOfNestedOwnersOverAMiss(200)).StaticQueryEvaluationCount, "resolver query computations");
    }

    /// <summary>
    /// K references `Fi = Lib.Ai.abs + 0` to K navigated bodies `Ai = xi`, each head a different member name of Lib's one
    /// row `C1.x1 + … + CK.xK`: every reference asks the guard about Lib's rows with a name of its own.
    /// </summary>
    private static string GuardedReferences(int size)
        => string.Concat(Enumerable.Range(1, size).Select(i => $"C{i} = {{ public x{i} = 1 }}\n"))
            + "Lib = {\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    public A{i} = x{i}\n"))
            + "    " + string.Join(" + ", Enumerable.Range(1, size).Select(i => $"C{i}.x{i}")) + "\n}\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"F{i} = Lib.A{i}.abs + 0\n")) + "0";

    [Fact]
    public void TheFallbackNameGuard_WalksEachBodysRowsOnce()
    {
        // The guard reads a navigated body's dot-edge member names from a set built once per body and operation, however
        // many references — each with a name of its own, so no recorded chase answers for another — it is asked about.
        AssertLinear(HistoricalContractAssertions.InputIndexWork(GuardedReferences(50)), HistoricalContractAssertions.InputIndexWork(GuardedReferences(100)), "guard row walks");
    }

    /// <summary>
    /// Owners `Oi = O(i+1).m` over a head no declaration provides (`OK = X.m`, X opened from two providers), each named by
    /// an alias `Zj = Oj`.
    /// </summary>
    private static string AliasesOfNestedOwnersOverAnUnprovidedHead(int size)
        => "m(v) = v\nM1 = { public X = { public z = 1 } }\nM2 = { public X = { public z = 2 } }\nF = {\n    open M1, M2\n"
            + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"    O{i} = O{i + 1}.m\n")) + $"    O{size} = X.m\n"
            + string.Concat(Enumerable.Range(1, size).Select(j => $"    Z{j} = O{j}\n")) + "    0\n}\nF";

    [Fact]
    public async Task AliasesOfNestedOwnersOverAnUnprovidedHead_AreResolvedInLinearWork()
    {
        // A head no declaration provides (here a name two opens provide: the program is erroneous, and the editor still
        // elaborates it) has no static structure — an answer the resolver's chase records like any other — and an owner
        // whose path reads it is its own structure, recorded too, so the K aliases' cycle checks cost O(K) together.
        await ParseErrorsAsync(AliasesOfNestedOwnersOverAnUnprovidedHead(3), ("AmbiguousOpen:", "[8:10, 8:11)"));
        AssertLinear(
            ResolveWithAmbiguousOpens(AliasesOfNestedOwnersOverAnUnprovidedHead(100)).StaticQueryEvaluationCount,
            ResolveWithAmbiguousOpens(AliasesOfNestedOwnersOverAnUnprovidedHead(200)).StaticQueryEvaluationCount,
            "resolver query computations");
    }

    /// <summary><see cref="Resolve"/> over a program whose only detected errors are ambiguous opens.</summary>
    private static FrontEndTraversalObservations ResolveWithAmbiguousOpens(string source)
    {
        var detectedInput = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        var (detected, detection) = detectedInput;
        Assert.NotEmpty(detection);
        Assert.All(detection, diagnostic => Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code));
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();
        _ = ImplicitArgumentResolver.ResolvePrevalidated(detectedInput, observations, diagnostics);
        Assert.Equal(0, diagnostics.ReportedCount);
        return observations;
    }

    /// <summary>`Ai = Lib.A(i+1).abs + 0` inside Lib: each member reads the next one through the owner.</summary>
    private static string OwnerPathChain(int size)
        => "Lib = {\n" + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"    public A{i} = Lib.A{i + 1}.abs + 0\n" : $"    public A{i} = z\n")) + "    0\n}\n0";

    [Fact]
    public async Task AChainOfOwnerPaths_IsResolvedInLinearWork()
    {
        await OkAsync("Lib = {\n    public A1 = Lib.A2.abs + 0\n    public A2 = Lib.A3.abs + 0\n    public A3 = z\n    0\n}\nLib.A1(-4)", "4");
        AssertLinear(Resolve(OwnerPathChain(100)).StaticQueryEvaluationCount, Resolve(OwnerPathChain(200)).StaticQueryEvaluationCount, "resolver query computations");
    }

    // ── A body shared by two scopes decides its deferred checks in each ──

    [Fact]
    public void ABodySharedByTwoScopes_DecidesItsDeferredCheckInEachScope()
    {
        // A host tree may share one body under two scopes whose receivers differ: under L1, `R.bar` reads a link body that
        // keeps an input (a calculation, so `bar` is a certain miss the closed G checks); under L2, a runtime link (the
        // runtime decides: no check). Each scope's check waits on the edge's provisional miss IN that scope.
        const string source = "Mk(n) = n + 1\nCap(meta op) = op\nInc(x) = x + 1\nL1 = {\n    R = Mk(x).Algorithm\n    H = {\n"
            + "        G(p) = R.bar + p\n        0\n    }\n    0\n}\nL2 = {\n    R = Cap(Inc(1)).Algorithm\n    0\n}\n0";
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        var shared = ((Algorithm.User)root.Properties.Single(p => p.Name == "L1").Value).Properties.Single(p => p.Name == "H");
        var sharedRoot = root with
        {
            Properties = [.. root.Properties.Select(p => p.Name == "L2" && p.Value is Algorithm.User l2
                ? p with { Value = l2 with { Properties = [.. l2.Properties, shared] } }
                : p)],
        };

        foreach (var tree in new[] { root, sharedRoot })
        {
            var diagnostics = new DiagnosticBag();
            var detectedInput = ParameterDetector.DetectPrevalidated(tree, diagnostics: diagnostics);
            var (detected, _) = detectedInput;
            _ = ImplicitArgumentResolver.ResolvePrevalidated(detectedInput, observations: null, diagnostics);
            var report = Assert.Single(diagnostics);
            Assert.Equal(DiagnosticCode.UndeclaredIdentifier, report.Code);
            Assert.Equal("[7:18, 7:21)", report.Span.ToString());
        }
    }
}
