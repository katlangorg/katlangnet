namespace KatLang.Tests;

/// <summary>
/// ALIAS-UNIFY-1 (M4★) tenth independent-review regressions. Source cases run on the six routes of
/// <see cref="SixRouteAgreement"/>; a deferred unit runs through the engine with an in-memory downloader; the scaling
/// facts compare the passes' own observations (<see cref="FrontEndTraversalObservations"/>) at two sizes. Detection reads
/// a body whose row ends in an <c>.Algorithm</c> link, and a navigated body whose head an enclosing body may infer as a
/// fallback name, as a structure the runtime decides; implicit-argument resolution decides it — from its input, where a
/// navigated body has the inputs detection gave it, and by processing a link body, a runtime reference only with no
/// input of its own, inferred, graced or lifted — refines a dot edge that reads it from MAY to MUST, and decides the
/// checks detection deferred for a certain miss. A structure or
/// target recorded while the body it reaches is in progress is completed with that body's processed form, in a deferred
/// unit too. Every static chase of either pass records what it learns once, nested member paths and sibling cycles
/// included, and the resolver reads an unprocessed sibling as written, so its answers and its wording never depend on
/// the processing order.
/// </summary>
public sealed class AliasUnifyTenthReviewRegressionTests
{
    private static async Task OkAsync(string source, string value)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(value, outcome.Value);
    }

    private static async Task CheckedMissAsync(string source, string member, string receiver)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", outcome.Kind);
        Assert.StartsWith($"UndeclaredIdentifier: Property '{member}' was not found on `{receiver}`", outcome.Errors[0], StringComparison.Ordinal);
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

    // ── A link body's input — from its receiver, its lifting or an enclosing binding — is resolution's to decide ──

    [Theory]
    // `X.foo` misses on X: its fallback name foo is A's input, so A is a calculation, its own structure.
    [InlineData("Mk(n) = n + 1\nX = {\n    public Y = 1\n}\nA = Mk(X.foo).Algorithm\nG(p) = A.bar + p\n5", "bar", "A")]
    // `5.abs.size`: size is the certain fallback name of a value, A's input.
    [InlineData("A = 5.abs.size.Algorithm\nG(p) = A.bar + p\n5", "bar", "A")]
    // `x.y` reads F's parameter, so y may be A's input: resolution decides it is.
    [InlineData("Mk(n) = n + 1\nF(p) = {\n    x = p\n    A = Mk(x.y).Algorithm\n    G(q) = A.foo + q\n    0\n}\nF(1)", "foo", "A")]
    // Mk infers t, so lifting gives A the parameter t.
    [InlineData("Mk = t + 1\nA = Mk.Algorithm\nG(p) = A.bar + p\n5", "bar", "A")]
    // The carrier C forwards to F(x), so lifting gives A the parameter x.
    [InlineData("F(x) = x\nC = { F }\nA = C.Algorithm\nG(p) = A.bar + p\n5", "bar", "A")]
    // B has the input x, so it is a calculation and A, a link of a calculation, keeps B's input.
    [InlineData("Mk(n) = n + 1\nB = Mk(x).Algorithm\nA = B.Algorithm\nG(p) = A.bar + p\n5", "bar", "A")]
    // The written control: Mk(t) requires t, so A lifts it.
    [InlineData("Mk(t) = t + 1\nA = Mk.Algorithm\nG(p) = A.bar + p\n5", "bar", "A")]
    // Lifting F inside the link's receiver gives A an input of its own.
    [InlineData("Mk(n) = n + 1\nF(x) = x\nA = Mk(F + 0).Algorithm\nG(p) = A.bar + p\n5", "bar", "A")]
    [InlineData("Mk(n) = n + 1\nF = x + 1\nA = Mk(F + 0).Algorithm\nG(p) = A.bar + p\n5", "bar", "A")]
    public async Task ALinkBodyWithAnInputOfItsOwn_IsItsOwnStructure_ThatAClosedListChecks(string source, string member, string receiver)
        => await CheckedMissAsync(source, member, receiver);

    [Theory]
    // A reads F's t, an enclosing binding: no input of its own, a runtime reference whose `.bar` the runtime decides.
    [InlineData("Mk(t) = t + 1\nF(t) = {\n    A = Mk.Algorithm\n    G(p) = A.bar + p\n    0\n}\nF(1)", "0")]
    [InlineData("Cap(meta op) = op\nLib = {\n    public bar = 7\n    1\n}\nMk(t) = Cap(Lib())\nF(t) = {\n    A = Mk.Algorithm\n    G(p) = A.bar + p\n    G(1)\n}\nF(5)", "8")]
    // An `.Algorithm` step before the last misses on X: A is a calculation the runtime decides, never checked.
    [InlineData("X = {\n    public Y = 1\n}\nA = X.Algorithm.Algorithm\nG(p) = A.bar + p\n5", "5")]
    [InlineData("Cap(meta op) = op\nLib = {\n    public bar = 7\n    1\n}\nfoo(v) = Cap(Lib())\nX = {\n    public Y = 1\n}\nA = X.foo.Algorithm\nG(p) = A.bar + p\nG(1)", "8")]
    // A runtime link with no input: `.bar` is the runtime's.
    [InlineData("Cap(meta op) = op\nInc(x) = x + 1\nA = Cap(Inc(1)).Algorithm\nG(p) = A.bar + p\n5", "5")]
    public async Task ALinkBodyWithNoInputOfItsOwn_IsARuntimeReference(string source, string value)
        => await OkAsync(source, value);

    [Theory]
    // Mk infers t and F lifts x into the link's receiver: A(t) / A(x) is a calculation, so `A.abs` lifts A into H, and
    // A(3) projects `.Algorithm` from Mk(…) = 4, a number.
    [InlineData("Mk = t + 1\nA = Mk.Algorithm\nH = A.abs + 0\nH(3)")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nA = Mk(F + 0).Algorithm\nH = A.abs + 0\nH(3)")]
    public async Task ALinkBodyWithAnInputOfItsOwn_IsLiftedIntoItsCertainFallback(string source)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith("TypeMismatch:", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Contains("`Algorithm` requires a call reference, got numeric value 4", outcome.Errors[0], StringComparison.Ordinal);
    }

    [Fact]
    public async Task ACertainFallbackNameOnALinkCalculation_IsCheckedForAmbiguity()
    {
        // A(x) is a calculation, so `A.bar` certainly takes its fallback, whose name two opens provide (Q-29).
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(
            "L1 = { public bar(v) = 1 }\nL2 = { public bar(v) = 2 }\nMk(n) = n + 1\nA = Mk(x).Algorithm\nG = {\n    open L1, L2\n    A.bar + 0\n}\n5");
        Assert.Equal("parse", outcome.Kind);
        Assert.StartsWith("AmbiguousOpen: 'bar' is ambiguous: 2 different opened algorithms provide it at the same open level (L1, L2)", outcome.Errors[0], StringComparison.Ordinal);
    }

    // ── A navigated body beside a structural hit of its head's name infers that name itself ──

    [Theory]
    // `Cfg.Inner.x`, `Cfg.x` through an open, a reference and a block: structural hits, so Lib infers no x — A is A(x)
    // and F lifts it. (Detection's guard counts every member name an enclosing body's dot edges give and leaves such a
    // body to implicit-argument resolution, which decides it from the processed body.)
    [InlineData("Lib = {\n    Cfg = {\n        public Inner = {\n            public x = 1\n        }\n    }\n    public A = x\n    Cfg.Inner.x + 0\n}\nF = Lib.A.abs + 0\nF(-3)", "3")]
    [InlineData("Configs = {\n    public Cfg = {\n        public x = 1\n    }\n}\nLib = {\n    open Configs\n    public A = x\n    Cfg.x + 0\n}\nF = Lib.A.abs + 0\nF(-3)", "3")]
    [InlineData("Defaults = {\n    public x = 1\n}\nLib = {\n    Cfg = Defaults\n    public A = x\n    Cfg.x + 0\n}\nF = Lib.A.abs + 0\nF(-3)", "3")]
    [InlineData("Lib = {\n    public A = x\n    { public x = 1 }.x + 0\n}\nF = Lib.A.abs + 0\nF(-3)", "3")]
    // `5.x` may take its fallback x: Lib may infer x, so `Lib.A` is the runtime's and `.bar` is never checked.
    [InlineData("Lib = {\n    public A = x\n    5.x\n}\nG(p) = Lib.A.bar + p\n5", "5")]
    public async Task ANavigatedBodysHead_IsItsOwnInput_UnlessAnEnclosingBodyMayInferIt(string source, string value)
        => await OkAsync(source, value);

    [Theory]
    // Read through Lib while Lib is in progress: the guard decides `A = x` (no edge of Lib may take the fallback x) …
    [InlineData("Lib = {\n    public A = x\n    G(p) = Lib.A.bar + p\n    0\n}\n5", "bar", "Lib.A")]
    [InlineData("Lib = {\n    G(p) = Lib.A.bar + p\n    public A = x\n    0\n}\n5", "bar", "Lib.A")]
    // … and resolution decides a link body: its processed form, or the written body detection already gave an input.
    [InlineData("Mk(n) = n + 1\nLib = {\n    public A = Mk(x).Algorithm\n    G(p) = Lib.A.bar + p\n    0\n}\n5", "bar", "Lib.A")]
    [InlineData("Mk(n) = n + 1\nLib = {\n    G(p) = Lib.A.bar + p\n    public A = Mk(x).Algorithm\n    0\n}\n5", "bar", "Lib.A")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nLib = {\n    public A = Mk(F + 0).Algorithm\n    G(p) = Lib.A.bar + p\n    0\n}\n5", "bar", "Lib.A")]
    [InlineData("Mk(n) = n + 1\nF(x) = x\nLib = {\n    G(p) = Lib.A.bar + p\n    public A = Mk(F + 0).Algorithm\n    0\n}\n5", "bar", "Lib.A")]
    public async Task AReceiverReadThroughItsBodyInProgress_HasACertainMiss_ThatAClosedListChecks(string source, string member, string receiver)
        => await CheckedMissAsync(source, member, receiver);

    [Theory]
    [InlineData("Lib = {\n    public A = x\n    public F = Lib.A.abs + 0\n    0\n}\nLib.F(-3)", "3")]
    [InlineData("Cap(meta op) = op\nOnly(*xs) = 5\nLib = {\n    public A = Cap(Only(x)).Algorithm\n    public H = Lib.A.abs + 0\n    0\n}\nLib.H(3)", "5")]
    // A link body detection already gave an input of its own (x) is a calculation whatever resolution lifts: the miss is
    // certain from the input, with nothing processed, and A — which only names H in a neutral slot — is processed first.
    [InlineData("Cap(meta op) = op\nOnly(*xs) = 5\nLib = {\n    public H = Lib.A.abs + 0\n    public A = Cap(Only(x, H)).Algorithm\n    0\n}\nLib.H(3)", "5")]
    // A runtime link with no input stays the runtime's, read through its body in progress too.
    [InlineData("Cap(meta op) = op\nInc(x) = x + 1\nLib = {\n    public A = Cap(Inc(1)).Algorithm\n    G(p) = Lib.A.bar + p\n    0\n}\n5", "5")]
    public async Task AReceiverReadThroughItsBodyInProgress_IsLiftedIntoItsCertainFallback(string source, string value)
        => await OkAsync(source, value);

    [Fact]
    public async Task ANavigatedBodyWhoseHeadIsAStructuralHit_HasACertainMiss_ThatAClosedListChecks()
        => await CheckedMissAsync(
            "Lib = {\n    Cfg = {\n        public Inner = {\n            public x = 1\n        }\n    }\n    public A = x\n    Cfg.Inner.x + 0\n}\nG(p) = Lib.A.bar + p\n5",
            "bar",
            "Lib.A");

    // ── A structure or target read while its body is in progress is completed with the processed body ──

    [Theory]
    // b reaches U's member h through R's open while R is in progress: its structure is h's processed body, whose k lifts F.
    [InlineData("F(x) = x\nU = {\n    public h = {\n        public k = F + 0\n    }\n}\nR = {\n    open U\n    public a = R\n    public b = h\n    a.b.k + 0\n}\nR(7)")]
    [InlineData("F(x) = x\nV = {\n    public k = F + 0\n}\nR = {\n    public a = R\n    public b = V\n    a.b.k + 0\n}\nR(7)")]
    // R.a's target is R, in progress when a is elaborated: the recorded target is R as processed, which lifts F.
    [InlineData("F(x) = x\nR = {\n    public a = R\n    F + 0\n}\nZ = R.a + 0\nZ(7)")]
    [InlineData("F(x) = x\nR = {\n    public a = R\n    F + 0\n}\nZ = R + 0\nZ(7)")]
    [InlineData("F(x) = x\nR = {\n    public a = R\n    F + 0\n}\nQ(x) = R.a\nQ(7)")]
    public async Task AStructureOrTargetReadWhileItsBodyIsInProgress_IsTheProcessedBody(string source)
        => await OkAsync(source, "7");

    [Fact]
    public async Task ADeferredUnit_ReadsTheStructuresItsEagerRunProcessed()
    {
        // MOD-10: the load-bearing branch elaborates exactly as the eager branch does. b's structure, reached through R's
        // open of the eager U, is U.h as the eager run processed it, so G lifts k's F: G(7) is 7.
        const string Module = "https://katlang.org/lazy/a.kat";
        const string Declarations = "F(x) = x\nU = {\n    public h = {\n        public k = F + 0\n    }\n}\nPick(0) = 0\n";
        const string Body = "    R = {\n        open U\n        public a = R.b\n        public b = h\n        0\n    }\n    G = R.a.k + 0\n    G(7)\n}\nPick(1)";
        var fetches = 0;
        var options = new RunOptions
        {
            DownloadCode = (url, _) =>
            {
                fetches++;
                return url == Module ? ValueTask.FromResult("public A = 1") : throw new InvalidOperationException(url);
            },
        };

        var deferred = await KatLangEngine.RunAsync(Declarations + $"Pick(n) = {{\n    open '{Module}'\n" + Body, options);
        Assert.Equal("7", Assert.IsType<RunResult.Success>(deferred).ToDisplayString().ReplaceLineEndings("\n"));
        Assert.Equal(1, fetches);

        var eager = await KatLangEngine.RunAsync(Declarations + "Pick(n) = {\n" + Body, options);
        Assert.Equal("7", Assert.IsType<RunResult.Success>(eager).ToDisplayString().ReplaceLineEndings("\n"));
    }

    // ── An unprocessed sibling is read as written: one answer and one wording whatever the processing order ──

    [Theory]
    // X is processed while UA (an alias of the unnameable family U) is not, or the other way round: either way the
    // diagnostic names UA as the alias it is, by the hop that reached U.
    [InlineData("X = UA + 0\nUA = U\nU(0) = X\nU(1) = 1\n5", "UA")]
    [InlineData("UA = U\nX = UA + 0\nU(0) = X\nU(1) = 1\n5", "UA")]
    [InlineData("UA = U\nU(0) = 0\nU(1) = 1\nX = UA + 0\n5", "UA")]
    [InlineData("X = UB + 0\nUB = UA\nUA = U\nU(0) = X\nU(1) = 1\n5", "UB")]
    // A dotted path whose head L is unprocessed (L reads X) reaches L's member UA statically, in either order.
    [InlineData("X = L.UA + 0\nL = {\n    public UA = U\n    X + 0\n}\nU(0) = 1\nU(1) = 1\n5", "L.UA")]
    [InlineData("L = {\n    public UA = U\n    X + 0\n}\nX = L.UA + 0\nU(0) = 1\nU(1) = 1\n5", "L.UA")]
    public async Task AnAliasOfAnUnnameableFamily_IsNamedAsAnAlias_InEveryProcessingOrder(string source, string alias)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", outcome.Kind);
        Assert.StartsWith(
            $"UnliftableClauseFamily: '{alias}' is used as a value here, but '{alias}', an alias of clause family 'U', has no formula-lifting signature",
            outcome.Errors[0],
            StringComparison.Ordinal);
    }

    // ── Every static chase records what it learns once ──

    /// <summary>Owners O1 → … → OK (`Oi = O(i+1).m`) over a parameter receiver (`OK = p.m`): each body is its own structure.</summary>
    private static string OwnersOverAParameterReceiver(int size)
        => "foo(v) = 0\nF(p) = {\n" + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"    O{i} = O{i + 1}.m\n"))
            + $"    O{size} = p.m\n    O1.foo\n}}\nF({{ public m = 1 }})";

    /// <summary>Owners O1 → … → OK over a member miss (`OK = B.m`, B declaring no m): each body is its own structure.</summary>
    private static string OwnersOverADeterminedMiss(int size)
        => "foo(v) = 0\nB = { public z = 1 }\nF(p) = {\n" + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"    O{i} = O{i + 1}.m\n"))
            + $"    O{size} = B.m\n    O1.foo\n}}\nF(1)";

    [Theory]
    [InlineData("parameter-receiver")]
    [InlineData("determined-miss")]
    public async Task NestedOwnersOverAReceiverThatNamesNoMember_AreDetectedInLinearWork(string shape)
    {
        // Each owner's structure is itself — over a parameter (the runtime's) or over a declared miss — and is recorded
        // once, so the K chases (each owner's row, each OD-D walk) cost O(K) together.
        Func<int, string> generate = shape == "parameter-receiver" ? OwnersOverAParameterReceiver : OwnersOverADeterminedMiss;
        await OkAsync(generate(3), "0");
        var small = Detect(generate(100));
        var large = Detect(generate(200));
        var ratio = (double)large.StaticQueryEvaluationCount / small.StaticQueryEvaluationCount;
        Assert.True(ratio < 2.6, $"Doubling the size grew the detection work {ratio:F2}x ({small.StaticQueryEvaluationCount} -> {large.StaticQueryEvaluationCount}).");
    }

    /// <summary>
    /// K bodies `Qi = { open Oi ⏎ z + 0 }` over nested owners `Oi = O(i+1).m`, `OK = R.m` with `R.m = R`: each open
    /// target's chase meets the owners below it one level deeper than a chase started at them recorded them.
    /// </summary>
    private static string OpensOfNestedOwners(int size, bool reversed)
    {
        var owners = string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"O{i} = O{i + 1}.m\n" : $"O{i} = R.m\n"));
        var order = reversed ? Enumerable.Range(1, size).Reverse() : Enumerable.Range(1, size);
        var opens = string.Concat(order.Select(i => $"Q{i} = {{\n    open O{i}\n    z + 0\n}}\n"));
        return "R = {\n    public m = R\n    public z = 1\n    0\n}\n" + owners + opens + "Q1";
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task OpenTargetsOverNestedOwners_AreDetectedAndResolvedInLinearWork(bool reversed)
    {
        // An open target's chase is bounded by fuel; a recorded stretch is followed with the fuel it NEEDS, so a chase
        // that meets it deeper than it was recorded still follows it (in reverse order each open meets the previous
        // one's owners one level deeper).
        await OkAsync(OpensOfNestedOwners(3, reversed), "1");
        var small = Detect(OpensOfNestedOwners(100, reversed));
        var large = Detect(OpensOfNestedOwners(200, reversed));
        var ratio = (double)large.StaticQueryEvaluationCount / small.StaticQueryEvaluationCount;
        Assert.True(ratio < 2.6, $"Doubling the size grew the detection work {ratio:F2}x ({small.StaticQueryEvaluationCount} -> {large.StaticQueryEvaluationCount}).");
        var smallResolve = Resolve(OpensOfNestedOwners(100, reversed));
        var largeResolve = Resolve(OpensOfNestedOwners(200, reversed));
        var resolveRatio = (double)largeResolve.StaticQueryEvaluationCount / Math.Max(1, smallResolve.StaticQueryEvaluationCount);
        Assert.True(resolveRatio < 2.6, $"Doubling the size grew the resolver query computations {resolveRatio:F2}x ({smallResolve.StaticQueryEvaluationCount} -> {largeResolve.StaticQueryEvaluationCount}).");
    }

    /// <summary>
    /// Nested owners `Oi = hi.a` whose heads an open of the sibling U provides (`U.hi = O(i+1)`): U and the owners form a
    /// sibling cycle, so the resolver reads each owner's chain while its members are still unprocessed.
    /// </summary>
    private static string NestedOwnersThroughASiblingCycle(int size)
        => "Y = { public z = { public w = 1 } }\nP = {\n    open U\n    U = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"        public h{i} = O{i + 1}\n" : $"        public h{i} = R\n"))
            + "    }\n    R = {\n        public a = R\n        public w = { public z = 1 }\n        0\n    }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    O{i} = h{i}.a\n"))
            + "    X = O1.w\n    M = {\n        open Y\n        public B = z\n        0\n    }\n    Q = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"        public h{i} = 0\n")) + "    }\n"
            + "    M.B.w\n    X.z\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    Q.h{i}\n")) + "}\nP";

    /// <summary>Member paths `Bi = Si.k` over opened members `Si = mi` whose `k` is the next `B(i+1)`: a sibling cycle through U.</summary>
    private static string WaitingPathsThroughASiblingCycle(int size)
        => "Y = { public z = { public w = 1 } }\nP = {\n    open U\n    U = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"        public m{i} = {{ public k = B{i + 1} }}\n" : $"        public m{i} = {{ public k = {{ public w = {{ public z = 1 }} }} }}\n"))
            + "    }\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    S{i} = m{i}\n    B{i} = S{i}.k\n"))
            + "    X = B1.w\n    M = {\n        open Y\n        public B = z\n        0\n    }\n    Q = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"        public m{i} = 0\n")) + "    }\n"
            + "    M.B.w\n    X.z\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    Q.m{i}\n")) + "}\nP";

    /// <summary>Owners `Oi = O(i+1).a` over an inner chain `C1 = m1`, `U.m1 = C2`, …: each OD-D walk reaches the owner chain one link deeper.</summary>
    private static string OwnersOverAnInnerChain(int size)
        => "Y = { public z = { public w = 1 } }\nP = {\n    open U\n    U = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"        public m{i} = C{i + 1}\n" : $"        public m{i} = R\n"))
            + "    }\n    R = {\n        public a = R\n        public w = { public z = 1 }\n        0\n    }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    C{i} = m{i}\n"))
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"    O{i} = O{i + 1}.a\n" : $"    O{i} = C1.a\n"))
            + "    X = O1.w\n    M = {\n        open Y\n        public B = z\n        0\n    }\n    Q = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"        public m{i} = 0\n")) + "    }\n"
            + "    M.B.w\n    X.z\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    Q.m{i}\n")) + "}\nP";

    [Theory]
    [InlineData("nested-owners")]
    [InlineData("waiting-paths")]
    [InlineData("owners-over-an-inner-chain")]
    public async Task TheResolversStaticWalks_AreLinear_OverNestedPathsAndSiblingCycles(string shape)
    {
        // A recorded stretch is followed wherever a chase reaches it with the fuel it needs, an unprocessed sibling is read
        // as written (so its reads are recorded too), and the static invocation walk records where it ends: the K
        // owners' walks cost O(K) together.
        Func<int, string> generate = shape switch
        {
            "nested-owners" => NestedOwnersThroughASiblingCycle,
            "waiting-paths" => WaitingPathsThroughASiblingCycle,
            _ => OwnersOverAnInnerChain,
        };
        await OkAsync(generate(3), "S[1, 1, 0, 0, 0]");
        var small = Resolve(generate(100));
        var large = Resolve(generate(200));
        Assert.True(small.StaticQueryEvaluationCount > 0, "The resolver computed no query.");
        var ratio = (double)large.StaticQueryEvaluationCount / small.StaticQueryEvaluationCount;
        Assert.True(ratio < 2.6, $"Doubling the size grew the resolver query computations {ratio:F2}x ({small.StaticQueryEvaluationCount} -> {large.StaticQueryEvaluationCount}).");
    }
}
