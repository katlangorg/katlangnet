namespace KatLang.Tests;

/// <summary>
/// B3-5★ SIGNATURE SELECTION (November 2026; owner direction 2026-11-05: X-04 = plain A-agree, CG4 = A-agree). Implicit-argument
/// resolution decides every inferred signature of an operation — and through it every <c>.Algorithm</c> link's class —
/// JOINTLY, before it rewrites anything: one equation per written body per declaring context (D1a), rule G6 over the
/// joint classifications, the closed gate and simultaneous completion for cycles. No read observes a provisional signature, so declaration order is
/// unobservable, and a group with no selected answer is refused with a front-end error of the
/// <see cref="DiagnosticCode.SelfDependentInferredParameters"/> family, on A1's recovery route.
///
/// <para>Pinned here: the programs recursive inference leaves untouched; the link-classification categories (only self-supporting, undetermined U1, no
/// consistent reading); the research outcomes carried forward (D06 = 5, D15 = 4, ReadQ, the FU7 example, deferred
/// 10 / 11, case H's module reuse); bounded selection with explicit resource refusal; and cancellation and resource
/// exhaustion followed by a successful retry. Declaration-order permutations of helper-only "cycles" are pinned by
/// <see cref="SiblingDependencyCycleTests"/>.</para>
/// </summary>
public sealed class SignatureSelectionTests
{
    private const string Host = "modules.example";

    private static IEnumerable<T[]> Permutations<T>(IReadOnlyList<T> items)
    {
        if (items.Count <= 1)
        {
            yield return [.. items];
            yield break;
        }

        for (var index = 0; index < items.Count; index++)
        {
            var rest = items.Where((_, other) => other != index).ToArray();
            foreach (var tail in Permutations(rest))
                yield return [items[index], .. tail];
        }
    }

    private static string Program(IEnumerable<string> declarations, string row) => string.Join("\n", declarations) + "\n" + row;

    /// <summary>The 1-based line a declaration starting with <paramref name="prefix"/> is on.</summary>
    private static int LineOf(string source, string prefix)
        => Array.FindIndex(source.Split('\n'), line => line.StartsWith(prefix, StringComparison.Ordinal)) + 1;

    private static async Task<SixRouteAgreement.Observation> RefusedOnEveryRoute(string source, int errors)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "parse", $"{source}\ngave {observation}");
        Assert.Equal(errors, observation.Errors.Count);
        Assert.All(observation.Errors, error => Assert.StartsWith($"{nameof(KatLangErrorCode.SelfDependentInferredParameters)}: ", error, StringComparison.Ordinal));
        Assert.Empty(observation.HostCalls);
        return observation;
    }

    private static async Task AssertValueOnEveryRoute(string source, string value)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation is { Kind: "ok" } && observation.Value == value, $"{source}\ngave {observation}");
    }

    // ── What recursive inference leaves untouched (RecursiveParameterInferenceTests pins the completions) ──────

    /// <summary>
    /// What X-04 leaves alone: explicit recursive calls never lift; a self-read whose body infers nothing reads a
    /// zero-parameter value (Q-37 re-entrancy); a closed list is final, so its bare self-read lifts its own binding.
    /// </summary>
    [Fact]
    public async Task RecursionThatLiftsNothing_IsUnaffected()
    {
        await AssertValueOnEveryRoute("Fact = if(n <= 1, 1, n * Fact(n - 1))\nFact(5)", "120");
        await AssertValueOnEveryRoute("A = if(tick() < 3, A + 1, 0)\nA, A", "S[2, 2]");
        await AssertValueOnEveryRoute("F(x) = if(tick() > 3, x, F + 1)\nF(10)", "13");
    }

    // ── .Algorithm link classification: refusal categories ───────────────────────────────────────

    private const string LinkPrelude = "Cap(meta op) = op\nId(v) = v\nC(a, *p) = a\n";

    /// <summary>
    /// The link classes G6 decides, and the categories it refuses with. NL1 has one grounded reading in either order.
    /// DC1 and U1 changed deliberately with recursive inference: a counterfactual that had no meaning now completes, so
    /// their runtime reading is the one grounded answer. The two refused categories below keep a group that really does not
    /// settle, <c>A</c> and <c>B</c> without the link's read: only a self-supporting reading is left, or one that cannot be
    /// decided. CG4 has no consistent reading.
    /// </summary>
    [Fact]
    public async Task LinkClassification_SelectsTheGroundedReading_OrRefusesWithItsCategory()
    {
        foreach (var declared in Permutations(["    K = L.abs + 0", "    L = Cap(Id(K + C + 0)).Algorithm"]))
            await AssertValueOnEveryRoute(LinkPrelude + "Outer(a) = {\n" + string.Join("\n", declared) + "\n    0\n}\n0", "0");

        const string Dc1 = LinkPrelude + "B(p) = p\nD(z) = z\nOuter(a) = {\n    L = Cap(Id(K + 0)).Algorithm\n    K = L.repeat(D) + 0\n"
            + "    X = L.repeat(C) + B + Y\n    Y = X + 0\n    0\n}\n0";
        await AssertValueOnEveryRoute(Dc1, "0");

        const string U1 = LinkPrelude + "B(p) = p\nD(z) = z\nOuter(a) = {\n    L = Cap(Id(K + X + 0)).Algorithm\n    K = L.repeat(D) + 0\n"
            + "    X = L.repeat(C) + B + Y\n    Y = X + 0\n    0\n}\n0";
        await AssertValueOnEveryRoute(U1, "0");

        const string Group = "W(x, y) = x\nX1(x) = x\nY1(y) = y\nD(z) = z\n";
        const string Members = "    K = L.repeat(D) + 0\n    A = L.repeat(W) + B + X1\n    B = A + Y1\n    0\n}\n0";

        // Without L, A and B alternate; with it W fixes their order, and L reads only K, so L supports itself.
        var ungrounded = await RefusedOnEveryRoute(LinkPrelude + Group + "Outer(a) = {\n    L = Cap(Id(K + 0)).Algorithm\n" + Members, errors: 2);
        Assert.All(ungrounded.Errors, error => Assert.Contains("because every consistent reading of the .Algorithm reference 'L' supports only itself", error, StringComparison.Ordinal));

        // L reads A too, so whether L stands without its own support is the question that does not settle.
        var undetermined = await RefusedOnEveryRoute(LinkPrelude + Group + "Outer(a) = {\n    L = Cap(Id(K + A + 0)).Algorithm\n" + Members, errors: 4);
        Assert.All(undetermined.Errors, error => Assert.Contains(
            "because deciding the .Algorithm reference 'L' depends on a recursive inference that does not settle",
            error, StringComparison.Ordinal));

        foreach (var declared in Permutations(["    L1 = Cap(Id(H1 + 0)).Algorithm", "    H1 = L1.abs.repeat(A0) + B"]))
        {
            var source = LinkPrelude + "A0 = C + 0\nB(p) = p\nOuter(a) = {\n" + string.Join("\n", declared) + "\n    0\n}\n0";
            var cg4 = await RefusedOnEveryRoute(source, errors: 2);
            Assert.All(cg4.Errors, error => Assert.Contains(
                "because no consistent reading of the .Algorithm reference 'L1' exists: whether it is a calculation depends on the parameters this inference would give it",
                error, StringComparison.Ordinal));
        }
    }

    // ── The research outcomes carried forward ────────────────────────────────────────────────────

    /// <summary>
    /// D06: a block member reached through a path lifts its owner's reading of <c>A</c> (formerly the reader saw the
    /// block before it was processed and inferred nothing — an arity error at the call). D15: the same read through a
    /// transparent reference. Both in every declaration order and with renamed or wider callees.
    /// </summary>
    [Theory]
    [InlineData("A(x) = x\nH = { public Q = A + 0 }.Q + 1\nH(4)", "5")]
    [InlineData("H = { public Q = A + 0 }.Q + 1\nA(x) = x\nH(4)", "5")]
    [InlineData("A(x) = x\nH = { public Q = A + 0 }.Q + 1\nH(5)", "6")]
    [InlineData("Z(y) = y\nK = { public W = Z + 0 }.W + 1\nK(4)", "5")]
    [InlineData("A(x, y) = x + y\nH = { public Q = A + 0 }.Q + 1\nH(4, 5)", "10")]
    [InlineData("A(x) = x\nB = { public Q = A + 0 }\nH = B.Q + 1\nH(4)", "5")]
    [InlineData("A(x) = x\nR = { public Q = A + 0 }.Q\nR(4)", "4")]
    [InlineData("R = { public Q = A + 0 }.Q\nA(x) = x\nR(4)", "4")]
    [InlineData("A(x) = x\nB = { public Q = A + 0 }\nR = B.Q\nR(4)", "4")]
    [InlineData("F(0) = 0\nF(n) = {\n    A(x) = x + n\n    H = { public Q = A + 0 }.Q\n    H(1)\n}\nF(2)", "3")]
    public Task D06AndD15_LiftThroughBlockMembers(string source, string value) => AssertValueOnEveryRoute(source, value);

    /// <summary>ReadQ: a parameter's member read through a declared body, a transparent reference and a carrier.</summary>
    [Theory]
    [InlineData(7, 7, 8, "Lib", "S[7, 7, 8, 100, 100, 100]")]
    [InlineData(7, 7, 9, "Lib", "S[7, 7, 9, 100, 100, 100]")]
    [InlineData(7, 70, 8, "Lib2", "S[7, 70, 8, 100, 200, 100]")]
    public Task ReadQ_ReadsTheTargetsMembersThroughAReference_AndTheCarriersOwn(int lib, int lib2, int car, string referenced, string value)
    {
        _ = lib;
        var source = $"Lib = {{\n    public Q = 7\n    100\n}}\nLib2 = {{\n    public Q = {lib2}\n    200\n}}\nRef = {referenced}\n"
            + $"Car = {{\n    public Q = {car}\n    Lib\n}}\nReadQ(f) = f.Q\nReadQ(Lib), ReadQ(Ref), ReadQ(Car), Lib, Ref, Car";
        return AssertValueOnEveryRoute(source, value);
    }

    /// <summary>The FU7 documentation example: a member named like a callable never confuses the call with the member.</summary>
    [Fact]
    public Task Fu7Example_SeparatesTheCallFromTheMember()
        => AssertValueOnEveryRoute("Q(x) = x + 100\n\nLib = {\n    public Q = 7\n    0\n}\n\nQ(Lib)\nLib.Q\nLib", "S[100, 7, 0]");

    // ── Modules and deferred units ───────────────────────────────────────────────────────────────

    private static RunOptions ModuleOptions(IReadOnlyDictionary<string, string> modules, Action? onDownload = null,
        CancellationToken evaluation = default, SourceProcessingLimits? limits = null)
        => new()
        {
            AllowedHosts = [Host],
            DownloadCode = (url, _) =>
            {
                onDownload?.Invoke();
                return ValueTask.FromResult(modules[url]);
            },
            EvaluationCancellationToken = evaluation,
            SourceProcessingLimits = limits,
        };

    private static async Task AssertModuleValue(string source, IReadOnlyDictionary<string, string> modules, string value)
    {
        var result = await KatLangEngine.RunAsync(source, ModuleOptions(modules));
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(value, SixRouteAgreement.Neutral(success.Value));
    }

    private const string D06Module = "A(x) = x\nH = { public Q = A + 0 }.Q + 1\n0";
    private const string D15Module = "A(x) = x\nR = { public Q = A + 0 }.Q\n0";

    /// <summary>D06 and D15 inside a loaded module, eagerly and in a deferred unit selected at run time.</summary>
    [Theory]
    [InlineData(D06Module, "M = load('https://modules.example/u.kat')\nM.H(4)", "5")]
    [InlineData(D15Module, "M = load('https://modules.example/u.kat')\nM.R(4)", "4")]
    [InlineData(D06Module, "G(0) = 0\nG(a) = {\n    M = load('https://modules.example/u.kat')\n    M.H(a)\n}\nG(4)", "5")]
    [InlineData(D15Module, "G(0) = 0\nG(a) = {\n    M = load('https://modules.example/u.kat')\n    M.R(a)\n}\nG(4)", "4")]
    public Task D06AndD15_InModulesAndDeferredUnits(string module, string source, string value)
        => AssertModuleValue(source, new Dictionary<string, string> { ["https://modules.example/u.kat"] = module }, value);

    /// <summary>D06 in a deferred unit whose own reading of <c>A</c> reads a module member: 4 + 10 + 1.</summary>
    [Fact]
    public Task D06_InADeferredUnitThatReadsItsModule()
        => AssertModuleValue(
            "G(0) = 0\nG(a) = {\n    M = load('https://modules.example/z.kat')\n    A(x) = x + M.Z\n    H = { public Q = A + 0 }.Q + 1\n    H(a)\n}\nG(4)",
            new Dictionary<string, string> { ["https://modules.example/z.kat"] = "Z = 10\n0" },
            "15");

    private const string QModule = "Lib = {\n    public Algorithm = 5\n    0\n}\nX = Lib.Algorithm\nY = Cap(F(2)).Algorithm\nCap(meta op) = op\nF(x) = x + 1\n0";
    private const string CModule = "Cap(meta op) = op\nF(x) = x + 1\nL = Cap(F(2)).Algorithm\nG(f) = f(5)\nK = L.G\nA(x) = x\nR = { public Q = A + 0 }.Q(4)\n0";
    private const string CProgram = "G(0) = 0\nG(a) = {\n    M = load('https://modules.example/c.kat')\n    M.K + M.R + a\n}\nG(1)";

    /// <summary>
    /// Deferred selection (research "deferred 10 / 11"): the member and intrinsic answers of a deferred unit — a declared
    /// <c>Algorithm</c> member, a runtime link, a fallback through a link, a block member — are selected by the deferred
    /// operation: 5 + 4 + 1 and 6 + 4 + 1.
    /// </summary>
    [Fact]
    public async Task DeferredUnits_SelectTheirOwnLinksAndMembers()
    {
        await AssertModuleValue(
            "G(0) = 0\nG(a) = {\n    M = load('https://modules.example/q.kat')\n    M.X + M.Y(3) + a\n}\nG(1)",
            new Dictionary<string, string> { ["https://modules.example/q.kat"] = QModule },
            "10");
        await AssertModuleValue(CProgram, new Dictionary<string, string> { ["https://modules.example/c.kat"] = CModule }, "11");
    }

    /// <summary>
    /// Case H: a deferred unit (<c>b.kat</c>, loaded by a branch of <c>a.kat</c>) loads <c>a.kat</c> again — one canonical
    /// URL is one module declaration (Q-32), so it reads the eager unit's selected facts: <c>V</c> lifts <c>K</c>'s
    /// parameter through the reference <c>KR</c> (3 + 7), and <c>W</c> reads the carrier's own member (3).
    /// </summary>
    [Fact]
    public Task ADeferredUnit_ReusesTheEagerUnitOfTheModuleItLoads()
        => AssertModuleValue(
            "M = load('https://modules.example/a.kat')\nM.G(0), M.KC.Q",
            new Dictionary<string, string>
            {
                ["https://modules.example/a.kat"] = "K(x) = x\nKR = K\nKC = {\n    public Q = 3\n    K\n}\nG(0) = {\n"
                    + "    N = load('https://modules.example/b.kat')\n    N.V(3) + N.W\n}\nG(n) = n\n0",
                ["https://modules.example/b.kat"] = "M = load('https://modules.example/a.kat')\nV = M.KR + 7\nW = M.KC.Q\n0",
            },
            "S[13, 3]");

    // ── Bounded selection, cancellation and exhaustion ───────────────────────────────────────────

    private const string ChainPrelude = "Cap(meta op) = op\nId(v) = v\nD(z) = z\n";

    /// <summary>
    /// A chain of 40 links, each one's class decided by the previous one's (<c>K_i</c> reads <c>D</c> only when
    /// <c>L_i</c> is a calculation): every link is a component of its own, so selection costs one table of one vector per
    /// equation — never 2^40 classifications — and every link is a calculation.
    /// </summary>
    [Fact]
    public void AChainOfLinks_IsSelectedOneComponentAtATime()
    {
        const int Links = 40;
        var source = ChainPrelude + "K0 = D + 0\n"
            + string.Concat(Enumerable.Range(1, Links).Select(i => $"L{i} = Cap(Id(K{i - 1} + 0)).Algorithm\nK{i} = L{i}.repeat(D) + 0\n"))
            + "0";
        var parsed = SourceProvenance.ParseValid(source);
        foreach (var i in Enumerable.Range(1, Links))
        {
            Assert.Equal(["z"], Assert.Single(parsed.Root.Properties, property => property.Name == $"K{i}").Value.Params);
            Assert.Equal(["z"], Assert.IsType<Algorithm.User>(Assert.Single(parsed.Root.Properties, property => property.Name == $"L{i}").Value).Params);
        }
    }

    /// <summary>A ring of links: <c>L_i</c> reads <c>K_i</c>, whose read of <c>D</c> is guarded by <c>L_(i+1)</c>.</summary>
    private static string LinkRing(int links)
        => ChainPrelude
            + string.Concat(Enumerable.Range(0, links).Select(i => $"L{i} = Cap(Id(K{i} + 0)).Algorithm\nK{i} = L{(i + 1) % links}.repeat(D) + 0\n"))
            + "0";

    /// <summary>
    /// A ring of three links is one joint region: "all calculations" supports only itself, so the unique grounded reading
    /// makes every link a runtime reference. A ring of 64 would enumerate 2^64 classifications: it is refused as an
    /// explicit structural resource refusal (<see cref="DiagnosticCode.StaticStructureLimitExceeded"/>), never an
    /// inference rule, and nothing is published.
    /// </summary>
    [Fact]
    public void AJointRegion_IsSelectedWithinItsBound_AndRefusedBeyondIt()
    {
        var small = SourceProvenance.ParseValid(LinkRing(3));
        foreach (var i in Enumerable.Range(0, 3))
        {
            Assert.True(Assert.Single(small.Root.Properties, property => property.Name == $"L{i}").Value is Algorithm.Alias { HasRuntimeTarget: true });
            Assert.Empty(Assert.Single(small.Root.Properties, property => property.Name == $"K{i}").Value.Params);
        }

        var large = Parser.Parse(LinkRing(64));
        var refusal = Assert.Single(large.Diagnostics, diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, refusal.Code);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(LinkRing(64)));
    }

    /// <summary>
    /// A deferred unit's selection observes the run's cancellation (here requested while the module is downloaded), and
    /// leaves nothing behind: the same program in a fresh run selects the unit and gives 11.
    /// </summary>
    [Fact]
    public async Task ACancelledDeferredSelection_LeavesNothingBehind_AndARetrySucceeds()
    {
        var modules = new Dictionary<string, string> { ["https://modules.example/c.kat"] = CModule };
        using var cancellation = new CancellationTokenSource();
        await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => KatLangEngine.RunAsync(CProgram, ModuleOptions(modules, onDownload: cancellation.Cancel, evaluation: cancellation.Token)));

        await AssertModuleValue(CProgram, modules, "11");
    }

    /// <summary>
    /// A deferred unit whose structural work exceeds the host's envelope is refused at run time with the structural
    /// resource error (never another value); a run under the default envelope selects it and gives 11.
    /// </summary>
    [Fact]
    public async Task AnExhaustedDeferredSelection_IsAResourceRefusal_AndARetryUnderTheDefaultEnvelopeSucceeds()
    {
        var padded = string.Join('\n', Enumerable.Range(0, 1000).Select(i => $"public P{i}={i}+0")) + "\n" + CModule;
        var modules = new Dictionary<string, string> { ["https://modules.example/c.kat"] = padded };

        var refused = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(CProgram,
            ModuleOptions(modules, limits: new() { MaxStaticStructureBytes = 4 * 1024 * 1024 })));
        Assert.Contains(refused.Errors, error => error.Code == KatLangErrorCode.StaticStructureLimitExceeded);

        await AssertModuleValue(CProgram, modules, "11");
    }
}
