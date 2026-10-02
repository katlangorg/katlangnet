using KatLang.Evaluation;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// CALLABLE ALIASES ARE BINDING INDIRECTION (FWD-02; decided October 1 2026). A body whose ONE written
/// row is a bare reference to a callable that declares parameterized callable structure is a callable
/// ALIAS (<see cref="Algorithm.Alias"/>) in an open body: the alias keeps its own BINDING — declaration,
/// exposure, zero-argument cache key, editor symbol — while every CALLABLE use of it is the target's own,
/// resolved once in the alias's declaration scope. No wrapper, no copied signature, no invocation.
///
/// <para>THE DIRECT-CALL ORACLE: for <c>A = F</c>, every invocation through <c>A</c> (and through
/// <c>B = A</c>, <c>C = B</c>) is the direct invocation of <c>F</c> with the same supply — the same value
/// or failure, the same host effects in the same order, on every execution route — up to the written
/// name in its frames. Pinned below over EVERY builtin of the registry, the user callable shapes,
/// Math members (alias, canonical and opened spellings), host operations, opened and dotted members,
/// nameable and unnameable families. Then the key witnesses: callable identity, cache separation, the
/// zero-parameter boundary, roles (X-45), the narrowed Q-77, navigation and <c>open</c>, the target fixed
/// in the declaration scope, negative controls, recursion, resource accounting, diagnostics, the editor
/// model, long chains and host-built cycles.</para>
/// </summary>
public class CallableAliasBindingIndirectionTests
{
    private static Task<RepeatedNameConstraintTests.Observation> OnEveryRoute(string source, long? seed = null)
        => RepeatedNameConstraintTests.OnEveryRouteAsync(source, seed);

    private static async Task<string> Outcome(string source, long? seed = null)
        => RepeatedNameConstraintTests.Rendered(await OnEveryRoute(source, seed));

    /// <summary>The written callee names a chain uses, replaced by the target's name for the oracle.</summary>
    private static readonly string[] ChainNames = ["AliasThree", "AliasTwo", "AliasOne"];

    /// <summary>
    /// The alias outcome with each written alias name replaced by the name the direct call writes in
    /// the same message: a user or Math callee's signature is displayed under the WRITTEN callee name
    /// (`Callable `A(x)``), and a dotted target under its member name (`Callable `Round(value, digits)``).
    /// </summary>
    private static string AsDirect(string outcome, string target)
    {
        var written = target[(target.LastIndexOf('.') + 1)..];
        foreach (var name in ChainNames)
            outcome = outcome.Replace(name, written, StringComparison.Ordinal);
        return outcome;
    }

    /// <summary>
    /// THE DIRECT-CALL ORACLE over one supply: <c>A(supply)</c>, <c>B(supply)</c> and <c>C(supply)</c> through
    /// a three-link chain over <paramref name="target"/> each have <c>target(supply)</c>'s outcome and host
    /// log on every route, the written names aside.
    /// </summary>
    private static async Task AssertAliasIsTheDirectCall(string declarations, string target, string supply)
    {
        var chain = $"AliasOne = {target}\nAliasTwo = AliasOne\nAliasThree = AliasTwo\n";
        var direct = await Outcome($"{declarations}{target}({supply})");
        foreach (var alias in ChainNames)
        {
            var through = await Outcome($"{declarations}{chain}{alias}({supply})");
            Assert.True(
                direct == AsDirect(through, target),
                $"{alias}({supply}) through `{target}`\n  direct: {direct}\n  alias:  {through}\ndeclarations:\n{declarations}");
        }
    }

    // ── 1. Every builtin of the registry ─────────────────────────────────────────────────

    private const string Vocabulary =
        "Inc(x) = trace(x) + 1\nAcc(item, acc) = item + acc\nIsBig(x) = x > 1\nBad = trace(0) / 0\n"
        + "Step(s) = s + 1\nCont(s) = s + 1, s < 3\n";

    /// <summary>Supplies that exercise every builtin's adapter, laziness, callbacks, loops and failures.</summary>
    private static readonly string[] BuiltinSupplies =
    [
        "", "[3, 1, 2]", "[3, 1, 2], 2", "[3, 1, 2], 7", "[1, 2, 3], Inc", "[1, 2, 3], IsBig", "[1, 2], Acc, 0",
        "true, 1, Bad", "false, Bad, 2", "Step, 3, 0", "Cont, 0", "1, 4", "[], Bad", "[[1, 2], 3]", "Bad", "(1, 2)*",
        "[[1], [1, 2]], count",
    ];

    public static TheoryData<string> EveryBuiltin()
    {
        var data = new TheoryData<string>();
        foreach (var builtin in Enum.GetValues<BuiltinId>())
            data.Add(builtin.ToString());
        return data;
    }

    [Theory]
    [MemberData(nameof(EveryBuiltin))]
    public async Task EveryBuiltin_ThroughAnAliasChain_IsTheBuiltinItself(string builtin)
    {
        Assert.Equal(21, Enum.GetValues<BuiltinId>().Length);
        foreach (var supply in BuiltinSupplies)
            await AssertAliasIsTheDirectCall(Vocabulary, builtin, supply);
    }

    /// <summary>The §33 witnesses, pinned verbatim.</summary>
    [Theory]
    [InlineData("C = count\nC([1, 2, 3])", "ok 3")]
    [InlineData("I = if\nI(true, 1, 1 / 0)", "ok 1")]
    [InlineData("Bad(x) = trace(x) / 0\nM = map\nM([], Bad)", "ok L[]")]
    [InlineData("Inc(x) = x + 1\nR = repeat\nR(Inc)",
        "err ArityMismatch: Callable `repeat(step, count, initialState)` expects at least 3 arguments, but was called with 1 argument.")]
    [InlineData("Fact(0) = 1\nFact(n) = n * Fact(n - 1)\nF = Fact\nF(1, 2)",
        "err NoMatchingBranch: while evaluating call to F: No matching branch for 'F'")]
    [InlineData("Inc(x) = x + 1\nA = abs\nK = A(Inc)\nK(-5)", "ok 4")]
    [InlineData("C = count\nW(collection) = C\nW([1, 2])", "ok 2")]
    [InlineData("C = count\nK = C + 1\nK([1, 2])", "ok 3")]
    [InlineData("S(1) = 1\nS(-1) = -1\nSA = S\nSA(-1), SA(1)", "ok S[-1, 1]")]
    public async Task KeyRegressionWitnesses(string source, string expected)
        => Assert.Equal(expected, await Outcome(source));

    [Theory]
    [InlineData("open Lib\nLib = {\n    public Only(*xs) = tick()\n}\nA = Only\nB = A\nC = B\nC, Lib.Only, A, B, C",
        "ok S[1, 2, 3, 4, 1] [tick#1,tick#2,tick#3,tick#4]")]
    [InlineData("F = y + 1\nLib = {\n    public A = F\n}\nG = {\n    W(x) = Lib.A\n    W(1) + y\n}\nG(10)", "ok 21")]
    [InlineData("I = if\nB = I\nApply(f) = f(true, trace(1), trace(2) / 0)\nApply(B)", "ok 1 [trace(1)]")]
    [InlineData("Inc(x) = trace(x) + 1\nR = repeat\nB = R\nApply(f) = f(Inc, 3, 0)\nApply(B)", "ok 3 [trace(0),trace(1),trace(2)]")]
    [InlineData("U((0, x)) = x\nU([x, 0]) = x\nA = U\nB = A\nmap([(0, 4), [5, 0]], B)", "ok L[4, 5]")]
    [InlineData("Only(*xs) = tick()\nA = Only\nP(f, f) = f()\nP(A, Only)",
        "err ArityMismatch: while evaluating call to P: Bad arity [tick#1,tick#2]")]
    [InlineData("F(x) = {\n    M = 2\n    x\n}\nA = {\n    M = 1\n    F\n}\nB = A\nM(v) = 9\nNavigate(f) = f.M\nA.M, F.M, B.M, Navigate(A)", "ok S[1, 2, 9, 2]")]
    [InlineData("K = C + 1\nC = B\nB = A\nA = F\nF = Inc + 1\nInc(x) = x + 1\nK(3)", "ok 6")]
    [InlineData("C = count\nC(trace(1) / 0, trace(2))",
        "err ArityMismatch: Callable `count(collection)` expects 1 argument, but was called with 2 arguments. [trace(1),trace(2)]")]
    public async Task HostileCompositionWitnesses(string source, string expected)
        => Assert.Equal(expected, await Outcome(source, seed: 7));

    // ── 2. User callables, Math members, host operations, members, families ─────────────────

    public static TheoryData<string, string, string> UserShapes => new()
    {
        // declarations, target, supplies (separated by `|`)
        { "F(x) = trace(x) * 10\n", "F", "7|7, 8||(1, 2)|[1, 2]" },
        { "F(x, y) = x - y\n", "F", "10, 3|10|(10, 3)|10, 3, 1" },
        { "F(*xs) = xs\n", "F", "|1|1, 2|(1, 2)|[1, 2]*|()" },
        { "F(a, *m, z) = [a, m, z]\n", "F", "1, 2|1, 2, 3, 4|1|" },
        { "F((a, b)) = a + b\n", "F", "(2, 3)|[2, 3]|2, 3|" },
        { "F([a, *r]) = [a, r]\n", "F", "[1, 2, 3]|[1]|[]|1" },
        { "F(([a, b], c)) = a + b + c\n", "F", "([1, 2], 3)|((1, 2), 3)" },
        { "Bad = trace(0) / 0\nF(x, x) = x\n", "F", "7, 7|7, 8|Bad, 7|7, Bad" },
        { "F((), []) = 1\n", "F", "(), []|[], ()|" },
        { "F = x * y + z\n", "F", "1, 2, 3|1, 2" },
        { "G(x) = trace(x) + 1\nF = G * 2\n", "F", "5|" },
        { "Inc(x) = x + 1\nF(f, v) = f(v)\n", "F", "Inc, 4|4, Inc" },
        { "F(n) = if(n == 0, 0, n + F(n - 1))\n", "F", "4|0" },
        { "F(x) = trace(x) + trace(x + 1)\n", "F", "3" },
        { "Fact(0) = 1\nFact(n) = n * Fact(n - 1)\n", "Fact", "4|0|1, 2|" },
        { "S(1) = 1\nS(-1) = -1\n", "S", "1|-1|0|" },
        { "", "trace", "5||5, 6" },
        { "", "sin", "0||0, 1" },
        { "", "Math.Sin", "0|" },
        { "", "Math.Round", "2.567, 1|2.5" },
        { "", "atan2", "1, 2" },
        { "Lib = {\n    public F(x) = x + 1\n}\n", "Lib.F", "5||5, 6" },
        { "Lib = {\n    public Inner = {\n        public F(x) = x * 3\n    }\n}\n", "Lib.Inner.F", "5" },
        { "open Lib\nLib = {\n    public F(x) = x + 1\n}\n", "F", "5|" },
        { "open Math\n", "Sin", "0" },
    };

    [Theory]
    [MemberData(nameof(UserShapes))]
    public async Task EveryCallableShape_ThroughAnAliasChain_IsTheDirectCall(string declarations, string target, string supplies)
    {
        foreach (var supply in supplies.Split('|'))
            await AssertAliasIsTheDirectCall(declarations, target, supply);
    }

    [Fact]
    public async Task LoadedModuleMember_IsAliasedLikeADocumentCallable()
    {
        static RunOptions Serving(string module) => new() { DownloadCode = (_, _) => ValueTask.FromResult(module) };
        const string Module = "public F(x) = x * 3\npublic A = F\npublic Fam(0) = 0\npublic Fam(n) = n + 1";
        const string Document = "M = load('https://katlang.org/aliases/module.kat')\nB = M.F\nC = M.A\nD = M.Fam\nB(2), C(3), M.A(4), D(0), D(5)";
        var result = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(Document, Serving(Module)));
        Assert.Equal([6m, 9m, 12m, 0m, 6m], result.Atoms);
    }

    // ── 3. Callable identity, caching and the zero-parameter boundary ────────────────────────

    [Theory]
    [InlineData("P(f, f) = f(7)\nOnly(*xs) = 0\nA = Only\nP(A, Only)", "ok 0")]
    [InlineData("P(f, f) = f(7)\nOnly(*xs) = 0\nA = Only\nB = A\nP(B, Only), P(Only, B), P(A, B)", "ok S[0, 0, 0]")]
    [InlineData("P(f, f) = f(1)\nP(count, C)\nC = count", "err TypeMismatch: Type mismatch: Repeated bind equality requires the same callable identity")]
    public async Task CallableIdentity_IsTheTargets(string source, string expected)
    {
        // The last row is the control: a bare `count` passed as an ARGUMENT is a value demand of the
        // builtin, so its algorithm channel is count's own; `C`, an alias, is count's callable too —
        // and still the two VALUE outcomes differ (a value-less builtin), which Q-05 rejects.
        var outcome = await Outcome(source);
        if (expected.StartsWith("err TypeMismatch", StringComparison.Ordinal))
            Assert.StartsWith("err ", outcome, StringComparison.Ordinal);
        else
            Assert.Equal(expected, outcome);
    }

    [Theory]
    // A parameterized alias read bare is its target's zero-supply demand under its OWN cache entry.
    [InlineData("Only(*xs) = tick()\nA = Only\nA, Only, A", "ok S[1, 2, 1] [tick#1,tick#2]")]
    // An explicit call is fresh and populates nothing.
    [InlineData("Only(*xs) = tick()\nA = Only\nA(), A, A", "ok S[1, 2, 2] [tick#1,tick#2]")]
    [InlineData("Only(*xs) = tick()\nA = Only\nA, A(), A", "ok S[1, 2, 1] [tick#1,tick#2]")]
    // Each link of a chain is its own binding.
    [InlineData("Only(*xs) = tick()\nA = Only\nB = A\nB, A, B, Only", "ok S[1, 2, 1, 3] [tick#1,tick#2,tick#3]")]
    // A ZERO-PARAMETER target is READ, never aliased: ordinary property composition and caching.
    [InlineData("Z = tick()\nA = Z\nA, Z, A", "ok S[1, 1, 1] [tick#1]")]
    [InlineData("Z = tick()\nA = Z\nB = A\nB, A, Z", "ok S[1, 1, 1] [tick#1]")]
    public async Task Caching_FollowsTheBinding_NeverTheTarget(string source, string expected)
        => Assert.Equal(expected, await Outcome(source));

    [Fact]
    public void ZeroParameterTarget_IsNoAlias_WhileACollectorOnlyTargetIs()
    {
        var root = SourceProvenance.ParseValid("Z = 3\nOnly(*xs) = 0\nA = Z\nB = Only\n0").Root;
        Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "A").Value);
        Assert.Equal("Only", Assert.IsType<Expr.Resolve>(Assert.IsType<Algorithm.Alias>(root.Properties.Single(p => p.Name == "B").Value).Target).Name);
    }

    [Fact]
    public async Task Randomness_DrawsFollowTheCallAndTheBinding()
    {
        // `random(start, end)` is a parameterized Math member: `R = random` is an alias, and every CALL
        // through it draws afresh, exactly as a direct call does.
        Assert.Equal("ok S[false, false]", await Outcome("R = random\nR(0, 1) == R(0, 1), random(0, 1) == random(0, 1)", seed: 7));
        // A collector-only random wrapper behind an alias: its BARE reads are cached per binding — one
        // draw for B, another for A.
        Assert.Equal("ok S[true, false, true]", await Outcome("A(*xs) = random(0, 1)\nB = A\n(B == B), (B == A), (A == A)", seed: 7));
    }

    // ── 4. Roles, lifting and forwarding read the normalized target ──────────────────────────

    [Theory]
    // X-45: an argument of a call through an alias takes the TARGET's role.
    [InlineData("Inc(x) = x + 1\nA = abs\nK = A(Inc)\nK(-5)", "ok 4")]
    [InlineData("Inc(x) = x + 1\nA = Math.Abs\nB = A\nK = B(Inc)\nK(-5)", "ok 4")]
    [InlineData("Inc(x) = x + 1\nI = if\nK = I(c, Inc, 0)\nK(true, 4)", "ok 5")]
    [InlineData("Pair(x) = x, x\nC = count\nK = C(Pair)\nK(1)", "ok 2")]
    // A callback slot keeps the callable: through an alias of map, Inc is called per element.
    [InlineData("Inc(x) = x + 1\nM = map\nK = M([1, 2], Inc)\nK", "ok L[2, 3]")]
    // A user callee's argument stays neutral through an alias of it.
    [InlineData("Inc(x) = x + 1\nApply(f) = f(10)\nA = Apply\nA(Inc)", "ok 11")]
    // Formula lifting through an alias chain reads the target's lifting signature.
    [InlineData("C = count\nB = C\nK = B + 1\nK([1, 2, 3])", "ok 4")]
    [InlineData("F(x, y) = x * y\nA = F\nK = A * 2\nK(3, 4)", "ok 24")]
    // Bare forwarding through an alias chain reads the target's contract.
    [InlineData("C = count\nB = C\nW(collection) = B\nW([1, 2])", "ok 2")]
    [InlineData("F(x) = x + 1\nA = F\nW(x) = A\nW(4)", "ok 5")]
    public async Task RolesLiftingAndForwarding_ReadTheNormalizedTarget(string source, string expected)
        => Assert.Equal(expected, await Outcome(source));

    [Theory]
    [InlineData("Apply(f) = f(-5)\nApply({ abs })", "ok 5")]
    [InlineData("Apply(f) = f([1, 2])\nApply({ count })", "ok 2")]
    [InlineData("Apply(f) = f(true, 1, 1 / 0)\nApply({ if })", "ok 1")]
    [InlineData("E(0) = 0\nE(n) = n\nApply(f) = f(2)\nApply({ E })", "ok 2")]
    public async Task InlineAliasesOnTheCallableChannel_AreTargets(string source, string expected)
        => Assert.Equal(expected, await Outcome(source));

    /// <summary>
    /// X-45's closed-list half: Q-15's strict-value trigger follows the alias target. Under a closed list
    /// that cannot supply Inc's <c>y</c>, a call through an alias of a Math member is the front-end
    /// diagnostic the direct spelling is — the same code and message — through a chain, the canonical
    /// member, a dotted alias member and the must-selected dot fallback <c>Inc.A</c>.
    /// </summary>
    [Theory]
    [InlineData("A = abs\nK(z) = A(Inc)", "K(z) = abs(Inc)")]
    [InlineData("A = abs\nB = A\nK(z) = B(Inc)", "K(z) = abs(Inc)")]
    [InlineData("A = abs\nB = A\nC = B\nK(z) = C(Inc)", "K(z) = abs(Inc)")]
    [InlineData("A = Math.Abs\nK(z) = A(Inc)", "K(z) = Math.Abs(Inc)")]
    [InlineData("A = abs\nK(z) = Inc.A", "K(z) = Inc.abs")]
    [InlineData("Lib = {\n    public A = abs\n}\nK(z) = Lib.A(Inc)", "K(z) = abs(Inc)")]
    [InlineData("A = abs\nK(z) = A(Inc + 0)", "K(z) = abs(Inc + 0)")]
    [InlineData("open Math\nA = Abs\nK(z) = A(Inc)", "open Math\nK(z) = Abs(Inc)")]
    [InlineData("open Math\nA = Abs\nB = A\nC = B\nK(z) = C(Inc)", "open Math\nK(z) = Abs(Inc)")]
    [InlineData("Lib = {\n    public Inner = {\n        public A = Math.Abs\n        public B = A\n        public C = B\n    }\n}\nK(z) = Lib.Inner.C(Inc)", "K(z) = Math.Abs(Inc)")]
    [InlineData("K(z) = C(Inc)\nC = B\nB = A\nA = abs", "K(z) = abs(Inc)")]
    public void ClosedListStrictValueDiagnostic_FollowsTheAliasTarget(string throughAlias, string direct)
    {
        static IReadOnlyList<Diagnostic> Diagnostics(string program)
        {
            var open = program.StartsWith("open ", StringComparison.Ordinal) ? program[..(program.IndexOf('\n') + 1)] : "";
            return SourceProvenance.ExpectFrontEndError(open + "Inc(y) = y + 1\n" + program[open.Length..] + "\nK(1)");
        }

        var expected = Diagnostics(direct);
        Assert.Contains(expected, static d => d.Code == DiagnosticCode.UndeclaredIdentifier);
        Assert.Equal(
            expected.Select(static d => (d.Code, d.Message)),
            Diagnostics(throughAlias).Select(static d => (d.Code, d.Message)));
    }

    /// <summary>
    /// The negative controls: a host operation's arguments are values but never strict, and a user
    /// callee's argument is neutral — through an alias, as directly, a closed list that cannot supply
    /// Inc's <c>y</c> parses and fails at run time with the target's own outcome.
    /// </summary>
    [Theory]
    [InlineData("", "trace")]
    [InlineData("F(x) = x\n", "F")]
    public async Task ClosedListWithoutAStrictTarget_KeepsTheDirectRunTimeOutcome(string declarations, string target)
    {
        var program = "Inc(y) = y + 1\n" + declarations;
        var direct = await Outcome(program + $"K(z) = {target}(Inc)\nK(1)");
        Assert.StartsWith("err ", direct);
        Assert.Equal(direct, AsDirect(await Outcome(program + $"AliasOne = {target}\nK(z) = AliasOne(Inc)\nK(1)"), target));
    }

    [Fact]
    public void UnnameableFamily_IsAliasable_ButNeitherLiftableNorForwardable()
    {
        const string Sign = "S(1) = 1\nS(-1) = -1\nSA = S\n";
        Assert.IsType<Algorithm.Alias>(SourceProvenance.ParseValid(Sign + "SA(1)").Root.Properties.Single(p => p.Name == "SA").Value);

        // A formula over the alias is the family's own UnliftableClauseFamily ...
        var lifting = Assert.Single(SourceProvenance.ExpectFrontEndError(Sign + "K = SA + 1\n0"));
        Assert.Equal(DiagnosticCode.UnliftableClauseFamily, lifting.Code);

        // ... and a CLOSED lone row is the narrowed Q-77 front-end error: positioned at the written
        // callee, naming it, explaining the missing parameter names, with no internal terminology.
        const string Closed = Sign + "W(x) = SA\n\nW(1)";
        var rejection = Assert.Single(SourceProvenance.ExpectFrontEndError(Closed));
        Assert.Equal(DiagnosticCode.UnforwardableCallable, rejection.Code);
        Assert.Equal(new SourcePosition(4, 8), Assert.NotNull(rejection.Span).Start);
        Assert.Contains("'SA'", rejection.Message, StringComparison.Ordinal);
        Assert.Contains("has no parameter names to forward by", rejection.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("contract", rejection.Message, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("lifting signature", rejection.Message, StringComparison.OrdinalIgnoreCase);
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(Closed));
        Assert.Equal(KatLangErrorCode.UnforwardableCallable, Assert.Single(failure.Errors).Code);

        // The same through the family directly and through a chain.
        Assert.Equal(DiagnosticCode.UnforwardableCallable, Assert.Single(SourceProvenance.ExpectFrontEndError("S(1) = 1\nS(-1) = -1\nW(x) = S\n0")).Code);
        Assert.Equal(DiagnosticCode.UnforwardableCallable, Assert.Single(SourceProvenance.ExpectFrontEndError(Sign + "SB = SA\nW(x) = SB\n0")).Code);
        // A clause branch is a closed body too.
        Assert.Equal(DiagnosticCode.UnforwardableCallable, Assert.Single(SourceProvenance.ExpectFrontEndError(Sign + "W(0) = 0\nW(n) = SA\n0")).Code);
    }

    // ── 5. Navigation and open ───────────────────────────────────────────────────────────

    private const string LibWithMember = "Lib(x) = {\n    K = 5\n    x\n}\nA = Lib\nNavigate(f) = f.K\n";

    [Fact]
    public async Task WrittenMemberAccess_NeverFollowsAnAlias_ButACallablePassedThroughOneIsTheTarget()
    {
        Assert.Equal("ok 5", await Outcome(LibWithMember + "Lib.K"));
        Assert.Equal("ok 5", await Outcome(LibWithMember + "Navigate(Lib)"));
        Assert.Equal("ok 5", await Outcome(LibWithMember + "Navigate(A)"));
        // `A.K`: A declares no K, so the dot falls back to a lexical K, which nothing declares.
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(LibWithMember + "A.K"));
        Assert.Equal(KatLangErrorCode.UnresolvedImplicitParams, Assert.Single(failure.Errors).Code);
    }

    [Theory]
    [InlineData("Lib(x) = x\nA = Lib\nB = {\n    open A\n    1\n}\nB")]
    [InlineData("Lib = {\n    public F(x) = x\n}\nA = Lib.F\nB = {\n    open A\n    1\n}\nB")]
    [InlineData("Only(*xs) = 0\nA = Only\nB = {\n    open A\n    1\n}\nB")]
    [InlineData("C = count\nB = {\n    open C\n    1\n}\nB")]
    public void OpenOfACallableAlias_IsRefused(string source)
    {
        var rejection = Assert.Single(SourceProvenance.ExpectFrontEndError(source), d => d.Code == DiagnosticCode.IllegalInOpen);
        Assert.Contains("is a callable alias, not a namespace", rejection.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("Lib = {\n    public F(x) = x + 1\n}\nA = Lib.F\nA(1)")]
    [InlineData("open Lib\nLib = {\n    public F(x) = x + 1\n}\nA = F\nA(1)")]
    [InlineData("Lib = {\n    public F(x) = x + 1\n}\nOuter = {\n    open Lib\n    A = F\n    A(1)\n}\nOuter")]
    public async Task OpenedOrDottedSpellingOfTheTarget_ChangesNothing(string source)
        => Assert.Equal("ok 2", await Outcome(source));

    // ── 6. The target is fixed in the alias's declaration scope ─────────────────────────────

    [Theory]
    // A later nearer F never re-resolves the alias.
    [InlineData("F(x) = x + 1\nA = F\nOuter = {\n    F(x) = x * 100\n    A(5)\n}\nOuter", "ok 6")]
    // Nor does a parameter named F at the use site.
    [InlineData("F(x) = x + 1\nA = F\nG(F) = A(3)\nTen(x) = 10\nG(Ten)", "ok 4")]
    // An opened target stays the one the alias's scope selected.
    [InlineData("Lib = {\n    public F(x) = x + 1\n}\nOuter = {\n    open Lib\n    A = F\n    Inner = {\n        F(x) = 0\n        A(1)\n    }\n    Inner\n}\nOuter", "ok 2")]
    // A captured owner: the alias of a member that captures `k` is resolved per activation.
    [InlineData("Make(k) = {\n    Add(x) = x + k\n    A = Add\n    A(1)\n}\nMake(10), Make(20)", "ok S[11, 21]")]
    [InlineData("Make(k) = {\n    Add(x) = x + k\n    A = Add\n    map([1, 2], A)\n}\nMake(10), Make(20)", "ok S[L[11, 12], L[21, 22]]")]
    // A private member reached through the alias's own scope.
    [InlineData("Lib = {\n    Hidden(x) = x * 2\n    public A = Hidden\n}\nLib.A(4)", "ok 8")]
    public async Task TheTarget_IsFixedInTheAliasDeclarationScope(string source, string expected)
        => Assert.Equal(expected, await Outcome(source));

    [Fact]
    public async Task RecursiveActivations_EachResolveTheirOwnAliasTarget()
    {
        // Every activation of Walk declares an alias of its own Step, which captures that activation's
        // n: a memo that ignored activations would hand every level the first level's Step.
        const string source = "Walk(n) = {\n    Step(x) = x + n\n    A = Step\n    if(n == 0, 0, A(Walk(n - 1)))\n}\nWalk(4)";
        Assert.Equal("ok 10", await Outcome(source));
    }

    [Fact]
    public async Task AliasTargetMemo_UsesTheDeclaringActivation_BeneathAShadowingCaller()
    {
        const string source = "Make(k) = {\n    Add(x) = trace(x + k)\n    A = Add\n    B = A\n    Use(k) = map([1, 2], B)\n    Use(100)\n}\nMake(10), Make(20)";
        Assert.Equal("ok S[L[11, 12], L[21, 22]] [trace(11),trace(12),trace(21),trace(22)]", await Outcome(source));
    }

    [Fact]
    public async Task ParsedAliasTree_CanBeReusedAcrossConcurrentAsyncRuns()
    {
        var operations = HostOperations.Create(HostOperation.CreateAsync("touch", async (args, _) =>
        {
            await Task.Yield();
            return args[0];
        }, "x"));
        const string source = "Make(k) = {\n    Add(x) = touch(x + k)\n    A = Add\n    B = A\n    map([1, 2], B)\n}\nMake(10), Make(20)";
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var expected = new Result.SequenceValue([new Result.ListValue([new Result.Atom(11), new Result.Atom(12)]),
            new Result.ListValue([new Result.Atom(21), new Result.Atom(22)])]);
        var runs = Enumerable.Range(0, 16).Select(async _ =>
        {
            var result = await Evaluator.RunAsync(program, hostOperations: operations,
                zeroArgPropertyResultCache: new KatLang.Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache());
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal<Result>(expected, result.Value, Result.ValueComparer);
        });
        await Task.WhenAll(runs);
    }

    [Fact]
    public async Task LoadedModuleRoot_ThatIsAnAlias_KeepsItsCallableAndDocumentBinding()
    {
        const string source = "M = load('https://katlang.org/aliases/root.kat')\nM([1, 2]), map([[1], [1, 2]], M)";
        var options = new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("count") };
        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        Assert.IsType<Algorithm.Alias>(parsed.Root.Properties.Single(property => property.Name == "M").Value);
        var model = SemanticModelBuilder.Build(parsed);
        var use = model.FindResolutionAt(new SourcePosition(2, 1));
        var declaration = use?.ResolvedDeclaration;
        Assert.NotNull(declaration);
        Assert.Equal(new SourcePosition(1, 1), declaration.Span.Start);
        var result = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, options));
        Assert.Equal([2m, 1m, 2m], result.Atoms);
    }

    [Fact]
    public async Task DeferredModuleAliasChain_KeepsPerBindingCaches_AcrossBranchActivations()
    {
        var ticks = 0;
        var downloads = 0;
        var operations = HostOperations.Create(HostOperation.CreateAsync("tick", async (_, _) =>
        {
            await Task.Yield();
            return new Result.Atom(Interlocked.Increment(ref ticks));
        }));
        var options = new RunOptions
        {
            HostOperations = operations,
            DownloadCode = async (_, _) =>
            {
                await Task.Yield();
                Interlocked.Increment(ref downloads);
                return "public Only(*xs) = tick()";
            },
        };
        const string source = "Pick(0) = 0\nPick(n) = {\n    M = load('https://katlang.org/aliases/deferred.kat')\n    A = M.Only\n    B = A\n    (B, M.Only, B)\n}\nPick(0), Pick(1), Pick(2)";
        var result = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, options));
        Assert.Equal([0m, 1m, 2m, 1m, 1m, 2m, 1m], result.Atoms);
        Assert.Equal(2, ticks);
        Assert.Equal(1, downloads);
    }

    // ── 7. Negative controls: no alias without one static target identity ───────────────────

    [Fact]
    public void RuntimeOnlyAmbiguousAndUnresolvedNames_AreNeverAliases()
    {
        // A callable PARAMETER is known only at run time.
        var parameter = SourceProvenance.ParseValid("Apply(f) = {\n    A = f\n    A\n}\nInc(x) = x + 1\nApply(Inc)").Root;
        var apply = Assert.IsType<Algorithm.User>(parameter.Properties.Single(p => p.Name == "Apply").Value);
        Assert.IsNotType<Algorithm.Alias>(apply.Properties.Single(p => p.Name == "A").Value);

        // An ambiguous open selects nothing.
        var ambiguous = SourceProvenance.ParseAllowingDiagnostics(
            "open L1, L2\nL1 = {\n    public F(x) = x\n}\nL2 = {\n    public F(x) = x\n}\nA = F\nA(1)").Root;
        Assert.IsNotType<Algorithm.Alias>(ambiguous.Properties.Single(p => p.Name == "A").Value);

        // An unresolved name is the alias's own implicit parameter, never a target.
        var unresolved = SourceProvenance.ParseValid("A = Q\nA(5)").Root;
        var a = Assert.IsType<Algorithm.User>(unresolved.Properties.Single(p => p.Name == "A").Value);
        Assert.Equal(["Q"], a.Params);

        // A member only a runtime receiver could provide (the lone row `A` then bare-forwards A's own
        // inferred `F`, which the closed list does not bind: an ordinary FWD-02 rejection).
        var runtimeMember = SourceProvenance.ParseAllowingDiagnostics("G(r) = {\n    A = r.F\n    A\n}\nG(5)").Root;
        var g = Assert.IsType<Algorithm.User>(runtimeMember.Properties.Single(p => p.Name == "G").Value);
        Assert.IsNotType<Algorithm.Alias>(g.Properties.Single(p => p.Name == "A").Value);
    }

    // ── 8. Recursion ─────────────────────────────────────────────────────────────────────

    [Theory]
    // Recursion inside the target refers to the target's own declaration.
    [InlineData("Fact(0) = 1\nFact(n) = n * Fact(n - 1)\nF = Fact\nF(5)", "ok 120")]
    // Recursion written through the alias reaches the same target.
    [InlineData("F(n) = if(n == 0, 1, n * A(n - 1))\nA = F\nA(4)", "ok 24")]
    // Mutual recursion through aliases.
    [InlineData("Even(n) = if(n == 0, true, OddA(n - 1))\nOdd(n) = if(n == 0, false, EvenA(n - 1))\nEvenA = Even\nOddA = Odd\nEvenA(10), OddA(7)", "ok S[true, true]")]
    // Family recursion through an alias.
    [InlineData("Sum(0) = 0\nSum(n) = n + S(n - 1)\nS = Sum\nS(4)", "ok 10")]
    // An alias declared inside a recursive body.
    [InlineData("F(n) = {\n    A = G\n    if(n == 0, 0, A(n - 1) + 1)\n}\nG(m) = F(m)\nF(5)", "ok 5")]
    // An alias declared after its use.
    [InlineData("A(3)\nA = F\nF(x) = x * 2", "ok 6")]
    public async Task Recursion_ThroughAndInsideAliases(string source, string expected)
        => Assert.Equal(expected, await Outcome(source));

    // ── 9. Resource accounting: an alias is no invocation ───────────────────────────────────

    [Fact]
    public void ThirtyAliases_ChargeExactlyTheDirectTargetCalls()
    {
        var chain = string.Concat(Enumerable.Range(1, 30).Select(i => $"A{i} = A{i - 1}\n"));
        var aliased = "F(x) = x * 2\nA0 = F\n" + chain + "A30(1), A30(2)";
        const string direct = "F(x) = x * 2\nF(1), F(2)";
        foreach (var optimized in new[] { false, true })
        {
            var (aliasResult, aliasBudget) = Evaluator.RunCountedObserved(
                new Expr.AlgorithmExpr(SourceProvenance.ParseValid(aliased).Root), enableOptimizations: optimized);
            var (directResult, directBudget) = Evaluator.RunCountedObserved(
                new Expr.AlgorithmExpr(SourceProvenance.ParseValid(direct).Root), enableOptimizations: optimized);
            Assert.False(aliasResult.IsError);
            Assert.False(directResult.IsError);
            Assert.Equal(directBudget.ConsumedSteps, aliasBudget.ConsumedSteps);
            Assert.Equal(directBudget.PeakDepth, aliasBudget.PeakDepth);
        }
    }

    [Theory]
    [InlineData(2)]
    [InlineData(10)]
    [InlineData(100)]
    public void DottedAliasChain_FirstNormalization_RemembersEveryBinding(int length)
    {
        var libraries = string.Concat(Enumerable.Range(0, length).Select(index =>
            $"Lib{index} = {{\n    public A = {(index == 0 ? "F" : $"Lib{index - 1}.A")}\n}}\n"));
        var source = "F(x) = x + 1\n" + libraries + $"Alias = Lib{length - 1}.A\nAlias(1), Alias(2)";
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal(length + 1, budget.AliasTargets.Count);
    }

    // ── 10. Diagnostics: the target's semantics, the written call's frame ──────────────────

    [Theory]
    // One frame, naming the written alias — never a synthetic `call to F` beneath it.
    [InlineData("F(x, y) = x / y\nA = F\nA(1, 0)", "err DivisionByZero: while evaluating call to A: Division by zero")]
    [InlineData("F(x, y) = x / y\nA = F\nB = A\nB(1, 0)", "err DivisionByZero: while evaluating call to B: Division by zero")]
    // The target's arity category, against the target's own signature.
    // (A user target's signature is shown under the WRITTEN callee name, with the target's parameters.)
    [InlineData("F(x, y) = x - y\nA = F\nA(1)", "err ArityMismatch: Callable `A(x, y)` expects 2 arguments, but was called with 1 argument.")]
    [InlineData("C = count\nC()", "err ArityMismatch: Callable `count(collection)` expects 1 argument, but was called with 0 arguments.")]
    // An argument failure is the argument's.
    [InlineData("Bad = trace(0) / 0\nF(x) = x\nA = F\nA(Bad)", "err DivisionByZero: while evaluating call to A: Division by zero [trace(0)]")]
    public async Task Diagnostics_KeepTheTargetsKind_UnderTheWrittenFrame(string source, string expected)
        => Assert.Equal(expected, await Outcome(source));

    [Fact]
    public void TheAliasCallSpan_IsTheWrittenCall()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("F(x, y) = x / y\nA = F\nA(1, 0)"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.DivisionByZero, error.Code);
        Assert.Equal(1, Assert.NotNull(error.Span).Start.Line);
    }

    // ── 11. The editor model ────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("F(x) = x\nA = F", "A", "A(x)", "F", "F(x)")]
    [InlineData("C = count", "C", "C(collection)", "count", "count(collection)")]
    [InlineData("I = if", "I", "I(condition, whenTrue, whenFalse)", "if", "if(condition, whenTrue, whenFalse)")]
    [InlineData("R = repeat", "R", "R(step, count, *init)", "repeat", "repeat(step, count, *init)")]
    // A family displays its first clause's positions (`Fact(0)` names none: `value`), alias and target alike.
    [InlineData("Fact(0) = 1\nFact(n) = n * Fact(n - 1)\nF = Fact", "F", "F(value)", "Fact", "Fact(value)")]
    [InlineData("U(1) = 1\nU(-1) = -1\nUA = U", "UA", "UA(value)", "U", "U (clause family without nameable positions)")]
    [InlineData("Single([x]) = x\nA = Single\nB = A", "B", "B([x])", "Single", "Single([x])")]
    public void Editor_ShowsTheAliasUnderItsOwnName_AndNamesItsTarget(
        string source, string alias, string signature, string targetName, string targetSignature)
    {
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source + "\n0").Parsed);
        var property = Assert.Single(model.FindProperties(alias));
        Assert.Equal(signature, property.DisplaySignature);
        Assert.NotNull(property.AliasTarget);
        Assert.Equal(targetName, property.AliasTarget.QualifiedName);
        Assert.Equal(targetSignature, property.AliasTarget.DisplaySignature);
        // The alias symbol is its own declaration.
        Assert.NotNull(property.Declaration);
    }

    [Fact]
    public void Editor_AliasRowResolvesToTheTarget_AndAUseResolvesToTheAlias()
    {
        const string source = "F(x) = x * 2\nA = F\nA(3)";
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        // `F` in the alias row: go-to-definition reaches F.
        var row = model.FindResolutionAt(new SourcePosition(2, 5));
        Assert.NotNull(row?.ResolvedDeclaration);
        Assert.Equal(new SourcePosition(1, 1), row.ResolvedDeclaration.Span.Start);
        // `A` at the use site: the alias's own declaration.
        var use = model.FindResolutionAt(new SourcePosition(3, 1));
        Assert.NotNull(use?.ResolvedDeclaration);
        Assert.Equal(new SourcePosition(2, 1), use.ResolvedDeclaration.Span.Start);
    }

    // ── 12. Long chains: no host recursion, no re-chase per call ───────────────────────────

    private static T OnOneMebibyteStack<T>(Func<T> work)
    {
        T result = default!;
        Exception? failure = null;
        var thread = new Thread(() =>
        {
            try { result = work(); }
            catch (Exception exception) { failure = exception; }
        }, maxStackSize: 1024 * 1024);
        thread.Start();
        thread.Join();
        if (failure is not null)
            throw new InvalidOperationException("The work failed on the 1 MiB thread.", failure);
        return result;
    }

    private static string Chain(int length, string head, string target)
        => $"{head}0 = {target}\n" + string.Concat(Enumerable.Range(1, length - 1).Select(i => $"{head}{i} = {head}{i - 1}\n"));

    /// <summary>
    /// (length, target declarations, target, the call through the last link, its value) — a user callable,
    /// a builtin, `if`, a nameable and an unnameable family. Each chain is its own program: the evaluator's
    /// name lookup scans a level's properties, so one program holding several 10,000-link chains would
    /// measure that (pre-existing, alias-independent) scan rather than the chase.
    /// </summary>
    public static TheoryData<int, string, string, string, decimal> ChainCases()
    {
        var data = new TheoryData<int, string, string, string, decimal>();
        foreach (var length in new[] { 2, 10, 100, 1_000, 10_000 })
        {
            data.Add(length, "Inc(x) = x + 1\n", "Inc", "(1)", 2m);
            data.Add(length, "", "count", "([1, 2])", 2m);
            data.Add(length, "", "if", "(false, 1, 2)", 2m);
            data.Add(length, "", "abs", "(-5)", 5m);
            data.Add(length, "", "hostInc", "(1)", 2m);
            data.Add(length, "Fact(0) = 1\nFact(n) = n * Fact(n - 1)\n", "Fact", "(4)", 24m);
            data.Add(length, "U(1) = 1\nU(-1) = -1\n", "U", "(-1)", -1m);
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(ChainCases))]
    public void AliasChains_NormalizeOnAOneMebibyteStack(int length, string declarations, string target, string call, decimal expected)
    {
        // The first call chases the chain once (iteratively — a 1 MiB thread survives any length) and
        // remembers every link; a thousand further calls through the last link, as a callback, reuse it.
        var last = $"A{length - 1}";
        var source = declarations + Chain(length, "A", target) + $"{last}{call}, map(range(1, 1000), {{ v * 0 + {last}{call} }}).count";
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("hostInc",
                static (args, _) => new Result.Atom(Assert.IsType<Result.Atom>(args[0]).Value + 1), "x")),
        };
        var success = Assert.IsType<RunResult.Success>(OnOneMebibyteStack(() => KatLangEngine.Run(source, options)));
        Assert.Equal([expected, 1000m], success.Atoms);
    }

    [Theory]
    [InlineData("abs", "-5", "ok S[5, 5]")]
    [InlineData("trace", "5", "ok S[5, 5] [trace(5),trace(5)]")]
    public async Task LongMathAndHostAliasChains_AgreeOnEveryRoute(string target, string supply, string expected)
    {
        var source = Chain(1_000, "A", target) + $"A999({supply}), A500({supply})";
        Assert.Equal(expected, await Outcome(source));
    }

    [Fact]
    public async Task LongAliasChain_IsEquivalentOnTheAsyncRoutesToo()
    {
        var source = "Inc(x) = x + 1\n" + Chain(1_000, "A", "Inc") + "map(range(1, 20), A999).sum, A999(1)";
        Assert.Equal("ok S[230, 2]", await Outcome(source));
    }

    /// <summary>
    /// A host-built 2,000-hop chain (no front end): the evaluator normalizes it iteratively, once per
    /// binding scope, and the pre-evaluation gate rejects a host-built CYCLE structurally.
    /// </summary>
    [Fact]
    public void HostBuiltChains_NormalizeAndHostBuiltCycles_AreRejectedStructurally()
    {
        const int Hops = 2_000;
        static Algorithm.User Root(IEnumerable<Property> aliases, Expr output)
            => new(
                null,
                [],
                [],
                [new Property("F", new Algorithm.User(null, Algorithm.NormalParameters(["x"]), [], [], [new Expr.Binary(BinaryOp.Mul, new Expr.Param("x"), new Expr.Num(3))])),
                    .. aliases],
                [output]);

        var chain = Enumerable.Range(0, Hops).Select(i => new Property(
            $"A{i}", new Algorithm.Alias(null, [], [], new Expr.Resolve(i == 0 ? "F" : $"A{i - 1}"))));
        var call = new Expr.Call(new Expr.Resolve($"A{Hops - 1}"), [new Expr.Num(5)]);
        var normalized = OnOneMebibyteStack(() => Evaluator.Run(new Expr.AlgorithmExpr(Root(chain, call))));
        Assert.False(normalized.IsError, normalized.IsError ? normalized.Error.ToString() : null);

        // A cycle closed at the far end of the same chain.
        var cyclic = Enumerable.Range(0, Hops).Select(i => new Property(
            $"A{i}", new Algorithm.Alias(null, [], [], new Expr.Resolve(i == 0 ? $"A{Hops - 1}" : $"A{i - 1}"))));
        var rejected = OnOneMebibyteStack(() => Evaluator.Run(new Expr.AlgorithmExpr(Root(cyclic, call))));
        Assert.True(rejected.IsError);
        var illegal = Assert.IsType<EvalError.IllegalInEval>(rejected.Error);
        Assert.Equal(Evaluator.AliasCycleMessage, illegal.Reason);

        // A target that is no static path is rejected the same way.
        var notStatic = Evaluator.Run(new Expr.AlgorithmExpr(Root(
            [new Property("A", new Algorithm.Alias(null, [], [], new Expr.Num(1)))],
            new Expr.Call(new Expr.Resolve("A"), []))));
        Assert.IsType<EvalError.IllegalInEval>(notStatic.Error);
    }

    [Fact]
    public void HostBuiltCycleThroughAnOpen_IsCaughtByTheRuntimeChase()
    {
        // The static gate follows names and declared members only; a cycle closed through an `open`
        // is caught when the chase revisits an alias in the same resolving scope — never a hang.
        var lib = new Algorithm.User(null, [], [], [new Property("X", new Algorithm.Alias(null, [], [], new Expr.Resolve("A")), IsPublic: true)], []);
        var root = new Algorithm.User(
            null,
            [],
            [new Expr.Resolve("Lib")],
            [new Property("Lib", lib), new Property("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("X")))],
            [new Expr.Call(new Expr.Resolve("A"), [new Expr.Num(1)])]);
        var result = OnOneMebibyteStack(() => Evaluator.Run(new Expr.AlgorithmExpr(root)));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext withContext)
            error = withContext.Inner;
        Assert.Equal(Evaluator.AliasCycleMessage, Assert.IsType<EvalError.IllegalInEval>(error).Reason);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task SharedHostAlias_CycleValidationDependsOnItsScope_NotVisitOrder(bool cyclicFirst)
    {
        var span = new SourceSpan(7, 3, 7, 4);
        var shared = new Algorithm.Alias(null, [], [], new Expr.Resolve("F") { Span = span });
        var terminal = new Algorithm.User(null, Algorithm.NormalParameters(["x"]), [], [], [new Expr.Param("x")]);
        var safe = new Algorithm.User(null, [], [], [new Property("A", shared), new Property("F", terminal)], []);
        var cyclic = new Algorithm.User(null, [], [],
            [new Property("A", shared), new Property("F", new Algorithm.Alias(null, [], [], new Expr.Resolve("A") { Span = span }))], []);
        Property[] owners = cyclicFirst
            ? [new Property("Cyclic", cyclic), new Property("Safe", safe)]
            : [new Property("Safe", safe), new Property("Cyclic", cyclic)];
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], owners, [new Expr.Num(99)]));

        var sync = Evaluator.Run(program);
        Assert.True(sync.IsError);
        var rejection = Assert.IsType<EvalError.IllegalInEval>(sync.Error);
        Assert.Equal(Evaluator.AliasCycleMessage, rejection.Reason);
        Assert.Equal(span, rejection.Span);

        var asyncResult = await Evaluator.RunAsync(program, zeroArgPropertyResultCache: new KatLang.Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache());
        Assert.True(asyncResult.IsError);
        Assert.Equal(rejection, asyncResult.Error);
    }

    [Fact]
    public async Task SharedHostAlias_RevisitedInADifferentScope_IsNotACycle()
    {
        var shared = new Algorithm.Alias(null, [], [], new Expr.Resolve("F"));
        var terminal = new Algorithm.User(null, Algorithm.NormalParameters(["x"]), [], [], [new Expr.Param("x")]);
        var lib = new Algorithm.User(null, [], [], [new Property("A", shared), new Property("F", terminal)], []);
        var indirect = new Algorithm.Alias(null, [], [], new Expr.DotCall(new Expr.Resolve("Lib"), "A", null));
        var root = new Algorithm.User(null, [], [],
            [new Property("A", shared), new Property("F", indirect), new Property("Lib", lib)],
            [new Expr.Call(new Expr.Resolve("A"), [new Expr.Num(5)])]);
        var program = new Expr.AlgorithmExpr(root);

        var sync = Evaluator.Run(program);
        Assert.False(sync.IsError, sync.IsError ? sync.Error.ToString() : null);
        Assert.Equal(new Result.Atom(5), sync.Value);
        var asyncResult = await Evaluator.RunAsync(program, zeroArgPropertyResultCache: new KatLang.Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache());
        Assert.False(asyncResult.IsError, asyncResult.IsError ? asyncResult.Error.ToString() : null);
        Assert.Equal(sync.Value, asyncResult.Value);
    }

    [Fact]
    public void SharedHostAlias_InsideSharedContainers_IsValidatedInEachScope()
    {
        var terminal = new Algorithm.User(null, Algorithm.NormalParameters(["x"]), [], [], [new Expr.Param("x")]);
        var left = new Algorithm.User(null, [], [],
            [new Property("A", new Algorithm.Alias(null, [], [], new Expr.DotCall(new Expr.Resolve("F"), "B", null)))], []);
        var right = new Algorithm.User(null, [], [],
            [new Property("B", new Algorithm.Alias(null, [], [], new Expr.DotCall(new Expr.Resolve("Left"), "A", null)))], []);
        var safeTarget = new Algorithm.User(null, [], [], [new Property("B", terminal)], []);
        var safe = new Algorithm.User(null, [], [],
            [new Property("Left", left), new Property("Right", right), new Property("F", safeTarget)], []);
        var cyclic = new Algorithm.User(null, [], [],
            [new Property("Left", left), new Property("Right", right), new Property("F", right)], []);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [new Property("Safe", safe), new Property("Cyclic", cyclic)], [new Expr.Num(99)]));

        var result = Evaluator.Run(program);
        Assert.True(result.IsError);
        Assert.Equal(Evaluator.AliasCycleMessage, Assert.IsType<EvalError.IllegalInEval>(result.Error).Reason);
    }

    [Theory]
    [InlineData(9)]
    [InlineData(18)]
    [InlineData(30)]
    public void SharedHostAlias_UnrelatedScopeDeclarations_DoNotMultiplyValidationPaths(int depth)
    {
        Algorithm shared = new Algorithm.Alias(null, [], [], new Expr.Resolve("F"));
        for (var level = 0; level < depth; level++)
        {
            var block = new Expr.AlgorithmExpr(shared);
            var left = new Algorithm.User(null, [], [], [new Property("LeftMarker", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))], [block]);
            var right = new Algorithm.User(null, [], [], [new Property("RightMarker", new Algorithm.User(null, [], [], [], [new Expr.Num(2)]))], [block]);
            shared = new Algorithm.User(null, [], [], [new Property("Left", left), new Property("Right", right)], []);
        }

        var terminal = new Algorithm.User(null, Algorithm.NormalParameters(["x"]), [], [], [new Expr.Param("x")]);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [new Property("F", terminal), new Property("Diamond", shared)], [new Expr.Num(99)]));
        var observations = new FrontEndTraversalObservations();
        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(program, observations));
        Assert.InRange(observations.WalkerAlgorithmExpansions, 1, 12 * depth);
    }
}
