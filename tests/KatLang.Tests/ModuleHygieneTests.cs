using static KatLang.Tests.ModuleRouteAgreement;

namespace KatLang.Tests;

/// <summary>
/// Q-31 H-P (decided 2026-10-06): a loaded module is a hygienic source unit rooted at the prelude.
/// Its free names resolve in its own declarations, then the prelude (builtins, <c>Math</c> and its
/// aliases, the run's host operations) — never at the load site: the site's properties, opened names,
/// prelude shadows and parameters never reach it, whichever spelling holds it (<c>open 'u'</c>,
/// <c>M = load('u')</c>, <c>open M</c>, <c>open load('u')</c>, a load in a nested body, in a
/// parameterized owner, or in a deferred branch). A name the module cannot resolve is an implicit
/// parameter of the module member that uses it (PAR-03, MOD-06); a site parameter reaches a member only
/// through the ordinary call laws written at the site — an explicit argument, bare forwarding (FWD-02)
/// or formula lifting (PAR-07). So <c>open 'u'</c> ≡ <c>M = load('u'); open M</c> ≡ <c>M.Member</c>.
/// Every observation is pinned on every module route (<see cref="ModuleRouteAgreement"/>).
/// </summary>
public class ModuleHygieneTests
{
    private const string Sum = "https://mods.test/sum.kat";
    private const string Abs = "https://mods.test/abs.kat";
    private const string MathMember = "https://mods.test/math.kat";
    private const string Trace = "https://mods.test/trace.kat";
    private const string FreeBase = "https://mods.test/base.kat";
    private const string FreeParameter = "https://mods.test/param.kat";
    private const string Chain = "https://mods.test/chain.kat";
    private const string OwnShadow = "https://mods.test/shadow.kat";
    private const string MemberA = "https://mods.test/pa.kat";
    private const string OutputRow = "https://mods.test/row.kat";
    private const string Opened = "https://mods.test/opened.kat";

    private static Modules Server() => new(
        (Sum, "public V = sum((1, 2))"),
        (Abs, "public V = abs(-3)"),
        (MathMember, "public V = Math.Abs(-3)"),
        (Trace, "public V = trace(7)"),
        (FreeBase, "public V = Base + 1"),
        (FreeParameter, "public V = n + 1"),
        (Chain, $"S = load('{Sum}')\npublic V = S.V * 10"),
        (OwnShadow, "sum(xs) = 777\npublic V = sum((1, 2))"),
        (MemberA, "public a = 3"),
        (OutputRow, "x + 1"),
        (Opened, "public V = Q + 1"));

    /// <summary>The loading shapes of one module whose member <c>V</c> the program reads, after the site's <paramref name="siteDeclarations"/>.</summary>
    private static IEnumerable<(string Shape, string Source)> Shapes(string url, string siteDeclarations)
    {
        yield return ("open-string", $"open '{url}'\n{siteDeclarations}\nV");
        yield return ("property-load", $"{siteDeclarations}\nM = load('{url}')\nM.V");
        yield return ("open-property", $"open M\n{siteDeclarations}\nM = load('{url}')\nV");
        yield return ("open-load", $"open load('{url}')\n{siteDeclarations}\nV");
        yield return ("nested-body", $"{siteDeclarations}\nA = {{\n    M = load('{url}')\n    M.V\n}}\nA");
        yield return ("parameterized-owner", $"{siteDeclarations}\nG(k) = {{\n    M = load('{url}')\n    M.V + k * 0\n}}\nG(1)");
    }

    private static async Task AssertEveryShape(string url, string siteDeclarations, string expected, params string[] hostCalls)
    {
        foreach (var (shape, source) in Shapes(url, siteDeclarations))
        {
            var observed = await OnEveryRouteAsync(source, Server);
            Assert.True(observed.Kind == "ok" && observed.Value == expected, $"{shape}: expected ok {expected}, got {observed}\n{source}");
            Assert.Equal(hostCalls, observed.HostCalls);
        }
    }

    [Fact]
    public Task BuiltinShadowAtTheSite_NeverReachesTheModule()
        => AssertEveryShape(Sum, "sum(xs) = 999", "3");

    [Fact]
    public async Task MathAliasAndMemberShadowsAtTheSite_NeverReachTheModule()
    {
        await AssertEveryShape(Abs, "abs(x) = 100", "3");
        await AssertEveryShape(MathMember, "Math = { public Abs(x) = 100 }", "3");
    }

    [Fact]
    public Task HostOperationShadowAtTheSite_NeverReachesTheModule()
        => AssertEveryShape(Trace, "trace(x) = 99", "7", "trace(7)");

    [Fact]
    public Task ModuleOwnDeclarations_StillBeatThePrelude()
        => AssertEveryShape(OwnShadow, "sum(xs) = 999", "777");

    [Fact]
    public Task NestedModule_IsHygienicToo()
        => AssertEveryShape(Chain, "sum(xs) = 999", "30");

    [Fact]
    public async Task SiteProperty_IsNeverSeen_SoTheFreeNameIsTheMembersParameter()
    {
        // `Base` in the module is V's own implicit parameter whatever the site declares, so the
        // same module has one signature everywhere and a bare root read is its arity error.
        foreach (var site in new[] { "Base = 10", "Unrelated = 10" })
        {
            var parsed = await Parser.ParseAsync($"{site}\nM = load('{FreeBase}')\nM.V(10)", Server().Options());
            Assert.Empty(parsed.Diagnostics);
            var module = Assert.Single(parsed.Root.Properties, p => p.Name == "M").Value;
            Assert.Equal(["Base"], Assert.Single(module.Properties, p => p.Name == "V").Value.Params);

            var called = await OnEveryRouteAsync($"{site}\nM = load('{FreeBase}')\nM.V(10)", Server);
            Assert.Equal("ok 11", $"{called.Kind} {called.Value}");
            var bare = await OnEveryRouteAsync($"{site}\nM = load('{FreeBase}')\nM.V", Server);
            Assert.Equal("err", bare.Kind);
            Assert.StartsWith("ArityMismatch", Assert.Single(bare.Errors), StringComparison.Ordinal);
        }
    }

    [Fact]
    public async Task OpenedNamesAtTheSite_AreNeverSeen()
    {
        // The site opens a library providing Q; the module's Q is still its member's own parameter.
        var observed = await OnEveryRouteAsync($"open Lib\nLib = {{ public Q = 10 }}\nM = load('{Opened}')\nM.V(1)", Server);
        Assert.Equal("ok 2", $"{observed.Kind} {observed.Value}");
    }

    [Fact]
    public async Task SiteParameter_ReachesAMember_OnlyThroughTheOrdinaryCallLaws()
    {
        // V is V(n): the site's `n` reaches it by bare forwarding (FWD-02), by formula lifting by
        // name (PAR-07), or as an explicit argument — never by the module reading the site.
        var bare = await OnEveryRouteAsync($"G(n) = {{\n    M = load('{FreeParameter}')\n    M.V\n}}\nG(5)", Server);
        Assert.Equal("ok 6", $"{bare.Kind} {bare.Value}");
        var formula = await OnEveryRouteAsync($"G(n) = {{\n    M = load('{FreeParameter}')\n    M.V + n\n}}\nG(5)", Server);
        Assert.Equal("ok 11", $"{formula.Kind} {formula.Value}");
        var explicitArgument = await OnEveryRouteAsync($"G(n) = {{\n    M = load('{FreeParameter}')\n    M.V(100)\n}}\nG(5)", Server);
        Assert.Equal("ok 101", $"{explicitArgument.Kind} {explicitArgument.Value}");

        var parsed = await Parser.ParseAsync($"G(n) = {{\n    M = load('{FreeParameter}')\n    M.V(100)\n}}\nG(5)", Server().Options());
        var g = Assert.Single(parsed.Root.Properties, p => p.Name == "G").Value;
        var module = Assert.Single(g.Properties, p => p.Name == "M");
        Assert.Equal(PropertyExposure.Exported, module.Exposure);
        Assert.Equal(["n"], Assert.Single(module.Value.Properties, p => p.Name == "V").Value.Params);
    }

    [Fact]
    public async Task HolderParameter_NeverCollidesWithAModuleDeclaration()
    {
        // The module meets none of its holder's parameters: `a` inside it is its own member.
        var observed = await OnEveryRouteAsync($"F(a) = {{\n    M = load('{MemberA}')\n    M.a + a\n}}\nF(1)", Server);
        Assert.Equal("ok 4", $"{observed.Kind} {observed.Value}");
    }

    [Fact]
    public async Task ModuleOutputFreeName_MakesTheModuleItselfParameterized()
    {
        var called = await OnEveryRouteAsync($"x = 100\nM = load('{OutputRow}')\nM(4)", Server);
        Assert.Equal("ok 5", $"{called.Kind} {called.Value}");

        // An algorithm that needs a call is no open provider (MOD-04), whichever spelling opens it.
        foreach (var source in new[] { $"open '{OutputRow}'\n1", $"open M\nM = load('{OutputRow}')\n1" })
        {
            var refused = await OnEveryRouteAsync(source, Server);
            Assert.Equal("parse", refused.Kind);
            Assert.StartsWith("IllegalInOpen", Assert.Single(refused.Errors), StringComparison.Ordinal);
        }
    }

    [Fact]
    public async Task OpenString_LoadThenOpen_AndDottedRead_MeanOneThing()
    {
        // PV-42: the three spellings of one module agree, the site shadow notwithstanding.
        string[] spellings =
        [
            $"open '{Sum}'\nsum(xs) = 999\nV",
            $"open M\nsum(xs) = 999\nM = load('{Sum}')\nV",
            $"sum(xs) = 999\nM = load('{Sum}')\nM.V",
        ];
        foreach (var source in spellings)
        {
            var observed = await OnEveryRouteAsync(source, Server);
            Assert.Equal("ok 3", $"{observed.Kind} {observed.Value}");
        }
    }

    [Fact]
    public async Task DeferredBranchLoads_AreHygienicToo()
    {
        var property = await OnEveryRouteAsync(
            $"sum(xs) = 999\nF(0) = 0\nF(k) = {{\n    M = load('{Sum}')\n    M.V + k * 0\n}}\nF(0), F(1)",
            Server, AsyncRoutes);
        Assert.Equal("ok S[0, 3]", $"{property.Kind} {property.Value}");
        var open = await OnEveryRouteAsync(
            $"sum(xs) = 999\nF(0) = 0\nF(k) = {{\n    open '{Sum}'\n    V + k * 0\n}}\nF(0), F(1)",
            Server, AsyncRoutes);
        Assert.Equal("ok S[0, 3]", $"{open.Kind} {open.Value}");
    }

    [Fact]
    public async Task ModuleMeansThePreludeRootedInlineOpenOracle()
    {
        // The module's text written as an inline open target — the prelude-rooted oracle (MOD-06) —
        // means what the loaded module means, at a site that shadows everything it reads.
        const string site = "sum(xs) = 999\nabs(x) = 100\nBase = 10";
        const string text = "public V = sum((1, 2)) + abs(-3) + Base";
        var oracle = await OnEveryRouteAsync($"open {{ {text} }}\n{site}\nV(4)", Server);
        Assert.Equal("ok 10", $"{oracle.Kind} {oracle.Value}");
        var server = () => new Modules(("https://mods.test/all.kat", text));
        foreach (var source in new[]
        {
            $"open 'https://mods.test/all.kat'\n{site}\nV(4)",
            $"{site}\nM = load('https://mods.test/all.kat')\nM.V(4)",
            $"open M\n{site}\nM = load('https://mods.test/all.kat')\nV(4)",
        })
        {
            Assert.True(oracle.AgreesWith(await OnEveryRouteAsync(source, server)), source);
        }
    }

    [Fact]
    public async Task AModuleThatIsACallableAlias_ResolvesItsTargetInTheModule()
    {
        // A module whose one row names a builtin is a callable ALIAS of it (FWD-02). Wherever it is
        // held, the alias resolves its target in the module — at the prelude — never in the scope that
        // holds it, so the site's `abs(x) = 100` is not the module's `abs` (H-P at run time too).
        const string url = "https://mods.test/alias.kat";
        var server = () => new Modules((url, "abs"));
        foreach (var source in new[]
        {
            $"abs(x) = 100\nM = load('{url}')\nM(-3)",
            $"abs(x) = 100\nG(k) = {{\n    M = load('{url}')\n    M(-3) + k * 0\n}}\nG(1)",
        })
        {
            var observed = await OnEveryRouteAsync(source, server);
            Assert.True(observed.Kind == "ok" && observed.Value == "3", $"{observed}\n{source}");
        }
    }

    [Fact]
    public async Task AHoldersParameterDependentShadow_NeverReachesTheHolder()
    {
        // The site's `sum` depends on G's `n`, but the module's `sum` — in a member and in the
        // module's own output row — is the prelude's: nothing the module reads escapes it to its
        // holder, so `M` and `N` stay exported and are readable from outside any activation of G
        // (formerly the module captured the shadow and its holder was local-only).
        const string outputSum = "https://mods.test/osum.kat";
        var server = () => new Modules((Sum, "public V = sum((1, 2))"), (outputSum, "sum((1, 2))"));
        var source = $"G(n) = {{\n    sum(xs) = n\n    public M = load('{Sum}')\n    public N = load('{outputSum}')\n    M.V + N\n}}\nG.M.V, G.N, G(5)";
        var observed = await OnEveryRouteAsync(source, server);
        Assert.Equal("ok S[3, 3, 6]", $"{observed.Kind} {observed.Value}");

        var parsed = await Parser.ParseAsync(source, server().Options());
        Assert.Empty(parsed.Diagnostics);
        var g = Assert.Single(parsed.Root.Properties, p => p.Name == "G").Value;
        Assert.Equal(PropertyExposure.Exported, Assert.Single(g.Properties, p => p.Name == "M").Exposure);
        Assert.Equal(PropertyExposure.Exported, Assert.Single(g.Properties, p => p.Name == "N").Exposure);
    }

    [Fact]
    public async Task WhatAModuleReads_NeverOrdersItsHoldersSiblings()
    {
        // The module reads `pi` as a value (the prelude's) and its `V` gains `Base` by lifting `W`.
        // The site declares its own `pi`, which lifts `M.V`: it must see V's completed signature, so
        // `M` is resolved first. A module's reads are no sibling-order edges of its holder's level —
        // were they, `M` and the site's `pi` would form a cycle and `pi` would lift nothing.
        const string url = "https://mods.test/order.kat";
        var server = () => new Modules((url, "W = Base + 1\npublic V = W + if(pi > 0, 0, 1)"));
        var observed = await OnEveryRouteAsync($"pi = M.V + 0\nM = load('{url}')\npi(5)", server);
        Assert.Equal("ok 6", $"{observed.Kind} {observed.Value}");
    }

    [Fact]
    public void PreEvaluationAliasChase_RestartsAtALoadedModule()
    {
        // A host-built holder alias `Helper` of `M.F`, where the module's own `F` aliases `Helper`:
        // inside a loaded module `Helper` is not the holder's, so the chase is no cycle — the same
        // text as an ordinary nested body is one (Lean: `staticAliasStep?`, CoreTests/ModuleUnits).
        static Expr Program(bool loaded) => new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [],
            [
                new Property("Helper", new Algorithm.Alias(null, [], [], new Expr.DotCall(new Expr.Resolve("M"), "F", null))),
                new Property("M", new Algorithm.User(
                    null, [], [],
                    [new Property("F", new Algorithm.Alias(null, [], [], new Expr.Resolve("Helper")), IsPublic: true)],
                    []) { IsModuleElaborated = loaded }),
            ],
            [new Expr.Num(1)]));

        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(Program(loaded: true), observations: null));
        Assert.IsType<PreEvaluationAstViolation.AliasCycle>(
            AlgorithmValidation.FindFirstPreEvaluationViolation(Program(loaded: false), observations: null));
    }

    [Fact]
    public async Task EditorModelsTheModuleAsElaborated_WithItsOwnSignature()
    {
        // The editor reads the elaborated tree: the document's `M.V` resolves to the module's
        // locationless member, whose signature is the module's own (V(Base)), not the site's.
        const string source = "Base = 10\nM = load('" + FreeBase + "')\nM.V(1)";
        var parsed = await Parser.ParseAsync(source, Server().Options());
        Assert.Empty(parsed.Diagnostics);
        var model = KatLang.Semantics.SemanticModelBuilder.Build(parsed);
        var resolution = model.FindResolutionAt(new SourcePosition(3, 3));
        Assert.NotNull(resolution);
        Assert.Equal("V", resolution.Occurrence.Name);
        Assert.Null(resolution.ResolvedDeclaration);
        Assert.Equal(["Base"], resolution.ResolvedProperty!.Parameters.Select(static p => p.Name));
    }
}
