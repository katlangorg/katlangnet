using static KatLang.Tests.ModuleRouteAgreement;

namespace KatLang.Tests;

/// <summary>
/// Q-32 I-U (decided 2026-10-06, with Q-31 H-P): one compiled program has ONE module declaration per
/// canonical URL — one elaborated module, one member binding, one callable identity — however many
/// directives, holders, owners, branches and spellings reach it (<c>M = load('u')</c>, <c>open 'u'</c>,
/// <c>open load('u')</c>, a load in a nested body or a selected deferred branch). Holders stay separate
/// bindings of their own (a holder's read of the module's OUTPUT is cached under the holder, FWD-02),
/// distinct canonical URLs are distinct declarations even when they serve identical bytes, and an
/// explicit call is fresh as ever. Source admission (Q-71) is unchanged: one fetch per canonical URL
/// per operation. Seeded draws (<c>randomInt</c>) and logged host calls (<c>tick()</c>) make binding
/// identity observable; every observation is pinned on every module route.
/// </summary>
public class ModuleIdentityTests
{
    private const string Random = "https://mods.test/r.kat";
    private const string RandomTwin = "https://mods.test/r2.kat";
    private const string Tick = "https://mods.test/t.kat";
    private const string Five = "https://mods.test/x.kat";
    private const string FiveTwin = "https://mods.test/x2.kat";
    private const string OutputDraw = "https://mods.test/out.kat";
    private const string Nest = "https://mods.test/nest.kat";
    private const string NestOpen = "https://mods.test/nest-open.kat";
    private const string NestFive = "https://mods.test/nest-five.kat";
    private const string FiveAlias = "https://MODS.test:443/./x.kat#alias";
    private const string RandomText = "public R = randomInt(0, 1000000)";

    private static Modules Server() => new(
        (Random, RandomText),
        (RandomTwin, RandomText),
        (Tick, "public T = tick()"),
        (Five, "public X = 5"),
        (FiveTwin, "public X = 5"),
        (OutputDraw, "public R = randomInt(0, 1000000)\nrandomInt(0, 1000000)"),
        (Nest, $"S = load('{Random}')\npublic R2 = S.R"),
        (NestOpen, $"open '{Random}'\npublic R2 = R"),
        (NestFive, $"public S = load('{Five}')"));

    private static async Task<string[]> Draws(string source, Route[]? routes = null)
    {
        var observed = await OnEveryRouteAsync(source, Server, routes);
        Assert.True(observed.Kind == "ok", observed.ToString());
        var value = observed.Value!;
        return value.StartsWith("S[", StringComparison.Ordinal)
            ? value[2..^1].Split(", ")
            : [value];
    }

    private static void AllEqual(string[] draws) => Assert.Single(draws.Distinct());

    [Fact]
    public async Task TwoLoadsOfOneUrl_AreOneMemberBinding()
    {
        var draws = await Draws($"A = load('{Random}')\nB = load('{Random}')\nA.R, B.R, A.R, B.R");
        AllEqual(draws);

        // An explicit call is fresh: it neither reads nor populates the binding's entry.
        var called = await Draws($"A = load('{Random}')\nB = load('{Random}')\nA.R, B.R(), B.R");
        Assert.Equal(called[0], called[2]);
        Assert.NotEqual(called[0], called[1]);
    }

    [Theory]
    [InlineData("nested-owners", "A = { M = load('$U')\nM.R }\nB = { N = load('$U')\nN.R }\nA, B")]
    [InlineData("parent-and-child", "A = { M = load('$U')\nC = { N = load('$U')\nN.R }\nM.R, C }\nA")]
    [InlineData("siblings-with-different-bodies", "A = { M = load('$U')\nM.R }\nB = { K = 1\nN = load('$U')\nN.R + K * 0 }\nA, B")]
    [InlineData("open-string-and-holder", "open '$U'\nA = load('$U')\nR, A.R")]
    [InlineData("two-open-regions-and-holder", "A = load('$U')\nX = { open '$U'\nR }\nY = { open '$U'\nR }\nA.R, X, Y")]
    [InlineData("open-load-and-holder", "open load('$U')\nA = load('$U')\nR, A.R")]
    [InlineData("parameterized-owners", "F(k) = { M = load('$U')\nM.R + k * 0 }\nF(1), F(2), F(1)")]
    [InlineData("recursive-owner", "F(k) = { M = load('$U')\nif(k == 0, M.R, F(k - 1)) }\nF(0), F(3)")]
    public async Task EveryReachOfOneUrl_IsOneMemberBinding(string topology, string template)
    {
        _ = topology;
        AllEqual(await Draws(template.Replace("$U", Random, StringComparison.Ordinal)));
    }

    [Fact]
    public async Task EagerAndDeferredReaches_AreOneMemberBinding()
    {
        AllEqual(await Draws(
            $"A = load('{Random}')\nF(0) = 0\nF(k) = {{\n    M = load('{Random}')\n    M.R + k * 0\n}}\nA.R, F(1), F(2)",
            AsyncRoutes));
        AllEqual(await Draws(
            $"F(0) = {{\n    M = load('{Random}')\n    M.R\n}}\nF(k) = {{\n    N = load('{Random}')\n    N.R + k * 0\n}}\nF(0), F(1), F(0), F(1)",
            AsyncRoutes));
    }

    [Fact]
    public async Task ALoadInsideALoadedModule_IsTheSameDeclaration()
    {
        // Module nesting mints no second `r.kat`: the module's own load (held or opened) and the
        // root's load are one declaration, so one member binding and one draw.
        AllEqual(await Draws($"A = load('{Random}')\nN = load('{Nest}')\nA.R, N.R2, A.R"));
        AllEqual(await Draws($"A = load('{Random}')\nN = load('{NestOpen}')\nA.R, N.R2, A.R"));
        AllEqual(await Draws($"N = load('{Nest}')\nA = load('{Random}')\nN.R2, A.R"));

        var parsed = await Parser.ParseAsync($"A = load('{Five}')\nN = load('{NestFive}')\nA.X + N.S.X", Server().Options());
        Assert.Empty(parsed.Diagnostics);
        var a = Assert.Single(parsed.Root.Properties, p => p.Name == "A").Value;
        var n = Assert.Single(parsed.Root.Properties, p => p.Name == "N").Value;
        Assert.Same(a, Assert.Single(n.Properties, p => p.Name == "S").Value);
    }

    [Fact]
    public async Task AHostEffectOfAMember_RunsOncePerBinding()
    {
        var observed = await OnEveryRouteAsync($"A = load('{Tick}')\nB = load('{Tick}')\nA.T, B.T, A.T()", Server);
        Assert.Equal("ok S[1, 1, 2]", $"{observed.Kind} {observed.Value}");
        Assert.Equal(["tick#1", "tick#2"], observed.HostCalls);

        var opened = await OnEveryRouteAsync($"open '{Tick}'\nA = load('{Tick}')\nT, A.T", Server);
        Assert.Equal("ok S[1, 1]", $"{opened.Kind} {opened.Value}");
        Assert.Equal(["tick#1"], opened.HostCalls);
    }

    [Fact]
    public async Task CanonicalAliases_AreOneDeclaration_AndOneFetch()
    {
        AllEqual(await Draws(
            $"A = load('{Random}')\nB = load('https://MODS.test:443/./r.kat#alias')\nA.R, B.R"));

        var modules = Server();
        var parsed = await Parser.ParseAsync(
            $"A = load('{Random}')\nB = load('https://MODS.test:443/./r.kat#alias')\nA.R, B.R", modules.Options());
        Assert.Empty(parsed.Diagnostics);
        Assert.Equal(1, Assert.Single(modules.Fetches).Value);
        Assert.Same(
            Assert.Single(parsed.Root.Properties, p => p.Name == "A").Value,
            Assert.Single(parsed.Root.Properties, p => p.Name == "B").Value);
    }

    [Fact]
    public async Task DistinctCanonicalUrls_AreDistinctDeclarations_EvenWithIdenticalBytes()
    {
        var draws = await Draws($"A = load('{Random}')\nB = load('{RandomTwin}')\nA.R, B.R");
        Assert.NotEqual(draws[0], draws[1]);

        var callables = await OnEveryRouteAsync($"P(f, f) = f\nA = load('{Five}')\nB = load('{FiveTwin}')\nP(A.X, B.X)", Server);
        Assert.Equal("err", callables.Kind);
        Assert.StartsWith("TypeMismatch", Assert.Single(callables.Errors), StringComparison.Ordinal);

        // The same for two written declarations of identical text: identity is never the text.
        var written = await OnEveryRouteAsync("P(f, f) = f\nA = { public X = 5 }\nB = { public X = 5 }\nP(A.X, B.X)", Server);
        Assert.Equal("err", written.Kind);
        Assert.StartsWith("TypeMismatch", Assert.Single(written.Errors), StringComparison.Ordinal);

        // Two declarations provide X, so a written X is the front end's ambiguity (Q-29 A-U).
        var opened = await OnEveryRouteAsync($"open A, B\nA = load('{Five}')\nB = load('{FiveTwin}')\nX", Server);
        Assert.Equal("parse", opened.Kind);
        Assert.StartsWith("AmbiguousOpen", Assert.Single(opened.Errors), StringComparison.Ordinal);
    }

    [Fact]
    public async Task HolderOutputs_StayPerHolder_WhileMembersShareTheModulesBinding()
    {
        // `A` and `B` read the module's OUTPUT under each holder's own entry (a bare read is the
        // target's demand under the holder's binding, FWD-02); their member `R` is the module's one.
        var draws = await Draws($"A = load('{OutputDraw}')\nB = load('{OutputDraw}')\nA, B, A.R, B.R, A, B");
        Assert.NotEqual(draws[0], draws[1]);
        Assert.Equal(draws[2], draws[3]);
        Assert.Equal(draws[0], draws[4]);
        Assert.Equal(draws[1], draws[5]);

        // A zero-parameter holder read through another property is that property's ordinary read.
        var aliased = await Draws($"A = load('{OutputDraw}')\nB = A\nA, B, A, B");
        AllEqual(aliased);
    }

    [Fact]
    public async Task OneModule_IsOneCallableIdentity()
    {
        // NEED-04: a repeated parameter binds ONE callable — every reach of one module's member is it.
        foreach (var source in new[]
        {
            $"P(f, f) = f\nA = load('{Five}')\nB = load('{Five}')\nP(A.X, B.X)",
            $"P(f, f) = f\nA = load('{Five}')\nC = {{ B = load('{Five}')\nB.X }}\nP(A.X, C.B.X)",
            $"open A\nP(f, f) = f\nA = load('{Five}')\nP(X, A.X)",
            $"open '{Five}'\nP(f, f) = f\nA = load('{Five}')\nP(X, A.X)",
            $"P(f, f) = f\nA = load('{Five}')\nB = load('{FiveAlias}')\nP(A.X, B.X)",
            $"P(f, f) = f\nA = load('{Five}')\nN = load('{NestFive}')\nP(A.X, N.S.X)",
        })
        {
            var observed = await OnEveryRouteAsync(source, Server);
            Assert.True(observed.Kind == "ok" && observed.Value == "5", $"{observed}\n{source}");
        }
    }

    [Fact]
    public async Task OneModuleReachedTwice_IsOneOpenProvider()
    {
        // Q-19 D-I: providers are counted by identity, and every reach of one URL is one declaration.
        foreach (var source in new[]
        {
            $"open A, B\nA = load('{Five}')\nB = load('{Five}')\nX",
            $"open '{Five}', '{Five}'\nX",
            $"open A, '{Five}'\nA = load('{Five}')\nX",
            $"open load('{Five}'), A\nA = load('{Five}')\nX",
            $"open '{Five}', '{FiveAlias}'\nX",
        })
        {
            var observed = await OnEveryRouteAsync(source, Server);
            Assert.True(observed.Kind == "ok" && observed.Value == "5", $"{observed}\n{source}");
        }
    }

    [Fact]
    public async Task APropertyReadingAHolder_IsNoProviderOfTheModule()
    {
        // `B = A` reads A's value — the module's output — and declares nothing, so it is no alias of
        // the module and `open B` provides nothing: the written X is an implicit parameter of the
        // never-called root, reported at its row.
        var observed = await OnEveryRouteAsync($"open B\nA = load('{Five}')\nB = A\nX", Server);
        Assert.Equal("err", observed.Kind);
        Assert.StartsWith("UnresolvedImplicitParams", Assert.Single(observed.Errors), StringComparison.Ordinal);
        Assert.EndsWith("@ [4:1, 4:2)", observed.Errors[0], StringComparison.Ordinal);
    }

    [Fact]
    public async Task TheElaboratedTree_HoldsOneDeclarationPerUrl()
    {
        var parsed = await Parser.ParseAsync(
            $"open '{Five}'\nA = load('{Five}')\nB = {{ C = load('{Five}')\nC.X }}\nF(0) = 0\nF(k) = k\nA.X, B",
            Server().Options());
        Assert.Empty(parsed.Diagnostics);
        var a = Assert.Single(parsed.Root.Properties, p => p.Name == "A").Value;
        var c = Assert.Single(Assert.Single(parsed.Root.Properties, p => p.Name == "B").Value.Properties, p => p.Name == "C").Value;
        var opened = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(parsed.Root.Opens)).Algorithm;
        Assert.True(a.IsModuleRoot);
        Assert.Same(a, c);
        Assert.Same(a, opened);
    }

    [Fact]
    public async Task ModuleDiagnostics_AreReportedOnce_AtTheFirstImportSite()
    {
        // The module's closed list names an undeclared `y`: one module, one declaration, one report —
        // at the first site that imports it, never once per site.
        var server = () => new Modules(("https://mods.test/bad.kat", "public F(x) = y"));
        var parsed = await Parser.ParseAsync(
            "A = load('https://mods.test/bad.kat')\nB = load('https://mods.test/bad.kat')\nC = { D = load('https://mods.test/bad.kat')\nD }\n1",
            server().Options());
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 1, 1, 2), diagnostic.Span);

        // A module-internal open ambiguity is reported the same way (Q-29 A-U inside the unit).
        var ambiguous = () => new Modules(("https://mods.test/amb.kat",
            "open L1, L2\nL1 = { public X = 1 }\nL2 = { public X = 2 }\npublic V = X"));
        var twice = await Parser.ParseAsync(
            "open 'https://mods.test/amb.kat'\nM = load('https://mods.test/amb.kat')\n1", ambiguous().Options());
        var report = Assert.Single(twice.Diagnostics);
        Assert.Equal(DiagnosticCode.AmbiguousOpen, report.Code);
        Assert.Equal(new SourceSpan(1, 6, 1, 33), report.Span);
    }
}
