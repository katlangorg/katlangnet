using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// X-48 (constitution MOD-06, MOD-10, RUN-04): an open target is validated like any other body.
/// Prelude rooting decides what an inline <c>open { … }</c> target or a directly opened module
/// (<c>open 'u'</c>, <c>open load('u')</c>) can SEE — never which front-end rules apply inside it.
/// The implicit-argument resolver walked open targets with no diagnostics sink, so its own
/// verdicts — <see cref="DiagnosticCode.UnforwardableParameter"/>,
/// <see cref="DiagnosticCode.UnforwardableCallable"/>, <see cref="DiagnosticCode.UnliftableClauseFamily"/>
/// and the inferred-signature <see cref="DiagnosticCode.InvalidCollectingBinding"/> — vanished
/// there: <c>open { N(y) = y ⏎ public P(x) = N ⏎ public X = 1 }</c> / <c>X</c> printed <c>1</c>,
/// and <c>open { C1(a, *p) = a ⏎ C2(b, *q) = b ⏎ public K = C1 + C2 }</c> / <c>K(1, 2, 3)</c>
/// EVALUATED the parser-recovery signature to <c>3</c>. The open-target walk now reports into the
/// caller's sink like every other region, so the settled oracle holds: the same text is rejected
/// with the same code whether it is a property body or an open target, eagerly as a
/// <see cref="RunResult.ParseFailure"/> and inside a selected deferred compilation unit as the
/// <see cref="RunResult.EvalFailure"/> of that selection (MOD-11), while a never-selected unit stays
/// unacquired and silent (Q-61/Q-71). FWD-02 is unchanged: <c>P(x) = N</c> never means
/// <c>P(x) = N(x)</c>; <c>P(y) = N</c>, the explicit <c>P(x) = N(x)</c>, formula lifting and Q-04
/// ancestor reuse keep their meaning. C#-only traversal plumbing: Lean proves the forwarding law
/// (<c>bare_forwarding_never_renames</c> and siblings) and models neither open-target regions nor
/// deferred materialization.
/// </summary>
public class OpenTargetResolverValidationTests
{
    private const string Url = "https://katlang.org/x48/module.kat";
    private const string OtherUrl = "https://katlang.org/x48/other.kat";

    // ── Fixtures ─────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// A module text the settled front-end rules reject, the code they reject it with, and where:
    /// the reference <paramref name="Token"/> at the end-most occurrence inside the written line
    /// <paramref name="Anchor"/>. Every module also exports <c>X = 1</c>, the member the programs read.
    /// </summary>
    public sealed record InvalidModule(string Name, string Text, DiagnosticCode Code, string Anchor, string Token)
    {
        public override string ToString() => Name;
    }

    public static readonly InvalidModule[] InvalidModules =
    [
        new("no-renaming", "N(y) = y\npublic P(x) = N\npublic X = 1", DiagnosticCode.UnforwardableParameter, "public P(x) = N", "N"),
        new("alias", "N(y) = y\nA = N\npublic P(x) = A\npublic X = 1", DiagnosticCode.UnforwardableParameter, "public P(x) = A", "A"),
        new("alias-chain", "N(y) = y\nA = N\nB = A\npublic P(x) = B\npublic X = 1", DiagnosticCode.UnforwardableParameter, "public P(x) = B", "B"),
        new("list-leaf-reshaped", "N([y]) = y\npublic P(y) = N\npublic X = 1", DiagnosticCode.UnforwardableParameter, "public P(y) = N", "N"),
        new("sequence-vs-list", "N((y, z)) = y\npublic P([y, z]) = N\npublic X = 1", DiagnosticCode.UnforwardableParameter, "public P([y, z]) = N", "N"),
        new("repeated-name", "N(y, y) = y\npublic P(x) = N\npublic X = 1", DiagnosticCode.UnforwardableParameter, "public P(x) = N", "N"),
        new("nameable-family", "G(0) = 0\nG(k) = k\npublic P(j) = G\npublic X = 1", DiagnosticCode.UnforwardableParameter, "public P(j) = G", "G"),
        new("builtin", "public P(x) = count\npublic X = 1", DiagnosticCode.UnforwardableParameter, "public P(x) = count", "count"),
        new("math", "public P(q) = abs\npublic X = 1", DiagnosticCode.UnforwardableParameter, "public P(q) = abs", "abs"),
        new("host", "public P(y) = trace\npublic X = 1", DiagnosticCode.UnforwardableParameter, "public P(y) = trace", "trace"),
        new("unnameable-family-forwarded", "G(0) = 0\nG(1) = 1\npublic P(n) = G\npublic X = 1", DiagnosticCode.UnforwardableCallable, "public P(n) = G", "G"),
        new("unnameable-family-lifted", "G(0) = 0\nG(1) = 1\npublic K = G + 1\npublic X = 1", DiagnosticCode.UnliftableClauseFamily, "public K = G + 1", "G"),
        new("two-inferred-collectors", "C1(a, *p) = a\nC2(b, *q) = b\npublic K = C1 + C2\npublic X = 1", DiagnosticCode.InvalidCollectingBinding, "public K = C1 + C2", "C2"),
    ];

    public static TheoryData<InvalidModule> InvalidModuleData()
    {
        var data = new TheoryData<InvalidModule>();
        foreach (var module in InvalidModules)
            data.Add(module);
        return data;
    }

    /// <summary>
    /// A valid module, the request that exercises it (<c>{0}</c> is the member prefix: empty for an
    /// open target, <c>M.</c> for a property-held module) and its value in every position.
    /// </summary>
    public static TheoryData<string, string, string, string> ValidModules() => new()
    {
        { "same-name", "N(y) = y\npublic P(y) = N", "{0}P(5)", "5" },
        { "explicit-differently-named-call", "N(y) = y\npublic P(x) = N(x)", "{0}P(5)", "5" },
        { "formula-lifting", "N(y) = y\npublic P = N + 1", "{0}P(5)", "6" },
        { "alias-same-name", "N(y) = y\nA = N\npublic P(y) = A", "{0}P(5)", "5" },
        { "alias-explicit-call", "N(y) = y\nA = N\npublic P(x) = A(x)", "{0}P(5)", "5" },
        { "alias-chain-same-name", "N(y) = y\nA = N\nB = A\npublic P(y) = B", "{0}P(5)", "5" },
        { "list-same-contract", "N([y]) = y\npublic P([y]) = N", "{0}P([5])", "5" },
        { "sequence-same-contract", "N((y, z)) = y\npublic P((y, z)) = N", "{0}P((5, 6))", "5" },
        { "collector-to-collector", "N(*ys) = ys\npublic P(*ys) = N", "{0}P(1, 2)", "L[1, 2]" },
        { "collector-source-into-fixed", "N(ys) = ys\npublic P(*ys) = N", "{0}P(1, 2)", "L[1, 2]" },
        { "fixed-source-into-collector", "N(*ys) = ys\npublic P(ys) = N", "{0}P([1, 2])", "L[L[1, 2]]" },
        { "unsupplied-collector-forwards-nothing", "N(*ys) = ys\npublic P(*xs) = N", "{0}P(1, 2)", "L[]" },
        { "repeated-name-same-binding", "N(y, y) = y\npublic P(y) = N", "{0}P(5)", "5" },
        { "nameable-family-same-name", "G(0) = 0\nG(k) = k\npublic P(k) = G", "{0}P(5)", "5" },
        { "nameable-family-formula", "G(0) = 0\nG(k) = k\npublic K = G + 1", "{0}K(4)", "5" },
        { "builtin-contract-name", "public P(collection) = count", "{0}P([1, 2, 3])", "3" },
        { "one-shared-collector-name", "C1(a, *p) = a\nC2(b, *p) = b\npublic K = C1 + C2", "{0}K(1, 2, 3)", "4" },
    };

    private static string Indent(string text, string by = "  ")
        => string.Join("\n", text.Split('\n').Select(line => line.Length == 0 ? line : by + line));

    /// <summary>The module held by a property: the property-position oracle of the same text.</summary>
    private static string AsProperty(string module, string request)
        => "M = {\n" + Indent(module) + "\n}\n" + string.Format(request, "M.");

    /// <summary>The module as an inline open target.</summary>
    private static string AsInlineOpen(string module, string request)
        => "open {\n" + Indent(module) + "\n}\n" + string.Format(request, "");

    /// <summary>
    /// The half-open span of the end-most <paramref name="token"/> inside the one source line that
    /// contains <paramref name="anchor"/>.
    /// </summary>
    private static SourceSpan SpanOf(string source, string anchor, string token)
    {
        var lines = source.Split('\n');
        var index = Assert.Single(Enumerable.Range(0, lines.Length), i => lines[i].Contains(anchor, StringComparison.Ordinal));
        var column = lines[index].IndexOf(anchor, StringComparison.Ordinal) + anchor.LastIndexOf(token, StringComparison.Ordinal);
        return new SourceSpan(index + 1, column + 1, index + 1, column + 1 + token.Length);
    }

    /// <summary>The span of the first string literal on the one line containing <paramref name="anchor"/>.</summary>
    private static SourceSpan LiteralSpan(string source, string anchor)
    {
        var lines = source.Split('\n');
        var index = Assert.Single(Enumerable.Range(0, lines.Length), i => lines[i].Contains(anchor, StringComparison.Ordinal));
        var start = lines[index].IndexOf('\'');
        var end = lines[index].IndexOf('\'', start + 1) + 1;
        return new SourceSpan(index + 1, start + 1, index + 1, end + 1);
    }

    private static string Describe(KatLangErrorCode code, SourceSpan span) => $"{code} @ {span}";

    private static KatLangErrorCode Public(DiagnosticCode code) => KatLangError.MapDiagnosticCode(code);

    /// <summary>The code and position of every error of an observation, without the message.</summary>
    private static IReadOnlyList<string> CodesAndSpans(SixRouteAgreement.Observation observation)
        => [.. observation.Errors.Select(static error => error[..error.IndexOf(':', StringComparison.Ordinal)] + " @ " + error[(error.LastIndexOf(" @ ", StringComparison.Ordinal) + 3)..])];

    // ── Module routes ────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The six established routes for a program that loads modules. A configured downloader makes the
    /// synchronous engine entry point unavailable by contract, so <see cref="ModuleRoute.Engine"/> is
    /// <see cref="KatLangEngine.RunAsync"/> with synchronous host operations and an immediately
    /// completing downloader, <see cref="ModuleRoute.EngineSuspendingDownloader"/> the same engine
    /// with a downloader that suspends before every module, <see cref="ModuleRoute.EngineAsyncTwin"/>
    /// the engine with suspending host operations, and the three evaluator routes evaluate
    /// <see cref="Parser.ParseAsync(string, RunOptions?, CancellationToken)"/>'s tree. A tree carrying a
    /// deferred compilation unit is async-only by contract, so deferred programs skip the two
    /// synchronous evaluators.
    /// </summary>
    public enum ModuleRoute
    {
        Engine,
        EngineSuspendingDownloader,
        EngineAsyncTwin,
        Generic,
        Optimized,
        ForcedTwin,
    }

    private static readonly ModuleRoute[] EagerModuleRoutes = Enum.GetValues<ModuleRoute>();

    private static readonly ModuleRoute[] DeferredModuleRoutes =
        [ModuleRoute.Engine, ModuleRoute.EngineSuspendingDownloader, ModuleRoute.EngineAsyncTwin, ModuleRoute.ForcedTwin];

    private sealed class ModuleServer(params (string Url, string Source)[] modules)
    {
        private readonly Dictionary<string, string> _modules =
            modules.ToDictionary(module => module.Url, module => module.Source, StringComparer.Ordinal);

        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int this[string url] => Fetches.GetValueOrDefault(url);

        public int Total => Fetches.Values.Sum();

        public async ValueTask<string> Download(string url, CancellationToken cancellationToken, bool suspend)
        {
            lock (Fetches)
                Fetches[url] = this[url] + 1;
            if (suspend)
                await Task.Yield();
            return _modules.TryGetValue(url, out var source)
                ? source
                : throw new InvalidOperationException($"404: {url}");
        }
    }

    private sealed record ModuleObservation(string Kind, string? Value, IReadOnlyList<string> Errors, IReadOnlyList<string> HostCalls, int Fetches)
    {
        public override string ToString()
            => $"{Kind} {Value} errors=[{string.Join(" | ", Errors)}] host=[{string.Join(",", HostCalls)}] fetches={Fetches}";
    }

    private static HostOperations Operations(List<string> log, bool suspending)
        => suspending
            ? HostOperations.Create(HostOperation.CreateAsync("trace", async (args, _) =>
            {
                await Task.Yield();
                lock (log)
                    log.Add($"trace({SixRouteAgreement.Neutral(args[0])})");
                return args[0];
            }, "x"))
            : HostOperations.Create(HostOperation.Create("trace", (args, _) =>
            {
                lock (log)
                    log.Add($"trace({SixRouteAgreement.Neutral(args[0])})");
                return args[0];
            }, "x"));

    private static async Task<ModuleObservation> ObserveModuleAsync(ModuleRoute route, string source, params (string Url, string Source)[] modules)
    {
        var server = new ModuleServer(modules);
        var log = new List<string>();
        var options = new RunOptions
        {
            HostOperations = Operations(log, route is ModuleRoute.EngineAsyncTwin or ModuleRoute.ForcedTwin),
            DownloadCode = (url, token) => server.Download(url, token, suspend: route is ModuleRoute.EngineSuspendingDownloader),
        };

        static string Error(KatLangError error) => $"{error.Code} @ {error.Span}";

        if (route is ModuleRoute.Engine or ModuleRoute.EngineSuspendingDownloader or ModuleRoute.EngineAsyncTwin)
        {
            var result = await KatLangEngine.RunAsync(source, options);
            return result switch
            {
                RunResult.Success success => new("ok", SixRouteAgreement.Neutral(success.Value), [], [.. log], server.Total),
                RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(Error)], [.. log], server.Total),
                RunResult.ParseFailure failure => new("parse", null, [.. failure.Errors.Select(Error)], [.. log], server.Total),
                RunResult.NoProgramOutput none => new("none", null, [none.Diagnostic.Code.ToString()], [.. log], server.Total),
            };
        }

        var parsed = await Parser.ParseAsync(source, options);
        if (parsed.HasErrors)
        {
            return new("parse", null,
                [.. parsed.Diagnostics.Where(static d => d.Severity == DiagnosticSeverity.Error).Select(static d => Error(KatLangError.FromDiagnostic(d)))],
                [.. log], server.Total);
        }

        var program = new Expr.AlgorithmExpr(parsed.Root);
        var (evaluation, _) = route switch
        {
            ModuleRoute.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false, hostOperations: options.HostOperations),
            ModuleRoute.Optimized => Evaluator.RunCountedObserved(program, enableOptimizations: true, hostOperations: options.HostOperations),
            ModuleRoute.ForcedTwin => await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: options.HostOperations),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };

        return evaluation.IsError
            ? new("err", null, [Error(KatLangError.FromEvalError(evaluation.Error))], [.. log], server.Total)
            : new("ok", SixRouteAgreement.Neutral(evaluation.Value.Value), [], [.. log], server.Total);
    }

    /// <summary>Runs a module-loading program on <paramref name="routes"/>, requiring one shared observation.</summary>
    private static async Task<ModuleObservation> OnModuleRoutesAsync(ModuleRoute[] routes, string source, params (string Url, string Source)[] modules)
    {
        var oracle = await ObserveModuleAsync(routes[0], source, modules);
        foreach (var route in routes.Skip(1))
        {
            var observation = await ObserveModuleAsync(route, source, modules);
            Assert.True(
                oracle.Kind == observation.Kind
                    && oracle.Value == observation.Value
                    && oracle.Errors.SequenceEqual(observation.Errors)
                    && oracle.HostCalls.SequenceEqual(observation.HostCalls)
                    && oracle.Fetches == observation.Fetches,
                $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
        }

        return oracle;
    }

    // ── A. Eager inline open target ≡ property body ──────────────────────────────────────────

    [Theory]
    [MemberData(nameof(InvalidModuleData))]
    public async Task InlineOpenTarget_IsRejectedExactlyLikeThePropertyBody(InvalidModule module)
    {
        const string request = "trace({0}X)";
        var property = AsProperty(module.Text, request);
        var open = AsInlineOpen(module.Text, request);

        var oracle = await SixRouteAgreement.OnEveryRouteAsync(property);
        var observed = await SixRouteAgreement.OnEveryRouteAsync(open);

        // The property position is the settled oracle; the open target now reports the same error
        // at the same written reference, and neither program ever runs (`trace` never logs).
        var expected = Describe(Public(module.Code), SpanOf(property, module.Anchor, module.Token));
        Assert.Equal("parse", oracle.Kind);
        Assert.Equal([expected], CodesAndSpans(oracle));
        Assert.Equal("parse", observed.Kind);
        Assert.Equal([Describe(Public(module.Code), SpanOf(open, module.Anchor, module.Token))], CodesAndSpans(observed));
        Assert.Equal(SpanOf(property, module.Anchor, module.Token), SpanOf(open, module.Anchor, module.Token));
        Assert.Empty(observed.HostCalls);

        // Same wording as the property body: one verdict, one rule.
        Assert.Equal(oracle.Errors, observed.Errors);
    }

    [Fact]
    public async Task RecoveredInferredSignature_NeverReachesEvaluation()
    {
        // X-02: two collecting parameters at one level are no signature. The resolver installs the
        // recovery signature `K(a, *p, b, q)` beside its error so later passes see a well-formed tree;
        // that tree must never run. Before X-48 was fixed the open-target spelling evaluated it to 3.
        const string source = "open {\n  C1(a, *p) = a\n  C2(b, *q) = b\n  public K = C1 + C2\n}\ntrace(K(1, 2, 3))";

        var error = Assert.Single(SourceProvenance.ExpectFrontEndError(source), d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.InvalidCollectingBinding, error.Code);
        Assert.Equal(SpanOf(source, "public K = C1 + C2", "C2"), error.Span);
        Assert.Contains("'*p' (needed by 'C1') and '*q' (needed by 'C2')", error.Message, StringComparison.Ordinal);

        // The recovery tree exists only beside that error: the signature it holds is the one the
        // defect used to evaluate.
        var target = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(SourceProvenance.ParseAllowingDiagnostics(source).Root.Opens));
        var k = Assert.Single(target.Algorithm.Properties, property => property.Name == "K");
        Assert.Equal("K(a, *p, b, q)", CallableSignature.FromAlgorithm("K", k.Value).DisplayText);

        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", observation.Kind);
        Assert.Null(observation.Value);
        Assert.Empty(observation.HostCalls);
        Assert.Equal(
            [Describe(KatLangErrorCode.InvalidCollectingBinding, SpanOf(source, "public K = C1 + C2", "C2"))],
            CodesAndSpans(observation));
    }

    // ── B. Eager external open target ≡ property-held module ──────────────────────────────────

    [Theory]
    [MemberData(nameof(InvalidModuleData))]
    public async Task ExternalOpenTarget_IsRejectedLikeAPropertyHeldModule_BeforeAnythingRuns(InvalidModule module)
    {
        var property = $"M = load('{Url}')\ntrace(M.X)";
        var oracle = await OnModuleRoutesAsync(EagerModuleRoutes, property, (Url, module.Text));
        Assert.Equal("parse", oracle.Kind);
        Assert.Equal([Describe(Public(module.Code), SpanOf(property, "M = load", "M"))], oracle.Errors);

        foreach (var (spelling, site) in new[]
        {
            ($"open '{Url}'\ntrace(X)", (Func<string, SourceSpan>)(s => LiteralSpan(s, "open '"))),
            ($"open load('{Url}')\ntrace(X)", s => SpanOf(s, $"open load('{Url}')", $"load('{Url}')")),
            ($"F(n) = {{\n  open '{Url}'\n  trace(X)\n}}\nF(1)", s => LiteralSpan(s, "open '")),
        })
        {
            var observed = await OnModuleRoutesAsync(EagerModuleRoutes, spelling, (Url, module.Text));

            // Source acquired once, rejected by the front end at the import site with the
            // property-position code, and the body never ran.
            Assert.Equal("parse", observed.Kind);
            Assert.Equal([Describe(Public(module.Code), site(spelling))], observed.Errors);
            Assert.Equal(1, observed.Fetches);
            Assert.Empty(observed.HostCalls);
        }
    }

    [Fact]
    public async Task ModuleOpenTargetInsideAModule_IsValidatedToo()
    {
        // The opened module's own open target is an open-target region of its own: its invalid
        // member is reported at the outer import site, whichever position holds the outer module.
        var outer = $"open '{OtherUrl}'\npublic Z = X + 1";
        var inner = InvalidModules[0].Text;
        foreach (var source in new[] { $"open '{Url}'\ntrace(Z)", $"M = load('{Url}')\ntrace(M.Z)" })
        {
            var observed = await OnModuleRoutesAsync(EagerModuleRoutes, source, (Url, outer), (OtherUrl, inner));
            Assert.Equal("parse", observed.Kind);
            Assert.Equal(
                [Describe(KatLangErrorCode.UnforwardableParameter, source.StartsWith("open", StringComparison.Ordinal)
                    ? LiteralSpan(source, "open '") : SpanOf(source, "M = load", "M"))],
                observed.Errors);
            Assert.Equal(2, observed.Fetches);
            Assert.Empty(observed.HostCalls);
        }

        var selected = $"F(0) = 0\nF(n) = {{\n  open '{Url}'\n  trace(Z)\n}}\nF(1)";
        var deferred = await OnModuleRoutesAsync(DeferredModuleRoutes, selected, (Url, outer), (OtherUrl, inner));
        Assert.Equal("err", deferred.Kind);
        Assert.Equal([Describe(KatLangErrorCode.UnforwardableParameter, LiteralSpan(selected, "open '"))], deferred.Errors);
        Assert.Equal(2, deferred.Fetches);
        Assert.Empty(deferred.HostCalls);
    }

    // ── C. Deferred compilation units ─────────────────────────────────────────────────────────

    private static DeferredModuleRegion Region(Algorithm root, string family, int branch)
    {
        var conditional = Assert.IsType<Algorithm.Conditional>(root.Properties.Single(property => property.Name == family).Value);
        return Assert.IsType<DeferredModuleRegion>(conditional.Branches[branch].Body.DeferredRegion);
    }

    [Theory]
    [MemberData(nameof(InvalidModuleData))]
    public async Task SelectedDeferredOpenTarget_FailsAtTheSelectionBoundary_WithTheEagerCode(InvalidModule module)
    {
        const string branches = "F(0) = 0\nF(n) = {{\n  open '{0}'\n  trace(X)\n}}\n";
        var selected = string.Format(branches, Url) + "F(1)";

        var observed = await OnModuleRoutesAsync(DeferredModuleRoutes, selected, (Url, module.Text));

        // The whole unit is validated when the call selects it — the unread member included —
        // and the error stops the evaluation before the body runs, positioned at the branch's
        // import site (MOD-10/MOD-11): the eager spelling's code, transported as an EvalFailure.
        Assert.Equal("err", observed.Kind);
        Assert.Equal([Describe(Public(module.Code), LiteralSpan(selected, "open '"))], observed.Errors);
        Assert.Equal(1, observed.Fetches);
        Assert.Empty(observed.HostCalls);

        var eager = await OnModuleRoutesAsync(EagerModuleRoutes, $"open '{Url}'\ntrace(X)", (Url, module.Text));
        Assert.Equal(eager.Errors.Single().Split(' ')[0], observed.Errors.Single().Split(' ')[0]);

        // The property-position deferred twin reports the same code at its own import site.
        var propertyTwin = $"F(0) = 0\nF(n) = {{\n  M = load('{Url}')\n  trace(M.X)\n}}\nF(1)";
        var twin = await OnModuleRoutesAsync(DeferredModuleRoutes, propertyTwin, (Url, module.Text));
        Assert.Equal([Describe(Public(module.Code), SpanOf(propertyTwin, "M = load", "M"))], twin.Errors);

        // A failed materialization is never cached.
        var server = new ModuleServer((Url, module.Text));
        var parsed = await Parser.ParseAsync(selected, new RunOptions { DownloadCode = (url, token) => server.Download(url, token, suspend: false), HostOperations = Operations([], suspending: false) });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var region = Region(parsed.Root, "F", 1);
        var run = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root),
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            hostOperations: Operations([], suspending: false));
        Assert.True(run.Result.IsError);
        Assert.Equal(Public(module.Code), run.Result.Error.Code);
        Assert.False(region.IsMaterialized);
        Assert.Equal(1, server[Url]);
    }

    [Theory]
    [MemberData(nameof(InvalidModuleData))]
    public async Task UnselectedDeferredOpenTarget_StaysUnacquiredAndSilent(InvalidModule module)
    {
        var dead = $"F(0) = 0\nF(n) = {{\n  open '{Url}'\n  trace(X)\n}}\nF(0)";

        var observed = await OnModuleRoutesAsync(DeferredModuleRoutes, dead, (Url, module.Text));

        Assert.Equal("ok", observed.Kind);
        Assert.Equal("0", observed.Value);
        Assert.Equal(0, observed.Fetches);
        Assert.Empty(observed.HostCalls);

        var server = new ModuleServer((Url, module.Text));
        var parsed = await Parser.ParseAsync(dead, new RunOptions { DownloadCode = (url, token) => server.Download(url, token, suspend: false), HostOperations = Operations([], suspending: false) });
        Assert.Empty(parsed.Diagnostics);
        var region = Region(parsed.Root, "F", 1);
        var run = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root),
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            hostOperations: Operations([], suspending: false));
        Assert.False(run.Result.IsError, run.Result.IsError ? run.Result.Error.ToString() : "");
        Assert.False(region.IsMaterialized);
        Assert.Equal(0, server.Total);
    }

    [Fact]
    public async Task InlineOpenTargetInsideASelectedDeferredUnit_IsValidatedWithTheUnit()
    {
        // The branch loads a module, so the whole branch is one deferred compilation unit; its
        // inline open target is part of that unit and is judged when — and only when — it is selected.
        const string unit = "F(0) = 0\nF(n) = {\n  open {\n    N(y) = y\n    public P(x) = N\n    public W = 1\n  }, '" + OtherUrl + "'\n  trace(W + Y)\n}\n";
        const string other = "public Y = 2";

        var selected = await OnModuleRoutesAsync(DeferredModuleRoutes, unit + "F(1)", (OtherUrl, other));
        Assert.Equal("err", selected.Kind);
        Assert.Equal([Describe(KatLangErrorCode.UnforwardableParameter, SpanOf(unit + "F(1)", "public P(x) = N", "N"))], selected.Errors);
        Assert.Empty(selected.HostCalls);

        var dead = await OnModuleRoutesAsync(DeferredModuleRoutes, unit + "F(0)", (OtherUrl, other));
        Assert.Equal("ok", dead.Kind);
        Assert.Equal("0", dead.Value);
        Assert.Equal(0, dead.Fetches);
    }

    // ── D. Valid controls keep their meaning in every position ────────────────────────────────

    [Theory]
    [MemberData(nameof(ValidModules))]
    public async Task ValidForwardingAndLifting_KeepTheirMeaningInEveryPosition(string name, string module, string request, string expected)
    {
        _ = name;
        var property = await SixRouteAgreement.OnEveryRouteAsync(AsProperty(module, request));
        var open = await SixRouteAgreement.OnEveryRouteAsync(AsInlineOpen(module, request));
        Assert.Equal(("ok", expected), (property.Kind, property.Value));
        Assert.Equal(("ok", expected), (open.Kind, open.Value));

        var external = await OnModuleRoutesAsync(EagerModuleRoutes, $"open '{Url}'\n" + string.Format(request, ""), (Url, module));
        Assert.Equal(("ok", expected, 1), (external.Kind, external.Value, external.Fetches));

        var deferred = await OnModuleRoutesAsync(
            DeferredModuleRoutes,
            $"F(0) = 0\nF(n) = {{\n  open '{Url}'\n  " + string.Format(request, "") + "\n}\nF(1)",
            (Url, module));
        Assert.Equal(("ok", expected, 1), (deferred.Kind, deferred.Value, deferred.Fetches));
    }

    [Fact]
    public async Task HostOperationContract_IsForwardedInsideAnOpenTarget()
    {
        // `trace`'s declared parameter is `x`: the same-named binding forwards, the call runs once.
        var observation = await SixRouteAgreement.OnEveryRouteAsync("open {\n  public P(x) = trace\n}\nP(3)");
        Assert.Equal(("ok", "3"), (observation.Kind, observation.Value));
        Assert.Equal(["trace(3)"], observation.HostCalls);
    }

    // ── E. Q-04 ancestor reuse is unchanged; nothing is renamed ───────────────────────────────

    [Theory]
    [InlineData("F(y) = {\n  M = {\n    N(y) = y\n    public P(x) = N\n  }\n  M.P(5)\n}\nF(7)")]
    [InlineData("F(y) = {\n  N(y) = y\n  P(x) = N\n  P(5)\n}\nF(7)")]
    [InlineData("open {\n  public Q(y) = {\n    N(y) = y\n    P(x) = N\n    P(5)\n  }\n}\nQ(7)")]
    public async Task EnclosingBindingOfTheSameName_SuppliesTheCallee(string source)
    {
        // The enclosing `y` (Q-04) supplies N's `y`; P's own `x` stays unused — reuse, not renaming.
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal(("ok", "7"), (observation.Kind, observation.Value));
    }

    [Theory]
    [InlineData("y")]
    [InlineData("x")]
    public async Task OpenersBinding_IsInvisibleToTheOpenTarget_SoNothingIsSupplied(string openerParameter)
    {
        // MOD-06: an inline target sees none of the opener's bindings, so no `y` exists inside it, and
        // an unrelated `x` is never renamed to `y`. Formerly accepted, failing only when P was called.
        var source = $"F({openerParameter}) = {{\n  open {{\n    N(y) = y\n    public P(x) = N\n  }}\n  P(5)\n}}\nF(7)";
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", observation.Kind);
        Assert.Equal([Describe(KatLangErrorCode.UnforwardableParameter, SpanOf(source, "public P(x) = N", "N"))], CodesAndSpans(observation));
    }

    // ── F. Declaration order never decides validity ───────────────────────────────────────────

    public static TheoryData<string> DeclarationOrders() => new()
    {
        "N(y) = y\npublic P(x) = N\npublic X = 1",
        "N(y) = y\npublic X = 1\npublic P(x) = N",
        "public P(x) = N\nN(y) = y\npublic X = 1",
        "public P(x) = N\npublic X = 1\nN(y) = y",
        "public X = 1\nN(y) = y\npublic P(x) = N",
        "public X = 1\npublic P(x) = N\nN(y) = y",
    };

    [Theory]
    [MemberData(nameof(DeclarationOrders))]
    public async Task DeclarationOrder_NeverChangesTheVerdict(string module)
    {
        var open = AsInlineOpen(module, "trace({0}X)");
        var observation = await SixRouteAgreement.OnEveryRouteAsync(open);
        Assert.Equal("parse", observation.Kind);
        Assert.Equal([Describe(KatLangErrorCode.UnforwardableParameter, SpanOf(open, "public P(x) = N", "N"))], CodesAndSpans(observation));

        var external = $"open '{Url}'\ntrace(X)";
        var loaded = await OnModuleRoutesAsync(EagerModuleRoutes, external, (Url, module));
        Assert.Equal([Describe(KatLangErrorCode.UnforwardableParameter, LiteralSpan(external, "open '"))], loaded.Errors);

        var selected = $"F(0) = 0\nF(n) = {{\n  open '{Url}'\n  trace(X)\n}}\nF(1)";
        var deferred = await OnModuleRoutesAsync(DeferredModuleRoutes, selected, (Url, module));
        Assert.Equal([Describe(KatLangErrorCode.UnforwardableParameter, LiteralSpan(selected, "open '"))], deferred.Errors);
    }

    public static TheoryData<InvalidModule> CollectorAndAliasDeclarationOrders()
    {
        var data = new TheoryData<InvalidModule>();
        foreach (var fixture in InvalidModules.Where(module => module.Name is "alias-chain" or "two-inferred-collectors"))
        {
            var order = 0;
            foreach (var lines in Permute(fixture.Text.Split('\n')))
                data.Add(fixture with { Name = $"{fixture.Name}-order-{order++}", Text = string.Join("\n", lines) });
        }
        return data;

        static IEnumerable<string[]> Permute(string[] lines)
        {
            if (lines.Length == 0)
            {
                yield return [];
                yield break;
            }
            for (var index = 0; index < lines.Length; index++)
                foreach (var tail in Permute([.. lines.Take(index), .. lines.Skip(index + 1)]))
                    yield return [lines[index], .. tail];
        }
    }

    [Theory]
    [MemberData(nameof(CollectorAndAliasDeclarationOrders))]
    public async Task CollectorAndAliasOrder_NeverChangesTheStaticVerdict(InvalidModule module)
    {
        var inline = AsInlineOpen(module.Text, "trace({0}X)");
        var observed = await SixRouteAgreement.OnEveryRouteAsync(inline);
        Assert.Equal("parse", observed.Kind);
        Assert.Equal([Describe(Public(module.Code), SpanOf(inline, module.Anchor, module.Token))], CodesAndSpans(observed));
        Assert.Empty(observed.HostCalls);

        var selected = $"F(0) = 0\nF(n) = {{\n  open '{Url}'\n  trace(X)\n}}\nF(1)";
        var deferred = await OnModuleRoutesAsync(DeferredModuleRoutes, selected, (Url, module.Text));
        Assert.Equal("err", deferred.Kind);
        Assert.Equal([Describe(Public(module.Code), LiteralSpan(selected, "open '"))], deferred.Errors);
        Assert.Empty(deferred.HostCalls);
    }

    [Theory]
    [InlineData("N(y) = y\npublic P(x) = N\npublic Bad(z) = Missing + 0\npublic X = 1",
        KatLangErrorCode.UndeclaredIdentifier, KatLangErrorCode.UnforwardableParameter)]
    [InlineData("C1(a, *p) = a\nC2(b, *q) = b\npublic K = {\n  p = 7\n  C1 + C2\n}\npublic X = 1",
        KatLangErrorCode.InvalidCollectingBinding, KatLangErrorCode.ParameterPropertyCollision)]
    public async Task MultipleInvalidities_KeepThePropertyPositionsDiagnosticOrder(string module, KatLangErrorCode first, KatLangErrorCode second)
    {
        var property = await SixRouteAgreement.OnEveryRouteAsync(AsProperty(module, "trace({0}X)"));
        var opened = await SixRouteAgreement.OnEveryRouteAsync(AsInlineOpen(module, "trace({0}X)"));
        Assert.Equal("parse", property.Kind);
        Assert.Equal("parse", opened.Kind);
        Assert.Equal([first.ToString(), second.ToString()], property.Errors.Select(error => error[..error.IndexOf(':')]));
        Assert.Equal(property.Errors, opened.Errors);
        Assert.Empty(opened.HostCalls);
    }

    // ── G. Diagnostic multiplicity follows the property position ──────────────────────────────

    [Fact]
    public async Task OneCachedModuleAtTwoImportSites_ReportsOnce_AtTheFirstSite_LikeTwoLoads()
    {
        var module = InvalidModules[0].Text;
        const string opened = $"A = {{\n  open '{Url}'\n  X\n}}\nB = {{\n  open '{Url}'\n  X\n}}\nA + B";
        const string loaded = $"A = {{\n  M = load('{Url}')\n  M.X\n}}\nB = {{\n  M = load('{Url}')\n  M.X\n}}\nA + B";

        var viaOpen = await OnModuleRoutesAsync(EagerModuleRoutes, opened, (Url, module));
        var viaLoad = await OnModuleRoutesAsync(EagerModuleRoutes, loaded, (Url, module));

        // One fetch, one module declaration (Q-32 I-U), one report — at the first import site,
        // however many sites import it and whichever spelling they use.
        Assert.Single(viaLoad.Errors);
        Assert.Equal(
            [Describe(KatLangErrorCode.UnforwardableParameter, new SourceSpan(2, 8, 2, 8 + Url.Length + 2))],
            viaOpen.Errors);
        Assert.Equal(1, viaOpen.Fetches);
        Assert.Equal(1, viaLoad.Fetches);
    }

    [Fact]
    public async Task OneModuleOpenedTwiceInOneList_ReportsOnce_LikeTwoSiblingLoads()
    {
        var module = InvalidModules[0].Text;
        const string opened = $"open '{Url}', '{Url}'\n1";
        const string loaded = $"M1 = load('{Url}')\nM2 = load('{Url}')\nM1.X + M2.X";

        var viaOpen = await OnModuleRoutesAsync(EagerModuleRoutes, opened, (Url, module));
        var viaLoad = await OnModuleRoutesAsync(EagerModuleRoutes, loaded, (Url, module));

        Assert.Single(viaLoad.Errors);
        Assert.Equal([Describe(KatLangErrorCode.UnforwardableParameter, LiteralSpan(opened, "open '"))], viaOpen.Errors);
    }

    [Theory]
    // read through aliases and members from outside the target
    [InlineData("open {\n  N(y) = y\n  public P(x) = N\n  public X = 1\n}\nA = X\nB = A\nX + A + B")]
    // nested open inside an open target
    [InlineData("open {\n  open {\n    N(y) = y\n    public P(x) = N\n    public X = 1\n  }\n  public Y = X + 1\n}\nY")]
    // an open target inside a property inside an open target
    [InlineData("open {\n  public M = {\n    open {\n      N(y) = y\n      public P(x) = N\n      public X = 1\n    }\n    public V = X\n  }\n}\nM.V")]
    // an open target inside a clause branch inside an open target
    [InlineData("open {\n  G(0) = {\n    open {\n      N(y) = y\n      public P(x) = N\n      public X = 1\n    }\n    X\n  }\n  G(n) = n\n  public K = G(0)\n}\nK")]
    // an open target inside a clause branch at the root (no load: eager), never selected
    [InlineData("F(0) = 0\nF(n) = {\n  open {\n    N(y) = y\n    public P(x) = N\n    public X = 1\n  }\n  X\n}\nF(0)")]
    // several targets, one invalid
    [InlineData("open { public A1 = 1 }, {\n  N(y) = y\n  public P(x) = N\n  public X = 1\n}\nA1")]
    // duplicate providers of X, never read
    [InlineData("open {\n  N(y) = y\n  public P(x) = N\n  public X = 1\n}, {\n  public X = 2\n}\n1")]
    public async Task EveryOpenTargetShape_ReportsTheVerdictExactlyOnce(string source)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", observation.Kind);
        Assert.Equal([Describe(KatLangErrorCode.UnforwardableParameter, SpanOf(source, "public P(x) = N", "N"))], CodesAndSpans(observation));
    }

    [Theory]
    [InlineData("open {\n  open {\n    N(y) = y\n    public P(y) = N\n    public X = 1\n  }\n  public Y = X + P(4)\n}\nY", "5")]
    [InlineData("open {\n  public N(y) = y\n}\nA = N\nP(y) = A\nP(5)", "5")]
    [InlineData("open {\n  N(y) = y\n  public A = N\n  public P(y) = A\n}\nP(6)", "6")]
    [InlineData("W = {\n  open {\n    public N(y) = y\n  }\n  A = N\n  public P(y) = A\n}\nW.P(3)", "3")]
    [InlineData("open {\n  N(y) = y\n  M(z) = z\n  public P = N + M\n}\nP(5, 6)", "11")]
    [InlineData("open {\n  N(y) = y\n  public P(y) = N\n  public X = 1\n}, {\n  public X = 2\n}\nP(4)", "4")]
    public async Task ValidOpenTargetShapes_KeepTheirValues(string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal(("ok", expected), (observation.Kind, observation.Value));
    }

    // ── H. Both open-target walks, from host-built trees ──────────────────────────────────────

    /// <summary>
    /// A host-built open target <c>{ N(y) = y ⏎ P(x) = N }</c>: P's bare forwarding cannot supply
    /// N's <c>y</c>.
    /// </summary>
    private static Expr.AlgorithmExpr InvalidHostBuiltTarget()
    {
        var n = new Algorithm.User(null, [new CaptureParameterPattern("y")], [], [], [new Expr.Resolve("y")]) { HasExplicitParameterList = true };
        var p = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Resolve("N")]) { HasExplicitParameterList = true };
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("N", n), new Property("P", p)], [new Expr.Num(0)]));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void BothOpenTargetWalks_ReportIntoTheCallersSink(bool familyOwned)
    {
        // The resolver walks open targets from two owners: a user algorithm's own opens, and a
        // clause family's own opens. The parser never gives a family opens of its own (an open
        // written in a clause body is branch-owned, MOD-05), so the second walk is reachable only
        // from a host-built tree — and it reports exactly like the first.
        var target = InvalidHostBuiltTarget();
        var branch = new CondBranch(new Pattern.Bind("k"), new Algorithm.User(null, [], [], [], [new Expr.Resolve("k")]));
        Algorithm owner = familyOwned
            ? new Algorithm.Conditional(null, [target], [branch])
            : new Algorithm.User(null, [], [target], [], [new Expr.Num(1)]);
        var root = new Algorithm.User(null, [], [], [new Property("F", owner)], [new Expr.Num(0)]);
        var (detected, detectionDiagnostics) = ParameterDetector.Detect(root);
        Assert.Empty(detectionDiagnostics);

        var diagnostics = new DiagnosticBag();
        ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics);

        var error = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.UnforwardableParameter, error.Code);
        Assert.Contains("'N' is forwarded by name here, but its parameter 'y'", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HostBuiltSingletonSignature_AlsoReportsInsideAnOpenTarget()
    {
        // Written singleton sequence patterns are parser-rejected before the resolver, but a
        // structurally safe host tree can expose this fifth code from the shared signature
        // reporter. Reporting must follow the same sink rule, rather than a four-code whitelist.
        var n = new Algorithm.User(null,
            [new SequenceValueParameterPattern([new CaptureParameterPattern("x")])], [], [], [new Expr.Param("x")])
        {
            HasExplicitParameterList = true,
        };
        var k = new Algorithm.User(null, [], [], [], [new Expr.Binary(BinaryOp.Add, new Expr.Resolve("N"), new Expr.Num(1))]);
        var target = new Algorithm.User(null, [], [], [new Property("N", n), new Property("K", k)], [new Expr.Num(0)]);
        var root = new Algorithm.User(null, [], [new Expr.AlgorithmExpr(target)], [], [new Expr.Num(0)]);
        Assert.Null(AstStructuralPreflight.Check(root, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive));

        var diagnostics = new DiagnosticBag();
        ImplicitArgumentResolver.ResolvePrevalidated(root, diagnostics: diagnostics);

        var error = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.SingletonSequencePattern, error.Code);
        Assert.Contains("sequence pattern with exactly one non-collecting item", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SharedOpenTargetDag_ReportsOnceLikeTheSharedPropertyBody()
    {
        Algorithm target = InvalidHostBuiltTarget().Algorithm;
        // Distinct wrappers at each edge retain one shared target, including a nested diamond.
        for (var level = 0; level < 4; level++)
            target = new Algorithm.User(null, [], [new Expr.AlgorithmExpr(target), new Expr.AlgorithmExpr(target)], [], [new Expr.Num(0)]);

        foreach (var openPosition in new[] { false, true })
        {
            var root = new Algorithm.User(null, [],
                openPosition ? [new Expr.AlgorithmExpr(target), new Expr.AlgorithmExpr(target)] : [],
                openPosition ? [] : [new Property("A", target), new Property("B", target)],
                [new Expr.Num(0)]);
            var (detected, detectionDiagnostics) = ParameterDetector.Detect(root);
            Assert.Empty(detectionDiagnostics);
            var diagnostics = new DiagnosticBag();
            ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics);
            Assert.Equal(DiagnosticCode.UnforwardableParameter, Assert.Single(diagnostics).Code);
        }
    }

    [Fact]
    public async Task AliasOutsideTheTarget_IsJudgedAtItsOwnRow()
    {
        // The alias normalizes to the opened N; the bare-forwarding verdict belongs to the root's
        // closed P(x) — reported there, once, exactly as before X-48 was fixed.
        const string source = "open {\n  public N(y) = y\n}\nA = N\nP(x) = A\nP(5)";
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal([Describe(KatLangErrorCode.UnforwardableParameter, SpanOf(source, "P(x) = A", "A"))], CodesAndSpans(observation));
    }
}
