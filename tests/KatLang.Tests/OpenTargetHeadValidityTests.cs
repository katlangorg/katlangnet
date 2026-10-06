using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Constitution PV-11 (MOD-02, MOD-03, RES-09): open-target validity is decided statically for
/// EVERY written target, whatever its head — not only for name-headed paths.
/// <para>
/// An open target is an open form ALL the way down (Lean <c>resolveAlgForOpen</c> recurses through
/// a dotted path's receiver): the HEAD of the receiver chain must itself name an algorithm — a
/// name, a <c>{ … }</c> block, or a <c>load</c> module — and every dotted step must select a public
/// member of its receiver. The parser used to check only the OUTER node, so <c>open 5.N</c>,
/// <c>open F(1).N</c> or <c>open (A, B).N</c> were accepted; the static resolution described
/// failures of name-headed paths only, so a block- or module-headed path with a missing or
/// private step (<c>open { … }.Nope</c>, <c>open load(u).Shwn</c>) was silently dropped and the
/// names only it could provide were promoted to implicit parameters. The evaluators resolve every
/// target of a level as soon as a lookup consults it, so such a program failed at run time, after
/// effects, and only when some lookup happened to reach the level — or ran with a changed
/// signature. Every static consumer now reads the ONE decomposition
/// <c>AstHelpers.OpenTargetHead</c>: the parser's form check, the static resolution and its
/// diagnostic, parameter detection, and dependency analysis — which also charged a VALID
/// block-headed provider as if it provided nothing (the RES-09 half pinned at the end).
/// </para>
/// </summary>
public class OpenTargetHeadValidityTests
{
    [Fact]
    public void SharedDecomposition_PreservesHeadIdentity_Order_AndArgumentBearingBoundary()
    {
        var head = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], OutputBundle.Empty));
        var first = new Expr.DotCall(head, "S", null);
        var path = new Expr.DotCall(first, "T", null);
        Assert.Same(head, path.OpenTargetHead());
        Assert.Same(head, path.OpenTargetHead(out var steps));
        Assert.Equal(["S", "T"], steps);

        // An explicit empty call is still a call. It must not be flattened into a static path.
        var call = new Expr.DotCall(first, "Called", OutputBundle.Empty);
        var afterCall = new Expr.DotCall(call, "Leaf", null);
        Assert.Same(call, afterCall.OpenTargetHead());
        Assert.Same(call, afterCall.OpenTargetHead(out steps));
        Assert.Equal(["Leaf"], steps);
        Assert.Same(head, head.OpenTargetHead(out steps));
        Assert.Empty(steps);
    }

    [Theory]
    [InlineData("{ public S = { public X = 5 } }.S", "{ public S = { public X = 7 } }.S")]
    [InlineData("{ public S = { public X = 5 } }.S", "{ public S = { public X = 5 } }.S")]
    [InlineData("{ public S = { public T = { public X = 5 } } }.S.T", "{ public S = { public T = { public X = 7 } } }.S.T")]
    [InlineData("({ public S = { public X = 5 } }).S", "(({ public S = { public X = 7 } }.S))")]
    public async Task InlineHeadedPaths_AreDistinctProviders_InEitherOrder(string first, string second)
    {
        // The old dedup splitter sent both targets to the bounded renderer, producing the
        // same key `{...}.S`. The second provider vanished before ambiguity or lookup. Two
        // written blocks are two providers (Q-19 D-I), so a WRITTEN `X` both provide is the
        // static ambiguity (Q-29 A-U) in either order, and a lookup only evaluation decides
        // (a fallback on a parameter receiver) is the evaluators' run-time ambiguity.
        foreach (var targets in new[] { $"{first}, {second}", $"{second}, {first}" })
        {
            await AssertStaticAmbiguity($"open {targets}\nX", new SourceSpan(2, 1, 2, 2));
            await AssertFivePaths($"K(q) = {{\n    open {targets}\n    q.X\n}}\nK(10)", KatLangErrorCode.AmbiguousOpen);
        }
    }

    [Theory]
    [InlineData("public Y = 5")]
    [InlineData("X = 5")]
    public async Task InlineHeadedPaths_KeepMembersFoundOnlyInTheLaterProvider(string firstMember)
    {
        var first = $"{{ public S = {{ {firstMember} }} }}.S";
        const string second = "{ public S = { public X = 7 } }.S";
        foreach (var targets in new[] { $"{first}, {second}", $"{second}, {first}" })
            await AssertFivePaths($"open {targets}\nX", null, 7);
    }

    [Fact]
    public async Task NamedPaths_StillDeduplicateByCompleteName()
        => await AssertFivePaths("open Lib.S.T, (Lib.S).T\nLib = { public S = { public T = { public X = 7 } } }\nX", null, 7);

    /// <summary>
    /// Q-19 D-I (decided 2026-10-06): two module-headed paths into ONE module reach one
    /// declaration — one provider, never an ambiguity; paths into two modules (two canonical
    /// URLs) stay two providers.
    /// </summary>
    [Theory]
    [InlineData("lib.kat", false)]
    [InlineData("other.kat", true)]
    public async Task ModuleHeadedPaths_CountProvidersByModule(string secondFile, bool twoProviders)
    {
        var options = ModuleOptions(
            (ModuleUrl, "public S = { public T = { public X = 5 } }"),
            ("https://mods.test/other.kat", "public S = { public T = { public X = 7 } }"));
        var source = $"open load('{ModuleUrl}').S.T, load('https://mods.test/{secondFile}').S.T\nX";
        if (twoProviders)
            await AssertStaticAmbiguity(source, new SourceSpan(2, 1, 2, 2), options);
        else
            await AssertFivePaths(source, null, 5, options);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DeepModuleProvider_SettlesAtItsOpeningLevel_AndParticipatesInAmbiguity(bool competing)
    {
        var options = ModuleOptions((ModuleUrl, "public S = { public T = { public X(v) = 5 } }"));
        var targets = (competing ? "Lib, " : "") + $"load('{ModuleUrl}').S.T";
        // The module provider settles at Y's own open level. Its member is read through a
        // fallback on a parameter receiver — a lookup evaluation decides — so the competing
        // level is the evaluators' run-time ambiguity, which charges nothing (Y stays exported).
        var source = $"Outer(p) = {{\n open Lib\n Lib = {{ public X(v) = p }}\n public Y = {{\n open {targets}\n K(q) = q.X\n K(10)\n }}\n 1\n}}\nOuter.Y";
        var parsed = await Parser.ParseAsync(source, options);
        Assert.Empty(parsed.Diagnostics);
        var y = parsed.Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single(p => p.Name == "Y");
        Assert.Equal(PropertyExposure.Exported, y.Exposure);
        await AssertFivePaths(source, competing ? KatLangErrorCode.AmbiguousOpen : null, 5, options);

        // A WRITTEN X that the competing level provides twice is the static ambiguity (Q-29 A-U).
        if (competing)
        {
            var writtenOptions = ModuleOptions((ModuleUrl, "public S = { public T = { public X = 5 } }"));
            var written = $"Outer(p) = {{\n open Lib\n Lib = {{ public X = p }}\n public Y = {{\n open {targets}\n X\n }}\n 1\n}}\nOuter.Y";
            await AssertStaticAmbiguity(written, new SourceSpan(6, 2, 6, 3), writtenOptions);
        }
    }

    private static async Task AssertFivePaths(
        string source, KatLangErrorCode? error, int value = 0, RunOptions? options = null)
    {
        void Engine(RunResult result)
        {
            if (error is { } code)
                Assert.Equal(code, Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors).Code);
            else
                Assert.Equal((Decimal128)value, Assert.IsType<Result.Atom>(Assert.IsType<RunResult.Success>(result).Value).Value);
        }

        options ??= new RunOptions();
        // Module acquisition is async-only; its evaluator still takes the sync path here.
        Engine(options.DownloadCode is null ? KatLangEngine.Run(source, options)
            : await KatLangEngine.RunAsync(source, options));
        Engine(await KatLangEngine.RunAsync(source, new RunOptions
        {
            DownloadCode = options.DownloadCode,
            AllowedHosts = options.AllowedHosts,
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("forceAsync", async (_, _) =>
            {
                await Task.Yield();
                return new Result.Atom(0);
            })),
        }));
        var parsed = await Parser.ParseAsync(source, options);
        Assert.Empty(parsed.Diagnostics);
        var expression = new Expr.AlgorithmExpr(parsed.Root);
        void Raw(EvalResult<Evaluator.CountedResult> result)
        {
            if (error is { } code)
            {
                Assert.True(result.IsError);
                Assert.Equal(code, KatLangError.FromEvalError(result.Error).Code);
            }
            else
            {
                Assert.False(result.IsError);
                Assert.Equal((Decimal128)value, Assert.IsType<Result.Atom>(result.Value.Value).Value);
            }
        }

        Raw(Evaluator.RunCountedObserved(expression, enableOptimizations: false).Result);
        Raw(Evaluator.RunCountedObserved(expression, enableOptimizations: true).Result);
        Raw((await Evaluator.RunCountedObservedAsync(expression,
            zeroArgPropertyResultCache: new KatLang.Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache())).Result);
    }

    /// <summary>
    /// Q-29 A-U (decided 2026-10-06): a WRITTEN name two different providers supply is invalid
    /// source — the engines' <see cref="RunResult.ParseFailure"/> and the parse's one diagnostic,
    /// <see cref="DiagnosticCode.AmbiguousOpen"/> at the written occurrence (public
    /// <see cref="KatLangErrorCode.AmbiguousOpen"/>), on the sync and async engines alike.
    /// </summary>
    private static async Task AssertStaticAmbiguity(string source, SourceSpan at, RunOptions? options = null)
    {
        options ??= new RunOptions();
        var parsed = await Parser.ParseAsync(source, options);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code);
        Assert.Equal(at, diagnostic.Span);

        var engine = options.DownloadCode is null ? KatLangEngine.Run(source, options) : await KatLangEngine.RunAsync(source, options);
        var error = Assert.Single(Assert.IsType<RunResult.ParseFailure>(engine).Errors);
        Assert.Equal(KatLangErrorCode.AmbiguousOpen, error.Code);
        Assert.Equal(at, error.Span);
        var asyncEngine = await KatLangEngine.RunAsync(source, options);
        Assert.Equal(KatLangErrorCode.AmbiguousOpen, Assert.Single(Assert.IsType<RunResult.ParseFailure>(asyncEngine).Errors).Code);
    }

    private const string ModuleUrl = "https://mods.test/lib.kat";

    private static Diagnostic SingleDiagnostic(string source)
        => Assert.Single(SourceProvenance.ParseAllowingDiagnostics(source).Diagnostics);

    private static RunOptions ModuleOptions(params (string Url, string Source)[] modules)
    {
        var files = modules.ToDictionary(module => module.Url, module => module.Source, StringComparer.Ordinal);
        return new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (url, _) => files.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : throw new InvalidOperationException($"404: {url}"),
        };
    }

    // ── MOD-02: the head of a dotted target must itself be an open form ─────

    [Theory]
    // head source, the kind the diagnostic names, supporting declarations
    [InlineData("5", "num", "")]
    [InlineData("true", "boolLiteral", "")]
    [InlineData("()", "empty sequence", "")]
    [InlineData("F(1)", "call", "F(x) = x\n")]
    [InlineData("[A]", "listLiteral", "A = { public N = 1 }\n")]
    [InlineData("(A + B)", "binary", "A = 1\nB = 2\n")]
    [InlineData("(A:0)", "index", "A = 1, 2\n")]
    [InlineData("(-A)", "unary", "A = 1\n")]
    [InlineData("('https://mods.test/lib.kat')", "stringLiteral", "")]
    public void DottedTarget_WithANonAlgorithmHead_IsBadOpenForm_ExactlyLikeTheBareHead(
        string head, string kind, string declarations)
    {
        var expected = $"Invalid open form: '{kind}' is not allowed in open declarations.";

        // The bare head, and the same head under one and two dotted steps: one verdict, one
        // message, one report at the head (never a second one for the enclosing path).
        foreach (var target in new[] { head, head + ".N", head + ".N.M" })
        {
            var source = $"open {target}\n{declarations}1";
            var diagnostic = SingleDiagnostic(source);
            Assert.Equal(DiagnosticCode.BadOpenForm, diagnostic.Code);
            Assert.Equal(expected, diagnostic.Message);
            Assert.Equal(new SourceSpan(1, 6, 1, 6 + head.Length), diagnostic.Span);
            Assert.Equal(
                KatLangErrorCode.BadOpenForm,
                Assert.Single(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source)).Errors).Code);
        }
    }

    [Theory]
    [InlineData("(A, B)")]
    [InlineData("(A, B).N")]
    [InlineData("(A, B).N.M")]
    public void CapturedHead_IsTheCapturedValueDiagnostic_AtTheCapture(string target)
    {
        var diagnostic = SingleDiagnostic($"open {target}\nA = {{ public N = {{ public Z = 3 }} }}\nB = 1\n1");
        Assert.Equal(DiagnosticCode.BadOpenForm, diagnostic.Code);
        Assert.Equal(Parser.CapturedOpenTargetDiagnostic, diagnostic.Message);
        Assert.Equal(new SourceSpan(1, 6, 1, 12), diagnostic.Span);
    }

    [Fact]
    public void BadHead_FailsBeforeEvaluation_WhetherOrNotALookupConsultsTheLevel()
    {
        // The re-baseline witness: the evaluator resolved `5.N` only when `Y` fell through to
        // the opens — after `trace(2)` ran — and `F(false)` alone succeeded. Now nothing runs.
        const string consulted = "Lib = { public Y = 7 }\nF(c) = {\n    open 5.N, Lib\n    if(c, Y + 0, 0)\n}\nF(false), trace(2), F(true)";
        const string neverConsulted = "Lib = { public Y = 7 }\nF(c) = {\n    open 5.N, Lib\n    if(c, Y + 0, 0)\n}\nF(false)";
        foreach (var source in new[] { consulted, neverConsulted })
        {
            var calls = new List<string>();
            var options = new RunOptions
            {
                HostOperations = HostOperations.Create(
                    HostOperation.Create("trace", (args, _) => { calls.Add("trace"); return args[0]; }, "x")),
            };
            var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
            Assert.Equal(KatLangErrorCode.BadOpenForm, Assert.Single(failure.Errors).Code);
            Assert.Empty(calls);
        }
    }

    // ── MOD-03: an inline-headed path resolves statically like a name-headed one ──

    [Theory]
    // block-headed target, its name-headed twin (declared as `Lib`), the step the message names
    [InlineData("{ public X = 1 }.Nope", "Lib.Nope", "{ public X = 1 }",
        "'{...}.Nope' cannot be opened because '{...}' has no property named 'Nope'.",
        "'Lib.Nope' cannot be opened because 'Lib' has no property named 'Nope'.")]
    [InlineData("{ S = { public Q = 3 } }.S", "Lib.S", "{ S = { public Q = 3 } }",
        "'{...}.S' cannot be opened because property 'S' of '{...}' is not public; an open path selects public members only.",
        "'Lib.S' cannot be opened because property 'S' of 'Lib' is not public; an open path selects public members only.")]
    [InlineData("{ public S = { public T = 1 } }.S.Nope", "Lib.S.Nope", "{ public S = { public T = 1 } }",
        "'{...}.S.Nope' cannot be opened because '{...}.S' has no property named 'Nope'.",
        "'Lib.S.Nope' cannot be opened because 'Lib.S' has no property named 'Nope'.")]
    [InlineData("{ public F(0) = {\n    public X = 1\n    0\n}\npublic F(n) = n }.F.X", "Lib.F.X", "{ public F(0) = {\n    public X = 1\n    0\n}\npublic F(n) = n }",
        "'{...}.F.X' cannot be opened because 'X' is declared only inside a conditional branch of '{...}.F', and a clause family exposes no members.",
        "'Lib.F.X' cannot be opened because 'X' is declared only inside a conditional branch of 'Lib.F', and a clause family exposes no members.")]
    public void BlockHeadedTarget_ThatResolvesToNothing_IsRefusedLikeItsNameHeadedTwin(
        string blockTarget, string namedTarget, string library, string blockMessage, string namedMessage)
    {
        var blockDiagnostic = SingleDiagnostic($"open {blockTarget}\n1");
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, blockDiagnostic.Code);
        Assert.Equal(blockMessage, blockDiagnostic.Message);
        Assert.Equal(1, blockDiagnostic.Span!.Value.Start.Line);
        Assert.Equal(6, blockDiagnostic.Span!.Value.Start.Column);

        var namedDiagnostic = SingleDiagnostic($"open {namedTarget}\nLib = {library}\n1");
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, namedDiagnostic.Code);
        Assert.Equal(namedMessage, namedDiagnostic.Message);
    }

    [Fact]
    public void BlockHeadedTarget_ThatResolvesToNothing_NoLongerPromotesTheNamesItWouldProvide()
    {
        // The re-baseline witness `i1`: `X` became A's implicit parameter and `A(5)` ran as 5.
        const string source = "A = {\n    open { public X = 1 }.Nope\n    X\n}\nA(5)";
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, SingleDiagnostic(source).Code);
        Assert.Equal(
            KatLangErrorCode.UnresolvedOpenTarget,
            Assert.Single(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source)).Errors).Code);
    }

    [Theory]
    [InlineData("Shwn", "'{...}.Shwn' cannot be opened because '{...}' has no property named 'Shwn'.")]
    [InlineData("Hidden", "'{...}.Hidden' cannot be opened because property 'Hidden' of '{...}' is not public; an open path selects public members only.")]
    public async Task ModuleHeadedTarget_ThatResolvesToNothing_IsRefusedLikeANamedModule(string step, string message)
    {
        const string module = "public Show = 42\nHidden = { public Q = 1 }";
        var options = ModuleOptions((ModuleUrl, module));

        // The realistic typo: written inline it used to promote `Show` silently, while the
        // same module bound to a name was already refused.
        var inline = await Parser.ParseAsync($"A = {{\n    open load('{ModuleUrl}').{step}\n    Show\n}}\nA(5)", options);
        var inlineDiagnostic = Assert.Single(inline.Diagnostics);
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, inlineDiagnostic.Code);
        Assert.Equal(message, inlineDiagnostic.Message);
        // The whole written target `load('…').step`, in this document's coordinates.
        Assert.Equal(new SourceSpan(2, 10, 2, 44 + step.Length), inlineDiagnostic.Span);

        var named = await Parser.ParseAsync($"Lib = load('{ModuleUrl}')\nA = {{\n    open Lib.{step}\n    Show\n}}\nA(5)", options);
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, Assert.Single(named.Diagnostics).Code);
    }

    // ── Legal inline-headed targets are unchanged, and open never evaluates ──

    [Theory]
    [InlineData("open { public S = { public Q = 3 } }.S\nQ", "3")]
    [InlineData("open { public S = { public T = { public Q = 4 } } }.S.T\nQ", "4")]
    // A parameterized intermediate block is navigated by identity (MOD-04): its output row
    // makes `q` the block's own parameter, and the self-contained `S` still opens.
    [InlineData("open { public S = { public Q = 3 }\n    q + 1 }.S\nQ", "3")]
    // The name-headed twin decides the same.
    [InlineData("open Lib.S\nLib = { public S = { public Q = 3 } }\nQ", "3")]
    public void BlockHeadedTarget_ThatResolves_IsAccepted(string source, string display)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(display, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Fact]
    public async Task ModuleHeadedTarget_ThatResolves_IsAccepted()
    {
        var options = ModuleOptions((ModuleUrl, "public Sub = { public Q = 9 }"));
        var result = await KatLangEngine.RunAsync($"A = {{\n    open load('{ModuleUrl}').Sub\n    Q\n}}\nA", options);
        Assert.Equal("9", Assert.IsType<RunResult.Success>(result).ToDisplayString());
    }

    [Fact]
    public void OpenValidation_NeitherEvaluatesNorActivatesTheTarget()
    {
        // The block's own output row would call the host; opening a member of it never
        // evaluates the block (MOD-04), and static validation evaluates nothing at all.
        var calls = new List<string>();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("tick", (_, _) => { calls.Add("tick"); return new Result.Atom(1); })),
        };
        var result = KatLangEngine.Run("open { public S = { public Q = 3 }\n    tick() }.S\nQ", options);
        Assert.Equal("3", Assert.IsType<RunResult.Success>(result).ToDisplayString());
        Assert.Empty(calls);

        var refused = KatLangEngine.Run("open { public S = { public Q = 3 }\n    tick() }.Nope\n1", options);
        Assert.Equal(KatLangErrorCode.UnresolvedOpenTarget, Assert.Single(Assert.IsType<RunResult.ParseFailure>(refused).Errors).Code);
        Assert.Empty(calls);
    }

    // ── RES-09: dependency analysis settles an inline-headed provider where the evaluator reads it ──

    [Theory]
    // The bare inline block and the name-headed path already charged exactly what the evaluator
    // reads; the block-headed path was charged as if it provided nothing, so `X` escaped to the
    // enclosing `open Lib`, `Y` was classified local-only, and `Outer.Y` failed.
    [InlineData("open { public S = { public X = 5 } }.S")]
    [InlineData("open { public S = { public T = { public X = 5 } } }.S.T")]
    [InlineData("open { public X = 5 }")]
    [InlineData("open T.S\n        T = { public S = { public X = 5 } }")]
    public void InlineHeadedProvider_IsSettledAtItsOwnLevel_NeverChargedToAnEnclosingOpen(string innerOpen)
    {
        var source = $"Outer(p) = {{\n    open Lib\n    Lib = {{ public X = p }}\n    public Y = {{\n        {innerOpen}\n        X\n    }}\n    1\n}}\nOuter.Y";
        var parsed = SourceProvenance.ParseValid(source);
        var y = parsed.Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single(p => p.Name == "Y");
        Assert.Equal(PropertyExposure.Exported, y.Exposure);
        Assert.Equal("5", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Theory]
    [InlineData("open Lib, { public S = { public X = 5 } }.S")]
    [InlineData("open { public S = { public X = 5 } }.S, Lib")]
    [InlineData("open Lib, { public S = { public T = { public X = 5 } } }.S.T")]
    [InlineData("open { public S = { public T = { public X = 5 } } }.S.T, Lib")]
    public void InlineHeadedProvider_TakesPartInOpenAmbiguity_InEitherOrder(string innerOpen)
    {
        // Two providers at one level select nothing (ambiguousOpen), so dependency analysis
        // charges nothing — it used to see Lib as the sole provider and refuse `Outer.Y` as
        // local-only instead of reaching the true ambiguity. The read is a fallback on a
        // parameter receiver, a lookup only evaluation decides, so the ambiguity is the
        // evaluators' (a WRITTEN X there is the static ambiguity, Q-29 A-U — pinned below).
        var source = $"Outer(p) = {{\n    Lib = {{ public X(v) = p }}\n    public Y = {{\n        {innerOpen}\n        K(q) = q.X\n        K(10)\n    }}\n    1\n}}\nOuter.Y";
        var parsed = SourceProvenance.ParseValid(source);
        var y = parsed.Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single(p => p.Name == "Y");
        Assert.Equal(PropertyExposure.Exported, y.Exposure);
        Assert.Equal(
            KatLangErrorCode.AmbiguousOpen,
            Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors).Code);

        var written = $"Outer(p) = {{\n    Lib = {{ public X = p }}\n    public Y = {{\n        {innerOpen}\n        X\n    }}\n    1\n}}\nOuter.Y";
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(written));
        Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code);
        Assert.Equal(new SourceSpan(5, 9, 5, 10), diagnostic.Span);
    }
}
