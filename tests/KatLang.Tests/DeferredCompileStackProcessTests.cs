using System.Diagnostics;
using System.Numerics;
using System.Text;
using KatLang.TestInfrastructure;

namespace KatLang.Tests;

/// <summary>
/// Process-isolated regression for audit finding F1 (resource/cancellation boundary audit, November
/// 2026): a DEFERRED compilation runs on the evaluator's own stack. A conditional branch whose modules
/// load on demand is compiled when it is selected (<c>DeferredModuleRegion.CompileLoadedBody</c>), and
/// its modules parse inside <c>ModuleLoader.FetchAndSpliceAsync</c>, so when nothing suspends the
/// parser, the post-parse validation walk and the elaboration passes all start wherever evaluation had
/// got to. Their structural gates assume a nearly empty stack; before the fix, a valid, in-budget
/// program (<see cref="Reproducer"/>) killed the host process with <c>0xC00000FD</c> inside
/// <c>ImplicitArgumentResolver</c> on a 1 MiB thread. Every front-end recursion cycle now probes the
/// runtime's stack reserve per level (<c>FrontEndStack</c>) and fails structured.
///
/// <para>A process death cannot be observed in-process, so each sweep runs in a child
/// (<see cref="SubprocessProbe"/>) that writes a success marker; a pass needs the marker AND exit
/// code 0. Every sweep requires a compile and allows only the structured outcomes in
/// <see cref="AllowedRefusals"/>. Sweeps of deep trees also require a compile refusal without
/// pinning where it occurs (Q-09a). The flat comparison chain adds width to a single node, so an
/// evaluator stack check can stop smaller threads before compilation and leave no compile refusal
/// in the sweep. The compile-refusal assertion also allows for a larger stack supplied by glibc
/// (<see cref="ThreadStackSize"/>). The crash and outcome checks apply at every size.</para>
/// </summary>
public class DeferredCompileStackProcessTests
{
    private const string ProbeChildEnvironment = "KATLANG_DEFERRED_COMPILE_STACK_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_DEFERRED_COMPILE_STACK_PROBE_MARKER_FILE";
    private const string ProbeRouteEnvironment = "KATLANG_DEFERRED_COMPILE_STACK_PROBE_ROUTE";
    private const string ProbeShapeEnvironment = "KATLANG_DEFERRED_COMPILE_STACK_PROBE_SHAPE";
    private const string ProbeSuccessMarker = "katlang-deferred-compile-stack-ok";

    internal const string ModuleUrl = "https://katlang.org/lazy/m.kat";

    private const int LargeStack = 64 * 1024 * 1024;
    private const int OneMiB = 1024 * 1024;

    /// <summary>
    /// The audit's reproducer: a 90-level block body behind a load-bearing branch, selected
    /// <c>n</c> levels deep in evaluator recursion. Before the fix, <c>R(23)</c> killed a Release
    /// process on a 1 MiB thread and <c>R(15)</c> to <c>R(17)</c> a Debug one.
    /// </summary>
    internal static string Reproducer(int n) => Source("block", 90, n, "download");

    /// <summary>The only outcomes a run may have besides its ordinary result.</summary>
    internal static readonly KatLangErrorCode[] AllowedRefusals =
    [
        KatLangErrorCode.EvaluationStackExhausted,
        KatLangErrorCode.EvaluationDepthExceeded,
        KatLangErrorCode.ModuleElaborationStackExhausted,
        KatLangErrorCode.ModuleNestingTooDeep,
    ];

    /// <summary>
    /// Shapes admitted by the structural gates: nested blocks, braces, lists, groups, calls,
    /// builtin calls, clause families, operator / dot / selector chains (which build deep trees
    /// during iterative parsing), a wide flat comparison chain, prefix operators, interpolation
    /// holes, opens of blocks and clause-head patterns.
    /// </summary>
    internal static readonly (string Shape, int Depth)[] Shapes =
    [
        ("block", 90), ("brace", 90), ("list", 120), ("group", 90), ("call", 100), ("ifc", 80),
        ("family", 40), ("plus", 250), ("dot", 95), ("cmp", 250), ("index", 250), ("neg", 150),
        ("interp", 40), ("openb", 40), ("pattern", 80),
    ];

    /// <summary>
    /// <c>download</c>: the selected branch downloads its module synchronously, so the module
    /// parses AND the branch compiles on the evaluator's stack. <c>cached</c>: an eager
    /// <c>Eager = load(u)</c> already cached the module, so the branch compiles with no download at
    /// all. <c>module-text</c>: the depth is in the module's own text, so the nested parse and its
    /// validation walk are under test (chain shapes included).
    /// </summary>
    internal static readonly string[] Routes = ["download", "cached", "module-text"];

    public static TheoryData<string, string> SweepCases()
    {
        var cases = new TheoryData<string, string>();
        foreach (var route in Routes)
            foreach (var (shape, _) in Shapes)
                cases.Add(route, shape);
        return cases;
    }

    internal static string Deep(string shape, int depth, string inner)
    {
        var e = inner;
        switch (shape)
        {
            case "block": for (var i = 0; i < depth; i++) e = "{ P = " + e + "\nP + 0 }"; return e;
            case "brace": return new string('{', depth) + inner + new string('}', depth);
            case "list": return new string('[', depth) + inner + new string(']', depth);
            case "group": for (var i = 0; i < depth; i++) e = "(" + e + ", 0)"; return e;
            case "call": for (var i = 0; i < depth; i++) e = "Id(" + e + ")"; return e;
            case "ifc": for (var i = 0; i < depth; i++) e = "if(true, " + e + ", 0)"; return e;
            case "family": for (var i = 0; i < depth; i++) e = "{ G(0) = " + e + "\nG(x) = x\nG(0) }"; return e;
            case "plus": return Chain(inner, " + 0", depth);
            case "dot": return Chain(inner, ".Id", depth);
            case "cmp": return Chain(inner, " == 0", depth);
            case "index": return Chain(inner, "[0]", depth);
            case "neg": for (var i = 0; i < depth; i++) e = "-" + e; return e;
            case "interp": for (var i = 0; i < depth; i++) e = "\"{" + e + "}\""; return e;
            case "openb": for (var i = 0; i < depth; i++) e = "{ open { public W = " + e + " }\nW }"; return e;
            case "pattern":
            {
                var pattern = "x0";
                var argument = "1";
                for (var i = 1; i <= depth; i++)
                {
                    pattern = "(" + pattern + ", y" + i + ")";
                    argument = "(" + argument + ", 2)";
                }

                return "{ H(" + pattern + ") = x0\nH(" + argument + ") } + " + inner;
            }

            default:
                throw new ArgumentOutOfRangeException(nameof(shape), shape, "unknown shape");
        }

        static string Chain(string head, string link, int count)
        {
            var sb = new StringBuilder(head);
            for (var i = 0; i < count; i++)
                sb.Append(link);
            return sb.ToString();
        }
    }

    /// <summary>
    /// The program: <c>F(1)</c>'s body loads the module and reads <c>N.V</c> through the deep shape
    /// (or plainly, when the depth is in the module text), and <c>R(n)</c> selects that branch
    /// <paramref name="n"/> invocation levels deep.
    /// </summary>
    internal static string Source(string shape, int depth, int n, string route)
    {
        var body = route == "module-text" ? "N.V" : Deep(shape, depth, "N.V");
        var head = route == "cached" ? $"Eager = load('{ModuleUrl}')\n" : "";
        return $"{head}Id(x) = x\nF(0) = 0\nF(1) = {{\n    N = load('{ModuleUrl}')\n    {body}\n}}\nR(0) = F(1)\nR(k) = Id(R(k - 1))\nR({n})\n";
    }

    /// <summary>
    /// A chain of <paramref name="modules"/> modules where the exposure pass, alone among the probed
    /// walks, stacks every module's nesting on the one before it. Each pass elaborates a spliced module
    /// root once per compile, at the first site that reaches it. The branch and every module but the
    /// last hold <c>open load(next)</c> AND a property that reads <c>next</c> through its own
    /// <c>load</c> nested <paramref name="depth"/> blocks deep. The detector and the resolver visit
    /// opens before properties, so they reach each module at its shallow open and their stack stays
    /// about one module's nesting. The exposure pass visits properties first, so it reaches each
    /// module at the deep site and its stack grows with the whole chain. On a stack that the earlier
    /// passes leave, the exposure walk's own and dependency-summary probes stop the compile.
    /// Every level is an ordinary
    /// block, so the program evaluates with default limits.
    /// </summary>
    internal static (string Source, IReadOnlyDictionary<string, string> Modules) ModuleChain(int modules, int depth)
    {
        static string Url(int i) => $"https://katlang.org/chain/{i}.kat";
        string Level(int next, string declaration, string read)
        {
            var e = $"{{ M = load('{Url(next)}')\nM.{read} }}";
            for (var i = 0; i < depth; i++)
                e = "{ public P = " + e + "\nP }";
            return $"open load('{Url(next)}')\n{declaration} = {e}\n";
        }

        var texts = new Dictionary<string, string>(StringComparer.Ordinal);
        for (var i = 0; i < modules; i++)
            texts[Url(i)] = i == modules - 1 ? $"public V{i} = 7" : Level(i + 1, $"public V{i}", $"V{i + 1}");
        var branch = Level(0, "A", "V0").Replace("\n", "\n    ", StringComparison.Ordinal);
        var source = $"Id(x) = x\nF(0) = 0\nF(1) = {{\n    {branch}A\n}}\nR(0) = F(1)\nR(k) = Id(R(k - 1))\nR(0)\n";
        return (source, texts);
    }

    /// <summary>The module text: a plain value, or (module-text route) the deep shape with its own helper.</summary>
    internal static string Module(string shape, int depth, string route)
        => route == "module-text" ? "Id(x) = x\npublic V = " + Deep(shape, depth, "7") : "public V = 7";

    // ── Parent tests ────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(SweepCases))]
    public async Task DeferredCompile_NeverCrashes_AcrossThreadSizes(string route, string shape)
        => await RunProbeChild(nameof(ThreadSizeSweep_ProbeChild), route, shape);

    [Fact]
    public async Task DeferredCompile_NeverCrashes_AcrossEvaluatorDepth_OnOneMiB()
        => await RunProbeChild(nameof(EvaluatorWindow_ProbeChild));

    [Fact]
    public async Task PublicRoute_Reproducer_IsStructured_AndCompletesSynchronously()
        => await RunProbeChild(nameof(PublicRoute_ProbeChild));

    [Fact]
    public async Task RefusedCompile_IsRetryable_AndPublishesNothing()
        => await RunProbeChild(nameof(Retry_ProbeChild));

    [Fact]
    public async Task EagerFrontEnd_OnSmallThreads_IsStructured()
        => await RunProbeChild(nameof(EagerSmallThread_ProbeChild));

    [Fact]
    public async Task ExposurePass_OnSmallThreads_ProbesIndependentlyOfEarlierPasses()
        => await RunProbeChild(nameof(ExposurePass_ProbeChild));

    [Fact]
    public async Task ModuleChain_ExposureReachesModulesDeeper_NeverCrashes_AcrossThreadSizes()
        => await RunProbeChild(nameof(ModuleChainSweep_ProbeChild));

    [Fact]
    public async Task Reproducer_ParsesCleanly_AndEvaluatesOnALargeStack()
    {
        // Ties the sweeps to legal source: on a stack with room the reproducer is an ordinary
        // program with an ordinary value, through the public engine, synchronously.
        var (task, synchronous) = AstStructuralDepthProcessTests.RunOnThreadWithStack(LargeStack, () =>
        {
            var pending = KatLangEngine.RunAsync(Reproducer(5), Options("public V = 7"));
            return (pending, pending.IsCompleted);
        });
        Assert.True(synchronous, "a synchronously completing downloader must keep RunAsync synchronous");
        var success = Assert.IsType<RunResult.Success>(await task);
        Assert.Equal([7m], success.Atoms);
    }

    // ── Children ────────────────────────────────────────────────────────────

    /// <summary>
    /// One (route, shape): parse on a large thread and evaluate on the thread under test, so only
    /// the deferred compile (and the module parse it drives) is under test; a fresh parse per size,
    /// so every size compiles a fresh region. The compile starts near the top of the small thread
    /// (<c>R(0)</c>), and the sweep samples small stacks through sizes where the shape compiles.
    /// </summary>
    [Fact]
    public void ThreadSizeSweep_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        var route = Environment.GetEnvironmentVariable(ProbeRouteEnvironment)!;
        var shape = Environment.GetEnvironmentVariable(ProbeShapeEnvironment)!;
        var depth = Shapes.Single(s => s.Shape == shape).Depth;
        var source = Source(shape, depth, 0, route);
        var module = Module(shape, depth, route);

        // The large-stack run compiles the branch; its body may still meet the deterministic
        // invocation-depth limit (the `openb` family nests calls 40 levels), which every smaller
        // stack must then reach too, or stop earlier with a structured refusal.
        var reference = EvaluateOn(LargeStack, Prepare(source, module));
        Assert.True(reference.Materialized, $"{route}/{shape}: the branch must compile on a large stack: {Describe(reference.Outcome)}");
        Assert.True(reference.Outcome.IsOk || reference.Outcome.Error.Code == KatLangErrorCode.EvaluationDepthExceeded,
            $"{route}/{shape}: the program must evaluate on a large stack: {Describe(reference.Outcome)}");

        // Sweep the fixed range first, then take wider steps if compilation needs more room
        // (for example, a Debug nested module parse of a deep shape).
        var sweep = new SweepTally($"{route}/{shape}");
        for (var kib = 144; kib <= 688 || (!sweep.SawCompile && kib <= 4096); kib += kib < 688 ? 16 : 128)
        {
            var prepared = Prepare(source, module);
            var run = EvaluateOn(kib * 1024, prepared);
            sweep.Record(kib, run, reference.Outcome);
            if (route == "cached")
                Assert.Equal(0, prepared.DownloadsDuringEvaluation);
        }

        sweep.AssertOutcomes(requireCompileRefusal: shape != "cmp");
        WriteProbeMarker();
    }

    /// <summary>
    /// The evaluator window: on a 1 MiB thread, the branch is selected ever deeper in evaluator
    /// recursion, from the top of the stack past the evaluator's own backstop, for the reproducer
    /// and for a flat chain whose first recursive walk is after the parse.
    /// </summary>
    [Fact]
    public void EvaluatorWindow_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        foreach (var (route, shape) in new[] { ("download", "block"), ("cached", "plus"), ("module-text", "plus"), ("download", "list") })
        {
            var depth = Shapes.Single(s => s.Shape == shape).Depth;
            var module = Module(shape, depth, route);
            var sweep = new SweepTally($"evaluator window {route}/{shape}");
            for (var n = 0; n <= 72; n++)
            {
                var source = Source(shape, depth, n, route);
                EvalResult<IReadOnlyList<Decimal128>>? reference = n % 12 == 0 ? EvaluateOn(LargeStack, Prepare(source, module)).Outcome : (EvalResult<IReadOnlyList<Decimal128>>?)null;
                var run = EvaluateOn(OneMiB, Prepare(source, module));
                sweep.Record(n, run, reference);
            }

            sweep.AssertOutcomes();
        }

        WriteProbeMarker();
    }

    /// <summary>
    /// The public route: <see cref="KatLangEngine.RunAsync"/> parses AND evaluates on one 1 MiB
    /// thread with a synchronously completing downloader. The task is complete when the call returns
    /// (the synchronous-completion contract in-memory and WASM hosts rely on), every outcome is
    /// structured, a refusal is the module-elaboration stack error — an EvalFailure that is not a
    /// resource limit and not a clause non-match (the program's catch-all clause never answers) —
    /// and the same family on a plain <see cref="Task.Run(Func{Task})"/> thread is structured too.
    /// </summary>
    [Fact]
    public async Task PublicRoute_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        var options = Options("public V = 7");
        var refusals = 0;
        var compiles = 0;
        var log = new List<string>();
        var exact = true;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () =>
        {
            exact = ThreadStackSize.OfCurrentThread() is not { } actual || actual == OneMiB;
            for (var n = 0; n <= 40; n++)
            {
                foreach (var source in new[] { Reproducer(n), WithCatchAllClause(Reproducer(n)) })
                {
                    var pending = KatLangEngine.RunAsync(source, options);
                    Assert.True(pending.IsCompleted, $"R({n}): RunAsync with a synchronous downloader must complete synchronously");
                    switch (pending.GetAwaiter().GetResult())
                    {
                        case RunResult.Success success:
                            Assert.Equal([7m], success.Atoms);
                            compiles++;
                            log.Add($"{n}:ok");
                            break;

                        case RunResult.EvalFailure failure:
                            var error = Assert.Single(failure.Errors);
                            Assert.Contains(error.Code, AllowedRefusals);
                            log.Add($"{n}:{error.Code}");
                            if (FindRegion(failure.Root).IsMaterialized)
                                compiles++;
                            if (error.Code == KatLangErrorCode.ModuleElaborationStackExhausted)
                            {
                                refusals++;
                                Assert.False(error.IsResourceLimit, "a refused deferred compile is not a resource limit (Q-71)");
                                Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(WithoutContext(error.Source!));
                                Assert.Contains("not have enough stack left", error.Message, StringComparison.Ordinal);
                            }

                            break;

                        case var other:
                            Assert.Fail($"R({n}): unexpected run result {other.GetType().Name}");
                            break;
                    }
                }
            }
        });

        Console.WriteLine("public route: " + string.Join(" ", log));
        Assert.True(compiles > 0, "no public-route run compiled the branch; the sweep never reaches the other side of the frontier");
        Assert.True(refusals > 0 || !exact, "the public route never refused a deferred compile; the sweep no longer reaches the frontier");

        // A plain thread-pool thread: whatever stack the pool gives it, every outcome is structured.
        var poolSuccesses = 0;
        var poolRefusals = 0;
        for (var n = 0; n <= 80; n += 2)
        {
            var result = await Task.Run(() => KatLangEngine.RunAsync(Source("plus", 250, n, "download"), options));
            if (result is RunResult.Success success)
            {
                Assert.Equal([7m], success.Atoms);
                poolSuccesses++;
            }
            else
            {
                var failure = Assert.IsType<RunResult.EvalFailure>(result);
                Assert.Contains(Assert.Single(failure.Errors).Code, AllowedRefusals);
                poolRefusals++;
            }
        }

        Assert.True(poolSuccesses > 0, "the pool-thread family never compiled the branch");
        Assert.True(poolRefusals > 0, "the pool-thread family never reached a stack or depth backstop");
        WriteProbeMarker();
    }

    /// <summary>
    /// A refused compile publishes nothing and leaves the loader as it was: the region is not
    /// materialized, the materialization gate is free, no module is in progress and the loader's
    /// walk context is restored; the SAME tree then compiles and evaluates on a large stack.
    /// </summary>
    [Fact]
    public void Retry_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        var exact = true;
        var retried = 0;
        foreach (var (route, shape) in new[] { ("download", "block"), ("cached", "call"), ("module-text", "plus") })
        {
            var depth = Shapes.Single(s => s.Shape == shape).Depth;
            var source = Source(shape, depth, 0, route);
            var module = Module(shape, depth, route);
            for (var kib = 144; kib <= 688; kib += 8)
            {
                var prepared = Prepare(source, module);
                var loader = prepared.Region.Loader;
                var walkContext = loader.WalkContext;
                var small = EvaluateOn(kib * 1024, prepared);
                exact &= small.ExactStack;
                if (!small.Outcome.IsOk)
                    Assert.Contains(small.Outcome.Error.Code, AllowedRefusals);
                if (small.Outcome.IsOk || small.Materialized)
                    continue;
                if (small.Outcome.Error.Code is not (KatLangErrorCode.ModuleElaborationStackExhausted or KatLangErrorCode.ModuleNestingTooDeep))
                    continue;

                Assert.False(prepared.Region.IsMaterialized);
                Assert.Equal(1, loader.MaterializationGate.CurrentCount);
                Assert.Equal(0, loader.InProgressModuleCount);
                Assert.Equal(walkContext, loader.WalkContext);

                var large = EvaluateOn(LargeStack, prepared);
                Assert.True(large.Outcome.IsOk, $"{route}/{shape}: the refused tree must compile on a large stack: {Describe(large.Outcome)}");
                Assert.True(prepared.Region.IsMaterialized);
                Assert.Equal(1, loader.MaterializationGate.CurrentCount);
                Assert.Equal(0, loader.InProgressModuleCount);
                Assert.Equal(walkContext, loader.WalkContext);
                retried++;
                break;
            }
        }

        Assert.True(retried == 3 || !exact, $"only {retried} of 3 families refused a compile on any swept size");
        WriteProbeMarker();
    }

    /// <summary>
    /// The eager front end on threads smaller than the documented minimum, with no modules: every
    /// public entry point returns a structured result and no internal exception type escapes —
    /// <see cref="Parser.Parse(string)"/>, <see cref="Parser.ParseAsync"/>,
    /// <see cref="KatLangEngine.Run"/> and <see cref="KatLangEngine.RunAsync"/> — including a load
    /// the synchronous front end cannot perform.
    /// </summary>
    [Fact]
    public void EagerSmallThread_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        DiagnosticCode[] allowedParseCodes = [DiagnosticCode.NestingTooDeep, DiagnosticCode.ModuleElaborationStackExhausted];
        KatLangErrorCode[] allowedRunCodes =
        [
            KatLangErrorCode.NestingTooDeep, KatLangErrorCode.ModuleElaborationStackExhausted,
            KatLangErrorCode.EvaluationStackExhausted, KatLangErrorCode.EvaluationDepthExceeded,
        ];

        foreach (var (shape, depth) in new[] { ("plus", 250), ("block", 90), ("list", 120), ("index", 250), ("call", 100), ("pattern", 80) })
        {
            var source = "Id(x) = x\n" + Deep(shape, depth, "7") + "\n";
            var reference = AstStructuralDepthProcessTests.RunOnThreadWithStack(LargeStack, () => KatLangEngine.Run(source));
            var expected = Assert.IsType<RunResult.Success>(reference).Atoms;
            var refusals = 0;
            var clean = 0;
            var exact = true;
            for (var kib = 144; kib <= 688; kib += 16)
            {
                var requested = kib * 1024;
                AstStructuralDepthProcessTests.RunOnThreadWithStack(requested, () =>
                {
                    exact &= ThreadStackSize.OfCurrentThread() is not { } actual || actual == requested;
                    try
                    {
                        var parsed = Parser.Parse(source);
                        if (parsed.HasErrors)
                        {
                            Assert.All(parsed.Diagnostics.Where(static d => d.Severity == DiagnosticSeverity.Error),
                                error => Assert.Contains(error.Code, allowedParseCodes));
                            refusals++;
                        }
                        else
                        {
                            clean++;
                        }

                        var parsedAsync = Parser.ParseAsync(source);
                        Assert.True(parsedAsync.IsCompleted);
                        Assert.All(parsedAsync.GetAwaiter().GetResult().Diagnostics.Where(static d => d.Severity == DiagnosticSeverity.Error),
                            error => Assert.Contains(error.Code, allowedParseCodes));

                        AssertRun(KatLangEngine.Run(source));
                        var running = KatLangEngine.RunAsync(source);
                        Assert.True(running.IsCompleted);
                        AssertRun(running.GetAwaiter().GetResult());

                        // A load with no downloader: the synchronous front end reports it as unavailable.
                        var withLoad = $"N = load('{ModuleUrl}')\n" + source;
                        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(withLoad));
                    }
                    catch (Exception exception) when (exception is not Xunit.Sdk.XunitException)
                    {
                        Assert.Fail($"{shape} on {kib} KiB: {exception.GetType().FullName} escaped a public entry point: {exception.Message}");
                    }
                });
            }

            Assert.True(clean > 0, $"{shape}: no swept size parsed cleanly");
            Assert.True(refusals > 0 || !exact, $"{shape}: no swept size refused; the sweep no longer reaches the frontier");

            void AssertRun(RunResult result)
            {
                switch (result)
                {
                    case RunResult.Success success:
                        Assert.Equal(expected, success.Atoms);
                        break;
                    case RunResult.ParseFailure parseFailure:
                        Assert.All(parseFailure.Errors, error => Assert.Contains(error.Code, allowedRunCodes));
                        break;
                    case RunResult.EvalFailure evalFailure:
                        Assert.All(evalFailure.Errors, error => Assert.Contains(error.Code, allowedRunCodes));
                        break;
                    default:
                        Assert.Fail($"{shape}: unexpected run result {result.GetType().Name}");
                        break;
                }
            }
        }

        WriteProbeMarker();

    }

    /// <summary>
    /// Earlier, larger pass frames can refuse before exposure is reached. Run exposure alone on
    /// a legally parsed, completed tree, so no earlier pass's probe can stand in for the exposure
    /// pass's walk. That walk drives the dependency-summary collection at every scope, and both
    /// probe: removing the summary probes kills this child, while removing only the exposure
    /// file's probes does not, because the summary probes in the same recursion still refuse
    /// first (mutation-checked on 2026-11-08: every sweep shape in Debug, this block shape in Release).
    /// The internal pass propagates the control signal; the public conversion boundaries are
    /// exercised by the eager and deferred sweeps above.
    /// </summary>
    [Fact]
    public void ExposurePass_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        var source = Deep("block", 90, "7");
        var compiled = AstStructuralDepthProcessTests.RunOnThreadWithStack(
            LargeStack, () => SourceProvenance.ParseValid(source).Root);
        var successes = 0;
        var refusals = 0;
        var exact = true;
        for (var kib = 80; kib <= 688; kib += 8)
        {
            AstStructuralDepthProcessTests.RunOnThreadWithStack(kib * 1024, () =>
            {
                exact &= ThreadStackSize.OfCurrentThread() is not { } actual || actual == kib * 1024;
                try
                {
                    var exposed = PropertyExposureResolver.Resolve(compiled);
                    Assert.Equal(compiled.Output.Count, exposed.Output.Count);
                    Assert.Equal(compiled.Properties.Count, exposed.Properties.Count);
                    successes++;
                }
                catch (FrontEndStackExhaustedException)
                {
                    refusals++;
                }
            });
        }

        Assert.True(successes > 0, "the isolated exposure pass never completed");
        Assert.True(refusals > 0 || !exact, "the isolated exposure pass never reached its reserve probe");
        WriteProbeMarker();
    }

    /// <summary>
    /// The production-route witness for the exposure probes (<see cref="ModuleChain"/>): a deferred
    /// compile through the real loader and pipeline, where the exposure pass needs far more stack
    /// than any earlier probed walk. Below the frontier where the earlier passes refuse, there is a
    /// window that only the exposure walk's probes turn into a structured refusal: its own and the
    /// dependency-summary probes it drives per scope. Without the summary probes the child dies
    /// there with a stack overflow; the exposure file's own probes are not independently
    /// witnessed, since the summary probes refuse first. The sweep asserts only the
    /// allowed outcomes and that it saw both a refusal and a compile. It never pins where either
    /// one happens.
    /// </summary>
    [Fact]
    public void ModuleChainSweep_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        var (source, modules) = ModuleChain(modules: 12, depth: 22);
        string Download(string url) => modules[url];

        var reference = EvaluateOn(LargeStack, Prepare(source, Download));
        Assert.True(reference.Materialized, $"module chain: the branch must compile on a large stack: {Describe(reference.Outcome)}");
        Assert.True(reference.Outcome.IsOk, $"module chain: the program must evaluate on a large stack: {Describe(reference.Outcome)}");
        Assert.Equal([7m], reference.Outcome.Value);

        var sweep = new SweepTally("module chain");
        for (var kib = 144; kib <= 688 || (!sweep.SawCompile && kib <= 4096); kib += kib < 688 ? 16 : 128)
            sweep.Record(kib, EvaluateOn(kib * 1024, Prepare(source, Download)), reference.Outcome);

        sweep.AssertOutcomes();
        WriteProbeMarker();
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    /// <summary>A program of the family with a catch-all clause that would answer 99 if a refusal were a clause non-match.</summary>
    private static string WithCatchAllClause(string source)
        => source.Replace("R(0) = F(1)", "F(x) = 99\nR(0) = F(1)", StringComparison.Ordinal);

    private static EvalError WithoutContext(EvalError error)
        => error is EvalError.WithContext(_, var inner) ? WithoutContext(inner) : error;

    private static string Describe(EvalResult<IReadOnlyList<Decimal128>> outcome)
        => outcome.IsOk ? "ok " + string.Join(",", outcome.Value) : outcome.Error.ToString();

    private static RunOptions Options(string module)
        => new() { DownloadCode = (_, _) => ValueTask.FromResult(module) };

    private sealed class Prepared(Algorithm root, DeferredModuleRegion region, Func<int> downloads, int parsedDownloads)
    {
        public Algorithm Root { get; } = root;
        public DeferredModuleRegion Region { get; } = region;
        public int DownloadsDuringEvaluation => downloads() - parsedDownloads;
    }

    private readonly record struct Evaluation(EvalResult<IReadOnlyList<Decimal128>> Outcome, bool Materialized, bool ExactStack);

    /// <summary>Parses on a large thread, so eager elaboration is never the subject.</summary>
    private static Prepared Prepare(string source, string module)
        => Prepare(source, _ => module);

    private static Prepared Prepare(string source, Func<string, string> modules)
    {
        var downloads = 0;
        var options = new RunOptions
        {
            DownloadCode = (url, _) =>
            {
                Interlocked.Increment(ref downloads);
                return ValueTask.FromResult(modules(url));
            },
        };
        var parsed = AstStructuralDepthProcessTests.RunOnThreadWithStack(
            LargeStack, () => Parser.ParseAsync(source, options).GetAwaiter().GetResult());
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(static d => d.Message)));
        return new Prepared(parsed.Root, FindRegion(parsed.Root), () => Volatile.Read(ref downloads), Volatile.Read(ref downloads));
    }

    private static Evaluation EvaluateOn(int stackBytes, Prepared prepared)
        => AstStructuralDepthProcessTests.RunOnThreadWithStack(stackBytes, () =>
        {
            var exact = ThreadStackSize.OfCurrentThread() is not { } actual || actual == stackBytes;
            var outcome = Evaluator.RunFlatAsync(
                new Expr.AlgorithmExpr(prepared.Root), HostOperations.Create(), null, null, default).GetAwaiter().GetResult();
            return new Evaluation(outcome, prepared.Region.IsMaterialized, exact);
        });

    private static DeferredModuleRegion FindRegion(Algorithm root)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node))
                continue;
            if (node is Algorithm { DeferredRegion: { } region })
                return region;
            for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++)
                pending.Push(child);
        }

        throw new InvalidOperationException("The program has no deferred module region.");
    }

    /// <summary>
    /// Classifies a sweep's runs: a run is the ordinary result (equal to the large-stack reference
    /// when one is given) or one of <see cref="AllowedRefusals"/>; a refusal never published the
    /// region. A COMPILE is a run that materialized the region; a REFUSAL is a run whose deferred
    /// compile (or module parse) was refused.
    /// </summary>
    private sealed class SweepTally(string label)
    {
        private int _compiles;
        private int _refusals;
        private bool _exact = true;
        private readonly List<string> _log = [];

        public bool SawCompile => _compiles > 0;

        public void Record(int point, Evaluation run, EvalResult<IReadOnlyList<Decimal128>>? reference)
        {
            _exact &= run.ExactStack;
            if (run.Outcome.IsOk)
            {
                Assert.True(run.Materialized, $"{label} @{point}: a completed run must have compiled the branch");
                if (reference is { } expected && expected.IsOk)
                    Assert.Equal(expected.Value, run.Outcome.Value);
                _compiles++;
                _log.Add($"{point}:ok");
                return;
            }

            var code = run.Outcome.Error.Code;
            Assert.True(Array.IndexOf(AllowedRefusals, code) >= 0, $"{label} @{point}: unexpected outcome {code}: {run.Outcome.Error}");
            if (run.Materialized)
            {
                Assert.True(code is KatLangErrorCode.EvaluationStackExhausted or KatLangErrorCode.EvaluationDepthExceeded,
                    $"{label} @{point}: a published region cannot report {code}");
                _compiles++;
            }
            else if (code is KatLangErrorCode.ModuleElaborationStackExhausted or KatLangErrorCode.ModuleNestingTooDeep)
            {
                Assert.False(run.Outcome.Error.IsResourceLimit, $"{label} @{point}: a refused compile is not a resource limit");
                _refusals++;
            }

            _log.Add($"{point}:{(run.Materialized ? "compiled" : "unpublished")}:{code}");
        }

        public void AssertOutcomes(bool requireCompileRefusal = true)
        {
            Console.WriteLine($"{label}: {string.Join(" ", _log)}");
            Assert.True(_compiles > 0, $"{label}: no run compiled the branch\n{string.Join(" ", _log)}");
            if (requireCompileRefusal && _exact)
                Assert.True(_refusals > 0,
                    $"{label}: no run refused the compile; the sweep no longer crosses the frontier\n{string.Join(" ", _log)}");
        }
    }

    private static async Task RunProbeChild(string childTestName, string? route = null, string? shape = null)
    {
        var assemblyPath = typeof(DeferredCompileStackProcessTests).Assembly.Location;
        var testName = typeof(DeferredCompileStackProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(Path.GetTempPath(), $"katlang-deferred-compile-stack-probe-{Guid.NewGuid():N}.txt");

        var startInfo = SubprocessProbe.StartInfo(assemblyPath, [testName]);
        startInfo.Environment[ProbeChildEnvironment] = "1";
        startInfo.Environment[ProbeMarkerFileEnvironment] = markerFile;
        if (route is not null)
            startInfo.Environment[ProbeRouteEnvironment] = route;
        if (shape is not null)
            startInfo.Environment[ProbeShapeEnvironment] = shape;

        try
        {
            using var process = new Process { StartInfo = startInfo };
            process.Start();
            var stdoutTask = process.StandardOutput.ReadToEndAsync();
            var stderrTask = process.StandardError.ReadToEndAsync();
            await process.WaitForExitAsync();
            var combined = await stdoutTask + Environment.NewLine + await stderrTask;

            // Exit code first: its message carries the child's whole output, crash frames included.
            Assert.True(process.ExitCode == 0, $"Probe child '{childTestName}' ({route}/{shape}) exited with {process.ExitCode}.{Environment.NewLine}{combined}");
            Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
            Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
            Assert.True(File.Exists(markerFile), $"Probe child '{childTestName}' ({route}/{shape}) did not write its success marker.{Environment.NewLine}{combined}");
            Assert.Equal(ProbeSuccessMarker, (await File.ReadAllTextAsync(markerFile)).Trim());
        }
        finally
        {
            try { File.Delete(markerFile); }
            catch { /* best-effort cleanup */ }
        }
    }

    private static void WriteProbeMarker()
    {
        var markerFile = Environment.GetEnvironmentVariable(ProbeMarkerFileEnvironment);
        Assert.False(string.IsNullOrWhiteSpace(markerFile));
        File.WriteAllText(markerFile!, ProbeSuccessMarker);
    }
}
