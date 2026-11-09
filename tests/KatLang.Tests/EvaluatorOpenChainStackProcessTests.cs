using System.Diagnostics;
using System.Numerics;
using System.Text;
using KatLang.Tests.AsyncEvaluation;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// Process-isolated regression for the open-target navigation backstop (HOME F1 review, November
/// 2026, follow-ups H30/H31/H35, continuing audit finding F1). Resolving <c>open A.N.N…N</c> recurses
/// once per link of the TARGET (<c>Evaluator.ResolveAlgForOpen</c> ↔
/// <c>Evaluator.ResolveOpenPropAccess</c>), and a lexical lookup that consults the opens reaches that
/// navigation from wherever evaluation has got to. Before the fix the pair had no stack probe: the one
/// open-route probe (<c>OpenStructure</c>) runs only after the per-link descent returns, so a valid,
/// in-budget program (<see cref="Program"/>, 95 links at <c>R(27)</c> on the 1.5 MiB Debug CLI main
/// thread) killed the host process with <c>Stack overflow.</c> — 83 repetitions of the pair in the
/// trace. <c>ResolveOpenPropAccess</c> now probes the runtime's reserve once per link, before it
/// recurses, and refuses with <see cref="EvalError.EvaluationStackExhausted"/>.
///
/// <para>A process death cannot be observed in-process, so each sweep runs in a child
/// (<see cref="SubprocessProbe"/>) that writes a success marker; a pass needs the marker AND exit
/// code 0. Programs are parsed on a large thread and evaluated on exact-size small threads
/// (<see cref="AstStructuralDepthProcessTests.RunOnThreadWithStack(int, Action)"/>), so only the
/// evaluator is under test. The crash window is narrow (one or two recursion depths per stack size
/// and configuration), so the sweeps cover every recursion depth across the refusal frontier at
/// several stack sizes. A run is the ordinary result or a structured refusal from
/// the evaluator's stack/depth backstops or, on deferred routes, a compile-time stack refusal;
/// each sweep must see both, and where a refusal fires is never
/// pinned (Q-09a).</para>
/// </summary>
public class EvaluatorOpenChainStackProcessTests(ITestOutputHelper output)
{
    private const string ProbeChildEnvironment = "KATLANG_OPEN_CHAIN_STACK_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_OPEN_CHAIN_STACK_PROBE_MARKER_FILE";
    private const string ProbeStressEnvironment = "KATLANG_OPEN_CHAIN_STACK_PROBE_STRESS";
    private const string ProbeSuccessMarker = "katlang-open-chain-stack-ok";

    internal const string ModuleUrl = "https://katlang.org/open-chain/m.kat";

    private const int LargeStack = 64 * 1024 * 1024;

    /// <summary>The stack sizes the evaluator sweeps run on: below, at and above the documented 1 MiB minimum (the CLI main thread is 1.5 MiB).</summary>
    internal static readonly int[] StackSizes = [768 * 1024, 1024 * 1024, 1280 * 1024, 1536 * 1024];

    /// <summary>Open-target dot-link counts: one link through a near-ceiling dotted target. The one-name-open control is separate.</summary>
    internal static readonly int[] LinkCounts = [1, 32, 64, 95];

    /// <summary>The highest recursion depth swept; the measured Debug and Release frontiers lie within this window.</summary>
    internal const int MaxRecursion = 40;

    internal static string OpenTarget(int links)
        => "A" + new StringBuilder().Insert(0, ".N", links);

    /// <summary>
    /// The reproducer family: <c>A</c> whose public <c>N</c> is <c>A</c> itself, a body that opens
    /// <c>A.N…N</c> (<paramref name="links"/> links) and reads <c>V</c> through it, and <c>R(n)</c>,
    /// which selects that body <paramref name="n"/> recursion levels deep, each level eight braces
    /// deep. <c>Program(95, 27)</c> is the reproducer from the review, byte for byte apart from the
    /// link count it spells.
    /// </summary>
    internal static string Program(int links, int n)
        => "Id(x) = x\nA = {\n  public N = A\n  public V = 7\n}\nB(z) = {\n  open " + OpenTarget(links)
            + "\n  V + z\n}\nR(0) = B(0)\nR(k) = {{{{{{{{Id(R(k - 1))}}}}}}}}\nR(" + n + ")\n";

    /// <summary>
    /// Deferred-compile routes. Where the open is written: <c>branch</c> — in a load-bearing
    /// conditional branch, which compiles on the evaluator's stack and then resolves the open;
    /// <c>module</c> — in the module's own text, read through the module from the branch. Where the
    /// recursion is: <c>outer</c> — the branch is SELECTED <c>n</c> levels deep, so the compile and
    /// the open navigation share the depth (the compile's own probes usually refuse first);
    /// <c>inner</c> — the branch compiles near the top and a recursion INSIDE the compiled branch
    /// reaches the open <c>n</c> levels deeper, so the navigation itself meets the stack edge in code
    /// the deferred materialization produced.
    /// </summary>
    internal static readonly string[] DeferredRoutes = ["branch-outer", "module-outer", "branch-inner", "module-inner"];

    internal const int DeferredLinks = 90;

    internal static string DeferredSource(string route, int n)
    {
        var inner = route.EndsWith("-inner", StringComparison.Ordinal);
        var load = $"    M = load('{ModuleUrl}')\n";
        var read = route.StartsWith("branch", StringComparison.Ordinal)
            ? "{\n        open " + OpenTarget(DeferredLinks) + "\n        V + M.Z\n    }"
            : "M.W";
        var body = inner
            ? load + $"    G(0) = {read}\n    G(k) = {{{{{{{{{{{{{{{{Id(G(k - 1))}}}}}}}}}}}}}}}}\n    G({n})\n"
            : load + $"    {read}\n";
        return "Id(x) = x\nA = {\n  public N = A\n  public V = 7\n}\nF(0) = 0\nF(1) = {\n" + body
            + "}\nR(0) = F(1)\nR(k) = {{{{{{{{Id(R(k - 1))}}}}}}}}\nR(" + (inner ? 1 : n) + ")\n";
    }

    internal static string DeferredModule(string route)
        => route.StartsWith("branch", StringComparison.Ordinal)
            ? "public Z = 0"
            : "A = {\n  public N = A\n  public V = 7\n}\npublic W = {\n  open " + OpenTarget(DeferredLinks) + "\n  V\n}";

    // ── Parent tests ────────────────────────────────────────────────────────

    [Fact]
    public void Reproducer_ParsesCleanly_AndEvaluatesOnALargeStack()
    {
        foreach (var links in LinkCounts)
        {
            var result = AstStructuralDepthProcessTests.RunOnThreadWithStack(LargeStack, () => KatLangEngine.Run(Program(links, 3)));
            Assert.Equal([7m], Assert.IsType<RunResult.Success>(result).Atoms);
            AstStructuralDepthProcessTests.RunOnThreadWithStack(LargeStack, () => SourceProvenance.ParseValid(Program(links, MaxRecursion)));
        }

        foreach (var route in DeferredRoutes)
        {
            var options = new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult(DeferredModule(route)) };
            var result = AstStructuralDepthProcessTests.RunOnThreadWithStack(
                LargeStack, () => KatLangEngine.RunAsync(DeferredSource(route, 3), options).GetAwaiter().GetResult());
            Assert.Equal([7m], Assert.IsType<RunResult.Success>(result).Atoms);
            AstStructuralDepthProcessTests.RunOnThreadWithStack(LargeStack, () => SourceProvenance.ParseValid(DeferredModule(route)));
        }
    }

    [Fact]
    public async Task OpenChain_NeverCrashes_AcrossRecursionDepth_AndStackSize()
        => await RunProbeChild(nameof(OpenChainWindow_ProbeChild));

    [Fact]
    public async Task OpenChain_NeverCrashes_InsideADeferredCompile()
        => await RunProbeChild(nameof(DeferredOpenChain_ProbeChild));

    [Fact]
    public async Task OneNameOpenChain_Control_IsStructured()
        => await RunProbeChild(nameof(OneNameOpenChain_ProbeChild));

    /// <summary>
    /// The stress variant: the window sweep and the <c>inner</c> deferred sweeps while every processor spins a busy loop (half of
    /// them allocating, to provoke collections), so JIT tier-up and GC pauses perturb frame sizes
    /// and timing during the sweep.
    /// </summary>
    [Fact]
    public async Task OpenChain_NeverCrashes_UnderCpuLoad()
        => await RunProbeChild(nameof(OpenChainWindow_ProbeChild), stress: true);

    // ── Children ────────────────────────────────────────────────────────────

    /// <summary>
    /// The reproducer family on every swept stack size, recursion depth and link count, through the
    /// synchronous evaluator and the async twin (pass-through cache: it completes synchronously, so
    /// the whole chain consumes the same thread). Under stress, the <c>inner</c> deferred sweeps run too.
    /// </summary>
    [Fact]
    public void OpenChainWindow_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;
        ReportEvaluatorAssembly();

        using var load = Environment.GetEnvironmentVariable(ProbeStressEnvironment) == "1" ? CpuLoad.Start() : null;

        var asts = AstStructuralDepthProcessTests.RunOnThreadWithStack(LargeStack, () =>
            (from links in LinkCounts
             from n in Enumerable.Range(0, MaxRecursion + 1)
             select (Links: links, N: n, Ast: (Expr)new Expr.AlgorithmExpr(SourceProvenance.ParseValid(Program(links, n)).Root)))
            .ToList());

        foreach (var stack in StackSizes)
        {
            foreach (var links in LinkCounts)
            {
                var sweep = new Tally($"{stack / 1024} KiB / {links} links");
                foreach (var (_, n, ast) in asts.Where(a => a.Links == links))
                {
                    AstStructuralDepthProcessTests.RunOnThreadWithStack(stack, () =>
                    {
                        sweep.Record(n, "sync", Evaluator.RunFlat(ast));
                        var twin = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache());
                        Assert.True(twin.IsCompleted, "the pass-through twin path must complete synchronously");
                        sweep.RecordTwin(n, twin.GetAwaiter().GetResult());
                    });
                }

                sweep.AssertOutcomes();
            }
        }

        if (load is not null)
        {
            RunDeferredSweeps(innerOnly: true);
            Console.WriteLine($"cpu load: {load.Threads} spinning threads, {load.Collections} gen-0 collections during the sweep");
        }

        WriteProbeMarker();
    }

    /// <summary>The deferred-compile routes: the branch compiles on the evaluator's stack and then navigates the open there.</summary>
    [Fact]
    public void DeferredOpenChain_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;
        ReportEvaluatorAssembly();

        RunDeferredSweeps();
        WriteProbeMarker();
    }

    /// <summary>
    /// The control: a chain of ONE-NAME opens (<see cref="ExposureOpenChainComplexityTests.NestedOwnerChain"/>,
    /// every owner opening the next), which never recurses through the open-target navigation; its
    /// one open-route probe (<c>OpenStructure</c>) already protected it before the fix. On shrinking
    /// stacks it completes with its large-stack value or refuses structured.
    /// </summary>
    [Fact]
    public void OneNameOpenChain_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;
        ReportEvaluatorAssembly();

        var source = ExposureOpenChainComplexityTests.NestedOwnerChain(100);
        var ast = AstStructuralDepthProcessTests.RunOnThreadWithStack(
            LargeStack, () => (Expr)new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        var reference = AstStructuralDepthProcessTests.RunOnThreadWithStack(LargeStack, () => Evaluator.RunFlat(ast));
        if (!reference.IsOk)
            Assert.Fail($"the control must evaluate on a large stack: {reference.Error}");

        // Stacks far below the documented minimum can refuse before any positioned frame, so no span is required here.
        var sweep = new Tally("one-name open chain", reference.Value, requireSpan: false);
        // The top is 2048 KiB, not 1536 KiB (owner-approved calibration, November 2026). In Debug the
        // chain first completes at about 1536 KiB, give or take a few KiB per process (measured at 4 KiB
        // resolution), so a top sample of exactly 1536 KiB had no headroom: whenever a fresh process's
        // threshold landed a few KiB above it, every sample refused and the sweep failed with "no run
        // evaluated" (about 10-15% of runs). The extra samples only add completions; the low end still
        // refuses, and both outcomes remain required.
        for (var kib = 128; kib <= 2048; kib += 32)
            AstStructuralDepthProcessTests.RunOnThreadWithStack(kib * 1024, () => sweep.Record(kib, "sync", Evaluator.RunFlat(ast)));

        // Diagnostic only, never asserted: where this process first completed.
        Console.WriteLine($"one-name open chain: first completion at {sweep.FirstCompletion?.ToString() ?? "none"} KiB");
        sweep.AssertOutcomes();
        WriteProbeMarker();
    }

    private static void RunDeferredSweeps(bool innerOnly = false)
    {
        foreach (var route in DeferredRoutes.Where(r => !innerOnly || r.EndsWith("-inner", StringComparison.Ordinal)))
        {
            var module = DeferredModule(route);
            foreach (var stack in StackSizes)
            {
                var sweep = new Tally($"deferred {route} / {stack / 1024} KiB", allowDeferredCompileRefusal: true);
                for (var n = 0; n <= MaxRecursion; n++)
                {
                    // A fresh parse per run: every run compiles a fresh region on the thread under test.
                    var root = Prepare(DeferredSource(route, n), module);
                    var outcome = AstStructuralDepthProcessTests.RunOnThreadWithStack(stack, () =>
                        Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), HostOperations.Create(), null, null, default).GetAwaiter().GetResult());
                    sweep.Record(n, "deferred", outcome);
                }

                sweep.AssertOutcomes();
            }
        }
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    /// <summary>Parses on a large thread (eager elaboration is never the subject) and checks the tree holds a deferred region.</summary>
    private static Algorithm Prepare(string source, string module)
    {
        var options = new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult(module) };
        var parsed = AstStructuralDepthProcessTests.RunOnThreadWithStack(
            LargeStack, () => SourceProvenance.ParseValidAsync(source, options).GetAwaiter().GetResult());
        Assert.True(HasDeferredRegion(parsed.Root), "the branch must be a deferred module region");
        return parsed.Root;
    }

    private static bool HasDeferredRegion(Algorithm root)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node))
                continue;
            if (node is Algorithm { DeferredRegion: not null })
                return true;
            for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++)
                pending.Push(child);
        }

        return false;
    }

    /// <summary>Checks a sweep's expected value and route-specific refusals without pinning their boundary.</summary>
    private sealed class Tally(
        string label, IReadOnlyList<Decimal128>? expected = null, bool requireSpan = true,
        bool allowDeferredCompileRefusal = false)
    {
        private readonly IReadOnlyList<Decimal128> _expected = expected ?? [7m];
        private int _completions;
        private int _refusals;
        private readonly List<string> _log = [];

        /// <summary>The first point (in recording order) whose run completed; diagnostic only.</summary>
        public int? FirstCompletion { get; private set; }

        public void Record(int point, string route, EvalResult<IReadOnlyList<Decimal128>> outcome)
        {
            if (outcome.IsOk)
            {
                Assert.Equal(_expected, outcome.Value);
                FirstCompletion ??= point;
                _completions++;
                _log.Add($"{point}{route[0]}:ok");
                return;
            }

            var error = outcome.Error;
            // The message is built only on failure: rendering an error recurses, and this runs on the thread under test.
            if (error.Code is not (KatLangErrorCode.EvaluationStackExhausted or KatLangErrorCode.EvaluationDepthExceeded)
                && !(allowDeferredCompileRefusal && error.Code is KatLangErrorCode.ModuleElaborationStackExhausted or KatLangErrorCode.ModuleNestingTooDeep))
                Assert.Fail($"{label} @{point} ({route}): unexpected outcome {error.Code}: {error}");
            if (error.Code == KatLangErrorCode.EvaluationStackExhausted)
                Assert.True(error.IsResourceLimit);
            if (requireSpan)
                Assert.NotNull(error.Span);
            _refusals++;
            _log.Add($"{point}{route[0]}:{error.Code}@{error.Span}");
        }

        public void RecordTwin(int point, EvalResult<Evaluator.CountedResult> outcome)
        {
            if (outcome.IsOk)
            {
                Assert.True(outcome.Value.Value.TryToHostAtoms(int.MaxValue, out var atoms));
                Assert.Equal(_expected, atoms);
                _completions++;
                _log.Add($"{point}t:ok");
                return;
            }

            var category = SemanticExplorerHarness.ErrorCategory(outcome.Error);
            if (category is not ("evaluationStackExhausted" or "evaluationDepthExceeded"))
                Assert.Fail($"{label} @{point} (twin): unexpected outcome {outcome.Error}");
            _refusals++;
            _log.Add($"{point}t:{category}");
        }

        public void AssertOutcomes()
        {
            Console.WriteLine($"{label}: {string.Join(" ", _log)}");
            Assert.True(_completions > 0, $"{label}: no run evaluated\n{string.Join(" ", _log)}");
            Assert.True(_refusals > 0, $"{label}: no run was refused; the sweep no longer crosses the frontier\n{string.Join(" ", _log)}");
        }
    }

    /// <summary>
    /// <see cref="Environment.ProcessorCount"/> background threads spinning until disposed; every
    /// other one allocates short-lived arrays so gen-0 collections run during the sweep.
    /// </summary>
    private sealed class CpuLoad : IDisposable
    {
        private readonly CancellationTokenSource _stop = new();
        private readonly List<Thread> _threads = [];
        private readonly int _collectionsAtStart = GC.CollectionCount(0);

        public int Threads => _threads.Count;

        public int Collections => GC.CollectionCount(0) - _collectionsAtStart;

        public static CpuLoad Start()
        {
            var load = new CpuLoad();
            var token = load._stop.Token;
            for (var i = 0; i < Environment.ProcessorCount; i++)
            {
                var allocate = i % 2 == 1;
                var thread = new Thread(() =>
                {
                    var sink = 0L;
                    while (!token.IsCancellationRequested)
                    {
                        if (allocate)
                            sink += new byte[1024 + (int)(sink & 4095)].Length;
                        else
                            sink = unchecked(sink * 31 + 7);
                    }

                    GC.KeepAlive(sink);
                }) { IsBackground = true };
                thread.Start();
                load._threads.Add(thread);
            }

            return load;
        }

        public void Dispose()
        {
            _stop.Cancel();
            foreach (var thread in _threads)
                thread.Join();
            _stop.Dispose();
        }
    }

    private async Task RunProbeChild(string childTestName, bool stress = false)
    {
        var assemblyPath = typeof(EvaluatorOpenChainStackProcessTests).Assembly.Location;
        var testName = typeof(EvaluatorOpenChainStackProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(Path.GetTempPath(), $"katlang-open-chain-stack-probe-{Guid.NewGuid():N}.txt");

        var startInfo = SubprocessProbe.StartInfo(assemblyPath, [testName]);
        startInfo.Environment[ProbeChildEnvironment] = "1";
        startInfo.Environment[ProbeMarkerFileEnvironment] = markerFile;
        if (stress)
            startInfo.Environment[ProbeStressEnvironment] = "1";

        try
        {
            using var process = new Process { StartInfo = startInfo };
            process.Start();
            var stdoutTask = process.StandardOutput.ReadToEndAsync();
            var stderrTask = process.StandardError.ReadToEndAsync();
            await process.WaitForExitAsync();
            var stdout = await stdoutTask;
            var combined = stdout + Environment.NewLine + await stderrTask;

            // Exit code first: its message carries the child's whole output, crash frames included.
            Assert.True(process.ExitCode == 0, $"Probe child '{childTestName}' exited with {process.ExitCode}.{Environment.NewLine}{combined}");
            Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
            Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
            Assert.True(File.Exists(markerFile), $"Probe child '{childTestName}' did not write its success marker.{Environment.NewLine}{combined}");
            Assert.Equal(ProbeSuccessMarker, (await File.ReadAllTextAsync(markerFile)).Trim());
            var expectedAssembly = EvaluatorAssemblyIdentity();
            Assert.Contains(expectedAssembly, stdout.Split('\n').Select(line => line.TrimEnd('\r')));
            output.WriteLine(expectedAssembly);
        }
        finally
        {
            try { File.Delete(markerFile); }
            catch { /* best-effort cleanup */ }
        }
    }

    private static void ReportEvaluatorAssembly() => Console.WriteLine(EvaluatorAssemblyIdentity());

    /// <summary>Identifies the loaded evaluator assembly in both the parent and the child.</summary>
    private static string EvaluatorAssemblyIdentity()
    {
        var assembly = typeof(Evaluator).Assembly;
        return $"evaluator assembly: {assembly.Location} mvid {assembly.ManifestModule.ModuleVersionId}";
    }

    private static void WriteProbeMarker()
    {
        var markerFile = Environment.GetEnvironmentVariable(ProbeMarkerFileEnvironment);
        Assert.False(string.IsNullOrWhiteSpace(markerFile));
        File.WriteAllText(markerFile!, ProbeSuccessMarker);
    }
}
