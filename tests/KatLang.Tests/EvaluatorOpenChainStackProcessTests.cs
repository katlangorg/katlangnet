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
/// pinned (Q-09a). Sweeps with async twin runs require their refusals per family (one link
/// count, one deferred route) across the stack sizes: since the 2026-11-14 stack hop the twin
/// refuses only at helper probes, at depths that depend on where its hops land
/// (<see cref="Tally.AssertCrossesTheFrontier"/>).</para>
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

    /// <summary>
    /// The highest recursion depth the window sweep covers. It is 48, not 40: on the 1536 KiB thread in
    /// Release the SYNCHRONOUS route still completed at depth 40 (its frontier lies near 42; measured on
    /// Windows x64, November 2026), so only the async twin refused there and the sync side had no
    /// headroom. Every measured Debug and Release frontier of both routes now lies inside the window.
    /// </summary>
    internal const int MaxRecursion = 48;

    /// <summary>The highest recursion depth the deferred sweeps cover; their measured frontiers are 22 or less.</summary>
    internal const int DeferredMaxRecursion = 40;

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

    /// <summary>
    /// The <c>inner</c> routes' stack sizes: <see cref="StackSizes"/> plus a contiguous band of
    /// 4 KiB steps from 1028 to 1152 KiB. With the <c>ResolveOpenPropAccess</c> probe removed, an
    /// <c>inner</c> run crashes only when the recursion inside the compiled branch leaves the open
    /// navigation a reserve that passed every earlier probe but cannot hold 90 links. One
    /// recursion level moves that point by a fixed amount of stack, so the crash window recurs
    /// with that period as the thread size grows. Measured on Windows x64 in November 2026: in
    /// Release the window is 10–14 KiB wide every ~82 KiB (for example 1000–1010 and 1082–1094 KiB,
    /// ±4 KiB between processes), which none of the four coarse sizes reaches; in Debug it is
    /// ~64 KiB wide every ~112 KiB. The band spans 128 KiB, more than either period, at a step
    /// below the narrowest window, so the mutation kills the child in both configurations.
    /// </summary>
    internal static readonly int[] InnerStackSizes =
        [.. StackSizes.Concat(Enumerable.Range(1, 32).Select(static i => (1024 + 4 * i) * 1024)).Distinct().Order()];

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
    /// synchronous evaluator and the async twin (pass-through cache: it starts on the same thread and,
    /// since the 2026-11-14 stack hop, continues on fresh thread-pool stacks where an invocation or
    /// row funnel finds the stack low). Under stress, the <c>inner</c> deferred sweeps run too.
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

        var sweepsByLinks = LinkCounts.ToDictionary(static links => links, static _ => new List<Tally>());
        foreach (var stack in StackSizes)
        {
            foreach (var links in LinkCounts)
            {
                var sweep = new Tally($"{stack / 1024} KiB / {links} links");
                sweepsByLinks[links].Add(sweep);
                foreach (var (_, n, ast) in asts.Where(a => a.Links == links))
                {
                    AstStructuralDepthProcessTests.RunOnThreadWithStack(stack, () =>
                    {
                        sweep.Record(n, "sync", Evaluator.RunFlat(ast));
                        // The twin starts on this thread and continues on a fresh thread-pool stack
                        // wherever an invocation or row funnel finds it low (StackHop), so it is
                        // awaited; the open navigation keeps its own probe on whichever stack it runs.
                        var twin = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache()).AsTask();
                        Assert.True(twin.Wait(TimeSpan.FromMinutes(5)), "the twin run did not complete");
                        sweep.RecordTwin(n, twin.Result);
                    });
                }

                sweep.AssertOutcomes(requireRefusal: false);
            }
        }

        foreach (var (links, sweeps) in sweepsByLinks)
            Tally.AssertCrossesTheFrontier($"{links} links", sweeps);

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

        RunDeferredSweeps(innerBand: true);
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

        // Every refusal carries a span except a ROOT-LEVEL one: on a stack far below the documented
        // minimum (about 140 KiB and less on Windows x64, both configurations, November 2026) the
        // pre-evaluation validation gate (`Evaluator.PreEvaluationValidationError`) runs out of reserve
        // while walking the whole program, before evaluation has entered any written expression, so
        // there is no written position to report (the node its walk had reached is where the host
        // stack ran short, not a cause). The observed entry point exposes the run's budget, which
        // proves the spanless refusal did no evaluation work at all.
        var sweep = new Tally("one-name open chain", reference.Value);
        // The top is 2048 KiB, not 1536 KiB (owner-approved calibration, November 2026). In Debug the
        // chain first completes at about 1536 KiB, give or take a few KiB per process (measured at 4 KiB
        // resolution), so a top sample of exactly 1536 KiB had no headroom: whenever a fresh process's
        // threshold landed a few KiB above it, every sample refused and the sweep failed with "no run
        // evaluated" (about 10-15% of runs). The extra samples only add completions; the low end still
        // refuses, and both outcomes remain required.
        for (var kib = 128; kib <= 2048; kib += 32)
            AstStructuralDepthProcessTests.RunOnThreadWithStack(kib * 1024, () =>
            {
                var (result, budget) = Evaluator.RunCountedObserved(ast);
                sweep.RecordObserved(kib, result, budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth);
            });

        // Diagnostic only, never asserted: where this process first completed.
        Console.WriteLine($"one-name open chain: first completion at {sweep.FirstCompletion?.ToString() ?? "none"} KiB, {sweep.RootLevelRefusals} root-level refusal(s)");
        sweep.AssertOutcomes();
        WriteProbeMarker();
    }

    private static void RunDeferredSweeps(bool innerOnly = false, bool innerBand = false)
    {
        foreach (var route in DeferredRoutes.Where(r => !innerOnly || r.EndsWith("-inner", StringComparison.Ordinal)))
        {
            var module = DeferredModule(route);
            var routeSweeps = new List<Tally>();
            foreach (var stack in innerBand && route.EndsWith("-inner", StringComparison.Ordinal) ? InnerStackSizes : StackSizes)
            {
                var sweep = new Tally($"deferred {route} / {stack / 1024} KiB", allowDeferredCompileRefusal: true);
                routeSweeps.Add(sweep);
                for (var n = 0; n <= DeferredMaxRecursion; n++)
                {
                    // A fresh parse per run: every run compiles a fresh region on the thread under test.
                    var root = Prepare(DeferredSource(route, n), module);
                    var outcome = AstStructuralDepthProcessTests.RunOnThreadWithStack(stack, () =>
                        Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), HostOperations.Create(), null, null, default).GetAwaiter().GetResult());
                    sweep.Record(n, "deferred", outcome);
                }

                sweep.AssertOutcomes(requireRefusal: false);
            }

            Tally.AssertCrossesTheFrontier($"deferred {route}", routeSweeps);
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
        string label, IReadOnlyList<Decimal128>? expected = null, bool allowDeferredCompileRefusal = false)
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
            Assert.NotNull(error.Span);
            _refusals++;
            _log.Add($"{point}{route[0]}:{error.Code}@{error.Span}");
        }

        /// <summary>
        /// A synchronous observed run: the <see cref="Record"/> rules, except that a SPANLESS
        /// refusal is accepted only when it is root-level — <see cref="EvalError.EvaluationStackExhausted"/>
        /// after no evaluation step, no expression checkpoint and no invocation depth.
        /// </summary>
        public void RecordObserved(int point, EvalResult<Evaluator.CountedResult> outcome, long steps, long checkpoints, int peakDepth)
        {
            if (outcome.IsOk)
            {
                Assert.True(outcome.Value.Value.TryToHostAtoms(int.MaxValue, out var atoms));
                Assert.Equal(_expected, atoms);
                FirstCompletion ??= point;
                _completions++;
                _log.Add($"{point}s:ok");
                return;
            }

            var error = outcome.Error;
            if (error.Code is not (KatLangErrorCode.EvaluationStackExhausted or KatLangErrorCode.EvaluationDepthExceeded))
                Assert.Fail($"{label} @{point} (sync): unexpected outcome {error.Code}: {error}");
            if (error.Code == KatLangErrorCode.EvaluationStackExhausted)
                Assert.True(error.IsResourceLimit);
            if (error.Span is null)
            {
                Assert.True(error.Code == KatLangErrorCode.EvaluationStackExhausted && steps == 0 && checkpoints == 0 && peakDepth == 0,
                    $"{label} @{point}: a spanless refusal must be the root-level stack refusal before any evaluation, not {error.Code} after {steps} steps, {checkpoints} checkpoints, depth {peakDepth}");
                RootLevelRefusals++;
            }

            _refusals++;
            _log.Add($"{point}s:{error.Code}@{error.Span?.ToString() ?? "root"}");
        }

        /// <summary>Spanless refusals <see cref="RecordObserved"/> accepted as root-level; diagnostic only.</summary>
        public int RootLevelRefusals { get; private set; }

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

        /// <summary>Structured refusals recorded so far (stack or depth, or a deferred compile's).</summary>
        public int Refusals => _refusals;

        /// <summary>
        /// Every sweep must evaluate some run. A sweep must also be refused somewhere unless
        /// <paramref name="requireRefusal"/> is false — for a sweep with async twin runs, whose
        /// refusals the caller requires across the stack sizes instead (see
        /// <see cref="AssertCrossesTheFrontier"/>).
        /// </summary>
        public void AssertOutcomes(bool requireRefusal = true)
        {
            Console.WriteLine($"{label}: {string.Join(" ", _log)}");
            Assert.True(_completions > 0, $"{label}: no run evaluated\n{string.Join(" ", _log)}");
            if (requireRefusal)
                Assert.True(_refusals > 0, $"{label}: no run was refused; the sweep no longer crosses the frontier\n{string.Join(" ", _log)}");
        }

        /// <summary>
        /// The frontier requirement of sweeps with async twin runs, over all stack sizes of one family.
        /// Since the 2026-11-14 stack hop the twin continues on a fresh thread-pool stack where an
        /// invocation or row funnel would refuse, so its refusals come only from helper probes (the
        /// open navigation, a deferred compile) and recur once per hop period at depths that depend
        /// on where the hops land; one stack size may see none within the swept depths (Release,
        /// November 2026: a deferred <c>branch-inner</c> sweep at 1536 KiB, and under CPU load the
        /// synchronous frontier at 1280 KiB moved past the window that the twin used to cover). The
        /// family as a whole must still be refused somewhere.
        /// </summary>
        public static void AssertCrossesTheFrontier(string family, IReadOnlyCollection<Tally> sweeps)
            => Assert.True(sweeps.Sum(static sweep => sweep.Refusals) > 0,
                $"{family}: no run was refused at any stack size; the sweep no longer crosses the frontier");
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
