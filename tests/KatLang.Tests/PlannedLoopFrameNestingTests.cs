using System.Collections;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using ValEnv = System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Result Value)>;

namespace KatLang.Tests;

/// <summary>
/// Nested planned-loop frames and the value environment each one captures (2026-11-21). A loop that a
/// planned step's body starts again (recursion routed through loop steps, <c>F(n) = repeat(F(n), 1)</c>)
/// builds one <see cref="LoopRunFrame"/> per level over the previous frame's
/// <see cref="LoopRunFrame.ValueEnvironment"/>, and every frame copies that environment's values into its
/// captured slots. When each view wrapped its parent, counting, indexing and enumerating a view recursed
/// through one link per level in frames no stack probe guards, which killed the process on large threads
/// (corpus input #11176). A view built over a view now reads the original bindings directly
/// (<see cref="LoopValueEnvironment"/>).
///
/// <para>Production value environments are empty since Model C, so the program-level stack tests
/// (<c>EvaluationLimitsProcessTests.RecursionThroughPlannedLoopSteps_*</c>) cannot see what a view reads. The
/// frame test nests 4,096 frames over a non-empty terminal environment with a repeated name and two equal
/// values held by distinct objects. It checks the same names in the same order, the
/// terminal's own <see cref="Result"/> objects in its captured slots, and the terminal environment itself
/// serving every read, at the same managed stack depth whatever the nesting. The depth check is bounded: it
/// runs on a 16 MiB thread, where a reintroduced per-level recursion fails the assertion instead of
/// overflowing.</para>
///
/// <para>The program test exercises the engine's source entries, the evaluator's value and flat entries,
/// and the counted observation harness. Their async entries run inline for this synchronous program.
/// An async cache forces the generic twin for a separate control.</para>
/// </summary>
public class PlannedLoopFrameNestingTests
{
    private const int Depth = 4_096;

    private static readonly Result FirstX = new Result.Atom(1);
    private static readonly Result OnlyY = new Result.Bool(true);
    // Equal to FirstX but a distinct object: a captured slot must hold this very object.
    private static readonly Result SecondX = new Result.Atom(1);

    private static readonly (string Name, Result Value)[] TerminalBindings =
        [("x", FirstX), ("y", OnlyY), ("x", SecondX)];

    [Fact]
    public void NestedFrames_PreserveBindingsAndIdentity_AtConstantStackDepth()
    {
        AstStructuralDepthProcessTests.RunOnThreadWithStack(16 * 1024 * 1024, static () =>
        {
            var terminal = new ProbeEnvironment(TerminalBindings);
            var frames = NestFrames(terminal, Depth);
            AssertBindingsAndIdentity(terminal, frames);

            var shallow = frames[0].ValueEnvironment;
            var deep = frames[^1].ValueEnvironment;
            var template = frames[0].Template;
            AssertSameDepth(terminal, () => CountThrough(shallow), () => CountThrough(deep), "Count");
            AssertSameDepth(terminal, () => IndexThrough(shallow, 2), () => IndexThrough(deep, 2), "indexer");
            AssertSameDepth(terminal, () => EnumerateThrough(shallow), () => EnumerateThrough(deep), "enumeration");
            AssertSameDepth(terminal, () => CaptureThrough(template, shallow), () => CaptureThrough(template, deep), "captured slots");
        });
    }

    private static void AssertBindingsAndIdentity(ProbeEnvironment terminal, LoopRunFrame[] frames)
    {
        foreach (var level in new[] { 0, 1, 63, Depth - 1 })
        {
            var frame = frames[level];
            var view = frame.ValueEnvironment;
            Assert.Equal(TerminalBindings.Length, view.Count);
            for (var index = 0; index < TerminalBindings.Length; index++)
            {
                Assert.Equal(TerminalBindings[index].Name, view[index].Name);
                Assert.Same(TerminalBindings[index].Value, view[index].Value);
                Assert.Same(TerminalBindings[index].Value, frame.GetCapturedSlot(index));
            }

            // Enumeration keeps the order and the repeated name, and hands on the same objects.
            Assert.Equal(TerminalBindings.Select(static binding => binding.Name), view.Select(static binding => binding.Name));
            Assert.Equal<Result>(
                TerminalBindings.Select(static binding => binding.Value),
                view.Select(static binding => binding.Value),
                ReferenceEqualityComparer.Instance);
        }

        // The terminal environment itself serves every read of the innermost view: one read of it per view read.
        var innermost = frames[^1].ValueEnvironment;
        var reads = terminal.Reads;
        _ = innermost.Count;
        _ = innermost[2];
        Assert.Equal(reads + 2, terminal.Reads);
        var enumerators = terminal.EnumeratorsCreated;
        _ = new LoopRunFrame(frames[^1].Template, innermost, InitialState());
        Assert.Equal(enumerators + 1, terminal.EnumeratorsCreated);

        // Each frame keeps a cache identity of its own, which only its own iteration refreshes.
        var identities = frames.Select(static frame => Evaluator.ValueEnvironmentCacheIdentity(frame.ValueEnvironment)).ToArray();
        Assert.Equal(Depth, identities.Distinct(ReferenceEqualityComparer.Instance).Count());
        Assert.DoesNotContain(identities, identity => ReferenceEquals(identity, terminal));
        Assert.IsType<LoopValueEnvironment>(innermost).BeginIteration();
        Assert.NotSame(identities[^1], Evaluator.ValueEnvironmentCacheIdentity(innermost));
        Assert.Same(identities[^2], Evaluator.ValueEnvironmentCacheIdentity(frames[^2].ValueEnvironment));
        Assert.Same(identities[0], Evaluator.ValueEnvironmentCacheIdentity(frames[0].ValueEnvironment));
    }

    /// <summary>
    /// Bounded recursion through planned loop steps on the engine and evaluator entry points: one
    /// planned loop per level, each over the previous level's environment, completing with the generic
    /// value, step count and depth.
    /// </summary>
    [Fact]
    public async Task BoundedLoopStepRecursion_NestsOnePlannedFramePerLevel()
    {
        const int levels = 200;
        var source = $"F(n) = if(n > 0, repeat(F(n - 1), 1), 0)\nF({levels})";
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        AstStructuralDepthProcessTests.RunOnThreadWithStack(64 * 1024 * 1024, () =>
        {
            var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false);
            AssertZero(generic.Result, "generic");
            Assert.Equal(0, generic.Budget.CurrentDepth);

            var diagnostics = new LoopOptimizationDiagnostics();
            var planned = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics);
            AssertZero(planned.Result, "RunCountedObserved");
            Assert.Equal(0, planned.Budget.CurrentDepth);
            Assert.Equal(generic.Budget.ConsumedSteps, planned.Budget.ConsumedSteps);
            Assert.Equal(generic.Budget.ConsumedExpressionCheckpoints, planned.Budget.ConsumedExpressionCheckpoints);
            Assert.Equal(generic.Budget.PeakDepth, planned.Budget.PeakDepth);
            var loop = diagnostics.GetSnapshot();
            // Level n > 0 starts one loop, planned with its recursive row as a generic fallback.
            Assert.Equal(levels, loop.OptimizedLoopHits);
            Assert.Equal(0, loop.OptimizedLoopFallbacks);
            Assert.Equal(levels, loop.LoopIterations);

            AssertZero(Evaluator.Run(program), "Evaluator.Run");
            AssertZero(Evaluator.RunAsync(program).GetAwaiter().GetResult(), "Evaluator.RunAsync");
            Assert.Equal(0m, Assert.Single(Evaluator.RunFlat(program).Value));
            Assert.Equal(0m, Assert.Single(Evaluator.RunFlatAsync(program).GetAwaiter().GetResult().Value));
            var observedAsync = Evaluator.RunCountedObservedAsync(program).AsTask().GetAwaiter().GetResult();
            AssertZero(observedAsync.Result, "RunCountedObservedAsync");
            Assert.Equal(planned.Budget.ConsumedSteps, observedAsync.Budget.ConsumedSteps);
            AssertEngineZero(KatLangEngine.Run(source), "KatLangEngine.Run");
            AssertEngineZero(KatLangEngine.RunAsync(source).GetAwaiter().GetResult(), "KatLangEngine.RunAsync");
        });

        // The forced twin plans no loop; it may hop to fresh stacks, so it runs on an ordinary thread.
        var twin = await Evaluator.RunCountedObservedAsync(
            program,
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        AssertZero(twin.Result, "forced twin");
        Assert.Equal(0, twin.Budget.CurrentDepth);
    }

    // ── Helpers ──────────────────────────────────────────────────────────────────────────────

    private static LoopPlanTemplate Template()
    {
        var root = SourceProvenance.ParseValid("Step(a) = a + 1\nrepeat(Step(0), 1)").Root;
        var step = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties).Value);
        return new LoopPlanTemplate(
            LoopKind.Repeat,
            step,
            step.ParameterPatterns.ToArray(),
            ["a"],
            StateArity: 1,
            TempPlans: [],
            NextStateOutputs: [],
            ContinuationOutput: null,
            RequiresPerIterationCacheIdentity: false,
            Evaluator.EvalCtx.Empty,
            DiagnosticKey: null);
    }

    private static NeedCell[] InitialState()
        => [NeedCell.Ready(new Evaluator.CountedResult(new Result.Atom(0), 1))];

    /// <summary>Frame <c>k</c> is built over frame <c>k - 1</c>'s environment, as a nested planned loop builds it.</summary>
    private static LoopRunFrame[] NestFrames(ValEnv terminal, int depth)
    {
        var template = Template();
        var frames = new LoopRunFrame[depth];
        var environment = terminal;
        for (var level = 0; level < depth; level++)
        {
            frames[level] = new LoopRunFrame(template, environment, InitialState());
            environment = frames[level].ValueEnvironment;
        }

        return frames;
    }

    private static void AssertSameDepth(ProbeEnvironment terminal, Action shallowRead, Action deepRead, string operation)
    {
        // Interleaved twice, so a method tiering up between two reads cannot pass for a nesting effect.
        var depths = new List<(int Shallow, int Deep)>();
        for (var round = 0; round < 2; round++)
            depths.Add((terminal.DeepestRead(shallowRead), terminal.DeepestRead(deepRead)));
        foreach (var (shallow, deep) in depths)
        {
            Assert.True(shallow > 0, $"{operation}: the terminal environment was not read");
            Assert.True(Math.Abs(deep - shallow) <= 2,
                $"{operation}: the terminal was read {deep} frames deep through the innermost view and {shallow} through the outermost");
        }
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static int CountThrough(ValEnv view) => view.Count;

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static string IndexThrough(ValEnv view, int index) => view[index].Name;

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static int EnumerateThrough(ValEnv view)
    {
        var count = 0;
        foreach (var _ in view)
            count++;
        return count;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static LoopRunFrame CaptureThrough(LoopPlanTemplate template, ValEnv view)
        => new(template, view, InitialState());

    private static void AssertZero(EvalResult<Evaluator.CountedResult> result, string route)
    {
        Assert.False(result.IsError, $"{route}: {(result.IsError ? result.Error : null)}");
        Assert.Equal(0m, Assert.IsType<Result.Atom>(result.Value.Value).Value);
        Assert.Equal(1, result.Value.EmittedCount);
    }

    private static void AssertZero(EvalResult<Result> result, string route)
    {
        Assert.False(result.IsError, $"{route}: {(result.IsError ? result.Error : null)}");
        Assert.Equal(0m, Assert.IsType<Result.Atom>(result.Value).Value);
    }

    private static void AssertEngineZero(RunResult result, string route)
    {
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.True(Result.ValueComparer.Equals(new Result.Atom(0), success.Value), $"{route}: {success.Value}");
        Assert.Equal(1, success.EmittedCount);
    }

    /// <summary>
    /// A terminal value environment that counts its reads and, while armed, records the managed stack depth
    /// of each one. Its accessors are never inlined, so each read is a frame of its own.
    /// </summary>
    private sealed class ProbeEnvironment((string Name, Result Value)[] bindings) : IReadOnlyList<(string Name, Result Value)>
    {
        private readonly (string Name, Result Value)[] _bindings = bindings;
        private bool _armed;
        private int _deepest;

        public int Reads { get; private set; }

        public int EnumeratorsCreated { get; private set; }

        public int Count
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            get
            {
                Record();
                return _bindings.Length;
            }
        }

        public (string Name, Result Value) this[int index]
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            get
            {
                Record();
                return _bindings[index];
            }
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public IEnumerator<(string Name, Result Value)> GetEnumerator()
        {
            EnumeratorsCreated++;
            Record();
            return new Enumerator(this);
        }

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

        /// <summary>The deepest stack, in managed frames, at which <paramref name="read"/> read this environment.</summary>
        public int DeepestRead(Action read)
        {
            _deepest = 0;
            _armed = true;
            try
            {
                read();
            }
            finally
            {
                _armed = false;
            }

            return _deepest;
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private void Record()
        {
            Reads++;
            if (_armed)
                _deepest = Math.Max(_deepest, new StackTrace(fNeedFileInfo: false).FrameCount);
        }

        private sealed class Enumerator(ProbeEnvironment owner) : IEnumerator<(string Name, Result Value)>
        {
            private int _index = -1;

            public (string Name, Result Value) Current => owner._bindings[_index];

            object IEnumerator.Current => Current;

            [MethodImpl(MethodImplOptions.NoInlining)]
            public bool MoveNext()
            {
                owner.Record();
                return ++_index < owner._bindings.Length;
            }

            public void Reset() => _index = -1;

            public void Dispose()
            {
            }
        }
    }
}
