using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests.Hosting;

/// <summary>
/// HOST-VALUE ADMISSION (SEC-01-FU, October 2026): a successful host-operation return crosses ONE
/// boundary (<c>Evaluator.NormalizeHostOperationValue</c> → <see cref="Result.AdmitHostOperationValue"/>)
/// before any consumer or cache sees it, and the same DAG-safe walk that normalizes it also admits it.
/// Host code built the value outside every evaluator reservation, so before this boundary a host could
/// hand evaluation a collection or string larger than any the run could build itself.
///
/// <para>Pinned here: every distinct nested sequence/list node's IMMEDIATE count against the effective
/// <see cref="EvaluationLimits.MaxCollectionItems"/> (a nested value is one parent slot), every string
/// leaf against the effective <see cref="EvaluationLimits.MaxStringLength"/>, exact boundaries, shared
/// DAGs (node-bounded work, preserved identity), the structural-work charge and its cancellation
/// checkpoint, terminality, cache safety, callbacks and loop steps, the unchanged host exception
/// contract, sync/async/strategy/public-entry parity, and the accounting policy: admission is a size
/// check, NOT a reservation, so the cumulative materialization counters never move for a host
/// return.</para>
/// </summary>
public class HostValueAdmissionTests
{
    private static readonly TimeSpan Timeout = TimeSpan.FromSeconds(30);

    private static Result Num(int value) => new Result.Atom(value);

    private static Result.ListValue ListOf(int count) => new(Enumerable.Range(1, count).Select(Num));

    private static Result.SequenceValue SequenceOf(int count) => new(Enumerable.Range(1, count).Select(Num));

    /// <summary>A shared DAG: <c>L0 = [1, 1]</c>, <c>Lk = [Lk-1, Lk-1]</c> — k+1 nodes, 2^(k+1) leaf paths.</summary>
    private static Result.ListValue SharedTower(int levels)
    {
        var node = new Result.ListValue([Num(1), Num(1)]);
        for (var i = 0; i < levels; i++)
            node = new Result.ListValue([node, node]);
        return node;
    }

    private sealed class Effects
    {
        public int Calls;
        public int Ticks;

        public override string ToString() => $"calls={Calls} ticks={Ticks}";
    }

    private sealed record Outcome(string Text, long Materialized, long StringChars, long StructuralUnits, string Effects);

    /// <summary>
    /// Host operations for a test: <c>Value</c> (zero parameters) and <c>Make(x)</c> both return
    /// <paramref name="produce"/>'s value, <c>Id(x)</c> returns its argument, <c>Grow(n)</c> returns <c>[1..n]</c>, <c>Tick()</c> records an
    /// effect that must never happen after a terminal refusal.
    /// </summary>
    private static HostOperations Operations(Effects effects, Func<Result> produce) => HostOperations.Create(
        HostOperation.Create("Value", (_, _) => { effects.Calls++; return produce(); }),
        HostOperation.Create("Make", (_, _) => { effects.Calls++; return produce(); }, "x"),
        HostOperation.Create("Id", (args, _) => { effects.Calls++; return args[0]; }, "x"),
        HostOperation.Create("Grow", (args, _) => { effects.Calls++; return ListOf((int)args[0].AsNum()!.Value); }, "n"),
        HostOperation.Create("Tick", (_, _) => { effects.Ticks++; return Num(0); }));

    private static Expr Program(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static string Describe(EvalError error)
    {
        var inner = error;
        while (inner is EvalError.WithContext context)
            inner = context.Inner;
        return inner switch
        {
            EvalError.CollectionSizeLimitExceeded limit => $"err items {limit.Limit}/{limit.Requested}",
            EvalError.StringSizeLimitExceeded limit => $"err string {limit.Limit}/{limit.Requested}",
            EvalError.MaterializationLimitExceeded limit => $"err materialized {limit.Limit}",
            EvalError.EvaluationStepLimitExceeded limit => $"err steps {limit.Limit}",
            _ => "err " + inner.GetType().Name,
        };
    }

    private static string Text(EvalResult<Evaluator.CountedResult> result)
        => result.IsOk ? "ok " + SemanticExplorerHarness.Neutral(result.Value.Value) : Describe(result.Error);

    private static Outcome Sync(string source, Func<Result> produce, EvaluationLimits? limits, bool optimized, LoopOptimizationDiagnostics? loops = null)
    {
        var effects = new Effects();
        var operations = Operations(effects, produce);
        var (result, budget) = Evaluator.RunCountedObserved(
            Program(source, operations), limits, enableOptimizations: optimized, loopDiagnostics: loops, hostOperations: operations);
        return new(Text(result), budget.MaterializedItems, budget.MaterializedStringChars, budget.ConsumedStructuralWorkUnits, effects.ToString());
    }

    private static Outcome AsyncTwin(string source, Func<Result> produce, EvaluationLimits? limits)
    {
        var effects = new Effects();
        var operations = Operations(effects, produce);
        var (result, budget) = Evaluator.RunCountedObservedAsync(
            Program(source, operations), limits, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            hostOperations: operations).AsTask().GetAwaiter().GetResult();
        return new(Text(result), budget.MaterializedItems, budget.MaterializedStringChars, budget.ConsumedStructuralWorkUnits, effects.ToString());
    }

    /// <summary>Runs on the generic, optimized, and async-twin routes, which must agree exactly (accounting included).</summary>
    private static Outcome Observe(string source, Func<Result> produce, EvaluationLimits? limits = null)
    {
        var generic = Sync(source, produce, limits, optimized: false);
        Assert.Equal(generic, Sync(source, produce, limits, optimized: true));
        Assert.Equal(generic, AsyncTwin(source, produce, limits));
        return generic;
    }

    private static EvaluationLimits Items(int max) => new() { MaxCollectionItems = max };

    private static EvaluationLimits Chars(int max) => new() { MaxStringLength = max };

    // ── T1/T2/T4: immediate collection size, exact boundaries ────────────────

    [Theory]
    [InlineData(3, "ok L[1, 2, 3]")]
    [InlineData(4, "err items 3/4")]
    public void List_IsAdmittedAtTheLimit_AndRefusedOneAbove(int count, string expected)
        => Assert.Equal(expected, Observe("Value", () => ListOf(count), Items(3)).Text);

    [Theory]
    [InlineData(3, "ok S[1, 2, 3]")]
    [InlineData(4, "err items 3/4")]
    public void Sequence_IsAdmittedAtTheLimit_AndRefusedOneAbove(int count, string expected)
        => Assert.Equal(expected, Observe("Value", () => SequenceOf(count), Items(3)).Text);

    [Fact]
    public void DefaultCeiling_RefusesAnOversizedHostCollection_WithoutAnyConfiguration()
    {
        var oversized = ListOf(EvaluationLimits.MaxSupportedCollectionItems + 1);
        Assert.Equal($"err items {EvaluationLimits.MaxSupportedCollectionItems}/{EvaluationLimits.MaxSupportedCollectionItems + 1}",
            Observe("Value", () => oversized).Text);
        var full = ListOf(EvaluationLimits.MaxSupportedCollectionItems);
        Assert.StartsWith("ok L[1, 2, 3", Observe("Value", () => full).Text);
    }

    [Fact]
    public void AcceptedList_KeepsItsExactListRepresentation()
    {
        // A one-item list is never singleton-collapsed; a one-item sequence is (the existing normalization).
        Assert.Equal("ok L[7]", Observe("Value", () => new Result.ListValue([Num(7)]), Items(1)).Text);
        Assert.Equal("ok 7", Observe("Value", () => new Result.SequenceValue([Num(7)]), Items(1)).Text);
    }

    // ── T3: nested values ────────────────────────────────────────────────────

    [Fact]
    public void NestedOversizedCollection_InsideASmallOuterValue_IsRefused()
    {
        Assert.Equal("err items 3/4", Observe("Value", () => new Result.ListValue([Num(0), ListOf(4)]), Items(3)).Text);
        Assert.Equal("err items 3/4", Observe("Value",
            () => new Result.SequenceValue([Num(0), new Result.ListValue([SequenceOf(4)])]), Items(3)).Text);
    }

    [Fact]
    public void NestedValue_OccupiesOneParentSlot_NotItsTransitiveSize()
        => Assert.Equal("ok L[L[1, 2, 3], L[1, 2, 3], L[1, 2, 3]]",
            Observe("Value", () => new Result.ListValue([ListOf(3), ListOf(3), ListOf(3)]), Items(3)).Text);

    [Fact]
    public void FirstViolation_InDepthFirstOrder_IsReported()
        => Assert.Equal("err items 3/5", Observe("Value",
            () => new Result.ListValue([new Result.ListValue([ListOf(5)]), ListOf(4)]), Items(3)).Text);

    // ── T5: strings ──────────────────────────────────────────────────────────

    [Theory]
    [InlineData("abc", "ok 'abc'")]
    [InlineData("abcd", "err string 3/4")]
    public void TopLevelString_IsAdmittedAtTheLimit_AndRefusedOneAbove(string text, string expected)
        => Assert.Equal(expected, Observe("Value", () => new Result.Str(text), Chars(3)).Text);

    [Fact]
    public void NestedOversizedString_IsRefused()
        => Assert.Equal("err string 3/4", Observe("Value",
            () => new Result.ListValue([new Result.Str("ab"), new Result.SequenceValue([Num(1), new Result.Str("abcd")])]), Chars(3)).Text);

    [Fact]
    public void DefaultStringCeiling_RefusesAnOversizedHostString_AndContentsAreNeverTruncated()
    {
        var oversized = new Result.Str(new string('x', EvaluationLimits.MaxSupportedStringLength + 1));
        Assert.Equal($"err string {EvaluationLimits.MaxSupportedStringLength}/{EvaluationLimits.MaxSupportedStringLength + 1}",
            Observe("Value", () => oversized).Text);

        var full = new Result.Str(new string('x', EvaluationLimits.MaxSupportedStringLength));
        var effects = new Effects();
        var operations = Operations(effects, () => full);
        var result = Evaluator.Run(Program("Value", operations), operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.True(result.IsOk);
        Assert.Same(full, result.Value);
    }

    // ── T6: shared DAGs ──────────────────────────────────────────────────────

    [Fact]
    public void SharedDag_IsAdmittedNodeByNode_WithItsIdentityPreserved()
    {
        const int levels = 40;   // 41 distinct nodes, 2^41 leaf paths
        var tower = SharedTower(levels);
        var traversal = new ValueTraversalObservations();
        Result? seen = null;
        var operations = HostOperations.Create(
            HostOperation.Create("Value", (_, _) => tower),
            HostOperation.Create("See", (args, _) => { seen = args[0]; return Num(0); }, "x"));

        var (result, budget) = Evaluator.RunCountedObserved(Program("See(Value)", operations),
            Items(2), observations: new EvaluationObservations { StructuralTraversal = traversal }, hostOperations: operations);

        Assert.True(result.IsOk, result.IsError ? Describe(result.Error) : null);
        // Every node's immediate count is 2, so a limit of 2 admits a value with 2^41 leaves.
        Assert.Same(tower, seen);
        Assert.Equal(levels + 1, traversal.NormalizeStructureExpansionCount);
        // Admission: 40 nested frames × (2 slot inspections + 1 completion); the root's slots are free
        // and its second (shared) child is a memo hit. Passing the tower to See charges its
        // argument call-reference scan the same node-bounded 40 × 3.
        Assert.Equal(2 * 3 * levels, traversal.StructuralWorkUnits);
        Assert.Equal(2 * 3 * levels, budget.ConsumedStructuralWorkUnits);
    }

    [Fact]
    public void SharedNestedNode_IsChargedOnce()
    {
        var shared = ListOf(3);
        // One descent: 3 inspections + 1 completion; the second occurrence is a free root-level memo hit.
        Assert.Equal(4, Observe("Value", () => new Result.ListValue([shared, shared])).StructuralUnits);
        // Flat values charge nothing at all.
        Assert.Equal(0, Observe("Value", () => ListOf(1000)).StructuralUnits);
    }

    [Fact]
    public void DeepHostValue_AdmissionAndArgumentScan_StayStackSafe()
    {
        const int depth = 15_000;
        Result value = Num(1);
        for (var i = 0; i < depth; i++)
            value = new Result.ListValue([value]);
        var budget = EvaluationBudget.Create(Items(1));
        var observations = new ValueTraversalObservations();

        var admitted = value.AdmitHostOperationValue("Deep", budget, observations);

        Assert.True(admitted.IsOk);
        Assert.Same(value, admitted.Value);
        Assert.Equal(depth, observations.NormalizeStructureExpansionCount);
        Assert.Equal(2 * (depth - 1), budget.ConsumedStructuralWorkUnits);
        Assert.Null(Evaluator.HostArgumentBoundaryError(value, budget, observations));
        Assert.Equal(4 * (depth - 1), budget.ConsumedStructuralWorkUnits);
        Assert.Equal(depth - 1, observations.CallReferenceScanPeakPendingFrames);
    }

    [Fact]
    public void AdmissionAndArgumentScan_ChargeSharedEmptyStructuresOnce()
    {
        var first = new Result.ListValue([]);
        var second = new Result.ListValue([]);
        var value = new Result.ListValue([first, second, first, second]);
        var admissionBudget = EvaluationBudget.Create(null);
        var scanBudget = EvaluationBudget.Create(null);

        Assert.Same(value, value.AdmitHostOperationValue("Empty", admissionBudget, observations: null).Value);
        Assert.Null(Evaluator.HostArgumentBoundaryError(value, scanBudget, observations: null));

        Assert.Equal(2, admissionBudget.ConsumedStructuralWorkUnits);
        Assert.Equal(admissionBudget.ConsumedStructuralWorkUnits, scanBudget.ConsumedStructuralWorkUnits);
    }

    // ── T7: immutability of host-built values ────────────────────────────────

    [Fact]
    public void PublicConstruction_Snapshots_AndExposesReadOnlyViews()
    {
        var source = new List<Result> { Num(1), new Result.Str("a") };
        var list = new Result.ListValue(source);
        var sequence = new Result.SequenceValue(source);
        var hashBefore = Result.ValueComparer.GetHashCode(list);
        var copy = list with { };

        source[0] = Num(99);
        source.Add(Num(3));

        foreach (var value in new Result[] { list, sequence })
        {
            var items = value is Result.ListValue(var l) ? l : ((Result.SequenceValue)value).Items;
            Assert.Equal(2, items.Count);
            Assert.Equal(Num(1), items[0]);
            var mutable = Assert.IsAssignableFrom<IList<Result>>(items);
            Assert.Throws<NotSupportedException>(() => mutable.Add(Num(4)));
            Assert.Throws<NotSupportedException>(() => mutable[0] = Num(4));
            Assert.Throws<NotSupportedException>(() => mutable.Clear());
            Assert.False(items is Result[]);
        }

        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(list));
        Assert.True(Result.ValueComparer.Equals(list, copy));
        Assert.Same(list.Items, copy.Items);
        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(copy));
    }

    [Fact]
    public void ReturnedValue_CannotBeChangedThroughTheHostsOriginalStorage()
    {
        var storage = new List<Result> { Num(1), Num(2) };
        var effects = new Effects();
        Result.ListValue? returned = null;
        var operations = HostOperations.Create(
            HostOperation.Create("Value", (_, _) =>
            {
                returned = new Result.ListValue(storage);
                storage[0] = Num(100);   // after construction, before the run reads it
                storage.Add(Num(3));
                return returned;
            }),
            HostOperation.Create("Tick", (_, _) => { effects.Ticks++; storage.Clear(); return Num(0); }));

        var result = Evaluator.Run(Program("Value, Tick(), Value", operations), operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.True(result.IsOk);
        Assert.Equal("S[L[1, 2], 0, L[1, 2]]", SemanticExplorerHarness.Neutral(result.Value));
    }

    [Fact]
    public async Task OneSharedHostValue_ServesConcurrentRunsUnchanged()
    {
        var shared = new Result.ListValue([ListOf(3), new Result.Str("x"), ListOf(3)]);
        var hash = Result.ValueComparer.GetHashCode(shared);
        var operations = HostOperations.Create(HostOperation.Create("Value", (_, _) => shared));
        var runs = Enumerable.Range(0, 16).Select(_ => Task.Run(() =>
            KatLangEngine.Run("[Value, Value]", new RunOptions { HostOperations = operations }))).ToArray();
        var displays = (await Task.WhenAll(runs).WaitAsync(Timeout))
            .Select(static run => SemanticExplorerHarness.Neutral(Assert.IsType<RunResult.Success>(run).Value))
            .Distinct().ToArray();
        Assert.Equal("L[L[L[1, 2, 3], 'x', L[1, 2, 3]], L[L[1, 2, 3], 'x', L[1, 2, 3]]]", Assert.Single(displays));
        Assert.Equal(hash, Result.ValueComparer.GetHashCode(shared));
    }

    // ── T8/T15: sync/async parity and the public entry points ────────────────

    [Fact]
    public async Task GenuinelySuspendedAsyncReturn_IsAdmittedLikeTheSynchronousReturn()
    {
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var ticks = 0;
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("Value", async (_, _) => { reached.TrySetResult(); return await gate.Task; }),
            HostOperation.Create("Tick", (_, _) => { ticks++; return Num(0); }));
        var options = new RunOptions { HostOperations = operations, EvaluationLimits = Items(3) };

        var pending = KatLangEngine.RunAsync("Value, Tick()", options);
        await reached.Task.WaitAsync(Timeout);
        Assert.False(pending.IsCompleted);
        gate.SetResult(ListOf(4));
        var asyncFailure = Assert.IsType<RunResult.EvalFailure>(await pending.WaitAsync(Timeout));

        var syncOperations = HostOperations.Create(
            HostOperation.Create("Value", (_, _) => ListOf(4)),
            HostOperation.Create("Tick", (_, _) => { ticks++; return Num(0); }));
        var syncFailure = Assert.IsType<RunResult.EvalFailure>(
            KatLangEngine.Run("Value, Tick()", new RunOptions { HostOperations = syncOperations, EvaluationLimits = Items(3) }));

        Assert.Equal(KatLangErrorCode.CollectionSizeLimitExceeded, Assert.Single(syncFailure.Errors).Code);
        Assert.Equal(syncFailure.Errors.Select(static e => (e.Code, e.Span, e.Message)),
            asyncFailure.Errors.Select(static e => (e.Code, e.Span, e.Message)));
        Assert.Equal(0, ticks);
    }

    [Fact]
    public async Task EveryPublicEntryPoint_RefusesTheSameOversizedReturn()
    {
        var operations = Operations(new Effects(), () => new Result.ListValue([new Result.Str("abcd")]));
        var options = new RunOptions { HostOperations = operations, EvaluationLimits = Chars(3) };
        var ast = Program("Make(1)", operations);

        var engine = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("Make(1)", options));
        var engineAsync = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync("Make(1)", options));
        var evaluator = Evaluator.Run(ast, operations, Chars(3), randomSeed: null, CancellationToken.None);
        var evaluatorAsync = await Evaluator.RunAsync(ast, operations, Chars(3), randomSeed: null, CancellationToken.None);

        Assert.Equal(KatLangErrorCode.StringSizeLimitExceeded, Assert.Single(engine.Errors).Code);
        Assert.Equal(engine.Errors.Select(static e => (e.Code, e.Message)), engineAsync.Errors.Select(static e => (e.Code, e.Message)));
        Assert.Equal("err string 3/4", Describe(evaluator.Error));
        Assert.Equal("err string 3/4", Describe(evaluatorAsync.Error));
    }

    // ── T9: the zero-argument property cache ─────────────────────────────────

    private sealed class RecordingCache : IZeroArgPropertyResultCache
    {
        private readonly RunScopedZeroArgPropertyResultCache _inner = new();

        public int Stored;

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
            => _inner.GetOrEvaluate(execution, () =>
            {
                var evaluated = evaluate();
                if (evaluated.IsOk)
                    Stored++;
                return evaluated;
            });
    }

    [Fact]
    public void CachedProperty_StoresOnlyAnAdmittedValue_AndARefusalIsNeverCached()
    {
        var accepted = new Effects();
        var acceptedOps = Operations(accepted, () => new Result.SequenceValue([ListOf(3)]));
        var acceptedCache = new RecordingCache();
        var ok = Evaluator.RunCounted(Program("Value, Value", acceptedOps), acceptedCache, Items(3), hostOperations: acceptedOps);
        Assert.True(ok.IsOk);
        Assert.Equal("S[L[1, 2, 3], L[1, 2, 3]]", SemanticExplorerHarness.Neutral(ok.Value.Value));
        Assert.Equal(1, accepted.Calls);
        Assert.Equal(1, acceptedCache.Stored);

        var refused = new Effects();
        var refusedOps = Operations(refused, () => ListOf(4));
        var refusedCache = new RecordingCache();
        var failed = Evaluator.RunCounted(Program("Value, Value", refusedOps), refusedCache, Items(3), hostOperations: refusedOps);
        Assert.Equal("err items 3/4", Describe(failed.Error));
        Assert.Equal(1, refused.Calls);
        Assert.Equal(0, refusedCache.Stored);
    }

    // ── T10: callbacks and loop steps ────────────────────────────────────────

    [Fact]
    public void CallbackReturn_IsAdmittedBeforeTheConsumerUsesIt()
    {
        var outcome = Observe("map([3, 4, 3], Grow).count, Tick()", () => Num(0), Items(3));
        Assert.Equal("err items 3/4", outcome.Text);
        Assert.Equal("calls=2 ticks=0", outcome.Effects);
        Assert.Equal("ok S[3, 0]", Observe("map([3, 1, 3], Grow).count, Tick()", () => Num(0), Items(3)).Text);
    }

    [Fact]
    public void LoopStepReturn_IsAdmittedInEveryStrategy()
    {
        const string source = "repeat(Make(0), 3), Tick()";
        var refused = Observe(source, () => ListOf(4), Items(3));
        Assert.Equal("err items 3/4", refused.Text);
        Assert.Equal("calls=1 ticks=0", refused.Effects);
        Assert.Equal("ok S[L[1, 2, 3], 0]", Observe(source, () => ListOf(3), Items(3)).Text);
    }

    // ── T11: cancellation during admission ───────────────────────────────────

    /// <summary>64 distinct nested lists of 64 atoms: 64 × 65 = 4,160 admission units, 17 charges.</summary>
    private static Result.ListValue WideNested() => new(Enumerable.Range(0, 64).Select(_ => (Result)ListOf(64)));

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task Cancellation_IsObservedAtAnAdmissionCharge_BeforeTheWalkCompletes(bool asynchronous)
    {
        using var cts = new CancellationTokenSource();
        var ticks = 0;
        var value = WideNested();
        var traversal = new ValueTraversalObservations
        {
            BeforeStructuralWorkCharge = ordinal => { if (ordinal == 2) cts.Cancel(); },
        };
        var operations = HostOperations.Create(
            HostOperation.Create("Value", (_, _) => value),
            HostOperation.Create("Tick", (_, _) => { ticks++; return Num(0); }));
        var ast = Program("Value, Tick()", operations);
        var observations = new EvaluationObservations { StructuralTraversal = traversal };

        if (asynchronous)
        {
            await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(ast,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), observations: observations,
                hostOperations: operations, cancellationToken: cts.Token));
        }
        else
        {
            Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(ast,
                observations: observations, hostOperations: operations, cancellationToken: cts.Token));
        }

        Assert.Equal(2, traversal.StructuralWorkChargeCount);
        Assert.InRange(traversal.NormalizeStructureExpansionCount, 2, 10);   // of 65 distinct structures
        Assert.Equal(0, ticks);
    }

    // ── T12: the host exception contract is unchanged ────────────────────────

    private sealed class HostFailure() : Exception("host failed");

    [Fact]
    public async Task HostExceptions_AndNullReturns_KeepTheirContract_UnderTightLimits()
    {
        var throwing = HostOperations.Create(HostOperation.Create("Value", (_, _) => throw new HostFailure()));
        var throwingAsync = HostOperations.Create(HostOperation.CreateAsync("Value", async (_, _) => { await Task.Yield(); throw new HostFailure(); }));
        var nulling = HostOperations.Create(HostOperation.Create("Value", (_, _) => null!));
        var limits = new EvaluationLimits { MaxCollectionItems = 1, MaxStringLength = 0 };

        Assert.Throws<HostFailure>(() => KatLangEngine.Run("Value", new RunOptions { HostOperations = throwing, EvaluationLimits = limits }));
        await Assert.ThrowsAsync<HostFailure>(() => KatLangEngine.RunAsync("Value", new RunOptions { HostOperations = throwingAsync, EvaluationLimits = limits }));
        var nullError = Assert.Throws<InvalidOperationException>(() =>
            KatLangEngine.Run("Value", new RunOptions { HostOperations = nulling, EvaluationLimits = limits }));
        Assert.Contains("returned null", nullError.Message);

        // A refusal is a structured resource failure, never an exception.
        var oversized = HostOperations.Create(HostOperation.Create("Value", (_, _) => new Result.Str("a")));
        var failure = Assert.IsType<RunResult.EvalFailure>(
            KatLangEngine.Run("Value", new RunOptions { HostOperations = oversized, EvaluationLimits = limits }));
        Assert.Equal(KatLangErrorCode.StringSizeLimitExceeded, Assert.Single(failure.Errors).Code);
    }

    // ── T13: terminality ─────────────────────────────────────────────────────

    [Theory]
    [InlineData("Value, Tick()")]
    [InlineData("Pick([a, b, c, d]) = 1\nPick(x) = 2\nPick(Value), Tick()")]
    [InlineData("Sum(*xs) = xs.sum\nSum(Make(1), Tick())")]
    [InlineData("if(Make(1) == 0, Tick(), Tick())")]
    [InlineData("[Id(Make(1)), Tick()]")]
    public void Refusal_IsTerminal_NoConsumerAbsorbsIt_AndNothingRunsAfterIt(string source)
    {
        var outcome = Observe(source, () => ListOf(4), Items(3));
        Assert.Equal("err items 3/4", outcome.Text);
        Assert.EndsWith("ticks=0", outcome.Effects);
    }

    [Fact]
    public void AdmissionStructuralWork_StepRefusalIsTerminalOnEveryRoute()
    {
        var value = WideNested();
        var outcome = Observe("Value, Tick()", () => value, new EvaluationLimits { MaxSteps = 1 });
        Assert.Equal("err steps 1", outcome.Text);
        Assert.Equal("calls=1 ticks=0", outcome.Effects);
    }

    [Fact]
    public void UndemandedHostArgument_IsNeverInvoked_SoReachesNoLimit()
    {
        var outcome = Observe("G(x, y) = y\nG(Make(1), 5)", () => ListOf(4), Items(3));
        Assert.Equal("ok 5", outcome.Text);
        Assert.Equal("calls=0 ticks=0", outcome.Effects);
    }

    // ── Related: the host-ARGUMENT call-reference scan ──────────────────────

    [Fact]
    public void HostArgumentBoundaryScan_ChargesOnlyTheInspectedPrefix()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });
        budget.DecideInvocationPlanRetention(programMayCapture: true);
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        var cell = Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("count"), [new Expr.Num(1)]), ctx, []);
        var adapter = Evaluator.ReferenceAdapterCell(cell, ctx);
        Assert.True(adapter.Value.TryGetReadyValue(out var ready));
        var reference = Assert.IsType<Result.CallReference>(ready.Value);
        Assert.Null(budget.TryChargeStep());
        var nested = new Result.ListValue(new Result[] { reference }.Concat(Enumerable.Repeat(Num(0), 8192)));

        var error = Evaluator.HostArgumentBoundaryError(new Result.ListValue([nested]), budget, observations: null);

        Assert.IsType<EvalError.TypeMismatch>(error);
        // One inspected slot and one completed nested verdict; the untouched suffix costs nothing.
        Assert.Equal(2, budget.ConsumedStructuralWorkUnits);
    }

    [Fact]
    public void HostArgumentBoundaryScan_UsesDepthBoundedContinuationStorage()
    {
        const int width = 4096;
        var value = new Result.ListValue(Enumerable.Range(0, width).Select(i => (Result)new Result.ListValue([Num(i)])));
        var budget = EvaluationBudget.Create(null);
        var observations = new ValueTraversalObservations();

        Assert.Null(Evaluator.HostArgumentBoundaryError(value, budget, observations));

        Assert.Equal(width * 2, budget.ConsumedStructuralWorkUnits);
        Assert.Equal(1, observations.CallReferenceScanPeakPendingFrames);
    }

    [Fact]
    public void HostArgumentBoundaryScan_IsChargedStructuralWork_PerCall()
    {
        // X holds 200 distinct one-item lists, and each of 50 host calls receives it. The boundary
        // scan that keeps call references out of host code is DAG-safe per call but repeats per call:
        // before SEC-01-FU it was uncharged (50 × 200 nested expansions for zero units). Each call now
        // charges one unit per nested structure plus one per slot inside it (2 × 200); the host
        // returns a scalar, so admission adds nothing.
        const string source = "Mk(i) = [i]\nX = map(range(1, 200), Mk)\nF(i) = Make(X)\nmap(range(1, 50), F).count";
        var outcome = Observe(source, () => Num(0));
        Assert.Equal("ok 50", outcome.Text);
        Assert.Equal(50 * 400, outcome.StructuralUnits);
        // Flat arguments and the run-result export charge nothing.
        Assert.Equal(0, Observe("A = [1, 2, 3]\nMake(A), Id(A)", () => Num(0)).StructuralUnits);
    }

    [Fact]
    public void HostArgumentBoundaryScan_ObservesCancellation()
    {
        using var cts = new CancellationTokenSource();
        var calls = 0;
        var traversal = new ValueTraversalObservations { BeforeStructuralWorkCharge = _ => cts.Cancel() };
        var operations = HostOperations.Create(HostOperation.Create("Make", (_, _) => { calls++; return Num(0); }, "x"));
        var ast = Program("Mk(i) = [i, i]\nX = map(range(1, 300), Mk)\nMake(X)", operations);
        Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(ast,
            observations: new EvaluationObservations { StructuralTraversal = traversal }, hostOperations: operations,
            cancellationToken: cts.Token));
        Assert.Equal(0, calls);
        Assert.Equal(1, traversal.StructuralWorkChargeCount);
    }

    // ── T14: the cumulative accounting policy ────────────────────────────────

    [Fact]
    public void HostReturns_AreAdmitted_ButNeverChargedAsMaterialized()
    {
        var shared = new Result.ListValue([ListOf(3), new Result.Str("abc"), ListOf(3)]);
        // Fresh calls, the cached property read twice, and a returned value reused across calls:
        // the run constructed nothing, so both cumulative counters stay at zero.
        // (The root's own four-row output capture is the only reservation, as with scalar returns.)
        const string reading = "Make(1), Make(2), Value, Value";
        var reads = Observe(reading, () => shared);
        var scalarReads = Observe(reading, () => Num(0));
        Assert.StartsWith("ok S[", reads.Text);
        Assert.Equal((scalarReads.Materialized, 0L), (reads.Materialized, reads.StringChars));
        Assert.Equal(4, reads.Materialized);
        Assert.Equal("calls=3 ticks=0", reads.Effects);

        // A returned ARGUMENT keeps the one reservation its construction made.
        var returnedArgument = Observe("Id([1, 2, 3])", () => shared);
        Assert.Equal(3, returnedArgument.Materialized);
        var literal = Observe("[1, 2, 3]", () => shared);
        Assert.Equal(literal.Materialized, returnedArgument.Materialized);

        // A collection the RUN builds from a host value is charged exactly like the same
        // construction from a program-built value (minus that value's own literal reservation).
        var spread = Observe("[Make(1)*]", () => ListOf(3));
        var programSpread = Observe("X = [1, 2, 3]\n[X*]", () => shared);
        Assert.Equal(programSpread.Materialized - 3, spread.Materialized);
        Assert.True(spread.Materialized >= 3);
    }

    [Fact]
    public void CumulativeBudgets_DoNotRefuseAHostReturn_ButStillBoundWhatTheRunBuilds()
    {
        var limits = new EvaluationLimits { MaxMaterializedItems = 2, MaxMaterializedStringChars = 1 };
        Assert.Equal("ok S[L[L[1, 2, 3], 'abc'], L[L[1, 2, 3], 'abc']]", Observe("Make(1), Id(Value)",
            () => new Result.ListValue([ListOf(3), new Result.Str("abc")]), limits).Text);
        Assert.Equal("err materialized 2", Observe("[Make(1)*]", () => ListOf(3), limits).Text);
    }
}
