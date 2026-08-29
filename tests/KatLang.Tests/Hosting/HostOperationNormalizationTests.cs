using System.Numerics;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests.Hosting;

/// <summary>
/// Canonicalization of SUCCESSFUL host-operation return values at the host boundary
/// (<c>Evaluator.NormalizeHostOperationValue</c>): host code may construct
/// representations ordinary KatLang evaluation would have canonicalized during value
/// construction (a singleton transparent sequence around an atom, redundant nested
/// empty-sequence structure), and every such value must enter evaluation — and the
/// zero-argument property cache — in the same canonical <see cref="Result"/>
/// representation an equal program-produced value has. Covered here: the synchronous
/// dispatch, the async twin's await site (genuine suspension included), synchronous
/// operations reached through the async evaluator, cache insertion order (normalized
/// BEFORE the value is stored, not re-normalized per lookup), argument-taking
/// operations, already-canonical pass-through, failure-path transparency, and
/// sync/async parity.
/// </summary>
public class HostOperationNormalizationTests
{
    private static readonly TimeSpan Timeout = TimeSpan.FromSeconds(45);

    private static Result Atom(Decimal128 value) => new Result.Atom(value);

    /// <summary>A fresh noncanonical singleton wrapper: KatLang-produced <c>(1)</c> is <c>Atom(1)</c>.</summary>
    private static Result SingletonSequenceAround(Result item) => new Result.SequenceValue([item]);

    /// <summary>
    /// A fresh deliberately noncanonical NESTED shape:
    /// <c>SequenceValue([SequenceValue([Atom(1), SequenceValue([Atom(2)])])])</c>,
    /// whose canonical form (per the <see cref="Result.Normalize"/> oracle) is the
    /// two-item sequence <c>(1, 2)</c>.
    /// </summary>
    private static Result NoncanonicalNested()
        => new Result.SequenceValue([
            new Result.SequenceValue([
                Atom(1),
                new Result.SequenceValue([Atom(2)]),
            ]),
        ]);

    /// <summary>
    /// A fresh noncanonical VISIBLE-EMPTY shape: <c>SequenceValue([SequenceValue([])])</c>
    /// — canonically the empty sequence <c>()</c>. Raw, its <c>ValueCount()</c> is 1 and
    /// its opened collection view has one item; canonical, both are 0.
    /// </summary>
    private static Result NoncanonicalNestedEmpty()
        => new Result.SequenceValue([new Result.SequenceValue([])]);

    private static void AssertAtomRepresentation(Result value, Decimal128 expected)
        => Assert.Equal(expected, Assert.IsType<Result.Atom>(value).Value);

    /// <summary>Bounded await so a wedged run fails the test instead of hanging the suite.</summary>
    private static async Task<T> Complete<T>(Task<T> task)
    {
        var completed = await Task.WhenAny(task, Task.Delay(Timeout));
        Assert.Same(task, completed);
        return await task;
    }

    private static async Task Reached(Task reached)
    {
        var completed = await Task.WhenAny(reached, Task.Delay(Timeout));
        Assert.Same(reached, completed);
    }

    /// <summary>
    /// Deterministic suspension gate (the AsyncHostOperationTests pattern): evaluation
    /// genuinely suspends awaiting the gate, so releasing a noncanonical value proves
    /// the REAL asynchronous dispatch path — never a synchronously completed fallback —
    /// performed the canonicalization.
    /// </summary>
    private sealed class HeldOperation
    {
        private readonly TaskCompletionSource<Result> _gate = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private readonly TaskCompletionSource _reached = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private int _invocations;

        public int Invocations => Volatile.Read(ref _invocations);

        public Task ReachedTask => _reached.Task;

        public void Release(Result value) => _gate.TrySetResult(value);

        public void Fail(Exception exception) => _gate.TrySetException(exception);

        public async ValueTask<Result> InvokeAsync(IReadOnlyList<Result> args, CancellationToken cancellationToken)
        {
            Interlocked.Increment(ref _invocations);
            _reached.TrySetResult();
            return await _gate.Task;
        }
    }

    /// <summary>
    /// Records the exact <see cref="ZeroArgPropertyResult"/> each cache-miss evaluation
    /// produced — the very object the wrapped run-scoped cache STORES — so a test can
    /// distinguish "normalized before insertion" (the recorded stored value is already
    /// canonical) from "raw value cached, normalized independently after every lookup"
    /// (the recorded stored value would be the raw host shape).
    /// </summary>
    private sealed class RecordingZeroArgPropertyResultCache : IZeroArgPropertyResultCache
    {
        private readonly RunScopedZeroArgPropertyResultCache _inner = new();

        public List<ZeroArgPropertyResult> StoredValues { get; } = [];

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
            => _inner.GetOrEvaluate(execution, () =>
            {
                var evaluated = evaluate();
                if (evaluated.IsOk)
                    StoredValues.Add(evaluated.Value);
                return evaluated;
            });
    }

    /// <summary>Async counterpart of <see cref="RecordingZeroArgPropertyResultCache"/>.</summary>
    private sealed class RecordingAsyncZeroArgPropertyResultCache : IAsyncZeroArgPropertyResultCache
    {
        private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

        public List<ZeroArgPropertyResult> StoredValues { get; } = [];

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
            => _inner.GetOrEvaluate(execution, () =>
            {
                var evaluated = evaluate();
                if (evaluated.IsOk)
                    StoredValues.Add(evaluated.Value);
                return evaluated;
            });

        public ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
            ZeroArgPropertyExecution execution,
            Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
            => _inner.GetOrEvaluateAsync(execution, async () =>
            {
                var evaluated = await evaluateAsync();
                if (evaluated.IsOk)
                    StoredValues.Add(evaluated.Value);
                return evaluated;
            });
    }

    private static Expr ParsedAst(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    // ── 1. Synchronous singleton-sequence return ────────────────────────────

    [Fact]
    public void SyncOperation_SingletonSequenceReturn_IsCanonicalizedToTheAtom()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => SingletonSequenceAround(Atom(1)))),
        };

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data", options));

        // Direct representation assert: the raw host SequenceValue([Atom(1)]) must have
        // become the SAME canonical shape KatLang-produced (1) has — the bare atom.
        AssertAtomRepresentation(success.Value, 1m);
    }

    [Fact]
    public void SyncOperation_SingletonSequenceReturn_ParticipatesInLanguageEquality()
    {
        // The motivating M2 symptom: `Data == 1` was false for a host-returned
        // singleton sequence even though it is true for the equal program value.
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => SingletonSequenceAround(Atom(1)))),
        };

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data == 1", options));
        Assert.Equal("1", success.ToDisplayString());
    }

    [Fact]
    public void SyncOperation_ThroughPublicEvaluatorEntry_ReturnsTheCanonicalRepresentation()
    {
        var operations = HostOperations.Create(
            HostOperation.Create("Data", (_, _) => SingletonSequenceAround(Atom(1))));

        var result = Evaluator.Run(ParsedAst("Data", operations), operations, limits: null, CancellationToken.None);

        Assert.True(result.IsOk);
        AssertAtomRepresentation(result.Value, 1m);
    }

    // ── 2. Asynchronous singleton-sequence return (genuine suspension) ──────

    [Fact]
    public async Task AsyncOperation_SingletonSequenceReturn_IsCanonicalizedAfterGenuineSuspension()
    {
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        // Reaching the gate proves the run is suspended inside the REAL async host
        // dispatch (only asynchronous operations route there); the noncanonical value
        // is delivered through the resumption.
        var task = KatLangEngine.RunAsync("Data", options);
        await Reached(held.ReachedTask);
        Assert.False(task.IsCompleted);
        held.Release(SingletonSequenceAround(Atom(1)));

        var success = Assert.IsType<RunResult.Success>(await Complete(task));
        AssertAtomRepresentation(success.Value, 1m);
        Assert.Equal(1, held.Invocations);
    }

    // ── Synchronous operation reached through the ASYNC evaluator ───────────

    [Fact]
    public async Task SyncOperation_OnTheAsyncTwinPath_IsCanonicalizedThroughTheSharedSyncDispatch()
    {
        // An asynchronous operation in the CONFIGURATION routes the whole run through
        // the async twin family even though the program only uses the synchronous
        // operation; the sync NativeCall is a sync-delegable twin leaf, so this pins
        // that the shared synchronous dispatch canonicalizes on that path too.
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => SingletonSequenceAround(Atom(1))),
                HostOperation.CreateAsync("UnusedAsyncRouteForcer", (_, _) => ValueTask.FromResult(Atom(0)))),
        };

        var success = Assert.IsType<RunResult.Success>(
            await Complete(KatLangEngine.RunAsync("Data", options)));
        AssertAtomRepresentation(success.Value, 1m);
    }

    // ── 3. Nested noncanonical shapes (Normalize() oracle) ──────────────────

    [Fact]
    public void SyncOperation_NestedNoncanonicalShape_MatchesTheNormalizeOracle()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => NoncanonicalNested())),
        };

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data", options));

        // The canonical expectation comes from the existing Normalize() oracle, and
        // ValueComparer is representation-exact (a singleton sequence never equals its
        // element), so this assert fails on any surviving raw structure.
        var expected = NoncanonicalNested().Normalize();
        Assert.True(Result.ValueComparer.Equals(expected, success.Value));

        // Direct structural spot-check of the same expectation: (1, 2).
        var sequence = Assert.IsType<Result.SequenceValue>(success.Value);
        Assert.Equal(2, sequence.Items.Count);
        AssertAtomRepresentation(sequence.Items[0], 1m);
        AssertAtomRepresentation(sequence.Items[1], 2m);
    }

    [Fact]
    public void SyncOperation_NestedEmptyShape_HasCanonicalVisibleEmptyBehavior()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => NoncanonicalNestedEmpty())),
        };

        // Count anomaly: raw SequenceValue([SequenceValue([])]) opens to ONE item where
        // the canonical empty sequence opens to zero.
        var counted = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data.count", options));
        Assert.Equal("0", counted.ToDisplayString());

        // Visible-empty equivalence: the host-produced value must behave exactly like
        // the equivalent program-produced empty (`A = ()` accessed as a row) — same
        // canonical representation (no surviving nested structure), same root
        // emission, same display.
        var baseline = Assert.IsType<RunResult.Success>(KatLangEngine.Run("A = ()\nA"));
        var bare = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data", options));
        var empty = Assert.IsType<Result.SequenceValue>(bare.Value);
        Assert.Empty(empty.Items);
        Assert.True(Result.ValueComparer.Equals(baseline.Value, bare.Value));
        Assert.Equal(baseline.EmittedCount, bare.EmittedCount);
        Assert.Equal(baseline.ToDisplayString(), bare.ToDisplayString());
        Assert.Empty(bare.Atoms);
    }

    [Fact]
    public async Task AsyncOperation_NestedNoncanonicalShape_MatchesTheNormalizeOracle()
    {
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data", options);
        await Reached(held.ReachedTask);
        held.Release(NoncanonicalNested());

        var success = Assert.IsType<RunResult.Success>(await Complete(task));
        Assert.True(Result.ValueComparer.Equals(NoncanonicalNested().Normalize(), success.Value));
        Assert.Equal(2, Assert.IsType<Result.SequenceValue>(success.Value).Items.Count);
    }

    [Fact]
    public async Task AsyncOperation_NestedEmptyShape_IsCanonicalBeforeCaching_WithoutChangingRowArity()
    {
        var held = new HeldOperation();
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("Data", held.InvokeAsync));
        var cache = new RecordingAsyncZeroArgPropertyResultCache();

        var task = Evaluator.RunCountedAsync(
            ParsedAst("Data", operations), cache, limits: null, operations, CancellationToken.None).AsTask();
        await Reached(held.ReachedTask);
        Assert.False(task.IsCompleted);
        held.Release(NoncanonicalNestedEmpty());

        var result = await Complete(task);
        Assert.True(result.IsOk);

        // The root has one written `Data` output row, so its body arity remains one.
        // Value-sensitive consumers still see the canonical empty value (`Data.count`
        // is covered above); M2 must not erase the written row.
        Assert.Equal(1, result.Value.EmittedCount);
        Assert.Empty(Assert.IsType<Result.SequenceValue>(result.Value.Value).Items);

        // The cache stores the canonical VALUE, but its metadata is the wrapper
        // algorithm body's one written output row. That row contributes one slot even
        // when its value is (), by the existing arity algebra; M2 must not rewrite it.
        var stored = Assert.Single(cache.StoredValues);
        Assert.Equal(1, stored.EmittedCount);
        Assert.Empty(Assert.IsType<Result.SequenceValue>(stored.Value).Items);
        Assert.Equal(1, held.Invocations);
    }

    [Fact]
    public async Task AsyncNativeCountedBoundary_DerivesCountFromTheNormalizedValue()
    {
        var held = new HeldOperation();
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("Data", held.InvokeAsync));

        // A direct host-built NativeCall reaches the precise async counted boundary
        // before wrapper-row aggregation. Raw nested-empty ValueCount() is 1; its
        // normalized value count is 0.
        var task = Evaluator.RunCountedAsync(
            new Expr.NativeCall(HostOperations.NativeNamePrefix + "Data", []),
            new RecordingAsyncZeroArgPropertyResultCache(),
            limits: null,
            operations,
            CancellationToken.None).AsTask();
        await Reached(held.ReachedTask);
        held.Release(NoncanonicalNestedEmpty());

        var result = await Complete(task);
        Assert.True(result.IsOk);
        Assert.Equal(0, result.Value.EmittedCount);
        Assert.Empty(Assert.IsType<Result.SequenceValue>(result.Value.Value).Items);
        Assert.Equal(1, held.Invocations);
    }

    // ── 4. Zero-argument property cache stores the CANONICAL value ──────────

    [Fact]
    public void SyncZeroArgCache_StoresTheNormalizedValue_AndHitsServeIt()
    {
        var invocations = 0;
        var operations = HostOperations.Create(
            HostOperation.Create("Data", (_, _) =>
            {
                Interlocked.Increment(ref invocations);
                return SingletonSequenceAround(Atom(7));
            }));
        var cache = new RecordingZeroArgPropertyResultCache();

        // Two property-style rows: miss + hit under the existing cache contract.
        var result = Evaluator.RunCounted(
            ParsedAst("Data\nData", operations), cache, limits: null, operations, CancellationToken.None);

        Assert.True(result.IsOk);
        Assert.Equal(1, invocations);

        // The recorded value IS the object the run-scoped cache stored on the miss:
        // it must already be canonical, proving normalization happened BEFORE the
        // insertion — not independently after each lookup.
        var stored = Assert.Single(cache.StoredValues);
        AssertAtomRepresentation(stored.Value, 7m);
        Assert.Equal(1, stored.EmittedCount);

        // Both output rows — the miss row and the cache-hit row — are the canonical atom.
        var output = Assert.IsType<Result.SequenceValue>(result.Value.Value);
        Assert.Equal(2, output.Items.Count);
        AssertAtomRepresentation(output.Items[0], 7m);
        AssertAtomRepresentation(output.Items[1], 7m);
        Assert.Same(stored.Value, output.Items[0]);
        Assert.Same(output.Items[0], output.Items[1]);
    }

    [Fact]
    public async Task AsyncZeroArgCache_StoresTheNormalizedValue_AndHitsServeIt()
    {
        var held = new HeldOperation();
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("Data", held.InvokeAsync));
        var cache = new RecordingAsyncZeroArgPropertyResultCache();

        var task = Evaluator.RunCountedAsync(
            ParsedAst("Data\nData", operations), cache, limits: null, operations, CancellationToken.None).AsTask();
        await Reached(held.ReachedTask);
        Assert.False(task.IsCompleted);
        held.Release(SingletonSequenceAround(Atom(7)));

        var result = await Complete(task);

        Assert.True(result.IsOk);
        Assert.Equal(1, held.Invocations);

        var stored = Assert.Single(cache.StoredValues);
        AssertAtomRepresentation(stored.Value, 7m);
        Assert.Equal(1, stored.EmittedCount);

        var output = Assert.IsType<Result.SequenceValue>(result.Value.Value);
        Assert.Equal(2, output.Items.Count);
        AssertAtomRepresentation(output.Items[0], 7m);
        AssertAtomRepresentation(output.Items[1], 7m);
        Assert.Same(stored.Value, output.Items[0]);
        Assert.Same(output.Items[0], output.Items[1]);
    }

    [Fact]
    public void ExplicitZeroArgCall_BypassingTheCache_StillCanonicalizes()
    {
        // Data() bypasses the property cache entirely, so canonicalization must live
        // at the dispatch, not on the cache path.
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => SingletonSequenceAround(Atom(5)))),
        };

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data()", options));
        AssertAtomRepresentation(success.Value, 5m);
    }

    [Fact]
    public async Task AsyncExplicitZeroArgCall_BypassingTheCache_StillCanonicalizesAfterSuspension()
    {
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data()", options);
        await Reached(held.ReachedTask);
        Assert.False(task.IsCompleted);
        held.Release(SingletonSequenceAround(Atom(5)));

        var success = Assert.IsType<RunResult.Success>(await Complete(task));
        AssertAtomRepresentation(success.Value, 5m);
        Assert.Equal(1, held.Invocations);
    }

    // ── 5. Argument-taking operations ───────────────────────────────────────

    [Fact]
    public void SyncArgumentTakingOperation_ReturnValue_IsCanonicalized()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create(
                    "Wrap",
                    (args, _) => SingletonSequenceAround(Atom(((Result.Atom)args[0]).Value * 2)),
                    "x")),
        };

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Wrap(21)", options));
        AssertAtomRepresentation(success.Value, 42m);
    }

    [Fact]
    public async Task AsyncArgumentTakingOperation_ReturnValue_IsCanonicalized()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync(
                    "Wrap",
                    (args, _) => ValueTask.FromResult(
                        SingletonSequenceAround(Atom(((Result.Atom)args[0]).Value * 2))),
                    "x")),
        };

        var success = Assert.IsType<RunResult.Success>(
            await Complete(KatLangEngine.RunAsync("Wrap(21)", options)));
        AssertAtomRepresentation(success.Value, 42m);
    }

    [Fact]
    public void SyncOperation_AsDirectMapCallback_NormalizesBeforeTheBuiltinConsumesItsResult()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Wrap", (args, _) => SingletonSequenceAround(args[0]), "x")),
        };

        var success = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("[1, 2].map(Wrap)", options));
        var list = Assert.IsType<Result.ListValue>(success.Value);
        AssertAtomRepresentation(list.Items[0], 1m);
        AssertAtomRepresentation(list.Items[1], 2m);
    }

    [Fact]
    public async Task AsyncOperation_AsDirectMapCallback_NormalizesAfterGenuineSuspension()
    {
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Wrap", held.InvokeAsync, "x")),
        };

        var task = KatLangEngine.RunAsync("[3].map(Wrap)", options);
        await Reached(held.ReachedTask);
        Assert.False(task.IsCompleted);
        held.Release(SingletonSequenceAround(Atom(6)));

        var success = Assert.IsType<RunResult.Success>(await Complete(task));
        var list = Assert.IsType<Result.ListValue>(success.Value);
        AssertAtomRepresentation(Assert.Single(list.Items), 6m);
        Assert.Equal(1, held.Invocations);
    }

    // ── 6. Already-canonical values pass through unchanged ──────────────────

    [Fact]
    public void SyncOperation_AlreadyCanonicalSequence_PassesThroughByIdentity()
    {
        // Normalize() returns an already-canonical value AS ITSELF, and the single-row
        // wrapper/root boundaries pass the value through, so the exact host object
        // reaches the result — nothing is wrapped, rebuilt, or re-shaped.
        var canonical = new Result.SequenceValue([Atom(1), new Result.SequenceValue([Atom(2), Atom(3)])]);
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => canonical)),
        };

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data", options));
        Assert.Same(canonical, success.Value);
    }

    [Fact]
    public void SyncOperation_ListValues_KeepTheirExactOpacity()
    {
        // List structure is exact and never singleton-collapsed: [7] stays a one-item
        // list, [] stays the empty list (distinct from ()), and a sequence INSIDE a
        // list still canonicalizes under the ordinary Normalize rules.
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Single", (_, _) => new Result.ListValue([Atom(7)])),
                HostOperation.Create("Empty", (_, _) => new Result.ListValue([])),
                HostOperation.Create("Mixed", (_, _) => new Result.ListValue([SingletonSequenceAround(Atom(9))]))),
        };

        var single = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Single", options));
        var singleList = Assert.IsType<Result.ListValue>(single.Value);
        AssertAtomRepresentation(Assert.Single(singleList.Items), 7m);

        var empty = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Empty", options));
        Assert.Empty(Assert.IsType<Result.ListValue>(empty.Value).Items);
        Assert.Equal(1, empty.EmittedCount);

        var mixed = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Mixed", options));
        var mixedList = Assert.IsType<Result.ListValue>(mixed.Value);
        AssertAtomRepresentation(Assert.Single(mixedList.Items), 9m);
    }

    [Fact]
    public void SyncOperation_StringValue_PassesThroughUnchangedByIdentity()
    {
        var text = new Result.Str("(1, 2) is text, not structure");
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => text)),
        };

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data", options));
        Assert.Same(text, success.Value);
        Assert.Equal("(1, 2) is text, not structure", Assert.IsType<Result.Str>(success.Value).Value);
    }

    [Fact]
    public void SyncOperation_SharedNoncanonicalDag_NormalizesOnceAndPreservesSharing()
    {
        var shared = new Result.ListValue([SingletonSequenceAround(Atom(4))]);
        var raw = new Result.SequenceValue([shared, shared]);
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => raw)),
        };

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data", options));
        var normalizedRoot = Assert.IsType<Result.SequenceValue>(success.Value);
        Assert.Equal(2, normalizedRoot.Items.Count);
        Assert.Same(normalizedRoot.Items[0], normalizedRoot.Items[1]);
        Assert.NotSame(shared, normalizedRoot.Items[0]);
        var normalizedShared = Assert.IsType<Result.ListValue>(normalizedRoot.Items[0]);
        AssertAtomRepresentation(Assert.Single(normalizedShared.Items), 4m);
    }

    [Fact]
    public async Task AsyncOperation_AlreadyCanonicalValue_IsSemanticallyUnchanged()
    {
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var canonical = new Result.SequenceValue([Atom(1), Atom(2)]);
        var task = KatLangEngine.RunAsync("Data", options);
        await Reached(held.ReachedTask);
        held.Release(canonical);

        var success = Assert.IsType<RunResult.Success>(await Complete(task));
        Assert.Same(canonical, success.Value);
    }

    // ── 7. Failure behavior stays untouched ─────────────────────────────────

    [Fact]
    public void SyncHostException_StillPropagatesByIdentity()
    {
        var exception = new InvalidDataException("host database offline");
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => throw exception)),
        };

        var observed = Assert.Throws<InvalidDataException>(() => KatLangEngine.Run("Data", options));
        Assert.Same(exception, observed);
    }

    [Fact]
    public async Task AsyncFaultedAwaitable_StillPropagatesByIdentity()
    {
        var exception = new InvalidDataException("pre-faulted awaitable");
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync(
                    "Data",
                    (_, _) => new ValueTask<Result>(Task.FromException<Result>(exception)))),
        };

        var observed = await Assert.ThrowsAsync<InvalidDataException>(
            () => Complete(KatLangEngine.RunAsync("Data", options)));
        Assert.Same(exception, observed);
    }

    [Fact]
    public async Task CancelledWhileSuspended_WinsOverANoncanonicalRelease()
    {
        // A token cancelled during suspension is honored on resumption BEFORE the
        // successful-value boundary: the run is cancelled, and the noncanonical value
        // is discarded rather than normalized or surfaced.
        using var cts = new CancellationTokenSource();
        var held = new HeldOperation();
        var options = new RunOptions
        {
            EvaluationCancellationToken = cts.Token,
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data", options);
        await Reached(held.ReachedTask);
        cts.Cancel();
        held.Release(SingletonSequenceAround(Atom(1)));

        var observed = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Complete(task));
        Assert.Equal(cts.Token, observed.CancellationToken);
    }

    [Fact]
    public async Task CancelledWhileSuspended_WinsOverANullRelease()
    {
        using var cts = new CancellationTokenSource();
        var held = new HeldOperation();
        var options = new RunOptions
        {
            EvaluationCancellationToken = cts.Token,
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data", options);
        await Reached(held.ReachedTask);
        cts.Cancel();
        held.Release(null!);

        var observed = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Complete(task));
        Assert.Equal(cts.Token, observed.CancellationToken);
    }

    [Fact]
    public async Task FaultAfterSuspension_WinsOverConcurrentCancellationByIdentity()
    {
        using var cts = new CancellationTokenSource();
        var exception = new InvalidDataException("fault after cancellation request");
        var held = new HeldOperation();
        var options = new RunOptions
        {
            EvaluationCancellationToken = cts.Token,
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data", options);
        await Reached(held.ReachedTask);
        cts.Cancel();
        held.Fail(exception);

        // Await faults before the post-resumption cancellation observation. This is the
        // pre-M2 precedence and proves normalization did not catch or transform faults.
        var observed = await Assert.ThrowsAsync<InvalidDataException>(() => Complete(task));
        Assert.Same(exception, observed);
    }

    // ── 8. Sync/async parity ────────────────────────────────────────────────

    [Fact]
    public async Task SyncAndAsyncOperations_WithTheSameNoncanonicalReturns_ProduceTheSameCanonicalValue()
    {
        const string source = "Data\nData()\nWrap(3)";

        var syncOptions = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => NoncanonicalNested()),
                HostOperation.Create("Wrap", (args, _) => SingletonSequenceAround(args[0]), "x")),
        };
        var asyncOptions = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", (_, _) => ValueTask.FromResult(NoncanonicalNested())),
                HostOperation.CreateAsync(
                    "Wrap",
                    (args, _) => ValueTask.FromResult(SingletonSequenceAround(args[0])),
                    "x")),
        };

        var syncResult = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, syncOptions));
        var asyncResult = Assert.IsType<RunResult.Success>(
            await Complete(KatLangEngine.RunAsync(source, asyncOptions)));

        Assert.True(Result.ValueComparer.Equals(syncResult.Value, asyncResult.Value));
        Assert.Equal(syncResult.ToDisplayString(), asyncResult.ToDisplayString());

        // Both match the canonical expectation for the three rows: two rows of (1, 2)
        // and the atom 3 (the Wrap singleton wrapper collapses onto its argument).
        var expectedRow = NoncanonicalNested().Normalize();
        foreach (var value in new[] { syncResult.Value, asyncResult.Value })
        {
            var rows = Assert.IsType<Result.SequenceValue>(value);
            Assert.Equal(3, rows.Items.Count);
            Assert.True(Result.ValueComparer.Equals(expectedRow, rows.Items[0]));
            Assert.True(Result.ValueComparer.Equals(expectedRow, rows.Items[1]));
            AssertAtomRepresentation(rows.Items[2], 3m);
        }
    }
}
