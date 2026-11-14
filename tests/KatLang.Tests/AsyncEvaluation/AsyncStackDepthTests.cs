namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Stack-shape safety of the async twin family. The synchronous evaluator's
/// structured-failure boundaries are checked by its own pins; these
/// tests characterize the TWIN path, whose synchronously-completing async frames are
/// larger than their synchronous counterparts:
///
/// <list type="bullet">
///   <item>Where a twin is about to enter an invocation level, a row-loop funnel, or a need
///   cell's computation with the host stack below the runtime's reserve, it continues on a
///   fresh thread-pool stack (<see cref="KatLang.Evaluation.StackHop"/>, 2026-11-14) instead of
///   stopping with <see cref="EvalError.EvaluationStackExhausted"/>. On the documented
///   minimum 1 MiB thread the heaviest recursion shapes therefore reach the DETERMINISTIC depth
///   verdict, and recursion the synchronous evaluator stops on that thread completes. Such a
///   run completes asynchronously, so these tests await it rather than requiring synchronous
///   completion.</item>
///   <item>Pure expression SPINES stay iterative in the twin machine, so a deep flat
///   chain evaluates on a 384 KiB thread exactly as the synchronous machine's pin
///   demonstrates for the synchronous path — synchronously, with no hop.</item>
///   <item>A reduced dynamic depth ceiling reached before either host-stack backstop
///   gives the same deterministic verdict.</item>
/// </list>
/// </summary>
public class AsyncStackDepthTests
{
    private const int OneMiB = 1_048_576;

    // A hang guard for runs that continue on the thread pool, never a latency claim.
    private static readonly TimeSpan HopWaitLimit = TimeSpan.FromSeconds(120);

    /// <summary>
    /// The shape the 2026-11-14 audit measured: at <c>a4b545e8</c> the twin route stopped it with
    /// the stack backstop from <c>F(42)</c> on a 1 MiB harness thread, where the synchronous
    /// routes completed up to <c>F(101)</c>.
    /// </summary>
    private const string PlainRecursion = "F(n) = if(n == 0, 0, F(n - 1) + 1)\n";

    private static EvalResult<Evaluator.CountedResult> RunTwinSynchronouslyCompleting(
        Expr ast, EvaluationLimits? limits = null)
    {
        var pending = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache(), limits);

        // Pass-through seam and a shape that never runs short of stack: the twin path
        // completes synchronously, so the whole spine consumed the CURRENT thread's stack —
        // which is exactly what these probes measure.
        Assert.True(pending.IsCompleted);
        return pending.GetAwaiter().GetResult();
    }

    /// <summary>
    /// The twin path STARTED on the calling thread and awaited to completion: a run that
    /// outgrows that thread's stack continues on the thread pool and completes there.
    /// </summary>
    private static EvalResult<Evaluator.CountedResult> RunTwinToCompletion(
        Expr ast, EvaluationLimits? limits = null)
    {
        var pending = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache(), limits).AsTask();
        Assert.True(pending.Wait(HopWaitLimit), "the twin run did not complete");
        return pending.Result;
    }

    private static HostOperations UnusedAsyncOperation()
        => HostOperations.Create(
            HostOperation.CreateAsync("Ping", (_, _) => ValueTask.FromResult<Result>(new Result.Atom(1))));

    private static Expr ParseWith(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    /// <summary>
    /// The public host-operation route, STARTED on a fresh 1 MiB thread (the documented
    /// minimum) and then awaited: the run is not required to complete on that thread.
    /// </summary>
    private static async Task<EvalResult<Result>> RunPublicAsyncFromOneMiBThread(Expr ast, HostOperations operations)
    {
        var pending = AstStructuralDepthProcessTests.RunOnThreadWithStack(
            OneMiB, () => Evaluator.RunAsync(ast, operations, limits: null, randomSeed: null, CancellationToken.None));
        return await pending.WaitAsync(HopWaitLimit);
    }

    [Fact]
    public void TwinPath_DepthLimitedRecursion_AtReducedDeterministicCeiling_MatchesSyncVerdict()
    {
        // At a reduced deterministic ceiling the twin path's larger frames still fit
        // any supported stack comfortably, so the verdict is the DETERMINISTIC depth
        // error on both paths — exact equality.
        const string source = "F(0) = 0\nF(n) = F(n - 1)\nF(500)";
        var ast = AsyncEvaluationHarness.Ast(source);
        var limits = new EvaluationLimits { MaxDepth = 32 };

        var sync = Evaluator.RunCounted(ast, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(), limits);
        var async = RunTwinSynchronouslyCompleting(ast, limits);

        Assert.Equal("err evaluationDepthExceeded", AsyncEvaluationHarness.NeutralOf(sync));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
    }

    [Fact]
    public void TwinPath_DepthLimitedRecursion_AtDefaultCeilingOnDefaultThread_IsTheDeterministicVerdict()
    {
        // The twin family's synchronously-completing async frames are larger than their
        // synchronous counterparts, so on a default-sized thread a deep chain can run short
        // of host stack BEFORE the deterministic 128-level ceiling. Until 2026-11-14 that was
        // the structured stack-exhausted error; the twin now continues on a fresh stack, so
        // it reaches the deterministic depth verdict the synchronous path reports.
        const string source = "F(0) = 0\nF(n) = F(n - 1)\nF(500)";
        var ast = AsyncEvaluationHarness.Ast(source);

        var sync = Evaluator.RunCounted(ast);
        var async = RunTwinToCompletion(ast);

        Assert.True(sync.IsError);
        Assert.True(async.IsError);
        Assert.Equal("evaluationDepthExceeded", SemanticExplorerHarness.ErrorCategory(sync.Error));
        Assert.Equal("evaluationDepthExceeded", SemanticExplorerHarness.ErrorCategory(async.Error));
    }

    /// <summary>
    /// The four measured heaviest recursion shapes from the depth-ceiling calibration
    /// (collection-callback recursion, recursion through <c>if</c>, dotted recursion,
    /// plain clause recursion), each driven to the deterministic default ceiling.
    /// </summary>
    public static TheoryData<string, string> HeaviestRecursionShapes() => new()
    {
        { "plain-clause", "F(0) = 0\nF(n) = F(n - 1)\nF(500)" },
        { "through-if", "F(n) = if(n > 0, F(n - 1), 0)\nF(500)" },
        { "dotted", "Lib = {public F(n) = if(n > 0, Lib.F(n - 1), 0)}\nLib.F(500)" },
        { "collection-callback", "F(n) = if(n > 0, [n - 1].map(F).first, 0)\nF(500)" },
    };

    [Theory]
    [MemberData(nameof(HeaviestRecursionShapes))]
    public void TwinPath_HeaviestShapes_OnOneMiBThread_ReachTheDeterministicDepthVerdict(string shapeId, string source)
    {
        _ = shapeId;
        var ast = AsyncEvaluationHarness.Ast(source);

        EvalResult<Evaluator.CountedResult>? syncOutcome = null;
        EvalResult<Evaluator.CountedResult>? asyncOutcome = null;

        AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () =>
        {
            syncOutcome = Evaluator.RunCounted(ast);
        });

        AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () =>
        {
            asyncOutcome = RunTwinToCompletion(ast);
        });

        // Both paths: a structured outcome, never an unhandled overflow (an overflow
        // would have terminated the process before these assertions ran). The synchronous
        // path may stop with the stack backstop on this minimum-supported stack (Q-09a);
        // the twin continues each invocation that finds the stack low on a fresh one, so it
        // reaches the deterministic depth verdict.
        Assert.True(syncOutcome!.Value.IsError);
        Assert.True(asyncOutcome!.Value.IsError);

        var syncCategory = SemanticExplorerHarness.ErrorCategory(syncOutcome.Value.Error);
        Assert.Contains(syncCategory, new[] { "evaluationDepthExceeded", "evaluationStackExhausted" });
        Assert.Equal("evaluationDepthExceeded", SemanticExplorerHarness.ErrorCategory(asyncOutcome.Value.Error));
    }

    [Fact]
    public void TwinPath_DeepFlatExpressionSpine_On384KiBThread_MatchesSync()
    {
        // 250 additions: a flat operator chain at the language's supported chain depth
        // class. The twin spine machine is iterative like the synchronous one, so this
        // must evaluate on the same 384 KiB thread the synchronous iterative-spine pin
        // uses — one async driver frame, O(1) stack per spine node, and no stack hop.
        var source = string.Join(" + ", Enumerable.Repeat("1", 250));
        var ast = AsyncEvaluationHarness.Ast(source);
        var sync = Evaluator.RunCounted(ast);
        Assert.True(sync.IsOk);

        EvalResult<Evaluator.CountedResult>? asyncOutcome = null;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(393_216, () =>
        {
            asyncOutcome = RunTwinSynchronouslyCompleting(ast);
        });

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(asyncOutcome!.Value));
    }

    [Fact]
    public void TwinPath_NestedAlgorithmBodies_OnOneMiBThread_Complete()
    {
        // Nested zero-declaration algorithm bodies at the structural ceiling (2 counted
        // units per level plus an inner unary — the deepest recursive block shape),
        // host-built because the parser's own nesting budget rejects the equivalent
        // brace source before evaluation is reached. Every body passes through the twin's
        // row-loop funnel, which continues on a fresh stack when the thread runs low, so the
        // twin evaluates it on this minimum-supported stack.
        Expr ast = new Expr.Unary(UnaryOp.Minus, new Expr.Num(-42));
        for (var level = 0; level < (EvaluationLimits.MaxSupportedAstDepth - 1) / 2; level++)
        {
            ast = new Expr.AlgorithmExpr(new Algorithm.User(
                Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: [ast]));
        }

        var sync = Evaluator.RunCounted(ast);
        Assert.True(sync.IsOk, AsyncEvaluationHarness.NeutralOf(sync));

        EvalResult<Evaluator.CountedResult>? asyncOutcome = null;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () =>
        {
            asyncOutcome = RunTwinToCompletion(ast);
        });

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(asyncOutcome!.Value));
    }

    /// <summary>
    /// F8 — the PUBLIC contract, as documented on <see cref="EvaluationLimits.MaxDepth"/>,
    /// the host-operation <c>Evaluator.RunAsync</c> overload, and
    /// <c>KatLangEngine.RunAsync</c>: a configuration with an asynchronous host operation
    /// takes the twin path even when the operation is never called. Its recursion is not
    /// shortened by the twin's larger frames: an invocation that finds the stack low continues
    /// on a fresh one, so an unbounded recursion ends with the deterministic depth verdict —
    /// never a process crash. The synchronous evaluator's verdict on the same thread is either
    /// member of the resource-limit family (Q-09a); no host-stack depth is pinned.
    /// </summary>
    [Theory]
    [MemberData(nameof(HeaviestRecursionShapes))]
    public async Task PublicAsyncHostOperationSurface_DeepRecursion_ReachesTheDeterministicDepthVerdict(string shapeId, string source)
    {
        _ = shapeId;
        var operations = UnusedAsyncOperation();
        var ast = ParseWith(source, operations);

        var asyncOutcome = await RunPublicAsyncFromOneMiBThread(ast, operations);

        Assert.True(asyncOutcome.IsError);
        var asyncError = asyncOutcome.Error;
        Assert.True(asyncError.IsResourceLimit);
        Assert.Equal(KatLangErrorCode.EvaluationDepthExceeded, asyncError.Code);

        EvalResult<Result>? syncOutcome = null;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () =>
        {
            syncOutcome = Evaluator.Run(
                ast,
                HostOperations.Create(HostOperation.Create("Ping", (_, _) => new Result.Atom(1))),
                limits: null,
                randomSeed: null,
                CancellationToken.None);
        });
        Assert.True(syncOutcome!.Value.IsError);
        Assert.True(syncOutcome.Value.Error.IsResourceLimit);
        Assert.Contains(
            syncOutcome.Value.Error.Code,
            new[] { KatLangErrorCode.EvaluationStackExhausted, KatLangErrorCode.EvaluationDepthExceeded });
    }

    // ── The stack hop on the documented minimum stack (2026-11-14) ───────────

    [Fact]
    public async Task UnusedAsyncHostOperation_PlainRecursionPastTheSynchronousStack_OnOneMiBThread_Completes()
    {
        // F(120) is beyond what the synchronous routes complete on this thread (the audit
        // measured F(101)) and far beyond the twin's own synchronously-completing frames
        // (F(41)); the twin now continues on fresh stacks and completes it.
        var operations = UnusedAsyncOperation();
        var outcome = await RunPublicAsyncFromOneMiBThread(ParseWith(PlainRecursion + "F(120)", operations), operations);

        Assert.True(outcome.IsOk, outcome.IsError ? outcome.Error.ToString() : null);
        Assert.Equal(new Result.Atom(120), outcome.Value);
    }

    [Fact]
    public async Task UnusedAsyncHostOperation_RunawayPlainRecursion_OnOneMiBThread_StopsAtTheDeterministicDepthLimit()
    {
        var operations = UnusedAsyncOperation();
        var outcome = await RunPublicAsyncFromOneMiBThread(ParseWith(PlainRecursion + "F(200)", operations), operations);

        Assert.True(outcome.IsError);
        var leaf = outcome.Error;
        while (leaf is EvalError.WithContext(_, var inner))
            leaf = inner;
        var depth = Assert.IsType<EvalError.EvaluationDepthExceeded>(leaf);
        Assert.Equal(EvaluationLimits.MaxSupportedDepth, depth.Limit);
        Assert.Equal(KatLangErrorCode.EvaluationDepthExceeded, outcome.Error.Code);
    }

    /// <summary>
    /// A host operation awaited AFTER each descent (<c>wait(F(n - 1)) + 1</c>) cannot give the
    /// descent a fresh stack — the audit measured the twin failing it at <c>F(30)</c> — and one
    /// awaited BEFORE each descent (<c>if(wait(n == 0), …)</c>) already resumed on one when it
    /// genuinely suspended. With the stack hop both complete, whether the operation completes
    /// synchronously or genuinely yields. The waiting-after shape holds TWO dynamic invocations
    /// per level — the operation's wrapper, and the recursive call its argument makes inside it —
    /// so the deterministic 128-level limit admits <c>F(63)</c> on every route; <c>F(60)</c> is
    /// past both the twin's former stack stop and the synchronous route's stop on this thread.
    /// </summary>
    [Theory]
    [InlineData("F(n) = if(n == 0, 0, wait(F(n - 1)) + 1)", 60, false)]
    [InlineData("F(n) = if(n == 0, 0, wait(F(n - 1)) + 1)", 60, true)]
    [InlineData("F(n) = if(wait(n == 0), 0, F(n - 1) + 1)", 120, false)]
    [InlineData("F(n) = if(wait(n == 0), 0, F(n - 1) + 1)", 120, true)]
    public async Task WaitingRecursion_OnOneMiBThread_Completes(string definition, int n, bool yielding)
    {
        var operations = WaitOperation(yielding);

        var outcome = await RunPublicAsyncFromOneMiBThread(ParseWith($"{definition}\nF({n})", operations), operations);

        Assert.True(outcome.IsOk, outcome.IsError ? outcome.Error.ToString() : null);
        Assert.Equal(new Result.Atom(n), outcome.Value);
    }

    /// <summary>
    /// <c>wait(F(n - 1)) + 1</c> at <c>F(120)</c> needs about 240 nested invocations (two per
    /// level, see above): on the documented minimum stack the twin reaches the DETERMINISTIC
    /// depth verdict, as every route does with enough stack — never the stack backstop.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task WaitingAfterEachDescent_PastTheDepthLimit_OnOneMiBThread_IsTheDeterministicVerdict(bool yielding)
    {
        var operations = WaitOperation(yielding);

        var outcome = await RunPublicAsyncFromOneMiBThread(
            ParseWith("F(n) = if(n == 0, 0, wait(F(n - 1)) + 1)\nF(120)", operations), operations);

        Assert.True(outcome.IsError);
        var leaf = outcome.Error;
        while (leaf is EvalError.WithContext(_, var inner))
            leaf = inner;
        Assert.Equal(EvaluationLimits.MaxSupportedDepth, Assert.IsType<EvalError.EvaluationDepthExceeded>(leaf).Limit);
    }

    /// <summary>
    /// The hop's check must hold wherever the probe after it would fail. At an invocation
    /// chokepoint that probe runs two helper frames deeper than the twin that tests
    /// <see cref="KatLang.Evaluation.StackHop.HostStackIsLow"/>; an exact test left a window of a
    /// few hundred bytes where the check passed and the probe failed (a full-suite run reported
    /// <see cref="EvalError.EvaluationStackExhausted"/> at <c>wait(F(n - 1))</c>), which
    /// <see cref="KatLang.Evaluation.StackHop.ChokepointMargin"/> closes. Starting the same run at
    /// every 48-byte offset across 64 KiB — more than one recursion level's stack on this shape —
    /// lands every chokepoint of a level in any such window at some offset; every start completes.
    /// </summary>
    [Fact]
    public void WaitingRecursion_FromEveryStackOffset_OnOneMiBThread_Completes()
    {
        var operations = WaitOperation(yielding: false);
        var ast = ParseWith("F(n) = if(n == 0, 0, wait(F(n - 1)) + 1)\nF(60)", operations);
        var expected = new Result.Atom(60);
        var wrong = new List<string>();
        var starts = 0;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () =>
        {
            for (var offset = 0; offset <= 64 * 1024; offset += 48)
            {
                starts++;
                var pending = StartBelow(offset,
                    () => Evaluator.RunAsync(ast, operations, limits: null, randomSeed: null, CancellationToken.None));
                Assert.True(pending.Wait(HopWaitLimit), $"offset {offset}: the run did not complete");
                var outcome = pending.Result;
                if (outcome.IsError)
                    wrong.Add($"{offset}: {outcome.Error.Code}");
                else if (!expected.Equals(outcome.Value))
                    wrong.Add($"{offset}: {outcome.Value}");
            }
        });

        Assert.True(starts > 1000);
        Assert.True(wrong.Count == 0, $"{wrong.Count} of {starts} starts did not complete with 60: {string.Join("; ", wrong.Take(10))}");
    }

    // Starts a run `offset` bytes lower on the current thread's stack.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static T StartBelow<T>(int offset, Func<T> start)
    {
        Span<byte> padding = stackalloc byte[offset];
        return StartOnPadding(padding, start);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static T StartOnPadding<T>(Span<byte> padding, Func<T> start) => start();

    private static HostOperations WaitOperation(bool yielding)
        => HostOperations.Create(HostOperation.CreateAsync("wait", async (args, _) =>
        {
            if (yielding)
                await Task.Yield();
            return args[0];
        }, "value"));
}
