using KatLang.Evaluation;

namespace KatLang;

/// <summary>
/// The <c>reduce</c> fold with accumulators evaluated on demand (lazy <c>reduce</c>, November 2026;
/// Lean: <c>EvalBody.evalReduceCounted</c> over <c>NeedSuspension.applied</c>). Part of the
/// <see cref="Evaluator"/> partial class.
/// </summary>
public static partial class Evaluator
{
    /// <summary>
    /// The evaluation frame of a <c>reduce</c> fold's steps: ONE frame around the demand of the
    /// last step, which every step that demand runs is under — a failure never gains one frame per
    /// fold level, however many accumulators its demand crossed. Lean: <c>reduceStepContext</c>.
    /// </summary>
    private const string ReduceStepContext =
        "while evaluating reduce step (reduce passes each iterated collection item as collected and the accumulator as one value; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)";

    /// <summary>
    /// The VALUE of <c>reduce</c>'s <c>initial</c>, demanded now: the one value-slot demand of the
    /// supplied computation (<see cref="DemandSequenceBuiltinCallItemValue"/> — at most once: the
    /// cell memoizes it), reported by <c>reduce</c>'s own initial-accumulator rule
    /// (<see cref="DemandedSequenceBuiltinValue"/>), occupying ONE accumulator slot at the ordinary
    /// value boundary. The whole result of a fold over an empty collection, and the start of every
    /// other fold whose demand reaches it. A plain synchronous method with an asynchronous twin
    /// (<see cref="EvalReduceInitialAsync"/>), not a flag body: an empty fold is this call alone,
    /// and it allocates nothing of its own. Lean: the empty case of <c>reduce</c> in
    /// <c>applyBuiltinCountedSequence</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalReduceInitial(
        VariadicCallItem initial,
        SequenceBuiltinSuffixArgDescriptor descriptor,
        EvalCtx ctx,
        ValEnv valEnv)
        => ReduceInitialValue(descriptor, DemandSequenceBuiltinCallItemValue(initial, ctx, valEnv));

    // The demanded initial's value in ONE accumulator slot, or its report through reduce's own
    // initial-accumulator rule. Shared by EvalReduceInitial and its asynchronous twin.
    private static EvalResult<CountedResult> ReduceInitialValue(
        SequenceBuiltinSuffixArgDescriptor descriptor, VariadicCallItem demanded)
    {
        var valueR = DemandedSequenceBuiltinValue(BuiltinId.@reduce, descriptor, demanded);
        return valueR.IsError
            ? valueR.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(valueR.Value, valueR.Value.ValueCount()));
    }

    /// <summary>
    /// Evaluate <c>reduce(collection, reducer, initial)</c> over a NONEMPTY collection, with
    /// ACCUMULATORS EVALUATED ON DEMAND. The fold associates its top-level collection elements as
    /// a left fold — <c>reduce([a, b], R, i)</c> is <c>R(b, R(a, i))</c> — and demands ONLY ITS
    /// LAST STEP. Each step is the ordinary invocation <c>step(element, accumulator)</c> over its
    /// already evaluated element, exactly as collected from the post-binding collection view, and
    /// ONE deferred accumulator cell (<see cref="ReduceFold"/>): demanding that cell runs the
    /// preceding step, or evaluates the start, and a reducer that never demands it skips every
    /// step that only it would have reached, and the initial expression with them. A step's
    /// result is its ORDINARY call result at the call's value boundary (HO-03, Q-25), so
    /// <c>()</c>, a list or several rows occupy ONE accumulator slot with their ordinary value
    /// shape.
    ///
    /// <para>The last step is demanded under the one reduce step frame
    /// (<see cref="ReduceStepContext"/>), whatever earlier steps and start that demand goes on to
    /// run. One entry for both evaluation routes: the synchronous caller blocks on the completed
    /// task, the asynchronous twin awaits it. Lean: <c>evalReduceCounted</c>.</para>
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalReduceCounted(
        IReadOnlyList<CountedResult> items,
        Algorithm stepAlg,
        VariadicCallItem initial,
        SequenceBuiltinSuffixArgDescriptor initialDescriptor,
        EvalCtx ctx,
        ValEnv valEnv,
        bool asynchronous)
    {
        FoldTrampoline.ForkHostScope();
        // The fold defers the ORIGINAL supplied cell with its written slot. An argument WITHOUT a
        // cell (a hand-built plan) has no computation to retain: it is demanded here, once, and
        // its value supplied as produced data.
        NeedCell? start = null;
        if (initial.Cell is null)
        {
            var startR = asynchronous
                ? await EvalReduceInitialAsync(initial, initialDescriptor, ctx, valEnv).ConfigureAwait(FoldTrampoline.CaptureFoldContext)
                : EvalReduceInitial(initial, initialDescriptor, ctx, valEnv);
            if (startR.IsError) return startR.Error;
            start = NeedCell.Ready(startR.Value);
        }

        var fold = new ReduceFold(items, stepAlg, initial, initialDescriptor, start, ctx, valEnv);
        return WithCtx(ReduceStepContext, await fold.Last(asynchronous).ConfigureAwait(FoldTrampoline.CaptureFoldContext));
    }

    /// <summary>
    /// ONE <c>reduce</c> FOLD: its elements, its resolved reducer, its supplied <c>initial</c>
    /// computation and the context of the <c>reduce</c> call, shared by every accumulator cell of
    /// the fold. Accumulator <c>count</c> is the fold of the first <c>count</c> elements: the
    /// start for <c>0</c>, otherwise the step over element <c>count - 1</c> and accumulator
    /// <c>count - 1</c>. A cell is allocated when the step that receives it is invoked, never
    /// earlier, and it holds this fold and its index: no prefix is copied or rebuilt.
    ///
    /// <para><b>The cells are VALUE-only.</b> An accumulator cell has no suspension and no
    /// projection, so it has no CALLABLE identity, it is no invocation plan (a <c>meta</c>
    /// parameter refuses it), and it retains no slice. The start is a NEW cell over the original
    /// <c>initial</c> computation: that computation is demanded through the value-slot law, never
    /// replayed, and its callable identity, retained slice and written-call plan stay behind. A
    /// cell memoizes its counted value or its ordinary failure like every need cell; forwarding
    /// passes the cell without evaluating it, and reads and pattern inspections share its
    /// completion.</para>
    ///
    /// <para><b>Continuations.</b> A step that demands its accumulator is suspended until the
    /// preceding step has run: a fold continuation, accounted apart from call nesting
    /// (<see cref="EvaluationBudget.EnterFoldContinuation"/>: every step of the fold runs at the
    /// depth the fold began at). Its accumulator cell holds one computation object
    /// (<see cref="AccumulatorComputation"/>); an accumulator computed on the heap is a SEGMENT of the
    /// fold's TRAMPOLINE (<see cref="AccumulatorSegment"/>, <see cref="FoldTrampoline"/>): on the
    /// asynchronous route every accumulator demand queues its segment there and the demanding step
    /// suspends as heap state, so the fold's chain
    /// never grows the host stack and runs on the thread that demands it. The synchronous route keeps
    /// a short chain on the host stack — a plain synchronous step and the accumulator demand's context
    /// boundary (<c>Evaluate</c>) per suspended step, at most
    /// <see cref="FoldTrampoline.HostStackAllowance"/> per thread — and continues a longer one on the
    /// heap: its accumulator demand runs the segment on the asynchronous twins through the same
    /// trampoline, pumped on the calling thread (<see cref="FoldTrampoline.TryRunSynchronously"/>). No
    /// thread is started and nothing waits for another thread.</para>
    ///
    /// <para><b>The streamed route</b> (C#-only implementation optimization; no Lean counterpart).
    /// A reducer whose FIRST observable act is the read of its accumulator
    /// (<see cref="LeadsWithItsAccumulator"/>: <c>acc + x</c>, <c>{x + total}</c>,
    /// <c>acc * 10 + item</c>) demands every accumulator of its fold, each before anything else
    /// its step does. The nested evaluation of such a fold is therefore fully determined: every
    /// step is entered, last step first, with no effect but its invocation charge; then the start
    /// is evaluated; then every step completes, first step first. <see cref="Stream"/> performs
    /// exactly that sequence without suspending a step: the invocation charges of all steps, last
    /// step first, then each step's body in order over a COMPLETED accumulator — the start's own
    /// deferred cell for the first step, so the first step's leading read is what evaluates
    /// <c>initial</c>. Value, effects and their order, ordinary failures and total budget charges
    /// are those of the nested evaluation; no fold continuation exists, so such a fold costs what
    /// the former loop cost however long it is. One difference in WHEN work is charged: the nested
    /// evaluation charges a step's expression work before its accumulator read on the way down,
    /// the streamed route when that step's body runs. Only a step limit that runs out inside the
    /// fold can observe it (the same verdict at the same consumed total, after more completed
    /// steps), and every strategy takes the same route, so they stop at the same point (Q-09b).
    /// Every other reducer takes the general route.
    /// <see cref="ReduceFoldTestSeam"/> withholds the streamed route so tests can compare the two
    /// (<c>StreamedReduceFoldEquivalenceTests</c>).</para>
    ///
    /// <para>Lean: the chain of deferred applications <c>EvalBody.evalReduceCounted</c> allocates
    /// (<c>NeedSuspension.applied</c>): the start is the deferred application of <c>reduce</c>
    /// itself to an empty collection and the supplied <c>initial</c> cell, each step the deferred
    /// application of the reducer to its element and the preceding accumulator.</para>
    /// </summary>
    private sealed class ReduceFold(
        IReadOnlyList<CountedResult> items,
        Algorithm step,
        VariadicCallItem initial,
        SequenceBuiltinSuffixArgDescriptor initialDescriptor,
        NeedCell? start,
        EvalCtx ctx,
        ValEnv values)
    {
        // The depth open when the fold began: every step of the fold runs one level below it.
        private readonly int _depth = ctx.Budget.CurrentDepth;
        // The reducer, normalized through an alias by the first step that runs.
        private Algorithm _step = step;

        /// <summary>The fold's result: its last step, demanded by the fold itself.</summary>
        internal async ValueTask<EvalResult<CountedResult>> Last(bool asynchronous)
        {
            FoldTrampoline.ForkHostScope();
            if (!ReduceFoldTestSeam.WithholdsStreaming && LeadsWithItsAccumulator(_step) is { } reducer)
                return await Stream(reducer, asynchronous).ConfigureAwait(FoldTrampoline.CaptureFoldContext);

            return asynchronous ? await StepAsync(items.Count - 1).ConfigureAwait(FoldTrampoline.CaptureFoldContext) : Step(items.Count - 1);
        }

        // The step over element `index`: ONE ordinary invocation of the reducer over the element's
        // Ready cell and the deferred accumulator of the elements before it. A plain synchronous
        // method with an asynchronous twin (StepAsync): a step waiting for its accumulator keeps its frames on the
        // host stack, where an async method run to completion would add three frames (stub, builder,
        // state machine: about a kilobyte, measured November 2026) once per suspended step, each of
        // them walked by every garbage collection while the step stays suspended.
        private EvalResult<CountedResult> Step(int index)
        {
            // A reducer that is an alias is its target, resolved BEFORE the invocation charge (an
            // alias is no invocation). A safety net: lookups normalize aliases first.
            if (_step is Algorithm.Alias alias)
            {
                var target = ResolveAliasTarget(alias, ctx);
                if (target.IsError) return target.Error;
                _step = target.Value;
            }

            StepStackHop(asynchronous: false).GetAwaiter().GetResult();
            if (ctx.Budget.TryEnterInvocation() is { } limitError)
                return limitError;

            try
            {
                NeedCell[] supply = [NeedCell.Ready(CountedSequenceCallbackItem(items[index])), Accumulator(index)];
                // The step's ordinary call result, whole, with its value-boundary count (HO-03).
                return ReCountValueBoundary(EvalNeedCallbackSupplyCounted(_step, supply, ctx, values, ReduceStepFrameName));
            }
            finally
            {
                ctx.Budget.ExitInvocation();
            }
        }

        /// <summary>MIRROR OF <see cref="Step"/> — keep in lock-step.</summary>
        private async ValueTask<EvalResult<CountedResult>> StepAsync(int index)
        {
            // A reducer that is an alias is its target, resolved BEFORE the invocation charge (an
            // alias is no invocation). A safety net: lookups normalize aliases first.
            if (_step is Algorithm.Alias alias)
            {
                var target = await ResolveAliasTargetAsync(alias, ctx).ConfigureAwait(FoldTrampoline.CaptureFoldContext);
                if (target.IsError) return target.Error;
                _step = target.Value;
            }

            await StepStackHop(asynchronous: true);
            if (ctx.Budget.TryEnterInvocation() is { } limitError)
                return limitError;

            try
            {
                NeedCell[] supply = [NeedCell.Ready(CountedSequenceCallbackItem(items[index])), Accumulator(index)];
                // The step's ordinary call result, whole, with its value-boundary count (HO-03).
                return ReCountValueBoundary(await EvalNeedCallbackSupplyAsync(_step, supply, ctx, values, ReduceStepFrameName).ConfigureAwait(FoldTrampoline.CaptureFoldContext));
            }
            finally
            {
                ctx.Budget.ExitInvocation();
            }
        }

        // Await the hop in the step itself so the invocation and its body continue on the fresh stack.
        // An async helper could finish its hop before the step awaits it (see EnterInvocationFrameFlow).
        private static StackHop StepStackHop(bool asynchronous)
            => asynchronous && StackHop.HostStackIsLow() ? new StackHop() : StackHop.Skipped;

        // THE STREAMED ROUTE of a fold whose reducer leads with its accumulator: the sequence its
        // nested evaluation is known to take, with no step suspended.
        private async ValueTask<EvalResult<CountedResult>> Stream(Algorithm.User reducer, bool asynchronous)
        {
            FoldTrampoline.ForkHostScope();
            var budget = ctx.Budget;
            // Every step is entered before any step completes, last step first: the invocation
            // charges and their limit, cancellation and terminal checks, in that order. A step's
            // level is released again at once: nested, it would be a suspended continuation at
            // the fold's own depth while the next one is entered.
            for (var index = items.Count - 1; index >= 0; index--)
            {
                if (budget.TryEnterInvocation() is { } limitError)
                    return limitError;
                budget.ExitInvocation();
            }

            // The first step's leading read demands the start: the fold's own deferred cell.
            var accumulator = Accumulator(0);
            for (var index = 0; ; index++)
            {
                EvalResult<CountedResult> result;
                budget.EnterChargedInvocation();
                try
                {
                    NeedCell[] supply = [NeedCell.Ready(CountedSequenceCallbackItem(items[index])), accumulator];
                    // The step's ordinary call result, whole, with its value-boundary count (HO-03).
                    result = ReCountValueBoundary(
                        await EvalNeedCallbackSupply(reducer, supply, ctx, values, ReduceStepFrameName, asynchronous).ConfigureAwait(FoldTrampoline.CaptureFoldContext));
                }
                finally
                {
                    budget.ExitInvocation();
                }

                // A failure that ends the run (a resource limit, a carried host termination) is the
                // fold's outcome as it stands: the steps suspended above it only hand it on.
                if (index == items.Count - 1 || result is { IsError: true, Error.IsTerminalForRun: true }) return result;
                // The next step's accumulator is this step's completed outcome: its value, or its
                // ordinary failure, which that step's leading read receives exactly as the nested
                // evaluation delivers it.
                accumulator = result.IsError ? FailedAccumulator(NestMissingOutput(result.Error)) : NeedCell.Ready(result.Value);
            }
        }

        // A completed accumulator whose outcome is a failure.
        private NeedCell FailedAccumulator(EvalError failure)
        {
            var budget = ctx.Budget;
            EvalResult<CountedResult> outcome = failure;
            return new NeedCell(() => outcome, () => new ValueTask<EvalResult<CountedResult>>(outcome), token: budget.CancellationToken, budget: budget);
        }

        /// <summary>
        /// Whether <paramref name="reducer"/> LEADS WITH ITS ACCUMULATOR: a user algorithm with no
        /// <c>open</c>, whose head is exactly two plain, differently named parameters — so binding
        /// demands nothing — and whose first output row reaches the read of the second parameter
        /// before anything observable: through operands the evaluator takes left to right, past
        /// number and Boolean literals and the element's own read (an already evaluated value).
        /// A string literal reserves materialized characters and can refuse before the accumulator
        /// is reached. Decided from the reducer's own structure, never from values, and
        /// conservatively: a reducer it does not recognize takes the general route.
        /// </summary>
        private static Algorithm.User? LeadsWithItsAccumulator(Algorithm reducer)
        {
            if (reducer is not Algorithm.User { Opens.Count: 0, Output.Count: > 0, ParameterPatterns: { Count: 2 } patterns } user
                || patterns[0] is not CaptureParameterPattern { Kind: ParameterKind.Normal, Name: { } element }
                || patterns[1] is not CaptureParameterPattern { Kind: ParameterKind.Normal, Name: { } accumulator }
                || string.Equals(element, accumulator, StringComparison.Ordinal))
            {
                return null;
            }

            return LeadsWith(user.Output[0], element, accumulator) ? user : null;
        }

        // Whether evaluating `expression` reads the accumulator before anything observable. The
        // operand orders are the expression spine's: a unary operand, then its operator; a binary
        // operator's left operand, then (`and` / `or` judge the left operand first, so only an
        // arithmetic operator goes on) its right one, then the operator; a comparison chain's
        // first operand, then its first link's operand, then that link.
        private static bool LeadsWith(Expr expression, string element, string accumulator)
        {
            while (true)
            {
                switch (expression)
                {
                    case Expr.Param(var name):
                        return string.Equals(name, accumulator, StringComparison.Ordinal);
                    case Expr.Unary(_, var operand):
                        expression = operand;
                        continue;
                    case Expr.Binary(var op, var left, var right):
                        if (!IsInert(left, element))
                        {
                            expression = left;
                            continue;
                        }

                        if (op is BinaryOp.And or BinaryOp.Or or BinaryOp.Xor) return false;
                        expression = right;
                        continue;
                    case Expr.Comparison(var first, var links):
                        if (!IsInert(first, element))
                        {
                            expression = first;
                            continue;
                        }

                        if (links.Count == 0) return false;
                        expression = links[0].Operand;
                        continue;
                    default:
                        return false;
                }
            }
        }

        // A scalar literal with no materialization charge, or a read of the ready element.
        private static bool IsInert(Expr expression, string element)
            => expression is Expr.Num or Expr.BoolLiteral
                || (expression is Expr.Param(var name) && string.Equals(name, element, StringComparison.Ordinal));

        // The deferred accumulator of the first `count` elements: a VALUE-only cell over ONE
        // computation object (no closure, no delegates).
        private NeedCell Accumulator(int count)
        {
            if (count == 0 && start is not null) return start;
            var budget = ctx.Budget;
            return new NeedCell(new AccumulatorComputation(this, count), budget, budget.CancellationToken);
        }

        // The fold's trampoline, created by the first demand that needs it: every accumulator demand
        // of the asynchronous route, and a synchronous demand beyond the host stack's allowance.
        private FoldTrampoline? _trampoline;

        private FoldTrampoline Trampoline
            => Volatile.Read(ref _trampoline) ?? Interlocked.CompareExchange(ref _trampoline, new FoldTrampoline(ctx.Budget), null) ?? _trampoline!;

        // The synchronous VALUE computation of accumulator `count`: in place, nested on the host stack,
        // while this thread's chain stays within the host stack's allowance (FoldTrampoline: at most
        // HostStackAllowance fold continuations and HostStackByteAllowance of stack); beyond that on the
        // heap, through the fold's trampoline pumped on this thread. In place also where the run's
        // property cache offers the twins no asynchronous view (a host-supplied test cache) or a drain
        // loop of the same run runs on this thread, as every fold did before the trampoline.
        private EvalResult<CountedResult> EvaluateOnHostStack(int count)
        {
            if (FoldTrampoline.HostStackAllowanceIsUsed
                && ctx.ZeroArgPropertyResultCache.TwinView is not null
                && Trampoline.TryRunSynchronously(new AccumulatorSegment(this, count), ctx.Budget, out var continued))
            {
                return continued;
            }

            var nested = FoldTrampoline.EnterHostStackContinuation();
            ctx.Budget.NoteHostStackFoldContinuations(nested + 1);
            try
            {
                return Evaluate(count, asynchronous: false).GetAwaiter().GetResult();
            }
            finally
            {
                FoldTrampoline.LeaveHostStackContinuation(nested);
            }
        }

        // The asynchronous computation of accumulator `count` as a segment of the fold's trampoline,
        // counted for the run's observation of continuations kept on the heap.
        private ValueTask<EvalResult<CountedResult>> EvaluateSegment(int count)
        {
            ctx.Budget.NoteHeapFoldSegment();
            return Evaluate(count, asynchronous: true);
        }

        // The VALUE of accumulator `count`: the start, or the step over the element before it.
        // The method builder restores the demanding step's execution and synchronization contexts on
        // return, even on synchronous completion under suppressed flow. A host call in a step or in
        // the initial value can change either context. Its caller resumes with its own ambient state.
        private async ValueTask<EvalResult<CountedResult>> Evaluate(int count, bool asynchronous)
        {
            FoldTrampoline.ForkHostScope();
            var budget = ctx.Budget;
            var suspendedDepth = budget.EnterFoldContinuation(_depth);
            try
            {
                EvalResult<CountedResult> result;
                if (count == 0)
                {
                    result = asynchronous
                        ? await EvalReduceInitialAsync(initial, initialDescriptor, ctx, values).ConfigureAwait(FoldTrampoline.CaptureFoldContext)
                        : EvalReduceInitial(initial, initialDescriptor, ctx, values);
                }
                else
                {
                    result = asynchronous ? await StepAsync(count - 1).ConfigureAwait(FoldTrampoline.CaptureFoldContext) : Step(count - 1);
                }
                // The accumulator is a subordinate computation of whichever step demands it, so
                // its own missing output is stored as nested (Q-36), like a collector's element.
                return result.IsError ? NestMissingOutput(result.Error) : result;
            }
            finally
            {
                budget.ExitFoldContinuation(_depth, suspendedDepth);
            }
        }

        /// <summary>
        /// The VALUE computation of one deferred accumulator of a fold: its fold and its index, one
        /// object for both routes (<see cref="NeedComputation"/>). The asynchronous demand queues the
        /// accumulator's segment on the fold's trampoline.
        /// </summary>
        private sealed class AccumulatorComputation(ReduceFold fold, int count) : NeedComputation
        {
            internal override EvalResult<CountedResult> Evaluate() => fold.EvaluateOnHostStack(count);

            internal override ValueTask<EvalResult<CountedResult>> EvaluateAsync() => fold.Trampoline.Demand(new AccumulatorSegment(fold, count));
        }

        /// <summary>
        /// The asynchronous computation of one deferred accumulator as a segment of its fold's trampoline
        /// (<see cref="FoldSegment"/>), allocated when the computation runs on the heap.
        /// </summary>
        private sealed class AccumulatorSegment(ReduceFold fold, int count) : FoldSegment
        {
            protected override ValueTask<EvalResult<CountedResult>> RunSegment() => fold.EvaluateSegment(count);
        }
    }
}
