using KatLang.Evaluation;

namespace KatLang;

// META-S3-0b — asynchronous resolution over the ONE synchronous resolver.
//
// The async twin family obtains an identity (a callee, a dot receiver, an invoking slot's
// callback or loop step) through the SAME synchronous resolver the sync engine runs, so
// evaluation order, identity classification, error wrapping, written-slot blame, spans and
// contexts have one owner. The resolver runs as a NON-INITIATING observation
// (NeedCell.ObservationScope): it never starts a VALUE or a runtime CALLABLE projection. When it
// needs one, the adapter performs exactly that step asynchronously — in the current logical flow,
// so its wait-for edges are the ones the synchronous resolver would have recorded — RECORDS the
// step's actual outcome, published or not, and runs the resolver again, which then observes the
// recorded outcome at the very demand point it would have performed the step.
//
// PROGRESS: an observation answers terminal/cancellation → memo → recorded outcome → pending, so
// it reports pending only for a (cell, channel) pair with no observable outcome; the step
// performed for it always records one (a flow-local DemandCycle, a terminal answer, an ordinary
// failure or a success — cancellation and host exceptions leave the resolution instead). Every
// retry therefore strictly enlarges the set of determined pairs; the resolver reaches only
// retry-stable cells (supplied and parameter cells, cells retained by stable owners — Guard B in
// NeedCell), so the set is finite and the resolution ends after at most one step per reachable
// pair. Guard A below fails loud if a recorded pair is ever reported pending again.
public static partial class Evaluator
{
    /// <summary>
    /// THE asynchronous resolution of a synchronous identity resolver (META-S3-0b async-resolution
    /// law): its result is the synchronous result — value or error kind, span, context, effects and
    /// charges — with every VALUE and runtime CALLABLE step it needs awaited in its own order and
    /// replayed where it reads it. A run with no runtime projection cannot reach a pending step
    /// (identity resolution demands no VALUE), so the resolver then runs directly, allocating
    /// nothing. <paramref name="resolve"/> must be a pure identity resolver: it evaluates no
    /// expression and charges nothing (it may run once per determined step).
    /// </summary>
    internal static ValueTask<EvalResult<T>> ResolveAsync<TState, T>(
        EvalCtx ctx, TState state, Func<TState, EvalResult<T>> resolve)
        => ctx.Budget.HasRuntimeProjections
            ? ResolveObservedAsync(ctx.Budget, state, resolve)
            : new(resolve(state));

    private static async ValueTask<EvalResult<T>> ResolveObservedAsync<TState, T>(
        EvaluationBudget budget, TState state, Func<TState, EvalResult<T>> resolve)
    {
        NeedCell.ResolutionRecord? record = null;
        while (true)
        {
            var scope = NeedCell.EnterObservation(record);
            EvalResult<T> result;
            try { result = resolve(state); }
            finally { NeedCell.ExitObservation(scope); }
            if (scope.Pending is not { } cell)
            {
                if (result.IsError && NeedCell.IsObservationPending(result.Error))
                    throw EvalError.ObservationPending.Escaped();
                return result;
            }
            record ??= new();
            // Guard A: an observation reports pending only an undetermined pair, so a pair this
            // resolution already recorded can never be pending again — retrying it would make
            // no progress. Fail loud; never retry, never convert it into an outcome.
            if (record.Contains(cell, scope.PendingChannel))
                throw new System.Diagnostics.UnreachableException(
                    $"META-S3-0b: asynchronous resolution made no progress ({scope.PendingChannel} step reported pending after its outcome was recorded).");
            budget.NoteResolutionRetry();
            if (scope.PendingChannel == NeedCell.Channel.Value)
                record.RecordValue(cell, await cell.DemandAsync().ConfigureAwait(false));
            else
                record.RecordCallable(cell, await cell.ProjectCallableAsync().ConfigureAwait(false));
        }
    }

    /// <summary>
    /// A non-initiating, non-retrying observation (optimizer recognition): the resolver's result,
    /// or <c>null</c> when it would need a VALUE or runtime CALLABLE step — which is never started,
    /// so the caller declines and ordinary evaluation proceeds.
    /// </summary>
    internal static EvalResult<T>? PeekResolve<TState, T>(EvalCtx ctx, TState state, Func<TState, EvalResult<T>> resolve)
    {
        if (!ctx.Budget.HasRuntimeProjections) return resolve(state);
        var scope = NeedCell.EnterObservation();
        EvalResult<T> result;
        try { result = resolve(state); }
        finally { NeedCell.ExitObservation(scope); }
        return scope.Pending is null ? result : (EvalResult<T>?)null;
    }

    // The decline answer optimizer recognition receives for an identity that needs a runtime step:
    // recognition only tests IsError (and falls back), so it never reaches a program or a host.
    private const string RecognitionNeedsRuntimeStepDescription = "identity needs a runtime projection";

    /// <summary>
    /// <see cref="ResolveDotReceiver"/> as one resolver result (its structural-member flag
    /// carried with the receiver), for <see cref="ResolveAsync{TState,T}"/> and
    /// <see cref="PeekResolve{TState,T}"/>.
    /// </summary>
    private static EvalResult<(Algorithm Receiver, bool IsStructuralMember)> ResolveDotReceiverOutcome(Expr target, EvalCtx ctx)
    {
        var resolved = ResolveDotReceiver(target, ctx, out var isStructuralMember);
        return resolved.IsError ? resolved.Error : EvalResult<(Algorithm, bool)>.Ok((resolved.Value, isStructuralMember));
    }

    /// <summary>The async twin's receiver navigation: <see cref="ResolveDotReceiver"/> through <see cref="ResolveAsync{TState,T}"/>.</summary>
    private static ValueTask<EvalResult<(Algorithm Receiver, bool IsStructuralMember)>> ResolveDotReceiverAsync(Expr target, EvalCtx ctx)
        => ResolveAsync(ctx, (target, ctx), static state => ResolveDotReceiverOutcome(state.target, state.ctx));

    /// <summary>
    /// The async twin's callback of a sequence builtin's invoking slot: the ONE synchronous slot
    /// projection (<see cref="ExpectPreparedAlgorithmSuffixArg"/>, role diagnostics and span
    /// included) through <see cref="ResolveAsync{TState,T}"/>, which consumes the awaited
    /// projection outcome itself — never "await the cell, then re-read it synchronously".
    /// </summary>
    private static ValueTask<EvalResult<Algorithm>> ExpectPreparedAlgorithmSuffixArgAsync(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index,
        EvalCtx ctx)
        => ResolveAsync(ctx, (builtin, descriptors, args, index),
            static state => ExpectPreparedAlgorithmSuffixArg(state.builtin, state.descriptors, state.args, state.index));

    /// <summary>
    /// The async loop's step: the ONE invoking-slot projection (<see cref="ProjectLoopStep"/>)
    /// through <see cref="ResolveAsync{TState,T}"/>, made exactly where the synchronous loop makes
    /// it (only when an iteration needs the step, LOOP-05).
    /// </summary>
    private static ValueTask<EvalResult<Algorithm>> ProjectLoopStepAsync(ResolvedArgumentAlgorithm step, BuiltinId loop, EvalCtx ctx)
        => ResolveAsync(ctx, (step, loop), static state => ProjectLoopStep(state.step, state.loop));

    /// <summary>The async twin's callee: the ONE callee law (<see cref="ResolveCallee"/>) through <see cref="ResolveAsync{TState,T}"/>.</summary>
    private static ValueTask<EvalResult<Algorithm>> ResolveCalleeAsync(Expr callee, EvalCtx ctx)
        => ResolveAsync(ctx, (callee, ctx), static state => ResolveCallee(state.callee, state.ctx));
}
