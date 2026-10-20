using System.Collections.Frozen;
using KatLang.Evaluation;

namespace KatLang;

/// <summary>
/// META-S3-3 (October 2026): builtins that declare META parameters, and the loops
/// <c>while(meta step)</c> / <c>repeat(meta step, count)</c> over a captured step invocation.
/// </summary>
public static partial class Evaluator
{
    /// <summary>
    /// The binder patterns of every builtin whose registry signature declares a META parameter
    /// (<see cref="BuiltinDescriptor.DeclaresMetaParameter"/>), translated ONCE from that signature by
    /// the same translation a user algorithm's parameter patterns take (<see cref="NeedParameterPatterns"/>).
    /// </summary>
    private static readonly FrozenDictionary<BuiltinId, IReadOnlyList<NeedPattern>> MetaBuiltinPatterns =
        BuiltinRegistry.AllBuiltins
            .Where(static descriptor => descriptor.DeclaresMetaParameter)
            .ToFrozenDictionary(
                static descriptor => descriptor.Id,
                static descriptor => NeedParameterPatterns(descriptor.PlainSignature.ParameterPatterns));

    /// <summary>
    /// THE META BINDING OF A BUILTIN (META-S3-3): a builtin whose signature declares a META parameter is an
    /// ordinary fixed-arity callable. Its arity gate decides the supplied count before any demand
    /// (<see cref="WrongBuiltinArity"/>); then its supplied cells bind through THE ONE inspecting binder
    /// (<see cref="BindAcceptedNeedPatterns"/>) over its cached signature patterns, exactly as a user
    /// algorithm's do — a META pattern reifies its supplied cell through <see cref="ReferenceAdapterCell"/>
    /// in written order (nothing runs; a cell that is not a supplied call is the ordinary META refusal; a
    /// run whose J7 gate disabled plans fails loudly) — and its native arm runs over the bound environment.
    /// Every route to a builtin reaches it through <see cref="ApplyBuiltinCountedResolved"/> or its async
    /// twin (a direct or dot-fallback call, planned dispatch, an alias, a higher-order parameter, a loop
    /// step, a callback, <c>Invoke()</c>), whose arguments are supplied cells; an argument without a cell
    /// (the hand-built test-plan seam) gets a non-plan cell, which META refuses.
    /// Lean: the <c>builtinDeclaresMeta</c> branch of <c>applyBuiltinCounted</c>.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> ApplyMetaBuiltinCounted(
        BuiltinDescriptor descriptor, IReadOnlyList<ResolvedArgumentAlgorithm> arguments,
        EvalCtx ctx, ValEnv values, bool asynchronous)
    {
        if (!descriptor.AcceptsArity(arguments.Count))
            return WrongBuiltinArity(descriptor.Id, arguments.Count);
        var supplied = new NeedCell[arguments.Count];
        for (var i = 0; i < supplied.Length; i++)
            supplied[i] = ExistingArgumentCell(arguments[i], ctx, values);
        var bound = await BindAcceptedNeedPatterns(MetaBuiltinPatterns[descriptor.Id], supplied, ctx, asynchronous, family: false).ConfigureAwait(false);
        if (bound.IsError) return bound.Error;
        var env = bound.Value!;
        return descriptor.Id switch
        {
            BuiltinId.@while or BuiltinId.@repeat
                => await EvalMetaLoop(descriptor.Id, env, ctx, values, asynchronous).ConfigureAwait(false),
            _ => throw new InvalidOperationException($"Builtin '{descriptor.Name}' declares a META parameter but has no native arm."),
        };
    }

    /// <summary>
    /// The loop over a captured step invocation (META-S3-3, D1, CR-9, CR-13): the reference bound to
    /// <c>meta step</c> (its Ready adapter, read without running anything) decoded into its plan; the plan's
    /// ONE sticky supply (<see cref="PrepareArgumentView"/>, which also checks the reference's run
    /// ownership: its recorded preparation or exactly one formation in the captured caller context, opening
    /// only the explicit spreads written inside the captured call and demanding no argument VALUE) is the
    /// initial state — the ORIGINAL argument cells, never re-formed; an empty supply is the ordinary
    /// zero-slot state (OD-1) — and the plan's canonical callee cell (<see cref="InvocationPlan.CalleeCell"/>,
    /// inert) is the step, projected only when an iteration runs. The captured call itself is never
    /// dispatched. RP-1: <c>repeat</c> demands and validates its count, the outer call's own VALUE argument,
    /// once and only AFTER the captured supply is prepared, so a captured spread's failure, effect or
    /// cancellation precedes the count's (LOOP-01/05). Lean: <c>metaLoopCapture</c>, <c>metaRepeatSetup</c>.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalMetaLoop(
        BuiltinId builtin, NeedEnv env, EvalCtx ctx, ValEnv values, bool asynchronous)
    {
        var adapter = await DemandCell(LookupNeed(env, "step")!, asynchronous).ConfigureAwait(false);
        if (adapter.IsError) return adapter.Error;
        var reference = (Result.CallReference)adapter.Value.Value;
        var state = asynchronous
            ? await PrepareArgumentViewAsync(reference, ctx).ConfigureAwait(false)
            : PrepareArgumentView(reference, ctx);
        if (state.IsError) return state.Error;
        var plan = reference.Plan;
        // META-S3-4: the view established the plan's route (and refused an intrinsic route), so the step is
        // the route's canonical callee cell — a member path, the `.Algorithm` link or an extension's fallback.
        var step = new ResolvedArgumentAlgorithm(null) { Cell = plan.CalleeCell, Source = plan.CalleeExpression };

        var remaining = long.MaxValue;
        if (builtin == BuiltinId.@repeat)
        {
            var count = await DemandCell(LookupNeed(env, "count")!, asynchronous).ConfigureAwait(false);
            if (count.IsError) return count.Error;
            var integer = ExpectWholeInt(count.Value.Value, "Repeat count");
            if (integer.IsError) return integer.Error;
            if (integer.Value < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");
            remaining = integer.Value >= long.MaxValue ? long.MaxValue : (long)integer.Value;
        }
        return await EvalNeedLoop(builtin, step, remaining, state.Value, ctx, values, asynchronous).ConfigureAwait(false);
    }
}
