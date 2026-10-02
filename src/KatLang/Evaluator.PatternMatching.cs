using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang;

/// <summary>
/// Pattern matching for conditional algorithms, counted parameter-pattern binding, callback invocation, and the prepared algorithm-output / capture core (the "Pattern matching (for conditional algorithms)" section).
/// Part of the <see cref="Evaluator"/> partial class; the central state, lookup and open resolution,
/// the built-in prelude, and the run entry points remain in <c>Evaluator.cs</c>.
/// </summary>
public static partial class Evaluator
{
    // ── Pattern matching (for conditional algorithms) ────────────────────────

    /// <summary>
    /// Match a pattern against a Result, returning accumulated bindings on success.
    /// Lean: matchPattern. Compiler-exhaustive over the closed Pattern hierarchy,
    /// like Lean's total match: a new pattern kind fails this build instead of
    /// silently matching nothing.
    /// </summary>
    private static bool MatchPattern(
        Pattern pattern,
        Result result,
        List<(string Name, Result Value)> bindings)
        => pattern switch
        {
            Pattern.Bind(var name) => MatchBindPattern(name, result, bindings),
            // Literal patterns match by STRUCTURAL numeric equality (Decimal128.Equals:
            // NaN is one value, quantum ignored) — the same semantics the repeated-binder
            // arm above and Result.ValueComparer use. The IEEE `==` operator would make a
            // host-built LitInt(NaN) pattern unable to match anything, including itself.
            Pattern.LitInt(var n) => result is Result.Atom(var v) && v.Equals(n),
            Pattern.LitString(var s) => result is Result.Str(var sv)
                && string.Equals(sv, s, StringComparison.Ordinal),
            // A Boolean literal pattern matches only a Boolean value (never the number
            // it would once have encoded).
            Pattern.LitBool(var b) => result is Result.Bool(var bv) && bv == b,
            // STRUCTURAL PATTERN DELIMITERS SELECT THE VALUE KIND THEY DESTRUCTURE: a sequence
            // pattern matches only a sequence value, a list pattern only a list value, each
            // of exactly its length (Lean: `patternStructureMembers?`).
            Pattern.SequenceValue(var items) => MatchStructurePattern(items, result.SequencePatternItems(), bindings),
            Pattern.ListValue(var items) => MatchStructurePattern(items, result.ListPatternItems(), bindings),
        };

    private static bool MatchBindPattern(string name, Result result, List<(string Name, Result Value)> bindings)
    {
        var existing = LookupVal(bindings, name);
        if (existing is not null)
            return Result.ValueComparer.Equals(existing, result);

        bindings.Add((name, result));
        return true;
    }

    /// <summary>
    /// Matches a structural pattern's items against the elements its value supplied
    /// (<paramref name="members"/> is <c>null</c> when the value is not of the pattern's kind).
    /// The lengths must be equal: there is no singleton adaptation — a one-item sequence
    /// pattern is invalid, and no value is a one-item structure of another kind.
    /// Lean: <c>matchStructureInto</c> over <c>patternStructureMembers?</c>.
    /// </summary>
    private static bool MatchStructurePattern(
        IReadOnlyList<Pattern> items,
        IReadOnlyList<Result>? members,
        List<(string Name, Result Value)> bindings)
    {
        if (members is null || members.Count != items.Count)
            return false;

        for (var i = 0; i < items.Count; i++)
        {
            if (!MatchPattern(items[i], members[i], bindings))
                return false;
        }
        return true;
    }

    private static ValEnv? MatchPattern(Pattern pattern, Result result)
    {
        var bindings = new List<(string Name, Result Value)>();
        return MatchPattern(pattern, result, bindings) ? bindings : null;
    }

    /// <summary>
    /// Compatibility fallback for manually constructed core conditionals.
    /// Surface clause elaboration should already classify whole same-name
    /// plain-binder clause groups as ordinary <see cref="Algorithm.User"/>
    /// values in the parser. This helper intentionally keeps only the stricter
    /// flat multi-binder raw <see cref="Algorithm.Conditional"/> core shape
    /// call-compatible with ordinary user-call semantics so evaluator fallback
    /// does not silently broaden to bare single-binder conditionals.
    /// </summary>
    private static Algorithm.User? TryGetFlatBinderUserEquivalent(Algorithm callee)
    {
        if (callee is not Algorithm.Conditional cond || cond.Branches.Count != 1)
            return null;

        var paramNames = cond.Branches[0].Pattern.TryGetFlatMultiBinderParams();
        if (paramNames is null)
            return null;

        if (ChildOf(callee, cond.Branches[0].Body) is not Algorithm.User body)
            return null;

        // A `with` view of the branch body: a deferred placeholder's region comes along
        // (Algorithm.DeferredRegion), so demanding the equivalent's output materializes —
        // and shares — the very region the branch carries.
        return body with { ParameterPatterns = Algorithm.NormalParameters(paramNames) };
    }

    /// <summary>
    /// Report a conditional algorithm's rejected zero-argument demand. Callers
    /// first route zero-accepting families through ordinary branch dispatch.
    /// Mirrors the no-argument dot-call dispatch: a flat
    /// multi-binder core equivalent reports its ordinary call arity, and any
    /// other conditional reports NoMatchingBranch. Returns null for
    /// non-conditional algorithms. Lean: <c>conditionalValueAccessError?</c>.
    /// </summary>
    private static EvalError? ConditionalValueAccessError(string name, Algorithm alg)
    {
        if (alg is not Algorithm.Conditional)
            return null;

        var simple = TryGetFlatBinderUserEquivalent(alg);
        if (simple is not null)
            return new EvalError.ArityMismatch(simple.ParameterCount, 0);

        return new EvalError.NoMatchingBranch(name);
    }

    /// <summary>
    /// The counted view of one iterated collection item as the callback
    /// receives it. A callback item is a SELECTED value, so it crosses the same
    /// ordinary value boundary as <c>S:i</c> / <c>first</c> / <c>last</c>
    /// (<see cref="ReCountValueBoundary(CountedResult)"/>): the item keeps its
    /// stored shape (a nested sequence or list stays one value for pattern
    /// matching and for every count-sensitive reader inside the body — a bare
    /// <c>x</c> output row, <c>x.Coll</c> on a collecting receiver, the
    /// map/reduce single-element checks), a <c>()</c> item emits zero values,
    /// and only an explicit spread <c>x*</c> opens it.
    /// Lean: <c>countedSequenceCallbackItem</c>.
    /// </summary>
    private static CountedResult CountedSequenceCallbackItem(CountedResult item)
        => ReCountValueBoundary(item);

    /// <summary>
    /// Evaluate a resolved algorithm against pre-evaluated callback arguments
    /// that preserve their emitted top-level counts.
    /// </summary>
    private static EvalResult<CountedResult> EvalResolvedCallbackCallCounted(
        Algorithm? callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName = "conditional")
    {
        // A callback that is an alias is its target, resolved BEFORE the invocation charge (an
        // alias is no invocation). A safety net out of line — lookups normalize aliases first.
        if (callee is Algorithm.Alias)
            return EvalAliasCallbackCallCounted(callee, args, ctx, valEnv, calleeName);

        // Charged dynamic invocation boundary. This is the single callback dispatch
        // chokepoint: the plain wrapper, the sequence-callback wrappers, and the
        // conditional-callback path all route through here, so a callback invocation is
        // charged exactly once regardless of callee shape.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return limitError;

        try
        {
            return callee is null ? new EvalError.ArityMismatch(0, args.Count)
                : EvalResolvedCallbackCallCountedCore(callee, args, ctx, valEnv, calleeName);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    /// <summary>
    /// Callback dispatch. THE CALLBACK LAW (September 2026): every value a callback
    /// operation supplies is ONE ordinary argument, bound exactly as the ordinary call
    /// with the same supply — <c>map(xs, F)</c> calls <c>F(E)</c> for each element
    /// <c>E</c>, <c>reduce</c> calls <c>R(E, Acc)</c> — so a user callee (and a clause
    /// family's flat-binder equivalent) binds through the ONE counted binder
    /// <see cref="BindNeedPatterns"/>: fixed parameters take their values
    /// unchanged, a collector collects the supplied values exactly, and only the callee's
    /// explicit sequence-value patterns open a value. There is no callback row
    /// convention: <c>map([(1, 2)], Add)</c> with <c>Add(x, y)</c> is the ordinary
    /// arity error, while <c>AddPair((x, y))</c> opens the element explicitly. The
    /// user-callee arm is written inline (one frame, like the dispatch it replaced).
    /// Lean: <c>evalResolvedCallbackCallCounted</c> / <c>evalUserCallbackCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalResolvedCallbackCallCountedCore(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName)
    {
        return EvalNeedCallbackBody(callee, args, ctx, valEnv, calleeName, asynchronous: false).GetAwaiter().GetResult();
    }

    /// <summary>
    /// The value projection of counted callback dispatch. Callback items retain
    /// their ordinary value-boundary counts inside the counted implementation.
    /// </summary>
    private static EvalResult<Result> EvalResolvedCallbackCall(
        Algorithm? callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName = "conditional")
        => ProjectCountedValue(EvalResolvedCallbackCallCounted(callee, args, ctx, valEnv, calleeName));

    /// <summary>
    /// Evaluate a higher-order sequence callback on one iterated item.
    /// </summary>
    private static EvalResult<Result> EvalSequenceCallbackCall(
        Algorithm? callee,
        CountedResult item,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCall(callee, [CountedSequenceCallbackItem(item)], ctx, valEnv, calleeName);

    /// <summary>
    /// Counted variant of <see cref="EvalSequenceCallbackCall"/>.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceCallbackCallCounted(
        Algorithm? callee,
        CountedResult item,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCallCounted(callee, [CountedSequenceCallbackItem(item)], ctx, valEnv, calleeName);

    /// <summary>
    /// Evaluate an algorithm's output expressions and count how many top-level
    /// values they emitted at the current algorithm boundary.
    /// A parenthesized sequence-value expression counts as one value, while multiple top-level
    /// output expressions count separately.
    /// Lean: <c>evalAlgOutputCounted</c>.
    /// </summary>
    private static EvalResult<PreparedAlgorithmOutput> EvalAlgOutputPreparedCore(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (alg.DeferredRegion is { } region)
        {
            if (!region.TryGetMaterialized(out var materialized))
                throw DeferredModuleRegion.SynchronousSelectionNotSupported();
            alg = WithParent(materialized.WithParameterPatterns(alg.ParameterPatterns), alg.Parent);
        }

        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<PreparedAlgorithmOutput>.Ok(new(
                    countedR.Value,
                    CountedTopLevelValues(countedR.Value)));
        }

        var dupProp = alg.FindDuplicatePropName();
        if (dupProp is not null)
            return new EvalError.DuplicateProperty(dupProp);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output: { Count: 0 } })
            return new EvalError.MissingOutput();

        return EvalOutputRowsPreparedCore(alg.Output, EnterAlgorithmBody(alg, ctx, valEnv), ctx, valEnv);
    }

    /// <summary>
    /// The ONE shared output-row supply loop: evaluates ordered
    /// <see cref="OutputBundle"/> rows left to right (a spread row contributes
    /// its supplied items, a non-spread row contributes exactly one slot) and
    /// combines the collected slots into one canonical value
    /// (<see cref="CombineOutputSlots"/>). Algorithm output evaluation reaches
    /// it after pushing the algorithm's own scope; <see cref="Expr.Capture"/>
    /// evaluation reaches it directly with the surrounding context, because a
    /// capture owns no scope. Both receivers therefore share exactly the same
    /// supply semantics rather than duplicating them.
    ///
    /// <para><b>Structural-nesting stack backstop</b> (mirrored verbatim by the async
    /// twin <see cref="EvalOutputRowsPreparedCoreAsync"/>): nested brace and capture
    /// bodies recurse through this funnel WITHOUT crossing any invocation chokepoint
    /// (structural nesting charges no dynamic depth), and the static preflight bounds
    /// only the written nesting of ONE body. Dynamic recursion multiplies that bound:
    /// each recursion level crosses one charged, probing chokepoint and then descends
    /// its whole written nesting uncharged, so a body nested wider than the
    /// chokepoint probe's reserve overflowed the process stack BETWEEN two probes — the
    /// next chokepoint noticed exhaustion with no stack left to build the structured
    /// error (audit finding K2-R1, September 2026). Probing once per row loop, i.e.
    /// once per nesting level, bounds the uncharged descent between two probes to a
    /// single level of frames. This is NOT the rejected per-node probe (see
    /// <see cref="EvaluationLimits.MaxSupportedAstDepth"/>): it runs per row loop, not
    /// per expression node, so deep parser-produced expression spines are unaffected.
    /// Like the invocation-chokepoint probe it can only stop evaluation EARLIER with
    /// the structured error, never change a run that has host stack headroom, and it
    /// moves no budget counter.</para>
    /// </summary>
    private static EvalResult<PreparedAlgorithmOutput> EvalOutputRowsPreparedCore(
        IReadOnlyList<Expr> rows,
        EvalCtx rowCtx,
        EvalCtx reserveCtx,
        ValEnv valEnv)
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        var results = new List<Result>();
        var emittedCount = 0;

        foreach (var expr in rows)
        {
            var countedR = EvalCounted(expr, rowCtx, valEnv);
            if (countedR.IsError) return countedR.Error;

            if (expr is Expr.SequenceSpread)
            {
                AddCountedTopLevelValues(results, countedR.Value);
                emittedCount += countedR.Value.EmittedCount;
                continue;
            }

            // A non-spread output expression is always one visible output slot,
            // even when it evaluates to the empty sequence value `()`. Only an
            // explicit spread opens a sequence and can contribute zero items.
            results.Add(countedR.Value.Value);
            emittedCount += countedR.Value.EmittedCount == 0 ? 1 : countedR.Value.EmittedCount;
        }

        // Output-slot capture is a persistent collection: spread can expand it well beyond
        // any single input (`(A*, A*)` doubles), so the reservation happens
        // here, before the sequence value is built.
        if (ReserveSequenceCaptureAtRows(reserveCtx, results.Count, rows) is { } capturedLimitError)
            return capturedLimitError;

        var counted = new CountedResult(CombineOutputSlots(results), emittedCount);
        return EvalResult<PreparedAlgorithmOutput>.Ok(new(counted, results));
    }

    /// <summary>
    /// Evaluates a <see cref="Expr.Capture"/> body's rows in the surrounding
    /// context (a capture owns no scope, so nothing is pushed) through the
    /// shared output-row supply loop. The multi-item emitted count is
    /// preserved here; value-position consumers re-count at the capture's
    /// value boundary (<see cref="Result.ValueCount"/>). An empty bundle
    /// captures the empty sequence value.
    /// Lean: <c>evalCapturePreparedCore</c>.
    /// </summary>
    private static EvalResult<PreparedAlgorithmOutput> EvalCapturePreparedCore(
        OutputBundle body,
        EvalCtx ctx,
        ValEnv valEnv)
        => EvalOutputRowsPreparedCore(body, ctx, ctx, valEnv);

    private static EvalResult<CountedResult> EvalCaptureCountedCore(
        OutputBundle body,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var preparedR = EvalCapturePreparedCore(body, ctx, valEnv);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
    }

    /// <summary>
    /// Evaluates a capture body to its single canonical captured value.
    /// </summary>
    private static EvalResult<Result> EvalCaptureValue(
        OutputBundle body,
        EvalCtx ctx,
        ValEnv valEnv)
        => ProjectCountedValue(EvalCaptureCountedCore(body, ctx, valEnv));

    /// <summary>
    /// The algorithm-channel adapter for a capture: a fresh zero-parameter
    /// output-only thunk over the bundle, wired to the caller scope. CAPTURE IS
    /// NOT ALGORITHM IDENTITY — this never exposes the algorithm identity of
    /// any expression inside the bundle (a captured named algorithm stays
    /// suppressed, exactly like the pre-split transparent wrapper); it only
    /// lets algorithm-channel consumers evaluate the capture's value lazily.
    /// Lean: <c>captureValueThunk</c>.
    /// </summary>
    private static Algorithm CaptureValueThunk(OutputBundle body, EvalCtx ctx)
        => WireToCaller(
            ctx,
            new Algorithm.User(
                Parent: null,
                ParameterPatterns: [],
                Opens: [],
                Properties: [],
                Output: body));

    private static EvalResult<CountedResult> EvalAlgOutputCountedCore(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var preparedR = EvalAlgOutputPreparedCore(alg, ctx, valEnv);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
    }

    // Combine collected top-level output slots into one value. A single slot is
    // returned as-is so useful sequence structure is preserved; multiple slots
    // form one sequence value. Unlike <see cref="Result.FromItems"/>, this does
    // NOT singleton-collapse or recursively renormalize slot values — slots are
    // already evaluated values.
    private static Result CombineOutputSlots(IReadOnlyList<Result> slots)
        => slots.Count == 1 ? slots[0] : new Result.SequenceValue(slots);

    // Materialize a collection-producing builtin's kept/projected items as ONE
    // list value. Unlike canonical arity capture (ordinary
    // construction via <see cref="Result.Normalize"/>,
    // <see cref="CombineOutputSlots"/>), the list boundary is exact:
    // zero items form `[]`, a single kept item forms `[item]` (the one-item
    // collection boundary is NEVER erased, so `take(((1, 2), (3, 4)), 1)`
    // yields `[(1, 2)]`), and item internals are never renormalized, dropped,
    // or flattened — nested sequence values and nested list values stay exact
    // elements. The emitted count is always 1: a list value is one visible
    // value (<see cref="Result.ValueCount"/>), including the empty list `[]`.
    // The items array is freshly materialized here, so ownership transfer via
    // <see cref="Result.ListValue.TakeOwnership"/> is safe.
    // Lean: makeCollectionListResult.
    private static CountedResult MakeCollectionListResult(IEnumerable<Result> items)
        => new(Result.ListValue.TakeOwnership(items.ToArray()), 1);
}
