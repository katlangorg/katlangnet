using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Runtime;

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
    /// Lean: matchPattern.
    /// </summary>
    private static bool MatchPattern(
        Pattern pattern,
        Result result,
        List<(string, Result)> bindings)
    {
        switch (pattern)
        {
            case Pattern.Bind(var name):
                {
                    var existing = LookupVal(bindings, name);
                    if (existing is not null)
                        return Result.ValueComparer.Equals(existing, result);

                    bindings.Add((name, result));
                    return true;
                }

            // Literal patterns match by STRUCTURAL numeric equality (Decimal128.Equals:
            // NaN is one value, quantum ignored) — the same semantics the repeated-binder
            // arm above and Result.ValueComparer use. The IEEE `==` operator would make a
            // host-built LitInt(NaN) pattern unable to match anything, including itself.
            case Pattern.LitInt(var n):
                return result is Result.Atom(var v) && v.Equals(n);

            case Pattern.LitString(var s):
                return result is Result.Str(var sv)
                    && string.Equals(sv, s, StringComparison.Ordinal);

            case Pattern.SequenceValue(var items):
                // Result.normalize collapses sequenceValue [x] -> x, so a
                // singleton sequence-value pattern (e.g. "(b)") must also
                // match a non-sequence-value result by treating it as if it
                // were sequenceValue [result].
                if (result is Result.SequenceValue(var rs))
                {
                    if (rs.Count != items.Count) return false;
                }
                else if (items.Count == 1)
                {
                    rs = [result];
                }
                else
                {
                    return false;
                }

                for (var i = 0; i < items.Count; i++)
                {
                    if (!MatchPattern(items[i], rs[i], bindings))
                        return false;
                }
                return true;

            default:
                return false;
        }
    }

    private static IReadOnlyList<(string, Result)>? MatchPattern(Pattern pattern, Result result)
    {
        var bindings = new List<(string, Result)>();
        return MatchPattern(pattern, result, bindings) ? bindings : null;
    }

    /// <summary>
    /// Match a top-level conditional call head against the explicit arguments
    /// supplied at the call site.
    ///
    /// Ordinary direct conditional calls preserve explicit argument slots at
    /// the top level: a non-sequence-value head expects exactly one explicit argument,
    /// while a sequence-value head expects one explicit argument per sequence element. Nested
    /// sequence-value structure is still matched through <see cref="MatchPattern"/>.
    /// </summary>
    private static IReadOnlyList<(string, Result)>? MatchCallPattern(
        Pattern pattern,
        IReadOnlyList<Result> explicitArgs)
    {
        if (pattern is Pattern.SequenceValue(var items))
        {
            if (items.Count != explicitArgs.Count)
                return null;

            var bindings = new List<(string, Result)>();
            for (var i = 0; i < items.Count; i++)
            {
                if (!MatchPattern(items[i], explicitArgs[i], bindings))
                    return null;
            }

            return bindings;
        }

        return explicitArgs.Count == 1 ? MatchPattern(pattern, explicitArgs[0]) : null;
    }

    private static (CondBranch Branch, IReadOnlyList<(string, Result)> Bindings)? MatchCallBranches(
        IReadOnlyList<CondBranch> branches,
        IReadOnlyList<Result> explicitArgs)
    {
        foreach (var branch in branches)
        {
            var bindings = MatchCallPattern(branch.Pattern, explicitArgs);
            if (bindings is not null)
                return (branch, bindings);
        }

        return null;
    }

    private static bool MatchCountedPattern(
        Pattern pattern,
        CountedResult result,
        List<(string, CountedResult)> bindings)
    {
        switch (pattern)
        {
            case Pattern.Bind(var name):
                {
                    var existing = LookupCountedParam(bindings, name);
                    if (existing is not null)
                        return Result.ValueComparer.Equals(existing.Value.Value, result.Value);

                    bindings.Add((name, result));
                    return true;
                }

            // Structural numeric equality, mirroring the plain MatchPattern arm.
            case Pattern.LitInt(var n):
                return result.Value is Result.Atom(var v) && v.Equals(n);

            case Pattern.LitString(var s):
                return result.Value is Result.Str(var sv)
                    && string.Equals(sv, s, StringComparison.Ordinal);

            case Pattern.SequenceValue(var items):
                IReadOnlyList<Result> members;
                if (result.Value is Result.SequenceValue(var groupedMembers))
                {
                    if (groupedMembers.Count != items.Count)
                        return false;

                    members = groupedMembers;
                }
                else if (items.Count == 1)
                {
                    members = [result.Value];
                }
                else
                {
                    return false;
                }

                for (var i = 0; i < items.Count; i++)
                {
                    if (!MatchCountedPattern(
                        items[i],
                        new CountedResult(members[i], members[i].ValueCount()),
                        bindings))
                        return false;
                }

                return true;

            default:
                return false;
        }
    }

    private static IReadOnlyList<(string, CountedResult)>? MatchCountedPattern(
        Pattern pattern,
        CountedResult result)
    {
        var bindings = new List<(string, CountedResult)>();
        return MatchCountedPattern(pattern, result, bindings) ? bindings : null;
    }

    private static IReadOnlyList<(string, CountedResult)>? MatchCountedCallPattern(
        Pattern pattern,
        IReadOnlyList<CountedResult> explicitArgs)
    {
        if (pattern is Pattern.SequenceValue(var items))
        {
            if (items.Count != explicitArgs.Count)
                return null;

            var bindings = new List<(string, CountedResult)>();
            for (var i = 0; i < items.Count; i++)
            {
                if (!MatchCountedPattern(items[i], explicitArgs[i], bindings))
                    return null;
            }

            return bindings;
        }

        return explicitArgs.Count == 1 ? MatchCountedPattern(pattern, explicitArgs[0]) : null;
    }

    private static (CondBranch Branch, IReadOnlyList<(string, CountedResult)> Bindings)? MatchCountedCallBranches(
        IReadOnlyList<CondBranch> branches,
        IReadOnlyList<CountedResult> explicitArgs)
    {
        foreach (var branch in branches)
        {
            var bindings = MatchCountedCallPattern(branch.Pattern, explicitArgs);
            if (bindings is not null)
                return (branch, bindings);
        }

        return null;
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

        return ChildOf(callee, cond.Branches[0].Body) is Algorithm.User body
            ? (Algorithm.User)body.WithParameters(Algorithm.NormalParameters(paramNames))
            : null;
    }

    /// <summary>
    /// Value-position access to a conditional algorithm cannot select a branch,
    /// so it must fail instead of silently forcing the conditional's empty
    /// output list. Mirrors the no-argument dot-call dispatch: a flat
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
            return new EvalError.ArityMismatch(simple.Params.Count, 0);

        return new EvalError.NoMatchingBranch(name);
    }

    /// <summary>
    /// Reify a pre-evaluated counted argument as a zero-parameter algorithm
    /// that preserves the same value and emitted top-level count. This rebuild
    /// costs O(value size), so it is performed lazily — only when an
    /// algorithm-only consumer actually requests a prepared argument's
    /// algorithm channel — and each completed construction is recorded on the
    /// run's passive <see cref="EvaluationObservations"/>.
    /// </summary>
    private static Algorithm CountedArgAlgorithm(CountedResult arg, EvalCtx ctx)
    {
        OutputBundle output = arg.EmittedCount switch
        {
            0 => [EmptyResultExpr()],
            1 => [ResultToExpr(arg.Value, ctx.Observations)],
            _ => ResultsToExprBundle(arg.Value.ToItems(), ctx.Observations),
        };

        var algorithm = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: output);

        // Record the completed wrapper, not merely a request that entered this helper.
        ctx.Observations?.RecordCountedArgumentReification();
        return algorithm;
    }

    /// <summary>
    /// Ordinary call-style unpacking for a pre-evaluated explicit callback
    /// argument. A final explicit arg may still unpack across the remaining
    /// parameters, matching <c>callee(S:i)</c>.
    /// </summary>
    private static IReadOnlyList<CountedResult> UnpackCountedArg(CountedResult arg)
        => UnpackArgs(arg.Value)
            .Select(value => new CountedResult(value, value.ValueCount()))
            .ToList();

    /// <summary>
    /// Bind callback parameters while preserving the projected emitted count of
    /// the iterated item. This keeps callback params behaving like <c>S:i</c>
    /// without making them callable algorithms.
    /// </summary>
    private static EvalResult<IReadOnlyList<(string, CountedResult)>> BindCountedCallbackParams(
        IReadOnlyList<string> paramNames,
        IReadOnlyList<CountedResult> args)
    {
        if (args.Count > paramNames.Count)
            return new EvalError.ArityMismatch(paramNames.Count, args.Count);

        var boundValues = new List<CountedResult>(paramNames.Count);
        for (var argIndex = 0; argIndex < args.Count; argIndex++)
        {
            var isFinalArg = argIndex == args.Count - 1;
            var remainingParams = paramNames.Count - boundValues.Count;

            if (isFinalArg && remainingParams > 1)
            {
                boundValues.AddRange(UnpackCountedArg(args[argIndex]));
                break;
            }

            boundValues.Add(args[argIndex]);
        }

        if (boundValues.Count != paramNames.Count)
            return new EvalError.ArityMismatch(paramNames.Count, boundValues.Count);

        var bindings = new List<(string, CountedResult)>(paramNames.Count);
        for (var i = 0; i < paramNames.Count; i++)
            bindings.Add((paramNames[i], boundValues[i]));

        return EvalResult<IReadOnlyList<(string, CountedResult)>>.Ok(bindings);
    }

    /// <summary>
    /// Callback binding for a flat callee whose top-level parameters include a
    /// collecting parameter. The callback argument supply keeps the established
    /// flat-callback row convention: when fewer argument slots are supplied
    /// than top-level parameters, the final supplied argument opens into its
    /// items (matching <c>callee(S:i)</c>; exact lists stay opaque), exactly
    /// as <see cref="BindCountedCallbackParams"/> does for fixed-only flat
    /// callees. The resulting slots then bind through the shared
    /// prefix/collecting/suffix binder, so the collecting parameter COLLECTS its allocated
    /// slots as one exact immutable list. Lean:
    /// <c>bindCountedCallbackParameterPatternList</c>.
    /// </summary>
    private static EvalResult<CountedParameterPatternBindings> BindCountedCallbackParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx)
    {
        var slots = args;
        if (args.Count > 0 && args.Count < patterns.Count)
        {
            var expanded = new List<CountedResult>(patterns.Count);
            for (var index = 0; index < args.Count - 1; index++)
                expanded.Add(args[index]);
            expanded.AddRange(UnpackCountedArg(args[^1]));
            slots = expanded;
        }

        return BindCountedParameterPatternList(
            patterns,
            slots,
            ctx,
            static (required, actual) => new EvalError.ArityMismatch(required, actual));
    }

    private static EvalResult<CountedParameterPatternBindings> BindCountedParameterPattern(
        ParameterPattern pattern,
        CountedResult input,
        EvalCtx ctx)
    {
        switch (pattern)
        {
            case CaptureParameterPattern { Kind: ParameterKind.Normal } capture:
                return EvalResult<CountedParameterPatternBindings>.Ok(new CountedParameterPatternBindings(
                    [(capture.Name, input)]));

            case CaptureParameterPattern { Kind: ParameterKind.Collecting }:
                return new EvalError.BadArity();

            case SequenceValueParameterPattern group:
                {
                    // A received sequence value or exact list value opens to its
                    // immediate items (Lean: Result.structureItems?); the counted
                    // callback path keeps its stricter singleton-only scalar
                    // fallback (sequence-value-pattern callback deconstruction of
                    // scalar elements stays deferred; flat top-level collecting
                    // callbacks bind via BindCountedCallbackParameterPatternList).
                    var items = input.Value.StructureItems();
                    if (items is null && group.Items.Count == 1)
                        items = [input.Value];

                    if (items is null)
                        return new EvalError.BadArity();

                    var nestedInputs = items
                        .Select(static item => new CountedResult(item, item.ValueCount()))
                        .ToList();
                    return BindCountedParameterPatternList(
                        group.Items,
                        nestedInputs,
                        ctx,
                        (required, actual) => SequenceValuePatternArityMismatch(group, required, actual));
                }

            default:
                return new EvalError.BadArity();
        }
    }

    private static EvalResult<CountedParameterPatternBindings> BindCountedParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<CountedResult> inputs,
        EvalCtx ctx,
        Func<int, int, EvalError> arityMismatch)
    {
        var collectingIndex = -1;
        for (var index = 0; index < patterns.Count; index++)
        {
            if (patterns[index] is not CaptureParameterPattern { Kind: ParameterKind.Collecting })
                continue;

            if (collectingIndex >= 0)
                return new EvalError.BadArity();

            collectingIndex = index;
        }

        var bindings = new List<(string, CountedResult)>();

        EvalResult<bool> AddBindings(CountedParameterPatternBindings added)
        {
            foreach (var binding in added.CountedBindings)
            {
                var existing = LookupCountedParam(bindings, binding.Item1);
                if (existing is not null)
                {
                    if (!Result.ValueComparer.Equals(existing.Value.Value, binding.Item2.Value))
                        return new EvalError.BadArity();
                    continue;
                }

                bindings.Add(binding);
            }

            return EvalResult<bool>.Ok(true);
        }

        EvalResult<bool> BindOne(int patternIndex, int inputIndex)
        {
            var boundR = BindCountedParameterPattern(patterns[patternIndex], inputs[inputIndex], ctx);
            if (boundR.IsError) return boundR.Error;

            return AddBindings(boundR.Value);
        }

        if (collectingIndex < 0)
        {
            if (patterns.Count != inputs.Count)
                return arityMismatch(patterns.Count, inputs.Count);

            for (var index = 0; index < patterns.Count; index++)
            {
                var boundR = BindOne(index, index);
                if (boundR.IsError) return boundR.Error;
            }

            return EvalResult<CountedParameterPatternBindings>.Ok(new CountedParameterPatternBindings(bindings));
        }

        var requiredCount = patterns.Count - 1;
        if (inputs.Count < requiredCount)
            return arityMismatch(requiredCount, inputs.Count);

        for (var index = 0; index < collectingIndex; index++)
        {
            var boundR = BindOne(index, index);
            if (boundR.IsError) return boundR.Error;
        }

        var suffixCount = patterns.Count - collectingIndex - 1;
        var suffixInputStart = inputs.Count - suffixCount;
        for (var suffixIndex = 0; suffixIndex < suffixCount; suffixIndex++)
        {
            var boundR = BindOne(collectingIndex + 1 + suffixIndex, suffixInputStart + suffixIndex);
            if (boundR.IsError) return boundR.Error;
        }

        var collectingCapture = (CaptureParameterPattern)patterns[collectingIndex];
        var capturedValues = inputs
            .Skip(collectingIndex)
            .Take(suffixInputStart - collectingIndex)
            .Select(static input => input.Value)
            .ToList();
        // Collecting binding COLLECTS: the assigned supply becomes one exact
        // immutable list value, emitted count 1 (a list is one visible value).
        var capturedResultR = CollectSegment(ctx, capturedValues, collectingCapture.Span);
        if (capturedResultR.IsError) return capturedResultR.Error;
        var capturedResult = capturedResultR.Value;
        var captured = new CountedResult(capturedResult, 1);
        var captureBindingsR = AddBindings(new CountedParameterPatternBindings(
            [(collectingCapture.Name, captured)]));
        if (captureBindingsR.IsError) return captureBindingsR.Error;

        return EvalResult<CountedParameterPatternBindings>.Ok(new CountedParameterPatternBindings(bindings));
    }

    /// <summary>
    /// Higher-order callbacks keep the collected item value shape for pattern
    /// matching, while the counted callback-param view still uses the same
    /// one-level projection rule as <c>S:i</c> for callback param operations
    /// like <c>x.count</c>.
    /// </summary>
    private static CountedResult CountedSequenceCallbackItem(CountedResult item)
    {
        var projected = item.Value.ProjectIteratedContent();
        return new CountedResult(projected.Value, projected.EmittedCount);
    }

    /// <summary>
    /// Evaluate a resolved algorithm against pre-evaluated callback arguments
    /// that preserve their emitted top-level counts.
    /// </summary>
    private static EvalResult<CountedResult> EvalResolvedCallbackCallCounted(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        // Charged dynamic invocation boundary. This is the single callback dispatch
        // chokepoint: the plain wrapper, the sequence-callback wrappers, and the
        // conditional-callback path all route through here, so a callback invocation is
        // charged exactly once regardless of callee shape.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return limitError;

        try
        {
            return EvalResolvedCallbackCallCountedCore(callee, args, ctx, valEnv, calleeName);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<CountedResult> EvalResolvedCallbackCallCountedCore(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName)
    {
        switch (callee)
        {
            case Algorithm.Builtin(var builtin):
                return ApplyBuiltinCountedResolved(
                    builtin,
                    args.Select(static arg => new ResolvedArgumentAlgorithm(
                        Algorithm: null,
                        SpreadsSequence: false)
                    {
                        PreparedValue = arg,
                    }).ToList(),
                    ctx,
                    valEnv);

            case Algorithm.Conditional:
                if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
                {
                    if (simpleCallee.Output.Count == 0)
                        return new EvalError.MissingOutput();

                    var countedEnvR = BindCountedCallbackParams(simpleCallee.Params, args);
                    if (countedEnvR.IsError)
                        return AttachImplicitParameterProvenance(countedEnvR.Error, simpleCallee);

                    var newCtx = WithCountedParameterEnvironments(ctx, countedEnvR.Value, simpleCallee.Params);
                    return EvalAlgOutputCounted(simpleCallee, newCtx, valEnv);
                }

                return EvalConditionalCallbackCallCounted(callee, args, ctx, valEnv, calleeName);

            default:
                {
                    if (callee.Output.Count == 0)
                        return new EvalError.MissingOutput();

                    if (UsesPatternBinding(callee))
                    {
                        var countedPatternEnvR = BindCountedParameterPatternList(
                            callee.ParameterPatterns,
                            args,
                            ctx,
                            (required, actual) => new EvalError.ArityMismatch(required, actual));
                        if (countedPatternEnvR.IsError)
                            return AttachImplicitParameterProvenance(countedPatternEnvR.Error, callee);

                        var patternBindings = countedPatternEnvR.Value;
                        var patternCtx = WithCountedParameterEnvironments(
                            ctx,
                            patternBindings.CountedBindings,
                            patternBindings.CountedBindings.Select(static binding => binding.Item1));
                        return EvalAlgOutputCounted(callee, patternCtx, valEnv);
                    }

                    // A flat callee with a top-level collecting parameter (`Rows.map(F)`
                    // with `F(x, *y, z)` or a single-collecting `Collect(*items)`)
                    // binds through the shared prefix/collecting/suffix binder so the
                    // collecting parameter COLLECTS an exact immutable list, after the
                    // same final-argument row expansion the fixed-only flat path
                    // uses below. Single-collecting callees keep the whole iterated
                    // element as one collected slot.
                    if (ParameterPattern.HasCollectingCaptureAtCurrentLevel(callee.ParameterPatterns))
                    {
                        var collectingPatternEnvR = BindCountedCallbackParameterPatternList(callee.ParameterPatterns, args, ctx);
                        if (collectingPatternEnvR.IsError)
                            return AttachImplicitParameterProvenance(collectingPatternEnvR.Error, callee);

                        var collectingBindings = collectingPatternEnvR.Value;
                        var collectingCtx = WithCountedParameterEnvironments(
                            ctx,
                            collectingBindings.CountedBindings,
                            collectingBindings.CountedBindings.Select(static binding => binding.Item1));
                        return EvalAlgOutputCounted(callee, collectingCtx, valEnv);
                    }

                    // Fixed-only flat callback binding projects each callback item
                    // into slots and binds those slots to the algorithm's flat
                    // parameter names (the final item is unpacked across any
                    // remaining names); it does not apply item-supply
                    // singleton-boundary normalization. Scalar callback
                    // deconstruction stays deferred so the counted callback path
                    // keeps Lean/C# parity.
                    var countedEnvR = BindCountedCallbackParams(callee.Params, args);
                    if (countedEnvR.IsError)
                        return AttachImplicitParameterProvenance(countedEnvR.Error, callee);

                    var newCtx = WithCountedParameterEnvironments(ctx, countedEnvR.Value, callee.Params);
                    return EvalAlgOutputCounted(callee, newCtx, valEnv);
                }
        }
    }

    /// <summary>
    /// Non-counted wrapper for callback dispatch that still preserves projected
    /// item emitted counts internally where downstream operations depend on
    /// them.
    /// </summary>
    private static EvalResult<Result> EvalResolvedCallbackCall(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
        => ProjectCountedValue(EvalResolvedCallbackCallCounted(callee, args, ctx, valEnv, calleeName));

    /// <summary>
    /// Evaluate a higher-order sequence callback on one iterated item.
    /// </summary>
    private static EvalResult<Result> EvalSequenceCallbackCall(
        Algorithm callee,
        CountedResult item,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCall(callee, [CountedSequenceCallbackItem(item)], ctx, valEnv, calleeName);

    /// <summary>
    /// Counted variant of <see cref="EvalSequenceCallbackCall"/>.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceCallbackCallCounted(
        Algorithm callee,
        CountedResult item,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
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
        IReadOnlyList<(string, Result)> valEnv)
    {
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

        return EvalOutputRowsPreparedCore(alg.Output, ctx.Push(alg), ctx, valEnv);
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
        IReadOnlyList<(string, Result)> valEnv)
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
        if (ReserveSequenceCapture(reserveCtx, results.Count, FirstSpan(rows)) is { } capturedLimitError)
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
        IReadOnlyList<(string, Result)> valEnv)
        => EvalOutputRowsPreparedCore(body, ctx, ctx, valEnv);

    private static EvalResult<CountedResult> EvalCaptureCountedCore(
        OutputBundle body,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
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
        IReadOnlyList<(string, Result)> valEnv)
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
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: body));

    private static EvalResult<CountedResult> EvalAlgOutputCountedCore(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
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
    // exact immutable list value. Unlike canonical arity capture (ordinary
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
