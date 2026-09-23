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
            Pattern.SequenceValue(var items) => MatchSequenceValuePattern(items, result, bindings),
        };

    private static bool MatchBindPattern(string name, Result result, List<(string Name, Result Value)> bindings)
    {
        var existing = LookupVal(bindings, name);
        if (existing is not null)
            return Result.ValueComparer.Equals(existing, result);

        bindings.Add((name, result));
        return true;
    }

    private static bool MatchSequenceValuePattern(
        IReadOnlyList<Pattern> items,
        Result result,
        List<(string Name, Result Value)> bindings)
    {
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
    }

    private static ValEnv? MatchPattern(Pattern pattern, Result result)
    {
        var bindings = new List<(string Name, Result Value)>();
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
    private static ValEnv? MatchCallPattern(
        Pattern pattern,
        IReadOnlyList<Result> explicitArgs)
    {
        if (pattern is Pattern.SequenceValue(var items))
        {
            if (items.Count != explicitArgs.Count)
                return null;

            var bindings = new List<(string Name, Result Value)>();
            for (var i = 0; i < items.Count; i++)
            {
                if (!MatchPattern(items[i], explicitArgs[i], bindings))
                    return null;
            }

            return bindings;
        }

        return explicitArgs.Count == 1 ? MatchPattern(pattern, explicitArgs[0]) : null;
    }

    private static (CondBranch Branch, ValEnv Bindings)? MatchCallBranches(
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

    /// <summary>
    /// Counted twin of the plain <c>MatchPattern</c> above,
    /// dispatched the same compiler-exhaustive way over the closed Pattern hierarchy.
    /// </summary>
    private static bool MatchCountedPattern(
        Pattern pattern,
        CountedResult result,
        List<(string Name, CountedResult Value)> bindings)
        => pattern switch
        {
            Pattern.Bind(var name) => MatchCountedBindPattern(name, result, bindings),
            // Structural numeric equality, mirroring the plain MatchPattern arm.
            Pattern.LitInt(var n) => result.Value is Result.Atom(var v) && v.Equals(n),
            Pattern.LitString(var s) => result.Value is Result.Str(var sv)
                && string.Equals(sv, s, StringComparison.Ordinal),
            Pattern.LitBool(var b) => result.Value is Result.Bool(var bv) && bv == b,
            Pattern.SequenceValue(var items) => MatchCountedSequenceValuePattern(items, result, bindings),
        };

    private static bool MatchCountedBindPattern(
        string name,
        CountedResult result,
        List<(string Name, CountedResult Value)> bindings)
    {
        var existing = LookupCountedParam(bindings, name);
        if (existing is not null)
            return Result.ValueComparer.Equals(existing.Value.Value, result.Value);

        bindings.Add((name, result));
        return true;
    }

    private static bool MatchCountedSequenceValuePattern(
        IReadOnlyList<Pattern> items,
        CountedResult result,
        List<(string Name, CountedResult Value)> bindings)
    {
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
    }

    private static CountedParamEnv? MatchCountedPattern(
        Pattern pattern,
        CountedResult result)
    {
        var bindings = new List<(string Name, CountedResult Value)>();
        return MatchCountedPattern(pattern, result, bindings) ? bindings : null;
    }

    private static CountedParamEnv? MatchCountedCallPattern(
        Pattern pattern,
        IReadOnlyList<CountedResult> explicitArgs)
    {
        if (pattern is Pattern.SequenceValue(var items))
        {
            if (items.Count != explicitArgs.Count)
                return null;

            var bindings = new List<(string Name, CountedResult Value)>();
            for (var i = 0; i < items.Count; i++)
            {
                if (!MatchCountedPattern(items[i], explicitArgs[i], bindings))
                    return null;
            }

            return bindings;
        }

        return explicitArgs.Count == 1 ? MatchCountedPattern(pattern, explicitArgs[0]) : null;
    }

    private static (CondBranch Branch, CountedParamEnv Bindings)? MatchCountedCallBranches(
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
            ParameterPatterns: [],
            Opens: [],
            Properties: [],
            Output: output);

        // Record the completed wrapper, not merely a request that entered this helper.
        ctx.Observations?.RecordCountedArgumentReification();
        return algorithm;
    }

    /// <summary>
    /// The flat-callback row convention for a pre-evaluated callback argument:
    /// a final sequence-valued argument may unpack across remaining parameters;
    /// exact lists stay opaque. Ordinary direct calls keep one slot per argument.
    /// </summary>
    private static IReadOnlyList<CountedResult> UnpackCountedArg(CountedResult arg)
        => UnpackArgs(arg.Value)
            .Select(value => new CountedResult(value, value.ValueCount()))
            .ToList();

    /// <summary>
    /// Bind callback parameters with the item's ordinary value-boundary count,
    /// just like <c>S:i</c>, without making them callable algorithms.
    /// </summary>
    private static EvalResult<CountedParamEnv> BindCountedCallbackParams(
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

        var bindings = new List<(string Name, CountedResult Value)>(paramNames.Count);
        for (var i = 0; i < paramNames.Count; i++)
            bindings.Add((paramNames[i], boundValues[i]));

        return EvalResult<CountedParamEnv>.Ok(bindings);
    }

    /// <summary>
    /// Callback binding for a flat callee whose top-level parameters include a
    /// collecting parameter. The callback argument supply keeps the established
    /// flat-callback row convention: when fewer argument slots are supplied
    /// than top-level parameters, the final supplied argument opens into its
    /// items (sequence rows only; exact lists stay opaque), exactly
    /// as <see cref="BindCountedCallbackParams"/> does for fixed-only flat
    /// callees. The resulting slots then bind through the shared
    /// prefix/collecting/suffix binder, so the collecting parameter COLLECTS its allocated
    /// slots as one list under the collector supply-boundary law
    /// (<see cref="CollectorSupply"/>): a whole callback argument is a written
    /// slot (a lone sequence item on a single-collecting callee opens one level —
    /// <c>((1, 2), (3, 4)).map(Coll)</c> is <c>[[1, 2], [3, 4]]</c>), while
    /// row-unpacked slots are final items. Lean:
    /// <c>bindCountedCallbackParameterPatternList</c>.
    /// </summary>
    private static EvalResult<CountedParameterPatternBindings> BindCountedCallbackParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx)
    {
        IReadOnlyList<CountedPatternInput> slots;
        if (args.Count > 0 && args.Count < patterns.Count)
        {
            var expanded = new List<CountedPatternInput>(patterns.Count);
            for (var index = 0; index < args.Count - 1; index++)
                expanded.Add(new CountedPatternInput(args[index], SupplyOrigin.WrittenSlot));
            foreach (var slot in UnpackCountedArg(args[^1]))
                expanded.Add(new CountedPatternInput(slot, SupplyOrigin.FinalItem));
            slots = expanded;
        }
        else
        {
            slots = WrittenCallbackInputs(args);
        }

        return BindCountedParameterPatternList(
            patterns,
            slots,
            ctx,
            static (required, actual) => new EvalError.ArityMismatch(required, actual));
    }

    /// <summary>
    /// One counted binder input (the callback binding path): the counted value plus
    /// its <see cref="SupplyOrigin"/>. Lean: <c>CountedPatternInput</c>.
    /// </summary>
    private readonly record struct CountedPatternInput(CountedResult Counted, SupplyOrigin Origin);

    /// <summary>Whole callback arguments are written slots (Lean: `origin := .writtenSlot`).</summary>
    private static IReadOnlyList<CountedPatternInput> WrittenCallbackInputs(IReadOnlyList<CountedResult> args)
    {
        var inputs = new CountedPatternInput[args.Count];
        for (var index = 0; index < args.Count; index++)
            inputs[index] = new CountedPatternInput(args[index], SupplyOrigin.WrittenSlot);
        return inputs;
    }

    /// <summary>Already-opened slots (a reducer's accumulator state) are final items (Lean: `origin := .finalItem`).</summary>
    private static IReadOnlyList<CountedPatternInput> FinalCallbackInputs(IReadOnlyList<CountedResult> args)
    {
        var inputs = new CountedPatternInput[args.Count];
        for (var index = 0; index < args.Count; index++)
            inputs[index] = new CountedPatternInput(args[index], SupplyOrigin.FinalItem);
        return inputs;
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
                    // The callback value opens through the SAME nested-pattern rule
                    // as the ordinary binder (SequenceValuePatternItems): a sequence
                    // or list value opens one level, and any other value is a
                    // one-item supply at every level and for every group size, so
                    // `map([7], P)` with `P((x, *rest))` binds `x = 7, rest = []`
                    // exactly like `P(7)`, and `P((x, y))` rejects a scalar with the
                    // nested group's ordinary ArityMismatch(2, 1) in both
                    // (September 2026, S3; the callback path formerly fell back only
                    // for one-item groups). Lean: bindCountedParameterPattern.
                    //
                    // Pattern-opened items are FINAL supply items: a nested
                    // collecting binding collects them exactly (one boundary
                    // opened, never two).
                    var nestedInputs = SequenceValuePatternItems(input.Value)
                        .Select(static item => new CountedPatternInput(
                            new CountedResult(item, item.ValueCount()),
                            SupplyOrigin.FinalItem))
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

    /// <summary>
    /// The counted twin of <see cref="BindParameterPatternList"/> — the callback binding path
    /// (Lean <c>bindCountedParameterPatternList</c>) — with the same order: the arity check;
    /// every range binds ALL of its patterns before its repeated names are decided; the prefix
    /// binds and settles before the suffix, the collector is materialized after both, and the
    /// names shared across the collector are decided last. Each repeated name is decided ONCE,
    /// symmetrically, when its last contribution joins (counted contributions carry only the
    /// counted channel, so an unequal repeat is <see cref="EvalError.BadArity"/>). The first
    /// collecting capture is the list's collector; a second one (host-built only) is a suffix
    /// pattern that <see cref="BindCountedParameterPattern"/> rejects.
    /// </summary>
    private static EvalResult<CountedParameterPatternBindings> BindCountedParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<CountedPatternInput> inputs,
        EvalCtx ctx,
        Func<int, int, EvalError> arityMismatch)
    {
        var collectingIndex = FirstCollectingCaptureIndex(patterns);
        var requiredCount = ParameterPattern.MinimumSuppliedSlots(patterns);
        if (collectingIndex < 0)
        {
            if (inputs.Count != requiredCount)
                return arityMismatch(requiredCount, inputs.Count);

            var rangeR = BindCountedParameterPatternRange(patterns, inputs, 0, 0, patterns.Count, ctx, outside: null);
            if (rangeR.IsError) return rangeR.Error;
            return EvalResult<CountedParameterPatternBindings>.Ok(
                new CountedParameterPatternBindings(rangeR.Value.Merged.CountedBindings));
        }

        if (inputs.Count < requiredCount)
            return arityMismatch(requiredCount, inputs.Count);

        var collectingCapture = (CaptureParameterPattern)patterns[collectingIndex];
        var suffixStart = collectingIndex + 1;
        var suffixCount = patterns.Count - suffixStart;
        var suffixInputStart = inputs.Count - suffixCount;

        var prefixR = BindCountedParameterPatternRange(
            patterns, inputs, 0, 0, collectingIndex, ctx,
            new LevelNames(patterns, suffixStart, suffixCount, collectingCapture.Name));
        if (prefixR.IsError) return prefixR.Error;

        var suffixR = BindCountedParameterPatternRange(
            patterns, inputs, suffixStart, suffixInputStart, suffixCount, ctx,
            new LevelNames(patterns, 0, collectingIndex, collectingCapture.Name));
        if (suffixR.IsError) return suffixR.Error;

        var segmentCount = suffixInputStart - collectingIndex;
        var capturedValues = new List<Result>(segmentCount);
        var capturedOrigins = new List<SupplyOrigin>(segmentCount);
        for (var inputIndex = collectingIndex; inputIndex < suffixInputStart; inputIndex++)
        {
            capturedValues.Add(inputs[inputIndex].Counted.Value);
            capturedOrigins.Add(inputs[inputIndex].Origin);
        }

        // Collecting binding COLLECTS the collector supply of its allocated
        // segment (CollectorSupply: exact, except that one lone written sequence
        // slot opens one level) as one exact immutable list value, emitted
        // count 1 (a list is one visible value).
        var capturedResultR = CollectSegment(ctx, CollectorSupply(capturedValues, capturedOrigins), collectingCapture.Span);
        if (capturedResultR.IsError) return capturedResultR.Error;
        var collector = new UserCallBindings(
            [],
            [(collectingCapture.Name, new CountedResult(capturedResultR.Value, 1))],
            []);

        var bindings = new PatternBindingAccumulator();
        bindings.Add(prefixR.Value.Merged);
        bindings.Add(suffixR.Value.Merged);
        bindings.Add(collector);
        if ((bindings.SawRepeatedName || prefixR.Value.HadRepeatedName || suffixR.Value.HadRepeatedName)
            && FindCrossRepeatedNameFailure(
                prefixR.Value,
                collectingCapture.Name,
                collector,
                suffixR.Value,
                new LevelNames(patterns, suffixStart, suffixCount, extraName: null)) is { } failure)
        {
            return failure;
        }

        return EvalResult<CountedParameterPatternBindings>.Ok(
            new CountedParameterPatternBindings(bindings.ToBindings().CountedBindings));
    }

    /// <summary>
    /// Counted twin of <see cref="BindParameterPatternRange"/> (Lean <c>bindPairs</c>): every
    /// pattern of the range binds, left to right, before the range decides the repeated names
    /// whose every contribution it holds. Counted contributions are carried as counted-only
    /// <see cref="UserCallBindings"/> so both binders share one verdict.
    /// </summary>
    private static EvalResult<PatternRangeBindings> BindCountedParameterPatternRange(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<CountedPatternInput> inputs,
        int patternStart,
        int inputStart,
        int count,
        EvalCtx ctx,
        LevelNames? outside)
    {
        if (count == 0)
            return EvalResult<PatternRangeBindings>.Ok(new PatternRangeBindings(new UserCallBindings([], [], []), null));

        if (count == 1)
        {
            var singleR = BindCountedParameterPattern(patterns[patternStart], inputs[inputStart].Counted, ctx);
            if (singleR.IsError) return singleR.Error;
            return EvalResult<PatternRangeBindings>.Ok(new PatternRangeBindings(AsCountedContribution(singleR.Value), null));
        }

        var bound = new UserCallBindings[count];
        for (var offset = 0; offset < count; offset++)
        {
            var boundR = BindCountedParameterPattern(patterns[patternStart + offset], inputs[inputStart + offset].Counted, ctx);
            if (boundR.IsError) return boundR.Error;
            bound[offset] = AsCountedContribution(boundR.Value);
        }

        var bindings = new PatternBindingAccumulator();
        foreach (var patternBindings in bound)
            bindings.Add(patternBindings);

        if (bindings.SawRepeatedName && FindRangeRepeatedNameFailure(bound, outside) is { } failure)
            return failure;

        return EvalResult<PatternRangeBindings>.Ok(
            new PatternRangeBindings(bindings.ToBindings(), bound, bindings.SawRepeatedName));
    }

    private static UserCallBindings AsCountedContribution(CountedParameterPatternBindings bindings)
        => new([], bindings.CountedBindings, []);

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
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        ValEnv valEnv,
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
        ValEnv valEnv,
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

                    var parameterNames = simpleCallee.Params;
                    var countedEnvR = BindCountedCallbackParams(parameterNames, args);
                    if (countedEnvR.IsError)
                        return AttachImplicitParameterProvenance(countedEnvR.Error, simpleCallee);

                    var newCtx = WithCountedParameterEnvironments(ctx, countedEnvR.Value, parameterNames);
                    return EvalAlgOutputCounted(simpleCallee, newCtx, valEnv);
                }

                return EvalConditionalCallbackCallCounted(callee, args, ctx, valEnv, calleeName);

            default:
                {
                    if (callee.Output.Count == 0)
                        return new EvalError.MissingOutput();

                    if (UsesPatternBinding(callee))
                    {
                        // Whole callback arguments are written slots; the
                        // sequence-value patterns open them and their items are final.
                        // Each supplied callback value binds exactly as the ordinary
                        // call `P(V)` binds it: the same slot allocation and the same
                        // nested-pattern opening (SequenceValuePatternItems), with no
                        // row expansion.
                        var countedPatternEnvR = BindCountedParameterPatternList(
                            callee.ParameterPatterns,
                            WrittenCallbackInputs(args),
                            ctx,
                            (required, actual) => new EvalError.ArityMismatch(required, actual));
                        if (countedPatternEnvR.IsError)
                            return AttachImplicitParameterProvenance(countedPatternEnvR.Error, callee);

                        var patternBindings = countedPatternEnvR.Value;
                        var patternCtx = WithCountedParameterEnvironments(
                            ctx,
                            patternBindings.CountedBindings,
                            patternBindings.CountedBindings.Select(static binding => binding.Name));
                        return EvalAlgOutputCounted(callee, patternCtx, valEnv);
                    }

                    // A flat callee with a top-level collecting parameter (`Rows.map(F)`
                    // with `F(x, *y, z)` or a single-collecting `Collect(*items)`)
                    // binds through the shared prefix/collecting/suffix binder so the
                    // collecting parameter COLLECTS one list, after the
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
                            collectingBindings.CountedBindings.Select(static binding => binding.Name));
                        return EvalAlgOutputCounted(callee, collectingCtx, valEnv);
                    }

                    // Fixed-only flat callback binding keeps each selected item
                    // whole unless the final sequence row must unpack across
                    // remaining parameter names; it does not apply item-supply
                    // singleton-boundary normalization. No nested pattern is
                    // involved here (a callee with one routes to the patterned
                    // branch above), so the row convention is the whole callback
                    // supply-shape policy of this path.
                    var parameterNames = callee.Params;
                    var countedEnvR = BindCountedCallbackParams(parameterNames, args);
                    if (countedEnvR.IsError)
                        return AttachImplicitParameterProvenance(countedEnvR.Error, callee);

                    var newCtx = WithCountedParameterEnvironments(ctx, countedEnvR.Value, parameterNames);
                    return EvalAlgOutputCounted(callee, newCtx, valEnv);
                }
        }
    }

    /// <summary>
    /// The value projection of counted callback dispatch. Callback items retain
    /// their ordinary value-boundary counts inside the counted implementation.
    /// </summary>
    private static EvalResult<Result> EvalResolvedCallbackCall(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName = "conditional")
        => ProjectCountedValue(EvalResolvedCallbackCallCounted(callee, args, ctx, valEnv, calleeName));

    /// <summary>
    /// Evaluate a higher-order sequence callback on one iterated item.
    /// </summary>
    private static EvalResult<Result> EvalSequenceCallbackCall(
        Algorithm callee,
        CountedResult item,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCall(callee, [CountedSequenceCallbackItem(item)], ctx, valEnv, calleeName);

    /// <summary>
    /// Counted variant of <see cref="EvalSequenceCallbackCall"/>.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceCallbackCallCounted(
        Algorithm callee,
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
