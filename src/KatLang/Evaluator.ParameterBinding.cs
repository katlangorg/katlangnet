using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang;

/// <summary>
/// Parameter binding support (the "Bind parameters" section): the resolved-argument and
/// variadic-item records, loop-step binding preparation, written-slot sequence items, the
/// structural-pattern and repeated-name binding diagnostics, and the shared deconstruction
/// projection. Supply formation and the one inspecting binder live in <c>Evaluator.Needs.cs</c>.
/// Part of the <see cref="Evaluator"/> partial class; the central state, lookup and open resolution,
/// the built-in prelude, and the run entry points remain in <c>Evaluator.cs</c>.
/// </summary>
public static partial class Evaluator
{
    // ── Bind parameters ─────────────────────────────────────────────────────

    private readonly record struct VariadicCallItem(
        Result? Value,
        Algorithm? Algorithm,
        EvalError? ValueError,
        Expr? Source = null,
        Algorithm? Callable = null,
        NeedCell? Cell = null)
    {
        /// <summary>
        /// The algorithm this item NAMES: the identity the zero-argument value-demand law
        /// judges — the projected <see cref="Callable"/> when the item has one (a supplied
        /// cell whose VALUE demand failed, <see cref="FinishNeedCallItemDemand"/>), otherwise
        /// the value-side <see cref="Algorithm"/>, which a VALUE demand evaluates.
        /// Lean: <c>CallableCallItem.named?</c>.
        /// </summary>
        public Algorithm? NamedAlgorithm => Callable ?? Algorithm;
    }

    /// <summary>
    /// One argument a builtin receives. Every argument the evaluator builds is a SUPPLIED
    /// CELL (<see cref="Cell"/>): a builtin call passes its supply
    /// (<see cref="ResolveNeedSupply"/>, explicit spreads already opened), a builtin loop step
    /// its state cells and a builtin callback its element cells; a VALUE slot demands the cell
    /// and an invoking slot projects it, while <see cref="Algorithm"/> is <c>null</c>. An
    /// argument WITHOUT a cell is the direct-invocation seam that hand-built test plans use: a
    /// VALUE slot then demands <see cref="Algorithm"/> through the zero-argument law, and an
    /// invoking slot calls it. Lean: <c>ResolvedArgumentAlgorithm</c>.
    /// </summary>
    internal readonly record struct ResolvedArgumentAlgorithm(Algorithm? Algorithm)
    {
        internal NeedCell? Cell { get; init; }

        /// <summary>
        /// The argument's WRITTEN slot at this call, recorded from the supply formation
        /// (<see cref="ResolveNeedSupply"/> — the slot as written; for a transported collector
        /// slice, each cell's own original source): the demand-site identity a builtin VALUE
        /// slot's rejection reports through (<see cref="SequenceBuiltinValueDemandError"/> and
        /// the zero-argument value-demand law, <see cref="ZeroArgumentValueDemandError"/>) —
        /// its span, and whether the argument was written as a property, a parameter, a dot
        /// receiver, or a block. <c>null</c> for an opened spread's items. Diagnostic identity
        /// only: it never changes which callable a slot resolves to. Lean: <c>source?</c>.
        /// </summary>
        public Expr? Source { get; init; }
    }

    private readonly record struct GenericLoopStepBindingContract(
        IReadOnlyList<ParameterDeclaration> Parameters,
        IReadOnlyList<ParameterPattern> ParameterPatterns,
        IReadOnlyList<string> ParameterNames);

    /// <summary>
    /// The binding plan of a USER loop step for the planner's shape gate
    /// (<see cref="IsOptimizedLoopShapeEligible"/>), or <c>null</c> when the plan cannot be built. A
    /// step that is not a user algorithm never reaches this method, so <c>null</c> has exactly one
    /// meaning here: a refused construction (F7-D6).
    /// <para><see cref="CallableBindingPlan.FromSignature"/> refuses, with an
    /// <see cref="InvalidOperationException"/>, a head it cannot represent. That includes two
    /// collecting captures at one pattern level, and signature facts that disagree with the patterns.
    /// The pre-evaluation gate refuses the two-collector head (X-02). Such a head therefore reaches a
    /// loop only through a host-built head a host operation rewrote after the gate. Host-built
    /// parent scopes are covered by that gate (owner decision, 2026-10-12).</para>
    /// <para>The catch is meant for those refusals. Any other <see cref="InvalidOperationException"/>
    /// raised while the head is read, for example by a host's own list, also takes the generic
    /// route, which then reads the same head itself. Construction runs no KatLang code: it evaluates
    /// nothing, charges no budget and observes no cancellation. So the catch never sees an evaluation
    /// failure, a resource limit or a cancellation.</para>
    /// </summary>
    private static CallableBindingPlan? TryCreateUserLoopStepBindingPlan(Algorithm.User step)
    {
        try
        {
            var signature = CallableSignature.FromUserAlgorithm("loop step", step);
            return CallableBindingPlan.FromSignature(signature);
        }
        catch (InvalidOperationException)
        {
            return null;
        }
    }

    /// <summary>
    /// The planned loop's step-shape gate. It FAILS CLOSED (F7-D6): a USER step is eligible only
    /// when its binding plan is BUILT and shows flat fixed captures with distinct names, the one
    /// shape the planned frame binds by position. A plan that cannot be built is no evidence of
    /// eligibility, so the loop runs the generic route, as a patterned or collecting step does.
    /// Every other callable shape has no binding plan: it passes this gate, and the planner refuses
    /// it as an unsupported step shape (Q-23).
    /// </summary>
    private static bool IsOptimizedLoopShapeEligible(
        Algorithm step,
        out string? fallbackReason)
    {
        if (step is not Algorithm.User userStep)
        {
            fallbackReason = null;
            return true;
        }

        if (TryCreateUserLoopStepBindingPlan(userStep) is not { } plan)
        {
            fallbackReason = "loop step binding plan unavailable";
            return false;
        }

        if (plan.RequiresPatternedBinding || plan.HasTopLevelCollecting)
        {
            fallbackReason = "variadic loop step";
            return false;
        }

        fallbackReason = null;
        return true;
    }

    /// <summary>
    /// The loop-invariant part of a USER step's generic execution, prepared ONCE per loop
    /// invocation and reused by every iteration (M16). It holds the snapshot of the step's
    /// binding contract, frozen against host mutation, and the contract's need-pattern view.
    /// Both depend only on the step algorithm, never on iteration state. Each iteration binds
    /// its state cells through the one binder and shadows the inherited environments by the
    /// step's names (<see cref="InvokeLoopStepSupply"/>), and the binding's fresh environments
    /// are part of the zero-arg cache key.
    /// Nothing prepared here is consulted when the step's rows form the next state: the
    /// parameter patterns BIND the incoming state only, and the next state is the step's
    /// row supply (<see cref="EvalAlgOutputSlots"/>) whatever the pattern category
    /// (LOOP-03; Q-24 retired the former pattern-triggered packing of a spread row).
    /// </summary>
    private readonly record struct PreparedGenericLoopStep(
        GenericLoopStepBindingContract BindingContract,
        IReadOnlyList<NeedPattern> NeedPatterns);

    /// <summary>
    /// Freezes the temporary algorithm-shaped view used to derive the step's binding
    /// contract. Public
    /// host-built AST records may retain caller-owned <see cref="IReadOnlyList{T}"/>
    /// instances, so reading the original user algorithm again after a callback could
    /// mix a prepared binding for the old shape with parameter lists mutated to a new
    /// shape. The returned copy is used only while preparation derives the narrow
    /// <see cref="GenericLoopStepBindingContract"/> and its need patterns; it is not stored
    /// in the prepared object. Executable body, scope, properties, and opens remain on
    /// <paramref name="step"/> and are evaluated normally every iteration.
    /// </summary>
    private static Algorithm SnapshotGenericLoopStepBindingContract(Algorithm step)
    {
        if (step is not Algorithm.User user)
            return step;

        // The ONE parameter channel is snapshotted; Parameters and Params derive from it, so the
        // prepared view cannot observe a host mutation of the original pattern lists.
        return user with { ParameterPatterns = SnapshotParameterPatterns(user.ParameterPatterns) };
    }

    /// <summary>
    /// Iterative, DAG-preserving snapshot of recursive pattern-list membership. Capture
    /// records are immutable and can be shared; structural nodes (sequence and list
    /// patterns) are rebuilt with their kind so a host cannot mutate a retained nested
    /// <c>Items</c> list during the loop.
    /// Structural preflight has already rejected cycles before evaluation reaches this
    /// helper.
    /// </summary>
    private static IReadOnlyList<ParameterPattern> SnapshotParameterPatterns(
        IReadOnlyList<ParameterPattern> source)
    {
        if (source.Count == 0)
            return [];

        var snapshots = new Dictionary<ParameterPattern, ParameterPattern>(
            ReferenceEqualityComparer.Instance);
        var states = new Dictionary<ParameterPattern, byte>(
            ReferenceEqualityComparer.Instance);
        var stack = new Stack<(ParameterPattern Group, bool Expanded)>();

        foreach (var pattern in source)
        {
            if (ParameterPattern.StructuralItems(pattern) is null || snapshots.ContainsKey(pattern))
                continue;

            stack.Push((pattern, Expanded: false));
            while (stack.Count != 0)
            {
                var (group, expanded) = stack.Pop();
                if (snapshots.ContainsKey(group))
                    continue;

                if (!expanded)
                {
                    if (states.TryGetValue(group, out var state) && state == 1)
                        throw new InvalidOperationException("Cyclic parameter pattern reached loop preparation after structural preflight.");

                    states[group] = 1;
                    stack.Push((group, Expanded: true));
                    var groupItems = ParameterPattern.StructuralItems(group)!;
                    for (var index = groupItems.Count - 1; index >= 0; index--)
                    {
                        var child = groupItems[index];
                        if (ParameterPattern.StructuralItems(child) is not null
                            && !snapshots.ContainsKey(child))
                        {
                            stack.Push((child, Expanded: false));
                        }
                    }

                    continue;
                }

                var sourceItems = ParameterPattern.StructuralItems(group)!;
                var items = new ParameterPattern[sourceItems.Count];
                for (var index = 0; index < sourceItems.Count; index++)
                {
                    var item = sourceItems[index];
                    items[index] = ParameterPattern.StructuralItems(item) is not null
                        ? snapshots[item]
                        : item;
                }

                snapshots[group] = ParameterPattern.WithStructuralItems(group, items);
                states[group] = 2;
            }
        }

        var result = new ParameterPattern[source.Count];
        for (var index = 0; index < source.Count; index++)
        {
            var pattern = source[index];
            result[index] = ParameterPattern.StructuralItems(pattern) is not null
                ? snapshots[pattern]
                : pattern;
        }

        return result;
    }

    /// <summary>
    /// Prepares the invariant generic loop-step state. Non-evaluating and infallible:
    /// it charges no budget, observes no cancellation, resolves no names, and invokes
    /// no callbacks, so both the synchronous generic loops and their async twins share
    /// this ONE implementation (the M7/M10 twin rule: share non-evaluating
    /// preparation, mirror evaluating work). Callers prepare only when the loop will
    /// run at least one iteration — a zero-iteration loop must not gain preparation
    /// work it never had.
    /// </summary>
    private static PreparedGenericLoopStep PrepareGenericLoopStep(Algorithm step, EvalCtx ctx)
    {
        ctx.Observations?.RecordGenericLoopStepBindingPreparation();
        var bindingContract = SnapshotGenericLoopStepBindingContract(step);
        return new PreparedGenericLoopStep(
            new GenericLoopStepBindingContract(
                bindingContract.Parameters,
                bindingContract.ParameterPatterns,
                bindingContract.Params.ToArray()),
            NeedParameterPatterns(bindingContract.ParameterPatterns));
    }

    private static EvalResult<IReadOnlyList<Result>> EvalExplicitSequenceValueItems(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value));
        }

        if (alg.FindDuplicatePropName() is { } duplicateName)
            return new EvalError.DuplicateProperty(duplicateName);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output.Count: 0 })
            return new EvalError.MissingOutput();

        return EvalExplicitSequenceValueRowSlots(alg.Output, EnterAlgorithmBody(alg, ctx, valEnv), valEnv);
    }

    /// <summary>
    /// The shared written-slot loop over ordered bundle rows: each row
    /// contributes its explicit written slots. Algorithm-shaped groupings reach
    /// it after pushing their own scope; a <see cref="Expr.Capture"/> body
    /// reaches it directly (captures own no scope).
    ///
    /// <para>Carries the structural-nesting stack backstop (mirrored verbatim by the
    /// async twin <see cref="EvalExplicitSequenceValueRowSlotsAsync"/>; rationale on
    /// <see cref="EvalOutputRowsPreparedCore"/>): nested written groups recurse through
    /// this family without touching the ordinary dispatch or any invocation
    /// chokepoint, so the probe fires once per nesting level here too.</para>
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>> EvalExplicitSequenceValueRowSlots(
        IReadOnlyList<Expr> rows,
        EvalCtx rowCtx,
        ValEnv valEnv)
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        var slots = new List<Result>();
        // SEC-01: an overflowed group forms count-only; its owner's reservation refuses the full size.
        TransientSupply bound = default;
        foreach (var expr in rows)
        {
            var exprSlotsR = EvalExplicitSequenceValueExprSlots(expr, rowCtx, valEnv);
            // A row is a SUBORDINATE computation of the body or capture (Q-36).
            if (exprSlotsR.IsError) return NestMissingOutput(exprSlotsR.Error);
            AddSlotsBounded(slots, exprSlotsR.Value, rowCtx.Budget, ref bound, expr is Expr.SequenceSpread);
        }

        return bound.Overflowed
            ? RefuseOverflowedCaptureAtRows(rowCtx.Budget, bound, rows)
            : EvalResult<IReadOnlyList<Result>>.Ok(slots);
    }

    private static EvalResult<IReadOnlyList<Result>> EvalExplicitSequenceValueExprSlots(
        Expr expr,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // A nested capture element (a multi-slot group `((1, 2), 3)`, a lone
        // spread group `(A*)`, or a host-built single-row capture — the parser
        // writes `(A)` as `A`) materializes exactly one element, combined with
        // the same shallow singleton-erasing rule, and reserved by the same owner
        // (MakeCheckedSequenceCaptureAtRows, through the MakeCheckedUnfoldedSlot
        // leaf), as ordinary capture evaluation: a lone row IS its already-evaluated
        // value and an all-spread-empty group is `()` — never a
        // literal-unwritable orphan such as `(5)`. This is the same value
        // EvalCounted produces for the node, unfolded one level so nested
        // groups recurse through this family (see the stack backstop note on
        // EvalExplicitSequenceValueRowSlots); a zero-parameter scoped block
        // element unfolds through its algorithm the same way.
        // Both unfolding arms POSITION their failure at the written slot with the very
        // rule EvalCounted applies to the same node, because they are the only two arms
        // that bypass it: every other slot kind falls through to EvalCounted below and is
        // positioned there. Without this a written block element reported its missing
        // output with NO span at all (`[1, { }, 3]`), while the same element inside a
        // parenthesized group — which reaches EvalCounted's own Capture arm — was located
        // exactly. AtSpanIfMissing keeps a span the inner failure already carries, so a
        // nested slot still reports at its own precise location.
        if (expr is Expr.Capture(var captureBody))
        {
            var nestedItemsR = WithPreferredSpanOf(
                expr, captureBody, EvalExplicitSequenceValueRowSlots(captureBody, ctx, valEnv));
            if (nestedItemsR.IsError) return nestedItemsR.Error;

            return MakeCheckedUnfoldedSlot(ctx.Budget, nestedItemsR.Value, expr, captureBody);
        }

        if (expr is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            // Only the plain-output arm may bypass the demand funnel. Zero captures
            // do not imply zero supplied slots, and a family must dispatch its branch.
            if (!RequiresZeroArgumentSupplyBinding(wired))
            {
                // The block span rule is EvalAlgorithmExprValue's: the written block, else
                // its first positioned output row.
                var nestedItemsR = WithPreferredSpanOf(
                    expr, wired.Output, EvalExplicitSequenceValueItems(wired, ctx, valEnv));
                if (nestedItemsR.IsError) return nestedItemsR.Error;

                return MakeCheckedUnfoldedSlot(ctx.Budget, nestedItemsR.Value, expr, wired.Output);
            }
        }

        var countedR = EvalCounted(expr, ctx, valEnv);
        if (countedR.IsError) return countedR.Error;

        // WRITTEN-SLOT REIFICATION: a non-spread expression occupying one
        // written slot contributes exactly ONE persistent value — the value its
        // counted supply denotes — regardless of how many items the expression
        // emitted (zero, one, or many; a counted-multi supply such as a loop
        // result is already represented by one structural value). Only an
        // explicit spread supplies the value's items into the surrounding item slots.
        return expr is Expr.SequenceSpread
            ? EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value))
            : EvalResult<IReadOnlyList<Result>>.Ok([countedR.Value.Value]);
    }

    /// <summary>
    /// An ordinary structural pattern that received a value of another kind — a sequence
    /// pattern given a list or a scalar, a list pattern given a sequence or a scalar — fails
    /// its binding with this <see cref="EvalError.TypeMismatch"/>, naming the written pattern
    /// and the value received. A right-kind value with the wrong number of elements is the
    /// group's ordinary arity mismatch instead (<see cref="StructuralPatternArityMismatch"/>).
    /// A clause family never raises it: there a mismatch only rejects the clause.
    /// Lean: <c>structuralPatternKindMismatch</c>.
    /// </summary>
    private static EvalError StructuralPatternKindMismatch(ParameterPattern pattern, Result value)
        => new EvalError.TypeMismatch(pattern is ListValueParameterPattern
            ? $"list pattern `{pattern.DisplayName}` expects a list value, but received {DescribeOperand(value)}"
            : $"sequence pattern `{pattern.DisplayName}` expects a sequence value, but received {DescribeOperand(value)}");

    /// <summary>
    /// Arity mismatch produced by binding one nested structural pattern's OWN items — a
    /// right-kind value with the wrong number of elements. The structured payload keeps the
    /// innermost Lean-aligned <see cref="EvalError.ArityMismatch"/> unchanged; the added
    /// context only attributes the failure to the written pattern (e.g. <c>(b, c)</c> or
    /// <c>[b, c]</c>) instead of the enclosing call's argument count: a sequence pattern
    /// through <see cref="SequenceValueParameterBindingContext"/>, a list pattern through
    /// <see cref="ListValueParameterBindingContext"/>. Genuine top-level call-arity mismatches
    /// and argument evaluation errors passing through the binder are never wrapped.
    /// </summary>
    private static EvalError StructuralPatternArityMismatch(
        ParameterPattern group,
        int required,
        int actual)
    {
        var items = ParameterPattern.StructuralItems(group)
            ?? throw new InvalidOperationException("Only a structural pattern has its own items to bind.");
        var hasCollecting = items.Any(static item => item is CaptureParameterPattern { Kind: ParameterKind.Collecting });
        ErrorContext context = group is ListValueParameterPattern
            ? new ListValueParameterBindingContext(group.DisplayName, hasCollecting)
            : new SequenceValueParameterBindingContext(group.DisplayName, hasCollecting);
        return new EvalError.WithContext(context, new EvalError.ArityMismatch(required, actual));
    }

    /// <summary>
    /// The context of NEED-04's value verdict: the occurrences of one repeated parameter
    /// name received unequal VALUE contributions (the binder's <c>BadArity</c>, unchanged by
    /// Q-27). Lean: <c>bindNeedPatterns</c>.
    /// </summary>
    private static string RepeatedParameterContext(string name)
        => $"repeated parameter '{name}' requires equal arguments";

    /// <summary>
    /// NEED-04's VALUE agreement between two demanded contributions of one repeated name: exactly
    /// the <see cref="Result.ValueComparer"/> verdict, charged to the run's budget like every
    /// evaluator-owned comparison (SEC-02-FU, <see cref="Result.EvaluatorValueEquals"/>). A
    /// comparison with structural or long-string work runs through <paramref name="session"/>, the
    /// binder activation's one operation comparer, created on first use, so the agreements of one
    /// head reuse the verdicts of the shared subgraphs they already walked; it dies with the
    /// activation. A refusal is returned as the error it is — the caller must never turn it into
    /// the agreement's <c>BadArity</c> or a clause non-match.
    /// </summary>
    private static EvalResult<bool> RepeatedValueEquals(
        ref Result.ValueSemanticComparer? session, Result before, Result value, EvalCtx ctx)
    {
        if (!Result.ValueSemanticComparer.RequiresChargedWalk(before, value))
            return EvalResult<bool>.Ok(Result.SharedValueComparer.Equals(before, value));
        session ??= Result.CreateOperationComparer(ctx.Budget, ctx.Observations?.StructuralTraversal);
        return session.TryEquals(before, value);
    }

    /// <summary>
    /// NEED-04's COUNTED agreement of one contribution with its group's data anchor: the emitted
    /// counts first, then the charged VALUE comparison (<see cref="RepeatedValueEquals"/>, whose
    /// refusal is returned as the terminal error it is — never as disagreement). Lean: the
    /// <c>CountedResult</c> comparison of <c>NeedBinder.checkAnchor</c> / <c>bindName</c>.
    /// </summary>
    private static EvalResult<bool> RepeatedCountedValueAgrees(
        ref Result.ValueSemanticComparer? session, CountedResult anchor, CountedResult own, EvalCtx ctx)
        => anchor.EmittedCount != own.EmittedCount
            ? EvalResult<bool>.Ok(false)
            : RepeatedValueEquals(ref session, anchor.Value, own.Value, ctx);

    /// <summary>
    /// NEED-04 (group-aware, ALIAS-UNIFY-1, October 2026): the binder-local agreement state of ONE
    /// repeated name during one binding of a head (<see cref="BindAcceptedNeedPatterns"/>) — never a
    /// parameter, a value or a cell. <see cref="Identity"/> is the structural identity of the
    /// group's FIRST callable-bearing contribution; <see cref="Anchor"/> the counted VALUE of its
    /// FIRST value-only contribution, once one occurred (<see cref="HasAnchor"/>); and
    /// <see cref="Pending"/> the earlier callable-bearing contributions whose own counted VALUE no
    /// anchor has checked yet, in occurrence order (always empty once the group is anchored).
    /// Lean: <c>RepeatedGroup</c>.
    /// </summary>
    private sealed class RepeatedGroup
    {
        internal Algorithm? Identity;
        internal CountedResult Anchor;
        internal bool HasAnchor;
        internal List<NeedCell>? Pending;
    }

    /// <summary>
    /// NEED-04's callable-identity agreement between two contributions of one repeated name that
    /// both carry CALLABLE identity. They must be the same builtin, or the same declaration in the
    /// same declaring scope with compatible captured activations. Comparing identities evaluates
    /// neither algorithm and consults no value cache. Lean: <c>sameRepeatedCallableIdentity</c>.
    /// </summary>
    private static bool SameRepeatedCallableIdentity(Algorithm left, Algorithm right)
    {
        if (ReferenceEquals(left, right))
            return true;
        if (left is Algorithm.Builtin leftBuiltin)
            return right is Algorithm.Builtin rightBuiltin && leftBuiltin.Id == rightBuiltin.Id;
        return ReferenceEquals(left.Declaration, right.Declaration)
            && IsSameDeclaringScope(left.Parent, right.Parent)
            && CompatibleActivations(left.Parent, right.Parent)
            && CompatibleActivations(right.Parent, left.Parent);
    }

    /// <summary>
    /// One target of an assignment deconstruction, read from the binding of its right-hand side
    /// (<see cref="BindNeedDeconstruction"/>): the helper's one output row reads one of its own
    /// bindings, so the target is that bound cell's value — exactly what the helper's ordinary body
    /// computes. The bind is SHARED through the run's deconstruction binding cache only when
    /// <see cref="SharedDeconstructionBind"/> admits it; otherwise this helper binds on its own.
    /// <c>null</c> when the helper no longer has its parser signature and body (<see cref="DeconstructionProjectionName"/>),
    /// which only a host-modified helper can produce; the caller then evaluates the helper call as
    /// the ordinary call it is.
    /// </summary>
    private static EvalResult<Result>? TryProjectSharedDeconstructionTarget(
        Algorithm.User helper,
        AssignmentDeconstructionTarget target,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (DeconstructionProjectionName(helper, target) is not { } name)
            return null;
        var boundR = SharedDeconstructionBind(helper, target, args, ctx, valEnv) is { } shared
            ? ctx.DeconstructionBindingCache.GetOrBind(shared,
                () => BindNeedDeconstruction(helper, args, ctx, valEnv, asynchronous: false).GetAwaiter().GetResult())
            : BindNeedDeconstruction(helper, args, ctx, valEnv, asynchronous: false).GetAwaiter().GetResult();
        if (boundR.IsError) return boundR.Error;
        return ProjectCountedValue(boundR.Value[name].Demand());
    }

    /// <summary>
    /// The binding a deconstruction target helper's ordinary body reads: its ONE output row is a
    /// parameter read of the parser-origin signature, at the recorded target index. Verify the
    /// signature by reference against the group's origin descriptor, plus the actual output and
    /// empty body scope, in O(1). A copied signature or body runs through the ordinary call: the
    /// specialized bind's mandatory source demand and skipped body entry are justified only for
    /// the original unpacking helper, not an arbitrary callable that returns one of its parameters.
    /// </summary>
    private static string? DeconstructionProjectionName(Algorithm.User helper, AssignmentDeconstructionTarget target)
    {
        if (target.Group is not AssignmentDeconstructionGroup group
            || !ReferenceEquals(helper.ParameterPatterns, group.Patterns)
            || helper.Opens.Count != 0 || helper.Properties.Count != 0
            || helper.Output.Count != 1 || helper.Output[0] is not Expr.Param(var name))
            return null;
        if (helper.ParameterPatterns is [UnpackingParameterPattern { Items: var items }]
            && (uint)target.Index < (uint)items.Count
            && items[target.Index] is CaptureParameterPattern capture
            && capture.Name == name)
            return name;
        return null;
    }

    /// <summary>
    /// THE MEMO ELIGIBILITY RULE of the deconstruction shared bind (DECON-CACHE-2, October 2026): the
    /// execution under which this helper's bind may be shared and stored, or <c>null</c> when the helper
    /// must bind on its own (its ordinary, uncached bind). A bind is a pure function of the ACTUAL
    /// pattern list and the source VALUE its one argument supplies, so the helper qualifies only when
    /// <list type="number">
    ///   <item>its argument is ONE written name (<see cref="Expr.Resolve"/>) — the parser's
    ///   <c>$deconstruct$N</c>, or any name a host wrote there;</item>
    ///   <item>that name resolves STRUCTURALLY from the caller — the very lookup, from the very context,
    ///   the bind's own read performs (<see cref="LookupLexicalStructural"/> and
    ///   <see cref="NormalizeValueBinding"/>, the halves of <see cref="LookupLexicalForValue"/>), so a
    ///   target-local shadow, a host parent or an ownerless scope selects what the read will select; a
    ///   name only an <c>open</c> could provide is left to the ordinary bind, so nothing here resolves
    ///   an open; and</item>
    ///   <item>the read of that entry's cache key (<see cref="ZeroArgPropertyReadExecution"/>, the key
    ///   the read itself requests) obtains the source's PUBLISHED value
    ///   (<see cref="IZeroArgPropertyResultCache.ReadObtainsPublishedValue"/>): a published entry, or
    ///   an owning first read whose success is the entry. A re-entrant read of a source whose owning
    ///   evaluation is still running (Q-37) — say, the source read directly by the host — returns an
    ///   intermediate value that is never published, so its bind is never stored.</item>
    /// </list>
    /// The execution then keys the memo by the group, the actual pattern list and the source's complete
    /// cache key (<see cref="DeconstructionBindingExecution"/>) — never by the reader: every consumer of
    /// one published source entry through one pattern list shares the bind (OD-1). Non-evaluating and
    /// charge-free: the source is read only by the bind, exactly as before. Shared by the synchronous and
    /// async projections.
    /// </summary>
    private static DeconstructionBindingExecution? SharedDeconstructionBind(
        Algorithm.User helper,
        AssignmentDeconstructionTarget target,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (args.Count != 1 || args[0] is not Expr.Resolve(var sourceName) || ctx.CallStack.Count == 0)
            return null;
        if (LookupLexicalStructural(ctx.CallStack[0], sourceName, ctx) is not { } structural)
            return null;
        var sourceR = NormalizeValueBinding(EvalResult<ResolvedLexicalProperty>.Ok(structural), ctx);
        if (sourceR.IsError)
            return null;
        var source = sourceR.Value;
        var sourceKey = ZeroArgPropertyCacheKey.FromExecution(ZeroArgPropertyReadExecution(
            source.Owner, source.Binding, ZeroArgPropertyAccessKind.CountedLexical, source.ResolvedAlgorithm, ctx, valEnv));
        if (!ctx.ZeroArgPropertyResultCache.ReadObtainsPublishedValue(sourceKey))
            return null;
        return new DeconstructionBindingExecution(target.Group, helper.ParameterPatterns, sourceKey);
    }

    /// <summary>
    /// Builtin collection-item view of the bound collection argument: opens
    /// exactly one outer sequence or exact-list boundary to its immediate
    /// items; any other value supplies itself as one item (a scalar is a
    /// one-element collection). Never recursive — nested sequence values and
    /// nested list values stay intact as single items.
    /// Applied strictly AFTER ordinary fixed parameter binding, to the already
    /// bound <c>collection</c> parameter only — argument boundaries are never
    /// altered before binding. Shared by generic collection-builtin binding
    /// and by the sequence-pipeline optimizer's receiver mirror so both open
    /// collections identically.
    /// Lean: <c>builtinCollectionItems</c>.
    /// </summary>
    private static IReadOnlyList<Result> BuiltinCollectionItems(Result value)
        => value is Result.ListValue(var listItems) ? listItems : value.ToItems();

    /// <summary>
    /// RESOURCE LIMITS ARE TERMINAL FOR THE RUN (Q-02 / PV-06, September 2026): whether a
    /// failure an evaluation site actually encountered is ORDINARY (<c>true</c>) or a
    /// resource limit (<see cref="EvalError.IsResourceLimit"/>, <c>false</c>). Since Model C
    /// (NEED-01..03, 2026-10-02) no site defers a demanded failure: supply formation evaluates
    /// no ordinary argument (<see cref="FormNeedSupply"/>), a supplied computation runs on its
    /// first VALUE demand (<see cref="NeedCell"/>) and a demanded failure propagates at once,
    /// cardinality is checked before any such demand, and a reached resource limit is
    /// terminal for the run (the cell keeps that completion and the run budget retains it, so
    /// nothing restarts it or runs after it — no later argument, callee body, consumer, random
    /// draw, or host operation). The one remaining caller is
    /// <c>SequenceBuiltinValueDemandError</c>, the report precedence of a builtin value slot's
    /// demand failure: a limit outranks the zero-argument classification of the slot's
    /// callable channel. (Until Model C this predicate decided which failures user-call
    /// argument assembly and the builtin argument adapter
    /// (<see cref="BuildCallableCallItems"/>) could retain beside a binding or behind an arity
    /// verdict — ordinary ones — and which ended the run at once; before the Q-02 rule a limit
    /// reached inside an argument the callee never read was retained and dropped, so the run
    /// SUCCEEDED after partial evaluation.) A resource limit may stop a run; it never redefines
    /// the value of a run that succeeds. Laziness is untouched: an argument the language does
    /// not demand — an unused argument, an unselected <c>if</c> branch, an invoking callback
    /// slot — reaches no limit. No Lean counterpart: Lean models no resource limits.
    /// </summary>
    internal static bool IsDeferrableEvaluationFailure(EvalError failure) => !failure.IsResourceLimit;
}
