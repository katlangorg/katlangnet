using KatLang.Evaluation;

namespace KatLang;

public static partial class Evaluator
{
    /// <summary>
    /// The run-local decision a clause family's call needs before any clause (SEC-03 follow-up,
    /// November 2026): the duplicate-head verdict (Lean: <c>Algorithm.hasDuplicateBranchPatterns</c>,
    /// checked on every call) and the translated clause heads, taken together with the branch
    /// references whose bodies a match selects, so verdict, heads and body come from ONE view of
    /// the family's branch list. Immutable once published; <see cref="Heads"/> is null exactly when
    /// the verdict is a duplicate (no call of such a family reaches its heads).
    /// </summary>
    internal sealed class NeedFamilyPreparation(
        IReadOnlyList<CondBranch> source,
        CondBranch[] branches,
        IReadOnlyList<NeedPattern>[]? heads)
    {
        /// <summary>The branch list this entry was prepared from (its memo key).</summary>
        internal IReadOnlyList<CondBranch> Source { get; } = source;

        /// <summary>The branch references, in written order, read once at preparation.</summary>
        internal CondBranch[] Branches { get; } = branches;

        /// <summary>The translated heads, in written order; null for a duplicate-head family.</summary>
        internal IReadOnlyList<NeedPattern>[]? Heads { get; } = heads;

        internal bool HasDuplicateBranchPatterns => Heads is null;

        // These leaf calls return before a clause binder can demand a recursive argument.
        // Keep array-access temporaries out of that driver's frame (FRAME-SIZE DISCIPLINE).
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        internal int BranchCount() => Branches.Length;

        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        internal IReadOnlyList<NeedPattern> HeadAt(int index) => Heads![index];

        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        internal CondBranch BranchAt(int index) => Branches[index];
    }

    /// <summary>
    /// Run-local memo of <see cref="NeedFamilyPreparation"/>, held by the run's
    /// <see cref="EvaluationBudget"/> exactly like <see cref="PropertyBindingIndexCache"/>. It is
    /// keyed by the family's <see cref="Algorithm.Conditional.Branches"/> LIST REFERENCE: every
    /// lookup returns a fresh wired copy of the family (<c>family with { Parent = … }</c>) that
    /// shares its list, so all copies share one entry, while a <c>with { Branches = … }</c> copy
    /// gets its own. Never static and never attached to an AST, scope or prelude: an independent
    /// run creates a fresh memo, so host edits of a caller-owned list BETWEEN runs are observed
    /// (AST lists must not change DURING a run). An entry is published only after its computation
    /// completed, so a cancelled preparation leaves nothing behind.
    /// </summary>
    internal sealed class NeedFamilyPreparationCache
    {
        // The last entry served: a recursive family (and any loop over one family) hits it
        // without the lock. Entries are immutable, so a racing reader sees a complete one.
        private NeedFamilyPreparation? _last;
        private readonly Dictionary<IReadOnlyList<CondBranch>, NeedFamilyPreparation> _entries = new(ReferenceEqualityComparer.Instance);

        internal NeedFamilyPreparation Get(IReadOnlyList<CondBranch> branches, EvaluationBudget budget, EvaluationObservations? observations)
        {
            if (Volatile.Read(ref _last) is { } last && ReferenceEquals(last.Source, branches))
                return last;
            NeedFamilyPreparation? found;
            lock (_entries)
                _entries.TryGetValue(branches, out found);
            if (found is null)
            {
                // Computed outside the lock: the computation is a pure function of the list and
                // may be cancelled; the first completed entry wins, a racing one is discarded.
                var prepared = PrepareNeedFamily(branches, budget, observations);
                lock (_entries)
                {
                    if (!_entries.TryGetValue(branches, out found))
                    {
                        _entries.Add(branches, prepared);
                        found = prepared;
                    }
                }
            }
            Volatile.Write(ref _last, found);
            return found;
        }
    }

    // The ONE preparation of a family's branch list for a run: the duplicate verdict over the
    // runtime index (observing the run's token; uncharged, AST-bounded like the structural
    // preflight), then — only for a duplicate-free family — every head's translation.
    private static NeedFamilyPreparation PrepareNeedFamily(
        IReadOnlyList<CondBranch> source, EvaluationBudget budget, EvaluationObservations? observations)
    {
        var branches = new CondBranch[source.Count];
        for (var i = 0; i < branches.Length; i++) branches[i] = source[i];
        var duplicate = Algorithm.Conditional.HasDuplicatePatterns(
            branches, observations?.FamilyDuplicateIndex, budget.CancellationToken);
        IReadOnlyList<NeedPattern>[]? heads = null;
        if (!duplicate)
        {
            heads = new IReadOnlyList<NeedPattern>[branches.Length];
            for (var i = 0; i < heads.Length; i++) heads[i] = NeedClauseHead(branches[i].Pattern);
        }
        observations?.RecordClauseFamilyPreparation();
        return new NeedFamilyPreparation(source, branches, heads);
    }

    // Kept out of the recursive family drivers' frames (FRAME-SIZE DISCIPLINE): the memo lookup,
    // and any first preparation, run in this separate frame.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static NeedFamilyPreparation NeedFamilyPreparationOf(Algorithm callee, in EvalCtx ctx)
        => ctx.Budget.FamilyPreparations.Get(callee.Branches, ctx.Budget, ctx.Observations);
}
