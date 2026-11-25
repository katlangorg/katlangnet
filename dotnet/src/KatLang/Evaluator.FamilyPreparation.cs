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
    /// the verdict is a duplicate (no call of such a family reaches its heads). The literal clause runs
    /// (<see cref="LiteralClauseRun"/>) are indexed from those same heads, by first clause.
    /// </summary>
    internal sealed class NeedFamilyPreparation(
        IReadOnlyList<CondBranch> source,
        CondBranch[] branches,
        IReadOnlyList<NeedPattern>[]? heads,
        LiteralClauseRun?[]? literalRuns = null)
    {
        /// <summary>The branch list this entry was prepared from (its memo key).</summary>
        internal IReadOnlyList<CondBranch> Source { get; } = source;

        /// <summary>The branch references, in written order, read once at preparation.</summary>
        internal CondBranch[] Branches { get; } = branches;

        /// <summary>The translated heads, in written order; null for a duplicate-head family.</summary>
        internal IReadOnlyList<NeedPattern>[]? Heads { get; } = heads;

        internal bool HasDuplicateBranchPatterns => Heads is null;

        /// <summary>The indexed literal clause runs by first clause; null when the family has none.</summary>
        internal LiteralClauseRun?[]? LiteralRuns { get; } = literalRuns;

        // These leaf calls return before a clause binder can demand a recursive argument.
        // Keep array-access temporaries out of that driver's frame (FRAME-SIZE DISCIPLINE).
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        internal int BranchCount() => Branches.Length;

        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        internal IReadOnlyList<NeedPattern> HeadAt(int index) => Heads![index];

        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        internal CondBranch BranchAt(int index) => Branches[index];

        /// <summary>The literal clause run that starts at <paramref name="index"/> and can replay this supply, or null.</summary>
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        internal LiteralClauseRun? LiteralRunAt(int index, IReadOnlyList<NeedCell> supply)
        {
            var run = LiteralRuns?[index];
            if (run is null || run.Arity == 1) return run;
            var first = supply[0];
            for (var i = 1; i < run.Arity; i++)
                if (!first.CoversDemandChecksOf(supply[i])) return null;
            return run;
        }
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
    /// completed, so a cancelled preparation leaves nothing behind. Whether its preparations index
    /// literal clause runs is decided once, when the run creates the memo (only the test seam
    /// <see cref="OrderedClauseDispatchTestSeam"/> withholds the index).
    /// </summary>
    internal sealed class NeedFamilyPreparationCache
    {
        private readonly bool _indexesLiteralRuns = !OrderedClauseDispatchTestSeam.IsActive;

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
                var prepared = PrepareNeedFamily(branches, budget, observations, _indexesLiteralRuns);
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
    // preflight), then — only for a duplicate-free family — every head's translation and the index
    // of its literal clause runs, built from those heads.
    private static NeedFamilyPreparation PrepareNeedFamily(
        IReadOnlyList<CondBranch> source, EvaluationBudget budget, EvaluationObservations? observations, bool indexLiteralRuns)
    {
        var branches = new CondBranch[source.Count];
        for (var i = 0; i < branches.Length; i++) branches[i] = source[i];
        var duplicate = Algorithm.Conditional.HasDuplicatePatterns(
            branches, observations?.FamilyDuplicateIndex, budget.CancellationToken);
        IReadOnlyList<NeedPattern>[]? heads = null;
        LiteralClauseRun?[]? literalRuns = null;
        if (!duplicate)
        {
            heads = new IReadOnlyList<NeedPattern>[branches.Length];
            for (var i = 0; i < heads.Length; i++) heads[i] = NeedClauseHead(branches[i].Pattern);
            if (indexLiteralRuns) literalRuns = PrepareLiteralClauseRuns(heads, budget.CancellationToken);
        }
        observations?.RecordClauseFamilyPreparation();
        if (literalRuns is not null) observations?.RecordLiteralClauseRuns(literalRuns.Count(static run => run is not null));
        return new NeedFamilyPreparation(source, branches, heads, literalRuns);
    }

    // Kept out of the recursive family drivers' frames (FRAME-SIZE DISCIPLINE): the memo lookup,
    // and any first preparation, run in this separate frame.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static NeedFamilyPreparation NeedFamilyPreparationOf(Algorithm callee, in EvalCtx ctx)
        => ctx.Budget.FamilyPreparations.Get(callee.Branches, ctx.Budget, ctx.Observations);
}
