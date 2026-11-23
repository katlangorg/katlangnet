using System.Collections;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang;

public static partial class Evaluator
{
    /// <summary>
    /// How the binder binds a WIDE FLAT translated level (<see cref="WideNeedLevel"/>), decided once from its
    /// patterns (implementation-only, 2026-11-23, follow-up of the wide parameter frame audit).
    /// </summary>
    internal enum WideLevelShape : byte
    {
        /// <summary>
        /// Every other level: a META capture, a repeated or null name, more than one collector, or a literal beside a
        /// collector. The general binder binds it, exactly as before.
        /// </summary>
        General,

        /// <summary>
        /// Pairwise distinct, non-null names, at most one of them collecting, and no META capture and no literal:
        /// <see cref="WideDistinctNameBindings"/>.
        /// </summary>
        DistinctNames,

        /// <summary>
        /// At least one literal, and every other pattern a plain name (not collecting, not META), the names
        /// pairwise distinct: a clause head that <see cref="BindFlatLiteralHead"/> binds.
        /// </summary>
        DistinctNamesWithLiterals,
    }

    /// <summary>
    /// A WIDE FLAT translated level: more than <see cref="FlatUniqueNameBindingWidth"/> patterns, none of them
    /// structural (<see cref="TranslateNeedPatterns{T}"/>), together with its binding shape
    /// (<see cref="WideLevelShape"/>). The patterns are the translation's own records, in written order, and never
    /// change; the shape is a pure function of them, decided on its first read (one ordinal set of the names) and
    /// kept, so every binding of a level the run prepared once — an ordinary call's stored head
    /// (<see cref="NeedHeadPreparationCache"/>), a loop step (<see cref="PrepareGenericLoopStep"/>), a clause head
    /// (<see cref="NeedFamilyPreparation"/>) — reads it without rescanning the names.
    /// <para>Before (2026-11-22 audit of the wide parameter frames): every binding of such a level took the general
    /// binder, whose multiplicity count, visit table, work stacks and binding dictionary cost about 380 KB at 1,024
    /// names, beside the head's translation (about 64 B per pattern) on every ordinary call. A narrower level is
    /// still a plain array, bound by the pairwise-checked direct paths or the general binder.</para>
    /// </summary>
    internal sealed class WideNeedLevel : IReadOnlyList<NeedPattern>, ICollection<NeedPattern>
    {
        private readonly NeedPattern[] _patterns;

        // 0 until the shape is decided, then 1 + the shape. The collector's index is written before it is published.
        private int _shape;
        private int _collector = -1;

        internal WideNeedLevel(NeedPattern[] patterns) => _patterns = patterns;

        // Each translated capture already carries the immutable pattern it came from. These
        // references are the snapshot of the caller's list, including its count and order.
        internal bool MatchesStored(IReadOnlyList<ParameterPattern> stored)
        {
            if (stored.Count != _patterns.Length)
                return false;
            for (var i = 0; i < _patterns.Length; i++)
            {
                if (!ReferenceEquals(stored[i], _patterns[i].Original))
                    return false;
            }
            return true;
        }

        public int Count => _patterns.Length;

        public NeedPattern this[int index] => _patterns[index];

        public IEnumerator<NeedPattern> GetEnumerator() => ((IEnumerable<NeedPattern>)_patterns).GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => _patterns.GetEnumerator();

        // A read-only collection, as the array it wraps is to its consumers: a copy of the level (the general
        // binder's work stack, a LINQ materialization) is sized from Count and filled by CopyTo, exactly as for
        // the array, instead of growing by enumeration.
        public bool IsReadOnly => true;

        public bool Contains(NeedPattern item) => Array.IndexOf(_patterns, item) >= 0;

        public void CopyTo(NeedPattern[] array, int arrayIndex) => _patterns.CopyTo(array, arrayIndex);

        void ICollection<NeedPattern>.Add(NeedPattern item) => throw new NotSupportedException();

        void ICollection<NeedPattern>.Clear() => throw new NotSupportedException();

        bool ICollection<NeedPattern>.Remove(NeedPattern item) => throw new NotSupportedException();

        /// <summary>The level's binding shape, decided on the first read. A racing first read decides the same shape.</summary>
        internal WideLevelShape Shape
        {
            get
            {
                var shape = Volatile.Read(ref _shape);
                if (shape == 0)
                {
                    var decided = DecideShape(_patterns, out var collector);
                    _collector = collector;
                    shape = 1 + (int)decided;
                    Volatile.Write(ref _shape, shape);
                }
                return (WideLevelShape)(shape - 1);
            }
        }

        /// <summary>The index of the level's collecting capture, or -1: read only for a <see cref="WideLevelShape.DistinctNames"/> level.</summary>
        internal int Collector => Shape == WideLevelShape.DistinctNames ? _collector : -1;

        private static WideLevelShape DecideShape(NeedPattern[] patterns, out int collector)
        {
            collector = -1;
            var literals = false;
            var names = new HashSet<string>(patterns.Length, StringComparer.Ordinal);
            for (var i = 0; i < patterns.Length; i++)
            {
                var pattern = patterns[i];
                if (pattern.Meta || pattern.Children is not null)
                    return WideLevelShape.General;
                if (pattern.Literal is not null)
                {
                    if (pattern.Name is not null)
                        return WideLevelShape.General;
                    literals = true;
                    continue;
                }
                // A host-built capture can carry a null name; the general binder treats it as a non-name.
                if (pattern.Name is not { } name || !names.Add(name))
                    return WideLevelShape.General;
                if (pattern.Collecting)
                {
                    // X-02 refuses a second collector before evaluation; its general allocation is kept.
                    if (collector >= 0)
                        return WideLevelShape.General;
                    collector = i;
                }
            }

            if (!literals)
                return WideLevelShape.DistinctNames;
            // The literal head's direct path binds one cell per pattern: a collector keeps the general binder.
            return collector >= 0 ? WideLevelShape.General : WideLevelShape.DistinctNamesWithLiterals;
        }
    }

    /// <summary>
    /// The binder's direct path for a WIDE FLAT level of DISTINCT NAMES (<see cref="WideLevelShape.DistinctNames"/>),
    /// over a supply count its cardinality gate accepted: pattern <c>i</c> binds supplied cell <c>i</c>, the collector
    /// (at most one) the exact slice the fixed prefix and suffix leave (<see cref="NeedSourceRange"/>,
    /// <see cref="CollectorCell"/>), in written order, and nothing is demanded or projected.
    /// <para>EQUIVALENCE with the general path on such a level: every name counts once, so no group forms and no cell
    /// is inspected; <c>PushLevel</c> allocates the same ranges and pushes the patterns last-first, so the pops visit
    /// them in written order, each storing <c>bound[name_i] = cell_i</c> into a dictionary that is only ever added to,
    /// and the collector's lazy cell over the same slice is created there before the pops, which no observer can
    /// tell from creating it here: making a cell evaluates, charges and records nothing. The copied environment is
    /// <c>(name_i, cell_i)</c> in insertion, that is written, order — exactly this array, fresh per binding like the
    /// general path's. Reached through the narrow direct path's own statement in the binder
    /// (<see cref="IsFlatUniqueNameLevel"/>, <see cref="FlatUniqueNameBindings"/>), so the binder's frame does not grow.
    /// Pinned by <c>WideHeadPreparationTests</c>.</para>
    /// </summary>
    private static (string Name, NeedCell Cell)[] WideDistinctNameBindings(WideNeedLevel level, IReadOnlyList<NeedCell> supply, in EvalCtx ctx)
    {
        var count = level.Count;
        var collector = level.Collector;
        var env = new (string Name, NeedCell Cell)[count];
        for (var i = 0; i < count; i++)
        {
            var (start, length) = NeedSourceRange(count, collector, supply.Count, i);
            NeedCell cell;
            if (i == collector)
            {
                var slice = new NeedCell[length];
                for (var j = 0; j < length; j++) slice[j] = supply[start + j];
                cell = CollectorCell(slice, ctx);
            }
            else
            {
                cell = supply[start];
            }
            env[i] = (level[i].Name!, cell);
        }
        return env;
    }

    /// <summary>
    /// The translated head of an ORDINARY CALL whose stored head the flat direct path did not bind
    /// (<see cref="BindFlatCaptureHead"/>): a head of more than <see cref="FlatUniqueNameBindingWidth"/> patterns is
    /// served by the run's validated preparation (<see cref="NeedHeadPreparationCache"/>), every other head is
    /// translated as before. Out of line, and given the run's budget rather than the context, which costs the
    /// synchronous driver's frame the least (measured 2026-11-23: +16 B at Tier 0 and +32 B fully optimized, against
    /// +48 B and 0 B for the context passed by value).
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static IReadOnlyList<NeedPattern> NeedCallPatterns(IReadOnlyList<ParameterPattern> stored, EvaluationBudget budget)
        => stored.Count > FlatUniqueNameBindingWidth
            ? budget.HeadPreparations.Translate(stored)
            : NeedParameterPatterns(stored);

    /// <summary>
    /// The run-local memo of the WIDE STORED HEADS ordinary calls bind (implementation-only, 2026-11-23): per
    /// caller-owned <see cref="Algorithm.User.ParameterPatterns"/> list of more than
    /// <see cref="FlatUniqueNameBindingWidth"/> capture patterns, its translation — a <see cref="WideNeedLevel"/>, which
    /// also keeps the level's binding shape. Held by the run's <see cref="EvaluationBudget"/> beside the clause-family
    /// preparation (<see cref="NeedFamilyPreparationCache"/>) and keyed like it by the LIST REFERENCE, so every wired
    /// copy of a callee (<c>user with { Parent = … }</c>) shares one entry and a <c>with { ParameterPatterns = … }</c>
    /// copy gets its own; never static and never attached to an AST, so an independent run prepares afresh.
    /// <para>UNLIKE a family's branch list, a stored head is read through on every call: a host may edit its
    /// caller-owned list between two calls of one run, and the second call binds the edited head
    /// (<c>WideParameterFrameTests</c>, <c>FlatCaptureHeadBindingTests</c>). So an entry is only served after it is
    /// VALIDATED against the list as it is now: the same count and, position by position, the same pattern references
    /// it was prepared from (a capture pattern and its declaration are immutable records, so the same references are
    /// the same names and kinds). An edited list is prepared again and replaces its entry. Validation reads each
    /// position once and allocates nothing. A head holding a structural pattern, whose nested lists a reference check
    /// could not cover, is translated on every call as before.</para>
    /// <para>Only the translation is shared: it is immutable, and the binder reads it without changing it. Every
    /// binding still builds its own environment and collector cell, so cells, activations, binding contexts and their
    /// identities stay per invocation.</para>
    /// </summary>
    internal sealed class NeedHeadPreparationCache
    {
        // A host-built flat-binder family synthesizes a user head on every call. Key the translation
        // weakly so those temporary heads can be collected during the run. The partition table's
        // operations are sequential. Hold its lock only for table access, never across a host list read.
        private readonly BindingContextPartitionTable _entries = new(storeCount: 1);
        private int _preparations;

        /// <summary>How many translations this run has published, including replacements after a host edit.</summary>
        internal int Preparations => Volatile.Read(ref _preparations);

        /// <summary>How many reachable lists hold a prepared translation.</summary>
        internal int EntryCount
        {
            get
            {
                lock (_entries)
                    return _entries.LivePartitionCount(0);
            }
        }

        /// <summary>The translation of <paramref name="stored"/>'s current pattern references.</summary>
        internal IReadOnlyList<NeedPattern> Translate(IReadOnlyList<ParameterPattern> stored)
        {
            object?[]? slots;
            lock (_entries)
                slots = _entries.Find(stored);
            if (slots is not null && Volatile.Read(ref slots[0]) is WideNeedLevel cached && cached.MatchesStored(stored))
                return cached;

            var translated = NeedParameterPatterns(stored);
            if (translated is WideNeedLevel wide)
            {
                if (slots is null)
                {
                    lock (_entries)
                        slots = _entries.GetOrCreate(stored);
                }
                Volatile.Write(ref slots[0], wide);
                Interlocked.Increment(ref _preparations);
            }
            else if (slots is not null)
            {
                // A structural translation cannot be reused. Drop any prior flat translation.
                Volatile.Write(ref slots[0], null);
            }
            return translated;
        }
    }
}
