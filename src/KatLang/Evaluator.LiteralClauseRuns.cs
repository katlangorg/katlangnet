using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;

namespace KatLang;

public static partial class Evaluator
{
    /// <summary>
    /// The fewest consecutive literal-only clauses of one arity that a family's preparation indexes as one
    /// <see cref="LiteralClauseRun"/>. A two-clause run can share comparisons across its heads.
    /// </summary>
    internal const int MinimumLiteralClauseRunLength = 2;

    /// <summary>Distinct literals of one kind a <see cref="LiteralClauseBranch"/> compares one by one before hashing them.</summary>
    internal const int LiteralClauseScanWidth = 4;

    /// <summary>
    /// A LITERAL CLAUSE RUN (2026-11-22; C# implementation optimization, no Lean change; finding
    /// <c>values-builtins-numerics-literal-clause-table-quadratic</c> of the 2026-11-21 adversarial investigation,
    /// baseline <c>8947d21e</c>): a maximal run of at least <see cref="MinimumLiteralClauseRunLength"/> consecutive
    /// clauses of a duplicate-free family whose heads are LITERAL-ONLY of one arity (<see cref="LiteralOnlyArity"/>:
    /// one to <see cref="FlatUniqueNameBindingWidth"/> patterns, each a numeric, Boolean, or non-null string literal
    /// shorter than <see cref="Result.ValueSemanticComparer.StringCharsPerUnit"/> code units — the literals whose
    /// <see cref="MatchLiteralPattern"/> comparison is uncharged, infallible and O(1) for every value). The family's
    /// run-local preparation indexes it once as a trie over the head's positions: the node reached by the values
    /// <c>v0 … v(d-1)</c> holds the FIRST clause of the run, in written order, whose literals at positions below
    /// <c>d</c> equal them, and keys its children at position <c>d</c> by <see cref="MatchLiteralPattern"/>'s own
    /// equality (<see cref="Decimal128"/>.Equals — NaN is one value, the sign of zero and the quantum are ignored —,
    /// ordinal text, the Boolean value). Two clauses with equal literals share a path; the earlier one is the path's
    /// clause, as it is the earlier match.
    ///
    /// <para><b>The ordered route it replaces.</b> Every clause of the run binds through
    /// <see cref="BindFlatLiteralHead"/> in written order until the first match: it demands supplied cells 0, 1, …
    /// and stops at its first literal mismatch. A cell's first demand in the dispatch — the only operation of the run
    /// that can evaluate anything — therefore happens at the first clause whose earlier literals equal the earlier
    /// values: exactly a node's clause. Every other demand reads a completed cell, performing that cell's own
    /// cancellation and terminal checks. Ready cells have neither check. The dispatch uses the index only when
    /// cell 0 covers the checks of every position, so its probe observes any pending failure of a skipped read.
    /// Every indexed comparison is pure.</para>
    ///
    /// <para><b>The indexed route</b> (<see cref="SelectLiteralRunClause"/>) replays only some of those attempts,
    /// each with the demands its ordered attempt begins with, in the same order: the run's first clause; each node's
    /// clause the walk reaches (its first demand, cell 0, then the cell at the node's position); the clause right
    /// after each replayed attempt that mismatches, by its first demand alone (the ordered route's next observation
    /// after that attempt); and the selected clause. Every attempt it skips would demand only completed cells after
    /// an observation that found the run neither cancelled nor terminal, compare purely and not match. So the
    /// selected clause, the first error and where it nests, cancellation, every evaluating demand and the demand
    /// order, charges, effects and diagnostics are the ordered route's; a run replays at most <c>2·arity + 1</c>
    /// attempts instead of every clause before the match, and the recorded clause attempts
    /// (<see cref="ClauseAttemptObservations"/>) are the subsequence of the ordered route's attempts that it replays,
    /// with their outcomes. Every other head — names, repeated names, structural patterns, collectors, long or null
    /// strings, mixed literal-and-name heads, another arity — ends a run and keeps the ordered route, and the clauses
    /// outside a run are attempted in written order before and after it.</para>
    ///
    /// <para>The index belongs to the family's <see cref="NeedFamilyPreparation"/>, with its lifetime: one per run
    /// per branch-list reference, never static and never attached to an AST, built after the duplicate verdict
    /// from the very heads the ordered route reads, uncharged and AST-bounded like the rest of the preparation
    /// (linear storage and expected linear build time), and published only once complete. A lookup hashes no string of
    /// <see cref="Result.ValueSemanticComparer.StringCharsPerUnit"/> or more code units (no indexed literal is that
    /// long) and allocates nothing.</para>
    /// </summary>
    internal sealed class LiteralClauseRun(int start, int end, int arity, LiteralClauseBranch root)
    {
        /// <summary>The run's first clause, in the family's written order.</summary>
        internal int Start { get; } = start;

        /// <summary>One past the run's last clause.</summary>
        internal int End { get; } = end;

        /// <summary>The pattern count every head of the run has (the supply count each of them accepts).</summary>
        internal int Arity { get; } = arity;

        /// <summary>The node of the empty prefix: its clause is <see cref="Start"/>.</summary>
        internal LiteralClauseBranch Root { get; } = root;
    }

    /// <summary>
    /// A node of a <see cref="LiteralClauseRun"/>'s trie: the first clause of the run whose literals before this
    /// node's position equal the values that reach it. A node at the run's arity is a leaf (its clause is the
    /// selected one); every other node is a <see cref="LiteralClauseBranch"/>.
    /// </summary>
    internal class LiteralClauseNode(int first)
    {
        internal int First { get; } = first;
    }

    /// <summary>
    /// An inner node of a <see cref="LiteralClauseRun"/>'s trie, keying its children by the literal at its position.
    /// Built once during preparation and only read afterwards.
    /// </summary>
    internal sealed class LiteralClauseBranch(int first) : LiteralClauseNode(first)
    {
        private LiteralKeys<Decimal128>? _numbers;
        private LiteralKeys<string>? _texts;
        private LiteralClauseNode? _true;
        private LiteralClauseNode? _false;

        /// <summary>
        /// The child for a demanded VALUE: the node of the literals at this position that
        /// <see cref="MatchLiteralPattern"/> matches against it, or <c>null</c> when none does. A number matches a
        /// numeric literal Decimal128-equal to it, a Boolean the same Boolean literal, and a text shorter than
        /// <see cref="Result.ValueSemanticComparer.StringCharsPerUnit"/> the ordinally equal string literal; a
        /// longer text is never equal to an indexed (shorter) literal, and no other value matches a literal.
        /// </summary>
        [MethodImpl(MethodImplOptions.NoInlining)]
        internal LiteralClauseNode? Find(Result value) => value switch
        {
            Result.Atom(var number) => _numbers?.Find(number),
            Result.Str { Value: var text } => text.Length < Result.ValueSemanticComparer.StringCharsPerUnit ? _texts?.Find(text) : null,
            Result.Bool(var flag) => flag ? _true : _false,
            _ => null,
        };

        /// <summary>The child for an indexed LITERAL at this position, or <c>null</c> before one is added.</summary>
        internal LiteralClauseNode? FindLiteral(Pattern literal) => literal switch
        {
            Pattern.LitInt(var number) => _numbers?.Find(number),
            Pattern.LitString(var text) => _texts?.Find(text),
            Pattern.LitBool(var flag) => flag ? _true : _false,
            _ => throw new System.Diagnostics.UnreachableException("Only an indexable literal is keyed."),
        };

        /// <summary>Adds the child of an indexed literal that has none yet.</summary>
        internal void Add(Pattern literal, LiteralClauseNode child)
        {
            switch (literal)
            {
                case Pattern.LitInt(var number):
                    (_numbers ??= new(LiteralNumberEquality.Instance)).Add(number, child);
                    break;
                case Pattern.LitString(var text):
                    (_texts ??= new(StringComparer.Ordinal)).Add(text, child);
                    break;
                case Pattern.LitBool(true):
                    _true = child;
                    break;
                case Pattern.LitBool(false):
                    _false = child;
                    break;
                default:
                    throw new System.Diagnostics.UnreachableException("Only an indexable literal is keyed.");
            }
        }
    }

    /// <summary>
    /// The children of one literal kind: compared one by one while there are at most
    /// <see cref="LiteralClauseScanWidth"/>, then hashed. Keys are pairwise unequal under the comparer.
    /// </summary>
    internal sealed class LiteralKeys<TKey>(IEqualityComparer<TKey> comparer) where TKey : notnull
    {
        private readonly IEqualityComparer<TKey> _comparer = comparer;
        private TKey[] _keys = new TKey[LiteralClauseScanWidth];
        private LiteralClauseNode[] _children = new LiteralClauseNode[LiteralClauseScanWidth];
        private int _count;
        private Dictionary<TKey, LiteralClauseNode>? _table;

        internal LiteralClauseNode? Find(TKey key)
        {
            if (_table is { } table)
                return table.TryGetValue(key, out var child) ? child : null;
            for (var i = 0; i < _count; i++)
                if (_comparer.Equals(key, _keys[i]))
                    return _children[i];
            return null;
        }

        internal void Add(TKey key, LiteralClauseNode child)
        {
            if (_table is null && _count < _keys.Length)
            {
                _keys[_count] = key;
                _children[_count++] = child;
                return;
            }

            if (_table is null)
            {
                _table = new Dictionary<TKey, LiteralClauseNode>(2 * _count, _comparer);
                for (var i = 0; i < _count; i++)
                    _table.Add(_keys[i], _children[i]);
                _keys = [];
                _children = [];
            }

            _table.Add(key, child);
        }
    }

    /// <summary>
    /// <see cref="MatchLiteralPattern"/>'s numeric equality, <see cref="Decimal128"/>.Equals, with a hash consistent
    /// with it: every NaN and every zero hash alike here, and any other value through Decimal128's own hash, which
    /// the runtime keeps consistent with its Equals across quanta (pinned by <c>LiteralClauseRunTests</c>).
    /// </summary>
    internal sealed class LiteralNumberEquality : IEqualityComparer<Decimal128>
    {
        internal static readonly LiteralNumberEquality Instance = new();

        public bool Equals(Decimal128 x, Decimal128 y) => x.Equals(y);

        public int GetHashCode(Decimal128 value)
            => Decimal128.IsNaN(value) ? 1 : value.Equals(Decimal128.Zero) ? 0 : value.GetHashCode();
    }

    /// <summary>
    /// The pattern count of a LITERAL-ONLY head (see <see cref="LiteralClauseRun"/>), or 0 for every other head. Such
    /// a head is a flat literal level (<see cref="IsFlatLiteralHead"/>) for exactly the supply count it accepts.
    /// </summary>
    internal static int LiteralOnlyArity(IReadOnlyList<NeedPattern> head)
    {
        var count = head.Count;
        if (count == 0 || count > FlatUniqueNameBindingWidth)
            return 0;
        for (var i = 0; i < count; i++)
        {
            var pattern = head[i];
            if (pattern is not { Literal: { } literal, Name: null, Collecting: false, Meta: false, Children: null, List: false, Unpacking: false }
                || !IsIndexableLiteral(literal))
                return 0;
        }
        return count;
    }

    // The literals MatchLiteralPattern compares in O(1) without a charge or a failure, whatever the value.
    private static bool IsIndexableLiteral(Pattern literal) => literal switch
    {
        Pattern.LitInt or Pattern.LitBool => true,
        Pattern.LitString { Value: { } text } => text.Length < Result.ValueSemanticComparer.StringCharsPerUnit,
        _ => false,
    };

    /// <summary>
    /// The literal clause runs of a duplicate-free family's translated heads, by first clause (null where no run
    /// starts, and null altogether when the family has none). Observes <paramref name="token"/> between clauses.
    /// </summary>
    internal static LiteralClauseRun?[]? PrepareLiteralClauseRuns(IReadOnlyList<NeedPattern>[] heads, CancellationToken token)
    {
        LiteralClauseRun?[]? runs = null;
        for (var start = 0; start < heads.Length;)
        {
            var arity = ScanArity(start);
            var end = start + 1;
            if (arity != 0)
            {
                while (end < heads.Length && ScanArity(end) == arity)
                    end++;
                if (end - start >= MinimumLiteralClauseRunLength)
                    (runs ??= new LiteralClauseRun?[heads.Length])[start] = BuildLiteralClauseRun(heads, start, end, arity, token);
            }
            start = end;
        }
        token.ThrowIfCancellationRequested();
        return runs;

        int ScanArity(int index)
        {
            if ((index & 1023) == 0) token.ThrowIfCancellationRequested();
            return LiteralOnlyArity(heads[index]);
        }
    }

    private static LiteralClauseRun BuildLiteralClauseRun(
        IReadOnlyList<NeedPattern>[] heads, int start, int end, int arity, CancellationToken token)
    {
        var root = new LiteralClauseBranch(start);
        for (var clause = start; clause < end; clause++)
        {
            if (((clause - start) & 1023) == 0)
                token.ThrowIfCancellationRequested();
            var head = heads[clause];
            var node = root;
            for (var position = 0; position < arity; position++)
            {
                var literal = head[position].Literal!;
                var last = position + 1 == arity;
                // Clauses are added in written order, so a node's clause is the first one that reaches it.
                var child = node.FindLiteral(literal);
                if (child is null)
                {
                    child = last ? new LiteralClauseNode(clause) : new LiteralClauseBranch(clause);
                    node.Add(literal, child);
                }
                if (!last)
                    node = (LiteralClauseBranch)child;
            }
        }
        return new LiteralClauseRun(start, end, arity, root);
    }

    /// <summary>
    /// THE INDEXED ROUTE through one <see cref="LiteralClauseRun"/> (see there), for a supply of the run's arity: the
    /// selected clause, <c>-1</c> when no clause of the run matches (the dispatch continues after the run), or the
    /// error of the first failing demand, recorded on its attempt. Each replayed attempt is recorded like the
    /// drivers record theirs, before its first demand. One demand site serves every replayed attempt, so the frame
    /// a recursive argument's demand holds stays small; <see cref="LiteralRunWalk"/> steps through the trie.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<int> SelectLiteralRunClause(LiteralClauseRun run, IReadOnlyList<NeedCell> supply, EvaluationObservations? observations)
    {
        observations?.RecordLiteralClauseRunSelection();
        var walk = new LiteralRunWalk(run, observations?.ClauseAttempts);
        var cell = 0;
        do
        {
            var demanded = supply[cell].Demand();
            if (demanded.IsError) return walk.Failure(demanded.Error);
            cell = walk.Advance(demanded.Value.Value);
        }
        while (cell >= 0);
        return walk.Outcome(cell);
    }

    /// <summary>MIRROR OF <see cref="SelectLiteralRunClause"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<int>> SelectLiteralRunClauseAsync(LiteralClauseRun run, IReadOnlyList<NeedCell> supply, EvaluationObservations? observations)
    {
        observations?.RecordLiteralClauseRunSelection();
        var walk = new LiteralRunWalk(run, observations?.ClauseAttempts);
        var cell = 0;
        do
        {
            var demanded = await supply[cell].DemandAsync().ConfigureAwait(false);
            if (demanded.IsError) return walk.Failure(demanded.Error);
            cell = walk.Advance(demanded.Value.Value);
        }
        while (cell >= 0);
        return walk.Outcome(cell);
    }

    /// <summary>
    /// One walk of <see cref="SelectLiteralRunClause"/> through a run's trie: the replayed attempt, the node and
    /// position it has reached, and what the next demanded value is for — the attempt's value at its position, a
    /// probe's first demand, or the first demand of the next node's clause. It records the replayed attempts and
    /// their outcomes. <see cref="Advance"/> returns the cell to demand next, or a negative outcome
    /// (<see cref="Outcome"/>).
    /// </summary>
    private struct LiteralRunWalk
    {
        private const int Compare = 0;
        private const int Probe = 1;
        private const int Enter = 2;
        private const int NoMatch = -1;

        private readonly LiteralClauseRun _run;
        private readonly ClauseAttemptObservations? _attempts;
        private LiteralClauseNode _node;
        private LiteralClauseNode? _next;
        private int _clause;
        private int _position;
        private int _phase;

        // The run's first clause is the first attempt, recorded before its first demand.
        internal LiteralRunWalk(LiteralClauseRun run, ClauseAttemptObservations? attempts)
        {
            _run = run;
            _attempts = attempts;
            _node = run.Root;
            _next = null;
            _clause = run.Start;
            _position = 0;
            _phase = Compare;
            attempts?.RecordAttempt(run.Start);
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        internal int Advance(Result value)
        {
            if (_phase == Enter)
            {
                // The first demand of the next node's clause; then its next position, or it is selected.
                _phase = Compare;
                return _position == _run.Arity ? Selected() : _position;
            }

            if (_phase == Probe)
            {
                _attempts?.RecordOutcome(ClauseAttemptOutcome.NonMatch);
                return EnterNext();
            }

            var child = ((LiteralClauseBranch)_node).Find(value);
            if (child is not null && child.First == _clause)
            {
                // The replayed attempt matches this position too: it demands its next one, or it is selected.
                _node = child;
                return ++_position == _run.Arity ? Selected() : _position;
            }

            // It mismatches here, and so does every clause before the next node's clause (or the run's end): those
            // demand only completed cells. The first of them is replayed by its first demand alone.
            _attempts?.RecordOutcome(ClauseAttemptOutcome.NonMatch);
            _next = child;
            if (_clause + 1 < (child?.First ?? _run.End))
            {
                _attempts?.RecordAttempt(_clause + 1);
                _phase = Probe;
                return 0;
            }
            return EnterNext();
        }

        // Moves to the first clause whose literals equal the values so far, replaying its first demand.
        private int EnterNext()
        {
            if (_next is not { } next)
                return NoMatch;
            _node = next;
            _next = null;
            _clause = next.First;
            _position++;
            _phase = Enter;
            _attempts?.RecordAttempt(_clause);
            return 0;
        }

        private readonly int Selected()
        {
            _attempts?.RecordOutcome(ClauseAttemptOutcome.Matched);
            return -2 - _clause;
        }

        /// <summary>The selection a negative <see cref="Advance"/> result stands for.</summary>
        internal readonly EvalResult<int> Outcome(int advanced) => EvalResult<int>.Ok(advanced == NoMatch ? -1 : -2 - advanced);

        /// <summary>A failed demand: the outcome of the attempt that made it.</summary>
        internal readonly EvalResult<int> Failure(EvalError error)
        {
            _attempts?.RecordOutcome(ClauseAttemptOutcome.Error);
            return error;
        }
    }

    /// <summary>
    /// A run's <paramref name="selection"/> as the drivers' clause binding — the error, the non-match of a run
    /// without a matching clause, or the selected literal-only head's binding, which names nothing — and where the
    /// dispatch continues in <paramref name="clause"/>: at the selected clause, at the run's last clause when no
    /// clause of it matched (the loop then moves past the run), and unchanged for an error.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<NeedEnv?> LiteralRunBindings(in EvalResult<int> selection, LiteralClauseRun run, ref int clause)
    {
        if (selection.IsError) return selection.Error;
        if (selection.Value < 0)
        {
            clause = run.End - 1;
            return EvalResult<NeedEnv?>.Ok(null);
        }
        clause = selection.Value;
        return EvalResult<NeedEnv?>.Ok(Array.Empty<(string Name, NeedCell Cell)>());
    }
}
