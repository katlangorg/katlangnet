namespace KatLang;

internal static partial class ImplicitArgumentResolver
{
    /// <summary>
    /// THE SELECTION INVARIANT's rewrite-side record (B3-5★, ledger S-10): the callees one OPEN body's rewrite lifted, in
    /// the ORDER the formula-lifting role walk reaches their references — the order the selection composed the body's
    /// signature in (<see cref="SignatureSelector"/>'s lifting rule, written order, each callee identity once) — so
    /// <see cref="RequireSelectedComposition"/> compares the rewrite's own first contribution of every callee with the
    /// composition, position by position, without walking a row again.
    ///
    /// <para>The rewrite reaches references in another order than the role walk in exactly two places: an argument-bearing
    /// dot edge rewrites its arguments before its receiver (<see cref="RewriteDotCall"/>; the role walk reads the receiver
    /// first), and a hoisted deconstruction right-hand side is rewritten after every output row
    /// (<see cref="AstHelpers.RewriteDeconstructionSourceRows"/>), while <see cref="AstHelpers.WrittenRows"/> places it
    /// before the output row its index names. The log is a linked list with an insertion cursor: a receiver's lifts are
    /// inserted before its edge's argument lifts, and a right-hand side's before its row's marker successor, so the list
    /// reads in role-walk order however the rewrite recursed. Each lift, edge and row costs O(1); nothing is flattened —
    /// a signature is held by reference.</para>
    ///
    /// <para>Each memoized expression records its own segment. A REWRITE MEMO HIT appends a link to that segment, so a
    /// receiver or hoisted source can reach it before the occurrence rewritten first. Comparison visits each segment
    /// once, in role-walk order: it reads a DAG of independently recorded rewrite facts, never the AST, and never expands
    /// a shared segment per path. Thus sharing does not disable any part of the ordered invariant. Storage and comparison
    /// work are charged to the operation's ledger, proportional to rewritten nodes, edges, rows and actual lifts.</para>
    /// </summary>
    internal sealed class OpenBodyLiftLog
    {
        /// <summary>One lift, a shared segment link, or a row marker / segment head (neither identity nor segment).</summary>
        private sealed class Entry(object? identity, IReadOnlyList<ParameterPattern>? signature, string? name, Entry? segment = null)
        {
            public readonly object? Identity = identity;
            public readonly IReadOnlyList<ParameterPattern>? Signature = signature;
            public readonly string? Name = name;
            public readonly Entry? Segment = segment;
            public Entry? Next;
        }

        private Entry _head;
        private Entry _cursor;
        private readonly List<Entry> _rowMarkers = [];
        private List<(Entry Start, Entry? ArgumentsEnd)>? _edges;
        private readonly List<(Entry Head, Entry Cursor)> _parents = [];
        private Dictionary<Expr, Entry>? _valueSegments;
        private Dictionary<Expr, Entry>? _callableSegments;
        private int _sourceSlot = -1;
        private readonly StaticQueryResourceBudget? _resources;
        private readonly CancellationToken _cancellationToken;

        public OpenBodyLiftLog(StaticQueryResourceBudget? resources = null, CancellationToken cancellationToken = default)
        {
            _resources = resources;
            _cancellationToken = cancellationToken;
            Charge(4); // Log, lists and initial segment head; collection backing is charged as it grows.
            _head = _cursor = new(null, null, null);
        }

        /// <summary>Begin the facts of one expression the rewrite is about to compute, independently of its parent.</summary>
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        public void BeginNode()
        {
            Grow(_parents);
            _parents.Add((_head, _cursor));
            Charge(1);
            _head = _cursor = new(null, null, null);
        }

        /// <summary>Retain a completed segment for the rewrite memo's subsequent reaches; an empty segment needs no entry.</summary>
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        public void EndNode(Expr expression, LiftingRole role)
        {
            var segment = _head;
            (_head, _cursor) = _parents[^1];
            _parents.RemoveAt(_parents.Count - 1);
            if (segment.Next is null)
                return;
            var segments = role == LiftingRole.Value
                ? _valueSegments ??= new(ReferenceEqualityComparer.Instance)
                : _callableSegments ??= new(ReferenceEqualityComparer.Instance);
            Charge(segments.Count == 0 ? 5 : 3); // Dictionary object/entry/backing plus the segment link below.
            segments.Add(expression, segment);
            Insert(new(null, null, null, segment));
        }

        /// <summary>A value-role reference lifted <paramref name="identity"/>, forwarding <paramref name="signature"/>.</summary>
        public void Record(object identity, IReadOnlyList<ParameterPattern> signature, string name)
        {
            Charge(1);
            Insert(new(identity, signature, name));
        }

        /// <summary>The next output row begins (every row, a preserved root row included, so markers follow row indexes).</summary>
        public void BeginRow()
        {
            Charge(1);
            Grow(_rowMarkers);
            var marker = new Entry(null, null, null);
            Insert(marker);
            _rowMarkers.Add(marker);
        }

        /// <summary>Every output row is rewritten: the marker after the last one anchors the right-hand sides written last.</summary>
        public void EndRows() => BeginRow();

        /// <summary>An argument-bearing dot edge rewrites its arguments: they follow everything logged so far.</summary>
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        public void BeginEdgeArguments()
        {
            var edges = _edges ??= [];
            Grow(edges);
            edges.Add((_cursor, null));
        }

        /// <summary>The edge rewrites its receiver: the role walk reads it before the arguments, so its lifts go before theirs.</summary>
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        public void BeginEdgeReceiver()
        {
            var (start, _) = _edges![^1];
            _edges[^1] = (start, _cursor);
            _cursor = start;
        }

        /// <summary>The edge is rewritten: later lifts follow its arguments' (or, without any, its receiver's).</summary>
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        public void EndEdgeReceiver()
        {
            var (start, argumentsEnd) = _edges![^1];
            _edges.RemoveAt(_edges.Count - 1);
            if (!ReferenceEquals(argumentsEnd, start))
                _cursor = argumentsEnd!;
        }

        /// <summary>
        /// The rewrite of a hoisted deconstruction right-hand side written before output row <paramref name="rowIndex"/>
        /// begins (<see cref="Algorithm.User.AssignmentDeconstructionRowIndex"/>; past the last row, after every row): its
        /// lifts go after that row's marker and after the right-hand sides already inserted there, as
        /// <see cref="AstHelpers.WrittenRows"/> orders them.
        /// </summary>
        public void EnterSource(int rowIndex)
        {
            if (_sourceSlot >= 0)
                _rowMarkers[_sourceSlot] = _cursor;
            _sourceSlot = Math.Min(rowIndex, _rowMarkers.Count - 1);
            _cursor = _rowMarkers[_sourceSlot];
        }

        /// <summary>Every hoisted right-hand side is rewritten.</summary>
        public void EndSources()
        {
            if (_sourceSlot < 0)
                return;
            _rowMarkers[_sourceSlot] = _cursor;
            _sourceSlot = -1;
        }

        /// <summary>The region's rewrite memo served a node (<see cref="RewriteImplicitCalls"/>).</summary>
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        public void NoteMemoHit(Expr expression, LiftingRole role)
        {
            var segments = role == LiftingRole.Value ? _valueSegments : _callableSegments;
            if (segments?.TryGetValue(expression, out var segment) != true)
                return;
            Charge(1);
            Insert(new(null, null, null, segment));
        }

        /// <summary>
        /// How the logged lifts differ from <paramref name="composed"/>, the dependencies the body's selected signature was
        /// composed from, or null when they agree. The first lift of every callee, in role-walk
        /// order, is the composed dependency at the same position — the same static callee identity and the very signature
        /// object — and no lifted callee is missing or extra; a later lift of a callee already lifted adds nothing, whatever
        /// spelling forwarded it (<c>pow</c>, <c>Math.Pow</c>: one identity, two signature objects).
        /// Linear in the recorded DAG and the dependencies; never in logical paths or a signature's width.
        /// </summary>
        public string? Disagreement(IReadOnlyList<LiftedDependency> composed)
            => DisagreementWithWork(composed, out _);

        /// <summary>The same comparison with a passive work count for the DAG-complexity regression.</summary>
        internal string? DisagreementWithWork(IReadOnlyList<LiftedDependency> composed, out long comparedEntries)
        {
            comparedEntries = 0;
            HashSet<object>? lifted = null;
            HashSet<Entry>? visited = null;
            var pending = new List<Entry>();
            var count = 0;
            var entry = _head.Next;
            while (entry is not null || pending.Count > 0)
            {
                if (entry is null)
                {
                    entry = pending[^1];
                    pending.RemoveAt(pending.Count - 1);
                    continue;
                }

                comparedEntries++;
                _resources?.Work(1, _cancellationToken);
                if (entry.Segment is { } segment)
                {
                    visited ??= new(ReferenceEqualityComparer.Instance);
                    if (visited.Contains(segment))
                    {
                        entry = entry.Next;
                        continue;
                    }

                    Charge(visited.Count == 0 ? 3 : 2); // Set object/entry/backing, once per segment, never per logical path.
                    visited.Add(segment);
                    if (entry.Next is { } next)
                    {
                        Grow(pending);
                        pending.Add(next);
                    }

                    entry = segment.Next;
                    continue;
                }

                var current = entry;
                entry = entry.Next;
                if (current.Identity is not { } identity)
                    continue;
                // A later contribution of a callee already lifted: the composition holds its first one only.
                lifted ??= new(ReferenceEqualityComparer.Instance);
                if (lifted.Contains(identity))
                    continue;
                Charge(lifted.Count == 0 ? 3 : 2); // Distinct lifted-identity set object/entry/backing.
                lifted.Add(identity);
                if (count == composed.Count)
                    return $"the callee '{current.Name}', which its rows lift after every composed one";
                var expected = composed[count];
                if (!ReferenceEquals(expected.Identity, identity))
                    return $"the lifted callee '{current.Name}' at position {count + 1}, where it was composed from '{expected.Name}'";
                if (!ReferenceEquals(expected.Signature.ParameterPatterns, current.Signature))
                    return $"the lifted callee '{expected.Name}', whose first lift forwards another signature than it was composed with";
                count++;
            }

            if (count != composed.Count)
                return $"the lifted callee '{composed[count].Name}', which no row lifts";

            return null;
        }

        private void Charge(long units) => _resources?.Metadata(units, cancellationToken: _cancellationToken);

        /// <summary>Conservatively account for backing growth (up to two references per slot) before allocating it.</summary>
        private void Grow<T>(List<T> list)
        {
            if (list.Count == list.Capacity)
                Charge(1 + (Math.Max(4, list.Capacity * 2) + 3L) / 4);
        }

        private void Insert(Entry entry)
        {
            entry.Next = _cursor.Next;
            _cursor.Next = entry;
            _cursor = entry;
        }
    }
}
