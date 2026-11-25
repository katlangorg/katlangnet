namespace KatLang.Rendering;

internal static partial class ValueTextRenderer
{
    /// <summary>
    /// A width-capped measurement of one value's text whose walk can be continued later for a
    /// structure it entered. It writes the same text as
    /// <see cref="AppendValue(Result, DisplayOptions, IStringTextPolicy, IDisplaySink, ref Stack{SuspendedStructure}?)"/>
    /// with the same punctuation and leaf appends, refuses the first append that crosses the cap,
    /// and keeps the text it accepted.
    ///
    /// <para>A refused walk is kept: the structures it entered, each with its start offset, and the
    /// item step it was refused at (step boundaries only, so a quoted string refused part-way is
    /// measured again whole). The text of a structure <c>c</c> that the walk entered and had not
    /// finished starts with the kept text from <c>c</c>'s start to the refused step. A fresh walk of
    /// <c>c</c> under budget <c>b</c> can therefore skip that prefix. If an append crossed the cap,
    /// the end offset it needed also proves a refusal for every budget that still falls short.
    /// <see cref="MeasureEnteredChild"/> retries the refused step only once the budget reaches
    /// that offset (or the start of a step refused by the string classifier). Each answer equals a fresh walk under
    /// <c>b</c>, and so does the kept text of a value that fits.</para>
    ///
    /// <para>Such a continuation skips the string classifications a fresh walk would repeat over
    /// the skipped text. That is the same computation only while a repeat would charge nothing:
    /// strings shorter than the long-string threshold and cached long strings are answered free,
    /// but a long string the full classification cache could not keep is charged on every visit.
    /// The caller therefore continues only while the string policy has made no such uncached
    /// classification since the walk began (<see cref="Mark"/>), so classification charges,
    /// budget exhaustion and every layout decision are exactly those of fresh walks.</para>
    /// </summary>
    internal sealed class ResumableMeasurement : ICapacityDisplaySink
    {
        private const int InitialTextCapacity = 32;

        /// <summary>
        /// One structure the walk entered: its items, closing delimiter, absolute start offset, and
        /// its next item step (after the child the walk entered, or the step it was refused at).
        /// </summary>
        private struct Level
        {
            public IReadOnlyList<Result> Items;
            public string Close;
            public int Next;
            public long Start;
        }

        // The entered structures of the kept walk are _levels[_bottom.._pathEnd): the outermost
        // is the measured value, and the innermost holds the refused step.
        private Level[] _levels = [];
        private int _bottom;
        private int _pathEnd;

        // Offsets are absolute positions in the measured text; _text[0] is the text at _origin.
        // The text before the measured value's start is no longer needed; Room drops it once it is
        // as long as the live text.
        private char[] _text = [];
        private long _origin;
        private long _position;
        private long _remaining;
        private long _valueStart;
        private long _stepStart;
        private long _retryEnd;

        // Accepted units no longer included in _position after a fresh walk or a step rewind.
        private long _discardedCodeUnits;
        private Result? _value;

        /// <summary>True when the last walk was refused and kept; the walk is inside the measured value.</summary>
        public bool IsSuspended { get; private set; }

        /// <summary>The string policy's uncached-classification count when the kept walk began.</summary>
        public long Mark { get; private set; }

        /// <summary>Code units accepted by this sink over the rendering call (work observation).</summary>
        public long MeasuredCodeUnits => _discardedCodeUnits + _position;

        public long RemainingCapacity => Math.Max(_remaining, 0);

        /// <summary>The complete text of the last measured value that fit.</summary>
        public ReadOnlySpan<char> Text => _text.AsSpan((int)(_valueStart - _origin), (int)(_position - _valueStart));

        /// <summary>Items of the measured value the kept walk completed: indices below this one.</summary>
        public int CompletedItems
            => !IsSuspended ? 0
                : _pathEnd - _bottom > 1 ? _levels[_bottom].Next - 1
                : _levels[_bottom].Next;

        /// <summary>The index of the item structure the kept walk entered and had not finished, or -1.</summary>
        public int EnteredChildIndex => IsSuspended && _pathEnd - _bottom > 1 ? _levels[_bottom].Next - 1 : -1;

        /// <summary>The item structure the kept walk entered and had not finished, if any.</summary>
        public Result? EnteredChild
            => IsSuspended && _pathEnd - _bottom > 1 ? _levels[_bottom].Items[_levels[_bottom].Next - 1] : null;

        /// <summary>Whether the kept walk is a refused measurement of <paramref name="value"/>.</summary>
        public bool IsSuspendedIn(Result value) => IsSuspended && ReferenceEquals(_value, value);

        /// <summary>Forgets the kept walk.</summary>
        public void Reset()
        {
            IsSuspended = false;
            _value = null;
        }

        /// <summary>
        /// A fresh measurement of <paramref name="value"/> under <paramref name="budget"/> code units.
        /// <paramref name="mark"/> is the string policy's current uncached-classification count.
        /// </summary>
        public bool Measure(
            Result value,
            long budget,
            long mark,
            DisplayOptions displayOptions,
            IStringTextPolicy stringPolicy)
        {
            Reset();
            Mark = mark;
            _discardedCodeUnits += _position;
            _bottom = 0;
            _origin = 0;
            _position = 0;
            _valueStart = 0;
            _remaining = budget;

            IReadOnlyList<Result> items;
            string close;
            switch (value)
            {
                case Result.SequenceValue sequence:
                    if (!Append(SequenceOpen)) return false;
                    items = sequence.Items;
                    close = SequenceClose;
                    break;
                case Result.ListValue list:
                    if (!Append(ListOpen)) return false;
                    items = list.Items;
                    close = ListClose;
                    break;
                default:
                    // A leaf has no structure to keep.
                    return AppendValue(value, displayOptions, stringPolicy, this);
            }

            _value = value;
            return Walk(items, close, 0, 0, 0, displayOptions, stringPolicy);
        }

        /// <summary>
        /// Makes <see cref="EnteredChild"/> the measured value of the kept walk. The caller checks
        /// that there is one.
        /// </summary>
        public void DescendIntoEnteredChild()
        {
            ref var outer = ref _levels[_bottom];
            _value = outer.Items[outer.Next - 1];
            _bottom++;
            _valueStart = _levels[_bottom].Start;

            // Amortized: the live levels are moved down only once at least as many dropped ones lie below.
            var live = _pathEnd - _bottom;
            if (_bottom >= live)
            {
                Array.Copy(_levels, _bottom, _levels, 0, live);
                _pathEnd = live;
                _bottom = 0;
            }
        }

        /// <summary>
        /// Measures <see cref="EnteredChild"/> under <paramref name="budget"/> from the kept walk, with the
        /// answer and kept text of a fresh measurement. The caller checks that there is an entered child
        /// and that continuing the walk is exact (<see cref="Mark"/>).
        /// </summary>
        public bool MeasureEnteredChild(long budget, DisplayOptions displayOptions, IStringTextPolicy stringPolicy)
        {
            DescendIntoEnteredChild();

            // Reaching the step is insufficient when its append still cannot fit. In particular,
            // do not format a long number again for every one-column increase in available width.
            if (_retryEnd - _valueStart > budget) return false;

            // Otherwise a fresh walk accepts it all and reaches the refused step with the rest of the
            // budget. Text the refused step accepted before its refusal is written again.
            _discardedCodeUnits += _position - _stepStart;
            _position = _stepStart;
            _remaining = budget - (_stepStart - _valueStart);
            IsSuspended = false;
            var depth = _pathEnd - 1;
            ref var level = ref _levels[depth];
            return Walk(level.Items, level.Close, level.Next, level.Start, depth, displayOptions, stringPolicy);
        }

        /// <summary>
        /// The walk loop of <see cref="AppendValue(Result, DisplayOptions, IStringTextPolicy, IDisplaySink, ref Stack{SuspendedStructure}?)"/>
        /// with entered structures kept in <see cref="_levels"/> and a refusal kept at its step. It returns
        /// true when the measured value (the structure at <see cref="_bottom"/>) is closed.
        /// </summary>
        private bool Walk(
            IReadOnlyList<Result> items,
            string close,
            int next,
            long start,
            int depth,
            DisplayOptions displayOptions,
            IStringTextPolicy stringPolicy)
        {
            while (true)
            {
                var stepStart = _position;
                if (next >= items.Count)
                {
                    if (!Append(close)) return Suspend(items, close, next, start, depth, stepStart);
                    if (depth == _bottom) return true;

                    depth--;
                    ref var outer = ref _levels[depth];
                    (items, close, next, start) = (outer.Items, outer.Close, outer.Next, outer.Start);
                    continue;
                }

                if (next > 0 && !Append(ItemSeparator)) return Suspend(items, close, next, start, depth, stepStart);

                switch (items[next])
                {
                    case Result.Atom atom:
                        if (!AppendAtom(atom.Value, displayOptions, this)) return Suspend(items, close, next, start, depth, stepStart);
                        next++;
                        break;
                    case Result.Str str:
                        if (!stringPolicy.Append(str.Value, this)) return Suspend(items, close, next, start, depth, stepStart);
                        next++;
                        break;
                    case Result.Bool flag:
                        if (!Append(FormatBool(flag.Value))) return Suspend(items, close, next, start, depth, stepStart);
                        next++;
                        break;
                    case Result.SequenceValue sequence:
                        if (!Append(SequenceOpen)) return Suspend(items, close, next, start, depth, stepStart);
                        Keep(depth++, items, close, next + 1, start);
                        (items, close, next, start) = (sequence.Items, SequenceClose, 0, _position - 1);
                        break;
                    case Result.ListValue list:
                        if (!Append(ListOpen)) return Suspend(items, close, next, start, depth, stepStart);
                        Keep(depth++, items, close, next + 1, start);
                        (items, close, next, start) = (list.Items, ListClose, 0, _position - 1);
                        break;
                    case Result.CallReference reference:
                        if (!AppendCallReference(reference, stringPolicy, this)) return Suspend(items, close, next, start, depth, stepStart);
                        next++;
                        break;
                    default:
                        throw new InvalidOperationException("Unknown Result variant.");
                }
            }
        }

        private bool Suspend(IReadOnlyList<Result> items, string close, int next, long start, int depth, long stepStart)
        {
            Keep(depth, items, close, next, start);
            _pathEnd = depth + 1;
            _stepStart = stepStart;
            // A classifier may refuse before calling Append. In that case only the prefix up to
            // this step is known, and a fresh visit must make its own classification request.
            if (_remaining >= 0) _retryEnd = stepStart;
            IsSuspended = true;
            return false;
        }

        private void Keep(int depth, IReadOnlyList<Result> items, string close, int next, long start)
        {
            if (depth == _levels.Length)
                Array.Resize(ref _levels, Math.Max(4, 2 * _levels.Length));

            ref var level = ref _levels[depth];
            level.Items = items;
            level.Close = close;
            level.Next = next;
            level.Start = start;
        }

        public bool Append(string text) => Append(text.AsSpan());

        public bool Append(ReadOnlySpan<char> text)
        {
            _remaining -= text.Length;
            if (_remaining < 0) return RefuseAppend(text.Length);
            text.CopyTo(Room(text.Length));
            return true;
        }

        public bool Append(char c, int count)
        {
            _remaining -= count;
            if (_remaining < 0) return RefuseAppend(count);
            Room(count).Fill(c);
            return true;
        }

        private bool RefuseAppend(int count)
        {
            _retryEnd = _position + count;
            return false;
        }

        /// <summary>
        /// The next <paramref name="count"/> code units of kept text (an accepted append). Text before
        /// the measured value is dead once a walk is continued into an entered structure. The buffer
        /// drops it when it is at least as long as the live text, and otherwise grows by doubling.
        /// A drop copies no more live text than the dead text it discards, and all text was appended
        /// once, so copying stays proportional to the appended text and the buffer within a small
        /// multiple of the live text. A fresh walk grows only up to the end of its budget.
        /// </summary>
        private Span<char> Room(int count)
        {
            var used = (int)(_position - _origin);
            if (used + count > _text.Length)
            {
                var dead = (int)(_valueStart - _origin);
                if (dead > 0 && dead >= used - dead)
                {
                    _text.AsSpan(dead, used - dead).CopyTo(_text);
                    _origin = _valueStart;
                    used -= dead;
                    dead = 0;
                }

                if (used + count > _text.Length)
                {
                    var doubled = Math.Max(InitialTextCapacity, 2L * _text.Length);
                    var length = dead > 0 ? doubled : Math.Min(doubled, used + count + _remaining);
                    Array.Resize(ref _text, (int)Math.Max(used + count, length));
                }
            }

            _position += count;
            return _text.AsSpan(used, count);
        }
    }
}
