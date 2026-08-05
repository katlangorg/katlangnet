using KatLang.Rendering;

namespace KatLang.Formatting;

/// <summary>
/// Shared layout engine for the <c>readable</c> and <c>concise</c> formatters.
///
/// <para>Layout is pure presentation over finished values: the engine renders
/// exactly the rows it is given, in order, with their structure kinds intact —
/// it never spreads, flattens, collects, reorders, merges, splits, or
/// reinterprets anything, and string content always passes through the shared
/// <see cref="ValueTextRenderer"/> verbatim. The two modes differ only in
/// delimiter policy: <c>readable</c> preserves every sequence parenthesis and
/// list bracket, while <c>concise</c> may hide a sequence's parentheses in the
/// specific, locally provable safe shapes documented on
/// <see cref="ConciseOutputFormatter"/>. List brackets and the empty sequence
/// <c>()</c> are never hidden by either mode.</para>
///
/// <para>Inline layout requires BOTH fitting the preferred line width AND
/// structural simplicity: a sequence with two or more structured children —
/// or, inside an already structured layout, a multi-pair alternating
/// string/value child — lays out multiline even when its flat text would fit,
/// because that nesting is exactly what the flat form erases. Purely flat
/// values keep their inline layout, so the formatters never become
/// unconditionally vertical.</para>
///
/// <para>Robustness: all whole-value traversal is ITERATIVE with one
/// heap-allocated frame per open structure level (never one entry per pending
/// sibling — see the depth note on <see cref="Result"/>), and inline-fit
/// decisions use width-CAPPED measurement (<see cref="CappedWidthSink"/>)
/// that stops as soon as the remaining line width is exceeded, so a deeply
/// shared (DAG) value costs at most O(width) measurement per emitted node
/// instead of re-walking whole subtrees. Every emitted code unit — indentation,
/// separators, quotes, and newlines included — goes through the bounded
/// writer, which preserves the all-or-nothing display-limit contract.</para>
/// </summary>
internal static class StructuredLayoutRenderer
{
    // Cache only predicates whose repeated scan is materially more expensive
    // than the dictionary entry, and cap each cache so auxiliary storage stays
    // independent of collection breadth. This prevents a shared wide DAG node
    // from being reclassified once per incoming reference without turning a
    // wide tree of distinct nodes into a breadth-sized memo table.
    private const int PredicateCacheThreshold = 32;
    private const int PredicateCacheCapacity = 64;

    internal static bool WriteRows(
        IReadOnlyList<Result> rows,
        DisplayOptions displayOptions,
        OutputFormattingOptions options,
        bool concise,
        BoundedDisplayWriter writer)
        => new LayoutSession(displayOptions, options, concise, writer).WriteAllRows(rows);

    private enum FrameKind
    {
        /// <summary>Multiline sequence with visible parentheses and comma item separators.</summary>
        ParenSequence,

        /// <summary>Multiline list with visible brackets and comma element separators.</summary>
        BracketList,

        /// <summary>Concise paren-hidden block: one item (or pair) per line, boundaries carried by lines and indentation.</summary>
        ConciseBlock,
    }

    /// <summary>One open structure level of the layout walk (indexed continuation frame).</summary>
    private sealed class Frame
    {
        public required IReadOnlyList<Result> Items;
        public int Next;
        public required int Level;
        public required FrameKind Kind;
        public bool PairRun;
        public bool CloseComma;
        public bool PrevItemWasLine;
    }

    private sealed class LayoutSession
    {
        private readonly BoundedDisplayWriter _writer;
        private readonly DisplayOptions _displayOptions;
        private readonly DelimitedStringTextPolicy _strings;
        private readonly int _width;
        private readonly int _indentSize;
        private readonly string _newLine;
        private readonly int _rootSpacing;
        private readonly bool _concise;
        private readonly CappedWidthSink _measure = new();
        private readonly Stack<Frame> _frames = new();
        private readonly Dictionary<IReadOnlyList<Result>, bool> _structuredChildLayoutCache =
            new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<IReadOnlyList<Result>, bool> _structuralPairRunCache =
            new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<IReadOnlyList<Result>, Dictionary<int, bool>> _concisePairRunCache =
            new(ReferenceEqualityComparer.Instance);
        private bool _startedOutput;

        public LayoutSession(
            DisplayOptions displayOptions,
            OutputFormattingOptions options,
            bool concise,
            BoundedDisplayWriter writer)
        {
            _writer = writer;
            _displayOptions = displayOptions;
            // The delimiter mode influences layout only through the string
            // policy's per-value token decisions — the layout engine itself
            // never branches on it.
            _strings = new DelimitedStringTextPolicy(options.StringDelimiters);
            _width = options.PreferredLineWidth;
            _indentSize = options.IndentSize;
            _newLine = options.NewLine;
            _rootSpacing = options.RootOutputSpacing;
            _concise = concise;
        }

        public bool WriteAllRows(IReadOnlyList<Result> rows)
        {
            for (var i = 0; i < rows.Count; i++)
            {
                if (i > 0)
                {
                    for (var blank = 0; blank < _rootSpacing; blank++)
                    {
                        if (!_writer.Append(_newLine)) return false;
                    }
                }

                if (!WriteRow(rows[i])) return false;
            }

            return true;
        }

        private bool WriteRow(Result row)
        {
            _frames.Clear();

            if (_concise && row is Result.SequenceValue { Items.Count: >= 2 } rootSequence)
            {
                // Concise root preference order: whole-line space join, then the
                // paren-hidden root block, then delimited rendering below. The
                // outer sequence of one root-output block is the flagship safe
                // paren-removal shape. With zero root spacing, a paren-hidden
                // block whose every item is an ordinary line would render
                // exactly like several independent root rows, so the block is
                // allowed there only when a nested pair block will visibly
                // indent under a preceding line and bind the block together.
                if (CanSpaceJoinTokens(rootSequence.Items, 0))
                    return WriteSpaceJoinedLine(rootSequence.Items, 0);

                if ((_rootSpacing > 0 || HasIndentedPairBlockItem(rootSequence.Items))
                    && BlockItemsAreSafe(rootSequence.Items))
                {
                    _frames.Push(new Frame
                    {
                        Items = rootSequence.Items,
                        Level = 0,
                        Kind = FrameKind.ConciseBlock,
                        PairRun = IsConcisePairRun(rootSequence.Items, 0),
                    });
                    return WriteFrames();
                }
            }

            if (row is not (Result.SequenceValue or Result.ListValue)
                || (FitsInline(row, 0, 0) && !RequiresStructuredLayout(row, asChild: false)))
            {
                return StartLine(0) && AppendInline(row);
            }

            if (!OpenDelimited(row, 0, closeComma: false)) return false;
            return WriteFrames();
        }

        private bool WriteFrames()
        {
            while (_frames.Count > 0)
            {
                var frame = _frames.Peek();

                if (frame.Next >= frame.Items.Count)
                {
                    _frames.Pop();
                    if (frame.Kind != FrameKind.ConciseBlock)
                    {
                        if (!StartLine(frame.Level - 1)) return false;
                        if (!_writer.Append(frame.Kind == FrameKind.ParenSequence ? ")" : "]")) return false;
                        if (frame.CloseComma && !_writer.Append(",")) return false;
                    }

                    // A completed multiline child is not a single line, so the
                    // enclosing concise block cannot hang a sub-block off it.
                    if (_frames.Count > 0)
                        _frames.Peek().PrevItemWasLine = false;
                    continue;
                }

                if (frame.PairRun)
                {
                    if (!WritePairLine(frame)) return false;
                    continue;
                }

                if (frame.Kind == FrameKind.ConciseBlock)
                {
                    if (!WriteBlockItem(frame)) return false;
                    continue;
                }

                var item = frame.Items[frame.Next];
                var isLast = frame.Next == frame.Items.Count - 1;
                frame.Next++;

                if (item is Result.SequenceValue or Result.ListValue
                    && (RequiresStructuredLayout(item, asChild: true)
                        || !FitsInline(item, frame.Level, isLast ? 0 : 1)))
                {
                    if (!OpenDelimited(item, frame.Level, closeComma: !isLast)) return false;
                    continue;
                }

                if (!StartLine(frame.Level)) return false;
                if (!AppendInline(item)) return false;
                if (!isLast && !_writer.Append(",")) return false;
            }

            return true;
        }

        /// <summary>
        /// One line of a pair-run frame: a string label and its scalar value
        /// (an atom or a string). This is line GROUPING only — the items,
        /// their order, and their contents are untouched; delimited frames
        /// keep canonical comma separators, concise blocks separate the pair
        /// with one space.
        /// </summary>
        private bool WritePairLine(Frame frame)
        {
            var label = frame.Items[frame.Next];
            var value = frame.Items[frame.Next + 1];
            frame.Next += 2;
            var isLastPair = frame.Next >= frame.Items.Count;

            if (!StartLine(frame.Level)) return false;
            if (!AppendInline(label)) return false;
            if (!_writer.Append(frame.Kind == FrameKind.ConciseBlock ? " " : ", ")) return false;
            if (!AppendInline(value)) return false;
            if (frame.Kind != FrameKind.ConciseBlock && !isLastPair && !_writer.Append(",")) return false;
            frame.PrevItemWasLine = true;
            return true;
        }

        /// <summary>One item of a concise paren-hidden block.</summary>
        private bool WriteBlockItem(Frame frame)
        {
            var item = frame.Items[frame.Next];

            if (item is Result.SequenceValue { Items.Count: >= 2 } childSequence)
            {
                var childItems = childSequence.Items;

                // A safe alternating multi-pair child (two or more pairs) is
                // presented as an indented pair block even when it would fit
                // joined on one line: within a parent block, indentation
                // exposes the nested structure a flat join would erase. It
                // must hang off a preceding single-line sibling and must not
                // sit next to another block-shaped sibling, so paren-less
                // blocks can never merge; with zero indentation the nesting
                // would be invisible, so the pair block is not formed.
                if (IsPairBlockChild(childItems, frame.Level)
                    && frame.PrevItemWasLine
                    && !NextItemIsBlockCandidate(frame))
                {
                    frame.Next++;
                    frame.PrevItemWasLine = false;
                    _frames.Push(new Frame
                    {
                        Items = childItems,
                        Level = frame.Level + 1,
                        Kind = FrameKind.ConciseBlock,
                        PairRun = true,
                    });
                    return true;
                }

                if (CanSpaceJoinTokens(childItems, frame.Level))
                {
                    // A short flat child sequence occupying one entire logical
                    // line: parentheses safely carried by the line boundary.
                    frame.Next++;
                    frame.PrevItemWasLine = true;
                    return WriteSpaceJoinedLine(childItems, frame.Level);
                }

                if (RequiresStructuredLayout(item, asChild: true) || !FitsInline(item, frame.Level, 0))
                {
                    // A child sequence rendered as a complete indented block may
                    // hide its parentheses only when the indentation uniquely
                    // preserves the structure: it must hang off a preceding
                    // single-line sibling, must not merge with an adjacent
                    // block-shaped sibling, and all of its immediate items must
                    // be safe block lines.
                    var subBlockEligible = _indentSize > 0
                        && frame.PrevItemWasLine
                        && !NextItemIsBlockCandidate(frame)
                        && BlockItemsAreSafe(childItems);

                    frame.Next++;
                    frame.PrevItemWasLine = false;

                    if (subBlockEligible)
                    {
                        _frames.Push(new Frame
                        {
                            Items = childItems,
                            Level = frame.Level + 1,
                            Kind = FrameKind.ConciseBlock,
                            PairRun = IsConcisePairRun(childItems, frame.Level + 1),
                        });
                        return true;
                    }

                    return OpenDelimited(item, frame.Level, closeComma: false);
                }

                // Fits inline with parentheses: an ordinary line below.
            }
            else if (item is (Result.SequenceValue or Result.ListValue) && !FitsInline(item, frame.Level, 0))
            {
                // Lists always keep their brackets; empty and singleton
                // sequences always keep their parentheses.
                frame.Next++;
                frame.PrevItemWasLine = false;
                return OpenDelimited(item, frame.Level, closeComma: false);
            }

            frame.Next++;
            frame.PrevItemWasLine = true;
            return StartLine(frame.Level) && AppendInline(item);
        }

        /// <summary>
        /// The next sibling's natural shape, used by the adjacent-sub-block
        /// guard: two consecutive paren-hidden blocks would merge visually into
        /// one, so the earlier one falls back to a line or a delimited form.
        /// </summary>
        private bool NextItemIsBlockCandidate(Frame frame)
        {
            var nextIndex = frame.Next + 1;
            if (nextIndex >= frame.Items.Count) return false;
            return IsBlockShapedChild(frame.Items[nextIndex], frame.Level);
        }

        /// <summary>
        /// Structural-complexity gate: fitting the preferred width is necessary
        /// but not sufficient for an inline layout. A sequence whose flat text
        /// fits still lays out multiline when it contains two or more
        /// structured children (nested sequences or lists) — that nesting is
        /// exactly the information the flat form erases. As a CHILD inside an
        /// already structured layout, an alternating string/value run of two or
        /// more pairs also prefers multiline pair lines; at root a flat pair
        /// sequence may stay inline. Purely flat values are unaffected, so
        /// simple results remain inline and the formatters never become
        /// unconditionally vertical.
        /// </summary>
        private bool RequiresStructuredLayout(Result value, bool asChild)
        {
            if (value is not Result.SequenceValue(var items)) return false;

            if (asChild
                && items.Count >= PredicateCacheThreshold
                && _structuredChildLayoutCache.TryGetValue(items, out var cached))
            {
                return cached;
            }

            var structuredChildren = 0;
            foreach (var item in items)
            {
                if (item is Result.SequenceValue or Result.ListValue && ++structuredChildren >= 2)
                {
                    if (asChild && items.Count >= PredicateCacheThreshold)
                        TryCache(_structuredChildLayoutCache, items, true);
                    return true;
                }
            }

            var result = asChild && items.Count >= 4 && IsStructuralPairRun(items);
            if (asChild && items.Count >= PredicateCacheThreshold)
                TryCache(_structuredChildLayoutCache, items, result);
            return result;
        }

        /// <summary>
        /// A child that renders as an indented concise pair block: two or more
        /// safe alternating string/value pairs, with visible indentation
        /// available to carry the nesting.
        /// </summary>
        private bool IsPairBlockChild(IReadOnlyList<Result> items, int level)
            => _indentSize > 0 && items.Count >= 4 && IsConcisePairRun(items, level + 1);

        /// <summary>
        /// Whether this sibling would itself claim paren-hidden block-shaped
        /// rendering at the given level — an indented pair block, or a
        /// non-joinable sequence that cannot stay on one line. Used by the
        /// adjacency guard so two paren-less blocks can never sit side by side.
        /// </summary>
        private bool IsBlockShapedChild(Result item, int level)
        {
            if (item is not Result.SequenceValue { Items.Count: >= 2 } sequence) return false;
            if (IsPairBlockChild(sequence.Items, level)) return true;
            return !CanSpaceJoinTokens(sequence.Items, level)
                && !FitsInline(item, level, 0);
        }

        /// <summary>
        /// Conservative "this item will render as one unindented line at the
        /// block's own level" test, used by the zero-spacing root-block gate:
        /// a nested pair block anchors a root block only when it visibly hangs
        /// off a preceding line.
        /// </summary>
        private bool RendersAsBlockLine(Result item)
            => item switch
            {
                // Block-item strings are pre-checked safe tokens, so leaves
                // always occupy exactly one line.
                Result.Atom or Result.Str => true,
                Result.SequenceValue { Items.Count: >= 2 } sequence
                    => CanSpaceJoinTokens(sequence.Items, 0)
                        || (!RequiresStructuredLayout(item, asChild: true) && FitsInline(item, 0, 0)),
                Result.SequenceValue or Result.ListValue => FitsInline(item, 0, 0),
                _ => false,
            };

        /// <summary>
        /// Zero-root-spacing safety for paren-hidden root blocks: without blank
        /// lines between roots, a block whose every item is an ordinary line
        /// would render exactly like several independent root rows. The block
        /// is therefore allowed only when at least one nested multi-pair child
        /// will render as an indented pair block hanging off a preceding line —
        /// indentation no independent root row can begin with.
        /// </summary>
        private bool HasIndentedPairBlockItem(IReadOnlyList<Result> items)
        {
            for (var i = 1; i < items.Count; i++)
            {
                if (items[i] is not Result.SequenceValue { Items.Count: >= 4 } child) continue;
                if (!IsPairBlockChild(child.Items, 0)) continue;
                if (!RendersAsBlockLine(items[i - 1])) continue;
                if (i + 1 < items.Count && IsBlockShapedChild(items[i + 1], 0)) continue;
                return true;
            }

            return false;
        }

        /// <summary>
        /// Whether all tokens can form a whole-line space join. Returns false
        /// when any item lacks a safe single-token representation under the
        /// active string policy (see
        /// <see cref="DelimitedStringTextPolicy.IsTokenSafe"/> — the decision
        /// is per concrete value, never a global mode switch) or the joined
        /// line would exceed the preferred width. Atom tokens are always safe
        /// (canonical invariant number text contains no whitespace or commas);
        /// structural items never join, so nested sequences and lists keep
        /// their own delimiters.
        /// </summary>
        private bool CanSpaceJoinTokens(IReadOnlyList<Result> items, int level)
        {
            var columns = ColumnsOf(level);
            long total = columns + items.Count - 1;
            if (total > _width) return false;

            foreach (var item in items)
            {
                long tokenLength;
                switch (item)
                {
                    case Result.Atom(var number):
                        tokenLength = ValueTextRenderer.FormatAtom(number, _displayOptions).Length;
                        break;
                    case Result.Str(var text):
                        // Raw content length is a lower bound under every
                        // delimiter policy. Apply it before asking the policy
                        // whether quotes are needed/possible, because that
                        // classification may scan the string.
                        if (total + text.Length > _width) return false;
                        tokenLength = _strings.TokenLength(text);
                        if (total + tokenLength > _width) return false;
                        if (!_strings.IsTokenSafe(text)) return false;
                        break;
                    default:
                        return false;
                }

                total += tokenLength;
                if (total > _width) return false;
            }

            return true;
        }

        private bool WriteSpaceJoinedLine(IReadOnlyList<Result> items, int level)
        {
            if (!StartLine(level)) return false;
            for (var i = 0; i < items.Count; i++)
            {
                if (i > 0 && !_writer.Append(" ")) return false;
                if (!AppendInline(items[i])) return false;
            }

            return true;
        }

        /// <summary>
        /// Immediate-item safety of a paren-hidden block: every string item
        /// must be a safe standalone token under the active policy
        /// (<see cref="DelimitedStringTextPolicy.IsTokenSafe"/>). An unsafe
        /// string — a blank line, a line whose content mimics several items or
        /// a separator, or raw text indistinguishable from other syntax —
        /// keeps the parentheses instead. Non-string items are safe here:
        /// atoms and bracketed/parenthesized structures carry their own
        /// boundaries, and nested sequences make their own decision one level
        /// deeper.
        /// </summary>
        private bool BlockItemsAreSafe(IReadOnlyList<Result> items)
        {
            foreach (var item in items)
            {
                if (item is Result.Str(var text)
                    && !_strings.IsTokenSafe(text))
                {
                    return false;
                }
            }

            return true;
        }

        /// <summary>
        /// Structural pair run: an even number of alternating string/value
        /// items where every value is a SCALAR leaf (an atom or a string) —
        /// structured values (nested sequences or lists) never form pairs and
        /// keep conservative delimiters. Grouping pairs onto lines never
        /// changes items, order, or contents; it is presentation only, not
        /// dictionary or record semantics.
        /// </summary>
        private bool IsStructuralPairRun(IReadOnlyList<Result> items)
        {
            if (items.Count >= PredicateCacheThreshold
                && _structuralPairRunCache.TryGetValue(items, out var cached))
            {
                return cached;
            }

            if (items.Count < 2 || items.Count % 2 != 0) return false;
            for (var i = 0; i < items.Count; i += 2)
            {
                if (items[i] is not Result.Str || items[i + 1] is not (Result.Atom or Result.Str))
                {
                    if (items.Count >= PredicateCacheThreshold)
                        TryCache(_structuralPairRunCache, items, false);
                    return false;
                }
            }

            if (items.Count >= PredicateCacheThreshold)
                TryCache(_structuralPairRunCache, items, true);
            return true;
        }

        /// <summary>
        /// The rendered token length of one pair-position scalar, or null when
        /// it is unsafe or exceeds the supplied cap. String content length is
        /// checked before any delimiter/safety scan.
        /// </summary>
        private long? SafePairTokenLength(Result item, long maxLength)
        {
            if (maxLength < 0) return null;

            switch (item)
            {
                case Result.Atom(var number):
                    var atomLength = ValueTextRenderer.FormatAtom(number, _displayOptions).Length;
                    return atomLength <= maxLength ? atomLength : null;
                case Result.Str(var text):
                    if (text.Length > maxLength) return null;
                    if (!_strings.IsTokenSafe(text)) return null;
                    var tokenLength = _strings.TokenLength(text);
                    return tokenLength <= maxLength ? tokenLength : null;
                default:
                    return null;
            }
        }

        /// <summary>Pair-run eligibility for a concise block: safe label and value tokens, every pair line within width.</summary>
        private bool IsConcisePairRun(IReadOnlyList<Result> items, int level)
        {
            Dictionary<int, bool>? levels = null;
            var attachLevels = false;
            if (items.Count >= PredicateCacheThreshold)
            {
                if (_concisePairRunCache.TryGetValue(items, out levels)
                    && levels.TryGetValue(level, out var cached))
                {
                    return cached;
                }

                if (levels is null && _concisePairRunCache.Count < PredicateCacheCapacity)
                {
                    levels = [];
                    attachLevels = true;
                }
            }

            var result = ComputeConcisePairRun(items, level);
            if (levels is not null && levels.Count < PredicateCacheCapacity)
            {
                levels.TryAdd(level, result);
                if (attachLevels)
                    _concisePairRunCache.TryAdd(items, levels);
            }

            return result;
        }

        private bool ComputeConcisePairRun(IReadOnlyList<Result> items, int level)
        {
            if (!IsStructuralPairRun(items)) return false;
            var columns = ColumnsOf(level);
            for (var i = 0; i < items.Count; i += 2)
            {
                var available = (long)_width - columns;
                if (SafePairTokenLength(items[i], available - 1) is not { } labelLength) return false;
                if (SafePairTokenLength(items[i + 1], available - labelLength - 1) is not { } valueLength) return false;
                if (columns + labelLength + 1 + valueLength > _width) return false;
            }

            return true;
        }

        private static void TryCache(
            Dictionary<IReadOnlyList<Result>, bool> cache,
            IReadOnlyList<Result> items,
            bool value)
        {
            if (cache.Count < PredicateCacheCapacity)
                cache.TryAdd(items, value);
        }

        /// <summary>
        /// Pair-run eligibility for a delimited sequence frame: every
        /// comma-separated pair line within width. Token safety is not
        /// required here — the retained commas and parentheses delimit the
        /// items exactly like any other delimited content.
        /// </summary>
        private bool IsCommaPairRun(IReadOnlyList<Result> items, int level)
        {
            if (!IsStructuralPairRun(items)) return false;
            var columns = ColumnsOf(level);
            for (var i = 0; i < items.Count; i += 2)
            {
                var separator = i + 2 >= items.Count ? 0 : 1;
                var labelText = ((Result.Str)items[i]).Value;
                var fixedLength = (long)columns + 2 + separator;
                if (fixedLength + labelText.Length > _width) return false;
                var labelLength = _strings.TokenLength(labelText);
                if (fixedLength + labelLength > _width) return false;

                var valueLength = items[i + 1] switch
                {
                    Result.Atom(var number) => ValueTextRenderer.FormatAtom(number, _displayOptions).Length,
                    Result.Str(var text) when fixedLength + labelLength + text.Length <= _width
                        => _strings.TokenLength(text),
                    _ => long.MaxValue / 2,
                };
                if (fixedLength + labelLength + valueLength > _width) return false;
            }

            return true;
        }

        /// <summary>Opens a multiline delimited structure: the opening token on its own line, items one level deeper.</summary>
        private bool OpenDelimited(Result value, int atLevel, bool closeComma)
        {
            IReadOnlyList<Result> items;
            FrameKind kind;
            switch (value)
            {
                case Result.SequenceValue(var sequenceItems):
                    items = sequenceItems;
                    kind = FrameKind.ParenSequence;
                    break;
                case Result.ListValue(var listItems):
                    items = listItems;
                    kind = FrameKind.BracketList;
                    break;
                default:
                    return StartLine(atLevel) && AppendInline(value);
            }

            if (!StartLine(atLevel)) return false;
            if (!_writer.Append(kind == FrameKind.ParenSequence ? "(" : "[")) return false;
            _frames.Push(new Frame
            {
                Items = items,
                Level = atLevel + 1,
                Kind = kind,
                PairRun = kind == FrameKind.ParenSequence && IsCommaPairRun(items, atLevel + 1),
                CloseComma = closeComma,
            });
            return true;
        }

        /// <summary>
        /// Width-capped inline-fit test: measures through the SAME renderer
        /// that would emit the text, stopping at the remaining line width.
        /// </summary>
        private bool FitsInline(Result value, int level, int reserve)
        {
            var budget = (long)_width - ColumnsOf(level) - reserve;
            if (budget < 0) return false;
            _measure.Reset((int)Math.Min(budget, int.MaxValue));
            return ValueTextRenderer.AppendValue(value, _displayOptions, _strings, _measure);
        }

        private bool AppendInline(Result value)
            => ValueTextRenderer.AppendValue(value, _displayOptions, _strings, _writer);

        /// <summary>Ends the previous line (if any) and writes this line's indentation, all charged.</summary>
        private bool StartLine(int level)
        {
            if (_startedOutput && !_writer.Append(_newLine)) return false;
            _startedOutput = true;
            var columns = ColumnsOf(level);
            return columns == 0 || _writer.Append(' ', columns);
        }

        private int ColumnsOf(int level)
            => (int)Math.Min((long)level * _indentSize, int.MaxValue);
    }
}
