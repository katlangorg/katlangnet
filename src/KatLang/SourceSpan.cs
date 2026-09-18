namespace KatLang;

/// <summary>
/// A human-readable source coordinate: a 1-based <see cref="Line"/> and a 1-based
/// <see cref="Column"/> in the document a result describes. The coordinate contract is the
/// lexer's (<see cref="Lexer.Tokenize(string)"/>): a line feed ends a line, a carriage return
/// advances neither line nor column, and the column advances one per UTF-16 code unit (a
/// surrogate pair occupies two columns). Positions order lexicographically — by line, then by
/// column — which is what <see cref="CompareTo"/> and the comparison operators express.
/// <para>A position is a value: two positions with the same line and column are equal and hash
/// alike. The type is a struct, so <c>default(SourcePosition)</c> exists, but its zero
/// coordinates are NOT a position and never mean "no location": the constructor rejects them,
/// and an absent location is a <see langword="null"/> <c>SourceSpan?</c>, never a default
/// value. Human coordinates are a different concept from UTF-16 offsets into the source text
/// (<see cref="Token.Position"/> / <see cref="Token.Length"/>); the two are not merged.</para>
/// </summary>
public readonly record struct SourcePosition : IComparable<SourcePosition>
{
    /// <summary>
    /// Creates the position at <paramref name="line"/>:<paramref name="column"/>. Both are
    /// 1-based; a value below 1 is rejected, so a default-initialized coordinate can never
    /// enter a real location.
    /// </summary>
    public SourcePosition(int line, int column)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(line, 1);
        ArgumentOutOfRangeException.ThrowIfLessThan(column, 1);
        Line = line;
        Column = column;
    }

    /// <summary>The 1-based line.</summary>
    public int Line { get; }

    /// <summary>The 1-based column, counted in UTF-16 code units from the start of the line.</summary>
    public int Column { get; }

    public void Deconstruct(out int line, out int column)
    {
        line = Line;
        column = Column;
    }

    /// <summary>Lexicographic order: by <see cref="Line"/>, then by <see cref="Column"/>.</summary>
    public int CompareTo(SourcePosition other)
        => Line != other.Line ? Line.CompareTo(other.Line) : Column.CompareTo(other.Column);

    public static bool operator <(SourcePosition left, SourcePosition right) => left.CompareTo(right) < 0;

    public static bool operator <=(SourcePosition left, SourcePosition right) => left.CompareTo(right) <= 0;

    public static bool operator >(SourcePosition left, SourcePosition right) => left.CompareTo(right) > 0;

    public static bool operator >=(SourcePosition left, SourcePosition right) => left.CompareTo(right) >= 0;

    /// <summary>The earlier of two positions.</summary>
    public static SourcePosition Min(SourcePosition left, SourcePosition right) => left <= right ? left : right;

    /// <summary>The later of two positions.</summary>
    public static SourcePosition Max(SourcePosition left, SourcePosition right) => left >= right ? left : right;

    /// <summary>Renders <c>line:column</c>.</summary>
    public override string ToString() => $"{Line}:{Column}";
}

/// <summary>
/// A source location: the half-open range <c>[Start, End)</c> of human coordinates
/// (<see cref="SourcePosition"/>) in the document a result describes. <see cref="Start"/> is the
/// first covered coordinate and <see cref="End"/> the first coordinate AFTER the covered text, so
/// <c>[1:1, 1:2)</c> covers exactly one code unit and <c>[1:1, 1:1)</c> is an empty insertion
/// point — the position of an end-of-input diagnostic or of a missing token — which is a valid
/// span: <c>Start &lt;= End</c> is the one ordering invariant, and zero width is allowed.
/// <para>A span is a value: two spans with the same coordinates are equal and hash alike, and
/// nothing in KatLang keys a location by reference identity. Every span exposed by one result —
/// a <see cref="Diagnostic.Span"/>, an <see cref="EvalError.Span"/>, a <see cref="KatLangError.Span"/>,
/// an AST node's <see cref="Expr.Span"/>, a semantic-model site — belongs to THAT result's
/// document (one coordinate space per result): a module a document loads is spliced as a
/// locationless import view, and its constructs are positioned by the current document or not
/// at all. An absent location is a <see langword="null"/> <c>SourceSpan?</c>. The struct's
/// <c>default</c> value (both coordinates at 0:0) is not a location and never means "absent":
/// the constructor rejects zero coordinates, so no real span can carry them.</para>
/// <para>A span records human coordinates only; a <see cref="Token"/> keeps its UTF-16 source
/// offset and length separately (<see cref="Token.Position"/>, <see cref="Token.Length"/>) and
/// derives its span from them (<see cref="Token.Span"/>).</para>
/// </summary>
public readonly record struct SourceSpan
{
    /// <summary>
    /// Creates the half-open span <c>[start, end)</c>. Both positions must be real coordinates
    /// (line and column at least 1 — a default-initialized <see cref="SourcePosition"/> is
    /// rejected) and <paramref name="end"/> must not precede <paramref name="start"/>; equal
    /// positions form a valid empty span.
    /// </summary>
    public SourceSpan(SourcePosition start, SourcePosition end)
    {
        if (start.Line < 1 || start.Column < 1)
            throw new ArgumentOutOfRangeException(nameof(start), start, "A source span needs a real start position: lines and columns are 1-based.");
        if (end.Line < 1 || end.Column < 1)
            throw new ArgumentOutOfRangeException(nameof(end), end, "A source span needs a real end position: lines and columns are 1-based.");
        if (end < start)
            throw new ArgumentOutOfRangeException(nameof(end), end, $"A source span's end must not precede its start ({start}).");

        Start = start;
        End = end;
    }

    /// <summary>
    /// Creates the half-open span from <paramref name="startLine"/>:<paramref name="startColumn"/>
    /// up to but not including <paramref name="endLine"/>:<paramref name="endColumn"/>.
    /// </summary>
    public SourceSpan(int startLine, int startColumn, int endLine, int endColumn)
        : this(new SourcePosition(startLine, startColumn), new SourcePosition(endLine, endColumn))
    {
    }

    /// <summary>The first covered coordinate.</summary>
    public SourcePosition Start { get; }

    /// <summary>The first coordinate after the covered text (exclusive).</summary>
    public SourcePosition End { get; }

    /// <summary>True for an empty insertion point (<see cref="Start"/> equals <see cref="End"/>).</summary>
    public bool IsEmpty => Start == End;

    public void Deconstruct(out SourcePosition start, out SourcePosition end)
    {
        start = Start;
        end = End;
    }

    /// <summary>
    /// True when <paramref name="position"/> lies inside the half-open range:
    /// <c>Start &lt;= position &lt; End</c>. The start coordinate is included, the end coordinate is
    /// excluded, an empty span contains nothing, and two spans that share a boundary do not both
    /// contain it.
    /// </summary>
    public bool Contains(SourcePosition position) => Start <= position && position < End;

    /// <summary>
    /// The hull of this span and <paramref name="other"/>: from the earlier start to the later
    /// end. Adjacent, overlapping, disjoint, and empty operands are all just positions to
    /// compare — the hull of a span with an empty one still extends to the empty one's position.
    /// </summary>
    public SourceSpan Union(SourceSpan other)
        => new(SourcePosition.Min(Start, other.Start), SourcePosition.Max(End, other.End));

    /// <summary>
    /// Renders the half-open range as <c>[start, end)</c> (for example <c>[1:1, 1:6)</c>); an
    /// empty span renders its single position as <c>[1:6]</c>.
    /// </summary>
    public override string ToString() => IsEmpty ? $"[{Start}]" : $"[{Start}, {End})";
}
