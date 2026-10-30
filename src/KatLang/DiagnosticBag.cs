using System.Collections;

namespace KatLang;

/// <summary>
/// The ONE accumulator of the diagnostics a source-processing operation produces, and the owner
/// of the per-list diagnostic budget (<see cref="SourceProcessingLimits.MaxDiagnosticCount"/>).
/// One bag serves one diagnostic list: a parse — the lexer, the parser, module loading, every
/// module and nested module the parse loads, and every elaboration pass all report into it — or
/// one demand-time materialization of a deferred branch.
///
/// <para><b>The prefix law.</b> A bag of capacity N stores exactly the first N diagnostics
/// reported to it, in report order — the list an unbounded operation would have produced, cut
/// after N — and, only when more were reported, ONE trailing
/// <see cref="DiagnosticCode.DiagnosticCountExceeded"/> marker, which the capacity does not
/// count. A report past the capacity is counted and otherwise dropped: no
/// <see cref="Diagnostic"/> is constructed for it and, through
/// <see cref="Report{TState}(DiagnosticCode, SourceSpan?, TState, Func{TState, string})"/>, its
/// message is never formatted. The marker carries the most severe dropped severity, so
/// truncation never changes whether a list blocks evaluation.</para>
///
/// <para><b>Anchored reports.</b> A report a pass decides only later — parameter detection's check of
/// a dot fallback that implicit-argument resolution finds certain (M4★) — takes the place in the
/// list where the deciding pass would have made it: the deferring pass reserves an ANCHOR at that
/// point (<see cref="ReserveAnchor"/>), and the report made later under it
/// (<see cref="InsertingAt"/>) stands after every report made before the anchor was reserved and
/// before every report made after — anchors reserved at one point in their reservation order, the
/// reports of one anchor in their own order. The list is the list the operation would have produced
/// had each anchored report been made at its anchor, and the prefix law holds for it: a report an
/// anchored one moves past the capacity is dropped (the marker takes its severity). Counters count a
/// report when it is made.</para>
///
/// <para><b>Decisions read counters, never the stored list.</b> Recovery and loading decisions
/// that ask whether something was reported — the parser's clause-head recovery, whether a loaded
/// module elaborated cleanly enough to cache, whether a materialization succeeded, how a failed
/// module parse is classified — read <see cref="ReportedCount"/>,
/// <see cref="ReportedErrorCount"/>, and <see cref="HasReported"/>, which count dropped reports
/// too. The budget therefore changes which diagnostics are STORED and nothing else: the tree,
/// module loading, and every decision are identical at any capacity.</para>
///
/// <para><b>Stages.</b> A list that is WITHHELD — every pass of a provisional elaboration, whose
/// diagnostics may depend on a missing module (see <see cref="FrontEndPipeline"/>) — goes to a
/// STAGE bag of the same capacity (<see cref="CreateStage"/>), so it never stores more than one
/// list could. A stage is never committed: nothing it holds reaches the operation's list.</para>
///
/// <para><b>Payload.</b> Every stored message is at most <see cref="MaxRetainedMessageLength"/>
/// UTF-16 code units (a longer one keeps its surrogate-safe prefix and the <c>…</c> marker), so a
/// full list is bounded by a constant whatever the source echoed.</para>
///
/// <para>Not thread-safe: one operation reports sequentially (a deferred materialization runs
/// under its loader's materialization gate).</para>
/// </summary>
internal sealed class DiagnosticBag : IReadOnlyList<Diagnostic>
{
    /// <summary>
    /// Longest stored diagnostic message, in UTF-16 code units. Every bounded message KatLang
    /// formats — echoed names and lists at most <see cref="ExprNameRenderer.MaxRenderedNameLength"/>
    /// units each, a refused load target at most about 1,250 — stays far below it; only a message
    /// that echoes a multi-kilobyte identifier or URL the source wrote is cut.
    /// </summary>
    internal const int MaxRetainedMessageLength = 4096;

    // The stored diagnostics (the marker excluded) and, in parallel, each one's place in the list.
    private readonly List<Diagnostic> _stored = [];
    private readonly List<ListPlace> _places = [];
    private Diagnostic? _marker;
    private long _reported;
    private long _reportedErrors;
    private ulong _reportedCodes;
    private HashSet<DiagnosticCode>? _reportedOtherCodes;

    // Reports made in place (never under an anchor), and anchors reserved so far.
    private long _inPlace;
    private long _anchors;

    // While an anchored scope is open (InsertingAt): its anchor and the reports made under it.
    private DiagnosticAnchor? _inserting;
    private int _insertedUnderAnchor;

    /// <summary>A bag with the supported maximum capacity.</summary>
    internal DiagnosticBag()
        : this(SourceProcessingLimits.MaxSupportedDiagnosticCount)
    {
    }

    /// <summary>A bag that stores at most <paramref name="capacity"/> diagnostics before its marker.</summary>
    internal DiagnosticBag(int capacity)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(capacity, 1);
        Capacity = capacity;
    }

    /// <summary>How many reported diagnostics this bag stores before it is truncated.</summary>
    internal int Capacity { get; }

    /// <summary>Every diagnostic reported so far, stored or dropped (the marker excluded).</summary>
    internal long ReportedCount => _reported;

    /// <summary>Every error-severity diagnostic reported so far, stored or dropped.</summary>
    internal long ReportedErrorCount => _reportedErrors;

    /// <summary>True once any error-severity diagnostic was reported, stored or dropped.</summary>
    internal bool HasReportedErrors => _reportedErrors > 0;

    /// <summary>True once a report was dropped, so the stored list ends with the marker.</summary>
    internal bool IsTruncated => _marker is not null;

    /// <summary>
    /// True while the next report would be stored. A caller may test it before formatting an
    /// expensive message, but must still report (a report is what the counters observe) —
    /// <see cref="Report{TState}(DiagnosticCode, SourceSpan?, TState, Func{TState, string})"/>
    /// does both.
    /// </summary>
    internal bool StoresNext => _inserting is { } anchor ? StoresAt(PlaceUnder(anchor)) : _marker is null && _stored.Count < Capacity;

    /// <summary>The stored diagnostics, including the trailing marker when truncated.</summary>
    public int Count => _stored.Count + (_marker is null ? 0 : 1);

    public Diagnostic this[int index] => index == _stored.Count && _marker is not null ? _marker : _stored[index];

    public IEnumerator<Diagnostic> GetEnumerator()
    {
        foreach (var diagnostic in _stored)
            yield return diagnostic;
        if (_marker is not null)
            yield return _marker;
    }

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    /// <summary>A stage bag of the same capacity, for a withheld list (see the class documentation).</summary>
    internal DiagnosticBag CreateStage() => new(Capacity);

    /// <summary>Whether a diagnostic of <paramref name="code"/> was reported, stored or dropped.</summary>
    internal bool HasReported(DiagnosticCode code)
    {
        var value = (int)code;
        return value is >= 0 and < 64
            ? (_reportedCodes & (1UL << value)) != 0
            : _reportedOtherCodes?.Contains(code) == true;
    }

    /// <summary>
    /// Reserves the place a report decided later takes in the list: after every report made so far, before every
    /// report made from now on (see the class documentation). A reservation is no report: nothing is counted.
    /// </summary>
    internal DiagnosticAnchor ReserveAnchor() => new(_inPlace, ++_anchors);

    /// <summary>
    /// Makes every report until the returned scope is disposed at <paramref name="anchor"/>'s place, in report order
    /// (see the class documentation). Anchored scopes do not nest.
    /// </summary>
    internal AnchoredScope InsertingAt(DiagnosticAnchor anchor)
    {
        if (_inserting is not null)
            throw new InvalidOperationException("Anchored diagnostic scopes do not nest.");
        _inserting = anchor;
        _insertedUnderAnchor = 0;
        return new AnchoredScope(this);
    }

    /// <summary>Reports an already constructed diagnostic.</summary>
    internal void Add(Diagnostic diagnostic)
    {
        ArgumentNullException.ThrowIfNull(diagnostic);
        if (CountReport(diagnostic.Code, diagnostic.Severity) is not { } place)
            return;

        Store(place, diagnostic.WithBoundedMessage(MaxRetainedMessageLength));
    }

    /// <summary>Reports an error; the diagnostic is constructed only when it is stored.</summary>
    internal void Report(DiagnosticCode code, string message, SourceSpan? span)
    {
        if (CountReport(code, DiagnosticSeverity.Error) is { } place)
            Store(place, new Diagnostic(BoundMessage(message), DiagnosticSeverity.Error, span) { Code = code });
    }

    /// <summary>
    /// Reports an error whose message is formatted only when the diagnostic is stored — the
    /// form for high-volume report sites, so a report past the capacity allocates nothing.
    /// </summary>
    internal void Report<TState>(DiagnosticCode code, SourceSpan? span, TState state, Func<TState, string> formatMessage)
    {
        if (CountReport(code, DiagnosticSeverity.Error) is { } place)
            Store(place, new Diagnostic(BoundMessage(formatMessage(state)), DiagnosticSeverity.Error, span) { Code = code });
    }

    /// <summary>The same lazy report, retaining the formatter's structural separators.</summary>
    internal void Report<TState>(DiagnosticCode code, SourceSpan? span, TState state, Func<TState, DiagnosticMessage> formatMessage)
    {
        if (CountReport(code, DiagnosticSeverity.Error) is not { } place)
            return;
        var diagnostic = new Diagnostic(formatMessage(state), DiagnosticSeverity.Error, span) { Code = code };
        Store(place, diagnostic.WithBoundedMessage(MaxRetainedMessageLength));
    }

    // Counts one report and says where it is stored (its place in the list), or null when it is dropped: a report whose
    // place is past the capacity truncates the list, and a more severe dropped one raises the marker's severity. A report
    // made at an anchor may move the last stored one past the capacity (Store drops it then). Nothing is stored here, so
    // a message formatter that throws leaves the stored list as it was.
    private ListPlace? CountReport(DiagnosticCode code, DiagnosticSeverity severity)
    {
        _reported++;
        if (severity == DiagnosticSeverity.Error)
            _reportedErrors++;

        var value = (int)code;
        if (value is >= 0 and < 64)
            _reportedCodes |= 1UL << value;
        else
            (_reportedOtherCodes ??= []).Add(code);

        var place = _inserting is { } anchor ? PlaceUnder(anchor) : new ListPlace(++_inPlace, 0, 0);
        if (_inserting is not null)
            _insertedUnderAnchor++;
        if (!StoresAt(place))
        {
            MarkTruncated(severity);
            return null;
        }

        return place;
    }

    // Whether a report at `place` is among the first Capacity reports of the list: every stored report before it
    // counts, and once a report was dropped every later place is past the capacity too.
    private bool StoresAt(ListPlace place)
        => _stored.Count < Capacity && _marker is null
            || IndexOf(place) < Capacity && (_marker is null || place.CompareTo(_places[^1]) < 0);

    private ListPlace PlaceUnder(DiagnosticAnchor anchor) => new(anchor.Base, anchor.Sequence, _insertedUnderAnchor + 1);

    // The index a report at `place` takes among the stored reports (places are unique).
    private int IndexOf(ListPlace place)
    {
        var index = _places.BinarySearch(place);
        return index < 0 ? ~index : index;
    }

    // Stores a counted report at its place; a report beyond the capacity it moves out of the list is dropped.
    private void Store(ListPlace place, Diagnostic diagnostic)
    {
        var index = IndexOf(place);
        _places.Insert(index, place);
        _stored.Insert(index, diagnostic);
        if (_stored.Count <= Capacity)
            return;

        var moved = _stored[^1];
        _stored.RemoveAt(_stored.Count - 1);
        _places.RemoveAt(_places.Count - 1);
        MarkTruncated(moved.Severity);
    }

    private void MarkTruncated(DiagnosticSeverity severity)
    {
        if (_marker is null || severity > _marker.Severity)
            _marker = SourceProcessingDiagnostics.DiagnosticCountExceeded(Capacity, severity);
    }

    private void EndInsertion() => _inserting = null;

    private static string BoundMessage(string message)
    {
        if (message.Length <= MaxRetainedMessageLength)
            return message;

        return string.Concat(
            message.AsSpan(0, ExprNameRenderer.SafePrefixLength(message, MaxRetainedMessageLength)),
            ExprNameRenderer.TruncationMarker);
    }

    /// <summary>
    /// A report's place in the list: after the first <see cref="InPlace"/> reports made in place, then — for a report
    /// made at an anchor — after the anchors reserved before its own (<see cref="Anchor"/>, 0 for an in-place report),
    /// then in report order under its anchor (<see cref="Order"/>).
    /// </summary>
    private readonly record struct ListPlace(long InPlace, long Anchor, int Order) : IComparable<ListPlace>
    {
        public int CompareTo(ListPlace other)
        {
            var inPlace = InPlace.CompareTo(other.InPlace);
            if (inPlace != 0)
                return inPlace;
            var anchor = Anchor.CompareTo(other.Anchor);
            return anchor != 0 ? anchor : Order.CompareTo(other.Order);
        }
    }

    /// <summary>An open anchored scope (<see cref="InsertingAt"/>): disposing it ends the anchored reports.</summary>
    internal readonly struct AnchoredScope(DiagnosticBag bag) : IDisposable
    {
        public void Dispose() => bag?.EndInsertion();
    }
}

/// <summary>
/// The reserved place of a diagnostic a pass decides later (<see cref="DiagnosticBag.ReserveAnchor"/>): after the
/// <see cref="Base"/> reports made in place before it, in reservation order (<see cref="Sequence"/>).
/// </summary>
internal readonly record struct DiagnosticAnchor(long Base, long Sequence);
