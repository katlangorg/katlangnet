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
/// <para><b>Decisions read counters, never the stored list.</b> Recovery and loading decisions
/// that ask whether something was reported — the parser's clause-head recovery, whether a loaded
/// module elaborated cleanly enough to cache, whether a materialization succeeded, how a failed
/// module parse is classified — read <see cref="ReportedCount"/>,
/// <see cref="ReportedErrorCount"/>, and <see cref="HasReported"/>, which count dropped reports
/// too. The budget therefore changes which diagnostics are STORED and nothing else: the tree,
/// module loading, and every decision are identical at any capacity.</para>
///
/// <para><b>Stages.</b> A pass whose diagnostics may still be discarded and replaced (parameter
/// detection and implicit-argument resolution before ownership completion) reports into a STAGE
/// bag of the same capacity (<see cref="CreateStage"/>). Committing it
/// (<see cref="AddRange(DiagnosticBag)"/>) appends its diagnostics exactly as if they had been
/// reported here — its dropped reports included — so the prefix law holds for the final list,
/// and a live stage never stores more than one list could.</para>
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

    private readonly List<Diagnostic> _stored = [];
    private long _reported;
    private long _reportedErrors;
    private ulong _reportedCodes;
    private HashSet<DiagnosticCode>? _reportedOtherCodes;
    private bool _truncated;

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
    internal bool IsTruncated => _truncated;

    /// <summary>
    /// True while the next report would be stored. A caller may test it before formatting an
    /// expensive message, but must still report (a report is what the counters observe) —
    /// <see cref="Report{TState}(DiagnosticCode, SourceSpan?, TState, Func{TState, string})"/>
    /// does both.
    /// </summary>
    internal bool StoresNext => _reported < Capacity;

    /// <summary>The stored diagnostics, including the trailing marker when truncated.</summary>
    public int Count => _stored.Count;

    public Diagnostic this[int index] => _stored[index];

    public IEnumerator<Diagnostic> GetEnumerator() => _stored.GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    /// <summary>A stage bag of the same capacity, committed later with <see cref="AddRange(DiagnosticBag)"/>.</summary>
    internal DiagnosticBag CreateStage() => new(Capacity);

    /// <summary>Whether a diagnostic of <paramref name="code"/> was reported, stored or dropped.</summary>
    internal bool HasReported(DiagnosticCode code)
    {
        var value = (int)code;
        return value is >= 0 and < 64
            ? (_reportedCodes & (1UL << value)) != 0
            : _reportedOtherCodes?.Contains(code) == true;
    }

    /// <summary>Reports an already constructed diagnostic.</summary>
    internal void Add(Diagnostic diagnostic)
    {
        ArgumentNullException.ThrowIfNull(diagnostic);
        if (!CountReport(diagnostic.Code, diagnostic.Severity))
            return;

        _stored.Add(diagnostic.Message.Length <= MaxRetainedMessageLength
            ? diagnostic
            : diagnostic with { Message = BoundMessage(diagnostic.Message) });
    }

    /// <summary>Reports an error; the diagnostic is constructed only when it is stored.</summary>
    internal void Report(DiagnosticCode code, string message, SourceSpan? span)
    {
        if (CountReport(code, DiagnosticSeverity.Error))
            _stored.Add(new Diagnostic(BoundMessage(message), DiagnosticSeverity.Error, span) { Code = code });
    }

    /// <summary>
    /// Reports an error whose message is formatted only when the diagnostic is stored — the
    /// form for high-volume report sites, so a report past the capacity allocates nothing.
    /// </summary>
    internal void Report<TState>(DiagnosticCode code, SourceSpan? span, TState state, Func<TState, string> formatMessage)
    {
        if (CountReport(code, DiagnosticSeverity.Error))
            _stored.Add(new Diagnostic(BoundMessage(formatMessage(state)), DiagnosticSeverity.Error, span) { Code = code });
    }

    /// <summary>Reports each diagnostic in order.</summary>
    internal void AddRange(IEnumerable<Diagnostic> diagnostics)
    {
        foreach (var diagnostic in diagnostics)
            Add(diagnostic);
    }

    /// <summary>
    /// Commits a stage: its stored diagnostics are reported here in order, and its dropped
    /// reports are counted here, exactly as if the stage had reported to this bag directly.
    /// </summary>
    internal void AddRange(DiagnosticBag stage)
    {
        ArgumentNullException.ThrowIfNull(stage);
        if (ReferenceEquals(stage, this))
            throw new InvalidOperationException("A diagnostic bag cannot commit itself.");

        var storedOrdinary = stage._stored.Count - (stage._truncated ? 1 : 0);
        long storedErrors = 0;
        for (var index = 0; index < storedOrdinary; index++)
        {
            var diagnostic = stage._stored[index];
            if (diagnostic.Severity == DiagnosticSeverity.Error)
                storedErrors++;
            Add(diagnostic);
        }

        _reportedCodes |= stage._reportedCodes;
        if (stage._reportedOtherCodes is { } otherCodes)
            (_reportedOtherCodes ??= []).UnionWith(otherCodes);

        var droppedErrors = stage._reportedErrors - storedErrors;
        CountDropped(stage._reported - storedOrdinary, droppedErrors, stage.DroppedSeverity(droppedErrors));
    }

    // The most severe severity the stage dropped: its marker carries it (see CountReport).
    private DiagnosticSeverity? DroppedSeverity(long droppedErrors)
        => droppedErrors > 0
            ? DiagnosticSeverity.Error
            : _truncated ? _stored[^1].Severity : null;

    private void CountDropped(long dropped, long droppedErrors, DiagnosticSeverity? droppedSeverity)
    {
        if (dropped <= 0)
            return;

        _reported += dropped;
        _reportedErrors += droppedErrors;
        if (_reported > Capacity)
            MarkTruncated(droppedSeverity ?? DiagnosticSeverity.Error);
    }

    // Counts one report and says whether it is stored. A report past the capacity truncates the
    // list: the first one appends the marker, and a later, more severe one raises its severity.
    private bool CountReport(DiagnosticCode code, DiagnosticSeverity severity)
    {
        _reported++;
        if (severity == DiagnosticSeverity.Error)
            _reportedErrors++;

        var value = (int)code;
        if (value is >= 0 and < 64)
            _reportedCodes |= 1UL << value;
        else
            (_reportedOtherCodes ??= []).Add(code);

        if (_reported <= Capacity)
            return true;

        MarkTruncated(severity);
        return false;
    }

    private void MarkTruncated(DiagnosticSeverity severity)
    {
        if (!_truncated)
        {
            _truncated = true;
            _stored.Add(SourceProcessingDiagnostics.DiagnosticCountExceeded(Capacity, severity));
            return;
        }

        if (severity > _stored[^1].Severity)
            _stored[^1] = SourceProcessingDiagnostics.DiagnosticCountExceeded(Capacity, severity);
    }

    private static string BoundMessage(string message)
    {
        if (message.Length <= MaxRetainedMessageLength)
            return message;

        return string.Concat(
            message.AsSpan(0, ExprNameRenderer.SafePrefixLength(message, MaxRetainedMessageLength)),
            ExprNameRenderer.TruncationMarker);
    }
}
