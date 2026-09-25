namespace KatLang;

/// <summary>
/// Run-scoped, mutable accounting for <see cref="SourceProcessingLimits"/>: the aggregate source
/// elaborated (text accepted for parsing plus every splice of an already-loaded module), the
/// number of module downloads requested, and the current/peak import depth. One budget belongs to
/// exactly one run; the immutable <see cref="SourceProcessingLimits"/> may be shared by any number
/// of concurrent runs because the counters live here, never on the limits.
///
/// <para>Reservations use checked arithmetic and are all-or-nothing: a reservation that would
/// exceed its ceiling returns <c>false</c> and leaves its counter unchanged. The loader reserves
/// one module slot immediately before every downloader invocation and keeps it whatever the
/// download returns — a failed, oversized, or aggregate-rejected download still happened — and
/// reserves aggregate source for text accepted for parsing and for every splice of a cached
/// module. A module frame that is aborted by observed host cancellation rolls its own aggregate
/// reservations (its source and the splices its walk made) back before unwinding; downloader
/// invocations remain charged, including cancelled ones.</para>
///
/// <para>The diagnostic count is not a counter here: it bounds each diagnostic LIST, so the
/// budget only hands every operation its own bounded <see cref="DiagnosticBag"/>.</para>
/// </summary>
internal sealed class SourceProcessingBudget
{
    private readonly SourceProcessingLimits _limits;
    private long _aggregateSource;
    private int _moduleCount;
    private int _depth;

    internal SourceProcessingBudget(SourceProcessingLimits? limits)
        => _limits = limits ?? SourceProcessingLimits.Default;

    internal int MaxSourceLength => _limits.EffectiveMaxSourceLength;
    internal int MaxModuleDepth => _limits.EffectiveMaxModuleDepth;
    internal long MaxAggregateSourceLength => _limits.EffectiveMaxAggregateSourceLength;
    internal int MaxModuleCount => _limits.EffectiveMaxModuleCount;
    internal int MaxDiagnosticCount => _limits.EffectiveMaxDiagnosticCount;

    /// <summary>
    /// A fresh diagnostic list for one operation of this run — the parse, or one demand-time
    /// materialization of a deferred branch — bounded by the configured diagnostic count. The
    /// count bounds each LIST, so every operation gets its own bag; nothing here accumulates
    /// diagnostics across operations.
    /// </summary>
    internal DiagnosticBag CreateDiagnosticBag() => new(MaxDiagnosticCount);

    /// <summary>Total source (main plus every module accepted for parsing) reserved so far this run.</summary>
    internal long AggregateSource => _aggregateSource;

    /// <summary>Module downloads requested so far this run.</summary>
    internal int ModuleCount => _moduleCount;

    /// <summary>Current import nesting (for invariant checks and diagnostic reporting).</summary>
    internal int CurrentDepth => _depth;

    /// <summary>Deepest import nesting reached this run (for observation/testing).</summary>
    internal int PeakDepth { get; private set; }

    /// <summary>True when one source of the given length is within the per-source ceiling.</summary>
    internal bool SourceLengthWithinLimit(int length) => length <= _limits.EffectiveMaxSourceLength;

    /// <summary>
    /// True when <paramref name="length"/> more code units of aggregate source would still fit,
    /// without reserving anything. Lets a caller check several reservations before committing any.
    /// </summary>
    internal bool CanReserveAggregate(int length)
    {
        if (length < 0) return false;

        long projected;
        try { projected = checked(_aggregateSource + length); }
        catch (OverflowException) { return false; }

        return projected <= _limits.EffectiveMaxAggregateSourceLength;
    }

    /// <summary>True when one more module download would still fit, without reserving anything.</summary>
    internal bool CanReserveModule() => _moduleCount < _limits.EffectiveMaxModuleCount;

    /// <summary>
    /// Reserves <paramref name="length"/> code units of aggregate source. Returns <c>false</c>
    /// without mutating the total if the reservation would exceed the aggregate ceiling.
    /// </summary>
    internal bool TryReserveAggregate(int length)
    {
        if (!CanReserveAggregate(length)) return false;

        _aggregateSource += length;
        return true;
    }

    /// <summary>
    /// Reserves one module-download slot. Returns <c>false</c> without mutating the count when the
    /// module-count ceiling is already reached. The loader calls this immediately before every
    /// downloader invocation — a load served from the run's module cache must not call it — and
    /// the slot stays consumed whatever the download returns.
    /// </summary>
    internal bool TryReserveModule()
    {
        if (!CanReserveModule()) return false;

        _moduleCount++;
        return true;
    }

    /// <summary>
    /// Rolls back previously successful <see cref="TryReserveAggregate"/> calls totalling
    /// <paramref name="length"/> code units — a frame's own source and the splices its walk
    /// charged — when host cancellation aborts that frame before its result is kept.
    /// </summary>
    internal void RollbackAggregate(long length)
    {
        if (length < 0 || _aggregateSource < length)
            throw new InvalidOperationException("Cannot roll back an aggregate source reservation that is not active.");

        _aggregateSource -= length;
    }

    /// <summary>
    /// Descends one import level. Returns <c>false</c> without mutating the depth when the next
    /// level would exceed the import-depth ceiling; the caller must not descend in that case.
    /// Pair every successful call with <see cref="ExitModule"/> in a <c>finally</c>.
    /// </summary>
    internal bool TryEnterModule()
    {
        if (_depth >= _limits.EffectiveMaxModuleDepth) return false;

        _depth++;
        if (_depth > PeakDepth) PeakDepth = _depth;
        return true;
    }

    /// <summary>Ascends one import level after a successful <see cref="TryEnterModule"/>.</summary>
    internal void ExitModule()
    {
        if (_depth <= 0)
            throw new InvalidOperationException("Cannot exit a module depth that was not entered.");

        _depth--;
    }
}

/// <summary>
/// Factory for the structured host-resource-policy diagnostics raised by
/// <see cref="SourceProcessingLimits"/>. These are ordinary parse/front-end
/// <see cref="Diagnostic"/>s (severity <see cref="DiagnosticSeverity.Error"/>) so they surface
/// through the same <see cref="KatLangError"/> / <see cref="RunResult.ParseFailure"/> channel as
/// every other pre-evaluation error and never as an <see cref="EvalError"/>. Each message names
/// the unit (UTF-16 code units, import levels, or modules), the effective limit, and the observed
/// or requested amount; module diagnostics also carry the module URL.
/// </summary>
internal static class SourceProcessingDiagnostics
{
    internal static Diagnostic SourceLengthExceeded(int actualLength, int limit)
        => Error(
            DiagnosticCode.SourceLengthExceeded,
            $"Source length {Quantity(actualLength, "UTF-16 code unit")} exceeds the maximum of {Quantity(limit, "UTF-16 code unit")}.",
            span: null);

    internal static Diagnostic ModuleSourceLengthExceeded(string url, int actualLength, int limit, SourceSpan? span)
        => Error(
            DiagnosticCode.SourceLengthExceeded,
            $"load: source from '{url}' is {Quantity(actualLength, "UTF-16 code unit")}, over the maximum of {Quantity(limit, "UTF-16 code unit")}.",
            span);

    internal static Diagnostic ModuleImportDepthExceeded(
        string url,
        int requestedDepth,
        int limit,
        SourceSpan? span)
        => Error(
            DiagnosticCode.ModuleImportDepthExceeded,
            $"load: importing '{url}' would reach depth {requestedDepth}, over the maximum of {Quantity(limit, "nested module level")}.",
            span);

    internal static Diagnostic AggregateSourceLengthExceeded(
        string url,
        int sourceLength,
        long requestedTotal,
        long limit,
        SourceSpan? span)
        => Error(
            DiagnosticCode.AggregateSourceLengthExceeded,
            $"load: loading '{url}' ({Quantity(sourceLength, "UTF-16 code unit")}) would bring total source to {Quantity(requestedTotal, "UTF-16 code unit")}, over the maximum of {Quantity(limit, "UTF-16 code unit")}.",
            span);

    internal static Diagnostic AggregateSourceLengthExceededByProgram(int requestedLength, long limit)
        => Error(
            DiagnosticCode.AggregateSourceLengthExceeded,
            $"Program source ({Quantity(requestedLength, "UTF-16 code unit")}) exceeds the maximum total source of {Quantity(limit, "UTF-16 code unit")}.",
            span: null);

    /// <summary>
    /// A further splice of an already-loaded module does not fit the aggregate: the front end
    /// elaborates every splice, so it charges the source it adds to the program.
    /// </summary>
    internal static Diagnostic AggregateSourceLengthExceededBySplice(
        string url,
        int spliceWeight,
        long requestedTotal,
        long limit,
        SourceSpan? span)
        => Error(
            DiagnosticCode.AggregateSourceLengthExceeded,
            $"load: splicing the already loaded '{url}' again ({Quantity(spliceWeight, "UTF-16 code unit")} of elaborated module source) would bring total source to {Quantity(requestedTotal, "UTF-16 code unit")}, over the maximum of {Quantity(limit, "UTF-16 code unit")}.",
            span);

    /// <summary>
    /// The marker that ends a truncated diagnostic list (see <see cref="DiagnosticBag"/>): a fact
    /// about the list, never about a place in the source, so it has no position. Its severity is
    /// the most severe one the list dropped — an error for every diagnostic KatLang reports.
    /// </summary>
    internal static Diagnostic DiagnosticCountExceeded(int limit, DiagnosticSeverity severity)
        => new(
            $"Diagnostic limit of {Quantity(limit, "diagnostic")} reached: later diagnostics were omitted.",
            severity,
            null)
        {
            Code = DiagnosticCode.DiagnosticCountExceeded,
        };

    internal static Diagnostic ModuleCountExceeded(string url, int requestedCount, int limit, SourceSpan? span)
        => Error(
            DiagnosticCode.ModuleCountExceeded,
            $"load: loading '{url}' would be module download {requestedCount}, over the maximum of {Quantity(limit, "module download")}.",
            span);

    internal static Diagnostic ModuleNestingTooDeep(string url, int limit, SourceSpan? span)
        => Error(
            DiagnosticCode.ModuleNestingTooDeep,
            $"load: loading '{url}' at this position would nest module content deeper than the cumulative structural depth limit of {Quantity(limit, "level")}. "
            + "Move the load closer to the top level of its module, or split the module chain into smaller modules.",
            span);

    internal static Diagnostic ModuleElaborationStackExhausted(int limit)
        => Error(
            DiagnosticCode.ModuleElaborationStackExhausted,
            "Module elaboration stopped: the host thread's remaining stack cannot safely walk this composition, "
            + $"although it is within the structural depth limit of {Quantity(limit, "level")}. "
            + "Run source processing on a thread with at least the documented 1 MiB stack, or reduce structural nesting around load directives.",
            span: null);

    private static string Quantity(long value, string singular)
        => $"{value} {singular}{(value == 1 ? string.Empty : "s")}";

    // A whole-document limit (the program's own length, the aggregate budget, the
    // elaboration stack) has no position and is reported unpositioned; a module limit is
    // positioned at the load or import site the loader supplies, when it has one.
    private static Diagnostic Error(DiagnosticCode code, string message, SourceSpan? span)
        => new(message, DiagnosticSeverity.Error, span) { Code = code };
}
