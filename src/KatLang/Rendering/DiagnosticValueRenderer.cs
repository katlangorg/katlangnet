using System.Text;

namespace KatLang.Rendering;

/// <summary>
/// Renders one KatLang value as the bounded value fragment embedded in an evaluation
/// diagnostic (<c>operator `+` expects numeric scalar operands, but the left operand was
/// a list value with 2 elements: <b>[1, 2]</b></c>).
///
/// <para><b>Why this is bounded.</b> A value is a DAG, not a tree: <c>Wrap = [x, x]</c>
/// applied n times reaches n+1 distinct nodes through 2^n root-to-leaf paths. Diagnostic
/// rendering spells out every PATH — that is the intended textual representation, and
/// repeated occurrences must stay repeated occurrences — so rendering work and output are
/// path-proportional on a value an ordinary in-budget loop builds. No evaluation budget
/// bounds it, because the blow-up happens inside ONE message-construction step. The
/// unbounded renderer this replaced produced 10*2^depth - 4 UTF-16 units for that shape:
/// 655,356 at depth 16, and roughly 11 TB at depth 40, from a three-line program.</para>
///
/// <para><b>The bound applies during construction, never afterwards.</b> Rendering appends
/// through <see cref="BoundedDiagnosticSink"/>, which refuses the first append that would
/// cross <see cref="MaxRenderedValueLength"/>, and
/// <see cref="ValueTextRenderer.AppendValue"/> abandons the walk on the first refusal. So
/// once no further visible text can be emitted the traversal stops: work is bounded by the
/// output budget rather than by the graph, and the forbidden string is never built. This is
/// the same policy <see cref="ExprNameRenderer"/> applies to the expression-name fragment of
/// the very same messages, and it is deliberately NOT reference-identity memoization —
/// deduplicating shared nodes would change what the diagnostic says.</para>
///
/// <para><b>Grammar.</b> Structure and atom text come from the shared formatter-neutral
/// <see cref="ValueTextRenderer"/>, the same renderer canonical display uses, with the
/// diagnostic string-leaf policy (<see cref="QuotedDiagnosticStringPolicy"/>). Values whose
/// rendering fits the bound therefore render byte-identically to the former unbounded
/// formatter.</para>
/// </summary>
internal static class DiagnosticValueRenderer
{
    /// <summary>
    /// Maximum rendered value length in UTF-16 units, excluding the truncation marker.
    ///
    /// <para>Deliberately equal to <see cref="ExprNameRenderer.MaxRenderedNameLength"/>: both
    /// bound ONE fragment embedded in one evaluation diagnostic, and the two fragments
    /// routinely appear in the same message, so they answer to one policy rather than two
    /// unrelated numbers. This is not the public display ceiling
    /// (<see cref="EvaluationLimits.MaxSupportedDisplayLength"/>), which bounds a whole
    /// rendered PROGRAM OUTPUT that the user asked to see; a diagnostic quotes a value to
    /// identify it, and the enclosing message already states its kind and element count.
    /// The two constants are pinned together by <c>BoundedDiagnosticValueRenderingTests</c>.</para>
    /// </summary>
    internal const int MaxRenderedValueLength = ExprNameRenderer.MaxRenderedNameLength;

    /// <summary>The repository's established elision marker, shared with <see cref="ExprNameRenderer"/>.</summary>
    internal const string TruncationMarker = ExprNameRenderer.TruncationMarker;

    /// <summary>
    /// Canonical invariant atom text and no decimal rounding, matching the former
    /// diagnostic formatter exactly. The carried display length is never read by
    /// <see cref="ValueTextRenderer"/> — the sink owns the bound — and is set to this
    /// renderer's own cap so the record cannot be mistaken for a display configuration.
    /// </summary>
    private static readonly DisplayOptions DiagnosticDisplayOptions =
        new(Decimals: null, MaxDisplayLength: MaxRenderedValueLength);

    /// <summary>Renders one value as a bounded diagnostic fragment.</summary>
    internal static string Render(Result value) => Render(value, out _);

    /// <summary>
    /// <see cref="Render(Result)"/>, additionally reporting how many append attempts the
    /// walk made. The count is a traversal-work measure: each structural advance is preceded
    /// by a successful visible opener or separator append, and every non-empty leaf token
    /// consumes output. The one zero-length token in the grammar is an empty string payload;
    /// it is bracketed by two visible quote appends. The first overflowing visible append
    /// therefore stops both output and traversal in O(the output budget), while a walk that
    /// kept traversing with refused writes ignored would report work proportional to its input.
    ///
    /// <para>The observation is passive and belongs to this one call: it changes no output,
    /// lives on the call's own sink, and is never shared across calls or threads. The
    /// ordinary <see cref="Render(Result)"/> path runs this exact implementation.</para>
    /// </summary>
    internal static string Render(Result value, out int appendAttempts)
        => Render(value, QuotedDiagnosticStringPolicy.Instance, out appendAttempts);

    /// <summary>
    /// Renders a string value with the historic double-quoted grammar used by numeric
    /// collection-item diagnostics. This shares the same bounded sink as ordinary diagnostic
    /// values so a one-million-unit string cannot bypass the fragment policy merely because
    /// its surrounding diagnostic uses different quote punctuation.
    /// </summary>
    internal static string RenderDoubleQuotedString(string value)
        => Render(new Result.Str(value), QuotedDiagnosticStringPolicy.DoubleQuoted, out _);

    private static string Render(
        Result value,
        IStringTextPolicy stringPolicy,
        out int appendAttempts)
    {
        var sink = new BoundedDiagnosticSink(MaxRenderedValueLength);
        ValueTextRenderer.AppendValue(value, DiagnosticDisplayOptions, stringPolicy, sink);
        appendAttempts = sink.AppendAttempts;
        return sink.Finish();
    }
}

/// <summary>
/// Bounded diagnostic-fragment sink. Every append is charged its actual UTF-16 length and
/// checked BEFORE any text is stored, so an oversized fragment is never constructed and then
/// measured. An append that does not fit contributes its surrogate-safe prefix — the
/// <see cref="ExprNameRenderer"/> convention for diagnostic fragments, which keeps the
/// leading characters of an overlong string or atom visible — and then permanently refuses
/// further output, which is what stops the caller's traversal.
///
/// <para>Truncated output is NOT delimiter-balanced, matching <see cref="ExprNameRenderer"/>:
/// the single trailing marker already tells the reader the fragment is incomplete, and
/// reserving budget for pending closers would spend visible characters on punctuation. Every
/// structural advance is gated by a visible opener or separator, and the only empty token is
/// an empty string payload between two visible quotes, so refusal still bounds traversal work
/// by a small constant factor of the character budget.</para>
/// </summary>
internal sealed class BoundedDiagnosticSink(int limit) : IDisplaySink
{
    private readonly StringBuilder _builder = new();

    /// <summary>True once an append was refused; no further output is produced.</summary>
    internal bool Truncated { get; private set; }

    /// <summary>
    /// Append attempts made against this sink, including the refused ones. Passive
    /// traversal-work observation for this one rendering call; see
    /// <see cref="DiagnosticValueRenderer.Render(Result, out int)"/>.
    /// </summary>
    internal int AppendAttempts { get; private set; }

    public bool Append(string text)
    {
        AppendAttempts++;
        if (Truncated) return false;

        var room = limit - _builder.Length;
        if (text.Length <= room)
        {
            _builder.Append(text);
            return true;
        }

        _builder.Append(text, 0, ExprNameRenderer.SafePrefixLength(text, room));
        Truncated = true;
        return false;
    }

    public bool Append(char c, int count)
    {
        AppendAttempts++;
        if (Truncated) return false;

        var room = limit - _builder.Length;
        if (count <= room)
        {
            if (count > 0) _builder.Append(c, count);
            return true;
        }

        if (room > 0) _builder.Append(c, room);
        Truncated = true;
        return false;
    }

    /// <summary>The rendered fragment, with one trailing marker when anything was elided.</summary>
    internal string Finish()
        => Truncated
            ? _builder.Append(DiagnosticValueRenderer.TruncationMarker).ToString()
            : _builder.ToString();
}

/// <summary>
/// Diagnostic string-leaf policy: the ordinary instance renders every string leaf inside
/// single quotes with its content verbatim, exactly as the former diagnostic formatter
/// spelled it; the double-quoted instance preserves the historic numeric collection-item
/// diagnostic grammar. This is deliberately not the presentation formatters' conditional
/// <see cref="Formatting.DelimitedStringTextPolicy"/> — a diagnostic quotes unconditionally
/// so the value's kind is unambiguous — and it performs no escaping, so an overlong or
/// control-character-bearing string is bounded by the sink rather than by expansion here.
/// </summary>
internal sealed class QuotedDiagnosticStringPolicy : IStringTextPolicy
{
    internal static QuotedDiagnosticStringPolicy Instance { get; } = new("'");

    internal static QuotedDiagnosticStringPolicy DoubleQuoted { get; } = new("\"");

    private readonly string _delimiter;

    private QuotedDiagnosticStringPolicy(string delimiter)
    {
        _delimiter = delimiter;
    }

    public bool Append(string value, IDisplaySink sink)
        => sink.Append(_delimiter) && sink.Append(value) && sink.Append(_delimiter);
}
