namespace KatLang.Formatting;

/// <summary>
/// The <c>readable</c> plain-text formatter: a structurally faithful pretty-printer.
///
/// <para>Every sequence parenthesis, every list bracket, <c>()</c>, and
/// <c>[]</c> stay visible; root-output boundaries, item order, and string
/// content are preserved exactly. What changes is layout only: structurally
/// simple values that fit the preferred line width render inline in canonical
/// punctuation, while larger OR structurally complex values break into
/// indented multiline form (opening delimiter, one item per line with
/// canonical comma separators, closing delimiter on its own line). Width is
/// necessary but not sufficient for inline layout — a sequence with two or
/// more structured children lays out multiline even when its flat text fits,
/// and a nested multi-pair string/value child renders one pair per line, so
/// nested structure stays visible. Independently emitted root outputs are
/// separated by configurable blank lines so programs need not emit <c>''</c>
/// rows for spacing.</para>
///
/// <para>String quoting follows
/// <see cref="OutputFormattingOptions.StringDelimiters"/>; under
/// <see cref="StringDelimiterMode.Never"/> an explicitly emitted empty-string
/// row renders as a visually blank line (use
/// <see cref="StringDelimiterMode.WhenNeeded"/> to keep it visible as
/// <c>''</c>, distinct from formatter-added spacing).</para>
/// </summary>
internal sealed class ReadableOutputFormatter : OutputFormatter
{
    public override string Id => "readable";

    protected override bool WriteSuccessOutput(
        IReadOnlyList<Result> outputRows,
        OutputFormattingOptions options,
        BoundedOutputWriter writer)
        => StructuredLayoutRenderer.WriteRows(
            outputRows,
            writer.DisplayOptions,
            options,
            concise: false,
            writer.Core);
}
