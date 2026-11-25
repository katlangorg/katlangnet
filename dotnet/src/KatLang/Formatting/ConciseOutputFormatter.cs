namespace KatLang.Formatting;

/// <summary>
/// The <c>concise</c> plain-text formatter uses spaces, lines, and indentation
/// in place of sequence punctuation where the layout permits.
///
/// <para>A flat sequence of scalars can occupy one line with space separators.
/// A nested sequence of two or more string/value pairs can use an indented
/// block with one pair per line. A string can use these layouts if its rendered
/// text fits on the line. Any quotes count toward the width. Spacing and
/// punctuation within a string are preserved. For example, <c>('social tax', 3)</c>
/// renders as <c>social tax 3</c> under <c>Never</c> and <c>'social tax' 3</c>
/// under the quoting modes.</para>
///
/// <para>Width alone never forces a structurally complex value flat: a
/// sequence with two or more structured children lays out as a block or
/// delimited multiline form even when its canonical flat text fits the
/// preferred width, so natural structured results need no spread operator for
/// readable presentation (spread DISCARDS the parent structure, and the
/// formatter never reconstructs it heuristically).</para>
///
/// <para>Zero root-output spacing allows a paren-hidden root block only when a
/// nested pair block visibly anchors it (indentation no independent root row
/// can begin with); otherwise the root parentheses stay so one root sequence
/// can never be confused with several root rows. Zero indentation retains
/// parentheses around multiline child sequences, because there line layout
/// alone cannot carry the erased boundary.</para>
///
/// <para>Lists keep their brackets, empty and singleton sequences keep their
/// parentheses, and sequences inside lists keep their delimiters.</para>
/// </summary>
internal sealed class ConciseOutputFormatter : OutputFormatter
{
    public override string Id => "concise";

    protected override bool WriteSuccessOutput(
        IReadOnlyList<Result> outputRows,
        OutputFormattingOptions options,
        BoundedOutputWriter writer)
        => StructuredLayoutRenderer.WriteRows(
            outputRows,
            writer.DisplayOptions,
            options,
            concise: true,
            writer.Core);
}
