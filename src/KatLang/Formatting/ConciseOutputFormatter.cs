namespace KatLang.Formatting;

/// <summary>
/// The <c>concise</c> plain-text formatter: reduces structural punctuation while staying
/// conservative and faithful.
///
/// <para>It may hide a sequence's parentheses only in locally provable safe
/// shapes: the outer sequence of one root-output block, a child sequence
/// rendered as a complete indented block hanging off a preceding single-line
/// sibling (and not adjacent to another such block), and a short flat sequence
/// occupying one entire logical line with space-separated unambiguous tokens.
/// A one-pair child sequence (<c>(neto, 1473.80)</c>) occupies one line
/// (<c>neto 1473.80</c>); a safe alternating string/value child with TWO OR
/// MORE pairs is presented as an indented pair block — one pair per line, one
/// indentation level deeper than its siblings — even when it would fit joined
/// on one line, because the indentation exposes the nested structure a flat
/// join would erase. A root pair sequence may stay flat; the pair block is a
/// child-context layout. This is structural line grouping only, never
/// dictionary, record, or field semantics. Everything else keeps canonical
/// delimiters: list brackets are ALWAYS visible, the empty sequence is ALWAYS
/// <c>()</c>, sequences inline inside lists keep their parentheses, empty and
/// singleton sequences keep theirs, and any item whose rendered text could
/// blur item boundaries (empty, whitespace-bearing, comma-bearing, or
/// ambiguous under the selected string-delimiter policy) forces the
/// parentheses back.</para>
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
/// <para>The string-delimiter policy controls string QUOTING only, never the
/// structural decisions above. Under <see cref="StringDelimiterMode.Never"/>
/// the elision safety of each string is judged on its raw content
/// (<c>neto</c>, <c>net_salary</c>, and other plain labels stay eligible for
/// delimiter removal), and a raw string whose content would need delimiters
/// (empty, whitespace, commas, <c>( ) [ ]</c>, a single quote, or
/// numeric-looking text) conservatively forces the containing sequence's
/// parentheses back rather than being quoted or altered.</para>
///
/// <para>Concise never invents punctuation or text: no colons, bullets,
/// headings, labels, or case changes — <c>neto 1473.8</c> can only contain a
/// colon if the string value itself does — and string content (including
/// every <c>_</c>) is preserved verbatim. A sequence and a list with the same
/// elements remain visibly different (<c>(1, 2)</c> may lose its parentheses
/// only where line structure carries the boundary; <c>[1, 2]</c> always keeps
/// its brackets).</para>
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
