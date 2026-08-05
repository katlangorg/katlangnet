namespace KatLang.Formatting;

/// <summary>
/// The <c>exact</c> formatter: canonical KatLang display. This is a thin
/// façade over the SAME internal rendering used by
/// <see cref="RunResult.ToDisplayString"/> — one implementation, two entry
/// points — so its output is byte-for-byte identical to canonical display:
/// platform newline row separators, canonical sequence and list punctuation,
/// culture-invariant numbers, <c>DisplayDecimals</c>, raw unquoted strings
/// (every character preserved verbatim, including <c>_</c>), and the shared
/// bounded overflow behavior.
///
/// <para>Layout and string-delimiter options are deliberately ignored:
/// canonical output is not configurable. Only the option's display-length
/// restriction applies (it can lower the limit, never raise it).</para>
/// </summary>
internal sealed class ExactOutputFormatter : OutputFormatter
{
    public override string Id => "exact";

    protected override bool WriteSuccessOutput(
        IReadOnlyList<Result> outputRows,
        OutputFormattingOptions options,
        BoundedOutputWriter writer)
        => RunResult.AppendSuccessRows(outputRows, writer.DisplayOptions, writer.Core);
}
