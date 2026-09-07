namespace KatLang;

/// <summary>
/// Passive, parse-scoped observer of the parser's token-traversal work. One instance belongs to ONE
/// measured parse (<see cref="Parser.ParseSyntaxObserved"/>); it is never static and never ambient, so
/// a count can never leak across parses, runs, or threads, and a fresh instance starts at zero by
/// construction. The observed and unobserved parse paths share one implementation, so the AST,
/// diagnostics, and spans are identical — only this passive count differs.
///
/// <para>Internal and excluded from every public API; the count is a C# implementation observation
/// used only by scaling regressions (the Grace marker-run linearity pins), with no semantic meaning.</para>
/// </summary>
internal sealed class ParserTraversalObservations
{
    /// <summary>
    /// Number of token-index steps the parse performed: one per consumed token
    /// (<c>Parser.Advance</c>) plus one per significant-token index probe
    /// (<c>Parser.NextSignificantIndex</c>, the primitive every declaration and run lookahead
    /// walks with). A lookahead that restarts from the current position for each offset — the
    /// former <c>PeekSignificant(offset)</c> loop over a k-marker Grace run — shows up here as
    /// O(k²); a single-cursor walk shows up as O(k).
    /// </summary>
    public long TokenSteps { get; private set; }

    internal void RecordTokenSteps(long tokenSteps) => TokenSteps = tokenSteps;
}
