namespace KatLang;

/// <summary>
/// Passive, parse-scoped observer of the parser's token-traversal work. One instance belongs to ONE
/// measured parse (<see cref="Parser.ParseSyntaxObserved"/>, or one test-only classification run,
/// <see cref="Parser.ClassifyDeclarationStartsInOrder"/>); it is never static and never ambient, so
/// a count can never leak across parses, runs, or threads, and a fresh instance starts at zero by
/// construction. The observed and unobserved parse paths share one implementation, so the AST,
/// diagnostics, and spans are identical — only these passive counts differ.
///
/// <para>Internal and excluded from every public API; the counts are a C# implementation observation
/// used only by scaling regressions (the Grace marker-run, stray-closer, and nested clause-head
/// lookahead linearity pins), with no semantic meaning.</para>
/// </summary>
internal sealed class ParserTraversalObservations
{
    /// <summary>
    /// Number of token-index steps the parse performed: one per consumed token
    /// (<c>Parser.Advance</c>) plus one per significant-token index probe
    /// (<c>Parser.NextSignificantIndex</c>, the primitive every declaration and run lookahead
    /// walks with). A lookahead that restarts from the current position for each offset — the
    /// former <c>PeekSignificant(offset)</c> loop over a k-marker Grace run — shows up here as
    /// O(k²); a single-cursor walk shows up as O(k). The clause-head delimiter-region memo
    /// (<c>Parser.TryCloseDelimiterRegion</c>) adds its own work: one step per entry read or
    /// written, and its storage work (<see cref="RegionMemoInitializationSteps"/>), so a reused
    /// or failed region is never free work here.
    /// </summary>
    public long TokenSteps => TokenVisits + RegionMemoAccessSteps + RegionMemoInitializationSteps;

    /// <summary>Consumed tokens and parser token-index probes, including recovery probes.</summary>
    public long TokenVisits { get; private set; }

    /// <summary>One step for each delimiter-region memo read or write.</summary>
    public long RegionMemoAccessSteps { get; private set; }

    /// <summary>
    /// The part of <see cref="TokenSteps"/> that prepared the clause-head delimiter-region memo's
    /// storage: one step per memo slot allocated, per used slot copied when a window widens, and
    /// per used slot cleared when the parse moves its window to a later walk
    /// (<c>Parser.PrepareRegionMemo</c>).
    /// </summary>
    public long RegionMemoInitializationSteps { get; private set; }

    /// <summary>
    /// The memo slots the parse allocated, over every window it allocated (one <c>int</c>, four
    /// bytes, per slot, array headers aside).
    /// </summary>
    public long RegionMemoAllocatedSlots { get; private set; }

    /// <summary>Messages formatted for a module holder carrying an output-spreading marker.</summary>
    public long ModuleHolderMarkerMessages { get; private set; }

    internal void Record(long tokenVisits, long regionMemoAccessSteps, long regionMemoInitializationSteps, long regionMemoAllocatedSlots, long moduleHolderMarkerMessages)
    {
        TokenVisits = tokenVisits;
        RegionMemoAccessSteps = regionMemoAccessSteps;
        RegionMemoInitializationSteps = regionMemoInitializationSteps;
        RegionMemoAllocatedSlots = regionMemoAllocatedSlots;
        ModuleHolderMarkerMessages = moduleHolderMarkerMessages;
    }
}
