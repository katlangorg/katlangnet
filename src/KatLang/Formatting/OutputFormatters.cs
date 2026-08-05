using System.Collections.Frozen;
using System.Diagnostics.CodeAnalysis;

namespace KatLang.Formatting;

/// <summary>
/// The immutable registry of built-in KatLang output formatters.
///
/// <para>Stable ids (lowercase, suitable for persistence by external
/// applications): <c>exact</c> — canonical display, byte-identical to
/// <see cref="RunResult.ToDisplayString"/>; <c>readable</c> — structurally
/// faithful pretty-printer (every delimiter preserved, layout improved);
/// <c>concise</c> — conservative layout that hides only provably safe
/// sequence parentheses. Lookup uses ORDINAL, case-sensitive comparison, and
/// unknown ids deterministically fall back to <see cref="Exact"/> unless the
/// caller supplies another fallback.</para>
///
/// <para>The built-in instances are stateless and freely shared across
/// threads. The registry is fixed: there is no mutable global registration —
/// applications wanting additional formatters compose their own registry of
/// <see cref="OutputFormatter"/> instances. Localized display names, selector
/// UI, and persisted user preferences belong to consuming applications, not
/// to this package.</para>
/// </summary>
public static class OutputFormatters
{
    // This is the single built-in registration point. A future formatter is
    // implemented in its own class and added here; lookup and enumeration are
    // derived from the same immutable data.
    private static readonly IReadOnlyList<OutputFormatter> BuiltIns =
        Array.AsReadOnly<OutputFormatter>(
        [
            new ExactOutputFormatter(),
            new ReadableOutputFormatter(),
            new ConciseOutputFormatter(),
        ]);

    private static readonly FrozenDictionary<string, OutputFormatter> BuiltInsById =
        BuiltIns.ToFrozenDictionary(formatter => formatter.Id, StringComparer.Ordinal);

    /// <summary>The canonical formatter, id <c>exact</c>.</summary>
    public static OutputFormatter Exact => BuiltInsById["exact"];

    /// <summary>The structure-preserving pretty-printer, id <c>readable</c>.</summary>
    public static OutputFormatter Readable => BuiltInsById["readable"];

    /// <summary>The conservative low-punctuation formatter, id <c>concise</c>.</summary>
    public static OutputFormatter Concise => BuiltInsById["concise"];

    /// <summary>
    /// All built-in formatters in deterministic order:
    /// <c>exact</c>, <c>readable</c>, <c>concise</c>.
    /// </summary>
    public static IReadOnlyList<OutputFormatter> All => BuiltIns;

    /// <summary>
    /// Looks up a built-in formatter by its stable id using ordinal,
    /// case-sensitive comparison. Null and unknown ids return false.
    /// </summary>
    public static bool TryGet(string? id, [NotNullWhen(true)] out OutputFormatter? formatter)
    {
        if (id is not null && BuiltInsById.TryGetValue(id, out var found))
        {
            formatter = found;
            return true;
        }

        formatter = null;
        return false;
    }

    /// <summary>
    /// Returns the built-in formatter with the given id, or <see cref="Exact"/>
    /// for null and unknown ids — the guaranteed safe fallback for persisted
    /// preferences that no longer resolve.
    /// </summary>
    public static OutputFormatter GetOrDefault(string? id)
        => GetOrDefault(id, Exact);

    /// <summary>
    /// Returns the built-in formatter with the given id, or the supplied
    /// fallback for null and unknown ids.
    /// </summary>
    public static OutputFormatter GetOrDefault(string? id, OutputFormatter fallback)
    {
        ArgumentNullException.ThrowIfNull(fallback);
        return TryGet(id, out var formatter) ? formatter : fallback;
    }
}
