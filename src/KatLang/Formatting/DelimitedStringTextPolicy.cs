using System.Buffers;
using System.Globalization;
using KatLang.Rendering;

namespace KatLang.Formatting;

/// <summary>
/// String-leaf presentation shared by Readable and Concise, and the string
/// CLASSIFIER their layout decisions consult.
///
/// <para>One instance belongs to exactly one rendering call (a layout session),
/// so its classification cache and work budget are per call: nothing is
/// global, nothing is shared between concurrent renderings, and every cached
/// string reference is released with the session.</para>
///
/// <para>Classification work is bounded (security finding F4). A layout
/// decision may consult the same immutable string once per reference to it,
/// and before the bounded writer has any chance to refuse output, so an
/// unbounded classifier would cost <c>references × length</c>. Strings shorter
/// than <see cref="LongStringLength"/> are classified directly — their cost is
/// a small constant per visit, like the visit itself. A LONG string is
/// classified at most once per cache entry: the facts are cached by STRING
/// REFERENCE identity (never by content — a content hash would rescan the
/// string on every lookup), in a cache of at most
/// <see cref="FactsCacheCapacity"/> entries, and every uncached
/// classification first charges the string's length against a per-call
/// budget of <see cref="ClassificationBaseAllowance"/> plus
/// <see cref="ClassificationLimitMultiplier"/> code units per unit of the
/// effective display limit. A classification the budget cannot pay for is NOT
/// performed and reports "not classified" — never "safe" — and from then on the
/// classifier is <see cref="ClassificationExhausted"/>: cached facts still
/// answer, every other long string stays unclassified without being scanned.
/// The sum of long classification input lengths is therefore bounded by the budget,
/// independent of how many times or in how many distinct strings the content
/// is referenced. Each classification performs a fixed number of linear
/// passes, so actual character-inspection work is a constant multiple of that
/// allowance, rather than one inspection per charged code unit.</para>
///
/// <para>EMISSION is exact and never budgeted: quoting decides what the
/// output text IS, so <see cref="Append"/> always computes it — but a leaf
/// whose raw length already exceeds the sink's remaining capacity is refused
/// before any scan (quotes only add length), so emission scanning stays within
/// the output the sink actually accepts. Width MEASUREMENT
/// (<see cref="Measurement"/>) is a layout decision: it uses the budgeted
/// classifier and reports "does not fit" for an unclassified string, the
/// conservative answer for every layout that asks.</para>
/// </summary>
internal sealed class DelimitedStringTextPolicy : IStringTextPolicy
{
    /// <summary>Strings at least this long are cached and charged; shorter ones are classified directly.</summary>
    internal const int LongStringLength = 64;

    /// <summary>Maximum cached long strings per rendering call (matches the layout predicate caches).</summary>
    internal const int FactsCacheCapacity = 64;

    /// <summary>Classification allowance every rendering call receives, in UTF-16 code units.</summary>
    internal const long ClassificationBaseAllowance = 4_000_000;

    /// <summary>Additional classification allowance per code unit of the effective display limit.</summary>
    internal const long ClassificationLimitMultiplier = 16;

    private static readonly SearchValues<char> UnquotableChars = SearchValues.Create("'\n\r");

    // The five characters that terminate a visual line: CR, LF, and the
    // Unicode layout separators NEL (U+0085), LINE SEPARATOR (U+2028),
    // and PARAGRAPH SEPARATOR (U+2029). Deliberately NOT general Unicode
    // whitespace — ordinary spaces and tabs stay on one visual line.
    private static readonly SearchValues<char> LineBreakChars =
        SearchValues.Create("\r\n\u0085\u2028\u2029");

    private readonly StringDelimiterMode _mode;
    private Dictionary<string, StringFacts>? _cache;
    private long _budget;

    public DelimitedStringTextPolicy(StringDelimiterMode mode, long classificationBudget)
    {
        _mode = mode;
        ClassificationBudget = Math.Max(classificationBudget, 0);
        _budget = ClassificationBudget;
        Measurement = new MeasuringView(this);
    }

    /// <summary>
    /// The classification allowance of one rendering call under
    /// <paramref name="displayLimit"/>: a fixed base plus a multiple of the
    /// limit (at most 20,000,000 code units under the supported ceiling).
    /// </summary>
    internal static long DefaultClassificationBudget(int displayLimit)
        => ClassificationBaseAllowance + ClassificationLimitMultiplier * Math.Max(displayLimit, 0);

    /// <summary>This rendering call's total classification allowance, in UTF-16 code units.</summary>
    internal long ClassificationBudget { get; }

    /// <summary>The width-measurement face of this policy (budgeted; unclassified means "does not fit").</summary>
    internal IStringTextPolicy Measurement { get; }

    /// <summary>
    /// True once a long-string classification was refused for lack of budget.
    /// From then on only cached facts answer, so every later answer for the
    /// same string is the same — a renderer that saw this flip during a row
    /// re-renders that row against the now-stable classifier.
    /// </summary>
    internal bool ClassificationExhausted { get; private set; }

    /// <summary>Code units charged against the classification budget.</summary>
    internal long ChargedCodeUnits { get; private set; }

    /// <summary>
    /// Sum of input lengths passed to classification or quoting computations
    /// (short strings included). Counts each input once even when the original
    /// predicates make several linear passes; this is not a count of inspected
    /// characters. Cache hits and raw-length refusals contribute nothing.
    /// </summary>
    internal long ScanInputCodeUnits { get; private set; }

    /// <summary>Long-string classifications actually performed.</summary>
    internal long LongClassifications { get; private set; }

    /// <summary>Long-string classifications answered from the identity cache.</summary>
    internal long CacheHits { get; private set; }

    /// <summary>Classification requests answered "not classified within budget".</summary>
    internal long UnclassifiedResults { get; private set; }

    /// <summary>Leaves refused by a sink on raw length alone, without a content scan.</summary>
    internal long LengthRefusals { get; private set; }

    /// <summary>Exact emission: quoting is always decided, never budgeted.</summary>
    public bool Append(string value, IDisplaySink sink)
    {
        if (sink is ICapacityDisplaySink bounded && value.Length > bounded.RemainingCapacity)
        {
            // The raw text alone cannot fit; let the sink record the refusal.
            LengthRefusals++;
            return sink.Append(value);
        }

        bool usesDelimiters;
        if (value.Length >= LongStringLength && _cache is not null && _cache.TryGetValue(value, out var cached))
        {
            CacheHits++;
            usesDelimiters = cached.UsesDelimiters;
        }
        else
        {
            ScanInputCodeUnits += value.Length;
            usesDelimiters = UsesDelimiters(value);
        }

        return AppendToken(value, usesDelimiters, sink);
    }

    /// <summary>
    /// Classifies one string: false when the classification could not be
    /// performed within the budget — which every caller must treat as
    /// "not established", never as safe.
    /// </summary>
    internal bool TryClassify(string value, out StringFacts facts)
    {
        if (value.Length < LongStringLength)
        {
            ScanInputCodeUnits += value.Length;
            facts = Compute(value);
            return true;
        }

        if (_cache is not null && _cache.TryGetValue(value, out facts))
        {
            CacheHits++;
            return true;
        }

        if (ClassificationExhausted || value.Length > _budget)
        {
            ClassificationExhausted = true;
            UnclassifiedResults++;
            facts = default;
            return false;
        }

        _budget -= value.Length;
        ChargedCodeUnits += value.Length;
        ScanInputCodeUnits += value.Length;
        LongClassifications++;
        facts = Compute(value);

        _cache ??= new Dictionary<string, StringFacts>(ReferenceEqualityComparer.Instance);
        if (_cache.Count < FactsCacheCapacity)
            _cache.TryAdd(value, facts);
        return true;
    }

    private bool AppendMeasured(string value, IDisplaySink sink)
    {
        if (sink is ICapacityDisplaySink bounded && value.Length > bounded.RemainingCapacity)
        {
            LengthRefusals++;
            return sink.Append(value);
        }

        if (value.Length < LongStringLength)
        {
            // Short strings need only the quoting decision here, exactly as
            // emission computes it.
            ScanInputCodeUnits += value.Length;
            return AppendToken(value, UsesDelimiters(value), sink);
        }

        // Unclassified within budget: conservatively "does not fit".
        return TryClassify(value, out var facts) && AppendToken(value, facts.UsesDelimiters, sink);
    }

    private static bool AppendToken(string value, bool usesDelimiters, IDisplaySink sink)
    {
        if (!usesDelimiters)
            return sink.Append(value);

        return sink.Append("'") && sink.Append(value) && sink.Append("'");
    }

    /// <summary>
    /// Every fact the layout needs about one string, computed by the original
    /// predicates (a constant number of linear passes), so a cached answer is
    /// exactly the answer a fresh computation would give for this mode.
    /// </summary>
    private StringFacts Compute(string value)
    {
        var needsDelimiters = NeedsDelimiters(value);
        var canDelimit = CanDelimitFaithfully(value);
        var usesDelimiters = _mode switch
        {
            StringDelimiterMode.Always => canDelimit,
            StringDelimiterMode.WhenNeeded => needsDelimiters && canDelimit,
            _ => false,
        };

        return new StringFacts(
            usesDelimiters ? (long)value.Length + 2 : value.Length,
            usesDelimiters,
            IsTokenSafe(value, needsDelimiters, canDelimit, usesDelimiters),
            value.AsSpan().ContainsAny(LineBreakChars));
    }

    /// <summary>
    /// Whether this string can stand as ONE safe Concise token in a layout
    /// that removed the surrounding sequence punctuation — text that cannot be
    /// confused with a separator, a neighbouring token, structural
    /// punctuation, or canonical atom output. This is a per-value structural
    /// decision, deliberately separate from the quoting policy itself: the
    /// delimiter mode only changes WHAT the rendered token is, and safety is
    /// judged on that exact token.
    ///
    /// <para>Under <see cref="StringDelimiterMode.Never"/> the token is the
    /// raw content, so it is safe exactly when the content would never need
    /// delimiters: non-empty, no whitespace or control characters, none of
    /// <c>, ( ) [ ] '</c>, no invisible Unicode format characters or unpaired
    /// surrogates, and not numeric-looking. Ordinary labels such as
    /// <c>neto</c> or <c>net_salary</c> are safe; ambiguous raw strings make
    /// the CONTAINING sequence keep its parentheses instead of being quoted
    /// (<c>Never</c> forbids added delimiters) or altered.</para>
    ///
    /// <para>Under the quoting modes a delimited token is self-bounding, so
    /// only content that still blurs line/join boundaries (whitespace,
    /// control characters, commas, invisible format characters, unpaired
    /// surrogates) or that needs delimiters it cannot faithfully receive
    /// remains unsafe. The scan is early-exit and never copies the string;
    /// measurement and emission share the same quoting decision, so they
    /// cannot disagree.</para>
    /// </summary>
    private bool IsTokenSafe(string value, bool needsDelimiters, bool canDelimit, bool usesDelimiters)
    {
        if (_mode == StringDelimiterMode.Never)
            return !needsDelimiters;

        if (value.Length == 0)
            return usesDelimiters;

        if (needsDelimiters && !canDelimit)
            return false;

        for (var i = 0; i < value.Length; i++)
        {
            var c = value[i];
            if (char.IsWhiteSpace(c) || char.IsControl(c) || c == ',')
                return false;
            if (char.IsSurrogate(c))
            {
                // A well-formed surrogate pair is ordinary content (emoji and
                // other supplementary characters); an UNPAIRED surrogate is
                // invalid text that must stay delimited.
                if (char.IsHighSurrogate(c) && i + 1 < value.Length && char.IsLowSurrogate(value[i + 1]))
                {
                    i++;
                    continue;
                }

                return false;
            }

            if (char.GetUnicodeCategory(c) == UnicodeCategory.Format)
                return false;
        }

        return true;
    }

    private bool UsesDelimiters(string value) => _mode switch
    {
        StringDelimiterMode.Always => CanDelimitFaithfully(value),
        StringDelimiterMode.WhenNeeded => NeedsDelimiters(value) && CanDelimitFaithfully(value),
        _ => false,
    };

    private static bool CanDelimitFaithfully(string value)
        => !value.AsSpan().ContainsAny(UnquotableChars);

    private static bool NeedsDelimiters(string value)
    {
        if (value.Length == 0)
            return true;

        for (var i = 0; i < value.Length; i++)
        {
            var c = value[i];
            if (char.IsWhiteSpace(c) || char.IsControl(c))
                return true;
            if (c is ',' or '(' or ')' or '[' or ']' or '\'')
                return true;
            if (char.IsSurrogate(c))
            {
                // A well-formed surrogate pair is ordinary content; an UNPAIRED
                // surrogate is invalid text that needs delimiting.
                if (char.IsHighSurrogate(c) && i + 1 < value.Length && char.IsLowSurrogate(value[i + 1]))
                {
                    i++;
                    continue;
                }

                return true;
            }

            // Unicode format characters (bidi controls, zero-width spaces,
            // BOM/ZWNBSP, soft hyphen, word joiner, ...) are invisible or
            // visually reordering: raw content containing them must never
            // stand as an undelimited token.
            if (char.GetUnicodeCategory(c) == UnicodeCategory.Format)
                return true;
        }

        return LooksNumeric(value) || IsNonFiniteAtomSpelling(value);
    }

    /// <summary>
    /// The three canonical spellings a non-finite ATOM renders as (<c>NaN</c>,
    /// <c>Infinity</c>, <c>-Infinity</c> — <c>ValueTextRenderer.FormatNumberInvariant</c>
    /// keeps the runtime's literal spellings for them): raw string content equal to one
    /// of them would be indistinguishable from the atom, exactly the confusion the
    /// numeric-looking rule exists to prevent. Case-sensitive: <c>nan</c> is ordinary
    /// text, because the atom never renders that way.
    /// </summary>
    private static bool IsNonFiniteAtomSpelling(string value)
        => value is "NaN" or "Infinity" or "-Infinity";

    private static bool LooksNumeric(string value)
    {
        // Syntax recognition, not numeric conversion: overflow-sized and
        // exponent-form text is still visually numeric and should stay
        // distinguishable from atom output. ASCII digits are intentional
        // because canonical invariant atom text uses ASCII digits. Underscore
        // digit separators are recognized between digits because that is
        // KatLang's number-literal grammar (the lexer's ScanDigits rule), so
        // raw text such as `1_000` reads as a number and stays delimited.
        var span = value.AsSpan();
        var i = 0;
        if (i < span.Length && span[i] is '+' or '-') i++;

        var integralDigits = ScanDigitRun(span, ref i);

        var fractionalDigits = 0;
        if (i < span.Length && span[i] == '.')
        {
            i++;
            fractionalDigits = ScanDigitRun(span, ref i);
        }

        if (integralDigits + fractionalDigits == 0) return false;
        if (i < span.Length && span[i] is 'e' or 'E')
        {
            i++;
            if (i < span.Length && span[i] is '+' or '-') i++;
            if (ScanDigitRun(span, ref i) == 0) return false;
        }

        return i == span.Length;
    }

    /// <summary>
    /// Consumes one run of ASCII digits allowing underscore separators only
    /// BETWEEN digits (mirroring the lexer's digit-separator rule: a run of
    /// underscores is consumed only when a digit follows), and returns the
    /// digit count. The run must START with a digit — a leading underscore is
    /// identifier syntax in KatLang, never number syntax.
    /// </summary>
    private static int ScanDigitRun(ReadOnlySpan<char> span, ref int i)
    {
        var digits = 0;
        while (i < span.Length)
        {
            if (span[i] is >= '0' and <= '9')
            {
                digits++;
                i++;
                continue;
            }

            if (digits > 0 && span[i] == '_')
            {
                var afterUnderscores = i;
                while (afterUnderscores < span.Length && span[afterUnderscores] == '_')
                    afterUnderscores++;

                if (afterUnderscores < span.Length && span[afterUnderscores] is >= '0' and <= '9')
                {
                    i = afterUnderscores;
                    continue;
                }
            }

            break;
        }

        return digits;
    }

    /// <summary>Immutable classification facts of one string under this policy's mode.</summary>
    internal readonly record struct StringFacts(
        long TokenLength,
        bool UsesDelimiters,
        bool IsTokenSafe,
        bool ContainsLineBreak);

    private sealed class MeasuringView(DelimitedStringTextPolicy owner) : IStringTextPolicy
    {
        public bool Append(string value, IDisplaySink sink) => owner.AppendMeasured(value, sink);
    }
}
