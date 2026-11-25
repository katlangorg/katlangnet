namespace KatLang.Formatting;

/// <summary>
/// Immutable per-call options for the output formatters.
///
/// <para>Options are presentation policy only: they can never change which
/// values are rendered, their order, their structure kinds, or any string
/// content. The <c>exact</c> formatter ignores every layout option here
/// (canonical output is not configurable); it honors only
/// <see cref="MaxDisplayLength"/>, which can LOWER the run's effective
/// display-length limit but never raise it.</para>
///
/// <para>Following <see cref="EvaluationLimits"/> conventions, invalid values
/// throw at initialization and values above a supported maximum are clamped
/// down (so raising a request can never create unreasonable intermediate
/// work). Instances are immutable and safe to share across calls and threads;
/// there is no mutable process-wide default.</para>
/// </summary>
public sealed record OutputFormattingOptions
{
    /// <summary>Supported ceiling for <see cref="PreferredLineWidth"/>; larger requests are clamped down.</summary>
    public const int MaxSupportedPreferredLineWidth = 10_000;

    /// <summary>Supported ceiling for <see cref="IndentSize"/>; larger requests are clamped down.</summary>
    public const int MaxSupportedIndentSize = 64;

    /// <summary>Supported ceiling for <see cref="RootOutputSpacing"/>; larger requests are clamped down.</summary>
    public const int MaxSupportedRootOutputSpacing = 64;

    /// <summary>Shared default options instance.</summary>
    public static OutputFormattingOptions Default { get; } = new();

    private readonly int _preferredLineWidth = 100;
    private readonly int _indentSize = 2;
    private readonly string _newLine = Environment.NewLine;
    private readonly int _rootOutputSpacing = 1;
    private readonly int? _maxDisplayLength;
    private readonly StringDelimiterMode _stringDelimiters = StringDelimiterMode.WhenNeeded;

    /// <summary>
    /// Preferred maximum line width, in UTF-16 code units, used by the layout
    /// formatters to choose between inline and multiline rendering. A single
    /// leaf value longer than the width still renders on one line — formatters
    /// never invent line breaks inside a value. Default 100.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is zero or negative.</exception>
    public int PreferredLineWidth
    {
        get => _preferredLineWidth;
        init
        {
            if (value < 1)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(PreferredLineWidth), value, "Preferred line width must be at least 1.");
            }

            _preferredLineWidth = Math.Min(value, MaxSupportedPreferredLineWidth);
        }
    }

    /// <summary>Spaces per indentation level in multiline layouts. Default 2.</summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is negative.</exception>
    public int IndentSize
    {
        get => _indentSize;
        init
        {
            if (value < 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(IndentSize), value, "Indent size cannot be negative.");
            }

            _indentSize = Math.Min(value, MaxSupportedIndentSize);
        }
    }

    /// <summary>
    /// Line separator emitted by the layout formatters (structural line
    /// breaks, row separators, and blank root-spacing lines). Every emitted
    /// occurrence is charged its actual UTF-16 length against the display
    /// limit. Default <see cref="Environment.NewLine"/>. The <c>exact</c>
    /// formatter always uses the canonical platform newline.
    /// </summary>
    /// <exception cref="ArgumentNullException">The value is null.</exception>
    /// <exception cref="ArgumentException">The value is empty.</exception>
    public string NewLine
    {
        get => _newLine;
        init
        {
            ArgumentNullException.ThrowIfNull(value);
            if (value.Length == 0)
                throw new ArgumentException("Newline sequence cannot be empty.", nameof(NewLine));
            _newLine = value;
        }
    }

    /// <summary>
    /// Number of blank lines the layout formatters place between adjacent
    /// root-output blocks, so independently emitted root outputs stay visually
    /// distinct without programs emitting <c>''</c> rows for spacing. Default
    /// 1; 0 separates rows by a single line break like canonical display.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is negative.</exception>
    public int RootOutputSpacing
    {
        get => _rootOutputSpacing;
        init
        {
            if (value < 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(RootOutputSpacing), value, "Root output spacing cannot be negative.");
            }

            _rootOutputSpacing = Math.Min(value, MaxSupportedRootOutputSpacing);
        }
    }

    /// <summary>
    /// Optional per-call display-length limit, in UTF-16 code units. Values
    /// above <see cref="EvaluationLimits.MaxSupportedDisplayLength"/> are
    /// clamped to that ceiling. The
    /// effective limit of a formatting call is the SMALLER of this value and
    /// the evaluated run's own display limit — a caller can restrict output
    /// further but can never raise or bypass the run's limit. Null (the
    /// default) uses the run's limit unchanged.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is negative.</exception>
    public int? MaxDisplayLength
    {
        get => _maxDisplayLength;
        init
        {
            if (value is < 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxDisplayLength), value, "Display length limit cannot be negative.");
            }

            _maxDisplayLength = value is { } requested
                ? Math.Min(requested, EvaluationLimits.MaxSupportedDisplayLength)
                : null;
        }
    }

    /// <summary>
    /// String-delimiter policy for the layout formatters. Default
    /// <see cref="StringDelimiterMode.WhenNeeded"/>. Ignored by <c>exact</c>,
    /// which always renders canonical raw strings.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is not a defined policy.</exception>
    public StringDelimiterMode StringDelimiters
    {
        get => _stringDelimiters;
        init
        {
            if (value is not (StringDelimiterMode.Never or StringDelimiterMode.WhenNeeded or StringDelimiterMode.Always))
            {
                throw new ArgumentOutOfRangeException(
                    nameof(StringDelimiters), value, "Unknown string-delimiter mode.");
            }

            _stringDelimiters = value;
        }
    }

    /// <summary>
    /// The display limit actually enforced for one formatting call: the run's
    /// own limit, lowered — never raised — by <see cref="MaxDisplayLength"/>.
    /// </summary>
    internal int EffectiveDisplayLimit(int runDisplayLimit)
        => _maxDisplayLength is { } configured && configured < runDisplayLimit
            ? configured
            : runDisplayLimit;
}
