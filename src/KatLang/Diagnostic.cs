namespace KatLang;

/// <summary>
/// Severity of a <see cref="Diagnostic"/>. Only <see cref="Error"/> blocks: an error
/// diagnostic makes <see cref="ParseResult.HasErrors"/> true and stops every source-based
/// entry point before evaluation.
/// <para>The numeric values are stable and deliberately equal to the Monaco editor's marker
/// severities (Hint 1, Info 2, Warning 4, Error 8), so an editor integration can pass
/// <c>(int)severity</c> through unchanged. There is no zero member: <c>default</c> is not a
/// valid severity.</para>
/// </summary>
public enum DiagnosticSeverity
{
    /// <summary>A hint; never blocks.</summary>
    Hint = 1,

    /// <summary>Information; never blocks.</summary>
    Info = 2,

    /// <summary>A warning; never blocks.</summary>
    Warning = 4,

    /// <summary>An error; blocks evaluation of the source.</summary>
    Error = 8,
}

/// <summary>
/// A single diagnostic message produced during lexing, parsing, or front-end elaboration.
/// <see cref="Span"/> is the diagnostic's location in the document whose result carries it —
/// the half-open <see cref="SourceSpan"/> of the offending text, an empty span at an
/// insertion point (end of input, a missing token) — or <see langword="null"/> for a
/// diagnostic that has no position at all: a whole-document limit (source length, aggregate
/// module budget, elaboration stack), or a fact about content that has no location in this
/// document and no import site to report at. A missing location is never spelled as a
/// sentinel coordinate.
/// </summary>
public sealed record Diagnostic(
    string Message,
    DiagnosticSeverity Severity,
    SourceSpan? Span)
{
    /// <summary>The diagnostic data; replacing it discards the previous formatter's layout.</summary>
    public string Message
    {
        get;
        init
        {
            field = value;
            _lineBreakOffsets = default;
        }
    } = Message;

    // Declare the positional properties in their original order to preserve record printing.
    /// <summary>The severity that determines whether this diagnostic blocks execution.</summary>
    public DiagnosticSeverity Severity { get; init; } = Severity;

    /// <summary>The diagnostic's location, or null when it has no position.</summary>
    public SourceSpan? Span { get; init; } = Span;

    // Presentation provenance is equality-transparent, like the runtime metadata on AST
    // records. Only KatLang's prefix truncation keeps offsets when replacing Message;
    // a host's `with { Message = ... }` must not transplant them onto unrelated text.
    private readonly RuntimeStateSlot<IReadOnlyList<int>?> _lineBreakOffsets;

    internal Diagnostic(DiagnosticMessage message, DiagnosticSeverity severity, SourceSpan? span)
        : this(message.Text, severity, span)
        => _lineBreakOffsets = new(message.LineBreakOffsets);

    private Diagnostic(Diagnostic original, int prefixLength)
        : this(original)
    {
        Message = string.Concat(original.Message.AsSpan(0, prefixLength), ExprNameRenderer.TruncationMarker);
        _lineBreakOffsets = original._lineBreakOffsets;
    }

    /// <summary>Retains only the unchanged, surrogate-safe prefix and its original layout.</summary>
    internal Diagnostic WithBoundedMessage(int maxLength)
        => Message.Length <= maxLength ? this
            : new(this, ExprNameRenderer.SafePrefixLength(Message, maxLength));

    internal string RenderMessage(Func<string, string> renderFragment)
    {
        if (_lineBreakOffsets.Value is not { Count: > 0 } offsets)
            return renderFragment(Message);

        System.Text.StringBuilder? builder = null;
        var start = 0;
        foreach (var offset in offsets)
        {
            if (offset < start || offset > Message.Length - Environment.NewLine.Length
                || !Message.AsSpan(offset, Environment.NewLine.Length).SequenceEqual(Environment.NewLine))
                break;

            builder ??= new System.Text.StringBuilder();
            builder.Append(renderFragment(Message[start..offset])).Append(Environment.NewLine);
            start = offset + Environment.NewLine.Length;
        }

        return builder is null ? renderFragment(Message)
            : builder.Append(renderFragment(Message[start..])).ToString();
    }

    /// <summary>
    /// Stable machine-readable identity of the diagnostic's semantic family —
    /// the supported classification channel (<see cref="Message"/> remains
    /// human-readable presentation only). Every diagnostic produced by KatLang
    /// itself carries a deliberate non-default code; only externally
    /// constructed diagnostics default to <see cref="DiagnosticCode.Unspecified"/>.
    ///
    /// <para>The code is part of the diagnostic's record identity: it
    /// participates in value equality, hashing, and the synthesized
    /// <c>ToString</c>, and <c>with</c> copies preserve it. The positional
    /// constructor and <c>Deconstruct</c> shapes are unchanged (the code is
    /// init-only, not positional).</para>
    /// </summary>
    public DiagnosticCode Code { get; init; } = DiagnosticCode.Unspecified;
}

/// <summary>
/// A front-end explanation and its repair are separate fragments. Keep the separators'
/// provenance when joining them; raw newlines in either fragment remain untrusted.
/// </summary>
internal readonly record struct DiagnosticMessage(string Text, IReadOnlyList<int> LineBreakOffsets)
{
    internal static DiagnosticMessage JoinLines(string first, string second)
        => new(first + Environment.NewLine + second, [first.Length]);

    internal static DiagnosticMessage JoinLines(IReadOnlyList<string> lines)
    {
        var offsets = new int[Math.Max(0, lines.Count - 1)];
        var offset = 0;
        for (var i = 0; i < offsets.Length; i++)
        {
            offset += lines[i].Length;
            offsets[i] = offset;
            offset += Environment.NewLine.Length;
        }
        return new(string.Join(Environment.NewLine, lines), offsets);
    }
}

/// <summary>
/// The result of the public <see cref="Parser"/> entry points: the program after the
/// COMPLETE front end — parsing, <c>load</c> elaboration, parameter detection,
/// implicit-argument resolution, and property-exposure resolution — exactly as
/// <see cref="KatLangEngine"/> would evaluate it. <see cref="Root"/> is typed
/// <see cref="Algorithm.User"/> because a program root is ALWAYS a user algorithm: the parser
/// produces one (a source file is one scope-owning body; the recovery placeholder for an
/// unparseable or oversized source is an empty one too), and every elaboration pass returns
/// the variant it was given — so the root's properties, parameters, and output are readable
/// without a pattern match.
/// When <see cref="HasErrors"/> is true this is a recovery tree for diagnostics and
/// editor queries. Source-based engine entry points reject it without evaluation;
/// passing <see cref="Root"/> directly to an AST evaluator discards that source gate.
/// <para><see cref="Root"/> is ALWAYS the output of that complete front end, never raw
/// syntax — including when a module is MISSING. A <c>load</c> directive whose module was not
/// elaborated — unavailable because the parse had no <see cref="RunOptions.DownloadCode"/>
/// (one <see cref="DiagnosticCode.LoadElaborationUnavailable"/> error per directive), or
/// refused by module elaboration (a failed fetch, a refused target, a cycle, a budget limit,
/// invalid module source — each reported at its site) — stays in place as written, never
/// replaced by a stand-in value, and the program is elaborated PROVISIONALLY around it: the
/// elaboration passes' own diagnostics are withheld, because any of them could depend on
/// what the missing modules would supply. Such a result is never evaluated, but
/// <see cref="Semantics.SemanticModelBuilder.Build(ParseResult)"/> models it like any
/// other, classifying the names a missing module could supply as
/// <see cref="Semantics.IdentifierClassification.DeferredModuleReference"/>.</para>
/// <para>A result produced by <see cref="Parser"/> carries a read-only snapshot of its
/// <see cref="Diagnostics"/>, taken when the parse completed: nothing KatLang does later
/// (for example materializing a lazily loaded module while the tree is evaluated) changes
/// a result a host already holds.</para>
/// <para>Only the parser constructs these results. Payloads cannot be replaced independently
/// of the host-operation context used during elaboration. For a host-built elaborated AST,
/// use <see cref="Semantics.SemanticModelBuilder.Build(Algorithm)"/> directly.</para>
/// </summary>
public sealed record ParseResult
{
    internal ParseResult(Algorithm.User Root, IReadOnlyList<Diagnostic> Diagnostics)
        => (this.Root, this.Diagnostics) = (Root, Diagnostics);

    /// <summary>
    /// The elaborated root produced by the complete front end: a recovery tree when the parse
    /// has errors, and a provisional elaboration that keeps each unresolved <c>load</c> directive
    /// in place when its module is missing (unavailable without a downloader, or refused by
    /// module elaboration). Never raw syntax.
    /// </summary>
    public Algorithm.User Root { get; }

    /// <summary>
    /// The read-only diagnostic snapshot taken when parsing completed, in reporting order. It holds
    /// at most <see cref="SourceProcessingLimits.MaxDiagnosticCount"/> diagnostics; when the parse
    /// reported more, it holds exactly the first ones and ends with one unpositioned
    /// <see cref="DiagnosticCode.DiagnosticCountExceeded"/> diagnostic marking the list incomplete.
    /// </summary>
    public IReadOnlyList<Diagnostic> Diagnostics { get; }

    public void Deconstruct(out Algorithm.User Root, out IReadOnlyList<Diagnostic> Diagnostics)
        => (Root, Diagnostics) = (this.Root, this.Diagnostics);

    private readonly RuntimeStateSlot<HostOperations?> _hostOperations;

    /// <summary>
    /// True when <see cref="Diagnostics"/> contains an <see cref="DiagnosticSeverity.Error"/>
    /// diagnostic: <see cref="Root"/> is then a recovery tree that
    /// <see cref="KatLangEngine"/> would refuse to evaluate.
    /// </summary>
    public bool HasErrors => Diagnostics.Any(d => d.Severity == DiagnosticSeverity.Error);

    /// <summary>
    /// The host operations the elaboration resolved names against — ambient prelude members
    /// that parameter detection, exposure analysis, and the evaluator all see — carried so a
    /// semantic model built from this result resolves against the SAME prelude
    /// (<see cref="Semantics.SemanticModelBuilder.Build(ParseResult)"/>): an editor that
    /// omitted them classified an operation's references as unresolved, and a bare name an
    /// operation provides as a member of an opened library the evaluator never selects.
    /// Equality-transparent, so record equality, hashing, and printing are unchanged.
    /// </summary>
    internal HostOperations? HostOperations
    {
        get => _hostOperations.Value;
        init => _hostOperations = new(value);
    }
}
