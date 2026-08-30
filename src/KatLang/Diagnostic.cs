namespace KatLang;

public enum DiagnosticSeverity
{
    Hint = 1,
    Info = 2,
    Warning = 4,
    Error = 8,
}

/// <summary>A single diagnostic message produced during lexing or parsing.</summary>
public sealed record Diagnostic(
    string Message,
    DiagnosticSeverity Severity,
    SourceSpan Span)
{
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
/// The result of the public KatLang parser compatibility entry points.
/// <see cref="Root"/> is the elaborated program produced by the front-end pipeline,
/// not the raw syntax tree returned by <c>Parser.ParseSyntax</c>.
/// </summary>
public sealed record ParseResult(Algorithm Root, IReadOnlyList<Diagnostic> Diagnostics)
{
    public bool HasErrors => Diagnostics.Any(d => d.Severity == DiagnosticSeverity.Error);
}
