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
    SourceSpan Span);

/// <summary>
/// The result of the public KatLang parser compatibility entry points.
/// <see cref="Root"/> is the elaborated program produced by the front-end pipeline,
/// not the raw syntax tree returned by <c>Parser.ParseSyntax</c>.
/// </summary>
public sealed record ParseResult(Algorithm Root, IReadOnlyList<Diagnostic> Diagnostics)
{
    public bool HasErrors => Diagnostics.Any(d => d.Severity == DiagnosticSeverity.Error);
}
