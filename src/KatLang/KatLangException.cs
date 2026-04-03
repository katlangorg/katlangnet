namespace KatLang;

/// <summary>
/// Exception thrown by convenience methods when parse or evaluation fails.
/// </summary>
public sealed class KatLangException : Exception
{
    public IReadOnlyList<KatLangError> Errors { get; }

    public KatLangException(IReadOnlyList<KatLangError> errors)
        : base(string.Join(Environment.NewLine, errors.Select(e => e.ToString())))
    {
        Errors = errors;
    }
}
