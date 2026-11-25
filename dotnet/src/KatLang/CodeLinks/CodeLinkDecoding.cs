namespace KatLang;

/// <summary>
/// What <see cref="CodeLink.Decode"/> or <see cref="CodeLink.DecodeLink"/> read from a code
/// link: the program it carries (<see cref="Program"/>), or why it is refused
/// (<see cref="Refused"/>).
/// A C# <c>closed</c> hierarchy: those two nested records are its only variants, no other
/// assembly can derive from it, and a switch EXPRESSION naming both is compiler-exhaustive with
/// no catch-all arm.
/// Instances are produced only by <see cref="CodeLink"/>, and their payloads are read-only: a
/// host reads a result and cannot construct one, so a <see cref="Program"/> always carries a
/// program that passed every check.
/// </summary>
public closed record CodeLinkDecoding
{
    private CodeLinkDecoding() { }

    /// <summary>The link carries a program.</summary>
    public sealed record Program : CodeLinkDecoding
    {
        internal Program(string source) => Source = source;

        /// <summary>
        /// The program, exactly as the link carries it: 1 to
        /// <see cref="CodeLink.MaxSourceLength"/> UTF-16 code units, with nothing normalized
        /// (line breaks, tabs, trailing spaces and control characters are part of it, and it
        /// may hold an unpaired surrogate). Re-encoding it in the format named by the link
        /// reproduces the payload.
        /// </summary>
        public string Source { get; }
    }

    /// <summary>The link is refused: it carries no program anyone should run.</summary>
    public sealed record Refused : CodeLinkDecoding
    {
        internal Refused(CodeLinkRefusal reason) => Reason = reason;

        /// <summary>The first check the link failed.</summary>
        public CodeLinkRefusal Reason { get; }
    }
}

/// <summary>
/// Why a code link is refused (<see cref="CodeLinkDecoding.Refused"/>), numbered in the order
/// the checks are made. <see cref="NotACodeLink"/> comes from <see cref="CodeLink.DecodeLink"/>
/// only.
/// </summary>
public enum CodeLinkRefusal
{
    /// <summary>
    /// The link has no code-link fragment, <c>#&lt;format&gt;/&lt;payload&gt;</c>, as links in
    /// the earlier <c>#code/</c> format have not (<see cref="CodeLink.DecodeLink"/> only).
    /// </summary>
    NotACodeLink = 0,

    /// <summary>
    /// The link names a format this KatLang does not read: it was made in a newer format, which
    /// a newer KatLang may read, or it was changed on the way.
    /// </summary>
    UnsupportedVersion = 1,

    /// <summary>The payload is empty.</summary>
    EmptyPayload = 2,

    /// <summary>The payload is longer than <see cref="CodeLink.MaxPayloadLength"/> characters.</summary>
    PayloadTooLong = 3,

    /// <summary>The payload has a character outside <c>A–Z a–z 0–9 - _</c>.</summary>
    InvalidCharacter = 4,

    /// <summary>
    /// The payload does not decode to a program: it was cut short or changed on the way, so its
    /// check value does not match, its stream ends early, or its text is not valid.
    /// </summary>
    Damaged = 5,

    /// <summary>
    /// The stream's length field exceeds the format's byte limit, or its decoded text
    /// exceeds <see cref="CodeLink.MaxSourceLength"/> UTF-16 code units.
    /// </summary>
    SourceTooLong = 6,

    /// <summary>
    /// The payload decodes to a program, but that program's payload is a different one: the
    /// link was changed on the way.
    /// </summary>
    NotCanonical = 7,
}
