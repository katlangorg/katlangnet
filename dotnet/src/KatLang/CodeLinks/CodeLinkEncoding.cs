namespace KatLang;

/// <summary>
/// What <see cref="CodeLink.Encode"/> made of a program: its code link
/// (<see cref="Link"/>), or why it has none (<see cref="EmptyProgram"/>,
/// <see cref="SourceTooLong"/>, <see cref="PayloadTooLong"/>).
/// A C# <c>closed</c> hierarchy: those four nested records are its only variants, no other
/// assembly can derive from it, and a switch EXPRESSION naming all four is compiler-exhaustive
/// with no catch-all arm.
/// Instances are produced only by <see cref="CodeLink"/>, and their payloads are read-only: a
/// host reads a result and cannot construct one, so a <see cref="Link"/> always carries the
/// payload of a program that fits both limits.
/// </summary>
public closed record CodeLinkEncoding
{
    private CodeLinkEncoding() { }

    /// <summary>The program has a code link.</summary>
    public sealed record Link : CodeLinkEncoding
    {
        internal Link(int format, string payload)
        {
            Format = format;
            Payload = payload;
        }

        /// <summary>The number of the format the payload is in: <see cref="CodeLink.CurrentFormat"/>.</summary>
        public int Format { get; }

        /// <summary>
        /// The program's payload: 1 to <see cref="CodeLink.MaxPayloadLength"/> characters from
        /// <c>A–Z a–z 0–9 - _</c>. A URL fragment allows all of them as they are, so the payload
        /// is never percent-encoded.
        /// </summary>
        public string Payload { get; }

        /// <summary>
        /// The link's fragment, without its <c>#</c>: <see cref="Format"/>, <c>/</c> and
        /// <see cref="Payload"/>, for example <c>1/4MWjDBlNE4PH</c>. A host that serves the
        /// Playground on another origin appends <c>#</c> and the fragment to its own base URL.
        /// </summary>
        public string Fragment => Format.ToString(System.Globalization.CultureInfo.InvariantCulture) + "/" + Payload;

        /// <summary>The link on katlang.org: <see cref="CodeLink.CanonicalBaseUrl"/>, <c>#</c> and <see cref="Fragment"/>.</summary>
        public string Url => CodeLink.CanonicalBaseUrl + "#" + Fragment;
    }

    /// <summary>The program is empty: there is nothing to link.</summary>
    public sealed record EmptyProgram : CodeLinkEncoding
    {
        internal EmptyProgram() { }
    }

    /// <summary>
    /// The program is longer than <see cref="CodeLink.MaxSourceLength"/> UTF-16 code units. It
    /// was not encoded.
    /// </summary>
    public sealed record SourceTooLong : CodeLinkEncoding
    {
        internal SourceTooLong(int sourceLength) => SourceLength = sourceLength;

        /// <summary>The program's length in UTF-16 code units.</summary>
        public int SourceLength { get; }
    }

    /// <summary>
    /// The program fits <see cref="CodeLink.MaxSourceLength"/>, but its payload would be longer
    /// than <see cref="CodeLink.MaxPayloadLength"/> characters.
    /// </summary>
    public sealed record PayloadTooLong : CodeLinkEncoding
    {
        internal PayloadTooLong(int payloadLength) => PayloadLength = payloadLength;

        /// <summary>The length the payload would have, in characters.</summary>
        public int PayloadLength { get; }
    }
}
