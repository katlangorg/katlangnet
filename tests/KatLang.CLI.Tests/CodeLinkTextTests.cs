using System.Globalization;
using KatLang.Tests.CodeLinks;

namespace KatLang.CLI.Tests;

/// <summary>
/// The CLI's wording of code links (<see cref="CodeLinkText"/>): the line <c>--code-link</c>
/// writes for a program, and the reason <c>source</c> gives for a link it cannot read. The
/// format, the limits and the verdicts are the KatLang package's (<see cref="CodeLink"/>, tested
/// there against the format's reference implementation); these tests pin the exact text, which tools parse,
/// for the programs of the same fixtures (<see cref="CodeLinkFixtures"/>).
/// </summary>
public sealed class CodeLinkTextTests
{
    private const string LinkLinePrefix = "katlang-link: https://katlang.org/#1/";

    public static TheoryData<string> VectorNames => CodeLinkFixtures.Names(CodeLinkFixtures.Vectors);

    public static TheoryData<string> GeneratedCaseNames => CodeLinkFixtures.Names(CodeLinkFixtures.GeneratedCases);

    // ── The line --code-link writes ─────────────────────────────────────────

    [Theory]
    [MemberData(nameof(VectorNames))]
    public void Vector_HasItsLinkAsTheLine(string name)
    {
        var vector = CodeLinkFixtures.Vector(name);

        Assert.Equal(CodeLinkText.LinePrefix + vector.Url, CodeLinkText.Line(vector.Source));
        Assert.Equal(LinkLinePrefix + vector.Payload, CodeLinkText.Line(vector.Source));
    }

    [Theory]
    [MemberData(nameof(GeneratedCaseNames))]
    public void GeneratedCase_HasTheLineOfTheReferenceEncodersVerdict(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        var expected = @case.Status switch
        {
            "ok" => LinkLinePrefix + @case.Payload,
            "empty" => EmptyProgramLine,
            "sourceTooLong" => SourceTooLongLine(@case.Source.Length),
            "payloadTooLong" => PayloadTooLongLine(@case.Payload.Length),
            _ => throw new InvalidDataException($"Unknown reference verdict '{@case.Status}' for '{name}'."),
        };
        Assert.Equal(expected, CodeLinkText.Line(@case.Source));
    }

    [Fact]
    public void Line_StartsWithTheFixedPrefixes()
    {
        Assert.Equal("katlang-link: ", CodeLinkText.LinePrefix);
        Assert.Equal("none: ", CodeLinkText.NoLinkPrefix);
        Assert.Equal("katlang-link: https://katlang.org/#1/ML4", CodeLinkText.Line("1"));
    }

    [Fact]
    public void Line_TheEmptyProgram_HasNoLink()
        => Assert.Equal("katlang-link: none: the program is empty.", CodeLinkText.Line(""));

    [Theory]
    [InlineData("source-20000")]
    [InlineData("source-20000-emoji")]
    [InlineData("comment-20000")]
    public void Line_ASourceOfExactly20000CodeUnits_IsALink(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(20_000, @case.Source.Length);
        Assert.Equal(LinkLinePrefix + @case.Payload, CodeLinkText.Line(@case.Source));
    }

    [Theory]
    [InlineData("source-20001")]
    [InlineData("source-20001-emoji")]
    [InlineData("comment-20001")]
    public void Line_ASourceOf20001CodeUnits_HasNoLink(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(20_001, @case.Source.Length);
        Assert.Equal(
            "katlang-link: none: the program is 20,001 UTF-16 code units long, more than the 20,000 a code link can carry.",
            CodeLinkText.Line(@case.Source));
    }

    [Theory]
    [InlineData("payload-1970")]
    [InlineData("comment-payload-1970")]
    public void Line_APayloadOfExactly1970Characters_IsALink(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(1_970, @case.Payload.Length);
        Assert.Equal(LinkLinePrefix + @case.Payload, CodeLinkText.Line(@case.Source));
    }

    [Theory]
    [InlineData("payload-1971")]
    [InlineData("comment-payload-1971")]
    public void Line_APayloadOf1971Characters_HasNoLink(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(1_971, @case.Payload.Length);
        Assert.True(@case.Source.Length <= CodeLink.MaxSourceLength);
        Assert.Equal(
            "katlang-link: none: the program's link payload would be 1,971 characters long, more than the 1,970 a code link can carry.",
            CodeLinkText.Line(@case.Source));
    }

    [Fact]
    public void Line_CountsAreGroupedInTheInvariantCulture_WhateverTheCurrentOne()
    {
        var source = new string('x', 1_234_567);
        var previous = CultureInfo.CurrentCulture;
        try
        {
            // A culture that groups digits with a space and writes the decimal comma, built here
            // so that the test does not depend on the host's globalization data.
            var culture = (CultureInfo)CultureInfo.InvariantCulture.Clone();
            culture.NumberFormat.NumberGroupSeparator = " ";
            culture.NumberFormat.NumberDecimalSeparator = ",";
            CultureInfo.CurrentCulture = culture;
            Assert.Equal("1 234 567", 1_234_567.ToString("N0", CultureInfo.CurrentCulture));

            Assert.Equal(
                "katlang-link: none: the program is 1,234,567 UTF-16 code units long, more than the 20,000 a code link can carry.",
                CodeLinkText.Line(source));
            Assert.Equal("its payload is longer than 1,970 characters.", CodeLinkText.RefusalReason(CodeLinkRefusal.PayloadTooLong));
        }
        finally
        {
            CultureInfo.CurrentCulture = previous;
        }
    }

    [Fact]
    public void Line_EncodesTheSourceAsWritten_WithNothingNormalized()
    {
        // Each of these differs from "A = 1\nB = 2\nA + B" in whitespace alone, and each has a
        // link of its own.
        string[] names = ["lines-lf", "lines-lf-final", "lines-crlf", "lines-crlf-final", "lines-cr", "lines-mixed", "lines-tabs", "lines-trailing-spaces"];
        var lines = names.Select(name => CodeLinkText.Line(CodeLinkFixtures.Generated(name).Source)).ToList();

        Assert.Equal(names.Length, lines.Distinct(StringComparer.Ordinal).Count());
        Assert.All(names.Zip(lines), pair => Assert.Equal(LinkLinePrefix + CodeLinkFixtures.Generated(pair.First).Payload, pair.Second));
    }

    [Fact]
    public void Line_IsTerminalSafeAndOneLine()
    {
        // Every character of every line is printable ASCII: the payload alphabet and the fixed
        // text of the reasons.
        foreach (var @case in CodeLinkFixtures.GeneratedCases)
        {
            var line = CodeLinkText.Line(@case.Source);
            Assert.StartsWith(CodeLinkText.LinePrefix, line);
            Assert.All(line, character => Assert.InRange(character, ' ', '~'));
        }
    }

    // ── The reason source gives ─────────────────────────────────────────────

    [Theory]
    [InlineData(CodeLinkRefusal.NotACodeLink, "it has no #<format>/<payload> fragment.")]
    [InlineData(CodeLinkRefusal.EmptyPayload, "its payload is empty.")]
    [InlineData(CodeLinkRefusal.PayloadTooLong, "its payload is longer than 1,970 characters.")]
    [InlineData(CodeLinkRefusal.InvalidCharacter, "its payload has a character that code links do not use.")]
    [InlineData(CodeLinkRefusal.UnsupportedVersion, "its format is not one this KatLang reads; a newer KatLang may read it.")]
    [InlineData(CodeLinkRefusal.Damaged, "its payload is damaged or cut short.")]
    [InlineData(CodeLinkRefusal.SourceTooLong, "its program is longer than 20,000 UTF-16 code units.")]
    [InlineData(CodeLinkRefusal.NotCanonical, "its payload does not re-encode to itself, so it was changed.")]
    public void RefusalReason_IsOneFixedSentenceForEachRefusal(CodeLinkRefusal reason, string expected)
        => Assert.Equal(expected, CodeLinkText.RefusalReason(reason));

    [Fact]
    public void RefusalReason_CoversEveryRefusal_AndQuotesThePackagesLimits()
    {
        var reasons = Enum.GetValues<CodeLinkRefusal>().Select(CodeLinkText.RefusalReason).ToList();

        Assert.Equal(8, reasons.Count);
        Assert.Equal(reasons.Count, reasons.Distinct(StringComparer.Ordinal).Count());
        Assert.All(reasons, reason =>
        {
            Assert.EndsWith(".", reason, StringComparison.Ordinal);
            Assert.All(reason, character => Assert.InRange(character, ' ', '~'));
        });

        Assert.Contains(
            string.Create(CultureInfo.InvariantCulture, $"longer than {CodeLink.MaxPayloadLength:N0} characters"),
            CodeLinkText.RefusalReason(CodeLinkRefusal.PayloadTooLong),
            StringComparison.Ordinal);
        Assert.Contains(
            string.Create(CultureInfo.InvariantCulture, $"longer than {CodeLink.MaxSourceLength:N0} UTF-16 code units"),
            CodeLinkText.RefusalReason(CodeLinkRefusal.SourceTooLong),
            StringComparison.Ordinal);

        Assert.Throws<ArgumentOutOfRangeException>(() => CodeLinkText.RefusalReason((CodeLinkRefusal)99));
    }

    internal const string EmptyProgramLine = "katlang-link: none: the program is empty.";

    // The counts are grouped in the invariant culture whatever the test host's culture is: the
    // CLI's lines do not depend on the machine.
    internal static string SourceTooLongLine(int length)
        => string.Create(CultureInfo.InvariantCulture, $"katlang-link: none: the program is {length:N0} UTF-16 code units long, more than the 20,000 a code link can carry.");

    internal static string PayloadTooLongLine(int length)
        => string.Create(CultureInfo.InvariantCulture, $"katlang-link: none: the program's link payload would be {length:N0} characters long, more than the 1,970 a code link can carry.");
}
