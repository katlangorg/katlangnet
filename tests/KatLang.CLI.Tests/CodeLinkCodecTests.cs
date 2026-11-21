using System.Globalization;

namespace KatLang.CLI.Tests;

/// <summary>
/// The code-link encoder (<see cref="LzString"/>) and the line <c>--code-link</c> writes
/// (<see cref="CodeLink.Line"/>), against payloads katlang.org's own encoder made
/// (<see cref="CodeLinkFixtures"/>): the encoder must produce lz-string 1.5.0's output exactly,
/// or katlang.org refuses the link (it accepts a payload only if re-encoding its program gives
/// it back).
/// </summary>
public sealed class CodeLinkCodecTests
{
    private const string LinkLinePrefix = "katlang-link: https://katlang.org/#code/";

    public static TheoryData<string> PlaygroundVectorNames => CodeLinkFixtures.Names(CodeLinkFixtures.PlaygroundVectors);

    public static TheoryData<string> GeneratedCaseNames => CodeLinkFixtures.Names(CodeLinkFixtures.GeneratedCases);

    // ── Payloads ────────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(PlaygroundVectorNames))]
    public void PlaygroundVector_IsEncodedAsThePlaygroundEncodesIt(string name)
    {
        var vector = CodeLinkFixtures.PlaygroundVector(name);

        Assert.Equal(vector.Payload, LzString.CompressToEncodedUriComponent(vector.Source));
        Assert.Equal(CodeLink.UrlPrefix + vector.Payload, vector.Url);
        Assert.Equal(CodeLink.LinePrefix + vector.Url, CodeLink.Line(vector.Source));
    }

    [Theory]
    [MemberData(nameof(GeneratedCaseNames))]
    public void GeneratedCase_IsEncodedAndJudgedAsTheReferenceEncoderDoes(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(@case.Payload, LzString.CompressToEncodedUriComponent(@case.Source));

        var expected = @case.Status switch
        {
            "ok" => LinkLinePrefix + @case.Payload,
            "empty" => EmptyProgramLine,
            "tooLong" when @case.Source.Length > CodeLink.MaxSourceLength => SourceTooLongLine(@case.Source.Length),
            "tooLong" => PayloadTooLongLine(@case.Payload.Length),
            _ => throw new InvalidDataException($"Unknown reference verdict '{@case.Status}' for '{name}'."),
        };
        Assert.Equal(expected, CodeLink.Line(@case.Source));
    }

    [Fact]
    public void GeneratedCases_CoverWhatACodeLinkMustCarry()
    {
        var cases = CodeLinkFixtures.GeneratedCases;

        Assert.True(cases.Count >= 700, $"the fixture holds {cases.Count} cases");
        Assert.Equal(cases.Count, cases.Select(@case => @case.Name).Distinct(StringComparer.Ordinal).Count());

        Assert.Contains(cases, @case => @case.Source.Contains("\r\n", StringComparison.Ordinal));
        Assert.Contains(cases, @case => @case.Source.Contains('\r') && !@case.Source.Contains('\n'));
        Assert.Contains(cases, @case => @case.Source.Contains('\t'));
        Assert.Contains(cases, @case => @case.Source.Contains(" \n", StringComparison.Ordinal));
        Assert.Contains(cases, @case => "āčēģīķļņšūžĀČĒĢĪĶĻŅŠŪŽ".All(@case.Source.Contains));
        Assert.Contains(cases, @case => @case.Source.Contains('ÿ') && @case.Source.Contains('Ā'));
        Assert.Contains(cases, @case => HasSurrogatePair(@case.Source));
        Assert.Contains(cases, @case => HasUnpairedSurrogate(@case.Source));
        Assert.Contains(cases, @case => CountOccurrences(@case.Source, "__proto__") >= 50);

        // The limits, from both sides.
        Assert.Contains(cases, @case => @case.Payload.Length == CodeLink.MaxPayloadLength && @case.Status == "ok");
        Assert.Contains(cases, @case => @case.Payload.Length == CodeLink.MaxPayloadLength + 1 && @case.Status == "tooLong");
        Assert.Contains(cases, @case => @case.Source.Length == CodeLink.MaxSourceLength && @case.Status == "ok");
        Assert.Contains(cases, @case => @case.Source.Length == CodeLink.MaxSourceLength + 1 && @case.Status == "tooLong");
        Assert.Contains(cases, @case => @case.Source.Length == 0 && @case.Status == "empty");
    }

    /// <summary>
    /// lz-string keeps its dictionary in a plain JavaScript object, where assigning the key
    /// <c>"__proto__"</c> sets the prototype instead: the code is spent and the key is never
    /// stored. A source that repeats <c>__proto__</c> often enough to reach that phrase is encoded
    /// differently from an encoder that stores it, and katlang.org would refuse its link.
    /// </summary>
    [Theory]
    [InlineData("proto-spaced-50")]
    [InlineData("proto-joined-100")]
    [InlineData("proto-program")]
    public void Encoder_NeverStoresTheKeyAJavaScriptObjectCannotHold(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(@case.Payload, LzString.CompressToEncodedUriComponent(@case.Source));
    }

    [Fact]
    public void Encoder_OfTheEmptyString_IsLzStringsEndOfStreamAlone()
        => Assert.Equal("Q", LzString.CompressToEncodedUriComponent(""));

    [Fact]
    public void Encoder_RejectsNull()
        => Assert.Throws<ArgumentNullException>(() => LzString.CompressToEncodedUriComponent(null!));

    /// <summary>
    /// A run of one code unit makes the longest phrases LZW makes (one, two, three, ... units),
    /// the input on which string-keyed dictionaries cost the most: about 12 MB of key strings for
    /// 50,000 units. Keyed by prefix code and code unit, the encoder allocates a few kilobytes.
    /// </summary>
    [Fact]
    public void Encoder_IsLinear_OnTheLongestPhrases()
    {
        var source = new string('a', CodeLink.MaxSourceLength);
        _ = LzString.CompressToEncodedUriComponent("warm up the encoder's code paths: aaaa");

        var before = GC.GetAllocatedBytesForCurrentThread();
        var payload = LzString.CompressToEncodedUriComponent(source);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.True(allocated < 256 * 1024, $"encoding {source.Length} code units allocated {allocated} bytes");
        Assert.True(payload.Length < 1000, $"the payload is {payload.Length} characters");
    }

    // ── The line and its limits ─────────────────────────────────────────────

    [Fact]
    public void Limits_AreTheReferenceImplementations()
    {
        // katlang-code-link.js: MAX_SOURCE_LENGTH and MAX_PAYLOAD_LENGTH.
        Assert.Equal(50_000, CodeLink.MaxSourceLength);
        Assert.Equal(8_192, CodeLink.MaxPayloadLength);
    }

    [Fact]
    public void Line_TheEmptyProgram_HasNoLink()
        => Assert.Equal("katlang-link: none: the program is empty.", CodeLink.Line(""));

    [Theory]
    [InlineData("source-50000")]
    [InlineData("source-50000-emoji")]
    [InlineData("comment-50000")]
    public void Line_ASourceOfExactly50000CodeUnits_IsALink(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(50_000, @case.Source.Length);
        Assert.Equal(LinkLinePrefix + @case.Payload, CodeLink.Line(@case.Source));
    }

    [Theory]
    [InlineData("source-50001")]
    [InlineData("source-50001-emoji")]
    [InlineData("comment-50001")]
    public void Line_ASourceOf50001CodeUnits_HasNoLink_WhateverItsPayload(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(50_001, @case.Source.Length);
        Assert.True(@case.Payload.Length <= CodeLink.MaxPayloadLength, "the source length alone decides");
        Assert.Equal(
            "katlang-link: none: the program is 50,001 UTF-16 code units long, more than the 50,000 a code link can carry.",
            CodeLink.Line(@case.Source));
    }

    [Theory]
    [InlineData("payload-8192")]
    [InlineData("comment-payload-8192")]
    public void Line_APayloadOfExactly8192Characters_IsALink(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(8_192, @case.Payload.Length);
        Assert.Equal(LinkLinePrefix + @case.Payload, CodeLink.Line(@case.Source));
    }

    [Theory]
    [InlineData("payload-8193")]
    [InlineData("comment-payload-8193")]
    public void Line_APayloadOf8193Characters_HasNoLink(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(8_193, @case.Payload.Length);
        Assert.True(@case.Source.Length <= CodeLink.MaxSourceLength);
        Assert.Equal(
            "katlang-link: none: the program's link payload would be 8,193 characters long, more than the 8,192 a code link can carry.",
            CodeLink.Line(@case.Source));
    }

    [Fact]
    public void Line_EncodesTheSourceAsWritten_WithNothingNormalized()
    {
        // Each of these differs from "A = 1\nB = 2\nA + B" in whitespace alone, and each has a
        // link of its own.
        string[] names = ["lines-lf", "lines-lf-final", "lines-crlf", "lines-crlf-final", "lines-cr", "lines-mixed", "lines-tabs", "lines-trailing-spaces"];
        var lines = names.Select(name => CodeLink.Line(CodeLinkFixtures.Generated(name).Source)).ToList();

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
            var line = CodeLink.Line(@case.Source);
            Assert.StartsWith(CodeLink.LinePrefix, line);
            Assert.All(line, character => Assert.InRange(character, ' ', '~'));
        }
    }

    internal const string EmptyProgramLine = "katlang-link: none: the program is empty.";

    // The counts are grouped in the invariant culture whatever the test host's culture is: the
    // CLI's lines do not depend on the machine.
    internal static string SourceTooLongLine(int length)
        => string.Create(CultureInfo.InvariantCulture, $"katlang-link: none: the program is {length:N0} UTF-16 code units long, more than the 50,000 a code link can carry.");

    internal static string PayloadTooLongLine(int length)
        => string.Create(CultureInfo.InvariantCulture, $"katlang-link: none: the program's link payload would be {length:N0} characters long, more than the 8,192 a code link can carry.");

    private static bool HasSurrogatePair(string text)
    {
        for (var i = 0; i + 1 < text.Length; i++)
        {
            if (char.IsSurrogatePair(text[i], text[i + 1]))
                return true;
        }

        return false;
    }

    private static bool HasUnpairedSurrogate(string text)
    {
        for (var i = 0; i < text.Length; i++)
        {
            if (char.IsHighSurrogate(text[i]) && (i + 1 == text.Length || !char.IsLowSurrogate(text[i + 1])))
                return true;
            if (char.IsLowSurrogate(text[i]) && (i == 0 || !char.IsHighSurrogate(text[i - 1])))
                return true;
        }

        return false;
    }

    private static int CountOccurrences(string text, string value)
    {
        var count = 0;
        for (var index = text.IndexOf(value, StringComparison.Ordinal); index >= 0; index = text.IndexOf(value, index + value.Length, StringComparison.Ordinal))
            count++;
        return count;
    }
}
