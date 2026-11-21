using System.Security.Cryptography;
using System.Text;

namespace KatLang.Tests.CodeLinks;

/// <summary>
/// The code-link encoder (<see cref="CodeLink.Encode"/> over <see cref="CodeLinkFormat"/> and
/// <see cref="CodeLinkModel"/>) against payloads the format's reference implementation made
/// (<see cref="CodeLinkFixtures"/>). The format is frozen: a link already shared must keep
/// opening, so every payload here is an exact expectation, and a change that alters one is a
/// new format, which only the owner decides.
/// </summary>
public sealed class CodeLinkEncodingTests
{
    public static TheoryData<string> VectorNames => CodeLinkFixtures.Names(CodeLinkFixtures.Vectors);

    public static TheoryData<string> GeneratedCaseNames => CodeLinkFixtures.Names(CodeLinkFixtures.GeneratedCases);

    // ── Payloads ────────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(VectorNames))]
    public void Vector_IsEncodedAsTheReferenceEncodesIt(string name)
    {
        var vector = CodeLinkFixtures.Vector(name);

        var link = Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(vector.Source));
        Assert.Equal(vector.Payload, link.Payload);
        Assert.Equal(vector.Url, link.Url);
    }

    [Theory]
    [MemberData(nameof(GeneratedCaseNames))]
    public void GeneratedCase_IsEncodedAndJudgedAsTheReferenceEncoderDoes(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        var encoding = CodeLink.Encode(@case.Source);
        switch (@case.Status)
        {
            case "ok":
                var link = Assert.IsType<CodeLinkEncoding.Link>(encoding);
                Assert.Equal(@case.Payload, link.Payload);
                Assert.Equal(1, link.Format);
                Assert.Equal("https://katlang.org/#1/" + @case.Payload, link.Url);
                break;
            case "empty":
                Assert.IsType<CodeLinkEncoding.EmptyProgram>(encoding);
                break;
            case "sourceTooLong":
                Assert.Equal(@case.Source.Length, Assert.IsType<CodeLinkEncoding.SourceTooLong>(encoding).SourceLength);
                break;
            case "payloadTooLong":
                Assert.Equal(@case.Payload.Length, Assert.IsType<CodeLinkEncoding.PayloadTooLong>(encoding).PayloadLength);
                Assert.Equal(@case.Payload, CodeLinkFormat.Encode(@case.Source));
                break;
            default:
                throw new InvalidDataException($"Unknown reference verdict '{@case.Status}' for '{name}'.");
        }
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
        Assert.Contains(cases, @case => @case.Source.Contains('\0'));
        Assert.Contains(cases, @case => HasSurrogatePair(@case.Source));
        Assert.Contains(cases, @case => HasUnpairedSurrogate(@case.Source));
        Assert.Contains(cases, @case => @case.Source.Contains((char)0xFEFF));

        // The limits, from both sides.
        Assert.Contains(cases, @case => @case.Payload.Length == CodeLink.MaxPayloadLength && @case.Status == "ok");
        Assert.Contains(cases, @case => @case.Payload.Length == CodeLink.MaxPayloadLength + 1 && @case.Status == "payloadTooLong");
        Assert.Contains(cases, @case => @case.Source.Length == CodeLink.MaxSourceLength && @case.Status == "ok");
        Assert.Contains(cases, @case => @case.Source.Length == CodeLink.MaxSourceLength + 1 && @case.Status == "sourceTooLong");
        Assert.Contains(cases, @case => @case.Source.Length == 0 && @case.Status == "empty");
    }

    // ── The verdict and its limits ──────────────────────────────────────────

    [Fact]
    public void Limits_AndTheLinkShape_AreTheFormats()
    {
        Assert.Equal(20_000, CodeLink.MaxSourceLength);
        Assert.Equal(1_970, CodeLink.MaxPayloadLength);
        Assert.Equal(1, CodeLink.CurrentFormat);
        Assert.Equal("https://katlang.org/", CodeLink.CanonicalBaseUrl);
    }

    [Fact]
    public void Encode_RejectsNull()
        => Assert.Equal("source", Assert.Throws<ArgumentNullException>(() => CodeLink.Encode(null!)).ParamName);

    [Fact]
    public void Encode_TheEmptyProgram_HasNoLink()
        => Assert.IsType<CodeLinkEncoding.EmptyProgram>(CodeLink.Encode(""));

    [Fact]
    public void Encode_ALink_IsThePayloadOnTheCanonicalOrigin()
    {
        // The documented example: https://katlang.org/#1/4MWjDBlNE4PH opens 100 - 3 * 5 ^ 2.
        var link = Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode("100 - 3 * 5 ^ 2"));

        Assert.Equal(1, link.Format);
        Assert.Equal("4MWjDBlNE4PH", link.Payload);
        Assert.Equal("1/4MWjDBlNE4PH", link.Fragment);
        Assert.Equal("https://katlang.org/#1/4MWjDBlNE4PH", link.Url);
        Assert.Equal(CodeLink.CanonicalBaseUrl + "#" + link.Fragment, link.Url);
        Assert.True(CodeLink.TryGetPayload(link.Url, out var format, out var payload));
        Assert.Equal((link.Format, link.Payload), (format, payload));
    }

    [Theory]
    [InlineData("source-20000")]
    [InlineData("source-20000-emoji")]
    [InlineData("comment-20000")]
    public void Encode_ASourceOfExactly20000CodeUnits_IsALink(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(20_000, @case.Source.Length);
        Assert.Equal(@case.Payload, Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(@case.Source)).Payload);
    }

    [Theory]
    [InlineData("source-20001")]
    [InlineData("source-20001-emoji")]
    [InlineData("comment-20001")]
    public void Encode_ASourceOf20001CodeUnits_HasNoLink_AndIsNeverEncoded(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(20_001, @case.Source.Length);
        Assert.Equal("", @case.Payload);
        Assert.Equal(20_001, Assert.IsType<CodeLinkEncoding.SourceTooLong>(CodeLink.Encode(@case.Source)).SourceLength);
    }

    [Theory]
    [InlineData("payload-1970")]
    [InlineData("comment-payload-1970")]
    public void Encode_APayloadOfExactly1970Characters_IsALink(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(1_970, @case.Payload.Length);
        Assert.Equal(@case.Payload, Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(@case.Source)).Payload);
    }

    [Theory]
    [InlineData("payload-1971")]
    [InlineData("comment-payload-1971")]
    public void Encode_APayloadOf1971Characters_HasNoLink(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        Assert.Equal(1_971, @case.Payload.Length);
        Assert.True(@case.Source.Length <= CodeLink.MaxSourceLength);
        Assert.Equal(1_971, Assert.IsType<CodeLinkEncoding.PayloadTooLong>(CodeLink.Encode(@case.Source)).PayloadLength);
    }

    /// <summary>
    /// A program over the source limit is refused without the work of encoding it: the refusal
    /// allocates one small result, not the model's state.
    /// </summary>
    [Fact]
    public void Encode_ASourceOverTheLimit_IsNeverEncoded()
    {
        var random = new Random(20_001);
        var source = string.Create(1_000_000, random, static (span, random) =>
        {
            for (var i = 0; i < span.Length; i++)
                span[i] = (char)random.Next(' ', 0x2000);
        });
        _ = CodeLink.Encode(source[..(CodeLink.MaxSourceLength + 1)]);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var encoding = CodeLink.Encode(source);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal(1_000_000, Assert.IsType<CodeLinkEncoding.SourceTooLong>(encoding).SourceLength);
        Assert.True(allocated < 64 * 1024, $"refusing {source.Length} code units allocated {allocated} bytes");
    }

    /// <summary>
    /// Encoding the longest program allocates one copy of the model's state (about 3 MB) and
    /// buffers linear in the program, whatever the program is.
    /// </summary>
    [Fact]
    public void Encode_OfTheLongestProgram_AllocatesOneModelStateAndLinearBuffers()
    {
        var source = string.Concat(Enumerable.Repeat("😀", CodeLink.MaxSourceLength / 2));
        _ = CodeLink.Encode("warm up the primed state: 😀");

        var before = GC.GetAllocatedBytesForCurrentThread();
        var encoding = CodeLink.Encode(source);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        // Seven context tables and the match table cost 3,014,656 bytes. One MiB of headroom
        // covers the history, 40,000 WTF-8 bytes, output, and GC counter variation.
        var link = Assert.IsType<CodeLinkEncoding.Link>(encoding);
        Assert.True(allocated < 4 * 1024 * 1024, $"encoding {source.Length} code units allocated {allocated} bytes");
        Assert.True(link.Payload.Length < 1_000, $"the payload is {link.Payload.Length} characters");
    }

    [Fact]
    public void Encode_EncodesTheSourceAsWritten_WithNothingNormalized()
    {
        // Each of these differs from "A = 1\nB = 2\nA + B" in whitespace alone, and each has a
        // link of its own.
        string[] names = ["lines-lf", "lines-lf-final", "lines-crlf", "lines-crlf-final", "lines-cr", "lines-mixed", "lines-tabs", "lines-trailing-spaces"];
        var payloads = names
            .Select(name => Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(CodeLinkFixtures.Generated(name).Source)).Payload)
            .ToList();

        Assert.Equal(names.Length, payloads.Distinct(StringComparer.Ordinal).Count());
        Assert.All(names.Zip(payloads), pair => Assert.Equal(CodeLinkFixtures.Generated(pair.First).Payload, pair.Second));
    }

    [Fact]
    public void Encode_APayload_IsBase64UrlDigits_InTheCurrentFormat()
    {
        foreach (var @case in CodeLinkFixtures.GeneratedCases.Where(@case => @case.Status == "ok"))
        {
            var link = Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(@case.Source));
            Assert.InRange(link.Payload.Length, 1, CodeLink.MaxPayloadLength);
            Assert.Equal(CodeLink.CurrentFormat, link.Format);
            Assert.Equal("1/" + link.Payload, link.Fragment);
            Assert.All(link.Payload, character => Assert.True(
                char.IsAsciiLetterOrDigit(character) || character is '-' or '_',
                $"'{@case.Name}' has the payload character U+{(int)character:X4}"));
        }
    }

    [Fact]
    public void Encode_IsTheSameOnEveryThread()
    {
        var cases = CodeLinkFixtures.GeneratedCases.Where(@case => @case.Status == "ok" && @case.Source.Length < 2_000).ToList();
        var results = new string?[cases.Count];
        Parallel.For(0, cases.Count, i => results[i] = (CodeLink.Encode(cases[i].Source) as CodeLinkEncoding.Link)?.Payload);

        Assert.All(cases.Zip(results), pair => Assert.Equal(pair.First.Payload, pair.Second));
    }

    // ── The frozen parts of format 1 ────────────────────────────────────────

    /// <summary>
    /// The primer is part of the format: every format-1 link depends on its exact bytes, so it
    /// is pinned here. Changing it makes a new format, which only the owner decides; never edit
    /// the file, not even to follow a language change.
    /// </summary>
    [Fact]
    public void Primer_IsTheFrozenOne()
    {
        var primer = CodeLinkModel.Primer;

        Assert.Equal(15_102, primer.Length);
        Assert.Equal("71cf25503940d337838bc2e4d58c21880eb27e22e8a14335bb95b165fa489fdf", Convert.ToHexStringLower(SHA256.HashData(primer)));
        Assert.StartsWith("# KatLang code link primer, format 1. Frozen", Encoding.ASCII.GetString(primer), StringComparison.Ordinal);
    }

    [Fact]
    public void SquashPoints_AreTheLogisticFunctionRounded()
    {
        var points = CodeLinkModel.SquashPoints.ToArray();

        Assert.Equal(65, points.Length);
        for (var i = 0; i < points.Length; i++)
        {
            var exact = 4096.0 / (1.0 + Math.Exp(-(i - 32) / 4.0));
            Assert.Equal((int)Math.Clamp(Math.Round(exact, MidpointRounding.AwayFromZero), 1, 4095), points[i]);
        }
    }

    [Fact]
    public void SquashAndStretch_AreMonotoneInverses()
    {
        Assert.Equal(1, CodeLinkModel.Squash(-5000));
        Assert.Equal(2048, CodeLinkModel.Squash(0));
        Assert.Equal(4095, CodeLinkModel.Squash(5000));

        for (var d = -2046; d <= 2047; d++)
            Assert.True(CodeLinkModel.Squash(d - 1) <= CodeLinkModel.Squash(d), $"squash decreases at {d}");

        for (var p = 1; p < 4096; p++)
        {
            Assert.True(CodeLinkModel.Stretch(p - 1) <= CodeLinkModel.Stretch(p), $"stretch decreases at {p}");
            Assert.InRange(CodeLinkModel.Stretch(p), -2047, 2047);
        }

        for (var d = -2047; d <= 2047; d++)
            Assert.True(CodeLinkModel.Stretch(CodeLinkModel.Squash(d)) <= d, $"stretch(squash({d})) is above {d}");
    }

    [Fact]
    public void Crc32_IsTheIsoHdlcCrc()
    {
        Assert.Equal(0xCBF43926u, CodeLinkFormat.Crc32("123456789"u8));
        Assert.Equal(0u, CodeLinkFormat.Crc32([]));
    }

    [Fact]
    public void Wtf8_IsUtf8_WithEverySurrogateItsOwnCodePoint()
    {
        Assert.Equal(
            Convert.FromHexString("EDA08061F09F9880EDB080"),
            Wtf8.Encode("\uD800a😀\uDC00"));

        foreach (var @case in CodeLinkFixtures.GeneratedCases.Where(@case => !HasUnpairedSurrogate(@case.Source)))
            Assert.Equal(Encoding.UTF8.GetBytes(@case.Source), Wtf8.Encode(@case.Source));
    }

    [Fact]
    public void Encode_AnUnpairedSurrogate_IsCarriedExactly()
    {
        var link = Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode("\uD800"));

        Assert.Equal("gAAkpZYNE", link.Payload);
        Assert.Equal("\uD800", Assert.IsType<CodeLinkDecoding.Program>(CodeLink.Decode(1, link.Payload)).Source);
    }

    // ── The results ─────────────────────────────────────────────────────────

    [Fact]
    public void Results_AreValuesOfTheirPayloads()
    {
        Assert.Equal(CodeLink.Encode("1 + 2"), CodeLink.Encode("1 + 2"));
        Assert.NotEqual(CodeLink.Encode("1 + 2"), CodeLink.Encode("1 + 3"));
        Assert.Equal(CodeLink.Encode(""), CodeLink.Encode(""));
        Assert.Equal(CodeLink.Encode(new string('a', 20_001)), CodeLink.Encode(new string('b', 20_001)));
        Assert.NotEqual(CodeLink.Encode(new string('a', 20_001)), CodeLink.Encode(new string('a', 20_002)));
        Assert.NotEqual<CodeLinkEncoding>(CodeLink.Encode(""), CodeLink.Encode(new string('a', 20_001)));
    }

    [Fact]
    public void Results_AreExhaustivelySwitchable_WithNoCatchAll()
    {
        static string Describe(CodeLinkEncoding encoding) => encoding switch
        {
            CodeLinkEncoding.Link link => $"link {link.Payload}",
            CodeLinkEncoding.EmptyProgram => "empty",
            CodeLinkEncoding.SourceTooLong tooLong => $"source {tooLong.SourceLength}",
            CodeLinkEncoding.PayloadTooLong tooLong => $"payload {tooLong.PayloadLength}",
        };

        Assert.Equal("link ML4", Describe(CodeLink.Encode("1")));
        Assert.Equal("empty", Describe(CodeLink.Encode("")));
        Assert.Equal("source 20001", Describe(CodeLink.Encode(new string('a', 20_001))));
        Assert.Equal("payload 1971", Describe(CodeLink.Encode(CodeLinkFixtures.Generated("payload-1971").Source)));
    }

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
}
