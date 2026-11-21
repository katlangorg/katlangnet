namespace KatLang.Tests.CodeLinks;

/// <summary>
/// The code-link decoder (<see cref="CodeLink.Decode"/>, <see cref="CodeLink.TryGetPayload"/>
/// and <see cref="CodeLink.DecodeLink"/>) against the verdicts of the format's reference
/// decoder (<see cref="CodeLinkDecodeFixtures"/>): a link is accepted exactly when the reference
/// accepts it, with exactly the reference's program, and refused at the reference's check
/// otherwise.
/// </summary>
public sealed class CodeLinkDecodingTests
{
    /// <summary>The documented link's payload: <c>https://katlang.org/#1/4MWjDBlNE4PH</c>.</summary>
    private const string DocumentedPayload = "4MWjDBlNE4PH";

    private const string DocumentedLink = "https://katlang.org/#1/" + DocumentedPayload;

    private const string DocumentedSource = "100 - 3 * 5 ^ 2";

    public static TheoryData<string> VectorNames => CodeLinkFixtures.Names(CodeLinkFixtures.Vectors);

    public static TheoryData<string> GeneratedCaseNames => CodeLinkFixtures.Names(CodeLinkFixtures.GeneratedCases);

    public static TheoryData<string> OracleCaseNames => Names(CodeLinkDecodeFixtures.Cases.Select(@case => @case.Name));

    public static TheoryData<string> TruncationBaseNames => Names(CodeLinkDecodeFixtures.Truncations.Select(family => family.Base.Name));

    public static TheoryData<string> MutationBaseNames => Names(CodeLinkDecodeFixtures.Mutations.Select(family => family.Base.Name));

    // ── The oracle ──────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(OracleCaseNames))]
    public void OracleCase_GetsTheReferencesVerdict(string name)
    {
        var @case = CodeLinkDecodeFixtures.Case(name);
        if (!@case.IsLink)
        {
            Assert.Null(@case.Verdict.Mismatch(CodeLink.Decode(@case.Format, @case.Input)));
            return;
        }

        var found = CodeLink.TryGetPayload(@case.Input, out var format, out var payload);
        Assert.Equal(@case.LinkPayload is not null, found);
        if (found)
        {
            Assert.Equal(@case.LinkFormat, format);
            Assert.Equal(@case.LinkPayload, payload);
        }

        var decoding = CodeLink.DecodeLink(@case.Input);
        Assert.Null(@case.Verdict.Mismatch(decoding));
        if (found)
            Assert.Equal(CodeLink.Decode(format, payload!), decoding);
    }

    /// <summary>
    /// Proper prefixes of a payload: what a chat app or a mail client leaves of a link it cut.
    /// The reference refused every sampled one.
    /// </summary>
    [Theory]
    [MemberData(nameof(TruncationBaseNames))]
    public void EveryPrefixOfAPayload_GetsTheReferencesVerdict(string baseName)
    {
        var family = CodeLinkDecodeFixtures.TruncationsOf(baseName);
        var payload = family.Base.Payload;
        Assert.Equal(payload.Length - 1, family.Verdicts.Length);

        var mismatches = new List<string>();
        for (var length = 1; length < payload.Length && mismatches.Count < 10; length++)
        {
            var letter = family.Verdicts[length - 1];
            if (letter == '.')
                continue;

            var expected = letter switch
            {
                'K' => family.Accepted[length],
                'D' => Refusal(CodeLinkRefusal.Damaged),
                'N' => Refusal(CodeLinkRefusal.NotCanonical),
                'S' => Refusal(CodeLinkRefusal.SourceTooLong),
                _ => throw new InvalidDataException($"Unknown verdict letter '{letter}' in the truncations of '{baseName}'."),
            };

            if (expected.Mismatch(CodeLink.Decode(1, payload[..length])) is { } mismatch)
                mismatches.Add($"the first {length} of {payload.Length} characters: {mismatch}");
        }

        Assert.Empty(mismatches);

        // And the whole payload is its program.
        Assert.Equal(family.Base.Source, Assert.IsType<CodeLinkDecoding.Program>(CodeLink.Decode(1, payload)).Source);
    }

    /// <summary>
    /// One character replaced or deleted: refused, as damaged, or as a payload that decodes but
    /// is not its program's own.
    /// </summary>
    [Theory]
    [MemberData(nameof(MutationBaseNames))]
    public void EditedPayload_GetsTheReferencesVerdict(string baseName)
    {
        var family = CodeLinkDecodeFixtures.MutationsOf(baseName);

        var mismatches = new List<string>();
        foreach (var edit in family.Edits)
        {
            if (edit.Verdict.Mismatch(CodeLink.Decode(1, edit.Apply(family.Base.Payload))) is { } mismatch)
                mismatches.Add($"character {edit.At} {(edit.To is null ? "deleted" : $"replaced by '{edit.To}'")}: {mismatch}");
        }

        Assert.Empty(mismatches);
    }

    [Theory]
    [MemberData(nameof(GeneratedCaseNames))]
    public void EncoderCase_DecodesToItsSource_OrHasNoLinkToDecode(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        switch (@case.Status)
        {
            case "ok":
                // The round trip: every program with a link is exactly what its payload carries.
                Assert.Equal(@case.Source, Assert.IsType<CodeLinkDecoding.Program>(CodeLink.Decode(1, @case.Payload)).Source);
                break;
            case "payloadTooLong":
                Assert.Equal(CodeLinkRefusal.PayloadTooLong, Assert.IsType<CodeLinkDecoding.Refused>(CodeLink.Decode(1, @case.Payload)).Reason);
                break;
            case "sourceTooLong":
            case "empty":
                Assert.Equal("", @case.Payload);
                break;
            default:
                throw new InvalidDataException($"Unknown reference verdict '{@case.Status}' for '{name}'.");
        }
    }

    [Theory]
    [MemberData(nameof(VectorNames))]
    public void Vector_DecodesToItsSource(string name)
    {
        var vector = CodeLinkFixtures.Vector(name);

        Assert.Equal(vector.Source, Assert.IsType<CodeLinkDecoding.Program>(CodeLink.Decode(1, vector.Payload)).Source);
        Assert.True(CodeLink.TryGetPayload(vector.Url!, out var format, out var payload));
        Assert.Equal((1, vector.Payload), (format, payload));
        Assert.Equal(vector.Source, Assert.IsType<CodeLinkDecoding.Program>(CodeLink.DecodeLink(vector.Url!)).Source);
    }

    [Fact]
    public void Oracle_CoversWhatADecoderMustAcceptAndRefuse()
    {
        var cases = CodeLinkDecodeFixtures.Cases;
        var counts = CodeLinkDecodeFixtures.StatedCounts;

        Assert.Equal(cases.Count, cases.Select(@case => @case.Name).Distinct(StringComparer.Ordinal).Count());
        foreach (var kind in cases.Select(@case => @case.Kind).Distinct())
            Assert.Equal(counts[kind], cases.Count(@case => @case.Kind == kind));

        var truncations = CodeLinkDecodeFixtures.Truncations.Sum(family => family.Verdicts.Count(letter => letter != '.'));
        var mutations = CodeLinkDecodeFixtures.Mutations.Sum(family => family.Edits.Count);
        Assert.Equal(counts["truncations"], truncations);
        Assert.Equal(counts["mutations"], mutations);
        Assert.Equal(counts["total"], cases.Count + truncations + mutations);
        Assert.True(counts["total"] >= 2_000, $"the oracle holds {counts["total"]} inputs");

        // Every refusal the decoder can give, and programs, are among the expectations.
        var reasons = cases.Select(@case => @case.Verdict.Refusal)
            .Concat(CodeLinkDecodeFixtures.Mutations.SelectMany(family => family.Edits.Select(edit => edit.Verdict.Refusal)))
            .ToHashSet();
        Assert.Equal(
            Enum.GetValues<CodeLinkRefusal>().Cast<CodeLinkRefusal?>().Append(null).Order(),
            reasons.Order());

        // Every kind of damage is covered, every character outside the alphabet, and formats
        // this KatLang does not read.
        foreach (var kind in new[] { "length", "alphabet", "format", "check", "tail", "wtf8", "limit", "random", "link" })
            Assert.Contains(cases, @case => @case.Kind == kind);
        Assert.All(cases.Where(@case => @case.Kind == "format"), @case => Assert.NotEqual(1, @case.Format));
        for (var character = ' '; character < (char)0x7F; character++)
        {
            if (CodeLinkFormat.DigitOf(character) < 0)
                Assert.Contains(cases, @case => @case.Kind == "alphabet" && @case.Input.Contains(character));
        }

        // The bases span short and long payloads, both limits, and unpaired surrogates.
        var bases = CodeLinkDecodeFixtures.Truncations.Select(family => family.Base).ToList();
        Assert.Contains(bases, @base => @base.Payload.Length == CodeLink.MaxPayloadLength);
        Assert.Contains(bases, @base => @base.Source.Length == CodeLink.MaxSourceLength);
        Assert.Contains(bases, @base => @base.Payload.Length < 10);
        Assert.Contains(bases, @base => HasUnpairedSurrogate(@base.Source));
    }

    // ── Bounded work ────────────────────────────────────────────────────────

    /// <summary>
    /// The longest program in bytes (20,000 three-byte characters) is decoded and re-encoded with
    /// one model state each: the work is linear, and the memory a few megabytes.
    /// </summary>
    [Fact]
    public void Decode_OfTheMostBytesAProgramCanHave_IsBounded()
    {
        var payload = CodeLinkDecodeFixtures.Case("crafted-20000-euro").Input;
        _ = CodeLink.Decode(1, DocumentedPayload);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var decoding = CodeLink.Decode(1, payload);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        var program = Assert.IsType<CodeLinkDecoding.Program>(decoding);
        Assert.Equal(new string('€', CodeLink.MaxSourceLength), program.Source);
        // The two sets of model tables cost 6,029,312 bytes. The remaining space covers the
        // histories, byte and text buffers, and GC counter variation. A third set cannot fit.
        Assert.True(allocated < 7 * 1024 * 1024, $"decoding {payload.Length} characters allocated {allocated} bytes");
    }

    /// <summary>
    /// A stream announcing more bytes than any program can have is refused before anything is
    /// decoded, and one whose program grows past the source limit is refused at that byte.
    /// </summary>
    [Theory]
    [InlineData("crafted-20001-euro")]
    [InlineData("crafted-length-60001")]
    [InlineData("crafted-length-65536")]
    public void Decode_OfAStreamAnnouncingTooManyBytes_DecodesNothing(string name)
    {
        var payload = CodeLinkDecodeFixtures.Case(name).Input;
        _ = CodeLink.Decode(1, DocumentedPayload);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var decoding = CodeLink.Decode(1, payload);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal(CodeLinkRefusal.SourceTooLong, Assert.IsType<CodeLinkDecoding.Refused>(decoding).Reason);
        Assert.True(allocated < 64 * 1024, $"refusing {name} allocated {allocated} bytes");
    }

    [Theory]
    [InlineData("crafted-20001-a", CodeLinkRefusal.SourceTooLong)]
    [InlineData("crafted-10001-emoji", CodeLinkRefusal.SourceTooLong)]
    [InlineData("crafted-length-60000-of-3-bytes", CodeLinkRefusal.Damaged)]
    public void Decode_StopsAtTheFirstByteThatCannotBelongToALink(string name, CodeLinkRefusal reason)
    {
        var payload = CodeLinkDecodeFixtures.Case(name).Input;
        _ = CodeLink.Decode(1, DocumentedPayload);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var decoding = CodeLink.Decode(1, payload);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal(reason, Assert.IsType<CodeLinkDecoding.Refused>(decoding).Reason);
        // The decoder needs one set of tables (3,014,656 bytes) plus buffers. Starting the
        // canonical re-encode after this refusal would allocate another set.
        Assert.True(allocated < 4 * 1024 * 1024, $"refusing {name} allocated {allocated} bytes");
    }

    [Theory]
    // Three reference stream digits carry a truncated length field. Only the second prefix
    // has the 16th leading zero that decides SourceTooLong before the rest of the field.
    [InlineData("__7", CodeLinkRefusal.Damaged)]
    [InlineData("__9", CodeLinkRefusal.SourceTooLong)]
    // Reference streams for 20,000 or 20,001 ASCII 'a' bytes followed by 0xFF. The last byte
    // is invalid in both. Only the second stream must stop before reading it.
    [InlineData("__2O8I9GolghMVOv6xtpKx3vGd", CodeLinkRefusal.Damaged)]
    [InlineData("__2O6I9GolghMVOv6xtpK9fqHPY", CodeLinkRefusal.SourceTooLong)]
    public void Decode_ReportsTheFirstFailureInStreamOrder(string payload, CodeLinkRefusal reason)
        => Assert.Equal(reason, Assert.IsType<CodeLinkDecoding.Refused>(CodeLink.Decode(1, payload)).Reason);

    [Fact]
    public void DecodeLink_OfAnOversizedPayload_IsRefusedWithoutCopyingIt()
    {
        var link = "https://katlang.org/#1/" + new string('A', 1_000_000);
        _ = CodeLink.Decode(1, DocumentedPayload);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var result = CodeLink.DecodeLink(link);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal(CodeLinkRefusal.PayloadTooLong, Assert.IsType<CodeLinkDecoding.Refused>(result).Reason);
        Assert.True(allocated < 64 * 1024, $"refusing a link of {link.Length} characters allocated {allocated} bytes");
    }

    [Fact]
    public void Decode_IsTheSameOnEveryThread()
    {
        var cases = CodeLinkFixtures.GeneratedCases.Where(@case => @case.Status == "ok" && @case.Source.Length < 2_000).ToList();
        var results = new string?[cases.Count];
        Parallel.For(0, cases.Count, i => results[i] = (CodeLink.Decode(1, cases[i].Payload) as CodeLinkDecoding.Program)?.Source);

        Assert.All(cases.Zip(results), pair => Assert.Equal(pair.First.Source, pair.Second));
    }

    // ── Links ───────────────────────────────────────────────────────────────

    [Theory]
    [InlineData(DocumentedLink, 1, DocumentedPayload)]
    [InlineData("http://localhost:5218/#1/" + DocumentedPayload, 1, DocumentedPayload)]
    [InlineData("https://katlang.org/examples#1/" + DocumentedPayload, 1, DocumentedPayload)]
    [InlineData("https://katlang.org/?utm_source=chat&x=1#1/" + DocumentedPayload, 1, DocumentedPayload)]
    [InlineData("#1/" + DocumentedPayload, 1, DocumentedPayload)]
    [InlineData("https://katlang.org/#1/", 1, "")]
    [InlineData("https://katlang.org/#1/abc#def", 1, "abc#def")]
    [InlineData("https://katlang.org/#1/a b%2Bc", 1, "a b%2Bc")]
    [InlineData("https://katlang.org/#1/1/abc", 1, "1/abc")]
    [InlineData("https://katlang.org/#2/abc", 2, "abc")]
    [InlineData("https://katlang.org/#10/abc", 10, "abc")]
    [InlineData("https://katlang.org/#999999999/abc", 999_999_999, "abc")]
    [InlineData("https://katlang.org/", null, null)]
    [InlineData("https://katlang.org/1/" + DocumentedPayload, null, null)]
    [InlineData("https://katlang.org/#", null, null)]
    [InlineData("https://katlang.org/#1", null, null)]
    [InlineData("https://katlang.org/#/" + DocumentedPayload, null, null)]
    [InlineData("https://katlang.org/#0/" + DocumentedPayload, null, null)]
    [InlineData("https://katlang.org/#01/" + DocumentedPayload, null, null)]
    [InlineData("#\uFF11/" + DocumentedPayload, null, null)]
    [InlineData("#1\u0660/" + DocumentedPayload, null, null)]
    [InlineData("https://katlang.org/#1000000000/" + DocumentedPayload, null, null)]
    [InlineData("https://katlang.org/#+1/" + DocumentedPayload, null, null)]
    [InlineData("https://katlang.org/# 1/" + DocumentedPayload, null, null)]
    [InlineData("https://katlang.org/#c1/" + DocumentedPayload, null, null)]
    [InlineData("https://katlang.org/#code/IwBhAIFpwZnAqcBWcA9cAmIA", null, null)]
    [InlineData("https://katlang.org/#share/" + DocumentedPayload, null, null)]
    [InlineData("https://katlang.org/#x#1/" + DocumentedPayload, null, null)]
    [InlineData(DocumentedPayload, null, null)]
    [InlineData("", null, null)]
    public void TryGetPayload_ReadsTheFormatAndThePayloadOfTheFragment(string link, int? format, string? payload)
    {
        var found = CodeLink.TryGetPayload(link, out var actualFormat, out var actualPayload);

        Assert.Equal(payload is not null, found);
        Assert.Equal(payload, actualPayload);
        Assert.Equal(format ?? 0, actualFormat);
    }

    [Theory]
    [InlineData(DocumentedLink)]
    [InlineData("http://localhost:5218/#1/" + DocumentedPayload)]
    [InlineData("https://katlang.org/examples#1/" + DocumentedPayload)]
    [InlineData("https://katlang.org/?utm_source=chat&x=1#1/" + DocumentedPayload)]
    public void DecodeLink_ReadsOnlyTheFragment_WhateverTheOriginPathAndQuery(string link)
        => Assert.Equal(DocumentedSource, Assert.IsType<CodeLinkDecoding.Program>(CodeLink.DecodeLink(link)).Source);

    [Theory]
    [InlineData("https://katlang.org/", CodeLinkRefusal.NotACodeLink)]
    [InlineData("https://katlang.org/#code/IwBhAIFpwZnAqcBWcA9cAmIA", CodeLinkRefusal.NotACodeLink)]
    [InlineData("https://katlang.org/#c1/" + DocumentedPayload, CodeLinkRefusal.NotACodeLink)]
    [InlineData("https://katlang.org/#2/" + DocumentedPayload, CodeLinkRefusal.UnsupportedVersion)]
    [InlineData("https://katlang.org/#2/", CodeLinkRefusal.UnsupportedVersion)]
    [InlineData("https://katlang.org/#1/", CodeLinkRefusal.EmptyPayload)]
    [InlineData(DocumentedLink + "#x", CodeLinkRefusal.InvalidCharacter)]
    [InlineData(DocumentedLink + "%41", CodeLinkRefusal.InvalidCharacter)]
    [InlineData("https://katlang.org/#1/4MWjDBlNE4P", CodeLinkRefusal.Damaged)]
    [InlineData("https://katlang.org/#1/A", CodeLinkRefusal.Damaged)]
    [InlineData(DocumentedLink + "A", CodeLinkRefusal.NotCanonical)]
    public void DecodeLink_RefusesWithTheFirstCheckThatFails(string link, CodeLinkRefusal reason)
        => Assert.Equal(reason, Assert.IsType<CodeLinkDecoding.Refused>(CodeLink.DecodeLink(link)).Reason);

    [Theory]
    [InlineData(1, CodeLinkRefusal.PayloadTooLong)]
    [InlineData(2, CodeLinkRefusal.UnsupportedVersion)]
    public void FormatAndLengthChecks_PrecedeAlphabetValidation(int format, CodeLinkRefusal reason)
    {
        var payload = new string('%', CodeLink.MaxPayloadLength + 1);
        Assert.Equal(reason, Assert.IsType<CodeLinkDecoding.Refused>(CodeLink.Decode(format, payload)).Reason);
        Assert.Equal(reason, Assert.IsType<CodeLinkDecoding.Refused>(CodeLink.DecodeLink($"#{format}/{payload}")).Reason);
    }

    [Fact]
    public void DecodeLink_ReadsTheLinkAsGiven_WithNothingTrimmedOrDecoded()
    {
        Assert.Equal(
            CodeLinkRefusal.InvalidCharacter,
            Assert.IsType<CodeLinkDecoding.Refused>(CodeLink.DecodeLink(DocumentedLink + " ")).Reason);
        Assert.Equal(
            CodeLinkRefusal.InvalidCharacter,
            Assert.IsType<CodeLinkDecoding.Refused>(CodeLink.DecodeLink(DocumentedLink + "\n")).Reason);

        // A space before the fragment is part of the origin, which is not read.
        Assert.Equal(DocumentedSource, Assert.IsType<CodeLinkDecoding.Program>(CodeLink.DecodeLink(" " + DocumentedLink)).Source);
    }

    // ── Arguments and results ───────────────────────────────────────────────

    [Fact]
    public void NullArguments_AreRejected()
    {
        Assert.Equal("payload", Assert.Throws<ArgumentNullException>(() => CodeLink.Decode(1, null!)).ParamName);
        Assert.Equal("link", Assert.Throws<ArgumentNullException>(() => CodeLink.TryGetPayload(null!, out _, out _)).ParamName);
        Assert.Equal("link", Assert.Throws<ArgumentNullException>(() => CodeLink.DecodeLink(null!)).ParamName);
    }

    [Fact]
    public void Results_AreValuesOfTheirPayloads()
    {
        var program = Assert.IsType<CodeLinkDecoding.Program>(CodeLink.Decode(1, DocumentedPayload));
        Assert.Equal(DocumentedSource, program.Source);
        Assert.Equal(program, CodeLink.DecodeLink("http://localhost:5218/#1/" + DocumentedPayload));
        Assert.NotEqual(program, CodeLink.Decode(1, "ML4"));

        var refused = Assert.IsType<CodeLinkDecoding.Refused>(CodeLink.Decode(1, ""));
        Assert.Equal(CodeLinkRefusal.EmptyPayload, refused.Reason);
        Assert.Equal(refused, CodeLink.DecodeLink("#1/"));
        Assert.NotEqual(refused, CodeLink.Decode(2, "ML4"));
        Assert.NotEqual<CodeLinkDecoding>(program, refused);
    }

    [Fact]
    public void Results_AreExhaustivelySwitchable_WithNoCatchAll()
    {
        static string Describe(CodeLinkDecoding decoding) => decoding switch
        {
            CodeLinkDecoding.Program program => $"program {program.Source}",
            CodeLinkDecoding.Refused refused => $"refused {refused.Reason}",
        };

        Assert.Equal("program 1", Describe(CodeLink.Decode(1, "ML4")));
        Assert.Equal("refused Damaged", Describe(CodeLink.Decode(1, "ML")));
        Assert.Equal("refused UnsupportedVersion", Describe(CodeLink.Decode(0, "ML4")));

        // A payload with one digit more decodes to everything, and is refused all the same: it
        // is not the payload of its program.
        Assert.Equal("refused NotCanonical", Describe(CodeLink.Decode(1, "ML4A")));
    }

    [Fact]
    public void Refusals_AreNumberedInTheOrderOfTheChecks()
    {
        CodeLinkRefusal[] inOrder =
        [
            CodeLinkRefusal.NotACodeLink, CodeLinkRefusal.UnsupportedVersion, CodeLinkRefusal.EmptyPayload,
            CodeLinkRefusal.PayloadTooLong, CodeLinkRefusal.InvalidCharacter, CodeLinkRefusal.Damaged,
            CodeLinkRefusal.SourceTooLong, CodeLinkRefusal.NotCanonical,
        ];
        Assert.Equal(inOrder, Enum.GetValues<CodeLinkRefusal>());
        Assert.Equal(Enumerable.Range(0, 8), Enum.GetValues<CodeLinkRefusal>().Select(reason => (int)reason));
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static CodeLinkVerdict Refusal(CodeLinkRefusal reason) => new(reason, null, null, null);

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

    private static TheoryData<string> Names(IEnumerable<string> names)
    {
        var data = new TheoryData<string>();
        foreach (var name in names)
            data.Add(name);
        return data;
    }
}
