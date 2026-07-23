using System.Collections.Immutable;
using System.Globalization;
using KatLang.ParserFuzz;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// Deterministic coverage for the UTF-16 fuzz target (<c>KATLANG_FUZZ_MODE=utf16</c>,
/// <c>fuzz/KatLang.ParserFuzz/Utf16</c>).
///
/// <para>The harness is compiled into this assembly as shared source, so these tests exercise the
/// very decoder, builder, executor, relations and replay driver the campaign runs. Nothing here
/// depends on libFuzzer, SharpFuzz, or a fuzzing loop.</para>
///
/// <para>The parameter space is walked with the same deterministic stratified enumerator the
/// readiness report uses, so "the campaign found nothing" is backed by a sweep that is identical on
/// every machine rather than by a sample that depends on a seed.</para>
/// </summary>
public class Utf16FuzzHarnessTests
{
    private static readonly List<Utf16Parameters> StratifiedPoints = [.. Utf16Space.EnumerateStratified()];

    private static List<Utf16Parameters> Stratified => StratifiedPoints;

    private static string SeedDirectory =>
        Path.Combine(RepoRoot.Find(), "fuzz", "KatLang.ParserFuzz", "Utf16Testcases");

    // ── Decoder ──────────────────────────────────────────────────────────────

    [Fact]
    public void TheSameBytesAlwaysDecodeToTheSameCase()
    {
        foreach (var payload in SamplePayloads())
        {
            var first = Utf16Decoder.Decode(payload);
            var second = Utf16Decoder.Decode(payload);
            Assert.Equal(first, second);

            var builtOnce = Utf16SourceBuilder.Build(first);
            var builtTwice = Utf16SourceBuilder.Build(second);
            Assert.Equal(builtOnce.HexUnits, builtTwice.HexUnits);
        }
    }

    [Fact]
    public void EveryPayloadDecodes_IncludingTheEmptyAndVeryShortOnes()
    {
        // A decoder that rejected short input would make libFuzzer's first mutations useless.
        for (var length = 0; length <= Utf16Decoder.HeaderBytes + 4; length++)
        {
            var payload = new byte[length];
            for (var i = 0; i < length; i++) payload[i] = (byte)(i * 29);

            var parameters = Utf16Decoder.Decode(payload);
            var built = Utf16SourceBuilder.Build(parameters);
            Assert.NotNull(built.Source);
            Assert.Equal(built.Source.Length, built.CodeUnits.Length);
        }
    }

    [Fact]
    public void ALargePayloadDecodesExactlyLikeItsBoundedPrefix()
    {
        var huge = new byte[1024 * 1024];
        for (var i = 0; i < huge.Length; i++) huge[i] = (byte)(i * 131 % 251);

        var prefix = huge.AsSpan(0, Utf16Decoder.MaxPayloadPrefixBytes).ToArray();
        Assert.Equal(Utf16Decoder.Decode(prefix), Utf16Decoder.Decode(huge));

        // And nothing the harness allocates grows with the payload.
        var built = Utf16SourceBuilder.Build(Utf16Decoder.Decode(huge));
        Assert.True(
            built.CodeUnits.Length <= Utf16Tables.MaxSourceCodeUnits,
            $"A 1 MiB payload built a {built.CodeUnits.Length}-code-unit source.");
    }

    [Fact]
    public void NoGeneratedSourceEverExceedsTheCap()
    {
        var worst = 0;
        foreach (var parameters in Stratified)
            worst = Math.Max(worst, Utf16SourceBuilder.Build(parameters).CodeUnits.Length);

        Assert.True(worst <= Utf16Tables.MaxSourceCodeUnits, $"Worst source was {worst} code units.");

        // The cap is meant to be unreachable headroom, not a working limit that silently truncates.
        Assert.True(worst < Utf16Tables.MaxSourceCodeUnits / 2, $"Worst source was {worst} code units.");
    }

    [Fact]
    public void EveryPointRoundTripsThroughItsCanonicalPayload()
    {
        foreach (var parameters in Stratified)
        {
            var payload = Utf16Decoder.Encode(parameters);
            Assert.Equal(parameters, Utf16Decoder.Decode(payload));
            Assert.True(
                payload.Length <= Utf16Decoder.MaxPayloadPrefixBytes,
                $"Canonical payload is {payload.Length} bytes, over the bounded prefix.");
        }
    }

    [Fact]
    public void NormalizationIsIdempotentAndCollapsesOnlyIgnoredDimensions()
    {
        foreach (var payload in SamplePayloads())
        {
            var once = Utf16Decoder.Decode(payload);
            var twice = Utf16Decoder.Normalize(once);
            Assert.Equal(once, twice);
            Assert.Equal(once, Utf16Decoder.Normalize(twice));

            // A structured template carries no raw tail; a raw one draws nothing from the groups.
            if (Utf16Tables.IsRaw(once.Template))
            {
                Assert.Equal(Utf16CodeUnitGroup.Basic, once.Group);
                Assert.Equal(0, once.Member);
            }
            else
            {
                Assert.True(once.RawUnits.IsEmpty);
            }

            if (!Utf16Decoder.UsesFiller(once.Placement)) Assert.Equal(0, once.Filler);
        }
    }

    [Fact]
    public void TheDecoderGeneratesValidPairs_IsolatedSurrogates_AndExactCrLf()
    {
        var seen = new HashSet<Utf16SurrogateClass>();
        var sawCr = false;
        var sawLf = false;
        var sawNul = false;

        foreach (var parameters in Stratified)
        {
            var built = Utf16SourceBuilder.Build(parameters);
            seen.Add(built.SurrogateClass);
            foreach (var unit in built.CodeUnits)
            {
                if (unit == 0x000D) sawCr = true;
                if (unit == 0x000A) sawLf = true;
                if (unit == 0x0000) sawNul = true;
            }
        }

        Assert.Contains(Utf16SurrogateClass.WellFormedPairs, seen);
        Assert.Contains(Utf16SurrogateClass.IsolatedHigh, seen);
        Assert.Contains(Utf16SurrogateClass.IsolatedLow, seen);
        Assert.Contains(Utf16SurrogateClass.IsolatedMixed, seen);
        Assert.Contains(Utf16SurrogateClass.None, seen);
        Assert.True(sawCr && sawLf && sawNul, $"cr={sawCr} lf={sawLf} nul={sawNul}");
    }

    [Fact]
    public void CarriageReturnAndLineFeedAreNeverConflated()
    {
        var parameters = Utf16Decoder.Decode(Utf16Decoder.Encode(new Utf16Parameters(
            Utf16TemplateKind.IdentifierStart, Utf16PlacementKind.Alone, Utf16LineEndingMode.Lf,
            Utf16ExecutionMode.ParseSyntax, Utf16CodeUnitGroup.Basic, 0, 1, 0, [])));

        var lf = Utf16SourceBuilder.BuildWithLineEndings(parameters, Utf16LineEndingMode.Lf);
        var crlf = Utf16SourceBuilder.BuildWithLineEndings(parameters, Utf16LineEndingMode.Crlf);
        var cr = Utf16SourceBuilder.BuildWithLineEndings(parameters, Utf16LineEndingMode.LoneCr);

        Assert.Contains("000A", lf.HexUnits, StringComparison.Ordinal);
        Assert.DoesNotContain("000D", lf.HexUnits, StringComparison.Ordinal);
        Assert.Contains("000D 000A", crlf.HexUnits, StringComparison.Ordinal);
        Assert.Contains("000D", cr.HexUnits, StringComparison.Ordinal);
        Assert.DoesNotContain("000A", cr.HexUnits, StringComparison.Ordinal);

        // All three are genuinely different sources — the modes are not cosmetic.
        Assert.NotEqual(lf.HexUnits, crlf.HexUnits);
        Assert.NotEqual(lf.HexUnits, cr.HexUnits);
        Assert.NotEqual(crlf.HexUnits, cr.HexUnits);
    }

    [Fact]
    public void CodeUnitsSurviveTheStringRoundTripExactly()
    {
        // The whole target rests on this: a .NET string IS a code-unit sequence, so building one
        // from ill-formed UTF-16 and reading it back must not normalize or replace anything.
        foreach (var parameters in Stratified)
        {
            var built = Utf16SourceBuilder.Build(parameters);
            Assert.Equal(built.HexUnits, Utf16CodeUnits.ToHex(Utf16CodeUnits.FromString(built.Source)));
            Assert.Equal(built.CodeUnits.Length, built.Source.Length);

            // A replacement character may appear only where the case actually asked for one.
            var asked = built.Parameters.RawUnits.Contains((ushort)0xFFFD)
                        || (!Utf16Tables.IsRaw(built.Parameters.Template)
                            && Utf16Tables.MembersOf(built.Parameters.Group)[built.Parameters.Member]
                                .Units.Contains((ushort)0xFFFD));
            if (!asked) Assert.DoesNotContain('\uFFFD', built.Source);
        }
    }

    [Fact]
    public void AnIsolatedSurrogateIsNeverRewrittenByTheHarness()
    {
        // The failure this guards against is silent: route the units through UTF-8 anywhere — a
        // file, a manifest, an encoder — and D83D becomes FFFD with nothing reporting it.
        var parameters = new Utf16Parameters(
            Utf16TemplateKind.StringLiteral, Utf16PlacementKind.Alone, Utf16LineEndingMode.Lf,
            Utf16ExecutionMode.StringBridge, Utf16CodeUnitGroup.Surrogates, IndexOfMember(Utf16CodeUnitGroup.Surrogates, "high-alone"),
            1, 0, []);

        var built = Utf16SourceBuilder.Build(parameters);
        Assert.Contains("D83D", built.HexUnits, StringComparison.Ordinal);
        Assert.DoesNotContain("FFFD", built.HexUnits, StringComparison.Ordinal);

        // ... and it survives the canonical payload round trip the corpus and seeds rely on.
        var again = Utf16SourceBuilder.Build(Utf16Decoder.Decode(Utf16Decoder.Encode(parameters)));
        Assert.Equal(built.HexUnits, again.HexUnits);
    }

    private static int IndexOfMember(Utf16CodeUnitGroup group, string id)
    {
        var members = Utf16Tables.MembersOf(group);
        for (var i = 0; i < members.Length; i++)
            if (string.Equals(members[i].Id, id, StringComparison.Ordinal)) return i;
        throw new InvalidOperationException($"No member '{id}' in group {group}.");
    }

    [Fact]
    public void DecoderArithmeticIsChecked()
    {
        // Repeat and tail length are the only multiplications, and both are table-bounded.
        Assert.True(Utf16Decoder.MaxRepeat * Utf16Tables.MaxRawAlphabetUnits * 3 < Utf16Tables.MaxSourceCodeUnits);

        // A payload whose bytes are all 0xFF must still land inside every table.
        var saturated = Enumerable.Repeat((byte)0xFF, Utf16Decoder.MaxPayloadPrefixBytes * 2).ToArray();
        var parameters = Utf16Decoder.Decode(saturated);
        Assert.InRange((int)parameters.Template, 0, Utf16Tables.Templates.Length - 1);
        Assert.InRange(parameters.Member, 0, Utf16Tables.MembersOf(parameters.Group).Length - 1);
        Assert.InRange(parameters.Repeat, Utf16Decoder.MinRepeat, Utf16Decoder.MaxRepeat);
        Assert.InRange(parameters.Filler, 0, Utf16Tables.FillerLetters.Length - 1);
    }

    // ── Replay ───────────────────────────────────────────────────────────────

    [Fact]
    public void TrackedSeedsAreWellFormedAndCoverTheRequiredCases()
    {
        var problems = new List<string>();
        var seeds = LoadSeeds(problems);

        Assert.Empty(problems);
        Assert.True(seeds.Count >= 26, $"Only {seeds.Count} tracked seed(s).");

        var templates = seeds.Select(s => s.DeclaredTemplate).ToHashSet();
        Assert.Contains(Utf16TemplateKind.StringLiteral, templates);
        Assert.Contains(Utf16TemplateKind.LineComment, templates);
        Assert.Contains(Utf16TemplateKind.IdentifierStart, templates);

        var classes = new HashSet<Utf16SurrogateClass>();
        var lineEndings = new HashSet<Utf16LineEndingMode>();
        var sawNul = false;
        var sawLoneCr = false;
        var sawLineSeparator = false;
        var sawEmptySource = false;

        foreach (var seed in seeds)
        {
            var built = Utf16SourceBuilder.Build(Utf16Decoder.Decode(seed.Payload));
            classes.Add(built.SurrogateClass);
            lineEndings.Add(built.Parameters.LineEndings);
            if (built.CodeUnits.Contains((ushort)0x0000)) sawNul = true;
            if (built.CodeUnits.Contains((ushort)0x2028) || built.CodeUnits.Contains((ushort)0x2029))
                sawLineSeparator = true;
            if (built.Source.Contains('\r', StringComparison.Ordinal)
                && !built.Source.Contains('\n', StringComparison.Ordinal)) sawLoneCr = true;
            if (built.CodeUnits.IsEmpty) sawEmptySource = true;
        }

        Assert.Contains(Utf16SurrogateClass.WellFormedPairs, classes);
        Assert.Contains(Utf16SurrogateClass.IsolatedHigh, classes);
        Assert.Contains(Utf16SurrogateClass.IsolatedLow, classes);
        Assert.Contains(Utf16SurrogateClass.IsolatedMixed, classes);
        Assert.Contains(Utf16LineEndingMode.Crlf, lineEndings);
        Assert.Contains(Utf16LineEndingMode.Lf, lineEndings);
        Assert.Contains(Utf16LineEndingMode.Mixed, lineEndings);
        Assert.True(sawNul, "No tracked seed puts a NUL in the source.");
        Assert.True(sawLoneCr, "No tracked seed produces a lone-CR source.");
        Assert.True(sawLineSeparator, "No tracked seed uses U+2028/U+2029.");
        Assert.True(sawEmptySource, "No tracked seed produces the empty source.");
    }

    [Fact]
    public void EveryTrackedSeedReplaysCleanlyAndTwiceIdentically()
    {
        var problems = new List<string>();
        foreach (var seed in LoadSeeds(problems))
        {
            var first = Utf16Invariants.Run(seed.Payload);
            var second = Utf16Invariants.Run(seed.Payload);
            Assert.Equal(first.Fingerprint, second.Fingerprint);
            Assert.Equal(first.Case.HexUnits, second.Case.HexUnits);
        }

        Assert.Empty(problems);
    }

    [Theory]
    [InlineData("bytes=00 desc=no template field")]
    [InlineData("template=not-a-template bytes=00")]
    [InlineData("template=string-literal desc=no bytes field")]
    [InlineData("template=string-literal bytes=0 desc=odd hex digits")]
    [InlineData("template=string-literal bytes=zz desc=non-hex pair")]
    [InlineData("template=string-literal bytes= desc=empty payload")]
    [InlineData("template=line-comment bytes=06 00 00 03 04 05 00 00 desc=template does not match payload")]
    [InlineData("template=string-literal bytes=06 00 00 03 04 05 00 00 units=0041 desc=units do not match")]
    public void MalformedSeedMetadataIsReportedNotSilentlyAccepted(string line)
    {
        Assert.False(Utf16SeedFile.TryParse(line, "test", 1, out _, out var problem));
        Assert.NotEmpty(problem);
    }

    [Fact]
    public void ARawArtifactReplaysAsItsOwnPayload()
    {
        // libFuzzer writes corpus and crash artifacts as raw bytes; replay must accept exactly that.
        var payload = Utf16Decoder.Encode(Stratified[7]);
        var directory = Path.Combine(Path.GetTempPath(), "katlang-utf16-replay-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(directory);
        try
        {
            File.WriteAllBytes(Path.Combine(directory, "artifact"), payload);
            File.WriteAllBytes(Path.Combine(directory, "empty"), []);

            var exit = Utf16Replay.RunReplay(["utf16-replay", "--raw", directory]);
            Assert.Equal(0, exit);
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void ReplayingNothingIsAFailureNotACleanRun()
    {
        var empty = Path.Combine(Path.GetTempPath(), "katlang-utf16-empty-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(empty);
        try
        {
            Assert.NotEqual(0, Utf16Replay.RunReplay(["utf16-replay", empty]));
            Assert.NotEqual(0, Utf16Replay.RunReplay(["utf16-replay"]));
        }
        finally
        {
            Directory.Delete(empty, recursive: true);
        }
    }

    // ── Span validator: each violation must be caught, not merely usually caught ──

    [Theory]
    [InlineData(0, 1, 1, 1, "start line < 1")]
    [InlineData(1, 0, 1, 1, "start column < 1")]
    [InlineData(1, 1, 0, 1, "end line < 1")]
    [InlineData(1, 1, 1, 0, "end column < 1")]
    [InlineData(2, 1, 1, 1, "end line precedes start line")]
    [InlineData(1, 4, 1, 2, "end column precedes start column")]
    [InlineData(-5, 1, 1, 1, "start line < 1")]
    public void MalformedSpanShapesAreRejected(int startLine, int startColumn, int endLine, int endColumn, string expected)
    {
        var widths = SourceSpanValidator.LineWidths("abc\ndef");
        var reason = SourceSpanValidator.Validate(new SourceSpan(startLine, startColumn, endLine, endColumn), widths);
        Assert.Equal(expected, reason);
    }

    [Fact]
    public void OutOfRangeSpansAreRejectedAgainstTheRealSource()
    {
        var widths = SourceSpanValidator.LineWidths("abc\ndef");     // two lines, width 3 each

        Assert.NotNull(SourceSpanValidator.Validate(new SourceSpan(3, 1, 3, 1), widths));   // line past end
        Assert.NotNull(SourceSpanValidator.Validate(new SourceSpan(1, 1, 3, 1), widths));   // end line past end
        Assert.NotNull(SourceSpanValidator.Validate(new SourceSpan(1, 5, 1, 5), widths));   // column past width+1
        Assert.NotNull(SourceSpanValidator.Validate(new SourceSpan(1, 1, 2, 5), widths));   // end column past width+1
        Assert.NotNull(SourceSpanValidator.Validate(new SourceSpan(int.MaxValue, 1, int.MaxValue, 1), widths));

        // The one-past-end column is the legal EOF / end-exclusive position.
        Assert.Null(SourceSpanValidator.Validate(new SourceSpan(1, 4, 1, 4), widths));
        Assert.Null(SourceSpanValidator.Validate(new SourceSpan(2, 4, 2, 4), widths));
        Assert.Null(SourceSpanValidator.Validate(new SourceSpan(1, 1, 2, 3), widths));      // multiline is legal
    }

    [Fact]
    public void SpanValidationUsesTheDocumentedCarriageReturnAndSurrogateModel()
    {
        // CR is transparent: it occupies no column, so "a\r\nb" has two lines of width 1.
        var crlf = SourceSpanValidator.LineWidths("a\r\nb");
        Assert.Equal([1, 1], crlf);

        // A lone CR is NOT a line break, so "a\rb" is ONE line whose width counts a and b only.
        var loneCr = SourceSpanValidator.LineWidths("a\rb");
        Assert.Equal([2], loneCr);

        // Each half of a surrogate pair is its own column — this parser indexes code units.
        var pair = SourceSpanValidator.LineWidths("\uD83D\uDE00");
        Assert.Equal([2], pair);
        Assert.Null(SourceSpanValidator.Validate(new SourceSpan(1, 1, 1, 2), pair));
        Assert.NotNull(SourceSpanValidator.Validate(new SourceSpan(1, 1, 1, 4), pair));

        // A zero-length span at end of file is legal and must not be flagged.
        var empty = SourceSpanValidator.LineWidths("");
        Assert.Equal([0], empty);
        Assert.Null(SourceSpanValidator.Validate(new SourceSpan(1, 1, 1, 1), empty));
    }

    [Fact]
    public void OffsetToLineColumnMatchesTheWidthModelAtEveryOffset()
    {
        foreach (var source in new[] { "", "a", "a\nb", "a\r\nb", "a\rb", "\uD83D\uDE00\nx", "\n\n\n", "a b" })
        {
            var widths = SourceSpanValidator.LineWidths(source);
            for (var offset = 0; offset <= source.Length; offset++)
            {
                var (line, column) = SourceSpanValidator.LineColumnAt(source, offset);
                Assert.InRange(line, 1, widths.Length);
                Assert.InRange(column, 1, widths[line - 1] + 1);
            }
        }
    }

    // ── Parser and frontend invariants over the whole stratified space ────────

    [Fact]
    public void EveryStratifiedCaseSatisfiesEveryInvariant()
    {
        var failures = new List<string>();
        foreach (var parameters in Stratified)
        {
            var payload = Utf16Decoder.Encode(parameters);
            var phase = Utf16Phase.Build;
            try
            {
                _ = Utf16Invariants.Run(payload, ref phase);
            }
            catch (Exception exception)
            {
                failures.Add(
                    $"[phase={phase}] payload={Convert.ToHexString(payload)} " +
                    $"{exception.GetType().Name}: {exception.Message}");
            }
        }

        Assert.True(failures.Count == 0, string.Join("\n", failures.Take(10)));
    }

    [Fact]
    public void TheHarnessReachesEveryTemplatePlacementModeAndCodeUnitGroup()
    {
        var templates = new HashSet<Utf16TemplateKind>();
        var placements = new HashSet<Utf16PlacementKind>();
        var lineEndings = new HashSet<Utf16LineEndingMode>();
        var executions = new HashSet<Utf16ExecutionMode>();
        var members = new HashSet<(Utf16CodeUnitGroup, int)>();
        var surrogateClasses = new HashSet<Utf16SurrogateClass>();

        foreach (var parameters in Stratified)
        {
            templates.Add(parameters.Template);
            placements.Add(parameters.Placement);
            lineEndings.Add(parameters.LineEndings);
            executions.Add(parameters.ExecutionMode);
            if (!Utf16Tables.IsRaw(parameters.Template)) members.Add((parameters.Group, parameters.Member));
            surrogateClasses.Add(Utf16SourceBuilder.Build(parameters).SurrogateClass);
        }

        Assert.Equal(Utf16Tables.Templates.Length, templates.Count);
        Assert.Equal(Utf16Decoder.PlacementCount, placements.Count);
        Assert.Equal(Utf16Decoder.LineEndingCount, lineEndings.Count);
        Assert.Equal(Utf16Decoder.ExecutionCount, executions.Count);
        Assert.Equal(Enum.GetValues<Utf16SurrogateClass>().Length, surrogateClasses.Count);

        foreach (var group in Enum.GetValues<Utf16CodeUnitGroup>())
        for (var member = 0; member < Utf16Tables.MembersOf(group).Length; member++)
            Assert.Contains((group, member), members);
    }

    [Fact]
    public void EveryRelationIsReachedAndEverySkipReasonIsNamed()
    {
        var ran = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var skipped = new SortedDictionary<string, int>(StringComparer.Ordinal);

        foreach (var parameters in Stratified)
        {
            var report = Utf16Invariants.Run(Utf16Decoder.Encode(parameters));
            foreach (var name in report.Relations.Checked) ran[name] = ran.GetValueOrDefault(name) + 1;
            foreach (var reason in report.Relations.Skipped) skipped[reason] = skipped.GetValueOrDefault(reason) + 1;
        }

        foreach (var relation in new[]
                 {
                     Utf16Relations.CrTransparency, Utf16Relations.LoneCrNotALineBreak,
                     Utf16Relations.TrailingNewlineNeutral, Utf16Relations.ExactStringPreservation,
                 })
        {
            Assert.True(ran.ContainsKey(relation), $"Relation '{relation}' is never reached.");
        }

        // A skip reason is a named precondition, never a silent pass.
        foreach (var reason in skipped.Keys)
        {
            Assert.NotEmpty(reason);
            Assert.DoesNotContain(' ', reason);
        }
    }

    // ── Determinism and isolation ────────────────────────────────────────────

    [Fact]
    public void EveryCaseIsRepeatable_Isolated_AndOrderIndependent()
    {
        var forward = new List<string>(Stratified.Count);
        foreach (var parameters in Stratified)
            forward.Add(Utf16Invariants.Run(Utf16Decoder.Encode(parameters)).Fingerprint);

        // Reversed order: a fingerprint that depends on what ran before it is leaked state.
        var reversed = new List<string>(Stratified.Count);
        for (var i = Stratified.Count - 1; i >= 0; i--)
            reversed.Add(Utf16Invariants.Run(Utf16Decoder.Encode(Stratified[i])).Fingerprint);
        reversed.Reverse();

        Assert.Equal(forward, reversed);

        // A/B/A across two unrelated cases.
        for (var i = 0; i + 1 < Stratified.Count; i += 97)
        {
            var a = Utf16Decoder.Encode(Stratified[i]);
            var b = Utf16Decoder.Encode(Stratified[i + 1]);
            var first = Utf16Invariants.Run(a).Fingerprint;
            _ = Utf16Invariants.Run(b);
            Assert.Equal(first, Utf16Invariants.Run(a).Fingerprint);
        }
    }

    [Fact]
    public void FingerprintsCarryNothingThatCouldDifferBetweenRuns()
    {
        var pid = Environment.ProcessId.ToString(CultureInfo.InvariantCulture);
        var tid = Environment.CurrentManagedThreadId.ToString(CultureInfo.InvariantCulture);

        foreach (var parameters in Stratified.Take(400))
        {
            var report = Utf16Invariants.Run(Utf16Decoder.Encode(parameters));
            var fingerprint = report.Fingerprint;

            Assert.DoesNotContain(pid, fingerprint, StringComparison.Ordinal);
            Assert.DoesNotContain(tid, fingerprint, StringComparison.Ordinal);
            Assert.DoesNotContain("0x", fingerprint, StringComparison.OrdinalIgnoreCase);

            // No source text: every code unit of the source must be absent as a verbatim run.
            if (report.Case.CodeUnits.Length >= 4)
                Assert.DoesNotContain(report.Case.Source, fingerprint, StringComparison.Ordinal);

            foreach (var c in fingerprint)
                Assert.InRange(c, ' ', '~');     // printable ASCII only, never a raw code unit
        }
    }

    [Fact]
    public void FingerprintsDistinguishTheDimensionsTheyClaimTo()
    {
        var byFingerprint = new Dictionary<string, Utf16Parameters>(StringComparer.Ordinal);
        var collisions = 0;

        foreach (var parameters in Stratified)
        {
            var fingerprint = Utf16Invariants.Run(Utf16Decoder.Encode(parameters)).Fingerprint;
            if (byFingerprint.TryGetValue(fingerprint, out var other))
            {
                Assert.NotEqual(parameters, other);      // same point must give the same print
                collisions++;
            }
            else
            {
                byFingerprint[fingerprint] = parameters;
            }
        }

        // Distinct points may share a fingerprint (that is what a bucket is for), but the
        // fingerprint must still carry real information about the space.
        Assert.True(
            byFingerprint.Count > Stratified.Count / 3,
            $"Only {byFingerprint.Count} distinct fingerprints for {Stratified.Count} points ({collisions} collisions).");
    }

    [Fact]
    public void TheHarnessHoldsNoStaticMutableState()
    {
        var offenders = new List<string>();
        foreach (var type in typeof(Utf16Invariants).Assembly.GetTypes()
                     .Where(t => t.Namespace == "KatLang.ParserFuzz" && t.Name.StartsWith("Utf16", StringComparison.Ordinal)))
        {
            foreach (var field in type.GetFields(
                         System.Reflection.BindingFlags.Static
                         | System.Reflection.BindingFlags.Public
                         | System.Reflection.BindingFlags.NonPublic))
            {
                if (field.IsLiteral) continue;
                if (!field.IsInitOnly) offenders.Add($"{type.Name}.{field.Name} is a writable static field.");
                else if (IsMutableContainer(field.FieldType))
                    offenders.Add($"{type.Name}.{field.Name} is a readonly static holding a mutable container.");
            }

            foreach (var property in type.GetProperties(
                         System.Reflection.BindingFlags.Static
                         | System.Reflection.BindingFlags.Public
                         | System.Reflection.BindingFlags.NonPublic))
            {
                if (property.SetMethod is not null) offenders.Add($"{type.Name}.{property.Name} has a static setter.");
            }
        }

        Assert.True(offenders.Count == 0, string.Join("\n", offenders));
    }

    private static bool IsMutableContainer(Type type)
    {
        if (type.IsArray) return true;
        if (!type.IsGenericType) return false;
        var definition = type.GetGenericTypeDefinition();
        return definition == typeof(List<>) || definition == typeof(Dictionary<,>) || definition == typeof(HashSet<>);
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    private static List<Utf16Seed> LoadSeeds(List<string> problems)
    {
        var seeds = new List<Utf16Seed>();
        foreach (var file in Directory.EnumerateFiles(SeedDirectory, "*.txt").OrderBy(f => f, StringComparer.Ordinal))
            seeds.AddRange(Utf16SeedFile.Load(file, problems));
        return seeds;
    }

    /// <summary>Deterministic payload samples that cover short, exact, and over-long inputs.</summary>
    private static IEnumerable<byte[]> SamplePayloads()
    {
        yield return [];
        yield return [0x00];
        yield return [0xFF, 0xFF];

        for (var i = 0; i < 256; i++)
        {
            var payload = new byte[Utf16Decoder.HeaderBytes + (i % 20)];
            for (var b = 0; b < payload.Length; b++) payload[b] = (byte)((i * 31) + (b * 17));
            yield return payload;
        }

        foreach (var parameters in Utf16Space.EnumerateStratified().Where((_, index) => index % 11 == 0))
            yield return Utf16Decoder.Encode(parameters);
    }
}
