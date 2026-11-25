using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>
/// A deterministic stratified walk of the UTF-16 parameter space.
///
/// <para>The full cross product is far too large to enumerate, and sampling it randomly would make
/// the deterministic tests depend on a seed. Instead each stratum crosses ONE pair of dimensions
/// exhaustively while pinning the rest, so every template, placement, line-ending mode, execution
/// mode, code-unit group member, repeat and raw shape is reached by construction — and the whole
/// walk is the same list on every machine and in every process.</para>
///
/// <para>Normalization deduplicates: a stratum that varies a dimension the selected template
/// ignores collapses onto points another stratum already produced, so the cost of being thorough in
/// one stratum is not paid again in the next.</para>
/// </summary>
internal static class Utf16Space
{
    /// <summary>Templates that stand in for the whole set when a stratum crosses something else.</summary>
    private static readonly ImmutableArray<Utf16TemplateKind> RepresentativeTemplates =
    [
        Utf16TemplateKind.IdentifierStart,
        Utf16TemplateKind.StringLiteral,
        Utf16TemplateKind.LineComment,
        Utf16TemplateKind.NumberBoundary,
        Utf16TemplateKind.DottedCall,
        Utf16TemplateKind.RecoveryPoint,
    ];

    /// <summary>Deterministic raw tails: empty, short, mixed, and a full-length one.</summary>
    private static readonly ImmutableArray<int> RawTailLengths = [0, 1, 2, 3, 5, 8, 16, Utf16Decoder.MaxTailBytes];

    public static IEnumerable<Utf16Parameters> EnumerateStratified()
    {
        var seen = new HashSet<Utf16Parameters>();

        // 1. Every template crossed with every placement.
        foreach (var template in AllTemplates())
        foreach (var placement in All<Utf16PlacementKind>())
        {
            var point = Point(template, placement: placement);
            if (seen.Add(point)) yield return point;
        }

        // 2. Every template crossed with every physical line-ending encoding.
        foreach (var template in AllTemplates())
        foreach (var lineEndings in All<Utf16LineEndingMode>())
        {
            var point = Point(template, lineEndings: lineEndings);
            if (seen.Add(point)) yield return point;
        }

        // 3. Every template crossed with every execution mode.
        foreach (var template in AllTemplates())
        foreach (var execution in All<Utf16ExecutionMode>())
        {
            var point = Point(template, execution: execution);
            if (seen.Add(point)) yield return point;
        }

        // 4. Every code-unit group member, at every representative template.
        foreach (var template in RepresentativeTemplates)
        foreach (var group in All<Utf16CodeUnitGroup>())
        for (var member = 0; member < Utf16Tables.MembersOf(group).Length; member++)
        {
            var point = Point(template, group: group, member: member);
            if (seen.Add(point)) yield return point;
        }

        // 5. Every surrogate and whitespace member crossed with every placement — the two groups
        //    whose interaction with the insertion site is the point of this phase.
        foreach (var group in new[] { Utf16CodeUnitGroup.Surrogates, Utf16CodeUnitGroup.Whitespace })
        for (var member = 0; member < Utf16Tables.MembersOf(group).Length; member++)
        foreach (var placement in All<Utf16PlacementKind>())
        {
            var point = Point(Utf16TemplateKind.StringLiteral, placement: placement, group: group, member: member);
            if (seen.Add(point)) yield return point;
        }

        // 6. Every surrogate and whitespace member crossed with every line-ending encoding.
        foreach (var group in new[] { Utf16CodeUnitGroup.Surrogates, Utf16CodeUnitGroup.Whitespace })
        for (var member = 0; member < Utf16Tables.MembersOf(group).Length; member++)
        foreach (var lineEndings in All<Utf16LineEndingMode>())
        {
            var point = Point(Utf16TemplateKind.IdentifierStart, lineEndings: lineEndings, group: group, member: member);
            if (seen.Add(point)) yield return point;
        }

        // 7. Repeat counts and filler letters, where a decoration actually reads them.
        foreach (var template in RepresentativeTemplates)
        for (var repeat = Utf16Decoder.MinRepeat; repeat <= Utf16Decoder.MaxRepeat; repeat++)
        for (var filler = 0; filler < Utf16Tables.FillerLetters.Length; filler++)
        {
            var point = Point(template, placement: Utf16PlacementKind.Surrounded, repeat: repeat, filler: filler);
            if (seen.Add(point)) yield return point;
        }

        // 8. Both raw modes, at every tail length, crossed with the line-ending encodings.
        foreach (var template in new[] { Utf16TemplateKind.RawAlphabet, Utf16TemplateKind.RawLiteralUnits })
        foreach (var length in RawTailLengths)
        foreach (var lineEndings in All<Utf16LineEndingMode>())
        {
            var point = Utf16Decoder.Decode(RawPayload(template, length, lineEndings));
            if (seen.Add(point)) yield return point;
        }
    }

    /// <summary>Canonical payloads for the whole stratified walk — what the seed export and the
    /// determinism tests feed through the real decoder.</summary>
    public static IEnumerable<byte[]> EnumerateStratifiedPayloads()
        => EnumerateStratified().Select(Utf16Decoder.Encode);

    private static IEnumerable<Utf16TemplateKind> AllTemplates()
        => Enumerable.Range(0, Utf16Tables.Templates.Length).Select(i => (Utf16TemplateKind)i);

    private static IEnumerable<T> All<T>() where T : struct, Enum => Enum.GetValues<T>();

    private static Utf16Parameters Point(
        Utf16TemplateKind template,
        Utf16PlacementKind placement = Utf16PlacementKind.Alone,
        Utf16LineEndingMode lineEndings = Utf16LineEndingMode.Lf,
        Utf16ExecutionMode execution = Utf16ExecutionMode.StringBridge,
        Utf16CodeUnitGroup group = Utf16CodeUnitGroup.Surrogates,
        int member = 0,
        int repeat = 1,
        int filler = 0)
    {
        // A raw template ignores group/member, so give it a deterministic short tail instead of
        // silently degenerating to the empty source in every stratum that pins those dimensions.
        var raw = Utf16Tables.IsRaw(template)
            ? Utf16Decoder.Decode(RawPayload(template, 6, lineEndings)).RawUnits
            : ImmutableArray<ushort>.Empty;

        return Utf16Decoder.Normalize(new Utf16Parameters(
            template, placement, lineEndings, execution, group, member, repeat, filler, raw));
    }

    /// <summary>
    /// A deterministic raw payload: the tail bytes are a fixed low-discrepancy walk, so the two raw
    /// modes get reproducible but varied content without any randomness.
    /// </summary>
    private static byte[] RawPayload(Utf16TemplateKind template, int tailLength, Utf16LineEndingMode lineEndings)
    {
        var payload = new byte[Utf16Decoder.HeaderBytes + tailLength];
        payload[0] = (byte)(int)template;
        payload[1] = (byte)(int)Utf16PlacementKind.Alone;
        payload[2] = (byte)(int)lineEndings;
        payload[3] = (byte)(int)Utf16ExecutionMode.StringBridge;
        for (var i = 0; i < tailLength; i++)
            payload[Utf16Decoder.HeaderBytes + i] = (byte)((i * 37) + 11);
        return payload;
    }
}
