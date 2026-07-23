using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>
/// Maps fuzzer bytes to a normalized <see cref="Utf16Parameters"/> point, and back.
///
/// <para>The bytes are NOT source text. A raw byte-oriented fuzzer cannot carry ill-formed UTF-16
/// through UTF-8 decoding — an isolated surrogate has no UTF-8 form — so the payload instead
/// selects code units explicitly: a structured template plus a named code-unit group, or one of
/// two bounded raw modes that build the units from the payload tail directly.</para>
///
/// <para>PAYLOAD LAYOUT (frozen; a byte's meaning may never be re-used):</para>
/// <code>
///   0  template          index into Utf16Tables.Templates
///   1  placement         how the units sit relative to the insertion site
///   2  line-ending mode  physical encoding of every line break
///   3  execution mode    how far the source is processed
///   4  code-unit group   which named group the insertion is drawn from
///   5  member            which member of that group
///   6  repeat            1..4 copies of the insertion
///   7  filler            which ASCII letter the letter-adjacency placements use
///   8+ raw tail          ONLY read by the two raw templates, bounded to 48 bytes
/// </code>
///
/// <para>Every field is taken modulo its table size, so every byte string decodes — including the
/// empty one, which reads every field as zero. Bytes past the bounded prefix are ignored, so a
/// 1 MiB input decodes exactly like its prefix and no allocation depends on an encoded integer.</para>
/// </summary>
internal static class Utf16Decoder
{
    /// <summary>Fixed header size. Bytes 8+ are the raw tail.</summary>
    public const int HeaderBytes = 8;

    /// <summary>Largest raw tail read. Everything past <c>HeaderBytes + MaxTailBytes</c> is ignored.</summary>
    public const int MaxTailBytes = 48;

    /// <summary>Total bounded prefix of a payload. Campaign <c>-MaxLen</c> is set from this.</summary>
    public const int MaxPayloadPrefixBytes = HeaderBytes + MaxTailBytes;

    public const int MinRepeat = 1;
    public const int MaxRepeat = 4;

    public static Utf16Parameters Decode(ReadOnlySpan<byte> payload)
    {
        var template = (Utf16TemplateKind)(At(payload, 0) % Utf16Tables.Templates.Length);
        var placement = (Utf16PlacementKind)(At(payload, 1) % PlacementCount);
        var lineEndings = (Utf16LineEndingMode)(At(payload, 2) % LineEndingCount);
        var execution = (Utf16ExecutionMode)(At(payload, 3) % ExecutionCount);
        var group = (Utf16CodeUnitGroup)(At(payload, 4) % GroupCount);
        var member = At(payload, 5) % Utf16Tables.MembersOf(group).Length;
        var repeat = MinRepeat + (At(payload, 6) % (MaxRepeat - MinRepeat + 1));
        var filler = At(payload, 7) % Utf16Tables.FillerLetters.Length;

        var raw = Utf16Tables.IsRaw(template)
            ? DecodeTail(payload, template)
            : [];

        return Normalize(new Utf16Parameters(
            template, placement, lineEndings, execution, group, member, repeat, filler, raw));
    }

    /// <summary>
    /// Collapses every dimension the selected template ignores, so two payloads that describe the
    /// same case normalize to the same point (and therefore share one fingerprint).
    /// Idempotent by construction: it only ever writes fixed values into ignored fields.
    /// </summary>
    public static Utf16Parameters Normalize(Utf16Parameters parameters)
    {
        ArgumentNullException.ThrowIfNull(parameters);

        var isRaw = Utf16Tables.IsRaw(parameters.Template);

        // A raw template draws nothing from the group tables; a structured one carries no tail.
        var group = isRaw ? Utf16CodeUnitGroup.Basic : parameters.Group;
        var member = isRaw ? 0 : parameters.Member;
        var raw = isRaw ? parameters.RawUnits : [];

        // Only the letter-adjacency placements read a filler letter.
        var filler = UsesFiller(parameters.Placement) ? parameters.Filler : 0;

        return parameters with { Group = group, Member = member, Filler = filler, RawUnits = raw };
    }

    /// <summary>The canonical payload for a normalized point. <c>Decode(Encode(p)) == p</c>.</summary>
    public static byte[] Encode(Utf16Parameters parameters)
    {
        ArgumentNullException.ThrowIfNull(parameters);
        var normalized = Normalize(parameters);

        var tail = EncodeTail(normalized);
        var payload = new byte[checked(HeaderBytes + tail.Length)];
        payload[0] = (byte)(int)normalized.Template;
        payload[1] = (byte)(int)normalized.Placement;
        payload[2] = (byte)(int)normalized.LineEndings;
        payload[3] = (byte)(int)normalized.ExecutionMode;
        payload[4] = (byte)(int)normalized.Group;
        payload[5] = (byte)normalized.Member;
        payload[6] = (byte)(normalized.Repeat - MinRepeat);
        payload[7] = (byte)normalized.Filler;
        tail.CopyTo(payload.AsSpan(HeaderBytes));
        return payload;
    }

    /// <summary>True when the placement inserts one of <see cref="Utf16Tables.FillerLetters"/>.</summary>
    public static bool UsesFiller(Utf16PlacementKind placement) => placement
        is Utf16PlacementKind.AfterLetter
        or Utf16PlacementKind.BeforeLetter
        or Utf16PlacementKind.Surrounded;

    public static int PlacementCount => Enum.GetValues<Utf16PlacementKind>().Length;
    public static int LineEndingCount => Enum.GetValues<Utf16LineEndingMode>().Length;
    public static int ExecutionCount => Enum.GetValues<Utf16ExecutionMode>().Length;
    public static int GroupCount => Enum.GetValues<Utf16CodeUnitGroup>().Length;

    private static int At(ReadOnlySpan<byte> payload, int index)
        => index < payload.Length ? payload[index] : 0;

    private static ImmutableArray<ushort> DecodeTail(ReadOnlySpan<byte> payload, Utf16TemplateKind template)
    {
        var available = payload.Length > HeaderBytes ? payload.Length - HeaderBytes : 0;
        var tailBytes = Math.Min(available, MaxTailBytes);

        if (template == Utf16TemplateKind.RawAlphabet)
        {
            var count = Math.Min(tailBytes, Utf16Tables.MaxRawAlphabetUnits);
            var builder = ImmutableArray.CreateBuilder<ushort>(count);
            for (var i = 0; i < count; i++)
                builder.Add(Utf16Tables.RawAlphabet[payload[HeaderBytes + i] % Utf16Tables.RawAlphabet.Length]);
            return builder.MoveToImmutable();
        }

        // RawLiteralUnits: byte PAIRS are literal code units, little-endian. A trailing odd byte
        // is dropped rather than zero-extended, so encode/decode round-trips exactly.
        var units = Math.Min(tailBytes / 2, Utf16Tables.MaxRawLiteralUnits);
        var literals = ImmutableArray.CreateBuilder<ushort>(units);
        for (var i = 0; i < units; i++)
        {
            var low = payload[HeaderBytes + (i * 2)];
            var high = payload[HeaderBytes + (i * 2) + 1];
            literals.Add((ushort)(low | (high << 8)));
        }

        return literals.MoveToImmutable();
    }

    private static byte[] EncodeTail(Utf16Parameters parameters)
    {
        if (parameters.RawUnits.IsEmpty) return [];

        if (parameters.Template == Utf16TemplateKind.RawAlphabet)
        {
            var bytes = new byte[parameters.RawUnits.Length];
            for (var i = 0; i < bytes.Length; i++)
            {
                var index = Utf16Tables.RawAlphabet.IndexOf(parameters.RawUnits[i]);
                if (index < 0)
                    throw new InvalidOperationException(
                        $"Code unit U+{parameters.RawUnits[i]:X4} is not in the raw alphabet, so it " +
                        "cannot have come from a raw-alphabet payload.");
                bytes[i] = (byte)index;
            }

            return bytes;
        }

        var literal = new byte[checked(parameters.RawUnits.Length * 2)];
        for (var i = 0; i < parameters.RawUnits.Length; i++)
        {
            literal[i * 2] = (byte)(parameters.RawUnits[i] & 0xFF);
            literal[(i * 2) + 1] = (byte)(parameters.RawUnits[i] >> 8);
        }

        return literal;
    }
}
