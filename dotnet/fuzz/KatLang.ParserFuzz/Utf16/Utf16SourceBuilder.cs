using System.Collections.Immutable;
using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// Builds the exact UTF-16 code units of a case's source.
///
/// <para>Everything is assembled as a list of <c>ushort</c> code units and converted to a
/// <c>string</c> exactly once, at the end. No step goes through an encoder, a normalizer, or a
/// <c>Rune</c>: an isolated surrogate that a case asks for is the isolated surrogate the lexer
/// sees. Templates are written with <c>\n</c> for every line break and
/// <see cref="Utf16LineEndingMode"/> chooses the physical encoding — that rewrite is the ONLY
/// transformation applied to assembled text.</para>
/// </summary>
internal static class Utf16SourceBuilder
{
    private const ushort Lf = 0x000A;
    private const ushort Cr = 0x000D;
    private const ushort Space = 0x0020;
    private const ushort Dot = 0x002E;
    private const ushort Star = 0x002A;

    public static Utf16Case Build(Utf16Parameters parameters)
    {
        ArgumentNullException.ThrowIfNull(parameters);
        var normalized = Utf16Decoder.Normalize(parameters);

        var template = Utf16Tables.TemplateOf(normalized.Template);
        var (selected, memberId) = SelectUnits(normalized);
        var repeated = Repeat(selected, normalized.Repeat);
        var decorated = Decorate(repeated, normalized);

        var assembled = new List<ushort>(Utf16Tables.MaxSourceCodeUnits);
        if (normalized.Placement == Utf16PlacementKind.AtEndOfSource)
        {
            AppendText(assembled, template.Prefix);
            AppendText(assembled, template.Suffix);
            assembled.AddRange(decorated);
        }
        else
        {
            AppendText(assembled, template.Prefix);
            assembled.AddRange(decorated);
            AppendText(assembled, template.Suffix);
        }

        var final = ApplyLineEndings(assembled, normalized.LineEndings);

        if (final.Count > Utf16Tables.MaxSourceCodeUnits)
            throw new InvalidOperationException(
                $"Generated source is {final.Count.ToString(CultureInfo.InvariantCulture)} code units, " +
                $"over the {Utf16Tables.MaxSourceCodeUnits.ToString(CultureInfo.InvariantCulture)}-unit cap. " +
                "The tables are meant to make this unreachable, so this is a harness defect.");

        var units = ImmutableArray.CreateRange(final);
        var description = Describe(normalized, memberId, units.Length);
        return new Utf16Case(normalized, units, Utf16CodeUnits.ToStringExact(units), description);
    }

    /// <summary>Rebuilds the same case with a different line-ending encoding. Used by the
    /// line-ending relations, which must compare two encodings of ONE assembled source.</summary>
    public static Utf16Case BuildWithLineEndings(Utf16Parameters parameters, Utf16LineEndingMode mode)
    {
        ArgumentNullException.ThrowIfNull(parameters);
        return Build(parameters with { LineEndings = mode });
    }

    private static (ImmutableArray<ushort> Units, string MemberId) SelectUnits(Utf16Parameters parameters)
    {
        if (Utf16Tables.IsRaw(parameters.Template))
            return (parameters.RawUnits, parameters.RawUnits.IsEmpty ? "empty" : "payload");

        var members = Utf16Tables.MembersOf(parameters.Group);
        var member = members[parameters.Member];
        return (member.Units, member.Id);
    }

    private static List<ushort> Repeat(ImmutableArray<ushort> units, int times)
    {
        var result = new List<ushort>(checked(units.Length * times));
        for (var i = 0; i < times; i++) result.AddRange(units);
        return result;
    }

    private static List<ushort> Decorate(List<ushort> units, Utf16Parameters parameters)
    {
        var filler = Utf16Tables.FillerLetters[parameters.Filler];
        var half = units.Count / 2;

        return parameters.Placement switch
        {
            Utf16PlacementKind.Alone => units,
            Utf16PlacementKind.AtEndOfSource => units,
            Utf16PlacementKind.AfterLetter => Concat([filler], units),
            Utf16PlacementKind.BeforeLetter => Concat(units, [filler]),
            Utf16PlacementKind.Surrounded => Concat([filler], units, [filler]),
            Utf16PlacementKind.Doubled => Concat(units, units),
            Utf16PlacementKind.Repeated3 => Concat(units, units, units),
            Utf16PlacementKind.SplitByNewline =>
                Concat(units.GetRange(0, half), [Lf], units.GetRange(half, units.Count - half)),
            Utf16PlacementKind.SplitByPunctuation =>
                Concat(units.GetRange(0, half), [Dot], units.GetRange(half, units.Count - half)),
            Utf16PlacementKind.AfterDot => Concat([Dot], units),
            Utf16PlacementKind.BeforeSpread => Concat(units, [Star]),
            _ => throw new ArgumentOutOfRangeException(
                nameof(parameters), parameters.Placement, "Unknown placement."),
        };
    }

    /// <summary>
    /// Rewrites every <c>\n</c> in the assembled units. A <c>\r</c> the case itself asked for is
    /// never touched — only the builder's own line breaks are re-encoded.
    /// </summary>
    private static List<ushort> ApplyLineEndings(List<ushort> units, Utf16LineEndingMode mode)
    {
        var result = new List<ushort>(units.Count + 16);
        var breakIndex = 0;

        foreach (var unit in units)
        {
            if (unit != Lf)
            {
                result.Add(unit);
                continue;
            }

            switch (mode)
            {
                case Utf16LineEndingMode.Lf:
                case Utf16LineEndingMode.TrailingNewline:
                case Utf16LineEndingMode.NoTrailingNewline:
                    result.Add(Lf);
                    break;
                case Utf16LineEndingMode.Crlf:
                    result.Add(Cr);
                    result.Add(Lf);
                    break;
                case Utf16LineEndingMode.LoneCr:
                    result.Add(Cr);
                    break;
                case Utf16LineEndingMode.Mixed:
                    switch (breakIndex % 3)
                    {
                        case 0: result.Add(Lf); break;
                        case 1: result.Add(Cr); result.Add(Lf); break;
                        default: result.Add(Cr); break;
                    }

                    break;
                case Utf16LineEndingMode.NoNewline:
                    result.Add(Space);
                    break;
                case Utf16LineEndingMode.RepeatedBlankLines:
                    result.Add(Lf);
                    result.Add(Lf);
                    result.Add(Lf);
                    break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(mode), mode, "Unknown line-ending mode.");
            }

            breakIndex++;
        }

        switch (mode)
        {
            case Utf16LineEndingMode.TrailingNewline:
                if (result.Count == 0 || result[^1] != Lf) result.Add(Lf);
                break;
            case Utf16LineEndingMode.NoTrailingNewline:
                while (result.Count > 0 && (result[^1] == Lf || result[^1] == Cr)) result.RemoveAt(result.Count - 1);
                break;
            default:
                break;
        }

        return result;
    }

    private static void AppendText(List<ushort> target, string text)
    {
        foreach (var c in text) target.Add(c);
    }

    private static List<ushort> Concat(params List<ushort>[] parts)
    {
        var total = 0;
        foreach (var part in parts) total = checked(total + part.Count);
        var result = new List<ushort>(total);
        foreach (var part in parts) result.AddRange(part);
        return result;
    }

    private static string Describe(Utf16Parameters parameters, string memberId, int length)
    {
        var template = Utf16Tables.TemplateOf(parameters.Template).Id;
        var source = Utf16Tables.IsRaw(parameters.Template)
            ? $"{parameters.RawUnits.Length.ToString(CultureInfo.InvariantCulture)} raw units"
            : $"{parameters.Group.ToString().ToLowerInvariant()}/{memberId}";

        return $"{template} + {source} @{parameters.Placement} x{parameters.Repeat.ToString(CultureInfo.InvariantCulture)} " +
               $"[{parameters.LineEndings}, {parameters.ExecutionMode}] " +
               $"-> {length.ToString(CultureInfo.InvariantCulture)} code units";
    }
}
