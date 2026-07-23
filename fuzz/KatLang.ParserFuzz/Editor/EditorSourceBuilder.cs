using System.Collections.Immutable;
using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// Builds the exact UTF-16 code units of an editor case's source, resolves its cursor to an exact
/// offset, and applies its bounded edit.
///
/// <para>Everything is assembled as a list of <c>ushort</c> code units and converted to a
/// <c>string</c> exactly once. No step goes through an encoder, a normalizer, or a <c>Rune</c>: an
/// isolated surrogate a case asks for is the isolated surrogate the tooling sees. Templates are
/// written with <c>\n</c> for every line break and <see cref="EditorLineEndingMode"/> chooses the
/// physical encoding — that rewrite is the only transformation applied to assembled text.</para>
/// </summary>
internal static class EditorSourceBuilder
{
    private const ushort Lf = 0x000A;
    private const ushort Cr = 0x000D;

    public static EditorCase Build(EditorParameters parameters)
    {
        ArgumentNullException.ThrowIfNull(parameters);
        var normalized = EditorDecoder.Normalize(parameters);

        var template = EditorTables.TemplateOf(normalized.Template);
        var (baseUnits, injectionOffset) = AssembleSource(template, normalized);

        var source = Utf16CodeUnits.ToStringExact(baseUnits);
        var cursorOffset = EditorCursor.Resolve(normalized, source, injectionOffset);

        var (editedUnits, editApplied) = EditorEdit.Apply(normalized, baseUnits, cursorOffset, injectionOffset);
        var editedSource = Utf16CodeUnits.ToStringExact(editedUnits);
        var editedInjectionOffset = Math.Min(injectionOffset, editedUnits.Length);
        var editedCursorOffset = EditorCursor.Resolve(normalized, editedSource, editedInjectionOffset);

        var description = Describe(normalized, baseUnits.Length, editApplied);
        return new EditorCase(
            normalized,
            baseUnits,
            source,
            cursorOffset,
            editedUnits,
            editedSource,
            editedCursorOffset,
            editApplied,
            description);
    }

    /// <summary>Rebuilds the same case with a different line-ending encoding — used by the LF/CRLF
    /// relation, which compares two physical encodings of ONE assembled source.</summary>
    public static EditorCase BuildWithLineEndings(EditorParameters parameters, EditorLineEndingMode mode)
        => Build(parameters with { LineEndings = mode });

    /// <summary>Returns the assembled base code units and the offset at which the injection starts.</summary>
    private static (ImmutableArray<ushort> Units, int InjectionOffset) AssembleSource(
        EditorTemplate template, EditorParameters parameters)
    {
        var prefix = Utf16CodeUnits.FromString(template.Prefix);
        var injection = Decorate(SelectInjection(parameters), parameters);
        var suffix = Utf16CodeUnits.FromString(template.Suffix);

        var breakIndex = 0;
        var prefixEncoded = RewriteBreaks(prefix, parameters.LineEndings, ref breakIndex);
        var injectionEncoded = RewriteBreaks(injection, parameters.LineEndings, ref breakIndex);
        var suffixEncoded = RewriteBreaks(suffix, parameters.LineEndings, ref breakIndex);

        var assembled = new List<ushort>(checked(prefixEncoded.Count + injectionEncoded.Count + suffixEncoded.Count));
        assembled.AddRange(prefixEncoded);
        var injectionOffset = assembled.Count;
        assembled.AddRange(injectionEncoded);
        assembled.AddRange(suffixEncoded);

        if (parameters.LineEndings == EditorLineEndingMode.NoTrailingNewline)
        {
            while (assembled.Count > 0 && (assembled[^1] == Lf || assembled[^1] == Cr))
                assembled.RemoveAt(assembled.Count - 1);
        }

        if (assembled.Count > EditorTables.MaxSourceCodeUnits)
            throw new InvalidOperationException(
                $"Generated source is {assembled.Count.ToString(CultureInfo.InvariantCulture)} code units, over the " +
                $"{EditorTables.MaxSourceCodeUnits.ToString(CultureInfo.InvariantCulture)}-unit cap. The tables are " +
                "meant to make this unreachable, so this is a harness defect.");

        injectionOffset = Math.Min(injectionOffset, assembled.Count);
        return (ImmutableArray.CreateRange(assembled), injectionOffset);
    }

    private static ImmutableArray<ushort> SelectInjection(EditorParameters parameters)
        => Utf16Tables.MembersOf(parameters.InjectionGroup)[parameters.InjectionMember].Units;

    private static List<ushort> Decorate(ImmutableArray<ushort> units, EditorParameters parameters)
    {
        var filler = EditorTables.FillerLetters[parameters.InjectionMember % EditorTables.FillerLetters.Length];
        var result = new List<ushort>(units.Length + 2);
        switch (parameters.Placement)
        {
            case EditorInjectionPlacement.Alone:
                result.AddRange(units);
                break;
            case EditorInjectionPlacement.AfterLetter:
                result.Add(filler);
                result.AddRange(units);
                break;
            case EditorInjectionPlacement.BeforeLetter:
                result.AddRange(units);
                result.Add(filler);
                break;
            case EditorInjectionPlacement.Surrounded:
                result.Add(filler);
                result.AddRange(units);
                result.Add(filler);
                break;
            case EditorInjectionPlacement.Doubled:
                result.AddRange(units);
                result.AddRange(units);
                break;
            default:
                throw new ArgumentOutOfRangeException(nameof(parameters), parameters.Placement, "Unknown placement.");
        }

        return result;
    }

    /// <summary>Rewrites every <c>\n</c> per the mode; a <c>\r</c> the case asked for is untouched.
    /// Does no end-of-source trimming — that is applied once to the whole assembled source.</summary>
    private static List<ushort> RewriteBreaks(IReadOnlyList<ushort> units, EditorLineEndingMode mode, ref int breakIndex)
    {
        var result = new List<ushort>(units.Count + 8);
        foreach (var unit in units)
        {
            if (unit != Lf)
            {
                result.Add(unit);
                continue;
            }

            switch (mode)
            {
                case EditorLineEndingMode.Lf:
                case EditorLineEndingMode.NoTrailingNewline:
                    result.Add(Lf);
                    break;
                case EditorLineEndingMode.Crlf:
                    result.Add(Cr);
                    result.Add(Lf);
                    break;
                case EditorLineEndingMode.LoneCr:
                    result.Add(Cr);
                    break;
                case EditorLineEndingMode.Mixed:
                    switch (breakIndex % 3)
                    {
                        case 0: result.Add(Lf); break;
                        case 1: result.Add(Cr); result.Add(Lf); break;
                        default: result.Add(Cr); break;
                    }

                    break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(mode), mode, "Unknown line-ending mode.");
            }

            breakIndex++;
        }

        return result;
    }

    private static string Describe(EditorParameters parameters, int length, bool editApplied)
    {
        var template = EditorTables.TemplateOf(parameters.Template).Id;
        var member = Utf16Tables.MembersOf(parameters.InjectionGroup)[parameters.InjectionMember].Id;
        var edit = parameters.Edit == EditorEditKind.None
            ? "no-edit"
            : editApplied ? parameters.Edit.ToString() : $"{parameters.Edit}(skipped)";

        return $"{template} + {parameters.InjectionGroup.ToString().ToLowerInvariant()}/{member} @{parameters.Placement} " +
               $"[{parameters.LineEndings}, {parameters.ExecutionMode}] surface={parameters.Surface} " +
               $"cursor={parameters.Cursor} edit={edit} -> {length.ToString(CultureInfo.InvariantCulture)} code units";
    }
}
