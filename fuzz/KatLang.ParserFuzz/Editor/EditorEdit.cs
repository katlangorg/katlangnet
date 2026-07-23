using System.Collections.Immutable;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Applies a bounded source edit to the exact base code units and returns the edited units. Every
/// edit either transforms an existing feature or inserts one of the case's own injected units;
/// nothing reads an unbounded length, and an edit that would exceed the source cap or has nothing to
/// act on is reported as NOT applied rather than clamped into a different edit.
/// </summary>
internal static class EditorEdit
{
    private const ushort Space = 0x0020;
    private const ushort Quote = 0x0027;
    private const ushort Dot = 0x002E;
    private const ushort Comma = 0x002C;
    private const ushort Lf = 0x000A;
    private const ushort Cr = 0x000D;

    private static readonly ImmutableArray<ushort> Delimiters = ['(', ')', '[', ']', '{', '}'];

    public static (ImmutableArray<ushort> Units, bool Applied) Apply(
        EditorParameters parameters, ImmutableArray<ushort> baseUnits, int cursorOffset, int injectionOffset)
    {
        ArgumentNullException.ThrowIfNull(parameters);
        _ = injectionOffset;

        if (parameters.Edit == EditorEditKind.None)
            return (baseUnits, false);

        var editUnits = Utf16Tables.MembersOf(parameters.EditGroup)[parameters.EditMember].Units;
        var at = Math.Clamp(cursorOffset, 0, baseUnits.Length);
        var bias = parameters.EditBias;

        var result = parameters.Edit switch
        {
            EditorEditKind.Insert => Insert(baseUnits, at, editUnits),
            EditorEditKind.Delete => Delete(baseUnits, at, 1 + (bias % 3)),
            EditorEditKind.Replace => Insert(Delete(baseUnits, at, 1 + (bias % 2)) ?? baseUnits, at, editUnits),
            EditorEditKind.Append => Insert(baseUnits, baseUnits.Length, editUnits),
            EditorEditKind.Prepend => Insert(baseUnits, 0, editUnits),
            EditorEditKind.SplitToken => Insert(baseUnits, at, [Space]),
            EditorEditKind.JoinTokens => RemoveFirst(baseUnits, at, u => u == Space || u == 0x0009),
            EditorEditKind.AddDot => Insert(baseUnits, at, [Dot]),
            EditorEditKind.RemoveDot => RemoveFirst(baseUnits, at, u => u == Dot),
            EditorEditKind.AddComma => Insert(baseUnits, at, [Comma]),
            EditorEditKind.RemoveComma => RemoveFirst(baseUnits, at, u => u == Comma),
            EditorEditKind.AddDelimiter => Insert(baseUnits, at, [Delimiters[bias % Delimiters.Length]]),
            EditorEditKind.RemoveDelimiter => RemoveFirst(baseUnits, at, IsDelimiter),
            EditorEditKind.AddNewline => Insert(baseUnits, at, [Lf]),
            EditorEditKind.LineFeedToCarriageReturnLineFeed => ReplaceSequence(baseUnits, [Lf], [Cr, Lf]),
            EditorEditKind.CarriageReturnLineFeedToLineFeed => ReplaceSequence(baseUnits, [Cr, Lf], [Lf]),
            EditorEditKind.AddSpreadDot => AddSpreadDot(baseUnits, at),
            EditorEditKind.RemoveSpreadDot => RemoveSpreadDot(baseUnits, at),
            EditorEditKind.CompleteString => Insert(baseUnits, baseUnits.Length, [Quote]),
            EditorEditKind.BreakString => Insert(baseUnits, at, [Quote]),
            EditorEditKind.RenameLocalSymbol => Rename(baseUnits, toDuplicate: false, bias),
            EditorEditKind.RenameToDuplicate => Rename(baseUnits, toDuplicate: true, bias),
            _ => null,
        };

        if (result is null || result.Value.Length > EditorTables.MaxSourceCodeUnits)
            return (baseUnits, false);

        return (result.Value, !result.Value.AsSpan().SequenceEqual(baseUnits.AsSpan()));
    }

    private static ImmutableArray<ushort> Insert(ImmutableArray<ushort> units, int at, ImmutableArray<ushort> insertion)
        => units.InsertRange(Math.Clamp(at, 0, units.Length), insertion);

    private static ImmutableArray<ushort>? Delete(ImmutableArray<ushort> units, int at, int count)
    {
        if (units.Length == 0)
            return null;

        at = Math.Clamp(at, 0, units.Length);
        if (at >= units.Length)
            at = units.Length - 1;

        var end = Math.Min(at + count, units.Length);
        if (end <= at)
            return null;

        return units.RemoveRange(at, end - at);
    }

    private static ImmutableArray<ushort>? RemoveFirst(ImmutableArray<ushort> units, int at, Func<ushort, bool> match)
    {
        for (var i = Math.Clamp(at, 0, units.Length); i < units.Length; i++)
            if (match(units[i]))
                return Delete(units, i, 1);
        for (var i = 0; i < units.Length; i++)
            if (match(units[i]))
                return Delete(units, i, 1);
        return null;
    }

    private static ImmutableArray<ushort> ReplaceSequence(
        ImmutableArray<ushort> units, ImmutableArray<ushort> from, ImmutableArray<ushort> to)
    {
        var result = new List<ushort>(units.Length);
        var i = 0;
        while (i < units.Length)
        {
            if (MatchesAt(units, i, from))
            {
                result.AddRange(to);
                i += from.Length;
            }
            else
            {
                result.Add(units[i]);
                i++;
            }
        }

        return ImmutableArray.CreateRange(result);
    }

    private static bool MatchesAt(ImmutableArray<ushort> units, int index, ImmutableArray<ushort> pattern)
    {
        if (index + pattern.Length > units.Length)
            return false;
        for (var k = 0; k < pattern.Length; k++)
            if (units[index + k] != pattern[k])
                return false;
        return true;
    }

    private static ImmutableArray<ushort>? AddSpreadDot(ImmutableArray<ushort> units, int at)
    {
        for (var i = 0; i + 1 < units.Length; i++)
            if (units[i] == Dot && units[i + 1] == Dot)
                return Insert(units, i + 2, [Dot]);
        return Insert(units, at, [Dot, Dot, Dot]);
    }

    private static ImmutableArray<ushort>? RemoveSpreadDot(ImmutableArray<ushort> units, int at)
    {
        for (var i = 0; i + 2 < units.Length; i++)
            if (units[i] == Dot && units[i + 1] == Dot && units[i + 2] == Dot)
                return Delete(units, i, 1);
        return RemoveFirst(units, at, u => u == Dot);
    }

    private static bool IsDelimiter(ushort unit)
        => Delimiters.Contains(unit);

    /// <summary>
    /// Token-based rename of a chosen identifier. Because it walks the lexer token stream, it renames
    /// only real identifier tokens and never touches text inside strings or comments. Returns null
    /// when there is no suitable identifier (or, for the duplicate variant, no second name to collide
    /// with), so the edit is honestly reported as not applied rather than silently doing nothing.
    /// </summary>
    private static ImmutableArray<ushort>? Rename(ImmutableArray<ushort> units, bool toDuplicate, int bias)
    {
        var source = Utf16CodeUnits.ToStringExact(units);
        var (tokens, _) = Lexer.Tokenize(source);

        var names = new List<string>();
        foreach (var token in tokens)
        {
            if (token.Kind == TokenKind.Identifier && token.StringValue is { Length: > 0 } name && !names.Contains(name))
                names.Add(name);
        }

        if (names.Count == 0)
            return null;

        var target = names[bias % names.Count];
        string newName;
        if (toDuplicate)
        {
            if (names.Count < 2)
                return null;
            newName = names[(names.IndexOf(target) + 1) % names.Count];
        }
        else
        {
            newName = target + "Q";
        }

        var newUnits = Utf16CodeUnits.FromString(newName);
        var occurrences = new List<(int Position, int Length)>();
        foreach (var token in tokens)
        {
            if (token.Kind == TokenKind.Identifier && string.Equals(token.StringValue, target, StringComparison.Ordinal))
                occurrences.Add((token.Position, token.Length));
        }

        if (occurrences.Count == 0)
            return null;

        var result = units.ToList();
        for (var i = occurrences.Count - 1; i >= 0; i--)
        {
            var (position, length) = occurrences[i];
            result.RemoveRange(position, length);
            result.InsertRange(position, newUnits);
        }

        return ImmutableArray.CreateRange(result);
    }
}
