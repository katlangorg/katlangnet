using System.Globalization;
using System.Numerics;
using System.Text;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// SUPPLEMENTARY durable structural identity of a successful value (SEM-2A): an explicitly
/// versioned, ASCII-only, injective text whose ordinal equality is exactly
/// <see cref="Result.ValueComparer"/> equality.
///
/// <para><b>Why it exists.</b> The legacy neutral encoding (<see cref="MetamorphicValue.Neutral"/>,
/// mirrored by the semantic explorer and frozen by FORMAL-06) writes strings between unescaped
/// quotes, so <c>["a', 'b", "c"]</c> (two items) and <c>["a", "b", "c"]</c> (three) share the
/// text <c>L['a', 'b', 'c']</c>. That encoding stays exactly as it is; this one sits beside it.
/// In process, the typed <see cref="Result.ValueComparer"/> verdict stays authoritative and this
/// identity is cross-checked against it on every comparison; across processes (and, later,
/// against Lean) this text is the comparable form.</para>
///
/// <para><b>Format <c>kl-struct-v1</c>.</b> <c>kl-struct-v1:&lt;n&gt;:</c> followed by exactly
/// <c>n</c> node definitions; node ids are the definitions' zero-based positions and the ROOT is
/// the last one. Each definition is one of</para>
/// <list type="bullet">
/// <item><c>n&lt;len&gt;:&lt;number&gt;</c> — a Decimal128 atom in its canonical equality class:
/// <c>NaN</c>, <c>+Inf</c>, <c>-Inf</c>, <c>0</c> (both signed zeros), or
/// <c>[-]&lt;coefficient&gt;e&lt;exponent&gt;</c> with no leading or trailing coefficient zeros,
/// so <c>1.5</c>, <c>1.50</c> and <c>150e-2</c> all read <c>15e-1</c>;</item>
/// <item><c>b0</c> / <c>b1</c> — a Boolean;</item>
/// <item><c>t&lt;len&gt;:&lt;text&gt;</c> — a string of <c>len</c> UTF-16 code units, printable
/// ASCII written as itself except <c>\</c> (written <c>\\</c>), every other code unit written
/// <c>\uXXXX</c> (uppercase hex) — so lone surrogates, NUL and line breaks survive any byte
/// encoding;</item>
/// <item><c>s&lt;count&gt;:&lt;id&gt;,…;</c> / <c>l&lt;count&gt;:&lt;id&gt;,…;</c> — a sequence
/// or exact list over earlier node ids, each id followed by <c>,</c>, terminated by <c>;</c>
/// (<c>s0:;</c> is <c>()</c>, <c>l0:;</c> is <c>[]</c>).</item>
/// </list>
///
/// <para><b>Canonical DAG table.</b> Equal sub-values are defined ONCE (hash-consed by their
/// definition text) and ids are assigned in left-to-right post-order of first completion, so a
/// value that shares a subtree by reference and one that repeats an equal independent subtree
/// produce the same text, and the cost is proportional to distinct references plus distinct
/// definitions — never to root-to-leaf paths. The walk uses an explicit frame stack, so value
/// depth never reaches the host stack.</para>
/// </summary>
internal static class MetamorphicStructuralIdentity
{
    /// <summary>The format identifier every encoding starts with.</summary>
    internal const string Version = "kl-struct-v1";

    private const string Header = Version + ":";

    /// <summary>Encodes a completed run value. Call references never leave a run and are refused.</summary>
    internal static string Encode(Result value)
    {
        ArgumentNullException.ThrowIfNull(value);

        var table = new Table();
        if (table.TryLeaf(value, out var rootId)) return table.Render(rootId);

        var frames = new Stack<Frame>();
        frames.Push(new Frame(value));
        while (true)
        {
            var frame = frames.Peek();
            if (frame.Next < frame.Items.Count)
            {
                var child = frame.Items[frame.Next++];
                if (table.TryLeaf(child, out var childId)) frame.ChildIds.Add(childId);
                else frames.Push(new Frame(child));
                continue;
            }

            frames.Pop();
            var id = table.Complete(frame);
            if (frames.Count == 0) return table.Render(id);
            frames.Peek().ChildIds.Add(id);
        }
    }

    /// <summary>
    /// Decodes a <c>kl-struct-v1</c> text back into a value, sharing every node the table
    /// defines once. Rejects anything that is not EXACTLY a canonical encoding (wrong version,
    /// bad framing, forward references, non-canonical numbers or escapes, reordered, duplicated or
    /// unreferenced definitions), so <c>Encode(Decode(text)) == text</c> whenever this succeeds.
    /// </summary>
    internal static bool TryDecode(string text, out Result value, out string problem)
    {
        ArgumentNullException.ThrowIfNull(text);
        value = null!;

        var reader = new Reader(text);
        if (!text.StartsWith(Header, StringComparison.Ordinal))
            return Fail("missing '" + Header + "' version header", out problem);
        reader.Position = Header.Length;
        // Even the shortest definition occupies two characters. Validate framing BEFORE using
        // untrusted counts as allocation sizes; a tiny malformed record must stay a tiny read.
        if (!reader.TryNumber(out var count) || !reader.TryExpect(':') || count < 1
            || count > reader.Remaining / 2)
            return Fail("missing or invalid node count", out problem);

        var nodes = new Result[count];
        for (var index = 0; index < count; index++)
        {
            if (!TryReadNode(ref reader, nodes, index, out var node, out problem)) return false;
            nodes[index] = node;
        }

        if (reader.Position != text.Length) return Fail("trailing text after the last node", out problem);

        // Well-formed is not yet canonical: reordered, duplicated or unreferenced definitions
        // would still decode. Re-encoding pins the ONE canonical spelling of the value.
        if (!string.Equals(Encode(nodes[count - 1]), text, StringComparison.Ordinal))
            return Fail("well-formed but not the canonical encoding of its value", out problem);

        value = nodes[count - 1];
        problem = "ok";
        return true;
    }

    /// <summary>One string in the format's own unambiguous string spelling, <c>t&lt;len&gt;:&lt;escaped&gt;</c>.</summary>
    internal static string QuoteText(string value)
    {
        ArgumentNullException.ThrowIfNull(value);
        var text = new StringBuilder(value.Length + 8)
            .Append('t').Append(value.Length.ToString(CultureInfo.InvariantCulture)).Append(':');
        AppendEscaped(text, value);
        return text.ToString();
    }

    /// <summary>A bounded, still unambiguous excerpt for mismatch diagnostics. Never compared.</summary>
    internal static string Preview(string? identity, int maxLength = 240)
    {
        if (identity is null) return "-";
        if (identity.Length <= maxLength) return identity;
        return identity[..maxLength] + "…(+" + (identity.Length - maxLength).ToString(CultureInfo.InvariantCulture) + " chars)";
    }

    /// <summary>A bounded escaped diagnostic of legacy text, never used for equality.</summary>
    internal static string PreviewText(string? value)
    {
        if (value is null) return "-";
        const int MaxUnits = 32;
        var prefix = value[..Math.Min(value.Length, MaxUnits)];
        return QuoteText(prefix) + (value.Length <= MaxUnits
            ? ""
            : "…(+" + (value.Length - MaxUnits).ToString(CultureInfo.InvariantCulture) + " UTF-16 units)");
    }

    /// <summary>
    /// The canonical text of one Decimal128 equality class (<see cref="Decimal128.Equals(Decimal128)"/>:
    /// quantum ignored, <c>+0 == -0</c>, every NaN one value). The finite case reads the exact
    /// 34-significant-digit scientific form — a Decimal128 coefficient never has more digits — and
    /// strips its trailing zeros; culture-invariant, never rounded.
    /// </summary>
    internal static string CanonicalNumber(Decimal128 number)
    {
        if (Decimal128.IsNaN(number)) return "NaN";
        if (Decimal128.IsInfinity(number)) return Decimal128.IsNegative(number) ? "-Inf" : "+Inf";
        if (number.Equals(Decimal128.Zero)) return "0";

        var scientific = number.ToString("E33", CultureInfo.InvariantCulture);
        var exponentAt = scientific.IndexOf('E', StringComparison.Ordinal);
        var negative = scientific[0] == '-';
        var mantissa = scientific[(negative ? 1 : 0)..exponentAt].Replace(".", "", StringComparison.Ordinal);
        var exponent = int.Parse(scientific.AsSpan(exponentAt + 1), NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture);
        if (mantissa.Length != 34 || mantissa[0] == '0')
            throw new MetamorphicHarnessException($"Unexpected Decimal128 scientific form '{scientific}'.");

        var significant = mantissa.TrimEnd('0');
        var scale = exponent - 33 + (mantissa.Length - significant.Length);
        return (negative ? "-" : "") + significant + "e" + scale.ToString(CultureInfo.InvariantCulture);
    }

    private static bool TryParseCanonicalNumber(string text, out Decimal128 number)
    {
        number = default;
        switch (text)
        {
            case "NaN": number = Decimal128.NaN; return true;
            case "+Inf": number = Decimal128.PositiveInfinity; return true;
            case "-Inf": number = Decimal128.NegativeInfinity; return true;
            case "0": number = Decimal128.Zero; return true;
        }

        var e = text.IndexOf('e', StringComparison.Ordinal);
        if (e <= 0) return false;
        if (!Decimal128.TryParse(
                text[..e] + "E" + text[(e + 1)..], NumberStyles.AllowLeadingSign | NumberStyles.AllowExponent,
                CultureInfo.InvariantCulture, out number))
        {
            return false;
        }

        // Only the canonical spelling of its class is accepted, so decoding stays injective.
        return Decimal128.IsFinite(number) && string.Equals(CanonicalNumber(number), text, StringComparison.Ordinal);
    }

    private static bool TryReadNode(
        ref Reader reader, Result[] nodes, int index, out Result node, out string problem)
    {
        node = null!;
        if (!reader.TryRead(out var tag)) return Fail($"node {index}: missing definition", out problem);
        switch (tag)
        {
            case 'b':
                if (!reader.TryRead(out var flag) || flag is not ('0' or '1'))
                    return Fail($"node {index}: invalid Boolean", out problem);
                node = new Result.Bool(flag == '1');
                break;

            case 'n':
            {
                if (!reader.TryNumber(out var length) || !reader.TryExpect(':') || !reader.TryTake(length, out var digits))
                    return Fail($"node {index}: invalid number framing", out problem);
                if (!TryParseCanonicalNumber(digits, out var number))
                    return Fail($"node {index}: {PreviewText(digits)} is not a canonical number", out problem);
                node = new Result.Atom(number);
                break;
            }

            case 't':
            {
                if (!reader.TryNumber(out var length) || !reader.TryExpect(':') || length > reader.Remaining)
                    return Fail($"node {index}: invalid string framing", out problem);
                var units = new StringBuilder(length);
                for (var unit = 0; unit < length; unit++)
                {
                    if (!reader.TryReadUnit(out var decoded))
                        return Fail($"node {index}: invalid or truncated string unit {unit}", out problem);
                    units.Append(decoded);
                }

                node = new Result.Str(units.ToString());
                break;
            }

            case 's' or 'l':
            {
                if (!reader.TryNumber(out var childCount) || !reader.TryExpect(':')
                    || reader.Remaining < 1 || childCount > (reader.Remaining - 1) / 2)
                    return Fail($"node {index}: invalid structure framing", out problem);
                var items = new Result[childCount];
                for (var child = 0; child < childCount; child++)
                {
                    if (!reader.TryNumber(out var childId) || !reader.TryExpect(','))
                        return Fail($"node {index}: invalid child {child}", out problem);
                    if (childId >= index) return Fail($"node {index}: child {child} is not an earlier node", out problem);
                    items[child] = nodes[childId];
                }

                if (!reader.TryExpect(';')) return Fail($"node {index}: unterminated structure", out problem);
                node = tag == 's' ? new Result.SequenceValue(items) : new Result.ListValue(items);
                break;
            }

            default:
                return Fail($"node {index}: unknown tag {QuoteText(tag.ToString())}", out problem);
        }

        problem = "ok";
        return true;
    }

    private static bool Fail(string reason, out string problem)
    {
        problem = reason;
        return false;
    }

    private static void AppendEscaped(StringBuilder text, string value)
    {
        foreach (var unit in value)
        {
            if (unit == '\\') text.Append("\\\\");
            else if (unit is >= ' ' and <= '~') text.Append(unit);
            else text.Append("\\u").Append(((int)unit).ToString("X4", CultureInfo.InvariantCulture));
        }
    }

    /// <summary>One open structure level: the node, its next child index, and its completed child ids.</summary>
    private sealed class Frame(Result node)
    {
        public Result Node { get; } = node;

        public IReadOnlyList<Result> Items { get; } = node switch
        {
            Result.SequenceValue sequence => sequence.Items,
            Result.ListValue list => list.Items,
            _ => throw new InvalidOperationException($"{node.GetType().Name} is not a structure."),
        };

        public int Next { get; set; }

        public List<int> ChildIds { get; } = [];
    }

    /// <summary>The hash-consed definition table of one encoding call; discarded with it.</summary>
    private sealed class Table
    {
        private readonly Dictionary<Result, int> byReference = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<string, int> byDefinition = new(StringComparer.Ordinal);
        private readonly StringBuilder definitions = new(64);
        private readonly StringBuilder scratch = new(32);

        /// <summary>Resolves an already-seen reference or a scalar; <c>false</c> for an unseen structure.</summary>
        public bool TryLeaf(Result node, out int id)
        {
            if (byReference.TryGetValue(node, out id)) return true;

            scratch.Clear();
            switch (node)
            {
                case Result.Atom atom:
                {
                    var number = CanonicalNumber(atom.Value);
                    scratch.Append('n').Append(number.Length.ToString(CultureInfo.InvariantCulture)).Append(':').Append(number);
                    break;
                }

                case Result.Bool flag:
                    scratch.Append(flag.Value ? "b1" : "b0");
                    break;

                case Result.Str str:
                    scratch.Append(QuoteText(str.Value));
                    break;

                case Result.SequenceValue or Result.ListValue:
                    return false;

                default:
                    throw new InvalidOperationException(
                        $"{node.GetType().Name} is not a completed run value and has no structural identity.");
            }

            id = Intern(scratch.ToString());
            byReference[node] = id;
            return true;
        }

        public int Complete(Frame frame)
        {
            scratch.Clear();
            scratch.Append(frame.Node is Result.ListValue ? 'l' : 's')
                .Append(frame.ChildIds.Count.ToString(CultureInfo.InvariantCulture)).Append(':');
            foreach (var childId in frame.ChildIds)
                scratch.Append(childId.ToString(CultureInfo.InvariantCulture)).Append(',');
            scratch.Append(';');

            var id = Intern(scratch.ToString());
            byReference[frame.Node] = id;
            return id;
        }

        public string Render(int rootId)
        {
            // Post-order completion makes the root the last definition ever added.
            if (rootId != byDefinition.Count - 1)
                throw new MetamorphicHarnessException("The structural identity root is not the last definition.");
            return Header + byDefinition.Count.ToString(CultureInfo.InvariantCulture) + ":" + definitions;
        }

        private int Intern(string definition)
        {
            if (byDefinition.TryGetValue(definition, out var existing)) return existing;
            var id = byDefinition.Count;
            byDefinition.Add(definition, id);
            definitions.Append(definition);
            return id;
        }
    }

    private struct Reader(string text)
    {
        public int Position;

        public readonly int Remaining => text.Length - Position;

        public bool TryRead(out char value)
        {
            if (Position >= text.Length)
            {
                value = default;
                return false;
            }

            value = text[Position++];
            return true;
        }

        public bool TryExpect(char expected)
        {
            if (Position >= text.Length || text[Position] != expected) return false;
            Position++;
            return true;
        }

        /// <summary>A canonical non-negative decimal integer: no sign, no leading zero unless it is 0.</summary>
        public bool TryNumber(out int value)
        {
            value = 0;
            var start = Position;
            while (Position < text.Length && text[Position] is >= '0' and <= '9')
            {
                var digit = text[Position] - '0';
                if (value > (int.MaxValue - digit) / 10) return false;
                value = (value * 10) + digit;
                Position++;
            }

            var length = Position - start;
            return length > 0 && (length == 1 || text[start] != '0');
        }

        public bool TryTake(int length, out string value)
        {
            if (length < 0 || length > Remaining)
            {
                value = "";
                return false;
            }

            value = text.Substring(Position, length);
            Position += length;
            return true;
        }

        /// <summary>One escaped UTF-16 code unit, accepting only the canonical spelling.</summary>
        public bool TryReadUnit(out char unit)
        {
            if (!TryRead(out unit)) return false;
            if (unit != '\\') return unit is >= ' ' and <= '~';
            if (!TryRead(out var marker)) return false;
            if (marker == '\\')
            {
                unit = '\\';
                return true;
            }

            if (marker != 'u' || !TryTake(4, out var hex)) return false;
            foreach (var digit in hex)
            {
                if (digit is not ((>= '0' and <= '9') or (>= 'A' and <= 'F'))) return false;
            }

            unit = (char)int.Parse(hex, NumberStyles.AllowHexSpecifier, CultureInfo.InvariantCulture);
            // Printable ASCII, the backslash included, is never spelled \uXXXX.
            return unit is not (>= ' ' and <= '~');
        }
    }
}
