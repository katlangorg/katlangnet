using System.Globalization;
using System.Numerics;
using System.Text;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// KL-07: the hand-reviewed <c>kl-struct-v1</c> examples of the Lean exporter pilot
/// (<c>lean/CoreTests/StructuralIdentity.lean</c>). Each example is a C#-built value with its
/// expected text, written by hand from the format rules and reviewed against them; it is never
/// observed output. Three checks use the same table:
/// <list type="bullet">
/// <item>the C# encoder (<see cref="MetamorphicStructuralIdentity.Encode"/>) gives exactly that text
/// (<see cref="StructuralIdentityExporterTests"/>);</item>
/// <item>the hand-written Lean module carries a guard with that text for every Lean-comparable example;</item>
/// <item>the generated <c>lean/CoreTests/HostParentDifferential.lean</c> writes every Lean-comparable
/// example as a Lean literal (<see cref="LeanLiteral"/>) and guards that the Lean exporter's text
/// equals the C# encoder's text of the C# value.</item>
/// </list>
/// An example whose value Lean cannot represent (a fractional atom) is a C# encoder check only.
/// </summary>
internal static class StructuralIdentityExamples
{
    /// <param name="Name">Stable example name, also written in the generated guard's comment.</param>
    /// <param name="Value">The C#-built value.</param>
    /// <param name="Expected">The hand-reviewed <c>kl-struct-v1</c> text.</param>
    /// <param name="LeanComparable">Whether Lean can represent the value (integer atoms only).</param>
    internal sealed record Example(string Name, Result Value, string Expected, bool LeanComparable = true);

    internal static IReadOnlyList<Example> All { get; } = Build();

    internal static IEnumerable<Example> LeanComparable => All.Where(static example => example.LeanComparable);

    private static List<Example> Build()
    {
        static Result Num(string text) => new Result.Atom(Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture));
        static Result Str(string value) => new Result.Str(value);
        static Result Seq(params Result[] items) => new Result.SequenceValue(items);
        static Result List(params Result[] items) => new Result.ListValue(items);

        var pair = List(Num("1"), Str("a"));

        return
        [
            // Number classes: both zeros read 0, a negative keeps its sign, and trailing zeros move into
            // the exponent: Lean 1200 and C# 1200 / 1200.00 are the one class 12e2.
            new("zero", Num("0"), "kl-struct-v1:1:n1:0"),
            new("negative-zero", Num("-0"), "kl-struct-v1:1:n1:0"),
            new("seven", Num("7"), "kl-struct-v1:1:n3:7e0"),
            new("integer-1200", Num("1200"), "kl-struct-v1:1:n4:12e2"),
            new("integer-1200.00", Num("1200.00"), "kl-struct-v1:1:n4:12e2"),
            new("negative-5", Num("-5"), "kl-struct-v1:1:n4:-5e0"),
            new("negative-120", Num("-120"), "kl-struct-v1:1:n5:-12e1"),
            // C# encoder checks only: Lean has no fractional atom.
            new("fraction-1.5", Num("1.5"), "kl-struct-v1:1:n5:15e-1", LeanComparable: false),
            new("fraction-1.50", Num("1.50"), "kl-struct-v1:1:n5:15e-1", LeanComparable: false),

            // KL-07: both lists have the neutral text L['a', 'b'].
            new("collision-two-strings", List(Str("a"), Str("b")), "kl-struct-v1:3:t1:at1:bl2:0,1,;"),
            new("collision-one-string", List(Str("a', 'b")), "kl-struct-v1:2:t6:a', 'bl1:0,;"),

            // () against [], and Booleans against numbers and strings.
            new("empty-sequence", Seq(), "kl-struct-v1:1:s0:;"),
            new("empty-list", List(), "kl-struct-v1:1:l0:;"),
            new("booleans", List(new Result.Bool(true), new Result.Bool(false)), "kl-struct-v1:3:b1b0l2:0,1,;"),
            new("kinds", List(Num("1"), Str("1"), new Result.Bool(true)), "kl-struct-v1:4:n3:1e0t1:1b1l3:0,1,2,;"),

            // Strings: a doubled backslash; printable ASCII (quote, space, tilde) as itself; escaped line
            // feed and tab; a BMP unit; surrogate pairs counted as two UTF-16 units.
            new("backslash", Str("a\\b"), "kl-struct-v1:1:t3:a\\\\b"),
            new("printable", Str("\"q\" ~"), "kl-struct-v1:1:t5:\"q\" ~"),
            new("controls", Str("a\nb\t"), "kl-struct-v1:1:t4:a\\u000Ab\\u0009"),
            new("non-bmp", Str("\U0001F600"), "kl-struct-v1:1:t2:\\uD83D\\uDE00"),
            new("bmp-and-non-bmp", Str("é\U00010437x"), "kl-struct-v1:1:t4:\\u00E9\\uD801\\uDC37x"),

            // Nested lists and sequences, in post-order.
            new("nested", Seq(Num("1"), List(Num("2"), Seq()), List()), "kl-struct-v1:6:n3:1e0n3:2e0s0:;l2:1,2,;l0:;s3:0,3,4,;"),

            // Equal subtrees with different sharing: one object twice, two equal objects.
            new("shared-subtree", Seq(pair, pair), "kl-struct-v1:4:n3:1e0t1:al2:0,1,;s2:2,2,;"),
            new("independent-subtrees", Seq(List(Num("1"), Str("a")), List(Num("1.0"), Str("a"))),
                "kl-struct-v1:4:n3:1e0t1:al2:0,1,;s2:2,2,;"),
            new("repeated-atom", List(Num("7"), Num("7")), "kl-struct-v1:2:n3:7e0l2:0,0,;"),
            new("repeated-across-levels", List(List(Num("1")), Num("1")), "kl-struct-v1:3:n3:1e0l1:0,;l2:1,0,;"),

            // Multi-digit ids, counts and string lengths.
            new("eleven-atoms", List([.. Enumerable.Range(0, 11).Select(i => Num(i.ToString(CultureInfo.InvariantCulture)))]),
                "kl-struct-v1:12:n1:0n3:1e0n3:2e0n3:3e0n3:4e0n3:5e0n3:6e0n3:7e0n3:8e0n3:9e0n3:1e1l11:0,1,2,3,4,5,6,7,8,9,10,;"),
            new("long-string", Str("hello, world"), "kl-struct-v1:1:t12:hello, world"),
        ];
    }

    /// <summary>
    /// The Lean <c>Result</c> literal of a C#-built value: an atom as its exact integer (derived from
    /// its canonical class, so <c>1200.00</c> is <c>.atom 1200</c> and <c>-0</c> is <c>.atom 0</c>), a
    /// string through <see cref="LeanAstEncoder.QuoteString"/> (which refuses what a Lean string cannot
    /// hold). Fails loudly on a value Lean cannot represent: a fractional or non-finite atom, or a
    /// call reference.
    /// </summary>
    internal static string LeanLiteral(Result value)
    {
        var text = new StringBuilder();
        Append(text, value);
        return text.ToString();

        static void Append(StringBuilder text, Result value)
        {
            switch (value)
            {
                case Result.Atom atom:
                    var integer = LeanInteger(atom.Value);
                    text.Append(integer.StartsWith('-') ? $"(.atom ({integer}))" : $"(.atom {integer})");
                    break;
                case Result.Bool flag:
                    text.Append(flag.Value ? "(.bool true)" : "(.bool false)");
                    break;
                case Result.Str str:
                    text.Append("(.str ").Append(LeanAstEncoder.QuoteString(str.Value)).Append(')');
                    break;
                case Result.SequenceValue sequence:
                    AppendItems(text, "(.sequenceValue [", sequence.Items);
                    break;
                case Result.ListValue list:
                    AppendItems(text, "(.listValue [", list.Items);
                    break;
                default:
                    throw new NotSupportedException($"{value.GetType().Name} has no Lean result literal.");
            }
        }

        static void AppendItems(StringBuilder text, string open, IReadOnlyList<Result> items)
        {
            text.Append(open);
            for (var i = 0; i < items.Count; i++)
            {
                if (i > 0) text.Append(", ");
                Append(text, items[i]);
            }

            text.Append("])");
        }
    }

    /// <summary>The exact integer of an integral Decimal128, read from its canonical class.</summary>
    private static string LeanInteger(Decimal128 number)
    {
        var canonical = MetamorphicStructuralIdentity.CanonicalNumber(number);
        if (canonical == "0") return "0";
        var e = canonical.IndexOf('e', StringComparison.Ordinal);
        if (e < 0 || canonical[(e + 1)..].StartsWith('-'))
            throw new NotSupportedException($"The number class {canonical} is not an integer, so Lean cannot represent it.");
        var exponent = int.Parse(canonical.AsSpan(e + 1), NumberStyles.None, CultureInfo.InvariantCulture);
        return canonical[..e] + new string('0', exponent);
    }
}
