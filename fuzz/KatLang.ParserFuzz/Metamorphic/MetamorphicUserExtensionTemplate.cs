using System.Collections.Immutable;
using System.Globalization;
using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>One reviewed extension-function body, with the suffix arity it needs.</summary>
internal sealed record MetamorphicExtensionBody(string Id, string Body, int SuffixArity, bool SuffixIsSpread = false);

/// <summary>
/// Group B — a USER-defined function called ordinarily against the same function called in
/// dotted extension style.
///
/// <code>
/// MmF(r, n) = &lt;body&gt;                MmF(r, n) = &lt;body&gt;
/// MmR = &lt;receiver&gt;                  MmR = &lt;receiver&gt;
/// Output = MmF(MmR, 2)              Output = MmR.MmF(2)
/// </code>
///
/// <para><b>Equivalence argument.</b> The same receiver-first rewrite as Group A, applied to a
/// user callable: <c>A.F(B, C)</c> is <c>F(A, B, C)</c>. Written argument boundaries are
/// preserved exactly — the template NEVER introduces a spread when building the dotted form,
/// and the one spread body it generates places the spread identically in the SUFFIX of both
/// members (<c>F(R, MmS*)</c> against <c>R.F(MmS*)</c>), never on the receiver, which has no
/// dotted spelling at all.</para>
///
/// <para><b>Receiver evaluation.</b> The receiver is written as a whole expression on both
/// sides (a property reference bound to a compact collection construction), so evaluating it
/// twice would be operationally visible as doubled item materialization. That is the property
/// the exact-work relation is here to keep true.</para>
///
/// <para>This family declares <see cref="MetamorphicOperationalRelation.ExactObservedWorkEqual"/>:
/// the two spellings resolve to one and the same user invocation, so steps and peak depth must
/// match too — the contract the repository already asserts in
/// <c>OperationalMetamorphicTests.UserExtensionCall_ChargesTheSameInBothForms</c>.</para>
/// </summary>
internal static class MetamorphicUserExtensionTemplate
{
    private const int BodyDimension = 0;
    private const int ReceiverDimension = 1;
    private const int SuffixDimension = 2;

    private const string R = MetamorphicTables.ReceiverProperty;
    private const string F = MetamorphicTables.ExtensionFunction;

    /// <summary>
    /// Reviewed bodies whose semantics are stable and whose receiver boundary is observable.
    /// Nothing here is generated freely: the fuzzer selects a body, never invents one.
    /// </summary>
    internal static readonly ImmutableArray<MetamorphicExtensionBody> Bodies =
    [
        new("identity", "r", 0),
        new("receiverCount", "r.count", 0),
        new("firstElement", "r:0", 0),
        new("wrapInList", "[r]", 0),
        new("spreadIntoList", "[r*]", 0),
        new("builtinCall", "take(r, 1)", 0),
        new("multipleOutputs", "r, r", 0),
        new("constantList", "[1, 2]", 0),
        new("constantSequence", "(1, 2)", 0),
        new("dottedChainBody", "r.distinct.count", 0),
        new("takeSuffix", "take(r, a)", 1),
        new("pairList", "[r, a]", 1),
        new("dottedTakeSuffix", "r.take(a)", 1),
        new("countPlusSuffix", "r.count + a", 1),
        new("multipleOutputsSuffix", "r, a", 1),
        new("tripleList", "[r, a, b]", 2),
        new("sequenceOfSuffixes", "(a, b)", 2),
        new("spreadSuffix", "[r, a, b]", 2, SuffixIsSpread: true),
    ];

    internal static int BodyCount => Bodies.Length;

    /// <summary>Compact suffix argument values; index 0 is used when a body takes no suffix.</summary>
    private static readonly ImmutableArray<int> SuffixValues = [0, 1, 2, 3, 4, -1];

    internal static MetamorphicExtensionBody BodyOf(MetamorphicParameters parameters)
        => Bodies[parameters.Extra(BodyDimension)];

    internal static MetamorphicValueShape ReceiverOf(MetamorphicParameters parameters)
        => MetamorphicTables.ReceiverShapes[parameters.Extra(ReceiverDimension)];

    /// <summary>
    /// Collapses the suffix dimension to its canonical index wherever the selected body does not
    /// USE it: a zero-suffix body writes no suffix at all, and a spread-suffix body writes the
    /// same generated <c>MmS*</c> whatever the variant says. Leaving an ignored dimension free
    /// would let several payloads build byte-identical pairs and then be reported under distinct
    /// fingerprints — corpus and campaign effort spent re-testing one case.
    ///
    /// <para>Idempotent, which <c>Decode(Encode(p)) == p</c> requires: the canonical index
    /// normalizes to itself.</para>
    /// </summary>
    internal static MetamorphicParameters Normalize(MetamorphicParameters parameters)
    {
        var variants = SuffixVariantCount(BodyOf(parameters));
        return parameters.WithExtra(SuffixDimension, checked(parameters.Extra(SuffixDimension) % variants));
    }

    /// <summary>How many DISTINCT pairs the suffix dimension can produce for one body.</summary>
    internal static int SuffixVariantCount(MetamorphicExtensionBody body)
    {
        ArgumentNullException.ThrowIfNull(body);
        return body.SuffixArity == 0 || body.SuffixIsSpread ? 1 : SuffixValues.Length;
    }

    internal static MetamorphicPrecondition Validate(MetamorphicParameters parameters)
    {
        var body = BodyOf(parameters);

        // Unreachable for decoded points (Normalize collapses an ignored suffix dimension, and
        // MetamorphicTemplates.Build refuses anything the decoder did not produce); kept as a
        // guard so a body whose suffix dimension is ignored can never be silently split in two.
        if (SuffixVariantCount(body) == 1 && parameters.Extra(SuffixDimension) != 0)
            return MetamorphicPrecondition.Rejected("suffix-variant-on-a-body-that-ignores-it");

        if (body.SuffixArity is < 0 or > 2)
            return MetamorphicPrecondition.Rejected("unsupported-suffix-arity");

        // A spread body must place the spread in the SUFFIX; a spread receiver has no dotted
        // spelling, so such a pair could never be equivalent and is not constructible here.
        if (body.SuffixIsSpread && body.SuffixArity < 2)
            return MetamorphicPrecondition.Rejected("spread-suffix-needs-two-suffix-parameters");

        var receiver = ReceiverOf(parameters);
        if (receiver.Source.StartsWith('(') && receiver.Source.Contains('=', StringComparison.Ordinal))
            return MetamorphicPrecondition.Rejected("block-valued-receiver-resolves-structurally");

        return MetamorphicPrecondition.Ok;
    }

    internal static string DescribeVariant(MetamorphicParameters parameters)
    {
        var body = BodyOf(parameters);
        return $"body={body.Id} suffixArity={body.SuffixArity.ToString(CultureInfo.InvariantCulture)} " +
               $"spreadSuffix={(body.SuffixIsSpread ? "yes" : "no")} receiver={ReceiverOf(parameters).Id} " +
               $"suffixVariant={parameters.Extra(SuffixDimension)}";
    }

    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        var body = BodyOf(parameters);
        var receiver = ReceiverOf(parameters);
        var suffixValue = SuffixValues[parameters.Extra(SuffixDimension)].ToString(CultureInfo.InvariantCulture);

        var parameterNames = body.SuffixArity switch
        {
            0 => "r",
            1 => "r, a",
            _ => "r, a, b",
        };

        var preamble = new StringBuilder()
            .Append(F).Append('(').Append(parameterNames).Append(") = ").Append(body.Body).Append('\n')
            .Append(R).Append(" = ").Append(receiver.Source).Append('\n');

        string left;
        string right;
        if (body.SuffixIsSpread)
        {
            // Identical spread on both sides, in the suffix only.
            preamble.Append(MetamorphicTables.NamePrefix).Append("S = (8, 9)\n");
            var spread = MetamorphicTables.NamePrefix + "S*";
            left = $"{preamble}Output = {F}({R}, {spread})";
            right = $"{preamble}Output = {R}.{F}({spread})";
        }
        else
        {
            var suffixList = body.SuffixArity switch
            {
                0 => "",
                1 => suffixValue,
                _ => suffixValue + ", 2",
            };

            var ordinaryArguments = suffixList.Length == 0 ? R : R + ", " + suffixList;
            var dottedSuffix = suffixList.Length == 0 ? "" : "(" + suffixList + ")";
            left = $"{preamble}Output = {F}({ordinaryArguments})";
            right = $"{preamble}Output = {R}.{F}{dottedSuffix}";
        }

        return MetamorphicCaseFactory.Create(
            parameters,
            left,
            right,
            Validate(parameters),
            $"user extension body '{body.Id}' with {body.SuffixArity.ToString(CultureInfo.InvariantCulture)} " +
            $"suffix parameter(s), receiver {receiver.Id} = {receiver.Source}");
    }
}
