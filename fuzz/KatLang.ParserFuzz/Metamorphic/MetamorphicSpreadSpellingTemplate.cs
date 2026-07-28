using System.Collections.Immutable;
using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>One receiver context a spread expression can stand in as a whole slot.</summary>
internal sealed record MetamorphicSpreadContext(string Id, string Preamble, string LeftLine, string RightLine);

/// <summary>
/// Phase 2 Group E: the CALL spelling of the spread intrinsic against its
/// extension-property spelling — <c>spread(X)</c> versus <c>X.spread</c> —
/// over every trusted operand shape and every receiver context where a spread
/// slot is legal (root output, collecting-binding call, list literal, single
/// capture, grouped sequence value, and the chained form).
///
/// <para>The two spellings lower to the SAME <c>SequenceSpread</c> node at
/// parse time, so this family asserts the strongest relations the harness
/// has: semantic equality AND exact observed-work equality. A divergence in
/// parse eligibility, value, structured error, resource-limit classification,
/// or charged evaluation steps between the spellings is a real lowering bug,
/// never template noise.</para>
/// </summary>
internal static class MetamorphicSpreadSpellingTemplate
{
    private const int ContextDimension = 0;
    private const int OperandDimension = 1;

    private const string X = MetamorphicTables.NamePrefix + "X";
    private const string Y = MetamorphicTables.NamePrefix + "Y";
    private const string C = MetamorphicTables.NamePrefix + "C";

    /// <summary>
    /// The receiver contexts, each holding the full output line for the CALL
    /// spelling (left) and the PROPERTY spelling (right). The operand is
    /// always the shared property <see cref="X"/>, so the receiver expression
    /// and its single evaluation are identical on both sides.
    /// </summary>
    internal static readonly ImmutableArray<MetamorphicSpreadContext> Contexts =
    [
        new("rootOutput", "", $"Output = spread({X})", $"Output = {X}.spread"),
        new(
            "collectingCall",
            C + "(xs...) = xs\n",
            $"Output = {C}(spread({X}))",
            $"Output = {C}({X}.spread)"),
        new("listLiteral", "", $"Output = [spread({X}), 99]", $"Output = [{X}.spread, 99]"),
        new("singleCapture", $"{Y} = ", $"spread({X})\nOutput = {Y}", $"{X}.spread\nOutput = {Y}"),
        new("groupedSequence", "", $"Output = (spread({X}), 99)", $"Output = ({X}.spread, 99)"),
        new("chainedSpread", "", $"Output = [spread(spread({X})), 99]", $"Output = [{X}.spread.spread, 99]"),
    ];

    internal static int ContextCount => Contexts.Length;

    private static MetamorphicSpreadContext ContextOf(MetamorphicParameters parameters)
        => Contexts[parameters.Extra(ContextDimension)];

    private static MetamorphicValueShape OperandOf(MetamorphicParameters parameters)
        => MetamorphicTables.ReceiverShapes[parameters.Extra(OperandDimension)];

    /// <summary>Every dimension is always meaningful, so the canonical index is the index itself.</summary>
    internal static MetamorphicParameters Normalize(MetamorphicParameters parameters) => parameters;

    /// <summary>
    /// Spread is total over every trusted operand shape (atoms and strings
    /// supply themselves; sequences and lists open one boundary; empties
    /// supply zero items), and each context is a legal spread slot, so every
    /// decoded point builds.
    /// </summary>
    internal static MetamorphicPrecondition Validate(MetamorphicParameters parameters)
        => MetamorphicPrecondition.Ok;

    internal static string DescribeVariant(MetamorphicParameters parameters)
        => $"context={ContextOf(parameters).Id} operand={OperandOf(parameters).Id}";

    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        var context = ContextOf(parameters);
        var operand = OperandOf(parameters);

        var preamble = $"{X} = {operand.Source}\n{context.Preamble}";
        var left = preamble + context.LeftLine;
        var right = preamble + context.RightLine;

        return MetamorphicCaseFactory.Create(
            parameters,
            left,
            right,
            Validate(parameters),
            $"spread spelling parity in context '{context.Id}' over operand " +
            $"{operand.Id} = {operand.Source} " +
            $"({operand.CollectionItemCount.ToString(CultureInfo.InvariantCulture)} collection item(s))");
    }
}
