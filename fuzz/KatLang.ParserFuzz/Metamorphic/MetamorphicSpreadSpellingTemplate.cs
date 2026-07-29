using System.Collections.Immutable;
using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// One pair of still-equivalent spellings of the same spread program.
/// </summary>
/// <param name="Id">Stable context identifier used in variant descriptions.</param>
/// <param name="Preamble">Shared declarations emitted after the operand property.</param>
/// <param name="LeftLine">The explicit-call / single-grouping spelling's output line.</param>
/// <param name="RightLine">The fluent-chain / redundant-grouping spelling's output line.</param>
/// <param name="OperationalRelation">
/// The operational strength this context earns. The fluent-chain contexts lower to the
/// IDENTICAL AST on both sides, so they claim exact observed-work equality; the
/// redundant-grouping context adds a real (if tiny) extra block layer on the right, so it
/// makes no operational claim at all.
/// </param>
/// <param name="DerivedBudgetSafe">
/// False when the two spellings may charge slightly different totals, so a limit DERIVED
/// from the left member's measurement could stop one side and not the other. Such contexts
/// only run under the default and generous policies.
/// </param>
internal sealed record MetamorphicSpreadContext(
    string Id,
    string Preamble,
    string LeftLine,
    string RightLine,
    MetamorphicOperationalRelation OperationalRelation,
    bool DerivedBudgetSafe);

/// <summary>
/// Phase 2 Group E: two STILL-EQUIVALENT spellings of one spread program under the star
/// syntax — chiefly the fluent chain <c>X*.C</c> against the explicit call <c>C(X*)</c>,
/// over every trusted operand shape.
///
/// <para>The fluent dot continuation lowers at parse time to the ordinary lexical call with
/// the spread as the leading argument slot — the exact AST the explicit spelling builds — so
/// those contexts assert the strongest relations the harness has: semantic equality AND
/// exact observed-work equality. A divergence in parse eligibility, value, structured error,
/// resource-limit classification, or charged evaluation steps between the spellings is a
/// real lowering bug, never template noise.</para>
///
/// <para>The one non-lowering context pairs the grouped spread <c>(X*)</c> with its
/// redundantly grouped form <c>((X*))</c>: redundant unary sequence grouping canonicalizes
/// during value construction, so the two sides are semantically equal, but the extra block
/// layer is real work, so that context declares no operational relation and is confined to
/// execution policies whose limits are not derived from one member's measurement.</para>
/// </summary>
internal static class MetamorphicSpreadSpellingTemplate
{
    private const int ContextDimension = 0;
    private const int OperandDimension = 1;

    private const string X = MetamorphicTables.NamePrefix + "X";
    private const string C = MetamorphicTables.NamePrefix + "C";

    /// <summary>The collecting consumer both spellings call: total over any supplied slots.</summary>
    private const string ConsumerPreamble = C + "(*xs) = xs\n";

    /// <summary>
    /// The spelling pairs. The operand is always the shared property <see cref="X"/>, so the
    /// operand expression and its single evaluation are identical on both sides. Order and
    /// count are a seed-compatibility surface: existing payloads index this table.
    /// </summary>
    internal static readonly ImmutableArray<MetamorphicSpreadContext> Contexts =
    [
        new(
            "fluentRoot",
            ConsumerPreamble,
            $"Output = {C}({X}*)",
            $"Output = {X}*.{C}",
            MetamorphicOperationalRelation.ExactObservedWorkEqual,
            DerivedBudgetSafe: true),
        new(
            "fluentSuffix",
            ConsumerPreamble,
            $"Output = {C}({X}*, 99)",
            $"Output = {X}*.{C}(99)",
            MetamorphicOperationalRelation.ExactObservedWorkEqual,
            DerivedBudgetSafe: true),
        new(
            "fluentDouble",
            ConsumerPreamble,
            $"Output = {C}({X}**)",
            $"Output = {X}**.{C}",
            MetamorphicOperationalRelation.ExactObservedWorkEqual,
            DerivedBudgetSafe: true),
        new(
            "fluentGroupedOperand",
            ConsumerPreamble,
            $"Output = {C}(({X})*)",
            $"Output = ({X})*.{C}",
            MetamorphicOperationalRelation.ExactObservedWorkEqual,
            DerivedBudgetSafe: true),
        new(
            "fluentContinuation",
            ConsumerPreamble,
            $"Output = {C}({X}*).count",
            $"Output = {X}*.{C}.count",
            MetamorphicOperationalRelation.ExactObservedWorkEqual,
            DerivedBudgetSafe: true),
        new(
            "groupedRedundant",
            "",
            $"Output = ({X}*)",
            $"Output = (({X}*))",
            MetamorphicOperationalRelation.NotCompared,
            DerivedBudgetSafe: false),
    ];

    internal static int ContextCount => Contexts.Length;

    private static MetamorphicSpreadContext ContextOf(MetamorphicParameters parameters)
        => Contexts[parameters.Extra(ContextDimension)];

    private static MetamorphicValueShape OperandOf(MetamorphicParameters parameters)
        => MetamorphicTables.ReceiverShapes[parameters.Extra(OperandDimension)];

    /// <summary>Every dimension is always meaningful, so the canonical index is the index itself.</summary>
    internal static MetamorphicParameters Normalize(MetamorphicParameters parameters) => parameters;

    /// <summary>
    /// Spread is total over every trusted operand shape (atoms and strings supply themselves;
    /// sequences and lists open one boundary; empties supply zero items), and the collecting
    /// consumer accepts any slot count, so semantic agreement never depends on the operand.
    /// The redundant-grouping context alone is rejected under measurement-derived limit
    /// policies: its right member legitimately charges a little more than the left member the
    /// limits were calibrated on, so a boundary-placed budget could split the pair without
    /// disproving anything about the language.
    /// </summary>
    internal static MetamorphicPrecondition Validate(MetamorphicParameters parameters)
    {
        var context = ContextOf(parameters);
        if (!context.DerivedBudgetSafe
            && parameters.LimitMode is not (MetamorphicLimitMode.Default or MetamorphicLimitMode.Generous))
        {
            return MetamorphicPrecondition.Rejected("redundant-grouping-crosses-derived-budgets-differently");
        }

        return MetamorphicPrecondition.Ok;
    }

    /// <summary>Per-case operational relation: exact work for the parse-time-identical fluent
    /// contexts, no operational claim for the redundant-grouping context.</summary>
    internal static MetamorphicOperationalRelation SelectOperationalRelation(
        MetamorphicParameters parameters, EvaluationLimits? limits)
    {
        _ = limits;
        return ContextOf(parameters).OperationalRelation;
    }

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
