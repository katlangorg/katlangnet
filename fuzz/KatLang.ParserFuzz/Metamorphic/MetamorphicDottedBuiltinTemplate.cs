using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>
/// Group A — a trusted collection builtin written as an ordinary call against the same call
/// written in dotted extension style.
///
/// <code>
/// MmR = &lt;receiver&gt;                 MmR = &lt;receiver&gt;
/// Output = F(MmR, suffix...)        Output = MmR.F(suffix...)
/// </code>
///
/// <para><b>Equivalence argument.</b> KatLang DEFINES the dotted form as the ordinary
/// receiver-first call: <c>A.F(B, C)</c> means <c>F(A, B, C)</c>, with the receiver supplied as
/// ONE leading argument boundary — never <c>F(A..., B, C)</c>. Every builtin in
/// <see cref="MetamorphicTables.Builtins"/> is a fixed-arity callable whose first parameter is
/// the receiver, so the two spellings are the same call and the same argument boundaries.</para>
///
/// <para>The receiver is bound to a PROPERTY rather than inlined, so both sides write the
/// identical receiver expression and the comparison isolates the call form itself. Structural
/// member access is impossible here: the receiver is a value, and the member is a prelude
/// builtin, so the dotted form always resolves through the extension-call path.</para>
/// </summary>
internal static class MetamorphicDottedBuiltinTemplate
{
    private const int BuiltinDimension = 0;
    private const int ReceiverDimension = 1;
    private const int SuffixDimension = 2;

    internal static MetamorphicBuiltin BuiltinOf(MetamorphicParameters parameters)
        => MetamorphicTables.Builtins[parameters.Extra(BuiltinDimension)];

    internal static MetamorphicValueShape ReceiverOf(MetamorphicParameters parameters)
        => MetamorphicTables.ReceiverShapes[parameters.Extra(ReceiverDimension)];

    /// <summary>Reduces the suffix variant to the count its builtin actually offers.</summary>
    internal static MetamorphicParameters Normalize(MetamorphicParameters parameters)
    {
        var variants = MetamorphicTables.SuffixVariantCount(BuiltinOf(parameters).SuffixKind);
        return parameters.WithExtra(SuffixDimension, checked(parameters.Extra(SuffixDimension) % variants));
    }

    internal static MetamorphicPrecondition Validate(MetamorphicParameters parameters)
    {
        var builtin = BuiltinOf(parameters);
        var receiver = ReceiverOf(parameters);

        if (parameters.Extra(SuffixDimension) >= MetamorphicTables.SuffixVariantCount(builtin.SuffixKind))
            return MetamorphicPrecondition.Rejected("suffix-variant-out-of-range");

        // A block-valued receiver would resolve `.F` as STRUCTURAL member access instead of an
        // extension call, which is a different language construct and out of this relation's
        // scope. The receiver table contains only value shapes, so this is a guard, not a filter.
        if (receiver.Source.StartsWith('(') && receiver.Source.Contains('=', StringComparison.Ordinal))
            return MetamorphicPrecondition.Rejected("block-valued-receiver-resolves-structurally");

        return MetamorphicPrecondition.Ok;
    }

    internal static string DescribeVariant(MetamorphicParameters parameters)
        => $"builtin={BuiltinOf(parameters).Name} receiver={ReceiverOf(parameters).Id} " +
           $"suffixVariant={parameters.Extra(SuffixDimension)}";

    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        var builtin = BuiltinOf(parameters);
        var receiver = ReceiverOf(parameters);
        var suffix = MetamorphicTables.SuffixArguments(
            builtin, parameters.Extra(SuffixDimension), receiver.CollectionItemCount);

        var preamble = new StringBuilder();
        if (MetamorphicTables.NeedsCallbackPreamble(builtin, suffix))
            preamble.Append(MetamorphicTables.CallbackPreamble);
        preamble.Append(MetamorphicTables.ReceiverProperty).Append(" = ").Append(receiver.Source).Append('\n');

        var ordinaryArguments = suffix.Length == 0
            ? MetamorphicTables.ReceiverProperty
            : MetamorphicTables.ReceiverProperty + ", " + suffix;
        var dottedSuffix = suffix.Length == 0 ? "" : "(" + suffix + ")";

        var left = $"{preamble}Output = {builtin.Name}({ordinaryArguments})";
        var right = $"{preamble}Output = {MetamorphicTables.ReceiverProperty}.{builtin.Name}{dottedSuffix}";

        return MetamorphicCaseFactory.Create(
            parameters,
            left,
            right,
            Validate(parameters),
            $"{builtin.Name}(receiver{(suffix.Length == 0 ? "" : ", " + suffix)}) against the dotted spelling, " +
            $"receiver {receiver.Id} = {receiver.Source}");
    }
}
