using System.Globalization;
using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>
/// Group D — a DIRECT builtin callback against a user wrapper with a provably equivalent
/// callback projection.
///
/// <code>
/// MmRows = [[1, 2], [3]]            MmWrap(a) = a.count
/// Output = MmRows.map(count)        MmRows = [[1, 2], [3]]
///                                   Output = MmRows.map(MmWrap)
/// </code>
///
/// <para><b>Equivalence argument, and why it is narrow.</b> KatLang's flat-callback binding is
/// receiver-specific and is NOT ordinary function-call argument binding. A consumer supplies a
/// fixed number of values per invocation (one for <c>map</c>/<c>filter</c>, two for
/// <c>reduce</c>), and only a wrapper whose parameter list binds exactly those values
/// positionally sees the same per-invocation values as the direct builtin. Two projections are
/// therefore always REJECTED, not compared:</para>
/// <list type="bullet">
///   <item><b>Variadic</b> — <c>MmWrap(...xs)</c> COLLECTS the supplied slots into an exact list, so
///   the wrapper sees <c>[element]</c> where the builtin sees <c>element</c>. Measured:
///   <c>[[1, 2], [3]].map(count)</c> is <c>[2, 1]</c> while the variadic wrapper gives
///   <c>[1, 1]</c>. That is correct language behaviour and a false equivalence, not a defect.</item>
///   <item><b>ArityMismatched</b> — a flat multi-parameter callee first opens a lone
///   SEQUENCE-valued element into row slots and arity-errors on other kinds, so it neither
///   matches a one-value consumer nor a two-value one.</item>
/// </list>
///
/// <para><b>Algorithm/value duality.</b> The callback is written as a NAME in both members, so
/// the builtin's callable-algorithm channel is used on both sides and the harness never forces
/// an algorithm-only argument into a value. A materialization difference between the two forms
/// would mean a prepared callback value was reconstructed through Result -> Expr -> evaluator,
/// which is a production operational defect rather than a reason to weaken the relation.</para>
/// </summary>
internal static class MetamorphicCallbackWrapperTemplate
{
    private const int ConsumerDimension = 0;
    private const int CallbackDimension = 1;
    private const int InputDimension = 2;
    private const int ProjectionDimension = 3;

    private const string Rows = MetamorphicTables.RowsProperty;
    private const string Wrap = MetamorphicTables.WrapperFunction;

    internal static string ConsumerOf(MetamorphicParameters parameters)
        => MetamorphicTables.CallbackConsumers[parameters.Extra(ConsumerDimension)];

    internal static MetamorphicBuiltin CallbackOf(MetamorphicParameters parameters)
        => MetamorphicTables.Builtins[parameters.Extra(CallbackDimension)];

    internal static MetamorphicValueShape InputOf(MetamorphicParameters parameters)
        => MetamorphicTables.CallbackInputShapes[parameters.Extra(InputDimension)];

    internal static MetamorphicWrapperProjection ProjectionOf(MetamorphicParameters parameters)
        => MetamorphicTables.WrapperProjections[parameters.Extra(ProjectionDimension)];

    /// <summary>
    /// Reduces the callback dimension to the builtins that can validly appear as a callback of
    /// the selected consumer's arity, so a decoded point never names an impossible callback.
    /// </summary>
    internal static MetamorphicParameters Normalize(MetamorphicParameters parameters)
    {
        var arity = MetamorphicTables.CallbackArityOf(ConsumerOf(parameters));
        var eligible = EligibleCallbackIndices(arity);
        if (eligible.Count == 0) return parameters;

        var raw = parameters.Extra(CallbackDimension);

        // IDEMPOTENT by construction: an index that already names an eligible callback is kept,
        // so normalizing a normalized point is a fixed point and Decode(Encode(p)) == p holds.
        // Reducing unconditionally would remap an already-canonical index to a different one.
        if (eligible.Contains(raw)) return parameters;

        return parameters.WithExtra(CallbackDimension, eligible[checked(raw % eligible.Count)]);
    }

    private static List<int> EligibleCallbackIndices(int arity)
    {
        var indices = new List<int>(MetamorphicTables.Builtins.Length);
        for (var i = 0; i < MetamorphicTables.Builtins.Length; i++)
        {
            if (MetamorphicTables.Builtins[i].IsCallbackOfArity(arity)) indices.Add(i);
        }

        return indices;
    }

    internal static MetamorphicPrecondition Validate(MetamorphicParameters parameters)
    {
        var consumer = ConsumerOf(parameters);
        var arity = MetamorphicTables.CallbackArityOf(consumer);
        if (arity is < 1 or > 2)
            return MetamorphicPrecondition.Rejected("unsupported-callback-consumer");

        var callback = CallbackOf(parameters);
        if (!callback.IsCallbackOfArity(arity))
            return MetamorphicPrecondition.Rejected("callback-builtin-arity-does-not-match-consumer");

        return ProjectionOf(parameters) switch
        {
            // A variadic parameter COLLECTS the supplied slots into a list, so the wrapper receives
            // [element] where the direct builtin receives element. Never equivalent.
            MetamorphicWrapperProjection.Variadic =>
                MetamorphicPrecondition.Rejected("variadic-projection-collects-a-list-not-the-supplied-value"),

            // A flat multi-parameter callee opens a lone sequence element into rows and
            // arity-errors otherwise, so it is a different callback contract.
            MetamorphicWrapperProjection.ArityMismatched =>
                MetamorphicPrecondition.Rejected("wrapper-arity-does-not-match-callback-projection"),

            _ => MetamorphicPrecondition.Ok,
        };
    }

    internal static string DescribeVariant(MetamorphicParameters parameters)
        => $"consumer={ConsumerOf(parameters)} callback={CallbackOf(parameters).Name} " +
           $"callbackArity={MetamorphicTables.CallbackArityOf(ConsumerOf(parameters)).ToString(CultureInfo.InvariantCulture)} " +
           $"input={InputOf(parameters).Id} projection={ProjectionOf(parameters)}";

    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        var consumer = ConsumerOf(parameters);
        var arity = MetamorphicTables.CallbackArityOf(consumer);
        var callback = CallbackOf(parameters);
        var input = InputOf(parameters);
        var projection = ProjectionOf(parameters);
        var trailing = MetamorphicTables.ConsumerTrailingArgument(consumer);

        var rowsLine = $"{Rows} = {input.Source}\n";
        var left = $"{rowsLine}Output = {Rows}.{consumer}({callback.Name}{trailing})";
        var right = $"{WrapperDefinition(callback, arity, projection)}{rowsLine}Output = {Rows}.{consumer}({Wrap}{trailing})";

        return MetamorphicCaseFactory.Create(
            parameters,
            left,
            right,
            Validate(parameters),
            $"{consumer} with the direct builtin callback '{callback.Name}' against a {projection} wrapper, " +
            $"input {input.Id} = {input.Source}");
    }

    /// <summary>Builds the wrapper definition for one projection. Rejected projections are still
    /// generated so their rejection is exercised, but they are never compared.</summary>
    private static string WrapperDefinition(MetamorphicBuiltin callback, int arity, MetamorphicWrapperProjection projection)
    {
        var text = new StringBuilder();
        switch (projection)
        {
            case MetamorphicWrapperProjection.OrdinaryFixed:
                text.Append(Wrap).Append('(').Append(Parameters(arity)).Append(") = ")
                    .Append(callback.Name).Append('(').Append(Arguments(arity)).Append(')');
                break;

            case MetamorphicWrapperProjection.DottedFixed:
                text.Append(Wrap).Append('(').Append(Parameters(arity)).Append(") = a.").Append(callback.Name);
                if (arity > 1) text.Append('(').Append(Arguments(arity, skipFirst: true)).Append(')');
                break;

            case MetamorphicWrapperProjection.Variadic:
                text.Append(Wrap).Append("(...xs) = ").Append(callback.Name).Append("(xs)");
                break;

            default:   // ArityMismatched: deliberately the wrong arity for this consumer.
                var wrong = arity == 1 ? 2 : 1;
                text.Append(Wrap).Append('(').Append(Parameters(wrong)).Append(") = ")
                    .Append(callback.Name).Append("(a)");
                break;
        }

        return text.Append('\n').ToString();
    }

    private static string Parameters(int arity) => arity == 1 ? "a" : "a, b";

    private static string Arguments(int arity, bool skipFirst = false)
        => arity == 1 ? (skipFirst ? "" : "a") : (skipFirst ? "b" : "a, b");
}
