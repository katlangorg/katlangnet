using System.Globalization;
using System.Text;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Neutral, stable encodings of an evaluation outcome. Everything here is a pure READ of an
/// immutable evaluator value: nothing re-evaluates, nothing allocates a <see cref="Result"/>,
/// and nothing touches the run's budget.
/// </summary>
internal static class MetamorphicValue
{
    /// <summary>
    /// Neutral structural encoding, deliberately distinct from display syntax so that
    /// atoms, strings, sequences, exact lists, the empty sequence, the empty list, nesting,
    /// and order all stay distinguishable: <c>1</c>, <c>'x'</c>, <c>S[a, b]</c>, <c>S[]</c>,
    /// <c>L[a, b]</c>, <c>L[]</c>. This is the same encoding the repository's semantic
    /// explorer uses (<c>SemanticExplorerHarness.Neutral</c>), pinned by a mirror test.
    ///
    /// <para>Written with an explicit stack so an arbitrarily deep value cannot overflow the
    /// host stack inside the harness.</para>
    /// </summary>
    internal static string Neutral(Result result)
    {
        var text = new StringBuilder(64);
        var pending = new Stack<object>();
        pending.Push(result);

        while (pending.Count > 0)
        {
            var next = pending.Pop();
            if (next is string literal)
            {
                text.Append(literal);
                continue;
            }

            switch ((Result)next)
            {
                case Result.Atom atom:
                    text.Append(atom.Value.ToString(CultureInfo.InvariantCulture));
                    break;
                case Result.Str str:
                    text.Append('\'').Append(str.Value).Append('\'');
                    break;
                case Result.SequenceValue sequence:
                    PushStructure("S[", sequence.Items);
                    break;
                case Result.ListValue list:
                    PushStructure("L[", list.Items);
                    break;
                default:
                    text.Append('?');
                    break;
            }
        }

        return text.ToString();

        void PushStructure(string opening, IReadOnlyList<Result> items)
        {
            text.Append(opening);
            pending.Push("]");
            for (var i = items.Count - 1; i >= 0; i--)
            {
                pending.Push(items[i]);
                if (i > 0) pending.Push(", ");
            }
        }
    }

    /// <summary>
    /// Stable text for a HOST-ATOM projection (<c>RunFlat</c>, <c>RunResult.Success.Atoms</c>,
    /// <c>EvaluateToAtoms</c>): the flattened decimal list, culture-invariant, so two surfaces
    /// can be compared on it and it fingerprints identically on every machine. Deliberately
    /// distinct from <see cref="Neutral"/>: this projection has already opened every sequence
    /// and list boundary, so it cannot represent structure and must never be mistaken for it.
    /// </summary>
    internal static string HostAtoms(IReadOnlyList<decimal> atoms)
    {
        var text = new StringBuilder(2 + (atoms.Count * 3));
        text.Append('A').Append('[');
        for (var i = 0; i < atoms.Count; i++)
        {
            if (i > 0) text.Append(", ");
            text.Append(atoms[i].ToString(CultureInfo.InvariantCulture));
        }

        return text.Append(']').ToString();
    }

    /// <summary>Unwraps the contextual chain down to the structured error that actually occurred.</summary>
    internal static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext withContext) error = withContext.Inner;
        return error;
    }

    /// <summary>
    /// Stable error identity: the innermost structured error's CLR type name.
    ///
    /// <para>Deliberately NOT the Lean-facing category used by the semantic explorer, which
    /// intentionally collapses several distinct kinds (every arity error maps to
    /// <c>"arity"</c>) so the differential corpus can compare against a model that does not
    /// distinguish them. A metamorphic comparison is between two C# runs, so it wants
    /// MAXIMUM discrimination. It is also not the error message: prose and source context
    /// may legitimately differ between the dotted and ordinary spellings of one call.</para>
    /// </summary>
    internal static string ErrorCategory(EvalError error) => Innermost(error).GetType().Name;

    /// <summary>
    /// The stable, machine-independent part of an error's structured payload, or <c>null</c>
    /// when the error kind has none worth comparing across two spellings of a program.
    ///
    /// <para>Resource-limit errors carry item/unit counts and configured limits, which are
    /// machine-independent by construction and must agree between equivalent forms. Ordinary
    /// semantic errors are compared by kind only: their payloads can embed names and
    /// positions that legitimately differ between the two written forms.</para>
    /// </summary>
    internal static string? ErrorPayload(EvalError error) => Innermost(error) switch
    {
        EvalError.EvaluationDepthExceeded depth => Limit(depth.Limit),
        EvalError.EvaluationStepLimitExceeded steps => Limit(steps.Limit),
        EvalError.CollectionSizeLimitExceeded collection => Limit(collection.Limit, collection.Requested),
        EvalError.MaterializationLimitExceeded materialization => Limit(materialization.Limit),
        EvalError.StringSizeLimitExceeded stringSize => Limit(stringSize.Limit, stringSize.Requested),
        EvalError.StringMaterializationLimitExceeded stringTotal => Limit(stringTotal.Limit),
        EvalError.DisplayLengthLimitExceeded display => Limit(display.Limit),
        EvalError.EvaluationStackExhausted => "hostStackBackstop",
        _ => null,
    };

    private static string Limit(long limit) => "limit=" + limit.ToString(CultureInfo.InvariantCulture);

    private static string Limit(long limit, long requested)
        => Limit(limit) + ",requested=" + requested.ToString(CultureInfo.InvariantCulture);
}
