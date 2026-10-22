using System.Globalization;
using System.Numerics;
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
    /// atoms, Booleans, strings, sequences, exact lists, the empty sequence, the empty list, nesting,
    /// and order all stay distinguishable: <c>1</c>, <c>'x'</c>, <c>S[a, b]</c>, <c>S[]</c>,
    /// <c>L[a, b]</c>, <c>L[]</c>. This is the same encoding the repository's semantic
    /// explorer uses (<c>SemanticExplorerHarness.Neutral</c>), pinned by a mirror test.
    ///
    /// <para>Written with an explicit stack so an arbitrarily deep value cannot overflow the
    /// host stack inside the harness.</para>
    /// </summary>
    internal static string Neutral(Result result)
        => NeutralWithin(result, int.MaxValue)
            ?? throw new InvalidOperationException("The neutral text exceeded the maximum string length.");

    /// <summary>
    /// UTF-16 units of legacy neutral text an OBSERVATION will build (SEM-2A). The neutral text
    /// spells every root-to-leaf PATH, so a legally built shared value (<c>W = [x, x]</c> applied
    /// n times) has a 2^n-unit text; past this bound the observation records no legacy text
    /// (<see cref="MetamorphicSemanticObservation.Structure"/> is <c>null</c>) rather than a
    /// truncated one. Comparison never depends on it: the typed value and its linear
    /// <c>kl-struct-v1</c> identity are always recorded.
    /// </summary>
    internal const int MaxObservedNeutralLength = 4_000_000;

    /// <summary>
    /// <see cref="Neutral"/>, or <c>null</c> as soon as the text would exceed
    /// <paramref name="maxLength"/> units — never a truncated prefix.
    /// </summary>
    internal static string? NeutralWithin(Result result, int maxLength)
    {
        ArgumentNullException.ThrowIfNull(result);
        ArgumentOutOfRangeException.ThrowIfNegative(maxLength);
        var text = new StringBuilder(64);
        // One continuation per open level, never one entry per pending sibling. A small text
        // limit must also bound work on a wide value and refuse a large string BEFORE copying it.
        var pending = new Stack<(IReadOnlyList<Result> Items, int Next)>();
        Result? current = result;

        while (true)
        {
            switch (current)
            {
                case Result.Atom atom:
                    if (!AppendWithin(atom.Value.ToString(CultureInfo.InvariantCulture))) return null;
                    break;
                case Result.Str str:
                    if (maxLength - text.Length < 2 || str.Value.Length > maxLength - text.Length - 2) return null;
                    text.Append('\'').Append(str.Value).Append('\'');
                    break;
                case Result.Bool flag:
                    if (!AppendWithin(flag.Value ? "true" : "false")) return null;
                    break;
                case Result.SequenceValue sequence:
                    if (!AppendWithin("S[")) return null;
                    pending.Push((sequence.Items, 0));
                    break;
                case Result.ListValue list:
                    if (!AppendWithin("L[")) return null;
                    pending.Push((list.Items, 0));
                    break;
                case null:
                    break;
                default:
                    throw new InvalidOperationException($"Unhandled result variant {current.GetType().Name}.");
            }

            if (pending.Count == 0) return text.ToString();
            var (items, next) = pending.Pop();
            if (next == items.Count)
            {
                if (!AppendWithin("]")) return null;
                current = null;
            }
            else
            {
                if (next > 0 && !AppendWithin(", ")) return null;
                pending.Push((items, next + 1));
                current = items[next];
            }
        }

        bool AppendWithin(string fragment)
        {
            if (fragment.Length > maxLength - text.Length) return false;
            text.Append(fragment);
            return true;
        }
    }

    /// <summary>
    /// Stable text for a HOST-ATOM projection (<c>RunFlat</c>, <c>RunResult.Success.Atoms</c>,
    /// <c>EvaluateToAtoms</c>): the flattened decimal list, culture-invariant, so two surfaces
    /// can be compared on it and it fingerprints identically on every machine. Deliberately
    /// distinct from <see cref="Neutral"/>: this projection has already opened every sequence
    /// and list boundary, so it cannot represent structure and must never be mistaken for it.
    /// </summary>
    internal static string HostAtoms(IReadOnlyList<Decimal128> atoms)
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
