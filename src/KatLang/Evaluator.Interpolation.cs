using System.Text;
using KatLang.Evaluation;
using KatLang.Rendering;

namespace KatLang;

/// <summary>
/// Interpolated-string evaluation support (VAL-12): the text builder the two expression-spine
/// machines share (<see cref="EvalExpressionSpineCounted"/> and its async twin evaluate an
/// <see cref="Expr.InterpolatedString"/> as a spine node, so nested interpolation consumes no
/// proportional CLR stack). Part of the <see cref="Evaluator"/> partial class.
/// </summary>
public static partial class Evaluator
{
    /// <summary>
    /// The text of one interpolated-string evaluation: a display sink bounded by the run's LIVE
    /// string capacity, re-read before every append because the holes evaluated in between may
    /// themselves create strings. A hole value is appended as its structural value text
    /// (<see cref="ValueTextRenderer.AppendCanonicalValue"/>).
    /// <para><b>Limits (C#-only).</b> Each piece of text is checked, without committing, against
    /// the run's live string capacity before it is appended
    /// (<see cref="EvaluationBudget.StringConstructionCapacity"/>), so no oversized intermediate
    /// text is ever built and no later hole is evaluated once the text has crossed a limit; the
    /// finished text is then reserved once, exactly its length (<see cref="Complete"/>). A refused
    /// append records the length the text would have reached, and the node then reports the limit
    /// through the one string reservation (<see cref="EvaluationBudget.TryReserveString"/>), so the
    /// error (<see cref="EvalError.StringSizeLimitExceeded"/> /
    /// <see cref="EvalError.StringMaterializationLimitExceeded"/>, whose requested length is the
    /// length the text had reached when it crossed), its retention as the run's terminal failure,
    /// and the budget accounting are exactly those of every other string. The check is monotone,
    /// so it only ever stops a string that the final reservation would have refused.</para>
    /// </summary>
    private sealed class InterpolatedTextBuilder(EvaluationBudget budget) : IDisplaySink
    {
        private readonly StringBuilder _text = new();
        private long _crossedAt = -1;

        public bool Append(string text)
            => Admit(text.Length) && Write(text);

        public bool Append(char c, int count)
        {
            if (!Admit(count))
                return false;
            _text.Append(c, count);
            return true;
        }

        /// <summary>Appends the structural text of one hole value (VAL-12).</summary>
        public bool AppendValue(Result value) => ValueTextRenderer.AppendCanonicalValue(value, this);

        /// <summary>
        /// The limit error for the append that crossed the capacity: the failed reservation of the
        /// length the text would have reached, positioned at the interpolated string.
        /// </summary>
        public EvalError LimitError(SourceSpan? span)
        {
            if (_crossedAt < 0)
                throw new InvalidOperationException("An interpolated string reported a limit that no append crossed.");
            if (budget.TryReserveString(_crossedAt) is not { } limitError)
                throw new InvalidOperationException("A string longer than the run's string capacity was reserved.");
            return AtSpanIfMissing(limitError, span);
        }

        /// <summary>Reserves the finished text once and builds the one string value (emitted count 1).</summary>
        public EvalResult<CountedResult> Complete(SourceSpan? span)
            => budget.TryReserveString(_text.Length) is { } limitError
                ? AtSpanIfMissing(limitError, span)
                : EvalResult<CountedResult>.Ok(new CountedResult(new Result.Str(_text.ToString()), 1));

        private bool Admit(long length)
        {
            if (length <= budget.StringConstructionCapacity - _text.Length)
                return true;
            _crossedAt = _text.Length + length;
            return false;
        }

        private bool Write(string text)
        {
            _text.Append(text);
            return true;
        }
    }
}
