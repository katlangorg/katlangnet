namespace KatLang.Evaluation;

/// <summary>
/// Carries a budget refusal (<see cref="EvaluationBudget.TryChargeStructuralWork"/>) out of a
/// structural walk of an operation comparer (<see cref="Result.CreateOperationComparer"/>, SEC-02).
/// The walks run behind <see cref="IEqualityComparer{T}"/>, whose bool and int results have no
/// room for an <see cref="EvalError"/>, so the refusal unwinds to the evaluator operation that
/// owns the comparer, which catches exactly this type and returns <see cref="Error"/> as its
/// outcome. The error is already retained as the run's terminal failure, so nothing is lost if an
/// intermediate frame (a <see cref="HashSet{T}"/>) is abandoned on the way.
///
/// <para>Internal and never visible to hosts: it cannot escape an operation, because every
/// operation comparer is created and consumed inside one builtin evaluation that catches it.
/// Host cancellation is NOT carried this way — it stays the
/// <see cref="OperationCanceledException"/> the budget throws.</para>
/// </summary>
internal sealed class StructuralWorkRefusedException(EvalError error)
    : Exception("Structural value-traversal work was refused by the evaluation budget.")
{
    internal EvalError Error { get; } = error;
}
