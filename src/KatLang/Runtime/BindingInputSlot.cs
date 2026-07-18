namespace KatLang.Runtime;

// Data-only runtime input slot used to prepare future binding input unification.
// It does not bind, evaluate, or apply policy.
internal readonly record struct BindingInputSlot(
    Result? Value,
    Algorithm? Algorithm,
    EvalError? ValueError)
{
    public static BindingInputSlot FromUserCallItem(
        Result? value,
        Algorithm? algorithm,
        EvalError? valueError)
        => new(value, algorithm, valueError);

    public static BindingInputSlot FromEvaluatedValue(Result value)
        => new(value, Algorithm: null, ValueError: null);
}
