namespace KatLang.Evaluation;

// The row loop carries one reference to its source across awaits. The ordinary value-type
// specialization can discard the recording branch entirely, including the read of the slot count.
internal interface IOutputRowSource
{
    IReadOnlyList<Expr> Rows { get; }
    void RecordRow(int row, int slotEnd);
}

internal readonly struct OrdinaryOutputRows(IReadOnlyList<Expr> rows) : IOutputRowSource
{
    public IReadOnlyList<Expr> Rows { get; } = rows;
    public void RecordRow(int row, int slotEnd) { }
}

/// <summary>Records the physical slot deltas of the engine's root body in its shared row loop.</summary>
internal sealed class RootOutputRowRecorder(IReadOnlyList<Expr> rows) : IOutputRowSource
{
    public IReadOnlyList<Expr> Rows { get; } = rows;
    private int[]? _counts;
    private int _recordedRows;
    private int _lastSlotEnd;

    // The budget offers the recorder only until the root enters its row loop. The claiming
    // invocation carries it as its row source. Even a nested call with identical rows sees null.
    internal static RootOutputRowRecorder? Claim(EvaluationBudget budget, IReadOnlyList<Expr> candidate)
    {
        var recorder = budget.RootOutputRows;
        if (recorder is null || !ReferenceEquals(recorder.Rows, candidate) || candidate.Count == 0)
            return null;

        budget.RootOutputRows = null;
        recorder._counts = new int[candidate.Count];
        return recorder;
    }

    public void RecordRow(int row, int slotEnd)
    {
        _counts![row] = slotEnd - _lastSlotEnd;
        _lastSlotEnd = slotEnd;
        _recordedRows = row + 1;
    }

    // The engine takes the array only after successful root evaluation.
    internal int[]? TakeSlotCounts()
    {
        var counts = _counts;
        _counts = null;
        return counts is not null && _recordedRows == counts.Length ? counts : null;
    }
}
