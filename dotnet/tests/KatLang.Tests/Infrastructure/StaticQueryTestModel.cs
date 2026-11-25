namespace KatLang.Tests;

/// <summary>Equations shared with the external IR-04 oracle replay, not the independent expected-value algorithm.</summary>
internal sealed record StaticQueryTestGate(char Op, int A = 0, int B = 0, int Value = 0, int Ignored = -1);

internal sealed class StaticQueryTestModel(StaticQueryTestGate[] gates, bool reverseReads = false)
    : IStaticQueryDefinition<int, int>
{
    public int Runs { get; private set; }
    public int Initial(int key) => 0;
    public int PathCycleValue => -1;
    public bool ValueEquals(int left, int right) => left == right;
    public bool IsRefinement(int before, int after) => before == 0 || before == after;

    public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader)
    {
        Runs++;
        var gate = gates[key];
        if (!reverseReads && gate.Ignored >= 0) reader.Read(gate.Ignored);
        StaticQueryStep<int> result;
        switch (gate.Op)
        {
            case 'c': result = StaticQueryStep.Complete(gate.Value); break;
            case 'f': result = reader.Follow(gate.A); break;
            case 't':
                result = reader.Read(gate.A) switch
                {
                    1 => StaticQueryStep.Complete(1),
                    -1 => reader.Follow(gate.B),
                    _ => StaticQueryStep.Complete(reader.Read(gate.B) == 1 ? 1 : 0),
                };
                break;
            default:
                int a, b;
                if (reverseReads && gate.Op is '&' or '|')
                {
                    b = reader.Read(gate.B);
                    a = reader.Read(gate.A);
                }
                else
                {
                    a = reader.Read(gate.A);
                    b = gate.Op is '&' or '|' ? reader.Read(gate.B) : 0;
                }
                result = StaticQueryStep.Complete(gate.Op switch
                {
                    '=' => a,
                    '!' => -a,
                    '&' => a == -1 || b == -1 ? -1 : a == 1 && b == 1 ? 1 : 0,
                    '|' => a == 1 || b == 1 ? 1 : a == -1 && b == -1 ? -1 : 0,
                    _ => throw new InvalidOperationException($"Unknown test operator {gate.Op}"),
                });
                break;
        }
        if (reverseReads && gate.Ignored >= 0) reader.Read(gate.Ignored);
        return result;
    }
}
