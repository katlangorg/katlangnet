namespace KatLang.TestInfrastructure;

/// <summary>A shared read counter for <see cref="BudgetedPatternItems{T}"/> lists.</summary>
internal sealed class PatternReadBudget(int limit = 2000)
{
    public int Limit { get; } = limit;

    public int Reads;
}

/// <summary>
/// A two-item pattern list that counts every item read against a shared budget and throws once the
/// budget is exceeded: the probe that turns a walk expanding a shared host-built pattern DAG per
/// path (exponential in its depth) into a test failure instead of a hang.
/// </summary>
internal sealed class BudgetedPatternItems<T>(T first, T second, PatternReadBudget budget) : IReadOnlyList<T>
{
    public int Count => 2;

    public T this[int index]
    {
        get
        {
            if (++budget.Reads > budget.Limit)
                throw new InvalidOperationException("A pattern walk expanded shared pattern paths.");
            return index switch
            {
                0 => first,
                1 => second,
                _ => throw new ArgumentOutOfRangeException(nameof(index)),
            };
        }
    }

    public IEnumerator<T> GetEnumerator()
    {
        yield return this[0];
        yield return this[1];
    }

    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
}
