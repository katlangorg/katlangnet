namespace KatLang;

/// <summary>
/// Structured evaluation result.
/// Corresponds to <c>Result</c> in the Lean specification.
/// </summary>
public abstract record Result
{
    private Result() { }

    /// <summary>A single numeric value.</summary>
    public sealed record Atom(decimal Value) : Result;

    /// <summary>A first-class string value. Lean: Result.str.</summary>
    public sealed record Str(string Value) : Result;

    /// <summary>A group of results (preserves algorithm boundaries).</summary>
    public sealed record Group(IReadOnlyList<Result> Items) : Result;

    /// <summary>
    /// Normalize: unwrap single-element groups recursively.
    /// Lean: Result.normalize
    /// </summary>
    public Result Normalize()
    {
        return this switch
        {
            Atom _ => this,
            Str _ => this,
            Group(var items) =>
                items.Select(r => r.Normalize()).ToList() switch
                {
                    [var single] => single,
                    var normalized => new Group(normalized),
                },
            _ => this,
        };
    }

    /// <summary>
    /// Flatten result to a list of numbers.
    /// Lean: Result.atoms — strings are silently omitted from atom lists.
    /// </summary>
    public IReadOnlyList<decimal> ToAtoms()
    {
        return this switch
        {
            Atom(var n) => [n],
            Str _ => [],
            Group(var items) => items.SelectMany(r => r.ToAtoms()).ToList(),
            _ => [],
        };
    }

    /// <summary>
    /// Try to get as a single number.
    /// Returns null if the result is not a single atom (after normalization).
    /// Lean: Result.asInt?
    /// </summary>
    public decimal? AsNum()
    {
        return this switch
        {
            Atom(var n) => n,
            Str _ => null,
            Group(var items) => Normalize() switch
            {
                Atom(var n) => n,
                _ => null,
            },
            _ => null,
        };
    }

    /// <summary>
    /// Structural indexing (preserves grouping).
    /// Lean: Result.index?
    /// </summary>
    public Result? Index(int i)
    {
        return this switch
        {
            Atom(var n) when i == 0 => new Atom(n),
            Atom _ => null,
            Str _ when i == 0 => this,
            Str _ => null,
            Group(var items) when i >= 0 && i < items.Count => items[i],
            Group _ => null,
            _ => null,
        };
    }

    /// <summary>
    /// Try to get as integer (for indexing).
    /// </summary>
    public int? AsIndex()
    {
        var num = AsNum();
        if (num is null || num < 0 || num != Math.Floor(num.Value))
            return null;
        return (int)num.Value;
    }

    /// <summary>
    /// Create a group from items and normalize.
    /// </summary>
    public static Result FromItems(IEnumerable<Result> items)
    {
        var list = items.ToList();
        return new Group(list).Normalize();
    }
}
