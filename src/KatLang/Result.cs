namespace KatLang;

/// <summary>
/// Structured evaluation result.
/// Corresponds to <c>Result</c> in the Lean specification.
/// </summary>
public abstract record Result
{
    private Result() { }

    /// <summary>
    /// KatLang value-semantic comparer for <see cref="Result"/>.
    /// Atoms compare by numeric value, strings by exact string value, and
    /// groups structurally by ordered child results.
    /// </summary>
    public static IEqualityComparer<Result> ValueComparer { get; } = new ValueSemanticComparer();

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
    /// Count emitted top-level values when this result is already in hand.
    /// Empty results emit 0. Any non-empty atomic, string, or grouped value
    /// counts as one value.
    ///
    /// Lean: <c>Result.valueCount</c>. Used by <c>reduce</c> and <c>map</c>
    /// so grouped accumulator / mapped values count as one value.
    /// </summary>
    public int ValueCount()
    {
        return this switch
        {
            Group(var items) when items.Count == 0 => 0,
            _ => 1,
        };
    }

    /// <summary>
    /// KatLang truth testing used by builtins like <c>if</c>.
    /// Zero is false, any other numeric atom is true.
    /// Returns null when there is no numeric atom to truth-test.
    /// This follows the generic flattened-atoms convention; stricter builtins
    /// such as <c>filter</c> should use <c>SingleAtomicTruthValue()</c>.
    /// Lean: <c>Result.truthValue?</c>.
    /// </summary>
    public bool? TruthValue()
    {
        var atoms = ToAtoms();
        if (atoms.Count == 0)
            return null;
        return atoms[0] != 0;
    }

    /// <summary>
    /// Strict truth testing for <c>filter</c> predicates.
    /// Accepts exactly one atomic numeric value: <c>0</c> is false and any
    /// other atomic number is true. Groups, multi-output values, strings, and
    /// empty results are rejected.
    /// Lean: <c>Result.singleAtomicTruthValue?</c>.
    /// </summary>
    public bool? SingleAtomicTruthValue()
    {
        return this switch
        {
            Atom(var n) => n != 0,
            _ => null,
        };
    }

    /// <summary>
    /// Strict numeric extraction for numeric collection builtins such as
    /// <c>min</c>, <c>max</c>, <c>sum</c>, and <c>avg</c>.
    /// Accepts exactly one atomic numeric value and rejects groups and strings.
    /// Lean: <c>Result.singleAtomicNumber?</c>.
    /// </summary>
    public decimal? SingleAtomicNumber()
    {
        return this switch
        {
            Atom(var n) => n,
            _ => null,
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
    /// Extract top-level items from a result.
    /// Atom/string → singleton list; group → its items.
    /// Lean: <c>Result.toItems</c>.
    /// </summary>
    public IReadOnlyList<Result> ToItems()
    {
        return this switch
        {
            Atom or Str => [this],
            Group(var items) => items,
            _ => [],
        };
    }

    /// <summary>
    /// Construction preserves structure; selection projects content.
    /// Project one selected value to the top-level content it denotes at the
    /// current boundary, without recursively flattening nested grouped members.
    /// Lean: <c>Result.projectSelectedContent</c>.
    /// </summary>
    private static (Result Value, int EmittedCount) ProjectSelectedContent(Result selected)
    {
        var items = selected.ToItems();
        return (FromItems(items), items.Count);
    }

    /// <summary>
    /// Construction preserves structure; selection projects content.
    /// <c>:</c> selects one top-level item from the target and projects that
    /// item's content one level: atoms stay atomic, grouped items yield their
    /// immediate members, and nested grouped members remain grouped.
    /// Lean: <c>Result.select?</c>.
    /// </summary>
    public (Result Value, int EmittedCount)? SelectProjected(int i)
    {
        var sourceItems = ToItems();
        return i >= 0 && i < sourceItems.Count
            ? ProjectSelectedContent(sourceItems[i])
            : null;
    }

    /// <summary>
    /// Construction preserves structure; selection projects content.
    /// Higher-order sequence iteration uses the same one-level projection rule
    /// for each iterated item as <c>:</c> uses for a selected item.
    /// Lean: callback item projection via <c>Result.projectSelectedContent</c>.
    /// </summary>
    public (Result Value, int EmittedCount) ProjectIteratedContent()
        => ProjectSelectedContent(this);

    /// <summary>
    /// One-level projected selection result for <c>:</c>.
    /// Lean: <c>Result.index?</c>.
    /// </summary>
    public Result? Index(int i)
    {
        return SelectProjected(i)?.Value;
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

    private sealed class ValueSemanticComparer : IEqualityComparer<Result>
    {
        public bool Equals(Result? x, Result? y)
        {
            if (ReferenceEquals(x, y)) return true;
            if (x is null || y is null) return false;

            return (x, y) switch
            {
                (Atom(var left), Atom(var right)) => left == right,
                (Str(var left), Str(var right)) => StringComparer.Ordinal.Equals(left, right),
                (Group(var leftItems), Group(var rightItems)) =>
                    leftItems.Count == rightItems.Count && ItemsEqual(leftItems, rightItems),
                _ => false,
            };
        }

        public int GetHashCode(Result obj)
        {
            var hash = new HashCode();
            AddHashCode(ref hash, obj);
            return hash.ToHashCode();
        }

        private bool ItemsEqual(IReadOnlyList<Result> left, IReadOnlyList<Result> right)
        {
            for (var index = 0; index < left.Count; index++)
            {
                if (!Equals(left[index], right[index]))
                    return false;
            }

            return true;
        }

        private static void AddHashCode(ref HashCode hash, Result result)
        {
            switch (result)
            {
                case Atom(var value):
                    hash.Add(0);
                    hash.Add(value);
                    break;

                case Str(var value):
                    hash.Add(1);
                    hash.Add(value, StringComparer.Ordinal);
                    break;

                case Group(var items):
                    hash.Add(2);
                    hash.Add(items.Count);
                    foreach (var item in items)
                        AddHashCode(ref hash, item);
                    break;
            }
        }
    }
}
