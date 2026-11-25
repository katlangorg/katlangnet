namespace KatLang.Tests.Formatting;

/// <summary>
/// Hand-built <see cref="RunResult.Success"/> fixtures for formatter and display tests.
/// <para>A success carries the partition of its output rows over the rows of its root
/// (<see cref="RunResult.Success.OutputRowCounts"/>), and its constructor refuses a partition that
/// does not describe them. A fixture therefore needs a root whose rows can have produced the value
/// it displays: a root with no output row cannot own a visible value. The roots here are host-built
/// and never evaluated; only their row count and row kind matter.</para>
/// </summary>
internal static class HandBuiltSuccess
{
    // The source of a synthetic row can supply the fixture's chosen value. A fresh call
    // also allows two occurrences of the same spread node to supply different slices.
    internal static Expr FixtureCall() => new Expr.Call(new Expr.Resolve("nextFixtureValue"), OutputBundle.Empty);

    /// <summary>A root of one plain (non-spread) output row.</summary>
    private static Algorithm.User OnePlainRowRoot()
        => new(null, [], [], [], [FixtureCall()]);

    /// <summary>A root of one spread output row.</summary>
    private static Algorithm.User OneSpreadRowRoot()
        => new(null, [], [], [], [new Expr.SequenceSpread(FixtureCall())]);

    /// <summary>
    /// The success of a root whose one plain row produced <paramref name="value"/>: the value is
    /// the one output row, whatever it is.
    /// </summary>
    internal static RunResult.Success OfOnePlainRow(Result value)
        => new(OnePlainRowRoot(), value, [], EmittedCount: 1, OutputRowCounts: [1]);

    /// <summary>
    /// The success a value alone determines: a root whose one spread row supplied
    /// <paramref name="value"/> at its own value count, so the empty sequence value presents no
    /// output row and every other value presents one.
    /// </summary>
    internal static RunResult.Success OfValue(Result value)
        => OfOneSpreadRow(value, value.ValueCount());

    /// <summary>
    /// The success of a root whose one spread row supplied every output row
    /// <paramref name="value"/> presents for <paramref name="emittedCount"/>: none for zero, the
    /// value for one, and its top-level items for more.
    /// </summary>
    internal static RunResult.Success OfOneSpreadRow(Result value, int emittedCount)
        => new(OneSpreadRowRoot(), value, [], emittedCount, [RunResult.RowCountOf(value, emittedCount)]);
}
