using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Public root-output model: <see cref="RunResult.Success.OutputRows"/> keeps
/// separately produced root outputs distinguishable from one sequence value
/// containing the same items — a distinction <see cref="RunResult.Success.Value"/>
/// alone cannot represent — and matches the canonical display derivation
/// exactly.
/// </summary>
public class OutputRowsTests
{
    private static RunResult.Success Success(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

    [Fact]
    public void TwoRootOutputs_AndOneSequenceValue_HaveEqualValuesButDifferentRows()
    {
        var twoRows = Success("A = 1\nB = 2\nA()\nB()");
        var oneSequence = Success("(A() B())\nA = 1\nB = 2");

        // The structural values are KatLang-equal…
        Assert.True(Result.ValueComparer.Equals(twoRows.Value, oneSequence.Value));

        // …but the root-output boundary differs, and OutputRows preserves it.
        Assert.Equal(2, twoRows.OutputRows.Count);
        var sequenceRow = Assert.IsType<Result.SequenceValue>(Assert.Single(oneSequence.OutputRows));
        Assert.Equal(2, sequenceRow.Items.Count);

        // Canonical display reflects the same distinction.
        Assert.Equal($"1{Environment.NewLine}2", twoRows.ToDisplayString());
        Assert.Equal("(1, 2)", oneSequence.ToDisplayString());
    }

    [Fact]
    public void SpreadContributingZeroItems_HasZeroRows()
    {
        var success = Success("E = ()\nE*");

        Assert.Empty(success.OutputRows);
        Assert.Equal(string.Empty, success.ToDisplayString());
    }

    [Fact]
    public void OneAtomRow()
    {
        var success = Success("7");
        var row = Assert.Single(success.OutputRows);
        Assert.Equal(new Result.Atom(7), row);
    }

    [Fact]
    public void OneSequenceRow_StaysOneRow()
    {
        var success = Success("(1, 2, 3)");
        var row = Assert.Single(success.OutputRows);
        Assert.Equal(3, Assert.IsType<Result.SequenceValue>(row).Items.Count);
    }

    [Fact]
    public void SeveralRootRows_AreListedInEmissionOrder()
    {
        var success = Success("1, (2, 3), 4");

        Assert.Equal(3, success.OutputRows.Count);
        Assert.Equal(new Result.Atom(1), success.OutputRows[0]);
        Assert.IsType<Result.SequenceValue>(success.OutputRows[1]);
        Assert.Equal(new Result.Atom(4), success.OutputRows[2]);
    }

    [Fact]
    public void SpreadAndRepeatedSpread_ExposeTheActuallySuppliedRows()
    {
        foreach (var source in new[]
        {
            "S = ((1, 2), (3, 4))\nS*",
            "S = ((1, 2), (3, 4))\nS**",
        })
        {
            var success = Success(source);
            Assert.Equal(2, success.OutputRows.Count);
            Assert.Equal(2, Assert.IsType<Result.SequenceValue>(success.OutputRows[0]).Items.Count);
            Assert.Equal(2, Assert.IsType<Result.SequenceValue>(success.OutputRows[1]).Items.Count);
            Assert.Equal($"(1, 2){Environment.NewLine}(3, 4)", success.ToDisplayString());
        }
    }

    [Fact]
    public void PropertyAndCollectionResults_RemainSingleValueRows()
    {
        var property = Success("P = (1, 2)\nP");
        Assert.Single(property.OutputRows);
        Assert.IsType<Result.SequenceValue>(property.OutputRows[0]);

        var collection = Success("range(1, 3)");
        Assert.Single(collection.OutputRows);
        Assert.IsType<Result.ListValue>(collection.OutputRows[0]);
    }

    [Fact]
    public void ExplicitEmptyString_IsOneVisibleRow()
    {
        var success = Success("''");
        var row = Assert.Single(success.OutputRows);
        Assert.Equal(new Result.Str(string.Empty), row);
    }

    [Fact]
    public void EmptySequence_IsOneVisibleRow()
    {
        var success = Success("()");
        var row = Assert.Single(success.OutputRows);
        Assert.Empty(Assert.IsType<Result.SequenceValue>(row).Items);
    }

    [Fact]
    public void EmptyList_IsOneVisibleRow()
    {
        var success = Success("[]");
        var row = Assert.Single(success.OutputRows);
        Assert.Empty(Assert.IsType<Result.ListValue>(row).Items);
    }

    [Fact]
    public void NoProgramOutput_IsADistinctVariantWithoutRows()
    {
        // "No output" is not an empty row list on Success — it is its own
        // RunResult variant.
        Assert.IsType<RunResult.NoProgramOutput>(KatLangEngine.Run("T = 4"));
    }

    [Fact]
    public void ManuallyConstructedSuccess_DerivesOneRowFromTheValue()
    {
        var success = new RunResult.Success(
            new Algorithm.User(null, [], [], [], []),
            new Result.Atom(5),
            []);

        var row = Assert.Single(success.OutputRows);
        Assert.Equal(new Result.Atom(5), row);
    }

    [Fact]
    public void OutputRows_AreReadOnly()
    {
        foreach (var source in new[] { "7", "1, 2, 3", "(1, 2)" })
        {
            var rows = Success(source).OutputRows;
            if (rows is IList<Result> list)
            {
                Assert.True(list.IsReadOnly);
                if (list.Count > 0)
                    Assert.ThrowsAny<NotSupportedException>(() => list[0] = new Result.Atom(0));
            }
        }
    }

    [Fact]
    public void OutputRows_MatchCanonicalDisplayDerivation()
    {
        foreach (var source in new[]
        {
            "7", "1, 2, 3", "(1, 2)", "1, (2, 3)", "[1, 2]", "''", "()", "[]",
            "E = ()\nE*", "S = ((1, 2), (3, 4))\nS:0",
        })
        {
            var success = Success(source);
            var writer = new BoundedDisplayWriter(EvaluationLimits.MaxSupportedDisplayLength);
            for (var i = 0; i < success.OutputRows.Count; i++)
            {
                if (i > 0) writer.AppendRowSeparator();
                RunResult.AppendValue(success.OutputRows[i], DisplayOptions.Default, writer);
            }

            Assert.Equal(success.ToDisplayString(), writer.ToString());
        }
    }

    [Fact]
    public void MultiItemProjectionAlongsideAnotherExpression_PreservesDisplayRows()
    {
        var success = Success("S = ((1, 2), (3, 4))\nS:0\n5");

        // EmittedCount is a literal arity count (three here), but canonical
        // display uses it only to select the multi-row view. The combined value
        // retains the projected sequence as one top-level display row.
        Assert.Equal(3, success.EmittedCount);
        Assert.Equal(2, success.OutputRows.Count);
        Assert.Equal("(1, 2)", OutputFormatters.Exact.Format(new RunResult.Success(
            success.Root,
            success.OutputRows[0],
            [])));
        Assert.Equal(new Result.Atom(5), success.OutputRows[1]);
        Assert.Equal($"(1, 2){Environment.NewLine}5", success.ToDisplayString());
    }

    [Fact]
    public void LoneMultiItemProjection_UsesItsEmittedArityAsSeparateRows()
    {
        var success = Success("S = ((1, 2), (3, 4))\nS:0");

        Assert.Equal(2, success.EmittedCount);
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], success.OutputRows);
        Assert.Equal($"1{Environment.NewLine}2", success.ToDisplayString());
    }
}
