using System.Globalization;
using System.Numerics;
using KatLang.Formatting;
using KatLang.Rendering;
using Stats = KatLang.Formatting.StructuredLayoutRenderer.LayoutWorkStatistics;

namespace KatLang.Tests.Formatting;

/// <summary>
/// The readable and concise layouts measure an item before they write it inline or open it, and a
/// measurement that does not fit keeps its walk (<see cref="ValueTextRenderer.ResumableMeasurement"/>):
/// when the structure is opened, the item that walk entered is measured by continuing it. Before,
/// every nesting level walked its subtree's leading text again, a full line width per level wherever
/// the remaining width does not shrink with depth. At zero indentation, 20,000 nested levels under
/// the widest supported line took 3 to 5.5 seconds on a development machine (2026-11-22) for at most
/// 360,000 code units of output; they now take about 50 milliseconds.
///
/// <para>This is implementation-only work. Output, line breaking, display limits and every string
/// classification charge must equal the FRESH-WALK route (<c>resumeMeasurements: false</c>, the
/// measurement before this change), at every indentation. Work is asserted through deterministic
/// counters (<see cref="Stats.MeasuredCodeUnits"/>), never elapsed time, and expected texts are
/// written out by hand.</para>
/// </summary>
public class LayoutMeasurementReuseTests
{
    private static Result Num(long value) => new Result.Atom(value);

    private static Result Num(string literal) => new Result.Atom(Decimal128.Parse(literal, CultureInfo.InvariantCulture));

    private static Result Str(string text) => new Result.Str(text);

    private static Result Seq(params Result[] items) => Result.SequenceValue.TakeOwnership(items);

    private static Result List(params Result[] items) => Result.ListValue.TakeOwnership(items);

    private sealed record Rendering(bool Completed, string Text, Stats Stats);

    private static Rendering Render(
        IReadOnlyList<Result> rows,
        OutputFormattingOptions options,
        bool concise,
        bool resume,
        long? budget = null)
    {
        var stats = new Stats();
        var writer = new BoundedDisplayWriter(options.EffectiveDisplayLimit(DisplayOptions.Default.MaxDisplayLength));
        var completed = StructuredLayoutRenderer.WriteRows(
            rows, DisplayOptions.Default, options, concise, writer, stats, budget, resume);
        Assert.Equal(!completed, writer.LimitExceeded);
        return new(completed, writer.ToString(), stats);
    }

    /// <summary>
    /// Renders on both routes and requires everything except the measurement work to agree: text,
    /// completion, and the string classification work that decides quoting and exhaustion.
    /// </summary>
    private static Rendering RenderBoth(
        IReadOnlyList<Result> rows,
        OutputFormattingOptions options,
        bool concise,
        long? budget = null,
        string label = "")
        => RenderBothRoutes(rows, options, concise, budget, label).Kept;

    private static (Rendering Kept, Rendering Fresh) RenderBothRoutes(
        IReadOnlyList<Result> rows,
        OutputFormattingOptions options,
        bool concise,
        long? budget = null,
        string label = "")
    {
        var kept = Render(rows, options, concise, resume: true, budget);
        var fresh = Render(rows, options, concise, resume: false, budget);
        Assert.True(fresh.Completed == kept.Completed, $"completion differs {label}");
        Assert.True(fresh.Text == kept.Text, $"text differs {label}");
        Assert.True(fresh.Stats.ChargedCodeUnits == kept.Stats.ChargedCodeUnits, $"charged code units differ {label}");
        Assert.True(fresh.Stats.LongClassifications == kept.Stats.LongClassifications, $"long classifications differ {label}");
        Assert.True(fresh.Stats.UncachedClassifications == kept.Stats.UncachedClassifications, $"uncached classifications differ {label}");
        Assert.True(fresh.Stats.UnclassifiedResults == kept.Stats.UnclassifiedResults, $"unclassified results differ {label}");
        Assert.True(fresh.Stats.ClassificationExhausted == kept.Stats.ClassificationExhausted, $"exhaustion differs {label}");
        Assert.True(fresh.Stats.RowRestarts == kept.Stats.RowRestarts, $"row restarts differ {label}");
        Assert.True(kept.Stats.MeasuredCodeUnits <= fresh.Stats.MeasuredCodeUnits, $"kept walks measured more {label}");
        Assert.Equal(0, fresh.Stats.ResumedMeasurements);
        return (kept, fresh);
    }

    private static OutputFormattingOptions ZeroIndent(int width)
        => new() { PreferredLineWidth = width, IndentSize = 0, NewLine = "\n" };

    // Every level wraps the previous one, so each level's measurement enters it.
    private static Result Chain(int depth, Func<int, Result, Result> level)
    {
        Result value = Num(7);
        for (var k = 0; k < depth; k++)
            value = level(k, value);
        return value;
    }

    private static readonly Result SharedItem = List(Num(1), Str("x y"));

    private static Result ChainOf(string shape, int depth) => shape switch
    {
        // One item per level: the walk of a level is the walk of the next one shifted by one.
        "lists" => Chain(depth, (_, inner) => List(inner)),
        // A number before the nested item, and a sequence that keeps its parentheses.
        "sequences" => Chain(depth, (k, inner) => Seq(Num(k % 1000), inner)),
        // The nested item first: each level is entered at its very start.
        "nested-first" => Chain(depth, (k, inner) => Seq(inner, Num(k % 1000))),
        // A wide level: items the walk completes (measured aside) before the item it enters.
        "wide" => Chain(depth, (k, inner) => List(List(Num(1)), Str("a b"), Seq(Num(2), Num(3)), Num(k % 1000), inner)),
        // A completed item that is opened anyway (two structured children) before the entered one.
        "opened-before" => Chain(depth, (_, inner) => List(Seq(List(Num(1)), List(Num(2))), inner)),
        // One shared value object at two positions of every level (a list: a sequence with two
        // structured children is opened without a measurement).
        "shared" => Chain(depth, (_, inner) => List(SharedItem, inner, SharedItem)),
        // The entered item is opened without a measurement (two structured children), and the
        // walk moves into it for the measurement of its first item.
        "opened-entered" => Chain(depth, (_, inner) => List(Seq(inner, List(Num(1))))),
        _ => throw new ArgumentOutOfRangeException(nameof(shape)),
    };

    public static TheoryData<string, bool> ChainCases()
    {
        var data = new TheoryData<string, bool>();
        foreach (var shape in new[] { "lists", "sequences", "nested-first", "wide", "opened-before", "shared", "opened-entered" })
        foreach (var concise in new[] { false, true })
            data.Add(shape, concise);
        return data;
    }

    // ---------------------------------------------------------------- texts at zero indentation

    [Fact]
    public void ZeroIndent_NestedLists_OpenUntilTheSubtreeFits()
    {
        // [[[[[[7]]]]]] is 13 code units; under a width of 6 every level down to [[7]] is opened.
        var value = Chain(6, (_, inner) => List(inner));
        const string expected = "[\n[\n[\n[\n[[7]]\n]\n]\n]\n]";

        foreach (var concise in new[] { false, true })
        {
            var kept = RenderBoth([value], ZeroIndent(6), concise);
            Assert.Equal(expected, kept.Text);

            // The root walk enters [[[[[7]]]]], [[[[7]]]] and [[[7]]] in turn; [[7]] was completed
            // by the walk of [[[7]]] and is measured aside. Fresh walks measure 6 + 6 + 6 + 6 + 5
            // code units, the kept walk 6 + 1 + 1 + 1 + 5.
            Assert.Equal(3, kept.Stats.ResumedMeasurements);
            Assert.Equal(14, kept.Stats.MeasuredCodeUnits);
            Assert.Equal(29, Render([value], ZeroIndent(6), concise, resume: false).Stats.MeasuredCodeUnits);
        }
    }

    [Fact]
    public void ZeroIndent_NestedSequences_KeepTheirParentheses()
    {
        // (1, (2, (3, (4, 5)))) under a width of 10. Concise hides only the root's parentheses (a
        // root block over blank-line root spacing); at zero indentation a child sequence opened
        // over several lines keeps them.
        var value = Seq(Num(1), Seq(Num(2), Seq(Num(3), Seq(Num(4), Num(5)))));

        Assert.Equal(
            "(\n1,\n(\n2,\n(\n3,\n(4, 5)\n)\n)\n)",
            RenderBoth([value], ZeroIndent(10), concise: false).Text);
        Assert.Equal(
            "1\n(\n2,\n(\n3,\n(4, 5)\n)\n)",
            RenderBoth([value], ZeroIndent(10), concise: true).Text);
    }

    [Fact]
    public void ZeroIndent_WideLevel_WritesCompletedItemsFromTheirOwnMeasurement()
    {
        // Under a width of 26 the walk of the root completes the three short items and enters the
        // last one, which is measured by continuing that walk.
        var value = List(List(Num(1)), Str("a b"), Seq(Num(2), Num("3.50")), List(List(Num(4), Str("it's")), Seq()));
        var options = ZeroIndent(26);
        const string expected = "[\n[1],\n'a b',\n(2, 3.50),\n[[4, it's], ()]\n]";

        foreach (var concise in new[] { false, true })
        {
            var kept = RenderBoth([value], options, concise);
            Assert.Equal(expected, kept.Text);
            Assert.Equal(1, kept.Stats.ResumedMeasurements);
        }
    }

    [Fact]
    public void ZeroIndent_DisplayLimitSweep_MatchesTheFreshRouteAtEveryLimit()
    {
        var value = Seq(Str("totals"), ChainOf("wide", 4), ChainOf("sequences", 5));
        foreach (var concise in new[] { false, true })
        {
            var full = RenderBoth([value], ZeroIndent(12), concise);
            Assert.True(full.Completed);
            Assert.True(full.Stats.ResumedMeasurements > 0);
            for (var limit = 0; limit <= full.Text.Length + 1; limit++)
            {
                var options = ZeroIndent(12) with { MaxDisplayLength = limit };
                var bounded = RenderBoth([value], options, concise, label: $"concise={concise} limit={limit}");
                Assert.Equal(limit >= full.Text.Length, bounded.Completed);
                if (bounded.Completed)
                    Assert.Equal(full.Text, bounded.Text);
            }
        }
    }

    // ---------------------------------------------------------------- growth

    [Theory]
    [MemberData(nameof(ChainCases))]
    public void ZeroIndentChains_MeasureInProportionToTheirOutput(string shape, bool concise)
    {
        // At zero indentation every level of a chain deeper than the line is opened, so fresh
        // walks measured a full line width per opened level: at least depth × width / 4 code
        // units here (asserted, so the comparison cannot pass vacuously). A kept walk is continued
        // by the code units the next level adds: the measurement stays within a small multiple
        // of the output plus one line width, at both depths.
        const int width = 1_000;
        foreach (var depth in new[] { 1_500, 3_000 })
        {
            var (kept, fresh) = RenderBothRoutes([ChainOf(shape, depth)], ZeroIndent(width), concise, label: $"{shape} depth {depth}");

            Assert.True(kept.Completed);
            Assert.True(kept.Stats.ResumedMeasurements >= depth / 2, $"{shape}: {kept.Stats.ResumedMeasurements} resumed at depth {depth}");
            Assert.True(
                fresh.Stats.MeasuredCodeUnits >= (long)depth * width / 4,
                $"{shape}: fresh walks measured only {fresh.Stats.MeasuredCodeUnits} at depth {depth}");
            Assert.True(
                kept.Stats.MeasuredCodeUnits <= 3L * (kept.Text.Length + width),
                $"{shape}: kept walks measured {kept.Stats.MeasuredCodeUnits} for {kept.Text.Length} code units of output at depth {depth}");
        }
    }

    [Fact]
    public void ZeroIndentChain_AtTheWidestSupportedLine_StaysLinear()
    {
        // The reported shape: 20,000 nested lists under the supported maximum width. Fresh walks
        // measured about 20,000 × 10,000 = 2 × 10^8 code units for 70,003 code units of output.
        const int depth = 20_000;
        var options = ZeroIndent(OutputFormattingOptions.MaxSupportedPreferredLineWidth);
        foreach (var concise in new[] { false, true })
        {
            var kept = Render([ChainOf("lists", depth)], options, concise, resume: true);
            Assert.True(kept.Completed);
            Assert.Equal(70_003, kept.Text.Length);
            Assert.StartsWith("[\n[\n", kept.Text, StringComparison.Ordinal);
            Assert.True(
                kept.Stats.MeasuredCodeUnits <= 3L * (kept.Text.Length + options.PreferredLineWidth),
                $"measured {kept.Stats.MeasuredCodeUnits} code units");
        }
    }

    [Fact]
    public void RefusedLongAtom_AllocatesInProportionToItsNestedOutput()
    {
        // Each open bracket gives the atom one more column. Formatting its width+1 digits at
        // every level used 32 MB at width 4000, even though none of those appends fit.
        foreach (var concise in new[] { false, true })
        {
            foreach (var width in new[] { 1000, 4000 })
            {
                Result value = Num($"1e{width.ToString(CultureInfo.InvariantCulture)}");
                for (var i = 0; i < width; i++)
                    value = List(value);

                Result[] rows = [value];
                var options = ZeroIndent(width);
                var expected = string.Concat(Enumerable.Repeat("[\n", width)) + "1" + new string('0', width)
                    + string.Concat(Enumerable.Repeat("\n]", width));

                // Warm the number-formatting, layout and writer paths before the allocation window.
                bool Write(BoundedDisplayWriter writer)
                    => StructuredLayoutRenderer.WriteRows(rows, DisplayOptions.Default, options, concise, writer);
                Assert.True(Write(new BoundedDisplayWriter(expected.Length)));
                var writer = new BoundedDisplayWriter(expected.Length);
                var before = GC.GetAllocatedBytesForCurrentThread();
                var completed = Write(writer);
                var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

                Assert.True(completed);
                Assert.Equal(expected, writer.ToString());
                // 512 B per level covers layout frames, doubled arrays and emitted text. The
                // fixed allowance covers a number-buffer refill and the in-process GC quantum.
                Assert.True(allocated < 512L * width + 65_536, $"width {width} allocated {allocated} bytes");
            }
        }
    }

    [Fact]
    public void SharedDoublingValue_StaysWithinItsBoundedOutput()
    {
        // [A, A] doubling (the DAG of FormattingRobustnessTests) at zero indentation. An opened
        // level's second item, the same object as its first, starts a new kept walk; measurement
        // stays within a small multiple of the bounded output on both routes.
        Result value = Num(1);
        for (var i = 0; i < 24; i++)
            value = List(value, value);

        foreach (var concise in new[] { false, true })
        {
            var options = ZeroIndent(500) with { MaxDisplayLength = 200_000 };
            var kept = RenderBoth([value], options, concise);
            Assert.False(kept.Completed);
            Assert.True(kept.Stats.MeasuredCodeUnits <= 3L * (200_000 + 500), $"measured {kept.Stats.MeasuredCodeUnits}");
        }
    }

    [Fact]
    public void PositiveIndentation_IsUnchangedAndMeasuresNoMore()
    {
        foreach (var indent in new[] { 1, 2, 4 })
        foreach (var shape in new[] { "lists", "wide", "opened-before", "shared", "opened-entered" })
        foreach (var concise in new[] { false, true })
        {
            var options = new OutputFormattingOptions { PreferredLineWidth = 60, IndentSize = indent, NewLine = "\n" };
            RenderBoth([ChainOf(shape, 80)], options, concise, label: $"{shape} indent {indent} concise {concise}");
        }
    }

    // ---------------------------------------------------------------- string classification

    private static string LongLabel(int k)
        => new string((char)('a' + (k % 26)), 66) + k.ToString("D4", CultureInfo.InvariantCulture);

    [Fact]
    public void RetryingAStringAtItsRawLength_PreservesClassificationAndExhaustion()
    {
        var label = LongLabel(1) + " ";
        Result value = Str(label);
        for (var i = 0; i < 80; i++)
            value = List(value);

        foreach (var concise in new[] { false, true })
        foreach (var budget in new[] { label.Length - 1, label.Length })
        {
            // The first probes cannot fit the raw label. At its exact raw width the classifier
            // must run, even though the two quotes will still make the rendered token too wide.
            var rendered = RenderBoth([value], ZeroIndent(label.Length + 7), concise, budget);
            Assert.True(rendered.Completed);
            Assert.Equal(budget < label.Length, rendered.Stats.ClassificationExhausted);
            Assert.Equal(budget < label.Length ? 0 : label.Length, rendered.Stats.ChargedCodeUnits);
        }
    }

    [Fact]
    public void CachedLongStrings_AreClassifiedOnce_WhileWalksAreContinued()
    {
        // 40 distinct 70-unit labels, one per level: the classification cache keeps them all.
        var value = Chain(40, (k, inner) => List(Str(LongLabel(k)), inner));
        foreach (var concise in new[] { false, true })
        {
            var kept = RenderBoth([value], ZeroIndent(400), concise);
            Assert.Equal(40, kept.Stats.LongClassifications);
            Assert.Equal(40 * 70, kept.Stats.ChargedCodeUnits);
            Assert.Equal(0, kept.Stats.UncachedClassifications);
            Assert.True(kept.Stats.ResumedMeasurements >= 30, $"{kept.Stats.ResumedMeasurements} resumed");
        }
    }

    [Fact]
    public void UncachedLongStrings_AreChargedExactlyAsFreshWalksChargeThem()
    {
        // 200 distinct labels overflow the 64-entry cache, so a label past the first 64 is charged
        // on every walk that reaches it. Continuing a walk would skip those repeated charges, change
        // the remaining budget and so where it runs out; walks are therefore not continued once
        // the policy made an uncached classification, and the charges equal the fresh route's.
        var value = Chain(200, (k, inner) => List(Str(LongLabel(k)), inner));
        foreach (var concise in new[] { false, true })
        foreach (long? budget in new long?[] { null, 70 * 400, 70 * 150 })
        {
            var kept = RenderBoth([value], ZeroIndent(4_000), concise, budget, $"concise {concise} budget {budget}");
            Assert.True(kept.Stats.UncachedClassifications > 0);
            if (budget is 70 * 150)
            {
                Assert.True(kept.Stats.ClassificationExhausted);
                Assert.Equal(1, kept.Stats.RowRestarts);
            }
        }
    }

    // ---------------------------------------------------------------- generated differential

    [Fact]
    public void GeneratedValues_RenderAndChargeLikeFreshWalks()
    {
        // Seeded values over every layout option: chains with side items, wide and pair-run
        // sequences, shared subtrees, strings that need, refuse or break quoting, long strings
        // past the classification cache, display limits and classification budgets.
        var random = new Random(20261122);
        var generator = new ValueGenerator(random);
        int[] widths = [1, 2, 3, 5, 8, 12, 20, 40, 100, 10_000];
        int[] indents = [0, 0, 0, 1, 2, 3];
        var modes = new[] { StringDelimiterMode.Never, StringDelimiterMode.WhenNeeded, StringDelimiterMode.Always };
        var resumed = 0L;
        for (var c = 0; c < 600; c++)
        {
            var rows = new Result[1 + random.Next(3)];
            for (var r = 0; r < rows.Length; r++)
                rows[r] = c % 7 == 3 ? generator.LabelChain() : generator.Value(1 + random.Next(5));

            var options = new OutputFormattingOptions
            {
                PreferredLineWidth = widths[random.Next(widths.Length)],
                IndentSize = indents[random.Next(indents.Length)],
                StringDelimiters = modes[random.Next(modes.Length)],
                RootOutputSpacing = random.Next(3),
                NewLine = random.Next(4) == 0 ? "\r\n" : "\n",
                MaxDisplayLength = random.Next(4) == 0 ? random.Next(400) : null,
            };
            long? budget = random.Next(4) switch
            {
                0 => 0,
                1 => 70 + random.Next(400),
                2 => 64 * (60 + random.Next(30)),
                _ => null,
            };

            foreach (var concise in new[] { false, true })
                resumed += RenderBoth(rows, options, concise, budget, $"case {c} concise {concise}").Stats.ResumedMeasurements;
        }

        Assert.True(resumed > 1_000, $"only {resumed} measurements continued a kept walk");
    }

    private sealed class ValueGenerator(Random random)
    {
        private readonly List<Result> _built = [];

        public Result Value(int depth)
        {
            if (_built.Count > 0 && random.Next(10) == 0)
                return _built[random.Next(_built.Count)];

            Result value;
            switch (depth <= 0 ? random.Next(5) : random.Next(12))
            {
                case 0:
                    value = Atom();
                    break;
                case 1:
                    value = Text();
                    break;
                case 2:
                    value = new Result.Bool(random.Next(2) == 0);
                    break;
                case 3:
                case 4:
                    value = random.Next(2) == 0 ? Seq() : List();
                    break;
                case 5:
                {
                    var chain = Value(0);
                    for (var k = 1 + random.Next(60); k > 0; k--)
                    {
                        var side = random.Next(4) == 0 ? Value(0) : null;
                        Result[] items = side is null ? [chain] : random.Next(2) == 0 ? [side, chain] : [chain, side];
                        chain = random.Next(2) == 0 ? Result.ListValue.TakeOwnership(items) : Result.SequenceValue.TakeOwnership(items);
                    }

                    value = chain;
                    break;
                }
                case 6:
                {
                    var items = new Result[2 * (1 + random.Next(5))];
                    for (var i = 0; i < items.Length; i += 2)
                    {
                        items[i] = Text();
                        items[i + 1] = random.Next(2) == 0 ? Atom() : Text();
                    }

                    value = Result.SequenceValue.TakeOwnership(items);
                    break;
                }
                default:
                {
                    var items = new Result[random.Next(7)];
                    for (var i = 0; i < items.Length; i++)
                        items[i] = Value(depth - 1 - random.Next(2));
                    value = random.Next(2) == 0 ? Result.ListValue.TakeOwnership(items) : Result.SequenceValue.TakeOwnership(items);
                    break;
                }
            }

            if (value is Result.SequenceValue or Result.ListValue)
                _built.Add(value);
            return value;
        }

        // A deep chain of distinct long labels, more than the classification cache holds.
        public Result LabelChain()
        {
            Result chain = Atom();
            var offset = random.Next(200);
            for (var k = 60 + random.Next(120); k > 0; k--)
            {
                var label = Str(LongLabel(offset + k) + (k % 3 == 0 ? " x" : ""));
                Result[] items = random.Next(5) switch
                {
                    0 => [label, chain],
                    1 => [chain, label],
                    2 => [Atom(), label, chain],
                    3 => [chain],
                    _ => [label, Atom(), chain, Text()],
                };
                chain = random.Next(2) == 0 ? Result.ListValue.TakeOwnership(items) : Result.SequenceValue.TakeOwnership(items);
            }

            return chain;
        }

        private Result Atom() => random.Next(5) switch
        {
            0 => Num(random.Next(10)),
            1 => Num(random.Next(100_000) - 50_000),
            2 => Num("2.50"),
            3 => Num("-0.004"),
            _ => Num("1" + new string('0', 40)),
        };

        private Result Text() => random.Next(11) switch
        {
            0 => Str(string.Empty),
            1 => Str("a b"),
            2 => Str("x,y"),
            3 => Str("it's"),
            4 => Str("12"),
            5 => Str("line\nbreak"),
            6 => Str("NaN"),
            7 => Str(LongLabel(random.Next(80))),
            8 => Str(LongLabel(random.Next(80)) + "\n"),
            9 => Str("w" + random.Next(100).ToString(CultureInfo.InvariantCulture)),
            _ => Str("plain"),
        };
    }

    // ---------------------------------------------------------------- the kept walk itself

    private static readonly Result[] WalkValues =
    [
        List(Num(1), Seq(Str("a b"), List(Num("2.50"), Seq())), Str("it's"), new Result.Bool(true), Seq(List(Seq(Num(3))))),
        Seq(Seq(Seq(Seq(Str(string.Empty), Num(-4)), List()), Str("x,y")), Seq(Str("plain"), Num(5))),
        List(List(List(List(List(Num(1), Num(2)), Num(3)), Num(4)), Num(5)), Seq()),
        Seq(SharedItem, List(SharedItem, SharedItem), SharedItem),
    ];

    private static (bool Fits, string Text) FreshMeasure(Result value, long budget, IStringTextPolicy policy)
    {
        var sink = new CappedWidthSink();
        sink.Reset((int)budget, keepText: true);
        var fits = ValueTextRenderer.AppendValue(value, DisplayOptions.Default, policy, sink);
        return (fits, fits ? sink.Text.ToString() : string.Empty);
    }

    [Theory]
    [InlineData(StringDelimiterMode.Never)]
    [InlineData(StringDelimiterMode.WhenNeeded)]
    [InlineData(StringDelimiterMode.Always)]
    public void KeptWalk_MeasuresEveryEnteredStructureLikeAFreshWalk(StringDelimiterMode mode)
    {
        // For every cap of the first walk, every depth of the structures it entered, and every
        // budget of the continued measurement: the same answer and the same kept text as a fresh
        // walk of that structure. The values cover refusals at separators, closers, nested
        // openers, numbers, and inside a quoted string, and an empty string that renders as no text.
        var policy = new DelimitedStringTextPolicy(mode, DelimitedStringTextPolicy.DefaultClassificationBudget(0)).Measurement;
        foreach (var value in WalkValues)
        {
            var full = FreshMeasure(value, int.MaxValue, policy).Text;
            for (var cap = 0; cap <= full.Length + 1; cap++)
            {
                var walk = new ValueTextRenderer.ResumableMeasurement();
                var fits = walk.Measure(value, cap, 0, DisplayOptions.Default, policy);
                Assert.Equal(FreshMeasure(value, cap, policy), (fits, fits ? walk.Text.ToString() : string.Empty));
                if (fits) continue;

                // The structures the refused walk entered, outermost first.
                var entered = new List<Result>();
                for (var probe = Refused(value, cap, policy); probe.EnteredChild is { } child; probe.DescendIntoEnteredChild())
                    entered.Add(child);

                for (var depth = 0; depth < entered.Count; depth++)
                {
                    var target = entered[depth];
                    var targetText = FreshMeasure(target, int.MaxValue, policy).Text;
                    for (var budget = 0; budget <= targetText.Length + 1; budget++)
                    {
                        var resumed = Refused(value, cap, policy);
                        for (var d = 0; d < depth; d++)
                            resumed.DescendIntoEnteredChild();
                        Assert.Same(target, resumed.EnteredChild);
                        var resumedFits = resumed.MeasureEnteredChild(budget, DisplayOptions.Default, policy);
                        Assert.Equal(
                            FreshMeasure(target, budget, policy),
                            (resumedFits, resumedFits ? resumed.Text.ToString() : string.Empty));
                        Assert.Equal(!resumedFits, resumed.IsSuspendedIn(target));
                    }
                }
            }
        }
    }

    private static ValueTextRenderer.ResumableMeasurement Refused(Result value, long cap, IStringTextPolicy policy)
    {
        var walk = new ValueTextRenderer.ResumableMeasurement();
        Assert.False(walk.Measure(value, cap, 0, DisplayOptions.Default, policy));
        Assert.True(walk.IsSuspendedIn(value) || !walk.IsSuspended);
        return walk;
    }

    [Fact]
    public void KeptWalk_ContinuedRepeatedly_MatchesFreshWalksUnderChangingBudgets()
    {
        // A chain of continuations with seeded budgets, each one a refusal that the next continues.
        var policy = new DelimitedStringTextPolicy(StringDelimiterMode.WhenNeeded, DelimitedStringTextPolicy.DefaultClassificationBudget(0)).Measurement;
        var random = new Random(7);
        var value = ChainOf("wide", 30);
        for (var trial = 0; trial < 300; trial++)
        {
            var walk = new ValueTextRenderer.ResumableMeasurement();
            var cap = random.Next(200);
            if (walk.Measure(value, cap, 0, DisplayOptions.Default, policy)) continue;

            while (walk.EnteredChild is { } child)
            {
                var budget = random.Next(200);
                var fits = walk.MeasureEnteredChild(budget, DisplayOptions.Default, policy);
                Assert.Equal(FreshMeasure(child, budget, policy), (fits, fits ? walk.Text.ToString() : string.Empty));
                if (fits) break;
            }
        }
    }

    [Fact]
    public void KeptWalk_KeepsBoundedStorageAlongADeepChain()
    {
        // Continuing down 50,000 levels drops the text and the levels above the measured value as
        // it goes, so its storage follows one line and the walk's depth, not the chain.
        var policy = new DelimitedStringTextPolicy(StringDelimiterMode.WhenNeeded, 0).Measurement;
        var value = ChainOf("lists", 50_000);
        var walk = new ValueTextRenderer.ResumableMeasurement();
        Assert.False(walk.Measure(value, 100, 0, DisplayOptions.Default, policy));
        Assert.Equal(100, walk.MeasuredCodeUnits);

        Assert.False(walk.MeasureEnteredChild(100, DisplayOptions.Default, policy));
        var levels = 1;
        var before = GC.GetAllocatedBytesForCurrentThread();
        while (walk.EnteredChild is not null)
        {
            if (walk.MeasureEnteredChild(100, DisplayOptions.Default, policy)) break;
            levels++;
        }

        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        // Every level from the 49,999 lists inside the root down to the 50-list level (101 code
        // units) is refused, each continuation accepting one more code unit. The last refusal is
        // at that level's own closer: its one item, 99 code units, was completed by the walk.
        Assert.True(walk.IsSuspended);
        Assert.Equal(50_000 - 50, levels);
        Assert.Equal(100L + levels, walk.MeasuredCodeUnits);
        Assert.Equal(1, walk.CompletedItems);
        Assert.Equal(-1, walk.EnteredChildIndex);

        // A text buffer and level array kept for the whole chain would allocate megabytes over
        // 50,000 levels. Doubling the text buffer to 200 code units costs about 424 bytes, and the
        // larger level array (256 levels of 32 bytes) costs about 8 KB. The in-process counter may
        // also report one ~8 KB allocation quantum.
        Assert.True(allocated < 32_768, $"continuing the chain allocated {allocated} bytes");
    }
}
