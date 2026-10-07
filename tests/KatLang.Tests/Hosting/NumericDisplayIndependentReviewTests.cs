using System.Globalization;
using System.Numerics;
using KatLang.Formatting;

namespace KatLang.Tests.Hosting;

public sealed class NumericDisplayIndependentReviewTests
{
    private static readonly TimeSpan Timeout = TimeSpan.FromSeconds(30);

    private sealed class AtomFormatter : OutputFormatter
    {
        public override string Id => "review-atoms";
        protected override bool WriteSuccessOutput(IReadOnlyList<Result> rows,
            OutputFormattingOptions options, BoundedOutputWriter writer)
        {
            for (var i = 0; i < rows.Count; i++)
            {
                if (i > 0 && !writer.Append("|")) return false;
                if (!writer.AppendAtom(Assert.IsType<Result.Atom>(rows[i]).Value)) return false;
            }
            return true;
        }
    }

    [Fact]
    public void EqualNumericLeaves_HashEqually_InsideIndependentStructuresAndHashedContainers()
    {
        foreach (var pair in NumericRepresentativeSelectionTests.Pairs)
        {
            if (!(bool)pair[3]) continue;
            var a = Assert.IsType<RunResult.Success>(KatLangEngine.Run((string)pair[1])).Value;
            var b = Assert.IsType<RunResult.Success>(KatLangEngine.Run((string)pair[2])).Value;
            var an = Assert.IsType<Result.Atom>(a).Value;
            var bn = Assert.IsType<Result.Atom>(b).Value;
            Assert.True(an.Equals(bn));
            Assert.Equal(an.GetHashCode(), bn.GetHashCode());
            foreach (var (left, right) in new (Result, Result)[]
            {
                (a, b),
                (new Result.SequenceValue([a, new Result.ListValue([a])]),
                    new Result.SequenceValue([b, new Result.ListValue([b])])),
                (new Result.ListValue([new Result.SequenceValue([a, a]), a]),
                    new Result.ListValue([new Result.SequenceValue([b, b]), b])),
            })
            {
                Assert.True(Result.ValueComparer.Equals(left, right));
                Assert.Equal(Result.ValueComparer.GetHashCode(left), Result.ValueComparer.GetHashCode(right));
                var set = new HashSet<Result>(Result.ValueComparer) { left };
                Assert.False(set.Add(right));
                var map = new Dictionary<Result, Result>(Result.ValueComparer) { [left] = left };
                Assert.Same(left, map[right]);
            }
        }
    }

    [Fact]
    public async Task NestedCollectorSuffixes_KeepWrittenFirstOrLaterRichestWholeContribution()
    {
        foreach (var (call, expected) in new[]
        {
            ("P((1.00, [1.0, 9, 8], 1), 1.000)", "'1.00'"),
            ("P((1.00, [1.0, 9, 8], 1), A)", "'1.000'"),
            ("T(1.0, A, 1.00)", "'1.000'"),
            ("T(A, 1.0, A)", "'1.000'"),
            ("T(1.00, 1.0, 1)", "'1.00'"),
            ("N([(1.0, [2]), 7], [(1, [2.0]), 7.0], [(1.00, [2.00]), 7.00])",
                "L[S[1.0, L[2]], 7]"),
        })
        {
            var source = "A = 1.000\nP((x, [x, *rest], x), x) = x.string\n" +
                "T(x, x, x) = x.string\nN(x, x, x) = x\n" + call;
            SourceProvenance.ParseValid(source);
            var observed = await SixRouteAgreement.OnEveryRouteAsync(source, NumericRepresentativeSelectionTests.Exact);
            Assert.Equal("ok", observed.Kind);
            Assert.Equal(expected, observed.Value);
        }
    }

    // Owner follow-up: all permutations of this contribution set fail, while
    // NEED-04 reports the first violated contract in each written order. Each fixed
    // program must agree exactly across routes, including error details and effects.
    [Fact]
    public async Task MixedThreeContributionConflicts_ReportTheFirstExecutedContract()
    {
        const string prefix = "A = 1.0\nB = 1.00\nP(x, x, x) = x\n";
        foreach (var (arguments, code) in new[]
        {
            ("A, B, 2", KatLangErrorCode.TypeMismatch),
            ("B, A, 2", KatLangErrorCode.TypeMismatch),
            ("A, 2, B", KatLangErrorCode.ArityMismatch),
            ("B, 2, A", KatLangErrorCode.ArityMismatch),
            ("2, A, B", KatLangErrorCode.ArityMismatch),
            ("2, B, A", KatLangErrorCode.ArityMismatch),
        })
        {
            var source = prefix + "P(" + arguments + ")";
            SourceProvenance.ParseValid(source);
            var observed = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.Equal("err", observed.Kind);
            Assert.StartsWith(code + ":", Assert.Single(observed.Errors), StringComparison.Ordinal);
        }
    }

    [Fact]
    public async Task RetainedResultsAndSharedFormatter_StayIndependentAcrossUnfilteredAndFailedRuns()
    {
        var formatter = new AtomFormatter();
        var shared = new RunOptions { DefaultDisplayDecimals = 5, RandomSeed = 31 };
        var runs = new List<(RunResult.Success Run, int? Decimals, string Text)>();
        foreach (var (source, options, decimals, text) in new (string, RunOptions, int?, string)[]
        {
            ("DisplayDecimals = 7\n1.55555", shared, 5, "1.55555"),
            ("1.55555", new RunOptions(), null, "1.55555"),
            ("DisplayDecimals = 2\n1.55555", shared, 2, "1.56"),
            ("1.55555", shared, 5, "1.55555"),
        })
        {
            var run = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, options));
            runs.Add((run, decimals, text));
            Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync("DisplayDecimals = 100\n1", shared));
            Assert.Equal(5, shared.DefaultDisplayDecimals);
        }
        foreach (var (run, decimals, text) in runs.AsEnumerable().Reverse())
        {
            Assert.Equal(decimals, run.DisplayOptions.Decimals);
            Assert.Equal(text, formatter.Format(run));
            Assert.Equal(text, run.ToDisplayString());
            // A per-call length cap must preserve the already composed precision.
            // Pin text and fit directly: comparing two formatter calls can mask a
            // shared precision-loss bug in the bounded formatting path.
            var cap = new OutputFormattingOptions { MaxDisplayLength = text.Length };
            Assert.Equal(text, formatter.Format(run, cap));
            Assert.False(formatter.RenderDisplay(run, cap).LimitExceeded);
            Assert.Equal(text, OutputFormatters.Exact.Format(run, cap));
        }
    }

    [Fact]
    public async Task ConcurrentSuspendedSourceFilters_WithSharedOptionsAndFormatter_CompleteOutOfOrder()
    {
        var gates = Enumerable.Range(0, 3).Select(_ => new TaskCompletionSource<Result>(
            TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
        var entered = Enumerable.Range(0, 3).Select(_ => new TaskCompletionSource(
            TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
        var operations = HostOperations.Create(HostOperation.CreateAsync("Digits", async (args, _) =>
        {
            var lane = (int)Assert.IsType<Result.Atom>(args[0]).Value;
            entered[lane].SetResult();
            return await gates[lane].Task;
        }, "lane"));
        var shared = new RunOptions { DefaultDisplayDecimals = 5, HostOperations = operations };
        var formatter = new AtomFormatter();
        var pending = Enumerable.Range(0, 3).Select(i => KatLangEngine.RunAsync(
            $"DisplayDecimals = Digits({i})\n1.55555\n2.55555", shared)).ToArray();
        try
        {
            await Task.WhenAll(entered.Select(g => g.Task)).WaitAsync(Timeout);
            Assert.All(pending, task => Assert.False(task.IsCompleted));
            foreach (var i in new[] { 2, 0, 1 })
            {
                gates[i].SetResult(new Result.Atom(new[] { 7, 2, 5 }[i]));
                var run = Assert.IsType<RunResult.Success>(await pending[i].WaitAsync(Timeout));
                Assert.Equal(new[] { 5, 2, 5 }[i], run.DisplayOptions.Decimals);
            }
        }
        finally
        {
            foreach (var gate in gates) gate.TrySetResult(new Result.Atom(5));
        }
        var complete = await Task.WhenAll(pending).WaitAsync(Timeout);
        Assert.Equal("1.56|2.56", formatter.Format(complete[1]));
        Assert.Equal("1.55555|2.55555", formatter.Format(complete[0]));
        Assert.Equal("1.55555|2.55555", formatter.Format(complete[2]));
        Assert.Equal(5, shared.DefaultDisplayDecimals);
    }

    [Fact]
    public async Task FreshDisplayCorpus_UsesOneFilterForAllRows_AndNeverChangesRepresentation()
    {
        string[] settings = ["", "0", "1", "5", "7", "99", "1 + 1", "-0", "{ 7 }"];
        int?[] hosts = [null, 0, 1, 5, 7, 99];
        const string body = "1.555, 1.556, 1.50, -0.0, sqrt(-1), 1e6144 * 10, (1.555, [1.50]), 1.50.string";
        var baseline = Assert.IsType<RunResult.Success>(KatLangEngine.Run(body));
        var exact = NumericRepresentativeSelectionTests.Exact(baseline.Value);
        foreach (var setting in settings)
        foreach (var host in hosts)
        {
            int? source = setting switch { "" => null, "1 + 1" => 2, "-0" => 0, "{ 7 }" => 7,
                _ => int.Parse(setting, CultureInfo.InvariantCulture) };
            var effective = new[] { source, host }.OfType<int>().Order().Cast<int?>().FirstOrDefault();
            var code = setting.Length == 0 ? body : $"DisplayDecimals = {setting}\n{body}";
            SourceProvenance.ParseValid(code);
            foreach (var twin in new[] { false, true })
            {
                var options = new RunOptions { DefaultDisplayDecimals = host,
                    HostOperations = twin ? HostOperations.Create(HostOperation.CreateAsync("unused", (_, _) =>
                        ValueTask.FromResult<Result>(new Result.Atom(0)))) : null };
                var run = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(code, options));
                Assert.Equal(effective, run.DisplayOptions.Decimals);
                Assert.Equal(exact, NumericRepresentativeSelectionTests.Exact(run.Value));
                var reference = Assert.IsType<RunResult.Success>(KatLangEngine.Run(body,
                    new RunOptions { DefaultDisplayDecimals = effective }));
                foreach (var formatter in new[] { OutputFormatters.Exact, OutputFormatters.Readable, OutputFormatters.Concise })
                    Assert.Equal(formatter.Format(reference), formatter.Format(run));
                foreach (var limit in new[] { 1, 8, 40, 99 })
                {
                    var formatOptions = new OutputFormattingOptions { MaxDisplayLength = limit };
                    var expected = OutputFormatters.Exact.RenderDisplay(reference, formatOptions);
                    var actual = OutputFormatters.Exact.RenderDisplay(run, formatOptions);
                    Assert.Equal(expected.Text, actual.Text);
                    Assert.Equal(expected.LimitExceeded, actual.LimitExceeded);
                    Assert.Equal(expected.LimitError?.Code, actual.LimitError?.Code);
                    Assert.Equal(expected.LimitError?.Message, actual.LimitError?.Message);
                }
            }
        }
    }
}
