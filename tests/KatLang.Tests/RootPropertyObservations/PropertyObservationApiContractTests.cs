using static KatLang.Tests.RootPropertyObservations.PropertyObservationTestSupport;

namespace KatLang.Tests.RootPropertyObservations;

/// <summary>
/// D2(A): the snapshot is ancillary host data carried by <see cref="RunResult"/> through the
/// equality-transparent <see cref="RuntimeStateSlot{T}"/>, so <see cref="RunResult"/>'s record
/// equality, hashing, printing, and copying are exactly what they were; the snapshot types are
/// read-only and engine-produced; rendering reuses the canonical bounded renderer.
/// </summary>
public class PropertyObservationApiContractTests
{
    private const string Source = "Price = 200\nVAT = Price * 0.21\nTotal = Price + VAT\nTotal";

    public static TheoryData<string> VariantSources => new() { Source, "A = 1\n", "B = 2\nA = 1 / 0\nB + A" };

    [Theory]
    [MemberData(nameof(VariantSources))]
    public void Snapshot_TakesNoPartInEqualityHashingOrPrinting(string source)
    {
        var observed = Run(source);
        var stripped = observed with { PropertyObservations = null };
        var other = observed with { PropertyObservations = PropertyObservations.Empty };

        Assert.NotNull(observed.PropertyObservations);
        Assert.Null(stripped.PropertyObservations);
        Assert.Equal(observed, stripped);
        Assert.Equal(observed, other);
        Assert.True(observed == stripped);
        Assert.Equal(observed.GetHashCode(), stripped.GetHashCode());
        Assert.Equal(observed.GetHashCode(), other.GetHashCode());
        Assert.Equal(stripped.ToString(), observed.ToString());
        Assert.DoesNotContain("PropertyObservations", observed.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void Printing_KeepsTheSynthesizedMemberLayout()
    {
        var printed = KatLangEngine.Run("1 + 2").ToString();
        Assert.StartsWith("Success { IsSuccess = True, IsNoProgramOutput = False, IsFailure = False, Root = ", printed, StringComparison.Ordinal);
        Assert.Contains(", Value = Atom { Value = 3 }, Atoms = ", printed, StringComparison.Ordinal);

        var parse = KatLangEngine.Run("1 +").ToString();
        Assert.StartsWith("ParseFailure { IsSuccess = False, IsNoProgramOutput = False, IsFailure = True, Errors = ", parse, StringComparison.Ordinal);
    }

    [Fact]
    public void RecordCopies_ShareTheSnapshot()
    {
        var observed = Run(Source);
        var copy = observed with { };
        Assert.Same(observed.PropertyObservations, copy.PropertyObservations);
        Assert.Same(observed.PropertyObservations, observed.WithHostDisplayDecimals(1).PropertyObservations);
    }

    [Fact]
    public void Collection_IsReadOnly_AndIndexedInPublicationOrder()
    {
        var observations = Run(Source).PropertyObservations!;

        Assert.IsAssignableFrom<IReadOnlyList<PropertyValueObservation>>(observations);
        Assert.False(typeof(ICollection<PropertyValueObservation>).IsAssignableFrom(typeof(PropertyObservations)));
        Assert.False(typeof(System.Collections.IList).IsAssignableFrom(typeof(PropertyObservations)));
        Assert.Equal(3, observations.Count);
        Assert.Equal(["Price", "VAT", "Total"], observations.Select(static o => o.Name));
        Assert.Equal(observations.Select(static o => o.Name), Enumerable.Range(0, observations.Count).Select(i => observations[i].Name));
        Assert.Throws<IndexOutOfRangeException>(() => observations[3]);
    }

    [Fact]
    public void Observation_IsAValueRecord_WithStatusValueInvariants()
    {
        var first = Single(Run(Source), "VAT");
        var second = Single(Run(Source), "VAT");

        // Value equality: same name, anchor, status, structurally equal value, count.
        Assert.Equal(first, second);
        Assert.Equal(PropertyValueStatus.Available, first.Status);
        Assert.NotNull(first.Value);
        Assert.Equal(1, first.EmittedCount);
        Assert.Equal(0, (int)PropertyValueStatus.Available);
        Assert.Equal(1, (int)PropertyValueStatus.Withheld);
    }

    [Fact]
    public void RenderPropertyValue_ValidatesItsArgument_AndIsBoundedByTheRunsDisplayLimit()
    {
        var result = Run(Source);
        Assert.Throws<ArgumentNullException>(() => result.RenderPropertyValue(null!));

        var options = new RunOptions
        {
            ObservePropertyValues = true,
            EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 40 },
        };
        var bounded = KatLangEngine.Run("Big = range(1, 100)\nBig.count", options);
        var rendering = bounded.RenderPropertyValue(Single(bounded, "Big"));
        Assert.True(rendering.LimitExceeded);
        Assert.True(rendering.Text.Length <= 40);
        Assert.Equal("100", bounded.ToDisplayString());
    }

    [Fact]
    public void RenderPropertyValue_RendersThePropertysOwnRows_LikeAProgramWhoseOutputIsItsBody()
    {
        // The observation keeps the property's own value boundary: `P = 1, 'two', …` emits three
        // rows, rendered exactly like the program `1, 'two', …` — while the output row `P` reads it
        // as ONE value (a property read is a value boundary) and renders the sequence.
        foreach (var (source, name, body) in new[]
        {
            ("P = 1, 'two', [3, (4, 5)]\nP", "P", "1, 'two', [3, (4, 5)]"),
            ("X = 2 / 3\nDisplayDecimals = 3\nX", "X", "DisplayDecimals = 3\n2 / 3"),
            ("S = 'text'\nS", "S", "'text'"),
            ("E = ()\nE", "E", "()"),
            ("Q = (1, 2)\nQ", "Q", "(1, 2)"),
        })
        {
            var result = Run(source);
            Assert.Equal(KatLangEngine.Run(body).ToDisplayString(), result.RenderPropertyValue(Single(result, name)).Text);
        }

        var rows = Run("P = 1, 2\nP");
        Assert.Equal("(1, 2)", rows.ToDisplayString());
        Assert.Equal("1" + Environment.NewLine + "2", rows.RenderPropertyValue(Single(rows, "P")).Text);
    }

    [Fact]
    public async Task ConcurrentRuns_SharingOneOptionsObject_HaveIndependentSnapshots()
    {
        var log = new TickLog();
        var options = new RunOptions { ObservePropertyValues = true, HostOperations = log.Operations(suspending: true) };
        var sources = Enumerable.Range(0, 32).Select(static i => $"A{i} = {i}\nB{i} = A{i} * 2\nT = trace(B{i})\nT").ToArray();

        var results = await Task.WhenAll(sources.Select(source => Task.Run(() => KatLangEngine.RunAsync(source, options))));

        for (var i = 0; i < sources.Length; i++)
            Assert.Equal($"A{i}={i}#1; B{i}={i * 2}#1; T={i * 2}#1", Describe(results[i]));
        Assert.Equal(sources.Length, results.Select(static r => r.PropertyObservations).Distinct().Count());
    }

    [Fact]
    public void Cancellation_PropagatesWithoutAResult_WhetherOrNotObservationIsRequested()
    {
        foreach (var observe in new[] { false, true })
        {
            using var cancellation = new CancellationTokenSource();
            var operations = HostOperations.Create(
                HostOperation.Create("stop", (_, _) => { cancellation.Cancel(); return new Result.Atom(1); }));
            var options = new RunOptions
            {
                ObservePropertyValues = observe,
                HostOperations = operations,
                EvaluationCancellationToken = cancellation.Token,
            };

            const string source = "Before = 1\nStopped = stop()\nAfter = Before + Stopped + 1\nAfter";
            AssertLegal(source, operations);
            var thrown = Assert.ThrowsAny<OperationCanceledException>(() => KatLangEngine.Run(source, options));
            Assert.Equal(cancellation.Token, thrown.CancellationToken);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task Cancellation_AfterRealAsyncSuspension_PropagatesWithoutAResult(bool observe)
    {
        using var cancellation = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var operations = HostOperations.Create(HostOperation.CreateAsync("wait", async (_, token) =>
        {
            entered.SetResult();
            return await release.Task.WaitAsync(token);
        }));
        var options = new RunOptions
        {
            ObservePropertyValues = observe,
            HostOperations = operations,
            EvaluationCancellationToken = cancellation.Token,
        };
        const string source = "Before = 1\nStopped = wait()\nBefore + Stopped";
        AssertLegal(source, operations);

        var run = KatLangEngine.RunAsync(source, options);
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
        Assert.False(run.IsCompleted);
        cancellation.Cancel();

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run);
        Assert.Equal(cancellation.Token, thrown.CancellationToken);
    }
}
