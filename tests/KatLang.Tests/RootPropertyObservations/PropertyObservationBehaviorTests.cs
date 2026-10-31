using static KatLang.Tests.RootPropertyObservations.PropertyObservationTestSupport;

namespace KatLang.Tests.RootPropertyObservations;

/// <summary>
/// IV-1 (owner decisions D0(A), D1(A), D2(A), October 21 2026): with
/// <see cref="RunOptions.ObservePropertyValues"/> the run exposes exactly the entries its
/// zero-argument property cache PUBLISHED for source-declared root properties (the Q-37 outermost
/// successful property-style read), in publication order, as an immutable snapshot on
/// <see cref="RunResult.PropertyObservations"/>. Observation never evaluates anything: an unused
/// property has no record, a re-entrant completion or an explicit call publishes nothing, and an
/// <see cref="RunResult.EvalFailure"/> keeps what was published before the failure.
/// </summary>
public class PropertyObservationBehaviorTests
{
    private const string Brief = """
        Price = 200
        VAT = Price * 0.21
        Total = Price + VAT
        Unused = 6 * 7
        Total
        """;

    // ── 1. Basic publication behavior ────────────────────────────────────────────────────────

    [Fact]
    public void BriefExample_ObservesThePublishedChainInPublicationOrder_AndNotTheUnusedProperty()
    {
        var result = Run(Brief);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal("242.00", success.ToDisplayString());
        Assert.Equal("Price=200#1; VAT=42.00#1; Total=242.00#1", Describe(result));
        Assert.DoesNotContain(result.PropertyObservations!, o => o.Name == "Unused");
        Assert.All(result.PropertyObservations!, o => Assert.Equal(PropertyValueStatus.Available, o.Status));
    }

    [Fact]
    public void ObservedValue_IsThePublishedValueItself()
    {
        // `Total` is the program output: the output value and the observed value are the one
        // published result, not a separately calculated approximation.
        var result = Assert.IsType<RunResult.Success>(Run(Brief));
        Assert.Same(result.Value, Single(result, "Total").Value);
    }

    [Fact]
    public void RepeatedReads_ProduceOneObservation()
    {
        var log = new TickLog();
        var result = Run("A = tock()\nA + A + A", log.Operations());

        Assert.Equal("0", result.ToDisplayString());
        Assert.Equal("A=0#1", Describe(result));
        Assert.Equal(["tock:0"], log.Calls);
    }

    [Fact]
    public void EmittedCount_DistinguishesTwoRowsFromOneSequenceRow()
    {
        var result = Run("P = 1, 2\nQ = (1, 2)\nP\nQ");

        var p = Single(result, "P");
        var q = Single(result, "Q");
        Assert.Equal(2, p.EmittedCount);
        Assert.Equal(1, q.EmittedCount);
        Assert.True(Result.ValueComparer.Equals(p.Value, q.Value));
        Assert.Equal("1" + Environment.NewLine + "2", result.RenderPropertyValue(p).Text);
        Assert.Equal("(1, 2)", result.RenderPropertyValue(q).Text);
    }

    [Fact]
    public void CollectingOnlyProperty_ReadWithZeroSupply_IsObserved()
    {
        var result = Run("Only(*xs) = 7\nOnly");
        Assert.Equal("Only=7#1", Describe(result));
    }

    [Fact]
    public void StaticAlias_IsObservedOnlyThroughItsTarget()
    {
        // M4★ OD-E: `B = A` is a transparent reference that owns no entry, so reading B publishes — and
        // observes — A only (formerly "A=5#1; B=5#1"); nothing fakes an entry for the alias.
        var result = Run("A = 5\nB = A\nB");
        Assert.Equal("A=5#1", Describe(result));

        // A calculation over A is a property of its own: two observations, two declarations.
        var computed = Run("A = 5\nB = A + 0\nB");
        Assert.Equal("A=5#1; B=5#1", Describe(computed));
        Assert.NotEqual(Single(computed, "A").DeclarationSpan, Single(computed, "B").DeclarationSpan);
    }

    [Fact]
    public void DisplayDecimals_ReadByTheEngine_IsObservedAfterTheOutput_AndFiltersRendering()
    {
        var result = Run("X = 1 / 3\nDisplayDecimals = 2\nX");

        Assert.Equal("0.33", result.ToDisplayString());
        Assert.Equal("X=0.33#1; DisplayDecimals=2#1", Describe(result));
    }

    [Fact]
    public void HostDisplayFilter_AppliesToObservedValues_AndWithHostDisplayDecimalsSharesTheSnapshot()
    {
        var options = new RunOptions { ObservePropertyValues = true, DefaultDisplayDecimals = 1 };
        var result = KatLangEngine.Run("X = 1 / 3\nX", options);
        Assert.Equal("0.3", result.RenderPropertyValue(Single(result, "X")).Text);

        var widened = result.WithHostDisplayDecimals(4);
        Assert.Same(result.PropertyObservations, widened.PropertyObservations);
        Assert.Equal("0.3333", widened.RenderPropertyValue(Single(widened, "X")).Text);
    }

    [Fact]
    public void LazyBranch_LeavesTheUnselectedPropertyUnevaluatedAndUnobserved()
    {
        var log = new TickLog();
        var result = Run("Cheap = 1\nExpensive = tock()\nif(Cheap == 1, Cheap, Expensive)", log.Operations());

        Assert.Equal("Cheap=1#1", Describe(result));
        Assert.Empty(log.Calls);
    }

    [Fact]
    public void RootPropertyRead_FromALoopStep_IsObservedOnce()
    {
        var result = Run("Rate = 2\nStep(s) = s * Rate\nStep(1).repeat(3)");

        Assert.Equal("8", result.ToDisplayString());
        Assert.Equal("Rate=2#1", Describe(result));
    }

    [Fact]
    public void ParameterizedFunctionResult_IsObservedThroughItsPropertyOnly()
    {
        var result = Run("F(0) = 1\nF(n) = n * F(n - 1)\nG = F(5)\nG");
        Assert.Equal("G=120#1", Describe(result));
    }

    // ── 2. Q-37 publication versus successful completion ────────────────────────────────────

    [Fact]
    public void ReentrantCompletions_AreNotObserved_OnlyTheOwnersPublication()
    {
        // The reviewed Q-37 example: re-entrant reads complete A as 0, 1, 2 (each returned to
        // its caller and used), and the outermost owner publishes 3. Only that publication is an
        // observation (D0(A)).
        var log = new TickLog();
        var result = Run("A = if(tock() < 3, A + 1, 0)\nA", log.Operations());

        Assert.Equal("3", result.ToDisplayString());
        Assert.Equal("A=3#1", Describe(result));
        Assert.Equal(["tock:0", "tock:1", "tock:2", "tock:3"], log.Calls);
    }

    [Fact]
    public void SuccessfulInnerCompletion_UnderAFailingOwner_ProducesNoObservation()
    {
        // tock 0 < 1 takes the A / 0 branch; the inner, re-entrant A completes successfully as 1
        // (tock 1), then the owner divides by zero. Nothing is published, so nothing is observed,
        // although a successful calculation of A did complete.
        var log = new TickLog();
        var result = Run("A = if(tock() < 1, A / 0, 1)\nA", log.Operations());

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Equal(KatLangErrorCode.DivisionByZero, Assert.Single(failure.Errors).Code);
        Assert.Empty(result.PropertyObservations!);
        Assert.Equal(["tock:0", "tock:1"], log.Calls);
    }

    // ── 3. Explicit calls ───────────────────────────────────────────────────────────────────

    // CACHE-PUB-1 (owner decision 2026-10-22): an explicit zero-supply call that finds the entry empty
    // ESTABLISHES it through the one publication hook, so it is observed exactly like a read's
    // publication (formerly an explicit-call-only program had no observation).
    [Fact]
    public void ExplicitCallOnly_IsObserved_AsTheEstablishedValue()
    {
        var log = new TickLog();
        var result = Run("A = tock()\nA()", log.Operations());

        Assert.Equal("0", result.ToDisplayString());
        Assert.Equal("A=0#1", Describe(result));
        Assert.Equal(["tock:0"], log.Calls);
    }

    [Fact]
    public void MixedExplicitAndPropertyReads_ObserveTheEstablishedValue_NotTheLatestCall()
    {
        var log = new TickLog();
        var result = Run("A = tock()\nA() + A + A()", log.Operations());

        // A() = 0 (establishes the entry), A = 0 (reused), A() = 1 (fresh; replaces nothing and adds
        // no observation). Formerly A() = 0, A = 1 (published), A() = 2.
        Assert.Equal("1", result.ToDisplayString());
        Assert.Equal("A=0#1", Describe(result));
        Assert.Equal(["tock:0", "tock:1"], log.Calls);
    }

    [Fact]
    public void LaterExplicitCall_AddsNoObservation_AndNeverReplacesTheEstablishedValue()
    {
        var log = new TickLog();
        var result = Run("A = tock()\nA, A(), A(), A", log.Operations());

        Assert.Equal("0\n1\n2\n0", result.ToDisplayString().ReplaceLineEndings("\n"));
        Assert.Equal("A=0#1", Describe(result));
        Assert.Equal(["tock:0", "tock:1", "tock:2"], log.Calls);
    }

    // ── 4. Partial observations on failure (D1(A)) ──────────────────────────────────────────

    [Fact]
    public void EvalFailure_KeepsEarlierPublications_AndItsErrorsUnchanged()
    {
        const string source = "B = 2\nA = 1 / 0\nB + A";
        var unobserved = KatLangEngine.Run(source);
        var result = Run(source);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Equal(Outcome(unobserved), Outcome(result));
        Assert.Equal(
            ((RunResult.EvalFailure)unobserved).Errors.Select(static e => e.ToString()),
            failure.Errors.Select(static e => e.ToString()));
        Assert.Equal(KatLangErrorCode.DivisionByZero, Assert.Single(failure.Errors).Code);
        Assert.Equal("B=2#1", Describe(result));
        Assert.Null(unobserved.PropertyObservations);
    }

    [Fact]
    public void EvalFailure_EvaluatesNothingAfterTheFailure()
    {
        var log = new TickLog();
        var result = Run("Before = tock()\nBoom = 1 / 0\nAfter = tock()\nBefore + Boom + After", log.Operations());

        Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Equal("Before=0#1", Describe(result));
        Assert.Equal(["tock:0"], log.Calls);
    }

    [Fact]
    public void StepLimitFailure_KeepsThePublicationsBeforeTheLimit()
    {
        var options = new RunOptions
        {
            ObservePropertyValues = true,
            EvaluationLimits = new EvaluationLimits { MaxSteps = 200 },
        };
        const string source = "Step(s) = s + 1\nSmall = 1 + 1\nBig = Step(0).repeat(5000)\nSmall + Big";
        AssertLegal(source);
        var result = KatLangEngine.Run(source, options);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, Assert.Single(failure.Errors).Code);
        Assert.Equal("Small=2#1", Describe(result));
    }

    [Fact]
    public void InvalidDisplayDecimals_FailsTheRun_WithTheObservedValuesBeforeIt()
    {
        var result = Run("X = 1\nDisplayDecimals = 0.5\nX");

        Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Equal("X=1#1; DisplayDecimals=0.5#1", Describe(result));
    }

    // ── 5. Null / empty contract ─────────────────────────────────────────────────────────────

    [Fact]
    public void ObservationDisabled_IsTheDefault_AndYieldsNullOnEveryVariant()
    {
        Assert.False(new RunOptions().ObservePropertyValues);
        foreach (var source in new[] { "1", "A = 1\n", "1 / 0", "1 +" })
        {
            Assert.Null(KatLangEngine.Run(source).PropertyObservations);
            Assert.Null(KatLangEngine.Run(source, new RunOptions()).PropertyObservations);
        }
    }

    [Fact]
    public void ObservationEnabled_NullOnlyForParseFailure()
    {
        var options = Options(observe: true);

        Assert.Null(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("1 +", options)).PropertyObservations);

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("1 + 2", options));
        Assert.NotNull(success.PropertyObservations);
        Assert.Empty(success.PropertyObservations);

        var noOutput = Assert.IsType<RunResult.NoProgramOutput>(KatLangEngine.Run("A = 1\nB = A\n", options));
        Assert.NotNull(noOutput.PropertyObservations);
        Assert.Empty(noOutput.PropertyObservations);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("1 / 0", options));
        Assert.NotNull(failure.PropertyObservations);
        Assert.Empty(failure.PropertyObservations);
    }

    // ── 6. Sync / async engine parity ───────────────────────────────────────────────────────

    public static TheoryData<string> ParitySources => new()
    {
        Brief,
        "A = if(tock() < 3, A + 1, 0)\nA",
        "A = tock()\nA() + A + A()",
        "B = 2\nA = 1 / 0\nB + A",
        "x, y = 1, 2\nx + y",
        "P = 1, 2\nQ = trace(P.count)\nQ, P",
        "X = 1 / 3\nDisplayDecimals = 2\nX",
        "Rate = 2\nStep(s) = s * Rate\nStep(trace(1)).repeat(3)",
        "Total = range(1, 50).filter{n mod 3 == 0}.count\nTotal",
    };

    [Theory]
    [MemberData(nameof(ParitySources))]
    public async Task EngineRoutes_AgreeOnTheSnapshot(string source)
    {
        var syncLog = new TickLog();
        var asyncLog = new TickLog();
        var suspendingLog = new TickLog();

        var sync = Run(source, syncLog.Operations());
        var asynchronous = await RunAsync(source, asyncLog.Operations());
        var suspending = await RunAsync(source, suspendingLog.Operations(suspending: true));

        Assert.Equal(Outcome(sync), Outcome(asynchronous));
        Assert.Equal(Outcome(sync), Outcome(suspending));
        Assert.Equal(Describe(sync), Describe(asynchronous));
        Assert.Equal(Describe(sync), Describe(suspending));
        Assert.Equal(sync.PropertyObservations!.Select(o => o.DeclarationSpan), suspending.PropertyObservations!.Select(o => o.DeclarationSpan));
        Assert.Equal(syncLog.Calls, asyncLog.Calls);
        Assert.Equal(syncLog.Calls, suspendingLog.Calls);
    }
}
