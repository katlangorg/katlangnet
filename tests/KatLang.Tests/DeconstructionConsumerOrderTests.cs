using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.DeconstructionMemoEligibilityTests;

namespace KatLang.Tests;

/// <summary>
/// OOS-24 (Constitution audit 2026-10-23, snapshot <c>e62e3ac6</c>): the deconstruction group-bind
/// memo was keyed by the READER's binding context, so whether one group bound once or once per consumer
/// depended on which consumer first read a target. The audit's D1-DECON shape
/// <c>[0].map{ n + B }[0] + B.a + B.b</c> itself bound once even then — the callback reads the OWNER
/// <c>B</c>, whose body binds in <c>B</c>'s declaring context, and the member reads inherit that context
/// (CACHE-OWNER-D1). The consumer-order dependence appeared when a callback was the first reader of a
/// TARGET (<c>[0].map{ n + B.a }[0] + B.b + B</c>): two full binds, one extra step and checkpoint (the
/// bind's charged source read), and for a collector one extra materialization. The right-hand side ran
/// once either way, and values, effects and errors were unchanged.
///
/// <para>OD-1 (<c>2144d597</c>) removed every consumer dimension from the key, so the bind is shared by
/// every consumer of one published source entry through one pattern list. This class pins the
/// consumer-order variants of D1-DECON on the generic, optimized and genuinely suspending async routes:
/// the current accounting (identical across consumer orders), the measured audit-snapshot baseline it
/// replaced (identical at <c>852d0b3c</c>, the commit before OD-1), the near-limit verdicts the
/// eliminated work moves, local-activation and exported-source ownership, target calls, a collector,
/// count mismatches, and the Q-37 re-entrant <c>S[3, 3]</c> witness whose unstored nested binds stay.</para>
/// </summary>
public class DeconstructionConsumerOrderTests
{
    private const string BlockHeader = "F(k) = {\n    B = {\n        a, b = trace(k), k + 1\n        a + b\n    }\n    ";

    internal static readonly (string Id, string Source)[] Corpus =
    [
        // The audit's D1-DECON shape: the owner is read from a callback first, then the targets directly.
        ("D1", BlockHeader + "[0].map{ n + B }[0] + B.a + B.b\n}\nF(3)"),
        ("D1-DIRECT-FIRST", BlockHeader + "B.a + B.b + [0].map{ n + B }[0]\n}\nF(3)"),
        ("D1-TARGETS-REVERSED", BlockHeader + "[0].map{ n + B }[0] + B.b + B.a\n}\nF(3)"),
        ("D1-NO-CALLBACK", BlockHeader + "B + B.a + B.b\n}\nF(3)"),
        // A target is the callback's first read: the shape whose accounting depended on consumer order.
        ("T-CB-FIRST", BlockHeader + "[0].map{ n + B.a }[0] + B.b + B\n}\nF(3)"),
        ("T-DIRECT-FIRST", BlockHeader + "B.b + B + [0].map{ n + B.a }[0]\n}\nF(3)"),
        ("T-CB-ONLY", BlockHeader + "[0].map{ n + B.a }[0] + [0].map{ n + B.b }[0]\n}\nF(3)"),
        // Distinct callback, helper and loop consumers inside ONE declaring activation.
        ("REPEATED", BlockHeader + "G(x) = x + B.b\n    Step(s) = s + B.a\n    [0].map{ n + B.a }[0] + [1].map{ n + B.b }[0] + G(B.a) + [2, 3].map{ n + B.b }.sum + Step(0).repeat(2)\n}\nF(3)"),
        // Separate declaring activations of a local-only source: equal arguments, distinct arguments,
        // empty supplies. Each activation binds its own entry once.
        ("ACT-EQUAL", BlockHeader + "[0].map{ n + B.a }[0] + B.b + B\n}\nF(3), F(3)"),
        ("ACT-DISTINCT", BlockHeader + "[0].map{ n + B.a }[0] + B.b + B\n}\nF(3), F(4)"),
        ("ACT-ZERO", "Outer(k) = {\n    F = {\n        a, b = trace(k), k + 1\n        [0].map{ n + a }[0] + b\n    }\n    F() + F() + F\n}\nOuter(3)"),
        // An exported source: one entry per run and declaring scope, read from two activations of G.
        ("EXPORTED", "B = {\n    a, b = trace(1), 2\n    a + b\n}\nG(k) = [0].map{ n + B.a }[0] + B.b + k\nG(1), G(2)"),
        ("TARGET-CALLS", "F(k) = {\n    a, b = trace(k), k + 1\n    [0].map{ n + a() }[0] + a + b() + b\n}\nF(3)"),
        ("COLLECTOR", "F(k) = {\n    h, *t = trace(k), k + 1, k + 2\n    [0].map{ n + t.count }[0] + h + t.count + t().count\n}\nF(3)"),
        // Q-37 / Constitution mechanism note: binds nested in a running bind of their group are never stored.
        ("REENTRANT", "a, b = if(tick() < 3, (a + a, 0), (1, 1))\na, a"),
        // A successful right-hand side, then a count mismatch: the source is evaluated once.
        ("MISMATCH", "F(k) = {\n    a, b = trace(k), k + 1, k + 2\n    [0].map{ n + a }[0] + b\n}\nF(3)"),
        ("MISMATCH-AFTER-READ", "F(k) = {\n    s = trace(k), k + 1, k + 2\n    a, b = s\n    s.count + [0].map{ n + a }[0]\n}\nF(3)"),
    ];

    /// <summary>Value or error kind with host effects, then steps, checkpoints, peak depth, materialized items and full binds.</summary>
    private static readonly Dictionary<string, (string Comparable, long Steps, long Checkpoints, int Depth, long Items, long Binds)> Expected =
        new(StringComparer.Ordinal)
        {
            ["D1"] = ("ok 14 n=1 | t(3)", 11, 42, 7, 4, 1),
            ["D1-DIRECT-FIRST"] = ("ok 14 n=1 | t(3)", 11, 42, 5, 4, 1),
            ["D1-TARGETS-REVERSED"] = ("ok 14 n=1 | t(3)", 11, 42, 7, 4, 1),
            ["D1-NO-CALLBACK"] = ("ok 14 n=1 | t(3)", 10, 29, 6, 2, 1),
            ["T-CB-FIRST"] = ("ok 14 n=1 | t(3)", 11, 42, 6, 4, 1),
            ["T-DIRECT-FIRST"] = ("ok 14 n=1 | t(3)", 11, 42, 5, 4, 1),
            ["T-CB-ONLY"] = ("ok 7 n=1 | t(3)", 9, 45, 6, 6, 1),
            ["REPEATED"] = ("ok 34 n=1 | t(3)", 20, 95, 6, 10, 1),
            ["ACT-EQUAL"] = ("ok S[14, 14] n=2 | t(3),t(3)", 22, 84, 6, 10, 2),
            ["ACT-DISTINCT"] = ("ok S[14, 18] n=2 | t(3),t(4)", 22, 84, 6, 10, 2),
            ["ACT-ZERO"] = ("ok 21 n=1 | t(3),t(3)", 18, 72, 7, 8, 2),
            ["EXPORTED"] = ("ok S[4, 5] n=2 | t(1)", 12, 57, 6, 8, 1),
            ["TARGET-CALLS"] = ("ok 14 n=1 | t(3)", 10, 40, 6, 4, 1),
            ["COLLECTOR"] = ("ok 9 n=1 | t(3)", 11, 50, 6, 7, 1),
            ["REENTRANT"] = ("ok S[3, 3] n=2 | tick#1,tick#2,tick#3,tick#4,tick#5", 21, 77, 10, 12, 5),
            ["MISMATCH"] = ("err ArityMismatch | t(3)", 6, 30, 6, 4, 1),
            ["MISMATCH-AFTER-READ"] = ("err ArityMismatch | t(3)", 8, 34, 6, 4, 1),
        };

    /// <summary>
    /// The audit snapshot <c>e62e3ac6</c> (per-reader key; the same numbers at <c>852d0b3c</c>), measured
    /// on all three routes with the same harness: steps, checkpoints, materialized items, full binds.
    /// Values, effects, errors and peak depth were those of <see cref="Expected"/>.
    /// </summary>
    private static readonly Dictionary<string, (long Steps, long Checkpoints, long Items, long Binds)> AuditSnapshot =
        new(StringComparer.Ordinal)
        {
            ["D1"] = (11, 42, 4, 1),
            ["D1-DIRECT-FIRST"] = (11, 42, 4, 1),
            ["D1-TARGETS-REVERSED"] = (11, 42, 4, 1),
            ["D1-NO-CALLBACK"] = (10, 29, 2, 1),
            ["T-CB-FIRST"] = (12, 43, 4, 2),
            ["T-DIRECT-FIRST"] = (11, 42, 4, 1),
            ["T-CB-ONLY"] = (10, 46, 6, 2),
            ["REPEATED"] = (21, 96, 10, 2),
            ["ACT-EQUAL"] = (24, 86, 10, 4),
            ["ACT-DISTINCT"] = (24, 86, 10, 4),
            ["ACT-ZERO"] = (20, 74, 8, 4),
            ["EXPORTED"] = (13, 58, 8, 2),
            ["TARGET-CALLS"] = (11, 41, 4, 2),
            ["COLLECTOR"] = (13, 52, 9, 3),
            ["REENTRANT"] = (21, 77, 12, 5),
            ["MISMATCH"] = (6, 30, 4, 1),
            ["MISMATCH-AFTER-READ"] = (8, 34, 4, 1),
        };

    public static TheoryData<string, Route> Cases()
    {
        var data = new TheoryData<string, Route>();
        foreach (var (id, _) in Corpus)
            foreach (var route in Enum.GetValues<Route>())
                data.Add(id, route);
        return data;
    }

    private static Expr Program(string id)
        => new Expr.AlgorithmExpr(Parse(Corpus.Single(entry => entry.Id == id).Source));

    [Theory]
    [MemberData(nameof(Cases))]
    public async Task ConsumerOrderVariant_HasItsSharedAccounting(string id, Route route)
    {
        var observed = await Observe(Program(id), route);
        var expected = Expected[id];
        Assert.Equal(
            (expected.Comparable, expected.Steps, expected.Checkpoints, expected.Depth, expected.Items, expected.Binds),
            (observed.Comparable, observed.Steps, observed.Checkpoints, observed.PeakDepth, observed.Materialized, observed.Binds));
    }

    /// <summary>
    /// The OOS-24 question answered: reordering consumers of one source changes no value, effect, bind
    /// count, step, checkpoint or materialized item. Peak depth may differ — the reordered programs nest
    /// their first demand differently, which is ordinary non-memo work.
    /// </summary>
    [Theory]
    [InlineData("D1", "D1-DIRECT-FIRST", Route.Generic)]
    [InlineData("D1", "D1-DIRECT-FIRST", Route.Optimized)]
    [InlineData("D1", "D1-DIRECT-FIRST", Route.SuspendingAsync)]
    [InlineData("D1", "D1-TARGETS-REVERSED", Route.Generic)]
    [InlineData("D1", "D1-TARGETS-REVERSED", Route.Optimized)]
    [InlineData("D1", "D1-TARGETS-REVERSED", Route.SuspendingAsync)]
    [InlineData("T-CB-FIRST", "T-DIRECT-FIRST", Route.Generic)]
    [InlineData("T-CB-FIRST", "T-DIRECT-FIRST", Route.Optimized)]
    [InlineData("T-CB-FIRST", "T-DIRECT-FIRST", Route.SuspendingAsync)]
    [InlineData("T-CB-FIRST", "D1", Route.Generic)]
    [InlineData("T-CB-FIRST", "D1", Route.Optimized)]
    [InlineData("T-CB-FIRST", "D1", Route.SuspendingAsync)]
    public async Task ReorderedConsumers_ShareOneBindAndTheSameCharges(string left, string right, Route route)
    {
        var l = await Observe(Program(left), route);
        var r = await Observe(Program(right), route);
        Assert.Equal(1, l.Binds);
        Assert.Equal((l.Comparable, l.Steps, l.Checkpoints, l.Materialized, l.Binds),
            (r.Comparable, r.Steps, r.Checkpoints, r.Materialized, r.Binds));
    }

    /// <summary>
    /// The accounting change against the audit snapshot is exactly the eliminated binds: each one was a
    /// charged source read (one step, one expression checkpoint). The collector case also avoids one
    /// re-materialized two-item list across its two eliminated binds. Binds never grow; the Q-37
    /// re-entrant witness, single-consumer shapes and the
    /// owner-first D1 shapes are unchanged.
    /// </summary>
    [Fact]
    public void AccountingChangeSinceTheAuditSnapshot_IsExactlyTheEliminatedBinds()
    {
        Assert.Equal(Corpus.Select(entry => entry.Id).Order(StringComparer.Ordinal), Expected.Keys.Order(StringComparer.Ordinal));
        Assert.Equal(Expected.Keys.Order(StringComparer.Ordinal), AuditSnapshot.Keys.Order(StringComparer.Ordinal));
        var reduced = new List<string>();
        foreach (var (id, after) in Expected)
        {
            var before = AuditSnapshot[id];
            var eliminated = before.Binds - after.Binds;
            Assert.True(eliminated >= 0, id);
            if (eliminated > 0)
                reduced.Add(id);
            Assert.Equal(eliminated, before.Steps - after.Steps);
            Assert.Equal(eliminated, before.Checkpoints - after.Checkpoints);
            Assert.Equal(id == "COLLECTOR" ? 2 : 0, before.Items - after.Items);
        }

        Assert.Equal(
            ["ACT-DISTINCT", "ACT-EQUAL", "ACT-ZERO", "COLLECTOR", "EXPORTED", "REPEATED", "T-CB-FIRST", "T-CB-ONLY", "TARGET-CALLS"],
            reduced.Order(StringComparer.Ordinal));
    }

    /// <summary>
    /// Sharing against every helper binding alone (the memo out of the picture, the property cache's law
    /// intact): identical value, emitted count, error text and effects in order; never more binds, steps
    /// or items. The RHS trace count is pinned separately from the bind count.
    /// </summary>
    [Theory]
    [MemberData(nameof(Cases))]
    public async Task ConsumerOrderVariant_MatchesItsUnsharedBindExecution(string id, Route route)
    {
        var program = Program(id);
        var shared = await Observe(program, route);
        var unshared = await Observe(program, route, shareBinds: false);
        Assert.Equal(unshared.Outcome + " | " + unshared.Effects, shared.Outcome + " | " + shared.Effects);
        Assert.True(shared.Binds <= unshared.Binds, $"{shared} vs {unshared}");
        Assert.True(shared.Steps <= unshared.Steps, $"{shared} vs {unshared}");
        Assert.True(shared.Checkpoints <= unshared.Checkpoints, $"{shared} vs {unshared}");
        Assert.True(shared.Materialized <= unshared.Materialized, $"{shared} vs {unshared}");
    }

    /// <summary>
    /// Near-limit verdicts. T-CB-FIRST completes at <c>MaxSteps = 11</c> (the per-reader key needed 12)
    /// and still refuses at 10, at the same span as before; the unshared control still needs 12. The
    /// collector completes at <c>MaxMaterializedItems = 7</c> (formerly 9) and <c>MaxSteps = 11</c>
    /// (formerly 13), and still refuses one below each. A refusal is never a partial value.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task EliminatedBinds_MoveOnlyTheNearLimitVerdicts(Route route)
    {
        var targetFirst = Program("T-CB-FIRST");
        Assert.Equal("ok 14 n=1 | t(3)", (await Observe(targetFirst, route, new EvaluationLimits { MaxSteps = 11 })).Comparable);
        var refused = await Observe(targetFirst, route, new EvaluationLimits { MaxSteps = 10 });
        Assert.StartsWith("err EvaluationStepLimitExceeded:", refused.Outcome);
        Assert.EndsWith("@ [3:12, 3:13)", refused.Outcome);
        Assert.StartsWith("err EvaluationStepLimitExceeded:", (await Observe(targetFirst, route, new EvaluationLimits { MaxSteps = 11 }, shareBinds: false)).Outcome);
        Assert.Equal("ok 14 n=1 | t(3)", (await Observe(targetFirst, route, new EvaluationLimits { MaxSteps = 12 }, shareBinds: false)).Comparable);
        var directFirst = Program("T-DIRECT-FIRST");
        Assert.Equal("ok 14 n=1 | t(3)", (await Observe(directFirst, route, new EvaluationLimits { MaxSteps = 11 })).Comparable);
        Assert.StartsWith("err EvaluationStepLimitExceeded:", (await Observe(directFirst, route, new EvaluationLimits { MaxSteps = 10 })).Outcome);

        var collector = Program("COLLECTOR");
        Assert.Equal("ok 9 n=1 | t(3)", (await Observe(collector, route, new EvaluationLimits { MaxMaterializedItems = 7 })).Comparable);
        Assert.StartsWith("err MaterializationLimitExceeded:", (await Observe(collector, route, new EvaluationLimits { MaxMaterializedItems = 6 })).Outcome);
        Assert.Equal("ok 9 n=1 | t(3)", (await Observe(collector, route, new EvaluationLimits { MaxSteps = 11 })).Comparable);
        Assert.StartsWith("err EvaluationStepLimitExceeded:", (await Observe(collector, route, new EvaluationLimits { MaxSteps = 10 })).Outcome);
        Assert.StartsWith("err MaterializationLimitExceeded:", (await Observe(collector, route, new EvaluationLimits { MaxMaterializedItems = 8 }, shareBinds: false)).Outcome);
    }

    /// <summary>
    /// Inspect cache state after the program's bind failure rather than trying to continue the program:
    /// both the named RHS and the synthetic shared source retain their successful values, while the
    /// failed target publishes nothing and every active owner is released.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task BindMismatch_KeepsTheSuccessfulSharedSource(Route route)
    {
        var root = Parse("s = trace(3), 4, 5\na, b = s\na");
        var sink = new RootPropertyObservationSink(root);
        var cache = new RunScopedAsyncZeroArgPropertyResultCache(sink);
        var traces = 0;
        Result Trace(Result value) { traces++; return value; }
        EvalResult<Evaluator.CountedResult> result;
        if (route == Route.SuspendingAsync)
        {
            var operations = HostOperations.Create(HostOperation.CreateAsync("trace",
                async (args, _) => { await Task.Yield(); return Trace(args[0]); }, "x"));
            (result, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                new Expr.AlgorithmExpr(root), zeroArgPropertyResultCache: cache, hostOperations: operations));
        }
        else
        {
            var operations = HostOperations.Create(HostOperation.Create("trace", (args, _) => Trace(args[0]), "x"));
            (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(root),
                enableOptimizations: route == Route.Optimized, zeroArgPropertyResultCache: cache, hostOperations: operations);
        }

        Assert.True(result.IsError);
        Assert.Equal(KatLangErrorCode.ArityMismatch, KatLangError.FromEvalError(result.Error).Code);
        Assert.Equal(1, traces);
        Assert.Equal(2, cache.PublishedCount); // s and the synthetic source; no failed-target entry.
        Assert.Equal(0, cache.ActiveOwnerCount);
        var published = Assert.Single(sink.Complete());
        Assert.Equal("s", published.Name);
        Assert.Equal(PropertyValueStatus.Available, published.Status);
        Assert.Equal("S[3, 4, 5]", SixRouteAgreement.Neutral(published.Value!));
    }

    /// <summary>
    /// The re-entrant publication guard. The Constitution's witness keeps <c>S[3, 3]</c> (an unsafe memo
    /// gives <c>S[4, 4]</c>) with five binds — the binds started inside a running bind of the group stay
    /// unstored — on every route, shared or not, and at its exact step and item thresholds.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task ReentrantWitness_KeepsItsUnstoredNestedBinds(Route route)
    {
        var program = Program("REENTRANT");
        var shared = await Observe(program, route);
        var unshared = await Observe(program, route, shareBinds: false);
        Assert.Equal("ok S[3, 3] n=2 | tick#1,tick#2,tick#3,tick#4,tick#5", shared.Comparable);
        Assert.Equal(shared.Comparable, unshared.Comparable);
        Assert.Equal(5, shared.Binds);
        Assert.Equal(unshared.Binds, shared.Binds);
        Assert.Equal(unshared.Steps, shared.Steps);
        Assert.Equal(shared.Comparable, (await Observe(program, route, new EvaluationLimits { MaxSteps = 21 })).Comparable);
        Assert.StartsWith("err EvaluationStepLimitExceeded:", (await Observe(program, route, new EvaluationLimits { MaxSteps = 20 })).Outcome);
        Assert.Equal(shared.Comparable, (await Observe(program, route, new EvaluationLimits { MaxMaterializedItems = 12 })).Comparable);
        Assert.StartsWith("err MaterializationLimitExceeded:", (await Observe(program, route, new EvaluationLimits { MaxMaterializedItems = 11 })).Outcome);
    }

    /// <summary>
    /// One parsed tree run repeatedly and interleaved across routes keeps its per-run accounting: no
    /// bind, source entry or collector completion survives into the next run.
    /// </summary>
    [Fact]
    public async Task ReusedParsedTree_StartsEveryRunWithoutPriorBinds()
    {
        var program = Program("COLLECTOR");
        var expected = Expected["COLLECTOR"];
        foreach (var route in (Route[])[Route.Generic, Route.SuspendingAsync, Route.Optimized, Route.Generic])
        {
            var observed = await Observe(program, route);
            Assert.Equal((expected.Comparable, expected.Steps, expected.Items, expected.Binds),
                (observed.Comparable, observed.Steps, observed.Materialized, observed.Binds));
        }
    }
}
