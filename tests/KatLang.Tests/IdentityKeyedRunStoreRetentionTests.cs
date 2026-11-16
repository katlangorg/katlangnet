using System.Diagnostics;
using System.Globalization;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// IDENTITY-KEYED RUN STORES OUTSIDE THE CACHES (identity-store retention audit, 2026-11-16; a C#-only storage
/// policy, no Lean counterpart: it changes no hit, miss, publication, charge, diagnostic, plan or value). Two
/// run-scoped stores kept one entry per call until the run ended, because a key held an identity that dies
/// with the call:
/// <list type="bullet">
/// <item>the J7 per-site analysis memos (<see cref="EvaluationBudget.CalleeTransportedNames"/>,
/// <see cref="EvaluationBudget.CalleeBuiltinSlotSummaries"/>, <see cref="EvaluationBudget.TransportedNames"/>) under a
/// FLAT-BINDER family, which dispatches through a fresh user equivalent with a fresh parameter-pattern list per
/// call: about 0.7 KB per call (756 MB live at 10⁶ calls, measured in Release);</item>
/// <item>the per-plan supply-formation witness of an OBSERVED run (<see cref="EvaluationObservations"/>), which kept
/// every plan — its caller context, values and supply — alive: about 1.4 KB per round of a META loop.</item>
/// </list>
/// Both now keep an entry only while its identity object is reachable (<see cref="PartitionedMap{TKey, TValue}"/>,
/// prompt reclamation). The tests read the live partitions after a forced full collection while the run's store is
/// still held, the monotonic counts an unpartitioned store reports, a control whose identities stay reachable, and
/// the routes that read the stores across activations: every call of one WRITTEN callee shares its entry for the
/// run, and a call reference re-entering a returned activation still reads its plan's witness.
/// </summary>
public sealed class IdentityKeyedRunStoreRetentionTests(ITestOutputHelper output)
{
    private const int Calls = 20_000;
    private const int MaxLivePartitions = 64;

    // ── J7 per-site callee memos ───────────────────────────────────────────────────────

    /// <summary>
    /// A loop-only program (per-site retention) whose callee <c>F</c> is replaced, host-built, by a single-clause
    /// flat-binder family <c>F(a, b)</c>. Its user equivalent is minted per call, so its memo key is new on every call.
    /// The B9 variant transports both parameters into a value-only builtin, so the builtin-aware summary memo is
    /// exercised too.
    /// </summary>
    internal static string PerSiteProgram(string body, int calls)
        => "Inc(y) = y + 1\nF(a, b) = " + body + "\nStep(n) = F(Inc(n), Inc(0)) - 1\nStep(0).repeat("
            + calls.ToString(CultureInfo.InvariantCulture) + ")";

    public static TheoryData<string, bool> FlatBinderShapes => new()
    {
        { "a + b", true },
        { "a + b", false },
        { "if(a > b, a, b) + 1", true },
        { "if(a > b, a, b) + 1", false },
    };

    [Theory]
    [MemberData(nameof(FlatBinderShapes))]
    public void PerSiteCalleeMemo_FlatBinderViewsOfFinishedCalls_AreNotRetained(string body, bool optimized)
    {
        if (ForcedInvocationPlansHook.Forced) return; // no per-site run, no memo

        var (value, budget) = RunPerSite(FlatBinderRoot(PerSiteProgram(body, Calls)), optimized);
        ForceFullCollection();

        var names = budget.CalleeTransportedNames;
        var summaries = budget.CalleeBuiltinSlotSummaries;
        output.WriteLine($"{body} optimized={optimized}: callee names added {names.AddedCount}, live {names.LivePartitionCount()}; "
            + $"summaries added {summaries.AddedCount}, live {summaries.LivePartitionCount()}; node memo {budget.TransportedNames.Count}");
        Assert.Equal(Calls.ToString(CultureInfo.InvariantCulture), value);
        Assert.True(budget.UsesPerSiteInvocationPlans);
        // The count an unpartitioned memo reports: one miss per call (its second slot hits), never more.
        Assert.Equal(Calls, names.AddedCount);
        Assert.InRange(names.LivePartitionCount(), 0, MaxLivePartitions);
        // A user callee's entry is never run-wide: it follows its pattern list.
        Assert.Empty(names.RunWideValues);
        if (body.StartsWith("if", StringComparison.Ordinal))
        {
            Assert.Equal(Calls, summaries.AddedCount);
            Assert.InRange(summaries.LivePartitionCount(), 0, MaxLivePartitions);
            Assert.Empty(summaries.RunWideValues);
        }

        // The node memo holds program nodes only: it does not grow with the calls.
        var (_, small) = RunPerSite(FlatBinderRoot(PerSiteProgram(body, 100)), optimized);
        Assert.Equal(small.TransportedNames.Count, budget.TransportedNames.Count);
        Assert.Equal(small.BuiltinSlotSummaries.Count, budget.BuiltinSlotSummaries.Count);
        GC.KeepAlive(budget);
    }

    /// <summary>
    /// The route that reads the memo across activations: every call of a WRITTEN callee wires a fresh record over
    /// the same body lists and shares ONE entry for the run — its parameter-pattern list belongs to the program, so
    /// its partition stays alive while the program does, through a full collection.
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void PerSiteCalleeMemo_AWrittenCallee_SharesOneEntryForTheRun(bool optimized)
    {
        if (ForcedInvocationPlansHook.Forced) return;

        var root = SourceProvenance.ParseValid(PerSiteProgram("if(a > b, a, b) + 1", Calls)).Root;
        var (value, budget) = RunPerSite(root, optimized);
        ForceFullCollection();

        Assert.Equal(Calls.ToString(CultureInfo.InvariantCulture), value);
        Assert.Equal(1, budget.CalleeTransportedNames.AddedCount);
        Assert.Equal(1, budget.CalleeTransportedNames.LivePartitionCount());
        Assert.Equal(1, budget.CalleeBuiltinSlotSummaries.AddedCount);
        Assert.Equal(1, budget.CalleeBuiltinSlotSummaries.LivePartitionCount());
        GC.KeepAlive(root);
        GC.KeepAlive(budget);
    }

    /// <summary>
    /// The storage change decides nothing: the per-site classification of each call-shaped argument — the plans a
    /// run forms — is exactly what it was before (measured on the library before the change, 2026-11-16: the same
    /// counts on the planned and generic routes), and so is the value, on the planned, generic and async-twin
    /// routes. The written user twin forms only the loop's captured step plan. The flat-binder family keeps both
    /// arguments ordinary for <c>a + b</c>; for <c>if(a &gt; b, a, b) + 1</c> it plans both (its clause binders are
    /// not parameter captures of the clause body, so the program's inherited-read names include them — a
    /// conservative classification that predates this change and that the memo's storage cannot alter).
    /// </summary>
    [Theory]
    [InlineData("a + b", 0)]
    [InlineData("if(a > b, a, b) + 1", 2)]
    public async Task PerSiteClassification_IsUnchangedByTheMemoStorage_OnEveryRoute(string body, int flatPlansPerCall)
    {
        if (ForcedInvocationPlansHook.Forced) return;

        const int calls = 300;
        var source = PerSiteProgram(body, calls);
        var written = SourceProvenance.ParseValid(source).Root;
        foreach (var route in new[] { "planned", "generic", "async" })
        {
            var flat = await Observe(FlatBinderRoot(source), route);
            var twin = await Observe(written, route);
            output.WriteLine($"{route}: flat {flat}, written {twin}");
            Assert.Equal($"{calls} plans={1 + flatPlansPerCall * calls}", flat);
            Assert.Equal($"{calls} plans=1", twin);
        }
    }

    /// <summary>The partition law of the callee memos: a dead view's list frees its entry; a live list keeps it.</summary>
    [Fact]
    public void CalleeMemo_KeepsAnEntryWhileItsPatternListIsReachable_AndCountsMonotonically()
    {
        var budget = EvaluationBudget.Create(null);
        var memo = budget.CalleeTransportedNames;
        var rows = new List<Expr>();
        var properties = new List<Property>();
        var opens = new List<Expr>();
        IReadOnlyList<ParameterPattern> kept = [new CaptureParameterPattern("x")];
        var names = Evaluator.TransportedNamesOf(new Expr.Num(1), budget);
        var keptKey = new Evaluator.CalleeBodyKey(rows, properties, opens, kept);
        Assert.True(memo.TryAdd(keptKey, names));
        Assert.False(memo.TryAdd(new Evaluator.CalleeBodyKey(rows, properties, opens, kept), names));
        // A family's key has no pattern list: it is stored for the run.
        var familyKey = new Evaluator.CalleeBodyKey(new List<CondBranch>(), opens, null, null);
        Assert.True(memo.TryAdd(familyKey, names));

        AddUnderFreshPatternLists(memo, rows, properties, opens, names, count: 500);
        ForceFullCollection();

        Assert.Equal(502, memo.AddedCount);
        Assert.Equal(1, memo.LivePartitionCount());
        Assert.True(memo.TryGetValue(new Evaluator.CalleeBodyKey(rows, properties, opens, kept), out _));
        Assert.True(memo.TryGetValue(familyKey, out _));
        Assert.False(memo.TryGetValue(new Evaluator.CalleeBodyKey(rows, properties, opens, new List<ParameterPattern> { new CaptureParameterPattern("x") }), out _));
        GC.KeepAlive(kept);
        GC.KeepAlive(budget);
    }

    // ── The observed plan-formation witness ───────────────────────────────────────────

    /// <summary>
    /// A META loop whose rounds each capture, invoke and drop a call reference (full plan retention), observed: the
    /// witnesses of the dropped plans are gone after a forced full collection, while the counts are exact.
    /// </summary>
    [Theory]
    [InlineData("Cap(meta r) = r\nInc(y) = y + 1\nStep(n) = { R = Cap(Inc(n))\n n + 1 + R.Invoke() * 0 }\nStep(0).repeat({N})", true)]
    [InlineData("Cap(meta r) = r\nInc(y) = y + 1\nStep(n) = { R = Cap(Inc(n))\n n + 1 + R.Invoke() * 0 }\nStep(0).repeat({N})", false)]
    [InlineData("Cap(meta r) = r\nInc(y) = y + 1\nUse(r, n) = n + 1 + r.Invoke() * 0\nStep(n) = Use(Cap(Inc(n)), n)\nStep(0).repeat({N})", true)]
    public void ObservedRun_TheWitnessesOfDroppedPlans_AreNotRetained(string template, bool optimized)
    {
        var source = template.Replace("{N}", Calls.ToString(CultureInfo.InvariantCulture), StringComparison.Ordinal);
        var observations = new EvaluationObservations();
        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), enableOptimizations: optimized, observations: observations);
        ForceFullCollection();

        output.WriteLine($"plans {observations.InvocationPlanCount}, formations {observations.PlanSupplyFormationCount}, "
            + $"live witnesses {observations.LivePlanSupplyWitnessCount()}");
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(Calls.ToString(CultureInfo.InvariantCulture), SixRouteAgreement.Neutral(result.Value.Value));
        Assert.True(budget.RetainsInvocationPlans);
        // Every captured plan forms its supply exactly once.
        Assert.True(observations.InvocationPlanCount >= Calls, $"plans {observations.InvocationPlanCount}");
        Assert.Equal(observations.InvocationPlanCount, observations.PlanSupplyFormationCount);
        Assert.InRange(observations.LivePlanSupplyWitnessCount(), 0, MaxLivePartitions);
        GC.KeepAlive(observations);
    }

    /// <summary>
    /// The control and the re-entry route: references a META receiver keeps (the first <c>held</c> rounds' calls)
    /// stay reachable, so their witnesses survive a full collection, and a later receiver re-enters each of their
    /// returned activations twice: each plan still reads ONE formation (its supply is formed once and reused), and
    /// the re-entry yields the round's value. The other rounds' references are dropped, and so are their witnesses.
    /// </summary>
    [Fact]
    public void ObservedRun_AReferenceReenteringItsReturnedActivation_KeepsItsWitness()
    {
        const int held = 10;
        const int rounds = 2_000;
        var kept = new List<Result.CallReference>();
        var liveBeforeReentry = -1;
        var liveAfterReentry = -1;
        var observations = new EvaluationObservations();
        var operations = HostOperations.Create(
            HostOperation.Create("Keep", (_, _) => throw new InvalidOperationException("META receiver reached as a host operation"), "c"),
            HostOperation.Create("Replay", (_, _) => throw new InvalidOperationException("META receiver reached as a host operation"), "c"));
        var receivers = new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Keep"] = cells =>
            {
                var reference = Reify(cells[0]);
                var value = reference.Invoke();
                Assert.True(value.IsOk, value.IsError ? value.Error.ToString() : "");
                if (kept.Count < held)
                    kept.Add(reference);
                return new Result.Atom(0);
            },
            ["Replay"] = _ =>
            {
                ForceFullCollection();
                liveBeforeReentry = observations.LivePlanSupplyWitnessCount();
                var sum = 0;
                foreach (var reference in kept)
                {
                    Assert.Equal(1, reference.Plan.SupplyFormations);
                    var first = reference.Invoke();
                    var second = reference.Invoke();
                    Assert.True(first.IsOk && second.IsOk);
                    Assert.Equal(1, reference.Plan.SupplyFormations);
                    sum += (int)(decimal)((Result.Atom)first.Value.Value).Value + (int)(decimal)((Result.Atom)second.Value.Value).Value;
                }
                ForceFullCollection();
                liveAfterReentry = observations.LivePlanSupplyWitnessCount();
                return new Result.Atom(sum);
            },
        };

        var source = "Inc(y) = y + 1\nF(x) = { V = x + 1\n Keep(Inc(V)) }\nStep(n) = n + 1 + F(n) * 0\n"
            + $"S = Step(0).repeat({rounds})\nS, Replay(0)";
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        using var seam = InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam(receivers));
        var (result, _) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(parsed.Root), observations: observations, hostOperations: operations);

        output.WriteLine($"live witnesses before re-entry {liveBeforeReentry}, after {liveAfterReentry}, formations {observations.PlanSupplyFormationCount}");
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        // Round x (0-based) keeps Inc(V) = x + 2; each of the first ten is invoked twice: 2 * (2 + … + 11).
        Assert.Equal($"S[{rounds}, 130]", SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(held, kept.Count);
        Assert.InRange(liveBeforeReentry, held, held + MaxLivePartitions);
        Assert.InRange(liveAfterReentry, held, held + MaxLivePartitions);
        Assert.True(observations.PlanSupplyFormationCount >= rounds, $"formations {observations.PlanSupplyFormationCount}");
        GC.KeepAlive(kept);
    }

    // ── Helpers ─────────────────────────────────────────────────────────────────────────

    /// <summary>The program with its property <c>F</c> replaced by a single-clause flat-binder family over <c>F</c>'s rows.</summary>
    internal static Algorithm.User FlatBinderRoot(string source)
        => FlatBinderRoot(SourceProvenance.ParseValid(source).Root);

    internal static Algorithm.User FlatBinderRoot(Algorithm.User root)
    {
        var properties = root.Properties.Select(static property =>
        {
            if (property.Name != "F")
                return property;
            var written = Assert.IsType<Algorithm.User>(property.Value);
            var family = new Algorithm.Conditional(null, [],
                [new CondBranch(new Pattern.SequenceValue([new Pattern.Bind("a"), new Pattern.Bind("b")]),
                    new Algorithm.User(null, [], [], [], written.Output))]);
            return property with { Value = family };
        }).ToList();
        return root with { Properties = properties };
    }

    private static (string Value, EvaluationBudget Budget) RunPerSite(Algorithm.User root, bool optimized)
    {
        var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(root), enableOptimizations: optimized);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        return (SixRouteAgreement.Neutral(result.Value.Value), budget);
    }

    private static async Task<string> Observe(Algorithm.User root, string route)
    {
        var observations = new EvaluationObservations();
        var (result, budget) = route == "async"
            ? await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(root), observations: observations)
            : Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(root), enableOptimizations: route == "planned", observations: observations);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.True(budget.UsesPerSiteInvocationPlans);
        return $"{SixRouteAgreement.Neutral(result.Value.Value)} plans={observations.InvocationPlanCount}";
    }

    private static Result.CallReference Reify(NeedCell? cell)
    {
        var reified = Evaluator.ReifyMeta(cell);
        Assert.True(reified.IsOk, reified.IsError ? reified.Error.ToString() : null);
        return reified.Value;
    }

    // A separate frame, so no fresh pattern list stays reachable from the asserting method's locals.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static void AddUnderFreshPatternLists(
        PartitionedMap<Evaluator.CalleeBodyKey, Evaluator.TransportNames> memo,
        object rows, object properties, object opens, Evaluator.TransportNames names, int count)
    {
        for (var index = 0; index < count; index++)
            Assert.True(memo.TryAdd(new Evaluator.CalleeBodyKey(rows, properties, opens, new List<ParameterPattern>()), names));
    }

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }
}

/// <summary>
/// The peak-memory guards of the two stores <see cref="IdentityKeyedRunStoreRetentionTests"/> pins: each program
/// runs in a fresh <see cref="SubprocessProbe"/> child, which reports its peak working set, and the parent compares
/// 10⁵ with 10⁶ rounds. Measured in Release before the change: the host-built flat-binder per-site loop 137 → 959 MB
/// (756 MB live at the end), the observed META loop 203 → 1,489 MB; both now stay flat.
/// </summary>
public sealed class IdentityKeyedRunStorePeakMemoryProcessTests(ITestOutputHelper output)
{
    private const string Child = "KATLANG_IDENTITY_STORE_PEAK_CHILD";
    private const string Variant = "KATLANG_IDENTITY_STORE_PEAK_VARIANT";
    private const string Rounds = "KATLANG_IDENTITY_STORE_PEAK_ROUNDS";
    private const string Marker = "KATLANG_IDENTITY_STORE_PEAK_MARKER";
    private const int FewRounds = 100_000;
    private const int ManyRounds = 1_000_000;
    private const long AllowedGrowthBytes = 40L * 1024 * 1024;

    [Theory]
    [InlineData("flat-binder-per-site")]
    [InlineData("flat-binder-builtin-per-site")]
    [InlineData("observed-meta")]
    public async Task PeakWorkingSet_StaysWithinFortyMiB_FromTenToTheFifthToTenToTheSixthRounds(string variant)
    {
        if (ForcedInvocationPlansHook.Forced && variant != "observed-meta") return; // no per-site run

        var few = await PeakWorkingSetAsync(variant, FewRounds);
        var many = await PeakWorkingSetAsync(variant, ManyRounds);
        var summary = $"{variant}: peak working set {few / 1048576.0:F1} MiB at {FewRounds} rounds, "
            + $"{many / 1048576.0:F1} MiB at {ManyRounds} rounds";
        output.WriteLine(summary);
        Assert.True(many - few < AllowedGrowthBytes, summary);
    }

    [Fact]
    public void PeakChild()
    {
        if (Environment.GetEnvironmentVariable(Child) != "1")
            return;

        var rounds = int.Parse(Environment.GetEnvironmentVariable(Rounds)!, CultureInfo.InvariantCulture);
        EvalResult<Result> result;
        switch (Environment.GetEnvironmentVariable(Variant))
        {
            case "flat-binder-per-site":
                // The public host-AST entry: a host-built single-clause flat-binder family in a loop-only program.
                result = Evaluator.Run(new Expr.AlgorithmExpr(IdentityKeyedRunStoreRetentionTests.FlatBinderRoot(
                    IdentityKeyedRunStoreRetentionTests.PerSiteProgram("a + b", rounds))));
                break;
            case "flat-binder-builtin-per-site":
            {
                // Reach the second callee memo as well: both captured names enter if's value slots.
                var (counted, budget) = Evaluator.RunCountedObserved(
                    new Expr.AlgorithmExpr(IdentityKeyedRunStoreRetentionTests.FlatBinderRoot(
                        IdentityKeyedRunStoreRetentionTests.PerSiteProgram("if(a > b, a, b) + 1", rounds))));
                Assert.True(budget.UsesPerSiteInvocationPlans);
                Assert.Equal(rounds, budget.CalleeBuiltinSlotSummaries.AddedCount);
                result = counted.IsOk ? EvalResult<Result>.Ok(counted.Value.Value) : counted.Error;
                break;
            }
            case "observed-meta":
            {
                // Each round hands a fresh call reference to another call, which invokes and drops it.
                var source = "Cap(meta r) = r\nInc(y) = y + 1\nUse(r, n) = n + 1 + r.Invoke() * 0\nStep(n) = Use(Cap(Inc(n)), n)\n"
                    + $"Step(0).repeat({rounds.ToString(CultureInfo.InvariantCulture)})";
                var (counted, _) = Evaluator.RunCountedObserved(
                    new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), observations: new EvaluationObservations());
                result = counted.IsOk ? EvalResult<Result>.Ok(counted.Value.Value) : counted.Error;
                break;
            }
            default:
                throw new ArgumentOutOfRangeException(Variant);
        }

        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(rounds.ToString(CultureInfo.InvariantCulture), SixRouteAgreement.Neutral(result.Value));

        using var process = Process.GetCurrentProcess();
        process.Refresh();
        File.WriteAllText(
            Environment.GetEnvironmentVariable(Marker)!,
            process.PeakWorkingSet64.ToString(CultureInfo.InvariantCulture));
    }

    private static async Task<long> PeakWorkingSetAsync(string variant, int rounds)
    {
        var marker = Path.Combine(Path.GetTempPath(), $"katlang-identity-store-peak-{Guid.NewGuid():N}.txt");
        var start = SubprocessProbe.StartInfo(typeof(IdentityKeyedRunStorePeakMemoryProcessTests), nameof(PeakChild));
        start.Environment[Child] = "1";
        start.Environment[Variant] = variant;
        start.Environment[Rounds] = rounds.ToString(CultureInfo.InvariantCulture);
        start.Environment[Marker] = marker;
        try
        {
            using var process = Process.Start(start)!;
            var output = process.StandardOutput.ReadToEndAsync();
            var error = process.StandardError.ReadToEndAsync();
            await process.WaitForExitAsync();
            var text = await output + await error;
            Assert.True(process.ExitCode == 0, text);
            Assert.True(File.Exists(marker), text);
            return long.Parse(await File.ReadAllTextAsync(marker), CultureInfo.InvariantCulture);
        }
        finally
        {
            File.Delete(marker);
        }
    }
}
