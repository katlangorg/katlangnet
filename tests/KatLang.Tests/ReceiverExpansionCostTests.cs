using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Aggregate cost of continuation-aware receiver expansion across every observer and recomputation, on the production
/// detection and resolution route plus an explicit structural and invocation demand of every declaration (so every
/// reader and walk counted is actually demanded). Counters, never stopwatches. Each positive family is measured at
/// three sizes; doubling the source may at most (about) double every counter. Blocked A1 prefixes separately bound
/// the added expansion work. The bound is the claim, not a fit: the historical
/// candidate without shared divergences and observer precedence grew 3.2–3.7x per doubling on the ring (reads,
/// dependencies) and 4x in certificate work, and 3.1–3.5x in reads on a ring of first expansions that the unfixed
/// front end already handles linearly.
/// </summary>
public sealed class ReceiverExpansionCostTests
{
    private const double LinearGrowth = 2.3;

    internal sealed record Cost(long Reads, long Dependencies, long Auxiliary, long Adapter, long PeakStorage, long WalkSteps, long Verdicts, int Source)
    {
        internal IEnumerable<(string Name, long Value)> Counters()
        {
            yield return (nameof(Reads), Reads);
            yield return (nameof(Dependencies), Dependencies);
            yield return (nameof(Auxiliary), Auxiliary);
            yield return (nameof(Adapter), Adapter);
            yield return (nameof(PeakStorage), PeakStorage);
            yield return (nameof(WalkSteps), WalkSteps);
            yield return (nameof(Verdicts), Verdicts);
        }
    }

    internal static Cost Measure(string source, DiagnosticCode? expectedDiagnostic = null)
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        var operation = StaticStructureAdmission.Create(root).Operation;
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();
        var modules = new ModuleUnits();
        long steps = 0;
        operation.Queries.Observations = observations;
        operation.Queries.ReceiverExpansionWalkStepForTesting = () => steps++;
        // The same admitted operation also supports structural demand before detection. Starting with the readers
        // exposes a shared undecided suffix; detection first can settle other facts and hide that work.
        if (expectedDiagnostic is not null)
            foreach (var property in root.Properties.Where(static p => p.Name!.StartsWith('C')))
                operation.Queries.Get(StaticQueryKey.TargetWalk(operation.Queries.BodyIn(operation.Queries.Root, property.Value), StaticCycleCheck.Formation));
        var detected = ParameterDetector.DetectPrevalidated(root, null, observations, diagnostics, modules, operation);
        if (diagnostics.ReportedErrorCount == 0)
            ImplicitArgumentResolver.ResolvePrevalidated(detected.Root, observations, diagnostics, null, modules, operation);
        if (expectedDiagnostic is { } code)
            Assert.Equal(code, Assert.Single(diagnostics).Code);
        else
            Assert.Empty(diagnostics);
        var queries = operation.Queries;
        DemandDeclarations();
        void DemandDeclarations()
        {
            var q = operation.Queries;
            foreach (var property in q.BodyOf(q.Root).Properties)
            {
                var body = q.BodyIn(q.Root, property.Value);
                q.Get(StaticQueryKey.TargetWalk(body, StaticCycleCheck.Formation));
                q.Get(StaticQueryKey.Project(StaticQueryKind.TargetWalk, body, StaticQueryProjection.InvocationTarget));
                q.Get(StaticQueryKey.Project(StaticQueryKind.TargetWalk, body, StaticQueryProjection.OpenStructure));
            }
        }
        var statistics = queries.Statistics;
        var verdicts = observations.StaticQueryEvaluations
            .Where(static e => e.Key.Projection is StaticQueryProjection.ReceiverExpansionVerdict or StaticQueryProjection.OpenReceiverExpansionVerdict)
            .Sum(static e => e.Value);
        return new(statistics.Reads, statistics.Dependencies, statistics.AuxiliaryWork, statistics.AdapterWork, statistics.PeakStorageUnits,
            steps, verdicts, source.Length);
    }

    /// <summary>A ring of distinct member-path bodies: every return crosses a later expansion. R readers into it.</summary>
    internal static string Ring(int size, int readers = 0)
    {
        var text = new StringBuilder();
        for (var i = 1; i <= size; i++) text.Append($"A{i} = B{i}\nB{i} = {{ public M = C{i % size + 1}\n 0 }}\nC{i} = A{i}.M.abs\n");
        for (var j = 1; j <= readers; j++) text.Append($"D{j} = C1.abs\n");
        return text.Append("7\n").ToString();
    }

    /// <summary>N independent loops, R readers into the first.</summary>
    internal static string Loops(int size, int readers = 0, string? member = null)
    {
        var text = new StringBuilder();
        for (var i = 1; i <= size; i++) text.Append($"A{i} = B{i}\nB{i} = {{ public M = {member ?? "C" + i}\n 0 }}\nC{i} = A{i}.M.abs\n");
        for (var j = 1; j <= readers; j++) text.Append($"D{j} = C1.abs\n");
        return text.Append("7\n").ToString();
    }

    /// <summary>A ring of first expansions, which the first-expansion recipe decides alone.</summary>
    internal static string FirstExpansionRing(int size)
        => string.Concat(Enumerable.Range(1, size).Select(i => $"X{i} = X{i % size + 1}.abs\n")) + "7\n";

    /// <summary>
    /// A member-path chain ending at an undecided input gate in the approved A1 witness. Detection refuses the unit,
    /// but structural demand of each reader must still share the blocked suffix instead of walking it once per reader.
    /// </summary>
    internal static string BlockedChain(int size)
    {
        var text = new StringBuilder(StaticStructureWitnessSources.Cases["A.3.2"] + "\nT = P.R.m\n");
        for (var i = 1; i <= size; i++)
        {
            var next = i < size ? "C" + (i + 1) : "T";
            text.Append($"A{i} = B{i}\nB{i} = {{ public M = {next}\n 0 }}\nC{i} = A{i}.M.abs\n");
        }
        return text.ToString();
    }

    /// <summary>Rows read members through a bare reference chain of length k that ends at a member path; every row read.</summary>
    internal static string BareChain(int size)
    {
        var text = new StringBuilder("B = { public Sub = { public M = 1 } }\nA1 = B.Sub\n");
        for (var j = 2; j <= size; j++) text.Append($"A{j} = A{j - 1}\n");
        for (var i = 1; i <= size; i++) text.Append($"C{i} = A{size}.M.abs\n");
        for (var i = 1; i <= size; i++) text.Append($"C{i}\n");
        return text.ToString();
    }

    /// <summary>Rows read members through a member-path reference chain; every row read.</summary>
    internal static string MemberPathChain(int size)
    {
        var text = new StringBuilder("B = { public S = B\n public M = 1 }\nA1 = B.S\n");
        for (var j = 2; j <= size; j++) text.Append($"A{j} = A{j - 1}.S\n");
        for (var i = 1; i <= size; i++) text.Append($"C{i} = A{size}.M.abs\n");
        for (var i = 1; i <= size; i++) text.Append($"C{i}\n");
        return text.ToString();
    }

    public static TheoryData<string> Families() => new("ring", "ring-readers", "loops", "loops-readers", "first-expansion-ring", "bare-chain", "member-path-chain");

    private static string Source(string family, int size) => family switch
    {
        "ring" => Ring(size),
        "ring-readers" => Ring(16, size),
        "loops" => Loops(size),
        "loops-readers" => Loops(16, size),
        "first-expansion-ring" => FirstExpansionRing(size),
        "bare-chain" => BareChain(size),
        "member-path-chain" => MemberPathChain(size),
        _ => throw new ArgumentOutOfRangeException(nameof(family)),
    };

    [Theory]
    [MemberData(nameof(Families))]
    public void EveryCounterGrowsLinearly(string family)
    {
        var costs = new[] { 16, 32, 64 }.Select(size => Measure(Source(family, size))).ToArray();
        for (var i = 1; i < costs.Length; i++)
        {
            var sourceGrowth = (double)costs[i].Source / costs[i - 1].Source;
            foreach (var ((name, before), (_, after)) in costs[i - 1].Counters().Zip(costs[i].Counters()))
                Assert.True(after <= Math.Max(LinearGrowth, LinearGrowth * sourceGrowth / 2) * Math.Max(before, 64),
                    $"{family}: {name} grew from {before} to {after} while the source grew {sourceGrowth:F2}x\n{string.Join("\n", costs.AsEnumerable())}");
        }
    }

    [Fact]
    public void BlockedSuffixesShareReceiverExpansionWorkBeforeDetection()
    {
        var costs = new[] { 16, 32, 64 }.Select(size => Measure(BlockedChain(size), DiagnosticCode.SelfDependentInferredParameters)).ToArray();
        Assert.All(costs, static cost => Assert.True(cost.WalkSteps > 0 && cost.Verdicts > 0, cost.ToString()));
        // The baseline already has quadratic namespace-certificate work on this rejected A1 unit (10860, 36260,
        // 133908 auxiliary units). Isolate the ADDED expansion work: its walk steps were 1632, 6336, 24960 before
        // blocked prefixes were shared. Adapter work also includes every path push and record update, while the
        // verdict count bounds the memo-hit reads. Existing positive families above still bound EVERY counter.
        for (var i = 1; i < costs.Length; i++)
        {
            Assert.True(costs[i].WalkSteps <= LinearGrowth * costs[i - 1].WalkSteps, string.Join("\n", costs.AsEnumerable()));
            Assert.True(costs[i].Adapter <= LinearGrowth * costs[i - 1].Adapter, string.Join("\n", costs.AsEnumerable()));
            Assert.True(costs[i].Verdicts <= LinearGrowth * costs[i - 1].Verdicts, string.Join("\n", costs.AsEnumerable()));
        }
    }

    /// <summary>The walks were exercised where they should be, and only there.</summary>
    [Fact]
    public void TheVerdictWalksRunExactlyWhereTheSummariesStayUndecided()
    {
        var ring = Measure(Ring(32));
        Assert.True(ring.Verdicts > 0 && ring.WalkSteps > 0, ring.ToString());
        var loops = Measure(Loops(32));
        Assert.True(loops.Verdicts > 0 && loops.WalkSteps > 0, loops.ToString());
        // A constant member ends every walk in its own summary: a verdict read while that summary was still being
        // computed answers No at quiescence without walking. The first-expansion ring never asks at all.
        Assert.Equal(0, Measure(Loops(32, member: "5")).WalkSteps);
        var first = Measure(FirstExpansionRing(64));
        Assert.Equal(0, first.Verdicts);
        Assert.Equal(0, first.WalkSteps);
        // A shared ring costs no more walking than as many independent loops of the same size, within a constant.
        Assert.True(ring.WalkSteps <= 3 * loops.WalkSteps, $"{ring}\n{loops}");
        // Incoming readers reuse the proved divergence: they add no walk length.
        Assert.True(Measure(Ring(16, 64)).WalkSteps <= Measure(Ring(16)).WalkSteps + 4 * 64, "readers");
    }
}
