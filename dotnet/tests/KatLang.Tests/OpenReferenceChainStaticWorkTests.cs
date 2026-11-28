namespace KatLang.Tests;

/// <summary>
/// THE FRONT END'S STATIC WORK ON LONG OPEN-REFERENCE CHAINS (November 2026, from the open-chain investigation over
/// <c>19c4fcd8</c>; <c>docs/design/static-structure-resolver-2026-10.md</c> § 3, <i>Open-reference chains</i>).
/// <para><c>katlang check</c> of an N-link chain <c>A0 = Lib</c>, <c>A1 = A0</c>, …, opened as <c>open AN</c>, took
/// superlinear time (2.6 s at 5,000 links, 6.8 s at 10,000) although every count of the static work below was already
/// linear: the static query engine cleared one shared read set before every computation, and that set kept the
/// capacity of the widest computation so far, a namespace certificate that reads every link
/// (<c>StaticQueryEngineTests.EachComputationRecordsItsDistinctReads_AfterAComputationAsWideAsTheSolve</c>).</para>
/// <para>Each further bare link shares its direct open head and immediate open row target across strata.
/// Structure still checks the target cycles of the requesting stratum. The per-link costs include those gates
/// and, under a root open, the opened-name search reached while the lexical binding is still unknown.</para>
/// </summary>
public sealed class OpenReferenceChainStaticWorkTests
{
    private const string Library = "Lib = {\n  public X = 7\n  public Sub = {\n    public Y = 8\n  }\n}\n";

    private static string NameChain(string head, int length, string target)
        => $"{head}0 = {target}\n" + string.Concat(Enumerable.Range(1, length).Select(i => $"{head}{i} = {head}{i - 1}\n"));

    private static string MemberChain(int length)
        => "L = {\n  public X = 5\n  public S = L\n}\nM0 = L\n" + string.Concat(Enumerable.Range(1, length).Select(i => $"M{i} = M{i - 1}.S\n"));

    private static string Cycle(int length)
        => $"A0 = A{length}\n" + string.Concat(Enumerable.Range(1, length).Select(i => $"A{i} = A{i - 1}\n"));

    /// <summary>
    /// The compared families. Beside the settled chain, two levels keep a still-deferred provider: "verdict" opens a
    /// target on a ring of member-path bodies, so the level's member index waits for an open receiver-expansion verdict,
    /// and in "self-dependent" the provider <c>R = C</c> is a reference only if C has no input, which depends on whether
    /// the level's own opens provide <c>q</c>, so its names read presence witnesses.
    /// </summary>
    private static string Source(string family, int n) => family switch
    {
        "root-open" => $"open A{n}\n" + Library + NameChain("A", n, "Lib") + "X\n",
        "body-open" => Library + NameChain("A", n, "Lib") + $"Use = {{\n  open A{n}\n  X\n}}\nUse\n",
        "dot" => Library + NameChain("A", n, "Lib") + $"A{n}.X\n",
        "dotted-open" => Library + NameChain("A", n, "Lib") + $"Use = {{\n  open A{n}.Sub\n  Y\n}}\nUse\n",
        "member-path-open" => Library + NameChain("A", n, "Lib") + $"S = A{n}.Sub\nUse = {{\n  open S\n  Y + 1\n}}\nUse\n",
        "member-steps" => MemberChain(n) + $"Use = {{\n  open M{n}\n  X\n}}\nUse\n",
        "member-steps-dot" => MemberChain(n) + $"M{n}.X\n",
        "shared-suffix" => Library + NameChain("A", n, "Lib") + NameChain("B", n, $"A{n / 2}")
            + $"U = {{\n  open A{n}\n  V = {{\n    open B{n}\n    X\n  }}\n  V + X\n}}\nU\n",
        "ambiguous" => Library + "Lib2 = {\n  public X = 70\n}\n" + NameChain("A", n, "Lib") + NameChain("D", n, "Lib2")
            + $"Use = {{\n  open A{n}, D{n}\n  X\n}}\nUse\n",
        "cycle" => Library + Cycle(n) + $"Use = {{\n  open A{n}\n  X\n}}\nUse\n",
        "verdict" => Library + NameChain("A", n, "Lib")
            + "A1x = B1\nB1 = { public M = C2\n 0 }\nC1 = A1x.M.abs\nA2x = B2\nB2 = { public M = C1\n 0 }\nC2 = A2x.M.abs\nP3 = C1\n"
            + $"Use = {{\n  open A{n}, P3\n  X\n}}\nUse\n",
        "self-dependent" => Library + NameChain("A", n, "Lib") + "L = {\n  public q = 5\n}\n"
            + $"P = {{\n  open A{n}, R\n  public R = C\n  C = {{ open L\n  public W = 9\n  q }}\n  q + X + W\n}}\nP(1)\n",
        _ => throw new ArgumentOutOfRangeException(nameof(family), family, null),
    };

    private sealed record Work(long Keys, long Evaluations, long ConsumerReads, Dictionary<StaticQueryKind, int> KeysByFamily, string Diagnostics);

    private static Work Observe(string family, int n)
    {
        var observations = new FrontEndTraversalObservations();
        var parsed = Parser.ParseObserved(Source(family, n), null, observations);
        return new(observations.StaticQueryEvaluations.Count, observations.StaticQueryEvaluationCount, observations.StaticQueryReads,
            observations.StaticQueryEvaluations.Keys.GroupBy(key => key.Kind).ToDictionary(group => group.Key, group => group.Count()),
            string.Join(", ", parsed.Diagnostics.Select(diagnostic => diagnostic.Code)));
    }

    [Theory]
    [InlineData("root-open", "")]
    [InlineData("body-open", "")]
    [InlineData("dot", "")]
    [InlineData("dotted-open", "")]
    [InlineData("member-path-open", "")]
    [InlineData("member-steps", "")]
    [InlineData("member-steps-dot", "")]
    [InlineData("shared-suffix", "")]
    [InlineData("ambiguous", "AmbiguousOpen")]
    [InlineData("cycle", "")]
    [InlineData("verdict", "")]
    [InlineData("self-dependent", "")]
    public void EveryFurtherLink_AddsTheSameStaticWork(string family, string diagnostics)
    {
        const int step = 64;
        var work = new[] { Observe(family, step), Observe(family, 2 * step), Observe(family, 3 * step) };

        Assert.All(work, observed => Assert.Equal(diagnostics, observed.Diagnostics));
        Assert.Equal(work[1].Keys - work[0].Keys, work[2].Keys - work[1].Keys);
        Assert.Equal(work[1].Evaluations - work[0].Evaluations, work[2].Evaluations - work[1].Evaluations);
        Assert.Equal(work[1].ConsumerReads - work[0].ConsumerReads, work[2].ConsumerReads - work[1].ConsumerReads);
    }

    [Fact]
    public void RootOpen_UsesTheSameEntryLimitAfterSharing()
    {
        var options = new RunOptions { SourceProcessingLimits = new() { MaxStaticStructureBytes = 1024 * 1024 } };
        Assert.Empty(Parser.Parse(Source("root-open", 16), options).Diagnostics);
        var refused = Parser.Parse(Source("root-open", 17), options);
        var diagnostic = Assert.Single(refused.Diagnostics);
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, diagnostic.Code);
        Assert.Contains("entry bound (1024)", diagnostic.Message, StringComparison.Ordinal);
        Assert.Null(refused.Root.CompletedStructure);
    }

    /// <summary>Per-link keys of Q1 (bindings), Q2 (open providers), Q3 (target walks), Q4 (members), Q6 and Q7 (inputs).</summary>
    [Theory]
    [InlineData("root-open", 51, 27, 0, 17, 1, 5, 1)]
    [InlineData("body-open", 36, 12, 0, 17, 1, 5, 1)]
    [InlineData("dot", 34, 12, 0, 15, 1, 5, 1)]
    public void ABareChainLink_CostsTheseKeys_ByQueryFamily(string family, int total, int bindings, int providers, int walks, int members, int input, int inputs)
    {
        const int step = 100;
        var shorter = Observe(family, step);
        var longer = Observe(family, 2 * step);

        int Added(StaticQueryKind kind) => longer.KeysByFamily.GetValueOrDefault(kind) - shorter.KeysByFamily.GetValueOrDefault(kind);
        Assert.Equal(total * step, longer.Keys - shorter.Keys);
        Assert.Equal(
            (bindings * step, providers * step, walks * step, members * step, 0, input * step, inputs * step),
            (Added(StaticQueryKind.Binding), Added(StaticQueryKind.OpenProviders), Added(StaticQueryKind.TargetWalk),
                Added(StaticQueryKind.Members), Added(StaticQueryKind.MissSelection), Added(StaticQueryKind.IsInput), Added(StaticQueryKind.Inputs)));
    }
}
