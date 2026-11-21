using System.Globalization;
using KatLang.ParserFuzz;
using Xunit.Abstractions;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// The <c>seed-nested-wider</c> recipe (<see cref="SemanticNestedWider"/>, fuzz/README.md § Families and
/// interactions): collectors at every level and in every placement, repeated names in nested positions,
/// spreads in nested data and META parameters over nested patterns. It is FINITE — a stable 8,464
/// distinct programs, one per choice sequence, so <c>--exhaustive</c> applies — every program parses
/// cleanly in every member, every construct is present per kind, a few programs pin what the recipe
/// constructs, and a fixed strided slice runs in process (the full sweep is the nightly job's).
/// </summary>
public class SemanticNestedWiderTests(ITestOutputHelper output)
{
    private const int WiderPrograms = 8_464;

    private static readonly Lazy<SemanticExhaustive.Enumeration> Wider = new(() => SemanticExhaustive.Enumerate(SemanticCorpus.NestedWiderSeedRecipe));

    private static readonly Lazy<SemanticCase[]> Cases = new(() =>
        [.. Wider.Value.Programs.Select(static p => SemanticCorpus.ExhaustiveBuilder(SemanticCorpus.NestedWiderSeedRecipe, p.Choices).Build())]);

    /// <summary>
    /// The recipe is a new id among the seeded and finite recipes (the existing ids keep their place and
    /// meaning), enumerates 8,464 programs from as many choice sequences in depth-first order, and every
    /// seeded case of it (16 seeds × 16 indices) is one of them.
    /// </summary>
    [Fact]
    public void TheWiderRecipe_IsFinite_AndEnumeratesEveryProgramOnce()
    {
        Assert.Equal(["seed", "seed-nested", "seed-nested-wide", "seed-nested-wider"], SemanticCorpus.SeededRecipes.ToArray());
        Assert.Contains(SemanticCorpus.NestedWiderSeedRecipe, SemanticCorpus.FiniteRecipes);
        var enumeration = Wider.Value;
        Assert.Equal((WiderPrograms, WiderPrograms), (enumeration.Sequences, enumeration.Programs.Length));
        Assert.Equal(WiderPrograms, enumeration.Programs.Select(static p => p.CaseId).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal("sem2b/v1/seed-nested-wider/all/0.0.0.0.0.0", enumeration.Programs[0].CaseId);
        Assert.Equal("sem2b/v1/seed-nested-wider/all/4.1.1.1.3.3.1.7", enumeration.Programs[^1].CaseId);

        var bySource = Cases.Value.ToDictionary(static c => c.Source, StringComparer.Ordinal);
        for (var seed = 0x5EED_2B00_0001UL; seed <= 0x5EED_2B00_0010UL; seed++)
        {
            for (var index = 0; index < 16; index++)
            {
                var c = SemanticCorpus.SeededBuilder(SemanticCorpus.NestedWiderSeedRecipe, seed, index).Build();
                Assert.True(bySource.TryGetValue(c.Source, out var enumerated), $"{c.CaseId} is not enumerated:\n{c.Source}");
                Assert.Equal(c.Expected.ToString(), enumerated.Expected.ToString());
                Assert.Equal(c.Features.ToArray(), enumerated.Features.ToArray());
            }
        }
    }

    /// <summary>
    /// Every member of every program — the base source, its alpha-renaming and its declaration reordering —
    /// parses with no error diagnostic: the recipe writes no intended refusal.
    /// </summary>
    [Fact]
    [Trait("Tier", "Slow")]
    public void EveryWiderProgram_ParsesCleanly_InEveryMember()
    {
        var options = new RunOptions { HostOperations = MetamorphicHostFixture.Synchronous().Operations };
        var members = 0;
        foreach (var c in Cases.Value)
        {
            Assert.NotEqual(SemanticCaseKind.InvalidFrontEnd, c.Kind);
            Assert.InRange(c.Members.Length, 2, 3);
            foreach (var member in c.Members)
            {
                var parsed = Parser.Parse(member.Source, options);
                var error = parsed.Diagnostics.FirstOrDefault(static d => d.Severity == DiagnosticSeverity.Error);
                Assert.True(error is null, $"{c.CaseId} {member.Role}: {error?.Code} {error?.Message}\n{member.Source}");
                members++;
            }
        }

        output.WriteLine($"{Cases.Value.Length} programs, {members} members");
    }

    /// <summary>
    /// Every construct the recipe exists for is present, per kind, counted over the whole enumeration:
    /// a collector at each of the three levels in each of the three placements; a repeated name in each of
    /// its three position pairs in each head form, equal and unequal; a spread of each form at each level
    /// that admits it; META over nested patterns — the parameter first and last with each use and the
    /// refused argument, and each operation over a captured nested call. The shape totals, the outcome
    /// kinds and the error categories are pinned.
    /// </summary>
    [Fact]
    public void TheWiderRecipe_WritesEveryConstructPerKind()
    {
        var features = new Dictionary<string, int>(StringComparer.Ordinal);
        var kinds = new Dictionary<SemanticCaseKind, int>();
        var errors = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var c in Cases.Value)
        {
            kinds[c.Kind] = kinds.GetValueOrDefault(c.Kind) + 1;
            foreach (var feature in c.Features) features[feature] = features.GetValueOrDefault(feature) + 1;
            if (c.Expected.ErrorCategory is { } error) errors.Add(error);
        }

        int Count(string feature) => features.GetValueOrDefault(feature);
        int Joint(params string[] all) => Cases.Value.Count(c => all.All(c.Features.Contains));
        foreach (var (key, value) in features.Where(static p => p.Key.StartsWith("wider-", StringComparison.Ordinal)
                     || p.Key.StartsWith("collector-", StringComparison.Ordinal) || p.Key.StartsWith("spread", StringComparison.Ordinal)
                     || p.Key.StartsWith("meta", StringComparison.Ordinal) || p.Key.StartsWith("repeat", StringComparison.Ordinal)).OrderBy(static p => p.Key, StringComparer.Ordinal))
            output.WriteLine($"{key}: {value}");
        output.WriteLine(string.Join(", ", kinds.OrderBy(static p => p.Key).Select(static p => $"{p.Key}={p.Value}")));

        var shapes = SemanticNestedWider.Shapes.Select(s => Count("wider-" + s)).ToArray();
        output.WriteLine("shapes: " + string.Join(", ", shapes));
        Assert.Equal(WiderPrograms, shapes.Sum());
        Assert.Equal([2432, 960, 1872, 1152, 2048], shapes);
        Assert.Equal(WiderPrograms / SemanticGrammar.Contexts.Length, Count("ctx-brace"));

        // Collectors at every level, in every placement (the third level included).
        foreach (var level in new[] { 1, 2, 3 })
            foreach (var at in SemanticNestedWider.Placements)
                Assert.True(Count($"collector-level-{level}-{at}") > 0, $"no collector at level {level} placed {at}");

        // Repeated names: every pair in every head form, equal and unequal.
        Assert.Equal(960, Count("repeated-name"));
        foreach (var form in SemanticNestedWider.HeadForms)
            foreach (var pair in SemanticNestedWider.RepeatPairs)
                foreach (var equality in new[] { "repeat-equal", "repeat-unequal" })
                    Assert.True(Joint("wider-form-" + form, "wider-repeat-" + pair, equality) > 0, $"no {equality} {pair} in a {form} head");
        Assert.True(Count("wider-outcome-catch-all") > 0 && Count("wider-outcome-repeat-differs") > 0);

        // Spreads in nested data: each form, at each level it applies to, with and without one item more.
        foreach (var form in SemanticNestedWider.SpreadForms)
            Assert.True(Count("spread-" + form) > 0, $"no {form} spread");
        foreach (var level in new[] { 1, 2, 3 })
        {
            Assert.True(Joint("spread-whole", "spread-level-" + level.ToString(CultureInfo.InvariantCulture)) > 0, $"no whole spread at level {level}");
            Assert.True(Joint("spread-empty", "spread-level-" + level.ToString(CultureInfo.InvariantCulture)) > 0, $"no empty spread at level {level}");
        }

        Assert.True(Joint("spread-head-pair", "collect") > 0 && Count("wider-mutation-extra-in-spread") > 0);

        // META parameters over nested patterns.
        Assert.Equal(1152 + 2048, Count("meta-over-nested"));
        foreach (var at in new[] { "first", "last" })
            foreach (var use in SemanticNestedWider.MetaUses)
                Assert.True(Joint("meta-at-" + at, "meta-use-" + use) > 0, $"no META parameter {at} with use {use}");
        Assert.True(Joint("meta-refusal", "meta-at-first") > 0 && Joint("meta-refusal", "meta-at-last") > 0);
        foreach (var op in SemanticNestedWider.MetaOps)
            Assert.True(Count("meta-op-" + op) > 0, $"no META operation {op}");

        Assert.Equal(["ArityMismatch", "BadArity", "NotAnAlgorithm", "TypeMismatch"], errors.ToArray());
        Assert.Equal(WiderPrograms, kinds.Values.Sum());
        Assert.False(kinds.ContainsKey(SemanticCaseKind.InvalidFrontEnd));
        Assert.True(Count("three-level") > 0 && Count("async") > 0 && Count("parameter-list") > 0 && Count("clause-family") > 0);
    }

    /// <summary>
    /// What the recipe constructs, pinned on seven programs: collectors at all three levels placed first,
    /// middle and last; a repeated name between a nested list and a plain parameter that differs
    /// (<c>BadArity</c> after both values ran); a repeated name in a three-level clause head that differs,
    /// so the catch-all answers; a leading pair spread with one item more feeding a middle collector; a
    /// META parameter written last whose body invokes it after the structural argument ran and before the
    /// plain one; a refused META argument written after the structure; and fresh and rebuilt calls of a
    /// captured nested call, then one whose deepest structure is a scalar.
    /// </summary>
    [Theory]
    [InlineData("0.1.0.7.0.1.0.0",
        "v8((*v7, [(v1, v2, *v3), *v5, v4], v6)) = [count(v7), v1, v2, count(v3), count(v5), v4, v6]\nv8((trace(1), wait(2), [(trace(3), wait(4), trace(5), wait(6)), trace(7), wait(8), trace(9)], wait(1)))\n997",
        "value ([2, 3, 4, 2, 2, 9, 1], 997)", "trace:1,wait:2,trace:3,wait:4,trace:5,wait:6,trace:7,wait:8,trace:9,wait:1")]
    [InlineData("1.1.0.0.0.1.1.0",
        "v5([v1, *v3, v2], v1) = [v1, count(v3), v2]\nv5([trace(1), wait(2), trace(3), wait(4)], trace(2))\n997",
        "error BadArity", "trace:1,wait:2,trace:3,wait:4,trace:2")]
    [InlineData("1.2.1.1.2.1.0",
        "v5([([v1, v1], v3), v4]) = [1, v1, v3, v4]\nv5(v6) = [0]\nv5([([trace(1), wait(2)], trace(2)), wait(3)])\n997",
        "value ([0], 997)", "trace:1,wait:2,trace:2,wait:3")]
    [InlineData("2.0.0.2.1.1.1.1.0",
        "v5(([v1, *v3, v2], v4)) = [v1, count(v3), v2, v4]\nv5(([(trace(1), wait(2), wait(6))*, trace(3), wait(4)], trace(5)))\n997",
        "value ([1, 3, 4, 5], 997)", "trace:1,wait:2,wait:6,trace:3,wait:4,trace:5")]
    [InlineData("3.1.1.0.1.1.0.0",
        "v1(v2, v3) = v2 + v3\nv10([(v4, *v6, v5), v7], v8, meta v9) = [v9.Invoke(), v4, count(v6), v5, v7, v8]\nv10([(trace(1), wait(2), trace(3), wait(4)), trace(5)], wait(6), v1(trace(7), wait(8)))\n997",
        "value ([15, 1, 2, 4, 5, 6], 997)", "trace:1,wait:2,trace:3,wait:4,trace:5,trace:7,wait:8,wait:6")]
    [InlineData("3.1.0.0.0.0.1.0",
        "v1(v2, v3) = v2 + v3\nv8([v4, v5], v6, meta v7) = [v7.Arguments.count, v4, v5, v6]\nv8([trace(1), wait(2)], trace(3), 5)\n997",
        "error NotAnAlgorithm", "trace:1,wait:2")]
    [InlineData("4.0.1.1.2.3.1.0",
        "v5([(v1, v2, *v3), v4]) = [v1, v2, count(v3), v4]\nv6(meta v7) = v7\nv8 = v6(v5([(trace(1), wait(2), trace(3), wait(4)), trace(5)]))\n[v8.Algorithm([(6, 7, 8, 9), 1]), v8.Algorithm(v8.Arguments*), v8.Algorithm([99, 2])]\n997",
        "error TypeMismatch", "trace:1,wait:2,trace:3,wait:4,trace:5")]
    public void TheWiderRecipe_ConstructsItsExpectationFromTheDemandLaws(string choices, string source, string outcome, string events)
    {
        var id = "sem2b/v1/seed-nested-wider/all/" + choices;
        Assert.Contains(id, Wider.Value.Programs.Select(static p => p.CaseId));
        Assert.True(SemanticCorpus.TryBuilder(id, SemanticRecipe.RecipeVersion, out var builder, out var problem), problem);
        var c = builder.Build();
        Assert.Equal(source, c.Source);
        var e = c.Expected;
        Assert.Equal(outcome, e.Kind switch
        {
            SemanticCaseKind.ValidSuccess => "value " + Render(e.Value!),
            SemanticCaseKind.ValidRuntimeFailure => "error " + e.ErrorCategory,
            _ => $"refusal {e.Diagnostic}/{e.DiagnosticPhase}",
        });
        Assert.Equal(events, string.Join(",", e.Events));
        var result = SemanticRunner.Run(c);
        Assert.True(result.Passed, string.Join("; ", result.Findings));

        static string Render(Result value) => value switch
        {
            Result.Atom atom => atom.Value.ToString(CultureInfo.InvariantCulture),
            Result.ListValue list => "[" + string.Join(", ", list.Items.Select(Render)) + "]",
            Result.SequenceValue sequence => "(" + string.Join(", ", sequence.Items.Select(Render)) + ")",
            _ => throw new ArgumentOutOfRangeException(nameof(value), value, "not a constructed value"),
        };
    }

    /// <summary>
    /// The CI smoke of the recipe: a FIXED strided slice across its whole enumeration (every 53rd program)
    /// runs in process under every profile and passes. The full sweep is <c>semantic-campaign --exhaustive
    /// --recipe seed-nested-wider</c>, run nightly (.github/workflows/semantic-nightly.yml).
    /// </summary>
    [Fact]
    public void AStridedSliceOfTheWiderRecipe_PassesInProcess()
    {
        const int stride = 53;
        var ran = 0;
        for (var i = 0; i < Cases.Value.Length; i += stride)
        {
            var c = Cases.Value[i];
            var result = SemanticRunner.Run(c);
            Assert.True(result.Passed, $"{c.CaseId}: {string.Join("; ", result.Findings.Take(3))}\n{c.Source}");
            ran++;
        }

        Assert.Equal((WiderPrograms + stride - 1) / stride, ran);
        output.WriteLine($"{ran} programs of {WiderPrograms}");
    }
}
