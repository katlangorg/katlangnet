using System.Numerics;
using System.Text.RegularExpressions;

namespace KatLang.Tests;

/// <summary>
/// X-49 — the Grace movement law (PAR-06, decided 2026-10-08). An owner's OWN inferred parameters
/// start in first semantic occurrence with their exact summed weights; every POSITIVE weight takes
/// one turn, from the last-occurring to the first-occurring, then every NEGATIVE weight, from the
/// first-occurring to the last-occurring; each turn exchanges the mover with its neighbour one unit
/// at a time until its remaining weight is zero, it reaches an end of the own list, or the neighbour
/// moves the same way with at least as much REMAINING weight. A passed name keeps its weight, and
/// weight a name cannot use stays with it and keeps blocking.
/// <para>Two independent levels of checking: the real front end (signatures through
/// <see cref="SourceProvenance.ParseValid"/>, values on the six routes of
/// <see cref="SixRouteAgreement"/>) against <see cref="GraceMovementOracle"/>, which shares no code
/// with <c>GraceMovement</c>. Eligibility and ownership are Q-16 G-O's
/// (<see cref="GraceOwnershipSemanticsTests"/>); this suite pins the ORDER.</para>
/// </summary>
public class GraceMovementLawTests
{
    private static readonly string[] Names = ["a", "b", "c", "d", "e", "f"];

    private const int MainBound = 3;

    // ── helpers ──────────────────────────────────────────────────────────────

    private static string Term(string name, int weight)
        => weight < 0 ? new string('~', -weight) + name : name + new string('~', weight);

    /// <summary><c>K = a~ + ~b + c</c>: every name once, in order, carrying its weight as markers.</summary>
    private static string SumProgram(IReadOnlyList<int> weights, IReadOnlyList<string>? names = null)
    {
        names ??= Names;
        return "K = " + string.Join(" + ", weights.Select((weight, i) => Term(names[i], weight)));
    }

    /// <summary>
    /// <c>K = a~ * 100 + ~b * 10 + c</c>: the same list with place values, so <c>K(1, 2, …, n)</c>
    /// spells the signature in its digits.
    /// </summary>
    private static string WeightedBody(IReadOnlyList<int> weights, IReadOnlyList<string>? names = null)
    {
        names ??= Names;
        return string.Join(" + ", weights.Select((weight, i) =>
        {
            var place = BigInteger.Pow(10, weights.Count - 1 - i);
            return place.IsOne ? Term(names[i], weight) : $"{Term(names[i], weight)} * {place}";
        }));
    }

    private static string Call(string name, int arity)
        => $"{name}({string.Join(", ", Enumerable.Range(1, arity))})";

    private static IReadOnlyList<string> Signature(string source, string property = "K")
        => Assert.Single(SourceProvenance.ParseValid(source).Root.Properties, p => p.Name == property).Value.Params;

    private static int[] Indices(IReadOnlyList<string> signature, IReadOnlyList<string>? names = null)
    {
        names ??= Names;
        return [.. signature.Select(name => names.ToList().IndexOf(name))];
    }

    private static int[] FrontEndOrder(IReadOnlyList<int> weights, IReadOnlyList<string>? names = null)
        => Indices(Signature(SumProgram(weights, names)), names);

    private static async Task<string> ValueOnEveryRoute(string source)
    {
        SourceProvenance.ParseValid(source);
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "ok", $"expected success, got {observation}\nsource:\n{source}");
        return observation.Value!;
    }

    private static IEnumerable<int[]> Vectors(int length, int bound)
    {
        var current = new int[length];
        Array.Fill(current, -bound);
        while (true)
        {
            yield return (int[])current.Clone();
            var position = length - 1;
            while (position >= 0 && current[position] == bound)
            {
                current[position] = -bound;
                position--;
            }

            if (position < 0)
                yield break;
            current[position]++;
        }
    }

    private static IEnumerable<int[]> AllVectors(int maxLength, int bound)
        => Enumerable.Range(1, maxLength).SelectMany(length => Vectors(length, bound));

    private static string Key(IReadOnlyList<int> weights) => string.Join(",", weights);

    private static BigInteger[] Big(IReadOnlyList<int> weights) => [.. weights.Select(static w => new BigInteger(w))];

    /// <summary>
    /// The real front end's order for every MAIN state (1–5 names, weights −3…3: 19,607 parsed
    /// programs), computed once and shared by the exhaustive property tests.
    /// </summary>
    private static readonly Lazy<IReadOnlyDictionary<string, int[]>> MainOrders = new(() =>
    {
        var orders = new Dictionary<string, int[]>();
        foreach (var weights in AllVectors(5, MainBound))
            orders[Key(weights)] = FrontEndOrder(weights);
        return orders;
    });

    private static void AssertNoFailures(List<string> failures, string law)
        => Assert.True(failures.Count == 0, $"{failures.Count} violations of {law}; first: {string.Join(" | ", failures.Take(5))}");

    // ── 1. The canonical examples ────────────────────────────────────────────

    public static TheoryData<string, string, string, string[], string> Canonical() => new()
    {
        // A. Consecutive prefix markers: the front mover (x) clears the way for y.
        { "A", "K = s * 100 + ~x * 10 + ~y", "K(1, 2, 3)", ["x", "y", "s"], "312" },
        // B. Consecutive postfix markers: x (in front) moves first, making room for s.
        { "B", "Z = s~ * 100 + x~ * 10 + y", "Z(1, 2, 3)", ["y", "s", "x"], "231" },
        // C. The original X-49 witness: c, displaced by b, still takes its own turn.
        { "C", "K = a * 100 + b~ * 10 + ~~c", "K(1, 2, 3)", ["c", "a", "b"], "231" },
        // D. Opposing movements, postfix first: a moves right, then c moves left (prefix-first would give (c, a, b)).
        { "D", "K = a~ * 100 + b * 10 + ~c", "K(1, 2, 3)", ["b", "c", "a"], "312" },
        // E. Residual weight: a keeps its unused −1 at the front, and c (−2 → −1 after passing b) cannot pass it.
        { "E", "F = ~a * 100 + b * 10 + ~~c", "F(1, 2, 3)", ["a", "c", "b"], "132" },
        // F. Equal prefix weights at the front: a keeps −1 and blocks b.
        { "F", "K = ~a * 100 + ~b * 10 + c", "K(1, 2, 3)", ["a", "b", "c"], "123" },
        // G. Patent FIG. 12: a's extra unused weight still protects it from b.
        { "G", "SumOfParams = a~~ * 10 + b~", "SumOfParams(1, 2)", ["b", "a"], "21" },
        // H. An extended right-moving group moves as a unit among zero-weight names.
        { "H", "K = a~ * 1000 + b~ * 100 + c~ * 10 + d", "K(1, 2, 3, 4)", ["d", "a", "b", "c"], "2341" },
        // I. An extended left-moving group moves as a unit among zero-weight names.
        { "I", "K = a * 1000 + ~b * 100 + ~c * 10 + ~d", "K(1, 2, 3, 4)", ["b", "c", "d", "a"], "4123" },
        // J. Passive displacement: b, c, d carry e one place left before e takes its own turn.
        { "J", "K = a * 10000 + b~ * 1000 + c~ * 100 + d~ * 10 + ~e", "K(1, 2, 3, 4, 5)", ["e", "a", "b", "c", "d"], "23451" },
    };

    [Theory]
    [MemberData(nameof(Canonical))]
    public async Task CanonicalExample_HasItsSignatureAndValueOnEveryRoute(string id, string definition, string call, string[] signature, string value)
    {
        var property = definition[..definition.IndexOf(' ')];
        Assert.True(signature.SequenceEqual(Signature(definition, property)), $"{id}: {definition}");
        Assert.Equal(value, await ValueOnEveryRoute(definition + "\n" + call));
    }

    [Fact]
    public void PassiveDisplacement_TheUnweightedSpelling()
        => Assert.Equal(["e", "a", "b", "c", "d"], Signature("K = a + b~ + c~ + d~ + ~e"));

    // ── 2. The patent's worked examples (US 9,417,850: FIG. 6, 7, 9–12, 14) ──

    public static TheoryData<string, string, string, string[], string> PatentExamples() => new()
    {
        { "FIG. 6", "PrintName = {\n  lastName * 10\n  ~firstName\n}", "PrintName(1, 2)", ["firstName", "lastName"], "S[20, 1]" },
        { "FIG. 7", "PrintName = {\n  lastName~ * 10\n  firstName\n}", "PrintName(1, 2)", ["firstName", "lastName"], "S[20, 1]" },
        { "FIG. 9", "GetValue = c~~ * 100 - b * 10 + ~a", "GetValue(1, 2, 3)", ["a", "b", "c"], "281" },
        { "FIG. 10", "GetValue = c~ * 100 - b * 10 + ~~a", "GetValue(1, 2, 3)", ["a", "b", "c"], "281" },
        { "FIG. 11", "GetValue = c~~~ * 100 - ~b~ * 10 + ~a", "GetValue(1, 2, 3)", ["a", "b", "c"], "281" },
        { "FIG. 12", "SumOfParams = a~~ * 10 + b~", "SumOfParams(1, 2)", ["b", "a"], "21" },
        { "FIG. 14", "CalculateSomething = b * 100 + c * 10 + ~~a", "CalculateSomething(1, 2, 3)", ["a", "b", "c"], "231" },
    };

    [Theory]
    [MemberData(nameof(PatentExamples))]
    public async Task PatentWorkedExample_KeepsItsOrder(string figure, string definition, string call, string[] signature, string value)
    {
        var property = definition[..definition.IndexOf(' ')];
        Assert.True(signature.SequenceEqual(Signature(definition, property)), $"{figure}: {definition}");
        Assert.Equal(value, await ValueOnEveryRoute(definition + "\n" + call));
    }

    // ── 3. The real front end against the independent oracle ────────────────

    [Fact]
    public void EveryMainState_FrontEndMatchesTheOracle()
    {
        var failures = new List<string>();
        foreach (var (key, order) in MainOrders.Value)
        {
            var weights = key.Split(',').Select(int.Parse).ToArray();
            var expected = GraceMovementOracle.Order(weights);
            if (!expected.SequenceEqual(order))
                failures.Add($"{SumProgram(weights)} → [{string.Join(",", order)}], oracle [{string.Join(",", expected)}]");
        }

        Assert.Equal(19_607, MainOrders.Value.Count);
        AssertNoFailures(failures, "the movement law");
    }

    [Fact]
    public void TheTwoReferenceFormulations_Agree()
    {
        var states = 0;
        foreach (var weights in AllVectors(5, 3).Concat(Vectors(6, 2)))
        {
            states++;
            var big = Big(weights);
            var twoPass = GraceMovementOracle.TwoPass(big);
            var yielding = GraceMovementOracle.SourceOrderWithYielding(big);
            Assert.True(twoPass.Order.SequenceEqual(yielding.Order), $"orders differ for ({Key(weights)})");
            Assert.True(twoPass.Remaining.SequenceEqual(yielding.Remaining), $"leftovers differ for ({Key(weights)})");
        }

        Assert.Equal(19_607 + 15_625, states);
    }

    [Fact]
    public void TheMovementHelper_MatchesTheOracle_OnLargerAndLongerLists()
    {
        // Every 6-name state, weights to ±1000, and long random lists — the helper itself (the front
        // end's use of it is pinned by EveryMainState_FrontEndMatchesTheOracle).
        var random = new Random(49);
        var samples = Vectors(6, 3)
            .Concat(Enumerable.Range(0, 20_000).Select(_ =>
                Enumerable.Range(0, random.Next(1, 7)).Select(_ => random.Next(-1000, 1001)).ToArray()))
            .Concat(Enumerable.Range(0, 20_000).Select(_ =>
                Enumerable.Range(0, random.Next(7, 13)).Select(_ => random.Next(-4, 5)).ToArray()));

        var states = 0;
        foreach (var weights in samples)
        {
            states++;
            var names = Enumerable.Range(0, weights.Length).Select(static i => "p" + i).ToList();
            var settled = GraceMovement.Settle(names, names.Select((name, i) => (name, i)).ToDictionary(t => t.name, t => new BigInteger(weights[t.i])));
            var expected = GraceMovementOracle.SourceOrderWithYielding(Big(weights));
            Assert.True(expected.Order.Select(i => names[i]).SequenceEqual(settled.Order), $"order for ({Key(weights)})");
            // The oracle indexes by original identity; Settle aligns weights to its final order.
            var expectedRemaining = expected.Order.Select(i => expected.Remaining[i]).ToArray();
            Assert.True(expectedRemaining.SequenceEqual(settled.Remaining),
                $"remaining weights for ({Key(weights)}): expected [{string.Join(", ", expectedRemaining)}], " +
                $"actual [{string.Join(", ", settled.Remaining)}]");
        }

        Assert.Equal(117_649 + 40_000, states);
    }

    // ── 4. Monotonicity ──────────────────────────────────────────────────────

    /// <summary>
    /// One more postfix marker never moves its name earlier (one more prefix marker, the same pair read
    /// backwards, never later), and the name never overtakes, in the wrong direction, a name it was
    /// behind. Every single-unit raise of MAIN, crossing zero included.
    /// </summary>
    [Fact]
    public void OneMoreMarker_NeverMovesItsNameTheWrongWay()
    {
        var orders = MainOrders.Value;
        var failures = new List<string>();
        var raises = 0;
        foreach (var (key, before) in orders)
        {
            var weights = key.Split(',').Select(int.Parse).ToArray();
            for (var raised = 0; raised < weights.Length; raised++)
            {
                if (weights[raised] == MainBound)
                    continue;

                var higher = (int[])weights.Clone();
                higher[raised]++;
                var after = orders[Key(higher)];
                raises++;

                var from = Array.IndexOf(before, raised);
                var to = Array.IndexOf(after, raised);
                if (to < from)
                    failures.Add($"({key}) → ({Key(higher)}): name {raised} moved from {from} to {to}");

                foreach (var other in before.Take(from))
                {
                    if (Array.IndexOf(after, other) > to)
                        failures.Add($"({key}) → ({Key(higher)}): name {raised} overtook {other} leftward");
                }
            }
        }

        Assert.Equal(81_234, raises);
        AssertNoFailures(failures, "monotonicity");
    }

    // ── 5. Equal weights ─────────────────────────────────────────────────────

    [Fact]
    public void EqualWeights_KeepTheirFirstOccurrenceOrder()
    {
        var failures = new List<string>();
        var pairs = 0;
        foreach (var (key, order) in MainOrders.Value)
        {
            var weights = key.Split(',').Select(int.Parse).ToArray();
            for (var first = 0; first < weights.Length; first++)
            {
                for (var second = first + 1; second < weights.Length; second++)
                {
                    if (weights[first] != weights[second])
                        continue;
                    pairs++;
                    if (Array.IndexOf(order, first) > Array.IndexOf(order, second))
                        failures.Add($"({key}): {first} and {second}");
                }
            }
        }

        Assert.True(pairs > 10_000);
        AssertNoFailures(failures, "equal-weight order");
    }

    // ── 6. No skipped turns, no movement lost to timing ──────────────────────

    /// <summary>
    /// The helper's own final state: every name left with weight is held by the end it points to or
    /// by a neighbour moving the same way with at least as much remaining weight — so no marked name
    /// lost its turn, and no movement was lost to a blocker that moved later. Every state of 1–6
    /// names with weights −3…3 (137,256).
    /// </summary>
    [Fact]
    public void EveryLeftover_IsHeldByAnEndOrASameDirectionNeighbour()
    {
        var failures = new List<string>();
        var states = 0;
        foreach (var weights in AllVectors(6, MainBound))
        {
            states++;
            var names = Names.Take(weights.Length).ToList();
            var settled = GraceMovement.Settle(names, names.Select((name, i) => (name, i)).ToDictionary(t => t.name, t => new BigInteger(weights[t.i])));
            for (var place = 0; place < weights.Length; place++)
            {
                var left = settled.Remaining[place];
                var held = left.Sign switch
                {
                    > 0 => place == weights.Length - 1 || settled.Remaining[place + 1] >= left,
                    < 0 => place == 0 || settled.Remaining[place - 1] <= left,
                    _ => true,
                };
                if (!held)
                    failures.Add($"({Key(weights)}): {settled.Order[place]} kept {left} at {place} with a free step");
            }

            // Every leftover is a part of the name's own weight, never more and never the other way.
            foreach (var (name, place) in settled.Order.Select((name, place) => (name, place)))
            {
                var initial = weights[Array.IndexOf(Names, name)];
                var left = settled.Remaining[place];
                if (left.Sign * initial < 0 || BigInteger.Abs(left) > Math.Abs(initial))
                    failures.Add($"({Key(weights)}): {name} ends with {left} from {initial}");
            }
        }

        Assert.Equal(137_256, states);
        AssertNoFailures(failures, "final-state blocking");
    }

    // ── 7. Groups ────────────────────────────────────────────────────────────

    /// <summary>
    /// When every name outside a contiguous equal-weight run has zero weight, the run moves as a
    /// unit by that weight (as far as the end allows), in either direction and anywhere in the list.
    /// </summary>
    [Fact]
    public void EquallyMarkedRuns_MoveAsAUnit_WhenEveryOutsideWeightIsZero()
    {
        var cases = 0;
        foreach (var length in Enumerable.Range(2, 5))
        {
            foreach (var start in Enumerable.Range(0, length))
            {
                foreach (var runLength in Enumerable.Range(1, length - start))
                {
                    foreach (var weight in new[] { 1, 2, 0, -1, -2 })
                    {
                        var weights = new int[length];
                        for (var i = start; i < start + runLength; i++)
                            weights[i] = weight;

                        var run = Enumerable.Range(start, runLength).ToList();
                        var rest = Enumerable.Range(0, length).Where(i => i < start || i >= start + runLength).ToList();
                        var before = rest.Count(i => i < start);
                        var shift = weight > 0
                            ? Math.Min(weight, length - (start + runLength))
                            : -Math.Min(-weight, start);
                        var insertAt = before + shift;
                        var expected = rest.Take(insertAt).Concat(run).Concat(rest.Skip(insertAt)).ToArray();

                        cases++;
                        Assert.True(expected.SequenceEqual(FrontEndOrder(weights)), SumProgram(weights));
                    }
                }
            }
        }

        Assert.True(cases > 200);
    }

    [Fact]
    public async Task EqualWeights_PreserveRelativeOrder_ButOtherMoversCanSplitBothRuns()
    {
        const string definition = "K = a~ * 1000 + b~ * 100 + ~c * 10 + ~d";
        var signature = Signature(definition).ToArray();
        Assert.Equal(["c", "a", "d", "b"], signature);
        Assert.Equal("2413", await ValueOnEveryRoute(definition + "\nK(1, 2, 3, 4)"));

        var a = Array.IndexOf(signature, "a");
        var b = Array.IndexOf(signature, "b");
        var c = Array.IndexOf(signature, "c");
        var d = Array.IndexOf(signature, "d");
        Assert.True(a < b);
        Assert.True(c < d);
        Assert.True(b - a > 1);
        Assert.True(d - c > 1);
    }

    public static TheoryData<string, string[]> UnequalGroups() => new()
    {
        // At the ends.
        { "K = a~ * 100 + b~~ * 10 + c", ["c", "a", "b"] },
        { "K = a~~ * 100 + b~ * 10 + c", ["c", "b", "a"] },
        { "K = a * 100 + ~~b * 10 + ~c", ["b", "c", "a"] },
        { "K = a * 100 + ~b * 10 + ~~c", ["c", "b", "a"] },
        // In the middle of a longer list: each mover makes its own moves; a stronger one may pass a
        // weaker one that already moved (c in the second row ends where it started).
        { "K = a + b~ + c~~ + d + e", ["a", "d", "b", "e", "c"] },
        { "K = a + b~~ + c~ + d + e", ["a", "d", "c", "b", "e"] },
        { "K = a + b + ~c + ~~d + e", ["a", "d", "c", "b", "e"] },
        { "K = a + b + ~~c + ~d + e", ["c", "a", "d", "b", "e"] },
    };

    [Theory]
    [MemberData(nameof(UnequalGroups))]
    public void UnequallyMarkedNeighbours_EachMakeTheirOwnMoves(string source, string[] signature)
        => Assert.Equal(signature, Signature(source));

    // ── 8. Exact one-direction recipes ───────────────────────────────────────

    private static IEnumerable<int[]> Permutations(int length)
    {
        if (length == 0)
        {
            yield return [];
            yield break;
        }

        foreach (var shorter in Permutations(length - 1))
        {
            for (var at = 0; at <= shorter.Length; at++)
                yield return [.. shorter.Take(at), length - 1, .. shorter.Skip(at)];
        }
    }

    /// <summary>
    /// Prefix markers alone — one per earlier-written name that must end up after it — give exactly
    /// the intended order; so do postfix markers alone — one per later-written name that must end up
    /// before it. Every permutation of 1–6 names (873), both ways.
    /// </summary>
    [Fact]
    public void OneDirectionMarkings_GiveExactlyTheIntendedOrder()
    {
        var failures = new List<string>();
        var permutations = 0;
        foreach (var length in Enumerable.Range(1, 6))
        {
            foreach (var target in Permutations(length))
            {
                permutations++;
                var position = new int[length];
                for (var place = 0; place < length; place++)
                    position[target[place]] = place;

                var prefixOnly = Enumerable.Range(0, length)
                    .Select(i => -Enumerable.Range(0, i).Count(j => position[j] > position[i])).ToArray();
                var postfixOnly = Enumerable.Range(0, length)
                    .Select(i => Enumerable.Range(i + 1, length - i - 1).Count(j => position[j] < position[i])).ToArray();

                foreach (var weights in new[] { prefixOnly, postfixOnly })
                {
                    if (!target.SequenceEqual(FrontEndOrder(weights)))
                        failures.Add($"{SumProgram(weights)} for [{string.Join(",", target)}]");
                }
            }
        }

        Assert.Equal(873, permutations);
        AssertNoFailures(failures, "the one-direction recipes");
    }

    // ── 9. Residual weights, saturation and cancellation ────────────────────

    public static TheoryData<string, string[]> ResidualWeights() => new()
    {
        // Unused weight at an end stays and blocks an equal or weaker push from behind.
        { "K = ~a * 100 + b * 10 + ~~c", ["a", "c", "b"] },
        { "K = ~a * 100 + ~b * 10 + c", ["a", "b", "c"] },
        { "K = a~ * 10 + b~", ["a", "b"] },
        { "K = a~~ * 10 + b~", ["b", "a"] },
        { "K = a * 100 + b~ * 10 + c~", ["a", "b", "c"] },
        // A stronger push passes it.
        { "K = ~a * 100 + b * 10 + ~~~c", ["c", "a", "b"] },
        // A stronger same-direction mover may push a weaker one back: b moves, then c passes it.
        { "K = a * 100 + ~b * 10 + ~~c", ["c", "b", "a"] },
        // Saturation is never an error: weight beyond the end is kept, not wrapped.
        { "K = a * 100 + b * 10 + ~~~~~c", ["c", "a", "b"] },
        { "K = a~~~~ * 100 + b * 10 + c", ["b", "c", "a"] },
        // Opposite markers cancel before anything moves.
        { "K = a * 10 + ~b~", ["a", "b"] },
        { "K = a * 100 + b * 10 + ~~c~", ["a", "c", "b"] },
        { "K = ~~a~ * 100 + b * 10 + c", ["a", "b", "c"] },
        { "K = a~~ * 100 + ~~b~~ * 10 + c", ["b", "c", "a"] },
    };

    [Theory]
    [MemberData(nameof(ResidualWeights))]
    public void ResidualWeight_SaturationAndCancellation(string source, string[] signature)
        => Assert.Equal(signature, Signature(source));

    public static TheoryData<BigInteger[], string[], BigInteger[]> ExactResiduals() => new()
    {
        { [-1], ["a"], [-1] },
        { [1], ["a"], [1] },
        { [-1, 0, -2], ["a", "c", "b"], [-1, -1, 0] },
        { [0, 0, 0], ["a", "b", "c"], [0, 0, 0] },
        // One exchange consumes exactly one unit, including far beyond the signed 32-bit range.
        { [BigInteger.One << 64, (BigInteger.One << 64) - 1], ["b", "a"],
            [(BigInteger.One << 64) - 1, (BigInteger.One << 64) - 1] },
        { [-(BigInteger.One << 64) + 1, -(BigInteger.One << 64)], ["b", "a"],
            [-(BigInteger.One << 64) + 1, -(BigInteger.One << 64) + 1] },
    };

    [Theory]
    [MemberData(nameof(ExactResiduals))]
    public void Settle_ReturnsExactRemainingWeights_InFinalOrder(
        BigInteger[] weights, string[] order, BigInteger[] remaining)
    {
        var names = Names.Take(weights.Length).ToArray();
        var settled = GraceMovement.Settle(names,
            names.Select((name, i) => (name, i)).ToDictionary(t => t.name, t => weights[t.i]));
        Assert.Equal(order, settled.Order);
        Assert.Equal(remaining, settled.Remaining);
    }

    [Fact]
    public void HostBuiltWeights_CancelExactly_AndRetainExactBoundaryResiduals()
    {
        // A shared host AST contributes 2^64 occurrences, without writing 2^64 source markers.
        var magnitude = BigInteger.One << 64;
        Assert.Equal(["b", "a"], DetectedParams(Diamond(64, Graced("a", 1)),
            Diamond(64, Graced("b", 1)), Graced("b", -1)));
        var settled = GraceMovement.Settle(["a", "b"], new Dictionary<string, BigInteger>
        {
            ["a"] = magnitude,
            ["b"] = magnitude - 1,
        });
        Assert.Equal(["b", "a"], settled.Order);
        Assert.Equal([magnitude - 1, magnitude - 1], settled.Remaining);

        Assert.Equal(["a", "b"], DetectedParams(Diamond(64, Graced("a", 1)),
            Diamond(64, Graced("a", -1)), Graced("b", int.MaxValue, -int.MaxValue)));
        var cancelled = GraceMovement.Settle(["a", "b"], new Dictionary<string, BigInteger>
        {
            ["a"] = magnitude - magnitude,
            ["b"] = new BigInteger(int.MaxValue) - int.MaxValue,
        });
        Assert.Equal(["a", "b"], cancelled.Order);
        Assert.Equal([BigInteger.Zero, BigInteger.Zero], cancelled.Remaining);
    }

    // ── 10. Aggregation over occurrences ─────────────────────────────────────

    public static TheoryData<string, string[]> Aggregation() => new()
    {
        // No single occurrence of b can pass a's −1; their sum (−2) can.
        { "K = ~a * 10 + ~b + ~b", ["b", "a"] },
        { "K = ~a * 10 + ~b", ["a", "b"] },
        // No single occurrence of a can pass b's +1; their sum (+2) can.
        { "K = a~ * 10 + b~ + a~", ["b", "a"] },
        { "K = a~ * 10 + b~", ["a", "b"] },
        // Occurrences that cancel across the body leave the name unmarked.
        { "K = x~ + ~x + y", ["x", "y"] },
        { "K = a * 10 + ~b + b~ + b", ["a", "b"] },
        // Occurrences add up.
        { "K = a + b + ~c + ~c", ["c", "a", "b"] },
        { "K = a~ + a~ + b + c", ["b", "c", "a"] },
        // A grouped occurrence is the occurrence.
        { "K = a + b + (~~c)", ["c", "a", "b"] },
    };

    [Theory]
    [MemberData(nameof(Aggregation))]
    public void Occurrences_AggregateByExactSum(string source, string[] signature)
        => Assert.Equal(signature, Signature(source));

    // ── 11. Exact weights: large values, host-built Grace and shared DAGs ────

    private static Algorithm.User EmptyAlgorithm(params Expr[] output)
        => new(Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: output);

    private static IReadOnlyList<string> DetectedParams(params Expr[] output)
    {
        var (detected, diagnostics) = ParameterDetector.Detect(EmptyAlgorithm(output));
        Assert.Empty(diagnostics);
        return detected.Params;
    }

    private static Expr Graced(string name, params int[] stacked)
        => stacked.Aggregate((Expr)new Expr.Resolve(name), static (inner, weight) => new Expr.Grace(inner, weight));

    /// <summary>A binary diamond: one shared node per level, so the leaf is reached 2^depth times.</summary>
    private static Expr Diamond(int depth, Expr leaf)
    {
        var node = leaf;
        for (var level = 0; level < depth; level++)
            node = new Expr.Binary(BinaryOp.Add, node, node);
        return node;
    }

    [Fact]
    public void Weights_AreExactBeyondTheIntRange()
    {
        // 2^31 against 2^31 − 1: an int-saturated sum would tie them and block.
        Assert.Equal(["b", "a"], DetectedParams(Graced("a", int.MaxValue, 1), Graced("b", int.MaxValue)));
        // −2^31 − 1 against −2^31, leftward.
        Assert.Equal(["b", "a"], DetectedParams(Graced("a", int.MinValue), Graced("b", int.MinValue, -1)));
        // Cancellation near the extremes: (+Max) + (+Max) + (−Max) is +Max, never a clamped zero.
        Assert.Equal(["a", "g"], DetectedParams(
            Graced("g", int.MaxValue), Graced("g", int.MaxValue), Graced("g", -int.MaxValue), new Expr.Resolve("a")));
        // ... and (−Max) + (−Max) + (+Max) is −Max: one place left, never a clamped zero.
        Assert.Equal(["g", "a"], DetectedParams(
            new Expr.Resolve("a"), Graced("g", -int.MaxValue), Graced("g", -int.MaxValue), Graced("g", int.MaxValue)));
    }

    [Fact]
    public void StackedWrappersOnOneOccurrence_CancelExactly()
    {
        // The parser writes one wrapper per occurrence (`~c~` is one weight-0 wrapper); a host-built
        // tree may stack opposite weights on one occurrence, and they cancel before anything moves.
        Assert.Equal(["a", "g"], DetectedParams(new Expr.Resolve("a"), Graced("g", 1, -1)));
        Assert.Equal(["g", "a"], DetectedParams(Graced("g", -1, 1), new Expr.Resolve("a")));
        Assert.Equal(["g", "a"], DetectedParams(new Expr.Resolve("a"), Graced("g", 3, -1, -1, -2)));
    }

    [Fact]
    public void SharedDagWeights_AreExactPerSemanticOccurrence()
    {
        // 2^64 occurrences of +1 against 2^64 − 1: only an exact per-occurrence sum through the
        // detector's shared-node memo lets g pass h.
        Assert.Equal(["h", "g"], DetectedParams(
            Diamond(64, Graced("g", 1)),
            new Expr.Capture(new OutputBundle([Diamond(64, Graced("h", 1)), Graced("h", -1)]))));

        // The memoized DAG and the duplicated tree infer the same order.
        static Expr Tree(int depth, Func<Expr> leaf)
            => depth == 0 ? leaf() : new Expr.Binary(BinaryOp.Add, Tree(depth - 1, leaf), Tree(depth - 1, leaf));
        Assert.Equal(
            DetectedParams(new Expr.Resolve("a"), new Expr.Resolve("b"), Tree(3, () => Graced("c", -1))),
            DetectedParams(new Expr.Resolve("a"), new Expr.Resolve("b"), Diamond(3, Graced("c", -1))));
    }

    [Fact]
    public void LargeSourceWeights_AreExactAndSettleInBoundedWork()
    {
        Assert.Equal(["b", "c", "a"], Signature("K = a" + new string('~', 1000) + " * 100 + b * 10 + c"));
        // 500 prefix and 501 postfix markers net +1.
        Assert.Equal(["a", "c", "b"], Signature("K = a * 100 + " + new string('~', 500) + "b" + new string('~', 501) + " * 10 + c"));

        // An astronomical weight still settles: each turn makes at most n − 1 exchanges.
        var names = Enumerable.Range(0, 200).Select(static i => "p" + i).ToList();
        var weights = new Dictionary<string, BigInteger>
        {
            ["p0"] = BigInteger.Pow(10, 100),
            ["p199"] = -BigInteger.Pow(10, 100),
            ["p100"] = BigInteger.Pow(10, 100) - 1,
        };
        var settled = GraceMovement.Settle(names, weights);
        // p100 reaches the end first; p0 stops behind it, because p100 kept more REMAINING weight
        // (10^100 − 100) than p0 has left when they meet (10^100 − 198); p199 then runs to the front.
        Assert.Equal("p199", settled.Order[0]);
        Assert.Equal(["p0", "p100"], settled.Order[^2..]);
    }

    // ── 12. Owner isolation ──────────────────────────────────────────────────

    public static TheoryData<string, string> OwnerContexts() => new()
    {
        { "property", "K = a * 100 + b~ * 10 + ~~c\nK(1, 2, 3)" },
        { "nested-property", "Outer = {\n  K = a * 100 + b~ * 10 + ~~c\n  K(p, 2, 3)\n}\nOuter(1)" },
        { "block-callback", "Apply(f) = f(1, 2, 3)\nApply({ a * 100 + b~ * 10 + ~~c })" },
        { "block-in-property-row", "Apply(f) = f(1, 2, 3)\nG = Apply({ a * 100 + b~ * 10 + ~~c })\nG" },
        { "branch-local-property", "F(0) = {\n  K = a * 100 + b~ * 10 + ~~c\n  K(1, 2, 3)\n}\nF(0)" },
        { "branch-inline-callback", "Apply(f) = f(1, 2, 3)\nF(0) = Apply({ a * 100 + b~ * 10 + ~~c })\nF(0)" },
        { "block-under-explicit-list", "Apply(f) = f(1, 2, 3)\nF(z) = Apply({ a * 100 + b~ * 10 + ~~c }) + z\nF(0)" },
    };

    [Theory]
    [MemberData(nameof(OwnerContexts))]
    public async Task TheSameOwnList_HasTheSameOrder_InEveryOwner(string context, string source)
        => Assert.True("231" == await ValueOnEveryRoute(source), context);

    [Fact]
    public void TheRootOwner_OrdersItsOwnNamesTheSameWay()
        => Assert.Equal(["c", "a", "b"], SourceProvenance.ParseValid("a * 100 + b~ * 10 + ~~c").Root.Params);

    [Fact]
    public async Task AModuleOwner_OrdersItsOwnNamesTheSameWay()
    {
        const string url = "https://mods.test/x49-front-first.kat";
        ModuleRouteAgreement.Modules Server() => new((url, "public K = a * 100 + b~ * 10 + ~~c"));
        var observation = await ModuleRouteAgreement.OnEveryRouteAsync("M = load('" + url + "')\nM.K(1, 2, 3)", Server);
        Assert.Equal(("ok", "231"), (observation.Kind, observation.Value));
    }

    // ── 13. The lifted tail ──────────────────────────────────────────────────

    public static TheoryData<string, string, string[], string> LiftedTails() => new()
    {
        // The own part moves; the forwarded (p, q) follows it unchanged.
        { "A = p * 10 + q\nK = a * 100 + b~ * 10 + ~~c + A * 1000", "K(1, 2, 3, 4, 5)", ["c", "a", "b", "p", "q"], "45231" },
        // The last own name cannot move into the tail.
        { "A = p * 10 + q\nK = A * 100 + z~", "K(1, 2, 3)", ["z", "p", "q"], "2301" },
        { "A = p * 10 + q\nK = A * 1000 + x~ * 10 + y~", "K(1, 2, 3, 4)", ["x", "y", "p", "q"], "34012" },
        // A prefix marker cannot reach into it either.
        { "A = p * 10 + q\nK = A * 1000 + x * 10 + ~~y", "K(1, 2, 3, 4)", ["y", "x", "p", "q"], "34021" },
    };

    [Theory]
    [MemberData(nameof(LiftedTails))]
    public async Task TheOwnOrder_IsFollowedByTheUnchangedLiftedTail(string definitions, string call, string[] signature, string value)
    {
        Assert.Equal(signature, Signature(definitions));
        Assert.Equal(value, await ValueOnEveryRoute(definitions + "\n" + call));
    }

    // ── 14. Spelling never decides ───────────────────────────────────────────

    [Fact]
    public void Renaming_KeepsThePositionalOrder()
    {
        string[][] spellings = [["a", "b", "c"], ["z", "y", "x"], ["b", "a", "c"], ["c", "a", "b"], ["x1", "Q", "t_2"]];
        foreach (var weights in Vectors(3, MainBound))
        {
            var reference = FrontEndOrder(weights, spellings[0]);
            foreach (var names in spellings.Skip(1))
                Assert.True(reference.SequenceEqual(FrontEndOrder(weights, names)), $"{SumProgram(weights, names)}");
        }
    }

    // ── 15. Grace is only a way of writing the explicit list ─────────────────

    public static IEnumerable<object[]> TwinPrograms()
    {
        foreach (var weights in Vectors(3, 2))
            yield return [Key(weights)];
        foreach (var weights in Vectors(4, 1))
            yield return [Key(weights)];
        yield return ["0,1,1,1,-1"];
        yield return ["2,-1,0,1,-2"];
    }

    [Theory]
    [MemberData(nameof(TwinPrograms))]
    public async Task TheExplicitListTwin_IsIdentical(string key)
    {
        var weights = key.Split(',').Select(int.Parse).ToArray();
        var body = WeightedBody(weights);
        var implicitProgram = "K = " + body;
        var signature = Signature(implicitProgram);
        var twin = $"K({string.Join(", ", signature)}) = {body.Replace("~", "", StringComparison.Ordinal)}";

        Assert.True(GraceMovementOracle.Order(weights).Select(i => Names[i]).SequenceEqual(signature), implicitProgram);
        var call = Call("K", weights.Length);
        Assert.Equal(await ValueOnEveryRoute(twin + "\n" + call), await ValueOnEveryRoute(implicitProgram + "\n" + call));
    }

    // ── 16. The shared Lean table ────────────────────────────────────────────

    /// <summary>
    /// <c>lean/CoreTests/GraceMovement.lean</c> states the law as a Lean model; its
    /// <c>#guard move [w…] == [order…]</c> table is checked by <c>lake build CoreTests</c> AND here,
    /// against the real front end, so the Lean model and the C# implementation cannot drift apart.
    /// </summary>
    [Fact]
    public void TheLeanGuardTable_MatchesTheFrontEnd()
    {
        var path = Path.Combine(RepoRoot.Find(), "lean", "CoreTests", "GraceMovement.lean");
        var rows = Regex.Matches(
            File.ReadAllText(path),
            @"^#guard move \[(?<weights>[-0-9, ]*)\] == \[(?<order>[0-9, ]*)\]\s*$",
            RegexOptions.Multiline);

        static int[] Numbers(string text)
            => text.Length == 0 ? [] : [.. text.Split(',').Select(static part => int.Parse(part.Trim()))];

        Assert.True(rows.Count >= 30, $"only {rows.Count} guard rows found in {path}");
        foreach (Match row in rows)
        {
            var weights = Numbers(row.Groups["weights"].Value);
            var order = Numbers(row.Groups["order"].Value);
            if (weights.Length == 0)
            {
                // An owner with no inferred parameters has no list to order (and no program here).
                Assert.Empty(order);
                continue;
            }

            Assert.True(order.SequenceEqual(FrontEndOrder(weights)), $"{row.Value.Trim()}: front end gives {SumProgram(weights)} → [{string.Join(", ", FrontEndOrder(weights))}]");
        }
    }
}
