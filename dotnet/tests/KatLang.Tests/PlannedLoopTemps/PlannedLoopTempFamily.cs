using System.Globalization;
using System.Text;

namespace KatLang.Tests;

/// <summary>
/// The PLANNED-LOOP TEMPORARY generator family (KL-06 F01 follow-up, § 7 of the 2026-11-20 C#/Lean
/// differential bug hunt): a small deterministic family of <c>repeat</c> and <c>while</c> steps whose
/// zero-argument step properties ("temps") cover the four kinds the follow-up names, with result,
/// effect and publication expectations CONSTRUCTED here from the approved rule, never observed from
/// a run.
///
/// <para><b>The step.</b> Every case declares the same four temps in one step
/// <c>Step(n, acc)</c>:</para>
/// <list type="bullet">
/// <item><c>T = n * 2</c> — the F01 anchor: a pure, plannable LOCAL-ONLY temp, read
/// <see cref="PlannedLoopTempCase.Reuse"/> times in the accumulator row of every state-forming
/// round;</item>
/// <item><c>F = n * 10 + tick()</c> — a FALLBACK temp: the planner cannot plan a <c>tick()</c> call,
/// so the temp is never a planned slot; demanded (read <c>Reuse</c> times per state-forming round)
/// only on the <see cref="PlannedLoopTempFamily.TempPath.Fallback"/> path;</item>
/// <item><c>K = 7</c> — an EXPORTED, self-contained temp, read <c>Reuse</c> times per state-forming
/// round and, in a <c>while</c> step, once more by the continuation row <c>n + K &lt;= R + 7</c> of
/// every round (the false round included), so its count differs from <c>T</c>'s there;</item>
/// <item><c>U = n + 100</c> — DECLARED BUT NEVER DEMANDED.</item>
/// </list>
/// <para>The step's rows are <c>n + 1</c>, the accumulator row <c>acc + (T + K)×k</c> (with
/// <c>+ F</c> in each group on the fallback path) and, for <c>while</c>, the continuation row. On the
/// <see cref="PlannedLoopTempFamily.TempPath.Planned"/> path every row is planned and <c>T</c>, <c>K</c>
/// live in frame slots (<c>F</c> is undemanded, so its refusal leaves the rows planned). On the
/// fallback path the accumulator row reads <c>F</c>, which has no plan, so that row and the
/// continuation row run generically inside the optimized loop and the planner withdraws every temp
/// plan (a partially planned loop routes local properties through the run's cache).</para>
///
/// <para><b>Dimensions.</b> <see cref="PlannedLoopTempCase.Depth"/> is the activation depth: the
/// number of invoked owners declaring the step around it (0: the root; 1: <c>Run(b)</c>; 2:
/// <c>Outer(c)</c> around <c>Run(b)</c>), each case running its loop in two activations (two root
/// rows, initial accumulators 0 and 100). <see cref="PlannedLoopTempCase.Rounds"/> is the round count
/// <c>R</c> (<c>repeat(R)</c>, or a <c>while</c> with R true rounds and one false round) and
/// <see cref="PlannedLoopTempCase.Reuse"/> the reads per temp and state-forming round. The nine
/// (depth, rounds, reuse) triples are the L9 orthogonal array: every pair of levels of any two of
/// the three factors occurs exactly once, for each loop kind and path (36 cases).</para>
///
/// <para><b>Why these dimensions.</b> <see cref="Predict"/> also evaluates five REJECTED readings
/// (<see cref="Reading"/>), and <c>PlannedLoopTempFamilyTests</c> pins exactly which cases tell
/// each from the approved per-round memo: a run cache entry for the exported temp and a missed
/// publication are refuted by every case; a memo that survives the rounds of one loop needs
/// <c>R ≥ 2</c> or a <c>while</c>; a memo keyed by the outermost invoked owner needs depth ≥ 1 as
/// well; per-read evaluation needs a reused temp (<c>k ≥ 2</c>) or the <c>while</c> row's extra
/// read.</para>
/// </summary>
internal static class PlannedLoopTempFamily
{
    internal enum StepLoop { Repeat, While }

    internal enum TempPath { Planned, Fallback }

    /// <summary>
    /// The approved reading and the rejected ones the family must tell apart from it.
    /// </summary>
    internal enum Reading
    {
        /// <summary>
        /// KL-06 F01 Option A with the inner-property lifetime rule: a round is an actual call of the
        /// step, every temp it DEMANDS is evaluated and published once in it, later reads reuse that
        /// value, and an undemanded temp does no work.
        /// </summary>
        Approved,

        /// <summary>The exported temp keeps ONE run-scoped entry (the rule before the inner-property lifetime).</summary>
        ExportedRunEntry,

        /// <summary>A perturbed key: one entry per temp and LOOP EXECUTION, reused by its later rounds.</summary>
        LoopExecutionEntry,

        /// <summary>
        /// A perturbed key: the OUTERMOST invoked owner of the declaring chain instead of the nearest
        /// (the round). At depth 0 the round is the only invoked owner, so this equals the approved
        /// reading there; deeper, every round of one activation shares the entry.
        /// </summary>
        OutermostInvocationEntry,

        /// <summary>A wrong evaluation count: every read evaluates its temp afresh and publishes.</summary>
        PerRead,

        /// <summary>A missed publication: values and effects as approved, but no demanded temp is published.</summary>
        NoPublication,
    }

    /// <summary>The four temps every case declares, in declaration order.</summary>
    internal static readonly IReadOnlyList<string> TempNames = ["T", "F", "K", "U"];

    /// <summary>
    /// The L9 orthogonal array over (activation depth, rounds, reuse) with levels {0, 1, 2},
    /// {1, 2, 3} and {1, 2, 3}: each pair of levels of any two factors occurs exactly once.
    /// </summary>
    internal static readonly IReadOnlyList<(int Depth, int Rounds, int Reuse)> Grid =
    [
        (0, 1, 1), (0, 2, 2), (0, 3, 3),
        (1, 1, 2), (1, 2, 3), (1, 3, 1),
        (2, 1, 3), (2, 2, 1), (2, 3, 2),
    ];

    /// <summary>The initial accumulator of each of a case's two loop activations (one root row each).</summary>
    internal static readonly IReadOnlyList<int> ActivationBases = [0, 100];

    /// <summary>Every case, in a fixed order: loop kind, then path, then the grid's order.</summary>
    internal static IReadOnlyList<PlannedLoopTempCase> Cases { get; } =
    [
        .. from loop in new[] { StepLoop.Repeat, StepLoop.While }
           from path in new[] { TempPath.Planned, TempPath.Fallback }
           from cell in Grid
           select new PlannedLoopTempCase(loop, path, cell.Depth, cell.Rounds, cell.Reuse),
    ];

    /// <summary>
    /// What a run of <paramref name="loopCase"/> gives under <paramref name="reading"/>: the
    /// neutral observation, the publications per watched temp name and the number of
    /// <c>tick()</c> executions. A direct simulation of the step's arithmetic and of the reads
    /// in evaluation order (rows left to right, a <c>while</c> round's continuation row first),
    /// independent of the evaluator.
    /// </summary>
    internal static Prediction Predict(PlannedLoopTempCase loopCase, Reading reading)
    {
        var published = TempNames.ToDictionary(name => name, _ => 0, StringComparer.Ordinal);
        var memo = new Dictionary<(string Name, int Activation, int Round), long>();
        var ticks = 0;
        var finalStates = new List<(long N, long Acc)>();
        var reads = 0;

        for (var activation = 0; activation < ActivationBases.Count; activation++)
        {
            long n = 1;
            long acc = ActivationBases[activation];
            for (var round = 1; ; round++)
            {
                long Read(string name)
                {
                    reads++;
                    // The entry a read of `name` in this round finds, under the reading's key.
                    var key = reading switch
                    {
                        Reading.ExportedRunEntry when name == "K" => (name, -1, -1),
                        Reading.LoopExecutionEntry => (name, activation, -1),
                        Reading.OutermostInvocationEntry when loopCase.Depth > 0 => (name, activation, -1),
                        Reading.PerRead => (name, activation, -reads),
                        _ => (name, activation, round),
                    };
                    if (memo.TryGetValue(key, out var value))
                        return value;

                    value = name switch
                    {
                        "T" => n * 2,
                        "F" => n * 10 + ++ticks,
                        "K" => 7,
                        _ => throw new InvalidOperationException($"No row of the family reads {name}."),
                    };
                    memo.Add(key, value);
                    if (reading != Reading.NoPublication)
                        published[name]++;
                    return value;
                }

                if (loopCase.Loop == StepLoop.While)
                {
                    // LOOP-06: the continuation row first; a false verdict returns the round's state.
                    if (!(n + Read("K") <= loopCase.Rounds + 7))
                        break;
                }
                else if (round > loopCase.Rounds)
                {
                    break;
                }

                var next = acc;
                for (var group = 0; group < loopCase.Reuse; group++)
                {
                    next += Read("T");
                    next += Read("K");
                    if (loopCase.Path == TempPath.Fallback)
                        next += Read("F");
                }

                (n, acc) = (n + 1, next);
            }

            finalStates.Add((n, acc));
        }

        var raw = "S[" + string.Join(", ", finalStates.Select(state => FormattableString.Invariant($"S[{state.N}, {state.Acc}]"))) + "]";
        var neutral = FormattableString.Invariant($"ok raw={raw} n={finalStates.Count}");
        var publications = CachePublicationExpectation.Of([.. TempNames.Select(name => (name, published[name]))]);
        return new Prediction(neutral, publications, ticks);
    }

    /// <summary>A reading's observation of one case.</summary>
    internal sealed record Prediction(string Neutral, CachePublicationExpectation Publications, int Ticks)
    {
        public bool SameAs(Prediction other)
            => Neutral == other.Neutral && Ticks == other.Ticks && Publications.ToString() == other.Publications.ToString();
    }
}

/// <summary>One generated case of <see cref="PlannedLoopTempFamily"/>.</summary>
internal sealed record PlannedLoopTempCase(
    PlannedLoopTempFamily.StepLoop Loop,
    PlannedLoopTempFamily.TempPath Path,
    int Depth,
    int Rounds,
    int Reuse)
{
    private string LoopName => Loop == PlannedLoopTempFamily.StepLoop.Repeat ? "repeat" : "while";

    private string PathName => Path == PlannedLoopTempFamily.TempPath.Planned ? "planned" : "fallback";

    /// <summary>The stable case id: <c>plt/{loop}/{path}/d{depth}-r{rounds}-k{reuse}</c>.</summary>
    public string Id => FormattableString.Invariant($"plt/{LoopName}/{PathName}/d{Depth}-r{Rounds}-k{Reuse}");

    /// <summary>The Lean definition's name.</summary>
    public string LeanName
        => FormattableString.Invariant($"plt{char.ToUpperInvariant(LoopName[0])}{LoopName[1..]}{char.ToUpperInvariant(PathName[0])}{PathName[1..]}D{Depth}R{Rounds}K{Reuse}");

    /// <summary>The number of rounds one loop activation evaluates: a <c>while</c> adds its false round.</summary>
    public int RoundsPerActivation => Loop == PlannedLoopTempFamily.StepLoop.While ? Rounds + 1 : Rounds;

    /// <summary>The source program (LF line ends, four-space indentation).</summary>
    public string Source
    {
        get
        {
            var group = Path == PlannedLoopTempFamily.TempPath.Fallback ? " + T + K + F" : " + T + K";
            var step = new List<string>
            {
                "Step(n, acc) = {",
                "    T = n * 2",
                "    F = n * 10 + tick()",
                "    K = 7",
                "    U = n + 100",
                "    n + 1",
                "    acc" + string.Concat(Enumerable.Repeat(group, Reuse)),
            };
            if (Loop == PlannedLoopTempFamily.StepLoop.While)
                step.Add(FormattableString.Invariant($"    n + K <= {Rounds + 7}"));
            step.Add("}");

            var call = Loop == PlannedLoopTempFamily.StepLoop.Repeat
                ? FormattableString.Invariant($".repeat({Rounds})")
                : ".while";
            var bases = PlannedLoopTempFamily.ActivationBases;
            var lines = new StringBuilder();
            switch (Depth)
            {
                case 0:
                    Append(lines, 0, step);
                    foreach (var initial in bases)
                        lines.Append(CultureInfo.InvariantCulture, $"Step(1, {initial}){call}\n");
                    break;
                case 1:
                    lines.Append("Run(b) = {\n");
                    Append(lines, 1, step);
                    lines.Append($"    Step(1, b){call}\n}}\n");
                    foreach (var initial in bases)
                        lines.Append(CultureInfo.InvariantCulture, $"Run({initial})\n");
                    break;
                case 2:
                    lines.Append("Outer(c) = {\n    Run(b) = {\n");
                    Append(lines, 2, step);
                    lines.Append($"        Step(1, b){call}\n    }}\n    Run(c)\n}}\n");
                    foreach (var initial in bases)
                        lines.Append(CultureInfo.InvariantCulture, $"Outer({initial})\n");
                    break;
                default:
                    throw new InvalidOperationException($"No depth {Depth} in the family.");
            }

            return lines.ToString().TrimEnd('\n');

            static void Append(StringBuilder builder, int depth, IEnumerable<string> block)
            {
                foreach (var line in block)
                    builder.Append(' ', depth * 4).Append(line).Append('\n');
            }
        }
    }

    /// <summary>The approved expectation (<see cref="PlannedLoopTempFamily.Reading.Approved"/>).</summary>
    public PlannedLoopTempFamily.Prediction Expected => PlannedLoopTempFamily.Predict(this, PlannedLoopTempFamily.Reading.Approved);

    /// <summary>
    /// The part of the approved publications the OPTIMIZED route establishes in planned frame slots:
    /// on the planned path the demanded planned temps <c>T</c> and <c>K</c>, on the fallback path
    /// none (every temp read runs through the run's cache).
    /// </summary>
    public CachePublicationExpectation ExpectedFrameSlots
        => Path == PlannedLoopTempFamily.TempPath.Planned
            ? CachePublicationExpectation.Of(("K", Expected.Publications.Entries.Single(e => e.Name == "K").Count),
                ("T", Expected.Publications.Entries.Single(e => e.Name == "T").Count))
            : CachePublicationExpectation.Nothing;
}
