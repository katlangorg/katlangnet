using System.Globalization;
using System.Numerics;
using System.Text;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The final hostile review of comparison chaining (September 2026). The earlier classes
/// (<see cref="ComparisonChainParserTests"/>, <see cref="ComparisonChainEvaluationTests"/>,
/// <see cref="ComparisonChainHostileReviewTests"/>, <see cref="ComparisonChainAuditTests"/>) pin
/// hand-picked rows; here every chain is GENERATED and judged by an INDEPENDENT oracle that never
/// calls a production comparison: a value model with its own structural equality and ordering
/// rules, composed exactly as the frozen chain law prescribes — every operand evaluated once, left
/// to right; each link comparing the two ADJACENT operand values (the previous VALUE carried
/// forward, never re-evaluated, and never the Boolean verdict of the links so far); the result the
/// conjunction of every link, with no link skipped after a <c>false</c> one; the first error — an
/// operand's own or a link's rejection — ending the chain before any later operand runs. The same
/// law is checked on the generic evaluator, the optimized entry point, the planned loop, and the
/// suspended async twin, and the generated parenthesized trees pin that parentheses — and only
/// parentheses — separate a nested comparison from a chain, in the parsed tree, its diagnostic
/// spelling, and its value. Lean parity for the forms below is pinned by CoreTests
/// <c>ComparisonChains.lean</c> and the derived explorer specials (<c>chain*</c>).
/// </summary>
public class ComparisonChainDifferentialOracleTests
{
    // ── An independent value model: nothing here calls a production comparison ──

    private abstract record Value;
    private sealed record Number(decimal Magnitude) : Value;
    private sealed record NotANumber : Value;
    private sealed record Flag(bool Truth) : Value;
    private sealed record Text(string Content) : Value;
    private sealed record SequenceOf(Value[] Items) : Value;
    private sealed record ListOf(Value[] Items) : Value;

    /// <summary>
    /// Total structural equality: the same kind with equal contents, recursively; numbers by
    /// numeric value (so <c>2 == 2.0</c>), every NaN equal to every NaN, and different kinds —
    /// a number and a Boolean, a sequence and a list, <c>()</c> and <c>[]</c> — never equal.
    /// </summary>
    private static bool ModelEquals(Value left, Value right) => (left, right) switch
    {
        (Number a, Number b) => a.Magnitude == b.Magnitude,
        (NotANumber, NotANumber) => true,
        (Flag a, Flag b) => a.Truth == b.Truth,
        (Text a, Text b) => string.Equals(a.Content, b.Content, StringComparison.Ordinal),
        (SequenceOf a, SequenceOf b) => ItemsEqual(a.Items, b.Items),
        (ListOf a, ListOf b) => ItemsEqual(a.Items, b.Items),
        _ => false,
    };

    private static bool ItemsEqual(Value[] left, Value[] right)
        => left.Length == right.Length && left.Zip(right).All(pair => ModelEquals(pair.First, pair.Second));

    private abstract record Outcome;
    private sealed record Holds(bool Truth) : Outcome;

    /// <summary>A rejected link: a fragment its message carries, and the context naming the link (none for the string rejections).</summary>
    private sealed record Rejected(string Fragment, string? Context) : Outcome;

    /// <summary>An operand whose own evaluation fails (a division by zero) — never a link.</summary>
    private sealed record OperandFailed : Outcome;

    /// <summary>One chain operand: its source spelling, the name a diagnostic gives it, and its model value.</summary>
    private sealed record Operand(string Source, string Name, Value Value);

    /// <summary>
    /// ONE link under the ordinary operator semantics: <c>==</c>/<c>!=</c> are total structural
    /// equality and never fail; an ordering operator rejects strings (both, or one), then requires a
    /// numeric scalar on each side (a Boolean, sequence, or list is the value-kind rejection naming
    /// THIS link), and orders IEEE-style (every ordering with NaN is false).
    /// </summary>
    private static Outcome ModelLink(string op, Operand left, Operand right)
    {
        if (op == "==")
            return new Holds(ModelEquals(left.Value, right.Value));
        if (op == "!=")
            return new Holds(!ModelEquals(left.Value, right.Value));
        if (left.Value is Text && right.Value is Text)
            return new Rejected("Strings only support == and != operators", null);
        if (left.Value is Text || right.Value is Text)
            return new Rejected("Cannot apply operator to string and non-string operands", null);

        var context = $"while evaluating `{left.Name} {op} {right.Name}`";
        if (left.Value is not (Number or NotANumber))
            return new Rejected($"operator `{op}` expects numeric scalar operands, but the left operand was", context);
        if (right.Value is not (Number or NotANumber))
            return new Rejected($"operator `{op}` expects numeric scalar operands, but the right operand was", context);
        if (left.Value is not Number x || right.Value is not Number y)
            return new Holds(false);

        return new Holds(op switch
        {
            "<" => x.Magnitude < y.Magnitude,
            "<=" => x.Magnitude <= y.Magnitude,
            ">" => x.Magnitude > y.Magnitude,
            ">=" => x.Magnitude >= y.Magnitude,
            _ => throw new InvalidOperationException(op),
        });
    }

    /// <summary>
    /// The frozen chain law over operands that may fail: operand <c>i</c> runs (recorded in the
    /// trace), then link <c>i - 1</c> compares operand <c>i - 1</c>'s value with operand <c>i</c>'s;
    /// a false link is conjoined and the chain goes on; the first failure — operand or link — is
    /// the outcome and nothing after it runs. Returns the outcome, the rejecting link (or -1), and
    /// the operand trace.
    /// </summary>
    private static (Outcome Outcome, int FailingLink, List<int> Trace) ModelChain(
        IReadOnlyList<Operand> operands, IReadOnlyList<string> ops, Func<int, bool>? operandFails = null)
    {
        var trace = new List<int>();
        var holds = true;
        for (var index = 0; index < operands.Count; index++)
        {
            trace.Add(index);
            if (operandFails?.Invoke(index) == true)
                return (new OperandFailed(), -1, trace);
            if (index == 0)
                continue;

            var link = ModelLink(ops[index - 1], operands[index - 1], operands[index]);
            if (link is Rejected)
                return (link, index - 1, trace);
            holds &= ((Holds)link).Truth;
        }

        return (new Holds(holds), -1, trace);
    }

    private static readonly string[] Operators = ["<", "<=", ">", ">=", "==", "!="];

    /// <summary>
    /// Written operands of every value kind. <c>(2)</c> is a redundant grouping — the operand IS
    /// <c>2</c> (named <c>2</c>, but spanning its parentheses); <c>N</c> is a NaN property.
    /// </summary>
    private static readonly Operand[] Pool =
    [
        new("1", "1", new Number(1)),
        new("2", "2", new Number(2)),
        new("2.0", "2.0", new Number(2.0m)),
        new("-3", "-3", new Number(-3)),
        new("(2)", "2", new Number(2)),
        new("N", "N", new NotANumber()),
        new("true", "true", new Flag(true)),
        new("false", "false", new Flag(false)),
        new("'a'", "'a'", new Text("a")),
        new("'b'", "'b'", new Text("b")),
        new("(1, 2)", "(1, 2)", new SequenceOf([new Number(1), new Number(2)])),
        new("()", "()", new SequenceOf([])),
        new("[1, 2]", "[1, 2]", new ListOf([new Number(1), new Number(2)])),
        new("[]", "[]", new ListOf([])),
        new("[1]", "[1]", new ListOf([new Number(1)])),
    ];

    private const string NaNDeclaration = "N = Math.Sqrt(-1)\n";

    /// <summary>The written chain and each operand's 1-based [start, end) columns.</summary>
    private static (string Source, (int Start, int End)[] Columns) Spell(IReadOnlyList<Operand> operands, IReadOnlyList<string> ops)
    {
        var builder = new StringBuilder();
        var columns = new (int Start, int End)[operands.Count];
        for (var index = 0; index < operands.Count; index++)
        {
            if (index > 0)
                builder.Append(' ').Append(ops[index - 1]).Append(' ');
            var start = builder.Length + 1;
            builder.Append(operands[index].Source);
            columns[index] = (start, builder.Length + 1);
        }

        return (builder.ToString(), columns);
    }

    /// <summary>
    /// Parses and evaluates one PURE chain (generic strategy) and returns a mismatch description,
    /// or null when the parsed tree is the ONE flat chain that was written and its outcome — value,
    /// or error kind, message, link context, and link span (the hull of the two ADJACENT operands'
    /// written extents) — is what the model predicts.
    /// </summary>
    private static string? CheckPureChain(IReadOnlyList<Operand> operands, IReadOnlyList<string> ops)
    {
        var (chainSource, columns) = Spell(operands, ops);
        var parsed = Parser.Parse(NaNDeclaration + chainSource);
        if (parsed.HasErrors)
            return $"`{chainSource}` did not parse: {string.Join("; ", parsed.Diagnostics)}";
        if (parsed.Root.Output is not [Expr.Comparison chain]
            || !chain.Links.Select(link => ExprNameRenderer.ComparisonOpText(link.Op)).SequenceEqual(ops))
        {
            return $"`{chainSource}` is not ONE flat chain with its written operators";
        }

        var observed = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: false).Result;
        var (expected, failingLink, _) = ModelChain(operands, ops);
        switch (expected)
        {
            case Holds holds:
                if (observed.IsError)
                    return $"`{chainSource}`: expected {holds.Truth}, got {observed.Error}";
                if (observed.Value.Value is not Result.Bool(var truth) || truth != holds.Truth || observed.Value.EmittedCount != 1)
                    return $"`{chainSource}`: expected {holds.Truth} (one value), got {observed.Value.Value} n={observed.Value.EmittedCount}";
                return null;

            case Rejected rejected:
                if (!observed.IsError)
                    return $"`{chainSource}`: expected the rejection of link {failingLink}, got {observed.Value.Value}";
                var text = observed.Error.ToString();
                if (observed.Error.Code != KatLangErrorCode.TypeMismatch || !text.Contains(rejected.Fragment, StringComparison.Ordinal))
                    return $"`{chainSource}`: expected `{rejected.Fragment}` at link {failingLink}, got {observed.Error.Code}: {text}";
                if (rejected.Context is { } context
                        ? !text.Contains(context, StringComparison.Ordinal)
                        : text.Contains("while evaluating", StringComparison.Ordinal))
                {
                    return $"`{chainSource}`: expected the context {rejected.Context ?? "(none)"} for link {failingLink}, got {text}";
                }

                var linkSpan = new SourceSpan(2, columns[failingLink].Start, 2, columns[failingLink + 1].End);
                return observed.Error.Span == linkSpan
                    ? null
                    : $"`{chainSource}`: expected the link span {linkSpan}, got {observed.Error.Span}";

            default:
                throw new InvalidOperationException(expected.ToString());
        }
    }

    private static void AssertNoMismatch(List<string> mismatches, int checkedCases)
        => Assert.True(
            mismatches.Count == 0,
            $"{mismatches.Count} of {checkedCases} generated chains disagree with the oracle:\n" + string.Join("\n", mismatches.Take(25)));

    // ── Pure chains: the ordinary operator per link, the chain law over the links ──

    [Fact]
    public void EveryOrderedPair_UnderEveryOperator_IsTheOrdinaryComparisonTheModelPredicts()
    {
        // Two operands: every ordered pair of the pool under all six operators (15 x 15 x 6 =
        // 1,350 single comparisons). This validates the independent link model itself against the
        // ordinary operator semantics — equality total across every kind, ordering numeric-only,
        // the string rejections — before any longer chain is composed from it.
        var mismatches = new List<string>();
        var cases = 0;
        foreach (var left in Pool)
        {
            foreach (var right in Pool)
            {
                foreach (var op in Operators)
                {
                    cases++;
                    if (CheckPureChain([left, right], [op]) is { } mismatch)
                        mismatches.Add(mismatch);
                }
            }
        }

        Assert.Equal(1_350, cases);
        AssertNoMismatch(mismatches, cases);
    }

    [Fact]
    public void EveryThreeOperandChain_OverTheLinkClassRepresentatives_MatchesTheChainLaw()
    {
        // Three operands, EXHAUSTIVELY: every operator pair (36) over representatives of every
        // link class — numbers that order both ways, a Boolean (equal to itself, unequal to a
        // number, unordered), a string, and a list — 5^3 x 36 = 4,500 chains. A chain that read
        // left-associatively, compared the first operand again, carried the running verdict as
        // the next left operand, or stopped at a false link disagrees with the model here.
        Operand[] representatives = [Pool[0], Pool[1], Pool[6], Pool[8], Pool[13]];
        var mismatches = new List<string>();
        var cases = 0;
        foreach (var a in representatives)
        foreach (var b in representatives)
        foreach (var c in representatives)
        foreach (var op1 in Operators)
        foreach (var op2 in Operators)
        {
            cases++;
            if (CheckPureChain([a, b, c], [op1, op2]) is { } mismatch)
                mismatches.Add(mismatch);
        }

        Assert.Equal(4_500, cases);
        AssertNoMismatch(mismatches, cases);
    }

    [Fact]
    public void LongerGeneratedChains_OverEveryValueKind_MatchTheChainLaw()
    {
        // 1,500 deterministic samples of four to eight operands over the whole pool.
        var random = new Random(0x2026_0927);
        var mismatches = new List<string>();
        for (var sample = 0; sample < 1_500; sample++)
        {
            var count = random.Next(4, 9);
            var operands = Enumerable.Range(0, count).Select(_ => Pool[random.Next(Pool.Length)]).ToArray();
            var ops = Enumerable.Range(0, count - 1).Select(_ => Operators[random.Next(Operators.Length)]).ToArray();
            if (CheckPureChain(operands, ops) is { } mismatch)
                mismatches.Add(mismatch);
        }

        AssertNoMismatch(mismatches, 1_500);
    }

    // ── Observable operands: exact once, left to right, eager past false, stopped by errors ──

    private static readonly (Result Host, Value Model)[] HostPool =
    [
        (new Result.Atom(1), new Number(1)),
        (new Result.Atom(2), new Number(2)),
        (new Result.Atom(Decimal128.NaN), new NotANumber()),
        (new Result.Bool(true), new Flag(true)),
        (new Result.Bool(false), new Flag(false)),
        (new Result.Str("a"), new Text("a")),
        (new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]), new SequenceOf([new Number(1), new Number(2)])),
        (new Result.SequenceValue([]), new SequenceOf([])),
        (new Result.ListValue([new Result.Atom(1), new Result.Atom(2)]), new ListOf([new Number(1), new Number(2)])),
        (new Result.ListValue([]), new ListOf([])),
    ];

    public static TheoryData<string> Strategies() => new() { "generic", "optimized", "async" };

    [Theory]
    [MemberData(nameof(Strategies))]
    public async Task HostOperandChains_RunEveryOperandOnce_InOrder_PastFalse_AndStopAtTheFirstFailure(string strategy)
    {
        // Every operand is a host operation `Hi()` that records `i` when it runs — suspending
        // first (`Task.Yield`) on the async strategy — or `(Hi() / 0)`, whose host operation runs
        // and whose division then fails. The recorded trace must be EXACTLY the model's: each
        // operand once, in written order, every operand after a false link, and nothing after the
        // first operand or link failure.
        var random = new Random(0x0C4A_1215);
        var mismatches = new List<string>();
        const int Samples = 400;
        for (var sample = 0; sample < Samples; sample++)
        {
            var count = random.Next(2, 7);
            var values = Enumerable.Range(0, count).Select(_ => HostPool[random.Next(HostPool.Length)]).ToArray();
            var fails = Enumerable.Range(0, count).Select(_ => random.Next(8) == 0).ToArray();
            var ops = Enumerable.Range(0, count - 1).Select(_ => Operators[random.Next(Operators.Length)]).ToArray();
            var operands = Enumerable.Range(0, count)
                .Select(index => new Operand(fails[index] ? $"(H{index}() / 0)" : $"H{index}()", $"H{index}(...)", values[index].Model))
                .ToArray();

            var trace = new List<int>();
            var operations = HostOperations.Create(Enumerable.Range(0, count).Select(index =>
            {
                var returned = fails[index] ? new Result.Atom(1) : values[index].Host;
                return strategy == "async"
                    ? HostOperation.CreateAsync($"H{index}", async (_, _) => { await Task.Yield(); trace.Add(index); return returned; })
                    : HostOperation.Create($"H{index}", (_, _) => { trace.Add(index); return returned; });
            }).ToArray());

            var (source, _) = Spell(operands, ops);
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, source + ": " + string.Join("; ", parsed.Diagnostics));
            var ast = new Expr.AlgorithmExpr(parsed.Root);
            var observed = strategy == "async"
                ? (await Evaluator.RunCountedObservedAsync(ast, hostOperations: operations)).Result
                : Evaluator.RunCountedObserved(ast, enableOptimizations: strategy == "optimized", hostOperations: operations).Result;

            var (expected, _, expectedTrace) = ModelChain(operands, ops, index => fails[index]);
            string? mismatch = null;
            if (!trace.SequenceEqual(expectedTrace))
                mismatch = $"trace [{string.Join(",", trace)}], expected [{string.Join(",", expectedTrace)}]";
            else if (expected is Holds holds && (observed.IsError || observed.Value.Value is not Result.Bool(var truth) || truth != holds.Truth))
                mismatch = $"expected {holds.Truth}, got {(observed.IsError ? observed.Error.ToString() : observed.Value.Value.ToString())}";
            else if (expected is OperandFailed && (!observed.IsError || observed.Error.Code != KatLangErrorCode.DivisionByZero
                         || observed.Error.ToString().Contains("while evaluating", StringComparison.Ordinal)))
                mismatch = $"expected the operand's own division error, got {(observed.IsError ? observed.Error.ToString() : observed.Value.Value.ToString())}";
            else if (expected is Rejected rejected && (!observed.IsError || observed.Error.Code != KatLangErrorCode.TypeMismatch
                         || !observed.Error.ToString().Contains(rejected.Context ?? rejected.Fragment, StringComparison.Ordinal)))
                mismatch = $"expected `{rejected.Context ?? rejected.Fragment}`, got {(observed.IsError ? observed.Error.ToString() : observed.Value.Value.ToString())}";

            if (mismatch is not null)
                mismatches.Add($"{strategy} `{source}`: {mismatch}");
        }

        AssertNoMismatch(mismatches, Samples);
    }

    [Fact]
    public async Task PlannedLoopChains_CallEveryTempOnce_PastFalse_AndStopAtALinkRejection()
    {
        // Inside a planned loop step the operands are temp CALLS `Ti()`; a call bypasses the
        // property cache and materializes its string on every evaluation, and `Ti` holds 4^i
        // characters, so the step's materialized-character total decodes EXACTLY how many times
        // each temp ran (a temp appears at most three times). Equality links compare the strings
        // (equal only for the same temp); an ordering link is the string rejection, which ends the
        // chain in the first iteration. The planned strategy must plan the whole step (no
        // fallback) and agree with the generic strategy and the async twin on value, error, and
        // every character.
        var lengths = new[] { 1, 4, 16, 64, 256 };
        var temps = string.Concat(lengths.Select((length, index) => $"    T{index} = '{new string('x', length)}'\n"));
        var random = new Random(0x71A2);
        const int Samples = 150;
        const int Iterations = 3;
        for (var sample = 0; sample < Samples; sample++)
        {
            var count = random.Next(2, 6);
            var picks = new List<int>();
            while (picks.Count < count)
            {
                var pick = random.Next(lengths.Length);
                if (picks.Count(existing => existing == pick) < 3)
                    picks.Add(pick);
            }

            var ops = Enumerable.Range(0, count - 1)
                .Select(_ => random.Next(4) == 0 ? Operators[random.Next(4)] : Operators[4 + random.Next(2)])
                .ToArray();
            var operands = picks.Select(pick => new Operand($"T{pick}()", $"T{pick}(...)", new Text(new string('x', lengths[pick])))).ToArray();
            var (chain, _) = Spell(operands, ops);
            var source = $"Step = {{\n{temps}    n + if({chain}, 1, 0)\n}}\nStep.repeat({Iterations}, 0)";

            var (expected, _, trace) = ModelChain(operands, ops);
            var unitsPerIteration = trace.Sum(index => lengths[picks[index]]);
            string expectedNeutral;
            long expectedUnits;
            if (expected is Holds holds)
            {
                expectedNeutral = $"ok raw={(holds.Truth ? Iterations : 0)} n=1";
                expectedUnits = Iterations * unitsPerIteration;
            }
            else
            {
                expectedNeutral = "error";
                expectedUnits = unitsPerIteration;
            }

            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
            var diagnostics = new LoopOptimizationDiagnostics();
            var (planned, plannedBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: true, loopDiagnostics: diagnostics);
            var (generic, genericBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
            var (twin, twinBudget) = await AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));

            foreach (var (name, result, budget) in new[] { ("planned", planned, plannedBudget), ("generic", generic, genericBudget), ("async", twin, twinBudget) })
            {
                var neutral = result.IsError ? "error" : AsyncEvaluationHarness.NeutralOf(result);
                Assert.True(neutral == expectedNeutral, $"{name} `{chain}`: {neutral}, expected {expectedNeutral}");
                Assert.True(budget.MaterializedStringChars == expectedUnits,
                    $"{name} `{chain}`: {budget.MaterializedStringChars} characters, expected {expectedUnits}");
                if (result.IsError)
                {
                    Assert.Equal(KatLangErrorCode.TypeMismatch, result.Error.Code);
                    Assert.Contains("Strings only support == and != operators", result.Error.ToString(), StringComparison.Ordinal);
                }
            }

            if (generic.IsError)
                Assert.Equal(generic.Error.ToString(), planned.Error.ToString());
            var snapshot = diagnostics.GetSnapshot();
            Assert.Equal(1, snapshot.OptimizedLoopHits);
            Assert.Equal(0, snapshot.PlannedExpressionFallbacks);
        }
    }

    [Fact]
    public async Task PlannedLoopChains_OverPlannableLiterals_AgreeWithTheModelAndTheGenericStrategy()
    {
        // Pure chains of plannable literals (numbers, Booleans, strings) as a planned `if`
        // condition: value and error agree with the model and with the generic strategy, and the
        // whole step is planned.
        Operand[] plannable = [Pool[0], Pool[1], Pool[3], Pool[6], Pool[7], Pool[8], Pool[9]];
        var random = new Random(0x5EED);
        const int Samples = 400;
        var mismatches = new List<string>();
        for (var sample = 0; sample < Samples; sample++)
        {
            var count = random.Next(2, 6);
            var operands = Enumerable.Range(0, count).Select(_ => plannable[random.Next(plannable.Length)]).ToArray();
            var ops = Enumerable.Range(0, count - 1).Select(_ => Operators[random.Next(Operators.Length)]).ToArray();
            var (chain, _) = Spell(operands, ops);
            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid($"Step = {{\n    n + if({chain}, 1, 0)\n}}\nStep.repeat(2, 0)").Root);

            var diagnostics = new LoopOptimizationDiagnostics();
            var (planned, _) = Evaluator.RunCountedObserved(program, enableOptimizations: true, loopDiagnostics: diagnostics);
            var (generic, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
            var (twin, _) = await AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));
            var snapshot = diagnostics.GetSnapshot();

            var (expected, _, _) = ModelChain(operands, ops);
            var expectedNeutral = expected is Holds holds ? $"ok raw={(holds.Truth ? 2 : 0)} n=1" : "error";
            var context = (expected as Rejected)?.Context ?? (expected as Rejected)?.Fragment;
            foreach (var (name, result) in new[] { ("planned", planned), ("generic", generic), ("async", twin) })
            {
                var neutral = result.IsError ? "error" : AsyncEvaluationHarness.NeutralOf(result);
                if (neutral != expectedNeutral)
                    mismatches.Add($"{name} `{chain}`: {neutral}, expected {expectedNeutral}");
                else if (result.IsError && !result.Error.ToString().Contains(context!, StringComparison.Ordinal))
                    mismatches.Add($"{name} `{chain}`: {result.Error}, expected `{context}`");
            }

            if (generic.IsError && planned.IsError && generic.Error.ToString() != planned.Error.ToString())
                mismatches.Add($"`{chain}`: planned {planned.Error} differs from generic {generic.Error}");
            if (snapshot.OptimizedLoopHits != 1 || snapshot.PlannedExpressionFallbacks != 0)
                mismatches.Add($"`{chain}`: hits={snapshot.OptimizedLoopHits} fallbacks={snapshot.PlannedExpressionFallbacks}");
        }

        AssertNoMismatch(mismatches, Samples);
    }

    [Theory]
    [InlineData(1L)]
    [InlineData(42L)]
    [InlineData(20_260_927L)]
    public async Task SeededDraws_AFalseFirstLink_StillDrawsEveryLaterOperandOnce_InOrder(long seed)
    {
        // `R() < 0` is false for every draw of randomInt(1, 1000000) (and `R() > 1000000` too),
        // so the FIRST link of each chain is false whatever the seed. The explicit formulation
        // evaluates each operand once, left to right — three draws — so the row after the chain
        // takes the FOURTH draw of the stream. A chain that stopped at the false link would
        // leave it the second draw; one that re-evaluated a middle operand, the fifth.
        const string declaration = "R = randomInt(1, 1000000)\n";
        var options = new RunOptions { RandomSeed = seed };
        // An async host operation in the run's set routes RunAsync through the async twin
        // (without one, RunAsync runs the synchronous pipeline inline); the chain never calls it.
        var twinOptions = new RunOptions
        {
            RandomSeed = seed,
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("Idle", async (_, _) => { await Task.Yield(); return new Result.Atom(0); })),
        };
        var stream = Assert.IsType<RunResult.Success>(KatLangEngine.Run(declaration + "R(), R(), R(), R(), R()", options)).Atoms;
        Assert.Equal(5, stream.Count);
        Assert.Equal(5, stream.Distinct().Count());
        var fourth = stream[3].ToString(CultureInfo.InvariantCulture);

        foreach (var chain in new[] { "R() < 0 < R() < R()", "R() > 1000000 == R() != R()", "R() < 0 == R() >= R()" })
        {
            var expected = "false\n" + fourth;
            var sync = Assert.IsType<RunResult.Success>(KatLangEngine.Run(declaration + chain + ", R()", options));
            Assert.Equal(expected, sync.ToDisplayString().ReplaceLineEndings("\n"));
            var asynchronous = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(declaration + chain + ", R()", twinOptions));
            Assert.Equal(expected, asynchronous.ToDisplayString().ReplaceLineEndings("\n"));

            // The same chain inside a callback body: one element, the same three draws.
            var callback = Assert.IsType<RunResult.Success>(KatLangEngine.Run(declaration + $"map([0], {{ if(x == 0, {chain}, true) }}), R()", options));
            Assert.Equal("[false]\n" + fourth, callback.ToDisplayString().ReplaceLineEndings("\n"));
        }
    }

    // ── Generated parenthesized trees: only parentheses separate a nested comparison ──

    private abstract record Tree
    {
        /// <summary>Written inside REDUNDANT parentheses (a group whose content is exactly this node).</summary>
        public bool Grouped { get; init; }
    }

    private sealed record Leaf(object Literal) : Tree;
    private sealed record ChainNode(Tree First, (string Op, Tree Operand)[] Links) : Tree;
    private sealed record Negation(Tree Operand) : Tree;
    private sealed record Complement(Tree Operand) : Tree;
    private sealed record Arithmetic(string Op, Tree Left, Tree Right) : Tree;
    private sealed record Selection(Tree Target) : Tree;

    /// <summary>The parser's ladder: not 4 &lt; comparison 5 &lt; + - 6 &lt; * 7 &lt; prefix - 8 &lt; postfix 10 &lt; atom 11.</summary>
    private static int Tier(Tree tree) => tree switch
    {
        Leaf => 11,
        Selection => 10,
        Negation => 8,
        Arithmetic { Op: "*" } => 7,
        Arithmetic => 6,
        ChainNode => 5,
        Complement => 4,
        _ => throw new InvalidOperationException(tree.ToString()),
    };

    /// <summary>
    /// Writes <paramref name="tree"/> as source, parenthesizing a child exactly when it binds
    /// looser than its slot or is marked <see cref="Tree.Grouped"/> — except
    /// <paramref name="ungrouped"/>, whose parentheses are dropped even where they are required.
    /// </summary>
    private static string Write(Tree tree, Tree? ungrouped = null)
    {
        string Slot(Tree child, int slotTier)
        {
            var text = Write(child, ungrouped);
            return !ReferenceEquals(child, ungrouped) && (Tier(child) < slotTier || child.Grouped) ? $"({text})" : text;
        }

        return tree switch
        {
            Leaf { Literal: bool truth } => truth ? "true" : "false",
            Leaf leaf => Convert.ToString(leaf.Literal, CultureInfo.InvariantCulture)!,
            ChainNode chain => Slot(chain.First, 6) + string.Concat(chain.Links.Select(link => $" {link.Op} " + Slot(link.Operand, 6))),
            Negation negation => "-" + Slot(negation.Operand, 8),
            Complement complement => "not " + Slot(complement.Operand, 4),
            Arithmetic arithmetic => Slot(arithmetic.Left, Tier(arithmetic)) + $" {arithmetic.Op} " + Slot(arithmetic.Right, Tier(arithmetic) + 1),
            Selection selection => Slot(selection.Target, 10) + ":0",
            _ => throw new InvalidOperationException(tree.ToString()),
        };
    }

    private static string WriteRoot(Tree tree) => tree.Grouped ? $"({Write(tree)})" : Write(tree);

    /// <summary>The tree's shape: parentheses are invisible, a chain is ONE node.</summary>
    private static string ModelShape(Tree tree) => tree switch
    {
        Leaf { Literal: bool truth } => truth ? "true" : "false",
        Leaf leaf => Convert.ToString(leaf.Literal, CultureInfo.InvariantCulture)!,
        ChainNode chain => "cmp[" + string.Join(" ", chain.Links.Select(link => link.Op)) + "]("
            + string.Join(", ", chain.Links.Select(link => link.Operand).Prepend(chain.First).Select(ModelShape)) + ")",
        Negation negation => $"neg({ModelShape(negation.Operand)})",
        Complement complement => $"not({ModelShape(complement.Operand)})",
        Arithmetic arithmetic => $"{arithmetic.Op}({ModelShape(arithmetic.Left)}, {ModelShape(arithmetic.Right)})",
        Selection selection => $"index({ModelShape(selection.Target)}, 0)",
        _ => throw new InvalidOperationException(tree.ToString()),
    };

    private static string ParsedShape(Expr expr) => expr switch
    {
        Expr.Num(var value) => value.ToString(CultureInfo.InvariantCulture),
        Expr.BoolLiteral(var truth) => truth ? "true" : "false",
        Expr.Comparison chain => "cmp[" + string.Join(" ", chain.Links.Select(link => ExprNameRenderer.ComparisonOpText(link.Op))) + "]("
            + string.Join(", ", chain.Links.Select(link => link.Operand).Prepend(chain.First).Select(ParsedShape)) + ")",
        Expr.Unary(UnaryOp.Minus, var operand) => $"neg({ParsedShape(operand)})",
        Expr.Unary(UnaryOp.Not, var operand) => $"not({ParsedShape(operand)})",
        Expr.Binary(var op, var left, var right) => $"{ExprNameRenderer.BinaryOpText(op)}({ParsedShape(left)}, {ParsedShape(right)})",
        Expr.Index(var target, var selector) => $"index({ParsedShape(target)}, {ParsedShape(selector)})",
        _ => $"<{expr.GetType().Name}>",
    };

    /// <summary>
    /// The value model of a tree: numbers and Booleans; arithmetic, negation, and ordering take
    /// numbers only, `not` a Boolean only, equality is total, `:0` of a scalar is that scalar;
    /// <c>null</c> is a type mismatch. A chain follows the chain law (first error wins, eager
    /// past false).
    /// </summary>
    private static object? Evaluate(Tree tree)
    {
        switch (tree)
        {
            case Leaf leaf:
                return leaf.Literal is bool ? leaf.Literal : Convert.ToInt64(leaf.Literal, CultureInfo.InvariantCulture);
            case Selection selection:
                return Evaluate(selection.Target);
            case Negation negation:
                return Evaluate(negation.Operand) is long number ? -number : null;
            case Complement complement:
                return Evaluate(complement.Operand) is bool truth ? !truth : null;
            case Arithmetic arithmetic:
            {
                var left = Evaluate(arithmetic.Left);
                if (left is null) return null;
                var right = Evaluate(arithmetic.Right);
                if (left is not long x || right is not long y) return null;
                return arithmetic.Op switch { "+" => x + y, "-" => x - y, _ => x * y };
            }

            case ChainNode chain:
            {
                var previous = Evaluate(chain.First);
                if (previous is null) return null;
                var holds = true;
                foreach (var (op, operand) in chain.Links)
                {
                    var next = Evaluate(operand);
                    if (next is null) return null;
                    bool link;
                    if (op is "==" or "!=")
                    {
                        link = previous.Equals(next) == (op == "==");
                    }
                    else
                    {
                        if (previous is not long x || next is not long y) return null;
                        link = op switch { "<" => x < y, "<=" => x <= y, ">" => x > y, _ => x >= y };
                    }

                    holds &= link;
                    previous = next;
                }

                return holds;
            }

            default:
                throw new InvalidOperationException(tree.ToString());
        }
    }

    private static Tree Generate(Random random, int depth)
    {
        Tree tree;
        var kind = depth == 0 ? 0 : random.Next(10);
        if (kind <= 2)
        {
            tree = new Leaf(random.Next(5) == 0 ? random.Next(2) == 0 : (object)random.Next(1, 4));
        }
        else if (kind <= 5)
        {
            tree = GenerateChain(random, depth);
        }
        else if (kind == 6)
        {
            tree = new Arithmetic(random.Next(3) switch { 0 => "+", 1 => "-", _ => "*" }, Generate(random, depth - 1), Generate(random, depth - 1));
        }
        else if (kind == 7)
        {
            tree = new Negation(Generate(random, depth - 1));
        }
        else if (kind == 8)
        {
            tree = new Complement(Generate(random, depth - 1));
        }
        else
        {
            tree = new Selection(Generate(random, depth - 1));
        }

        return random.Next(6) == 0 ? tree with { Grouped = true } : tree;
    }

    private static ChainNode GenerateChain(Random random, int depth)
    {
        var first = Generate(random, depth - 1);
        var links = Enumerable.Range(0, random.Next(1, 4))
            .Select(_ => (Operators[random.Next(Operators.Length)], Generate(random, depth - 1)))
            .ToArray();
        return new ChainNode(first, links);
    }

    /// <summary>Every chain in the tree with an operand that is itself a chain: (outer, operand position).</summary>
    private static IEnumerable<(ChainNode Outer, int Position)> NestedChainOperands(Tree tree)
    {
        IEnumerable<Tree> Children(Tree node) => node switch
        {
            ChainNode chain => chain.Links.Select(link => link.Operand).Prepend(chain.First),
            Negation negation => [negation.Operand],
            Complement complement => [complement.Operand],
            Arithmetic arithmetic => [arithmetic.Left, arithmetic.Right],
            Selection selection => [selection.Target],
            _ => [],
        };

        if (tree is ChainNode outer)
        {
            var operands = outer.Links.Select(link => link.Operand).Prepend(outer.First).ToArray();
            for (var position = 0; position < operands.Length; position++)
            {
                if (operands[position] is ChainNode)
                    yield return (outer, position);
            }
        }

        foreach (var child in Children(tree))
        {
            foreach (var nested in NestedChainOperands(child))
                yield return nested;
        }
    }

    /// <summary><paramref name="tree"/> with the chain operand at <paramref name="position"/> of <paramref name="outer"/> MERGED into it.</summary>
    private static Tree Merge(Tree tree, ChainNode outer, int position)
    {
        if (ReferenceEquals(tree, outer))
        {
            var operands = outer.Links.Select(link => link.Operand).Prepend(outer.First).ToList();
            var ops = outer.Links.Select(link => link.Op).ToList();
            var inner = (ChainNode)operands[position];
            operands.RemoveAt(position);
            operands.InsertRange(position, inner.Links.Select(link => link.Operand).Prepend(inner.First));
            ops.InsertRange(position, inner.Links.Select(link => link.Op));
            return outer with { First = operands[0], Links = [.. ops.Select((op, index) => (op, operands[index + 1]))] };
        }

        return tree switch
        {
            ChainNode chain => chain with
            {
                First = Merge(chain.First, outer, position),
                Links = [.. chain.Links.Select(link => (link.Op, Merge(link.Operand, outer, position)))],
            },
            Negation negation => negation with { Operand = Merge(negation.Operand, outer, position) },
            Complement complement => complement with { Operand = Merge(complement.Operand, outer, position) },
            Arithmetic arithmetic => arithmetic with { Left = Merge(arithmetic.Left, outer, position), Right = Merge(arithmetic.Right, outer, position) },
            Selection selection => selection with { Target = Merge(selection.Target, outer, position) },
            _ => tree,
        };
    }

    [Fact]
    public async Task GeneratedTrees_ParenthesesAloneSeparateNestedComparisons_InTheTreeItsNamesAndItsValue()
    {
        // 1,200 deterministic trees mixing chains, parenthesized nested chains (left, middle, and
        // right operands), `not`, prefix minus, arithmetic, and a postfix `:0` receiver, with
        // redundant parentheses sprinkled anywhere. For each tree:
        //   * the parsed tree is the model tree (parentheses invisible, a chain one node);
        //   * both diagnostic spellings read back as the same tree;
        //   * dropping the parentheses around a nested chain operand MERGES it into the outer
        //     chain — a different tree, exactly the merged model — so the parentheses are what
        //     kept it nested;
        //   * the value (or type mismatch) is the model's, on the generic strategy and — for
        //     every fifth tree — the planned loop and the async twin.
        var random = new Random(0x7EE5);
        var mismatches = new List<string>();
        var nestedPairs = 0;
        const int Samples = 1_200;
        for (var sample = 0; sample < Samples; sample++)
        {
            Tree tree = random.Next(10) switch
            {
                < 7 => GenerateChain(random, 3),
                7 or 8 => new Complement(GenerateChain(random, 3)),
                _ => new Selection(GenerateChain(random, 3)),
            };
            if (random.Next(8) == 0)
                tree = tree with { Grouped = true };

            var source = WriteRoot(tree);
            var parsed = Parser.ParseSyntax(source);
            if (parsed.HasErrors || parsed.Root.Output is not [var expr])
            {
                mismatches.Add($"`{source}` did not parse to one row: {string.Join("; ", parsed.Diagnostics)}");
                continue;
            }

            var shape = ModelShape(tree);
            if (ParsedShape(expr) != shape)
            {
                mismatches.Add($"`{source}` parsed as {ParsedShape(expr)}, expected {shape}");
                continue;
            }

            foreach (var mode in new[] { ExprNameMode.DiagnosticName, ExprNameMode.Open })
            {
                var rendered = ExprNameRenderer.Render(expr, mode);
                var reparsed = Parser.ParseSyntax(rendered);
                if (reparsed.HasErrors || reparsed.Root.Output is not [var readBack] || ParsedShape(readBack) != shape)
                    mismatches.Add($"`{source}` renders ({mode}) as `{rendered}`, which does not read back as {shape}");
            }

            foreach (var (outer, position) in NestedChainOperands(tree))
            {
                nestedPairs++;
                var operand = position == 0 ? outer.First : outer.Links[position - 1].Operand;
                var flattened = Write(tree, ungrouped: operand);
                if (tree.Grouped)
                    flattened = $"({flattened})";
                var flatParse = Parser.ParseSyntax(flattened);
                var merged = ModelShape(Merge(tree, outer, position));
                if (flatParse.HasErrors || flatParse.Root.Output is not [var flatExpr] || ParsedShape(flatExpr) != merged || merged == shape)
                    mismatches.Add($"`{source}` without the parentheses of operand {position} (`{flattened}`) should be the merged chain {merged}");
            }

            var expected = Evaluate(tree);
            var run = KatLangEngine.Run(source);
            var observed = run switch
            {
                RunResult.Success success => success.ToDisplayString(),
                RunResult.EvalFailure failure when failure.Errors is [{ Code: KatLangErrorCode.TypeMismatch }] => "type",
                _ => run.ToDisplayString(),
            };
            var predicted = expected switch { null => "type", bool truth => truth ? "true" : "false", _ => expected.ToString() };
            if (observed != predicted)
            {
                mismatches.Add($"`{source}` evaluated to {observed}, expected {predicted}");
                continue;
            }

            if (sample % 5 == 0 && expected is not long)
            {
                var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid($"Step = {{\n    n + if({source}, 1, 0)\n}}\nStep.repeat(1, 0)").Root);
                var (planned, _) = Evaluator.RunCountedObserved(program, enableOptimizations: true);
                var (generic, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
                var (twin, _) = await AsyncEvaluationHarness.Complete(
                    Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));
                var loopExpected = expected is bool truth ? $"ok raw={(truth ? 1 : 0)} n=1" : "type";
                foreach (var (name, result) in new[] { ("planned", planned), ("generic", generic), ("async", twin) })
                {
                    var neutral = result.IsError ? (result.Error.Code == KatLangErrorCode.TypeMismatch ? "type" : result.Error.ToString()) : AsyncEvaluationHarness.NeutralOf(result);
                    if (neutral != loopExpected)
                        mismatches.Add($"{name} loop over `{source}`: {neutral}, expected {loopExpected}");
                }

                if (generic.IsError && planned.IsError && generic.Error.ToString() != planned.Error.ToString())
                    mismatches.Add($"`{source}`: planned {planned.Error} differs from generic {generic.Error}");
            }
        }

        Assert.True(nestedPairs > 500, $"only {nestedPairs} nested chain operands were generated");
        AssertNoMismatch(mismatches, Samples);
    }

    // ── Named forms: precedence around the tier, operand errors, recovery, width ──

    [Theory]
    // `not` sits below the whole chain; a grouped `not` is an ordinary chain operand.
    [InlineData("not 1 < 2", "not(cmp[<](1, 2))", "false")]
    [InlineData("not 1 == 2", "not(cmp[==](1, 2))", "true")]
    [InlineData("not 1 < 2 < 3", "not(cmp[< <](1, 2, 3))", "false")]
    [InlineData("not 3 < 2 < true", "not(cmp[< <](3, 2, true))", "type")]
    [InlineData("not (1 < 2)", "not(cmp[<](1, 2))", "false")]
    [InlineData("(not true) == false", "cmp[==](not(true), false)", "true")]
    [InlineData("(not 1 < 2) == false != true", "cmp[== !=](not(cmp[<](1, 2)), false, true)", "true")]
    // Arithmetic, prefix minus, and `^` bind inside an operand exactly as they do alone.
    [InlineData("-2 ^ 2 < -3", "cmp[<](neg(^(2, 2)), neg(3))", "true")]
    [InlineData("(-2) ^ 2 < -3", "cmp[<](^(neg(2), 2), neg(3))", "false")]
    [InlineData("1 < -2 ^ 2", "cmp[<](1, neg(^(2, 2)))", "false")]
    [InlineData("1 < (-2) ^ 2", "cmp[<](1, ^(neg(2), 2))", "true")]
    [InlineData("1 + 1 < 2 * 2 == 2 ^ 2", "cmp[< ==](+(1, 1), *(2, 2), ^(2, 2))", "true")]
    [InlineData("(1 + 1 < 2 * 2) == 2 ^ 2", "cmp[==](cmp[<](+(1, 1), *(2, 2)), ^(2, 2))", "false")]
    [InlineData("1 + 1 < (2 * 2 == 2 ^ 2)", "cmp[<](+(1, 1), cmp[==](*(2, 2), ^(2, 2)))", "type")]
    // Parentheses break a chain on either side, and a grouped chain is a postfix receiver.
    [InlineData("(1 < 2) < 3", "cmp[<](cmp[<](1, 2), 3)", "type")]
    [InlineData("1 < (2 < 3)", "cmp[<](1, cmp[<](2, 3))", "type")]
    [InlineData("(1 < 2) == true", "cmp[==](cmp[<](1, 2), true)", "true")]
    [InlineData("1 == (1 < 2)", "cmp[==](1, cmp[<](1, 2))", "false")]
    [InlineData("(1 < 2 < 3):0 == true", "cmp[==](index(cmp[< <](1, 2, 3), 0), true)", "true")]
    public void NamedForms_ParseAndEvaluateAsTheLadderPrescribes(string source, string shape, string value)
    {
        Assert.Equal(shape, ParsedShape(Assert.Single(SourceProvenance.ParseValid(source).Root.Output)));
        var run = KatLangEngine.Run(source);
        var observed = run is RunResult.EvalFailure { Errors: [{ Code: KatLangErrorCode.TypeMismatch }] } ? "type" : run.ToDisplayString();
        Assert.Equal(value, observed);
    }

    [Theory]
    [InlineData("1 / 0 < 2 < true", 1, 6)]
    [InlineData("1 < 1 / 0 < true", 5, 10)]
    [InlineData("1 < 2 < 1 / 0", 9, 14)]
    [InlineData("3 < 2 < (1 / 0) < true", 9, 16)]
    public void AnOperandsOwnError_IsThatOperandsError_NeverALinksRejection(string source, int start, int end)
    {
        // An operand that fails ends the chain with ITS error at ITS span — no comparison context
        // is attached (the link was never applied), and a later invalid link is never reached.
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors);
        Assert.Equal(KatLangErrorCode.DivisionByZero, error.Code);
        Assert.Equal(new SourceSpan(1, start, 1, end), error.Span);
        Assert.DoesNotContain("while evaluating", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("a < b ==\nGood = 41\nGood", "cmp[< ==](a, b, 0)")]
    [InlineData("a < b <\nGood = 41\nGood", "cmp[< <](a, b, 0)")]
    [InlineData("(a < b) ==\nGood = 41\nGood", "cmp[==](cmp[<](a, b), 0)")]
    [InlineData("a < (b <)\nGood = 41\nGood", "cmp[<](a, cmp[<](b, 0))")]
    [InlineData("a < (b == )\nGood = 41\nGood", "cmp[<](a, cmp[==](b, 0))")]
    public void AMalformedChain_KeepsItsWrittenLinks_AndTheNextDeclaration(string source, string recovered)
    {
        // One diagnostic on the malformed line; the missing operand is a placeholder link (the
        // written operator count survives, so the tree never reads as a shorter valid chain or
        // a merged one), and the next line's declaration keeps its own scope and row.
        var parsed = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(1, diagnostic.Span!.Value.Start.Line);
        Assert.Equal(recovered, RecoveredShape(parsed.Root.Output[0]));
        var good = Assert.Single(parsed.Root.Properties, property => property.Name == "Good");
        Assert.Equal(2, good.DeclarationSpans[0].Start.Line);
        Assert.Equal("Good", Assert.IsType<Expr.Resolve>(parsed.Root.Output[^1]).Name);
    }

    private static string RecoveredShape(Expr expr) => expr switch
    {
        Expr.Resolve(var name) => name,
        Expr.Comparison chain => "cmp[" + string.Join(" ", chain.Links.Select(link => ExprNameRenderer.ComparisonOpText(link.Op))) + "]("
            + string.Join(", ", chain.Links.Select(link => link.Operand).Prepend(chain.First).Select(RecoveredShape)) + ")",
        _ => ParsedShape(expr),
    };

    [Fact]
    public void AWideChain_IsOneFlatNode_AndItsFailingLastLink_IsReportedAlone_WithinBounds()
    {
        // 20,000 operands parse to ONE node with 20,000 links (a flat representation, one
        // chain-depth level), evaluate iteratively, and a rejection of the LAST link names
        // exactly that link at its own span. Grouped as the first operand of an outer failing
        // link, the whole chain's name is bounded by the renderer's output limit.
        var operands = string.Join(" < ", Enumerable.Range(0, 20_000));
        var source = operands + " < true";
        var chain = Assert.IsType<Expr.Comparison>(Assert.Single(SourceProvenance.ParseValid(source).Root.Output));
        Assert.Equal(20_000, chain.Links.Count);

        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.StartsWith("while evaluating `19999 < true`:", error.Message, StringComparison.Ordinal);
        var lastOperandStart = source.Length - "19999 < true".Length + 1;
        Assert.Equal(new SourceSpan(1, lastOperandStart, 1, source.Length + 1), error.Span);

        var grouped = Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run($"({operands}) < true")).Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, grouped.Code);
        Assert.StartsWith("while evaluating `(0 < 1 < 2", grouped.Message, StringComparison.Ordinal);
        Assert.Contains(ExprNameRenderer.TruncationMarker, grouped.Message, StringComparison.Ordinal);
        Assert.True(grouped.Message.Length < ExprNameRenderer.MaxRenderedNameLength + 512, $"{grouped.Message.Length} characters");
    }
}
