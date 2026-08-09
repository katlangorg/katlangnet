namespace KatLang.Tests;

/// <summary>
/// Generated optimized-versus-generic equivalence sweep for the two evaluator
/// optimizers (the loop planner in <c>Optimizations/Loops</c> and the
/// filter/count fusion in <c>Optimizations/Sequences</c>).
///
/// <para><b>Why this exists.</b> Both optimizers replace the generic evaluator
/// on their eligible shapes — the loop planner runs a whole loop through its
/// own expression evaluator (<c>LoopExprPlan</c> / <c>LoopRunFrame</c>), and
/// fusion never evaluates the <c>filter</c> node at all. The fuzz layer's
/// Phase 3 optimizer family already compares the two policies, but on a small
/// table of hand-picked reviewed sources whose declared optimizer path is
/// asserted. This sweep is the complementary breadth check: it crosses every
/// binary operator with every value KIND (atom, empty sequence, sequence
/// value, exact list, string, captured property) in every loop-body position
/// (next-state slot, continuation slot, one- and two-slot state) and every
/// recognized fusion spelling, and asserts only that the optimized and generic
/// executions observe the SAME value, emitted count, and error category.</para>
///
/// <para><b>Termination gate.</b> A configured step budget forces the generic
/// path (see <c>Evaluator.CreateRootCtx</c>), so the optimized side cannot be
/// bounded by limits. Generated <c>while</c> programs can legitimately fail to
/// terminate, so each case is first probed under a step budget; a program that
/// exhausts it is skipped rather than compared. Every family asserts that it
/// actually compared a substantial number of cases, so a generator change that
/// silently made everything non-terminating cannot pass as a green sweep.</para>
/// </summary>
public class OptimizerEquivalenceSweepTests
{
    /// <summary>Termination probe budget. Every intentionally-terminating case here needs far fewer steps.</summary>
    private static readonly EvaluationLimits ProbeLimits = new() { MaxSteps = 20_000 };

    private static readonly string[] BinaryOps =
        ["+", "-", "*", "/", "div", "mod", "^", "<", ">", "<=", ">=", "==", "!=", "and", "or", "xor"];

    /// <summary>One literal or captured property per value kind the loop frame can carry.</summary>
    private static readonly string[] Operands =
        ["0", "1", "2", "-1", "()", "(1, 2)", "[1, 2]", "[]", "'ab'", "Cst", "Lst", "Str", "Seq", "Emp"];

    private static readonly string[] Inits = ["0", "1", "3", "()", "[1, 2]", "'ab'", "(1, 2)"];

    private const string Prelude =
        "Cst = 3\n" +
        "Lst = [1, 2]\n" +
        "Str = 'ab'\n" +
        "Seq = (1, 2)\n" +
        "Emp = ()\n" +
        "Dbl(a) = a * 2\n" +
        "Pred(a) = a > 1\n";

    private sealed class SweepResult
    {
        public int Compared { get; set; }

        public int Skipped { get; set; }

        public List<string> Mismatches { get; } = [];

        public void AssertClean(int minimumCompared)
        {
            Assert.True(
                Mismatches.Count == 0,
                $"{Mismatches.Count} optimized/generic mismatches out of {Compared} compared "
                + $"({Skipped} skipped as non-terminating):\n"
                + string.Join("\n", Mismatches.Take(25)));
            Assert.True(
                Compared >= minimumCompared,
                $"Only {Compared} cases were comparable (expected at least {minimumCompared}); "
                + $"{Skipped} were skipped as non-terminating. The generator degenerated.");
        }
    }

    private static string Neutral(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? "err " + SemanticExplorerHarness.ErrorCategory(result.Error)
            : $"ok raw={SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount}";

    private static void Compare(string id, string source, SweepResult sweep)
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
            return;

        var expr = new Expr.AlgorithmExpr(parsed.Root);

        var probe = Evaluator.RunCountedObserved(expr, ProbeLimits, enableOptimizations: false).Result;
        if (probe.IsError && SemanticExplorerHarness.ErrorCategory(probe.Error) == "evaluationStepLimitExceeded")
        {
            sweep.Skipped++;
            return;
        }

        sweep.Compared++;
        var optimized = Neutral(Evaluator.RunCountedObserved(expr, enableOptimizations: true).Result);
        var generic = Neutral(Evaluator.RunCountedObserved(expr, enableOptimizations: false).Result);
        if (optimized != generic)
        {
            sweep.Mismatches.Add(
                $"{id}\n  source:    {source.Replace("\n", " | ")}\n  optimized: {optimized}\n  generic:   {generic}");
        }
    }

    [Fact]
    public void RepeatStepBodies_OptimizedMatchesGeneric()
    {
        var sweep = new SweepResult();
        foreach (var op in BinaryOps)
        {
            foreach (var operand in Operands)
            {
                foreach (var init in Inits)
                {
                    Compare(
                        $"repeat/{op}/{operand}/{init}",
                        $"{Prelude}S(x) = x {op} {operand}\nrepeat(S, 3, {init})",
                        sweep);
                }
            }
        }

        sweep.AssertClean(1_000);
    }

    [Fact]
    public void WhileStepBodies_OptimizedMatchesGeneric()
    {
        var sweep = new SweepResult();
        foreach (var op in BinaryOps)
        {
            foreach (var operand in Operands)
            {
                foreach (var init in Inits)
                {
                    // One state slot; the continuation is a literal, so exactly one iteration runs.
                    Compare(
                        $"while1/{op}/{operand}/{init}",
                        $"{Prelude}S(x) = x {op} {operand}, 0\nwhile(S, {init})",
                        sweep);

                    // Two slots: slot 0 is a bounded counter, slot 1 carries the tested expression.
                    Compare(
                        $"while2/{op}/{operand}/{init}",
                        $"{Prelude}S(k, y) = k - 1, y {op} {operand}, k > 0\nwhile(S, 3, {init})",
                        sweep);

                    // The tested expression IS the continuation slot.
                    Compare(
                        $"whileCont/{op}/{operand}/{init}",
                        $"{Prelude}S(k, y) = k - 1, y, if(k > 0, y {op} {operand}, 0)\nwhile(S, 3, {init})",
                        sweep);
                }
            }
        }

        sweep.AssertClean(3_000);
    }

    /// <summary>
    /// Body shapes rather than operators: every <c>LoopExprPlan</c> node kind
    /// (constant, string constant, state slot, captured slot, temp slot,
    /// unary, binary, planned <c>if</c>) plus the shapes that force the
    /// planner's <c>Fallback</c> arm (index, spread, dot-call, block, list,
    /// nested calls) and the emission counts that force a mid-loop handover to
    /// the generic continuation.
    /// </summary>
    [Fact]
    public void LoopBodyShapes_OptimizedMatchesGeneric()
    {
        var bodies = new[]
        {
            "x", "-x", "not x", "- -x",
            "if(x > 1, x - 1, x)", "if(x, x - 1, 0)", "if(x == 1, 'a', 0)",
            "if(x, (), 1)", "if(x, (1, 2), 3)", "if(x, [1], 2)",
            "if(Str, 1, 2)", "if(Lst, 1, 2)", "if(Emp, 1, 2)",
            "count(x)", "x.count", "Dbl(x)", "x:0", "(x)", "(x, 9):0", "[x]:0", "x*",
            "Tmp", "Tmp + x", "x + count('ab')",
            "range(1, x).count", "filter(range(1, 3), Pred).count",
            "x / 0", "x mod 0", "1 / x", "x ^ -1",
            "Lst:0 + x", "Seq:1 + x", "Emp + x", "Str == 'ab'",
            "sum((x, 1))", "reduce((1, 2), Add, x)",
        };

        const string extra = "Tmp = 5\nAdd(a, b) = a + b\n";
        var sweep = new SweepResult();
        foreach (var body in bodies)
        {
            foreach (var init in Inits)
            {
                Compare($"repeatBody/{body}/{init}", $"{Prelude}{extra}S(x) = {body}\nrepeat(S, 2, {init})", sweep);
                Compare($"whileBody1/{body}/{init}", $"{Prelude}{extra}S(x) = {body}, 0\nwhile(S, {init})", sweep);
                Compare(
                    $"whileBody2/{body}/{init}",
                    $"{Prelude}{extra}S(k, x) = k - 1, {body}, k > 0\nwhile(S, 2, {init})",
                    sweep);
                Compare(
                    $"whileCont/{body}/{init}",
                    $"{Prelude}{extra}S(k, x) = k - 1, x, if(k > 0, {body}, 0)\nwhile(S, 2, {init})",
                    sweep);
            }
        }

        sweep.AssertClean(700);
    }

    /// <summary>
    /// Every recognized filter/count spelling (dot-dot, plain-count over a dot
    /// filter, plain-count over a plain filter) and the non-fusable control
    /// (a captured intermediate), crossed with direct-range, list, sequence,
    /// string, spread, and non-collection sources, and with predicates that
    /// keep, drop, fail, return a string, return a list, or are a builtin.
    /// </summary>
    [Fact]
    public void FilterCountFusion_OptimizedMatchesGeneric()
    {
        var sources = new[]
        {
            "range(1, 5)", "range(5, 1)", "range(3, 3)", "[1, 2, 3]", "[]", "[[1, 2], [3]]", "['a', 'bc']",
            "(1, 2, 3)", "()", "7", "'ab'", "Src", "Src*", "(Src*)", "range(1, 3)*", "[1, 2, 3]*",
        };
        var predicates = new[] { "Pred", "Always", "Never", "Boom", "StrP", "count", "min", "Dbl" };

        const string extra =
            "Src = [1, 2, 3]\nAlways(a) = 1\nNever(a) = 0\nBoom(a) = a / 0\nStrP(a) = 'x'\n";

        var sweep = new SweepResult();
        foreach (var source in sources)
        {
            foreach (var predicate in predicates)
            {
                Compare($"dot-dot/{source}/{predicate}", $"{Prelude}{extra}{source}.filter({predicate}).count", sweep);
                Compare($"plain-dot/{source}/{predicate}", $"{Prelude}{extra}count({source}.filter({predicate}))", sweep);
                Compare($"plain-plain/{source}/{predicate}", $"{Prelude}{extra}count(filter({source}, {predicate}))", sweep);
                Compare(
                    $"unfused/{source}/{predicate}",
                    $"{Prelude}{extra}Kept = filter({source}, {predicate})\ncount(Kept)",
                    sweep);
            }
        }

        sweep.AssertClean(400);
    }

    /// <summary>
    /// Hand-written interaction cases the generated families cannot express:
    /// loops inside callbacks (a counted-parameter environment), nested loops,
    /// a step-local property (a temp slot), state that changes VALUE KIND
    /// mid-loop (the <c>TryCommitScratchFast</c> handover), spread and
    /// zero-emission step outputs, and errors raised inside a planned branch.
    /// </summary>
    [Fact]
    public void LoopInteractions_OptimizedMatchesGeneric()
    {
        var programs = new (string Id, string Source)[]
        {
            ("loop-in-callback", "Inner(x) = x + 1\nM(a) = repeat(Inner, a, 0)\nmap((1, 2, 3), M)"),
            ("loop-in-callback-while", "Inner(x) = x - 1, x > 0\nM(a) = while(Inner, a)\nmap((1, 2, 3), M)"),
            ("nested-loops", "Inner(y) = y + 1\nOuter(x) = repeat(Inner, 2, x)\nrepeat(Outer, 3, 0)"),
            ("loop-temp-property", "S(x) = {\n    T = x * 2\n    T + 1\n}\nrepeat(S, 3, 1)"),
            ("loop-counted-param", "Step(x) = x + 1\nM(a) = repeat(Step, 2, a)\nmap(((1, 2), 3), M)"),
            ("loop-reduce-callback", "Add(a, b) = a + b\nS(x) = reduce((1, 2), Add, x)\nrepeat(S, 3, 0)"),
            ("state-becomes-list", "S(x) = if(x > 0, x - 1, [1, 2])\nrepeat(S, 3, 2)"),
            ("state-becomes-string", "S(x) = if(x > 0, x - 1, 'ab')\nrepeat(S, 3, 2)"),
            ("state-becomes-sequence", "S(x) = if(x > 0, x - 1, (1, 2))\nrepeat(S, 3, 2)"),
            ("state-becomes-empty", "S(x) = if(x > 0, x - 1, ())\nrepeat(S, 3, 2)"),
            ("while-state-becomes-sequence", "S(x) = if(x > 0, x - 1, (1, 2)), 1\nwhile(S, 2)"),
            // A bounded counter drives the loop so the state slot can become `()`
            // (and stay `()`, which is transparent to `>` and would otherwise
            // never falsify a numeric continuation) without looping forever.
            ("while-state-becomes-empty", "S(k, x) = k - 1, if(k > 1, x - 1, ()), k > 0\nwhile(S, 3, 2)"),
            ("multi-slot-state-kind-change", "S(x, y) = y, if(x > 0, x - 1, (1, 2))\nrepeat(S, 3, 2, 2)"),
            ("step-shadows-outer-name", "x = 99\nS(x) = x + 1\nrepeat(S, 3, 0)"),
            ("cached-property-in-step", "P = 1, 2\nS(x) = x + P.count\nrepeat(S, 3, 0)"),
            ("native-call-in-step", "S(x) = x + Math.Abs(-1)\nrepeat(S, 3, 0)"),
            ("div-zero-late", "S(x) = 10 div (x - 2)\nrepeat(S, 4, 0)"),
            ("div-zero-in-continuation", "S(x) = x + 1, 10 div (x - 2)\nwhile(S, 0)"),
            ("string-state-planned", "S(x) = x\nrepeat(S, 3, 'ab')"),
            ("error-in-planned-branch", "S(x) = if(x > 1, x - 1, min(()))\nrepeat(S, 4, 3)"),
            ("spread-step-output", "S(x) = (x, 1)*\nrepeat(S, 2, 0)"),
            ("spread-while-output", "S(x) = (x - 1, x > 0)*\nwhile(S, 3)"),
            ("zero-emission-step", "S(x) = ()\nrepeat(S, 2, 1)"),
            ("zero-emission-while", "S(x) = (), 0\nwhile(S, 1)"),
        };

        var sweep = new SweepResult();
        foreach (var (id, source) in programs)
            Compare(id, source, sweep);

        sweep.AssertClean(programs.Length);
    }
}
