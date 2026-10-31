using KatLang.Evaluation;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests.InvocationRoute;

/// <summary>
/// META-S3-4: the generalized invocation-capture corpus, promoted from the independently reviewed
/// META-S3-4-R research matrix (164 distinct case programs: 94 matrix cases, the 25 original
/// ordinary/planned VALUE-equivalence pairs and the reviewer's 10 added pairs <c>EQ101</c>–<c>EQ110</c>).
/// Every case runs on the synchronous generic evaluator (mode 0), the synchronous optimized evaluator
/// (mode 1) and the asynchronous engine (mode 2, with the genuinely asynchronous host operations
/// <c>aflag</c> and <c>stop</c>). An observation records the outcome (value, or error code with its full
/// rendered message and span, or cancellation / the original host exception), the emitted count, host
/// effects in order, consumed semantic steps, raw expression checkpoints and materialization counters —
/// plus, outside the compared semantics, loop-optimizer hits, plan and supply-formation counts and real
/// suspensions.
/// </summary>
internal static class InvocationRouteCorpus
{
    /// <summary>The shared library (identical line count in both variants, so spans compare directly).</summary>
    internal const string Core = """
        IsBig(x) = x > 1
        Square(x) = trace(x) * x
        Inc(x) = x + 1
        Add(a, b) = a + b
        Step(x) = x + 1, x < 3
        Id(x) = x
        Apply(f, x) = f(x)
        Box = {
          Step(x) = x + 1, x < 3
          G(x) = x * 10
          V = tick()
          Sq = Square
        }
        Lib = { Sub = { G(x) = x * 2 } }
        Fam(0) = {
          Q(x) = x
          0
        }
        Fam(n) = n

        """;

    /// <summary>The META consumers (the J7 gate retains plans in a program that spells <c>meta</c>).</summary>
    internal const string Meta = "Capture(meta operation) = operation\nInspect(meta operation) = operation.Arguments.count\nKeep(meta op) = op\n";

    /// <summary>The META-free padding of the same line count: supplied invocations are ordinary cells.</summary>
    internal const string Plain = "Pad1 = 1\nPad2 = 2\nPad3 = 3\n";

    internal const string ModuleUrl = "https://modules.example/m.kat";
    internal const string ModuleText = "public Inc2(x) = x + 2\npublic Add2(x, y) = x + y";

    internal sealed record Case(string Id, string Source, bool Plain = false, bool AsyncOnly = false, string? Module = null,
        bool WithCancel = false, EvaluationLimits? Limits = null);

    private const string LoopDot = "Loop(meta op) = op.Algorithm(op.Arguments*).while\n";

    internal static readonly Case[] Cases =
    [
        // A — the reconstructed R.Algorithm invocation (the motivating wrapper)
        new("A1", LoopDot + "Step(0).Loop"),
        new("A2", "Loop(meta op) = while(op.Algorithm(op.Arguments*))\nStep(0).Loop"),
        new("A3", LoopDot + "Loop(Step(0)), Loop(Step(2)), Loop(Box.Step(1))"),
        new("A4", "Loop(meta op) = (op.Algorithm)(op.Arguments*).while\nStep(0).Loop"),
        new("A5", LoopDot + "if(aflag(), Step(0).Loop, 0)"),
        new("A6", LoopDot + "T(x) = x + Step(0).Loop, x < 10\nT(0).Loop, T(0).while"),
        new("A7", LoopDot + "Step(trace(0)).Loop"),
        new("A8", "Loop(meta op) = (op.Arguments.count, op.Algorithm(op.Arguments*).while, op.Invoke())\nStep(trace(0)).Loop"),
        new("A9", LoopDot + "Step([1][5]*).Loop, 0"),
        new("A9c", "Step([1][5]*).while, 0"),
        new("A10", LoopDot + "Loop2(meta op) = op.Algorithm(op.Arguments*).Loop\nStep(0).Loop2"),
        // B — the repeat wrapper
        new("B1", "Repeat(meta op, count) =\n    op.Algorithm(op.Arguments*).repeat(count)\nInc(0).Repeat(5)"),
        new("B2", "Repeat(meta op, n) = repeat(op.Algorithm(op.Arguments*), n)\nInc(0).Repeat(5)"),
        new("B3", "Repeat(meta op, n) = op.Algorithm(op.Arguments*).repeat(n)\nBox.G(1).Repeat(2)"),
        // C — qualified structural member calls
        new("C1", "Box.Step(0).while"),
        new("C2", "while(Box.Step(0))"),
        new("C3", "(Box.Step)(0).while"),
        new("C4", "Box.G(1).repeat(2)"),
        new("C5", "Lib.Sub.G(1).repeat(3)"),
        new("C6", "Box.Sq(3).repeat(1)"),
        new("C7", "Use(b) = b.Step(0).while\nUse(Box)"),
        // D — qualified module/builtin calls
        new("D1", "Math.Abs(-3).repeat(2)"),
        new("D2", "A = Math.Abs\nA(-3).repeat(2)"),
        new("D3", "repeat(Math.Abs(-3), 2)"),
        new("D4", "abs(-3).repeat(2)"),
        new("D5", "Math.Sqrt(16).repeat(1)"),
        // E — ordinary user-defined META consumers
        new("E1", "Inspect(Math.Abs(-3))"),
        new("E2", "Inspect(Box.G(1))"),
        new("E3", "Inspect(5.Add(1))"),
        new("E4", "R = Capture(Square(5))\nInspect(R.Algorithm(4, 5))"),
        new("E5", "Inspect(Lib.Sub.G(1)), Inspect((Box.G)(1))"),
        new("E6", "Inspect(Box.V())"),
        new("E7", "Inspect(Box.G(1).Inc)"),
        new("E8", "Inspect(5.Inc)"),
        new("E9", "Inspect(Box.G)"),
        new("E10", "R = Capture(Square(5))\nA = R.Algorithm\nInspect(A(9))"),
        new("E11", "Two(meta a, meta b) = a == b\nTwo(Box.G(1), Box.G(1))"),
        new("E12", "Same(meta a, x) = a.Invoke() + x\nSame(Box.G(trace(1)), 0)"),
        new("E13", "R = Capture(Box.G(2))\nR.Algorithm, 0"),
        new("E14", "R = Capture(Box.G(2))\nApply(R.Algorithm, 7), [1, 2].map(R.Algorithm)"),
        new("E15", "R = Capture(5.Add(2))\nApply(R.Algorithm, 7)"),
        // S — CallReference sharing
        new("S1", "R = Capture(Box.G(trace(2)))\nR.Arguments.count, R.Algorithm(3), R.Invoke(), R.Invoke()"),
        new("S2", "R = Capture(Square(5))\nQ = Capture(R.Algorithm(trace(4)))\nQ.Arguments.count, Q.Invoke(), Q.Algorithm(3), Q.Invoke()"),
        new("S3", "Op(meta op) = Capture(op.Algorithm(op.Arguments*))\nR = Op(Square(trace(7)))\nR.Invoke(), R.Invoke()"),
        new("S4", "Op(meta op) = (Capture(op.Algorithm(op.Arguments*)).Invoke(), op.Invoke(), op.Arguments.count)\nOp(Square(trace(7)))"),
        new("S5", "R = Capture(trace(5).Add(1))\nR.Arguments.count, R.Algorithm(10, 20), R.Invoke(), R.Invoke()"),
        new("S6", "Mk(t) = Capture(Square(t))\nR = Capture(Mk(trace(1)).Algorithm(3))\nR.Invoke(), R.Algorithm(4), R.Invoke()"),
        new("S6c", "Mk(t) = Capture(Square(t))\nMk(trace(1)).Algorithm(3), Mk(trace(1)).Algorithm(4)"),
        new("S7", "Both(meta r, x) = (r.Invoke(), x)\nW(y) = Both(y, y)\nW(Box.G(trace(3)))"),
        new("S8", "R = Capture(Box.G(1))\nR == R, R == Capture(Box.G(1))"),
        new("S9", "Op(meta op) = Capture(op.Algorithm(op.Arguments*))\nR = Op(Square(trace(7)))\nR.Arguments.count, R.Arguments[0], R.Invoke()"),
        // N — negative controls and the capture boundary
        new("N1", "Start = Step(0)\nwhile(Start)"),
        new("N2", "Start = Step(0)\nStart.while"),
        new("N3", "Inspect(1 + 2)"),
        new("N5", "X = Box.G(1)\nInspect(X)"),
        new("N6", "Inspect([Box.G(1)][0])"),
        new("N7", "Inspect(5.string())"),
        new("N8", "R = Capture(Square(5))\nInspect(R.Invoke())"),
        new("N9", "R = Capture(Square(5))\nInspect(R.Arguments())"),
        new("N10", "Box4 = { Algorithm(x) = x * 100 }\nInspect(Box4.Algorithm(2)), Capture(Box4.Algorithm(2)).Invoke(), Box4.Algorithm(2).repeat(1)"),
        new("N11", "Box5 = { Invoke(x) = x * 7 }\nInspect(Box5.Invoke(1)), Capture(Box5.Invoke(1)).Invoke()"),
        new("N12", "R = Capture(Square(5))\nCapture(R.Invoke()).Invoke()"),
        new("N13", "Capture(5.string()).Invoke()"),
        // X — adversarial
        new("X1a", "Fam.Q(1)"),
        new("X1b", "Inspect(Fam.Q(1))"),
        new("X1c", "Capture(Fam.Q(1)).Invoke()"),
        new("X1d", "Fam.Q(1).repeat(1)"),
        new("X2", "G(x) = x + 1000\nCapture(Box.G(1)).Invoke(), Box.G(1).repeat(1)"),
        new("X3", "R = Capture(Square(5))\nA = R.Algorithm\nBoxA = { B = A }\nInspect(BoxA.B(9)), BoxA.B(2).repeat(1), Capture(BoxA.B(3)).Invoke()"),
        new("X4", "R = Capture(R.Algorithm(1))\nR.Invoke()"),
        new("X4b", "R = Capture(R.Algorithm(1))\nInspect(R.Algorithm(2))"),
        new("X4c", "R = Capture(R.Algorithm(1))\nR.Algorithm(5)"),
        new("X5", "Bad = min([])\nInspect(Bad.Algorithm(1)), Capture(Bad.Algorithm(1)).Invoke()"),
        new("X5b", "Bad = min([])\nInspect(Bad.Algorithm(1))"),
        new("X7", "Inspect(Box.G(boom()))"),
        new("X7b", "Capture(Box.G(boom())).Invoke()"),
        new("X8", "R = Capture(Box.G(stop()))\nR.Invoke(), trace(1)", WithCancel: true),
        new("X8b", LoopDot + "Step(stop()).Loop, trace(1)", WithCancel: true),
        new("X11", "Use(f) = Capture(5.f(1)).Invoke()\nUse(Add)"),
        new("X12", "Inspect(3.Add(4)), Capture(3.Add(trace(4))).Arguments.count"),
        new("X13", "Loop(meta op) = op.Algorithm(op.Arguments*).while\nUse(b) = b.Step(0).Loop\nUse(Box)"),
        new("X14", "Inspect(if(aflag(), Box.G(1), 0))"),
        new("X15", "M(b) = Capture(b.G(4))\nR = M(Box)\nR.Invoke(), R.Algorithm(5), R.Arguments.count"),
        new("X16", "BoxT = { G(x) = trace(x) * 10 }\nR = Capture(BoxT.G(trace(1)))\nR.Invoke(), R.Invoke()"),
        new("X17", "Bad = min([])\nR = Capture(Bad.Algorithm(1))\nR.Arguments.count, R.Invoke()"),
        new("S6b", "Mk(t) = if(trace(t) > 0, Capture(Square(t)), 0)\nR = Capture(Mk(1).Algorithm(3))\nR.Invoke(), R.Algorithm(4), R.Invoke(), R.Arguments.count"),
        new("S6d", "Mk(t) = if(trace(t) > 0, Capture(Square(t)), 0)\nMk(1).Algorithm(3), Mk(1).Algorithm(4)"),
        new("S6e", "Mk(t) = if(aflag(), Capture(Square(t)), 0)\nR = Capture(Mk(1).Algorithm(3))\nR.Invoke(), R.Invoke()"),
        new("S6f", "Mk(t) = if(trace(t) > 0, Capture(Square(t)), 0)\nId(Mk(1).Algorithm(3)), Mk(1).Algorithm(3)"),
        new("X18", "MkBox(k) = {\n  G(x) = x * 10\n  k\n}\nR = if(aflag(), Capture(MkBox(1)), 0)\nUse(b) = (Inspect(b.G(3)), Capture(b.G(3)).Invoke(), b.G(3).repeat(1))\nUse(R.Algorithm)"),
        new("E16", "Inspect(Box.G(1).Add(2)), Box.G(1).Add(2).repeat(1)"),
        new("E17", "Inspect(5.Inc()), 5.Inc().repeat(2)"),
        new("X7c", "Box.G(boom())"),
        new("DM1", $"F(0) = Capture(Inc(0))\nF(n) = {{ open '{ModuleUrl}'\n Capture(n.Add2(1)) }}\nR = F(1)\nR.Invoke(), R.Arguments.count, R.Algorithm(5, 6)", AsyncOnly: true, Module: ModuleText),
        // EQ — original VALUE equivalence: Plain (no META, ordinary cells) vs Meta (plan cells)
        .. Equivalence("EQ1", "Id(Box.G(trace(2)))"),
        .. Equivalence("EQ2", "Id(Math.Abs(-3))"),
        .. Equivalence("EQ3", "Id(5.Add(trace(1)))"),
        .. Equivalence("EQ4", "Id(Box.G(1, 2))"),
        .. Equivalence("EQ5", "Id(Fam.Q(1))"),
        .. Equivalence("EQ7", "Id(Lib.Sub.G(trace(3)))"),
        .. Equivalence("EQ8", "Id((Box.G)(trace(2)))"),
        .. Equivalence("EQ10", "Id(Box.G(1 / 0))"),
        .. Equivalence("EQ11", "Id(3.string())"),
        .. Equivalence("EQ12", "Id(Box.Sq(trace(2)))"),
        .. Equivalence("EQ13", "Id(Box.G([1][5]*))"),
        .. Equivalence("EQ14", "Id(Box.V()), Id(Box.V()), Box.V"),
        .. Equivalence("EQ15", "Id(Box.G(true))"),
        .. Equivalence("EQ16", "Id(Box.Step(0))"),
        .. Equivalence("EQ17", "Id(Math.Abs(true))"),
        .. Equivalence("EQ18", "Id(3.Add(4, 5))"),
        .. Equivalence("EQ19", "Id([1, 2, 3].filter(IsBig).count)"),
        .. Equivalence("EQ20", "Id(count([1, 2, 3].filter(IsBig)))"),
        .. Equivalence("EQ21", "Id(Box.Step(0).while)"),
        .. Equivalence("EQ22", "Id(3.string(1))"),
        .. Equivalence("EQ23", "Bad = min([])\nId(Bad.Algorithm(1))"),
        .. Equivalence("EQ24", "Id(5.Algorithm(1))"),
        .. Equivalence("EQ25", "Bad = 5\nId(Bad.Algorithm(trace(1)))"),
        .. Equivalence("EQ26", "Id(Box.Missing(1))"),
        .. Equivalence("EQ27", "Id(Box.G(1).Add(trace(2)))"),
        // EQ101–EQ110 — the independent reviewer's added pairs (non-colliding identifiers)
        .. Equivalence("EQ101", "Id((Box.Missing)(1))"),
        .. Equivalence("EQ102", "Id(Box.V(1))"),
        .. Equivalence("EQ103", "Id(Box.G(()))"),
        .. Equivalence("EQ104", "Id(Box.G((1, 2)))"),
        .. Equivalence("EQ105", "Id(5.Add([1][5]*))"),
        .. Equivalence("EQ106", "Id((5.Inc)(1))"),
        .. Equivalence("EQ107", "Id((3.string)())"),
        .. Equivalence("EQ108", "Id((Box.Sq)(trace(2)))"),
        .. Equivalence("EQ109", "Id(Box.G(2)), Id(Box.G(3))"),
        .. Equivalence("EQ110", "Id({ X(a) = trace(a)\nX(1) }.X(2))"),
    ];

    private static Case[] Equivalence(string id, string source)
        => [new(id + "p", source, Plain: true), new(id + "m", source)];

    /// <summary>The bounded MaxSteps scan programs (limits 1–24 on the three engines: 216 comparisons).</summary>
    internal static readonly string[] ScanIds = ["A1", "A8", "B1", "C4", "E3", "S1", "S3", "X3", "S6b"];

    internal static Case ById(string id) => Cases.Single(c => c.Id == id);

    internal sealed record Observation(string Outcome, int Count, string Trace, long Steps, long Checkpoints,
        long Items, long Chars, long Loops, long LoopFallbacks, long Plans, long Formations, int Suspensions)
    {
        /// <summary>The engine-independent semantics every mode must agree on.</summary>
        public string Semantic => $"{Outcome}\tcount={Count}\ttrace={Trace}\tsteps={Steps}\tcheckpoints={Checkpoints}\titems={Items}\tchars={Chars}";
    }

    internal static string Value(Result r) => r switch
    {
        Result.Atom a => a.Value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Result.Bool b => b.Value ? "true" : "false",
        Result.Str s => "'" + s.Value + "'",
        Result.SequenceValue s => "(" + string.Join(", ", s.Items.Select(Value)) + ")",
        Result.ListValue l => "[" + string.Join(", ", l.Items.Select(Value)) + "]",
        _ => r.ToString() ?? "",
    };

    /// <summary>
    /// One run of <paramref name="c"/> on <paramref name="mode"/> (0 = sync generic, 1 = sync optimized,
    /// 2 = async with genuinely suspending <c>aflag</c> / <c>stop</c>). A cancellation must carry the run's own
    /// token, and a host failure must be the very exception <c>boom</c> threw.
    /// </summary>
    internal static async Task<Observation> Observe(Case c, int mode)
    {
        var trace = new List<string>();
        var suspensions = 0;
        using var cancel = new CancellationTokenSource();
        var boom = new InvalidOperationException("boom host failure");
        var operations = HostOperations.Create(
            HostOperation.Create("trace", (args, _) => { lock (trace) trace.Add(Value(args[0])); return args[0]; }, "x"),
            HostOperation.Create("boom", (_, _) => throw boom),
            mode == 2
                ? HostOperation.CreateAsync("aflag", async (_, _) => { await Task.Yield(); Interlocked.Increment(ref suspensions); return new Result.Bool(true); })
                : HostOperation.Create("aflag", (_, _) => new Result.Bool(true)),
            mode == 2
                ? HostOperation.CreateAsync("stop", async (_, _) => { await Task.Yield(); Interlocked.Increment(ref suspensions); cancel.Cancel(); return new Result.Bool(true); })
                : HostOperation.Create("stop", (_, _) => { cancel.Cancel(); return new Result.Bool(true); }));
        var options = c.Module is null
            ? new RunOptions { HostOperations = operations }
            : new RunOptions
            {
                HostOperations = operations,
                AllowedHosts = ["modules.example"],
                DownloadCode = async (_, token) => { await Task.Yield(); token.ThrowIfCancellationRequested(); return c.Module; },
            };
        var source = Core + (c.Plain ? Plain : Meta) + c.Source;
        var parsed = c.Module is null ? Parser.Parse(source, options) : await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors, c.Id + ": " + string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var observations = new EvaluationObservations();
        var loops = new LoopOptimizationDiagnostics();
        EvaluationBudget? budget = null;
        try
        {
            var run = mode == 2
                ? await Evaluator.RunCountedObservedAsync(program, c.Limits, observations: observations, hostOperations: operations,
                    cancellationToken: c.WithCancel ? cancel.Token : default)
                : Evaluator.RunCountedObserved(program, c.Limits, enableOptimizations: mode == 1, loopDiagnostics: loops,
                    observations: observations, hostOperations: operations, cancellationToken: c.WithCancel ? cancel.Token : default);
            budget = run.Item2;
            var result = run.Item1;
            var outcome = result.IsOk
                ? "ok " + Value(result.Value.Value)
                : "err " + result.Error.Code + " | " + KatLangError.FromEvalError(result.Error).Message.Replace("\n", " / ", StringComparison.Ordinal) + " @" + result.Error.Span;
            return Done(outcome, result.IsOk ? result.Value.EmittedCount : -1);
        }
        catch (OperationCanceledException e)
        {
            Assert.True(c.WithCancel, c.Id + " cancelled unexpectedly");
            Assert.Equal(cancel.Token, e.CancellationToken);
            return Done("cancelled", -1);
        }
        catch (InvalidOperationException e) when (ReferenceEquals(e, boom))
        {
            return Done("THROW same host exception", -1);
        }

        Observation Done(string outcome, int count) => new(outcome, count, string.Join(",", trace),
            budget?.ConsumedSteps ?? -1, budget?.ConsumedExpressionCheckpoints ?? -1, budget?.MaterializedItems ?? -1,
            budget?.MaterializedStringChars ?? -1, loops.OptimizedLoopHits, loops.OptimizedLoopFallbacks,
            observations.InvocationPlanCount, observations.PlanSupplyFormationCount, suspensions);
    }

    internal static int[] ModesOf(Case c) => c.AsyncOnly ? [2] : [0, 1, 2];
}
