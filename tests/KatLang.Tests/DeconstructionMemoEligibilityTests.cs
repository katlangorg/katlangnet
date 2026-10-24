using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// DECON-CACHE-2 (October 2026): the run-scoped shared bind of an assignment-deconstruction group
/// (<see cref="RunScopedDeconstructionBindingCache"/>) must never change what a target computes. A
/// memo result is trusted only when the helper that would run ordinarily binds the SAME actual
/// pattern to the SAME actual source entry, read in the same reader context, and that read obtains
/// the source's PUBLISHED value (Q-37); every other helper shape executes its ordinary bind.
///
/// <para>The host witnesses are the DECON-CACHE-1 research's (`experimental/features/decon-cache-1-research.md`
/// §4): parsed ASTs transformed with public record copies (<c>with</c>), shared property lists and
/// ownerless host scopes. Each is checked on the generic, optimized and genuinely suspending async
/// routes against its ORDINARY reference — the same AST whose target helpers carry no
    /// deconstruction metadata, so every target runs its helper as an ordinary call — and against the
/// reviewed expected value (uncached C# and, for the pure cases, Lean). The surface corpus pins the
/// established accounting of ordinary parser output (values, effects, steps, checkpoints, peak depth,
/// materialized items and full binds) on every route, so the correction keeps the existing sharing.</para>
/// </summary>
public class DeconstructionMemoEligibilityTests
{
    public enum Route
    {
        Generic,
        Optimized,
        SuspendingAsync,
    }

    internal sealed record Observation(
        string Outcome, string Effects, long Steps, long Checkpoints, int PeakDepth, long Materialized, long Binds)
    {
        /// <summary>Value and emitted count, or the error's kind, then the ordered host effects.</summary>
        public string Comparable
            => (Outcome.StartsWith("err ", StringComparison.Ordinal) ? Outcome[..Outcome.IndexOf(':')] : Outcome) + " | " + Effects;

        public override string ToString()
            => $"{Outcome} | {Effects} | steps={Steps} chk={Checkpoints} depth={PeakDepth} items={Materialized} binds={Binds}";
    }

    private static readonly HostOperations ParseOperations = HostOperations.Create(
        HostOperation.Create("tick", (_, _) => new Result.Atom(0)),
        HostOperation.Create("trace", (args, _) => args[0], "x"));

    internal static Algorithm.User Parse(string source)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = ParseOperations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return parsed.Root;
    }

    internal static async Task<Observation> Observe(Expr program, Route route, EvaluationLimits? limits = null)
    {
        var log = new List<string>();
        var ticks = 0;
        Result Tick()
        {
            lock (log)
            {
                var tick = ++ticks;
                log.Add($"tick#{tick}");
                return new Result.Atom((Decimal128)tick);
            }
        }

        Result Trace(Result value)
        {
            lock (log) log.Add($"t({SixRouteAgreement.Neutral(value)})");
            return value;
        }

        var observations = new EvaluationObservations();
        EvalResult<Evaluator.CountedResult> result;
        EvaluationBudget budget;
        if (route == Route.SuspendingAsync)
        {
            var operations = HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return Trace(args[0]); }, "x"));
            (result, budget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                program, limits, new SuspendingAsyncZeroArgPropertyResultCache(), observations: observations,
                hostOperations: operations, randomSeed: 7));
        }
        else
        {
            var operations = HostOperations.Create(
                HostOperation.Create("tick", (_, _) => Tick()),
                HostOperation.Create("trace", (args, _) => Trace(args[0]), "x"));
            (result, budget) = Evaluator.RunCountedObserved(
                program, limits, enableOptimizations: route == Route.Optimized, observations: observations,
                hostOperations: operations, randomSeed: 7);
        }

        string outcome;
        if (result.IsError)
        {
            var error = KatLangError.FromEvalError(result.Error);
            outcome = $"err {error.Code}: {error.Message} @ {error.Span}";
        }
        else
        {
            outcome = $"ok {SixRouteAgreement.Neutral(result.Value.Value)} n={result.Value.EmittedCount}";
        }

        return new Observation(outcome, string.Join(",", log), budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints,
            budget.PeakDepth, budget.MaterializedItems, observations.DeconstructionFullBindCount);
    }

    // ───────────────────────── AST transformations ─────────────────────────

    /// <summary>
    /// The ORDINARY reference of a program: every target helper reached through a property body's
    /// <c>helper(args)</c> row loses its deconstruction metadata, so it runs as the ordinary call it is
    /// (Lean's meaning: Lean has no group memo) — never through the shared bind.
    /// </summary>
    internal static Algorithm.User WithoutDeconstructionMetadata(Algorithm.User algorithm)
        => algorithm with
        {
            Properties = [.. algorithm.Properties.Select(property => property.Value is Algorithm.User body
                ? property with { Value = WithoutDeconstructionMetadata(body) }
                : property)],
            Output = new OutputBundle([.. algorithm.Output.Select(StripRow)]),
        };

    private static Expr StripRow(Expr row)
        => row is Expr.Call { Function: Expr.AlgorithmExpr { Algorithm: Algorithm.User { AssignmentDeconstructionTarget: not null } helper } } call
            ? call with { Function = new Expr.AlgorithmExpr(helper with { AssignmentDeconstructionTarget = null }) }
            : row;

    private static Algorithm.User TargetBody(Algorithm.User root, string target)
        => Assert.IsType<Algorithm.User>(root.Properties.First(property => property.Name == target).Value);

    private static Expr.Call HelperCall(Algorithm.User body)
        => Assert.IsType<Expr.Call>(Assert.Single(body.Output));

    private static Algorithm.User Helper(Expr.Call call)
    {
        var helper = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(call.Function).Algorithm);
        Assert.NotNull(helper.AssignmentDeconstructionTarget);
        return helper;
    }

    /// <summary>Adds property <paramref name="name"/> = <paramref name="body"/> and replaces the root rows by bare reads.</summary>
    private static Algorithm.User WithPropertyAndRows(Algorithm.User root, Property? extra, params string[] rows)
        => root with
        {
            Properties = extra is null ? root.Properties : [.. root.Properties, extra],
            Output = new OutputBundle([.. rows.Select(static name => (Expr)new Expr.Resolve(name))]),
        };

    /// <summary>H04/H05: <c>c</c> is target <c>a</c>'s body with its (unchanged) helper applied to <c>Resolve(q)</c>.</summary>
    private static Algorithm.User OtherArgumentCopy(params string[] rows)
    {
        var root = Parse("a, b = (1, 2)\nq = (7, 8)\na");
        var aBody = TargetBody(root, "a");
        var call = HelperCall(aBody);
        Helper(call);
        var cBody = aBody with { Output = [call with { Args = [new Expr.Resolve("q")] }] };
        return WithPropertyAndRows(root, new Property("c", cBody), rows);
    }

    /// <summary>V05/V06: <c>c</c> is <c>a</c>'s body whose helper copy unpacks <c>([a], b)</c>, metadata retained.</summary>
    private static Algorithm.User ChangedPatternCopy(params string[] rows)
    {
        var root = Parse("a, b = ([1], 2)\na");
        var aBody = TargetBody(root, "a");
        var call = HelperCall(aBody);
        var helper = Helper(call);
        var unpacking = Assert.IsType<UnpackingParameterPattern>(Assert.Single(helper.ParameterPatterns));
        var changed = helper with
        {
            ParameterPatterns = [new UnpackingParameterPattern([new ListValueParameterPattern([unpacking.Items[0]]), unpacking.Items[1]])],
        };
        Assert.Equal(helper.AssignmentDeconstructionTarget, changed.AssignmentDeconstructionTarget);
        var cBody = aBody with { Output = [call with { Function = new Expr.AlgorithmExpr(changed) }] };
        return WithPropertyAndRows(root, new Property("c", cBody), rows);
    }

    /// <summary>V07: <c>c</c> is <c>a</c>'s body plus a LOCAL <c>$deconstruct$0 = (7, 8)</c> its helper reads.</summary>
    private static Algorithm.User LocallyShadowedSourceCopy(params string[] rows)
    {
        var root = Parse("a, b = (1, 2)\na");
        var aBody = TargetBody(root, "a");
        var source = root.Properties.First(property => property.Name == "$deconstruct$0");
        var shadow = source with { Value = Assert.IsType<Algorithm.User>(source.Value) with { Output = [new Expr.Num(7), new Expr.Num(8)] } };
        return WithPropertyAndRows(root, new Property("c", aBody with { Properties = [shadow] }), rows);
    }

    /// <summary>H01/H02/H03: the root rows read the hoisted source directly before the targets (Q-37 re-entry).</summary>
    private static Algorithm.User DirectSourceRead(params string[] rows)
        => WithPropertyAndRows(Parse("a, b = if(tick() < 2, a + 10, 0), tick()\nb"), null, rows);

    /// <summary>
    /// D3-*: the root's properties live in ownerless host <see cref="ScopeCtx"/> levels parenting two opened
    /// blocks <c>{ public RunA = readA }</c> and <c>{ public RunB = readB }</c>; <paramref name="shape"/> is
    /// <c>same</c> (one scope), <c>fresh</c> (two scopes over one property list) or <c>copy</c> (a record copy).
    /// </summary>
    private static Expr HostScopes(string source, string shape, string readA, string readB, bool ordinary = false)
    {
        var root = ordinary ? WithoutDeconstructionMetadata(Parse(source)) : Parse(source);
        var prelude = new ScopeCtx(null, [], ParseOperations.RuntimePreludeAlgorithm.Properties);
        var first = new ScopeCtx(prelude, [], root.Properties);
        var second = shape switch
        {
            "same" => first,
            "fresh" => new ScopeCtx(prelude, [], root.Properties),
            "copy" => first with { },
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        static Algorithm.User Body(params Expr[] rows) => new(null, [], [], [], new OutputBundle(rows));
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [],
            [new Expr.AlgorithmExpr(new Algorithm.User(first, [], [], [new Property("RunA", Body(new Expr.Resolve(readA)), IsPublic: true)], OutputBundle.Empty)),
             new Expr.AlgorithmExpr(new Algorithm.User(second, [], [], [new Property("RunB", Body(new Expr.Resolve(readB)), IsPublic: true)], OutputBundle.Empty))],
            [], new OutputBundle([new Expr.Resolve("RunA"), new Expr.Resolve("RunB")])));
    }

    /// <summary>L01/L02: <c>Lib1</c> and <c>Lib2</c> are two declarations over ONE shared property list.</summary>
    private static Expr TwoDeclarationsOneList(string source, string readA, string readB, bool ordinary = false)
    {
        var list = (ordinary ? WithoutDeconstructionMetadata(Parse(source)) : Parse(source)).Properties;
        var lib1 = new Algorithm.User(null, [], [], list, OutputBundle.Empty);
        var lib2 = new Algorithm.User(null, [], [], list, OutputBundle.Empty);
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [new Property("Lib1", lib1, IsPublic: true), new Property("Lib2", lib2, IsPublic: true)],
            new OutputBundle([new Expr.DotCall(new Expr.Resolve("Lib1"), readA, null), new Expr.DotCall(new Expr.Resolve("Lib2"), readB, null)])));
    }

    // ───────────────────────── surface accounting (parser output keeps its sharing) ─────────────────────────

    /// <summary>
    /// The DECON-CACHE-1 surface corpus (R01–R29, X01, X04, V01–V11 and three extra shapes): property-cache
    /// RHS sharing, read orders, callbacks and helpers, collecting and opened targets, explicit
    /// <c>a()</c>, equal and distinct activations, recursion, Q-37 re-entry, loops (zero rounds included),
    /// seeded random, META capture and runtime aliases, forwarding, an alias right-hand side, and the
    /// R02 step-limit and V02 materialization-limit refusals. Each expectation is the observation of
    /// HEAD c6b77992 before DECON-CACHE-2 (identical on all three routes), so the correction keeps every
    /// value, effect, step, checkpoint, depth, materialization charge and full-bind count of ordinary
    /// parser output — the conservative per-consumer accounting included (OD-1 stays deferred).
    /// </summary>
    internal static readonly (string Id, string Source, EvaluationLimits? Limits)[] SurfaceCorpus =
    [
        ("R01", "F(k) = {\n    B = {\n        a, b = trace(k), k + 1\n        a + b\n    }\n    [1, 2].map{ n + B }[0] + B.a + B.b\n}\nF(3)", null),
        ("R02", "F(k) = {\n    B = {\n        a, b = trace(k), k + 1\n        a + b\n    }\n    [1, 2].map{ n + B.a }[0] + B.b\n}\nF(3)", null),
        ("R02-MaxSteps10", "F(k) = {\n    B = {\n        a, b = trace(k), k + 1\n        a + b\n    }\n    [1, 2].map{ n + B.a }[0] + B.b\n}\nF(3)", new EvaluationLimits { MaxSteps = 10 }),
        ("R02-MaxSteps11", "F(k) = {\n    B = {\n        a, b = trace(k), k + 1\n        a + b\n    }\n    [1, 2].map{ n + B.a }[0] + B.b\n}\nF(3)", new EvaluationLimits { MaxSteps = 11 }),
        ("R03", "F(k) = {\n    B = {\n        a, b = trace(k), k + 1\n        a + b\n    }\n    B.a + B.b + [1, 2].map{ n + B }[0]\n}\nF(3)", null),
        ("R04", "F(k) = {\n    B = {\n        a, b = trace(k), k + 1\n        a + b\n    }\n    G(x) = x + B.a\n    G(1) + B.b\n}\nF(3)", null),
        ("R05", "F(k) = {\n    a, b = trace(k), k + 1\n    [1].map{ n + a }[0] + b\n}\nF(3)", null),
        ("R06", "F(k) = {\n    x, y, z = trace(k), k + 1, k + 2\n    [0].map{ n + x }[0] + [0].map{ n + y }[0] + [0].map{ n + z }[0]\n}\nF(3)", null),
        ("R07", "F(k) = {\n    a, b = trace(k), k + 1\n    [1, 2, 3].map{ n + a() }.sum + b\n}\nF(3)", null),
        ("R08", "a, b = trace(1), 2\n[1].map{ n + a }[0] + b", null),
        ("R09", "B = {\n    a, b = trace(1), 2\n    a + b\n}\n[1].map{ n + B.a }[0] + B.b", null),
        ("R10", "F(k) = {\n    a, b = trace(k), k + 1\n    [1].map{ n + a }[0] + b\n}\nF(1), F(2)", null),
        ("R11", "F(k) = {\n    a, b = trace(k), k + 1\n    [1].map{ n + a }[0] + b\n}\nF(1), F(1)", null),
        ("R12", "F(k) = {\n    a, b = if(k > 0, F(k - 1), 0), k\n    a + b\n}\nF(3)", null),
        ("R13", "a, b = if(tick() < 3, a + 1, 0), 5\na, a, b", null),
        ("R14", "a, b = if(tick() < 3, [1].map{ n * 0 + a + 1 }[0], 0), 5\na, a, b", null),
        ("R15", "a, b = if(tick() < 3, b + 1, 0), 5\na, b, a", null),
        ("R16", "Step(s) = {\n    p, q = s + 1, s + 1 < 3\n    p, q\n}\nStep(0).while", null),
        ("R17", "Step(s) = {\n    p, q = s + 1, false\n    p, q\n}\nStep(0).while", null),
        ("R18", "F(k) = {\n    a, b = trace(k), k + 1\n    Step(s) = s + a\n    Step(0).repeat(3) + b\n}\nF(3)", null),
        ("R19", "F(k) = {\n    h, *t = trace(k), k + 1, k + 2\n    [1].map{ n + h }[0] + t.count + [1].map{ n * 0 + t.count }[0]\n}\nF(3)", null),
        ("R20", "F(k) = {\n    a, b = random(0, 1000), k\n    [1].map{ n * 0 + a }[0] == a, [2].map{ n * 0 + b }[0] == b\n}\nF(3)", null),
        ("R21", "F(k) = {\n    a, b = trace(k), k + 1\n    Inv(meta c) = c.Invoke()\n    Inv(a()) + [1].map{ n * 0 + Inv(b()) }[0] + a + b\n}\nF(3)", null),
        ("R22", "F(k) = {\n    a, b = trace(k), k + 1\n    H(v) = v\n    [1].map{ n + H(a) }[0] + H(b)\n}\nF(3)", null),
        ("R23", "F(k) = {\n    a, b = trace(k), 1 / 0\n    a + b\n}\nF(3)", null),
        ("R24", "F(k) = {\n    a, b = trace(k), k + 1\n    k\n}\nF(3)", null),
        ("R25", "F(k) = {\n    a, b = [trace(k), [k, k + 1]]\n    [1].map{ n + a }[0] + b[1]\n}\nF(3)", null),
        ("R26", "Step(s) = {\n    p, q = s + 1, s * 10\n    p\n}\nStep(0).repeat(3)", null),
        ("R27", "[1, 2, 3].map{\n    a, b = n * 10, n\n    [0].map{ m + a }[0] + b\n}", null),
        ("R28", "F(k) = {\n    B = {\n        C = {\n            a, b = trace(k), k + 1\n            a + b\n        }\n        C\n    }\n    [0].map{ n + B.C.a }[0] + [0].map{ n + B.C.b }[0] + B.C.a\n}\nF(3)", null),
        ("R29", "a, b = if(tick() < 3, [1].map{ n * 0 + a + b * 0 }[0] + 1, 0), tick()\na, b", null),
        ("X01", "F(k) = {\n    Only(*xs) = {\n        a, b = trace(k), k + 1\n        a + b + xs.count\n    }\n    [1].map{ n * 0 + Only.a }[0] + Only.b + Only\n}\nF(3)", null),
        ("X04", "F(k) = {\n    a, b = trace(k), k + 1\n    G = [1].map{ n + a }[0]\n    G + b\n}\nH = F\nH(3) + H(3)", null),
        ("V01", "F(k) = {\n    h, *t = trace(k), k + 1, k + 2\n    [1, 2, 3].map{ n * 0 + t().count }.sum + h\n}\nF(3)", null),
        ("V02-MaxItems11", "F(k) = {\n    h, *t = trace(k), k + 1, k + 2\n    [1, 2, 3].map{ n * 0 + t().count }.sum + h\n}\nF(3)", new EvaluationLimits { MaxMaterializedItems = 11 }),
        ("V03", "F(k) = {\n    open B\n    B = {\n        a, b = trace(k), k + 1\n        public A = a\n        public Z = b\n        a + b\n    }\n    [1].map{ n + A }[0] + Z\n}\nF(3)", null),
        ("V04", "Step(s) = {\n    a, b = trace(s), s + 1\n    b\n}\nStep(0).repeat(0)", null),
        ("V08-MaxDepth5", "F(k) = {\n    a, b = trace(k), k + 1\n    [1].map{ n + a }[0] + b\n}\nF(3)", new EvaluationLimits { MaxDepth = 5 }),
        ("V09", "F(k) = {\n    a, b = trace(k), k + 1\n    [1].map{ n + a }[0] + b\n}\nCap(meta c) = {\n    A = c.Algorithm\n    A(c.Arguments*)\n}\nCap(F(3)) + Cap(F(3))", null),
        ("V10", "Outer(k) = {\n    F = {\n        a, b = trace(k), k + 1\n        [1].map{ n + a }[0] + b\n    }\n    F() + F()\n}\nOuter(3)", null),
        ("V11", "Inc(x) = trace(x) + 1\nUse(meta r) = {\n    a, b = r, 1\n    [0].map{ n + a.Invoke() }[0] + b + a.Invoke()\n}\nUse(Inc(3))", null),
        ("ALIAS-RHS", "P(*xs) = trace(1), 2\na, b = P\n[1].map{ n + a }[0] + b, a, b", null),
        ("WIDE-BODY", "x0, x1, x2, x3, x4, x5 = range(1, 6)\nx0 + x1 + x2 + x3 + x4 + x5, x5, x0", null),
        ("COLLECT-WIDE", "F(k) = {\n    h, *t, z = trace(k), k + 1, k + 2, k + 3\n    t.count + h + z + [1].map{ n * 0 + t[0] }[0]\n}\nF(3)", null),
    ];

    private static readonly Dictionary<string, string> SurfaceExpectations = new(StringComparer.Ordinal)
    {
        ["R01"] = "ok 15 n=1 | t(3) | steps=13 chk=49 depth=7 items=6 binds=1",
        ["R02"] = "ok 8 n=1 | t(3) | steps=11 chk=40 depth=6 items=6 binds=2",
        ["R02-MaxSteps10"] = "err EvaluationStepLimitExceeded: Evaluation step limit of 10 was exceeded @ [6:32, 6:35) | t(3) | steps=10 chk=39 depth=6 items=6 binds=2",
        ["R02-MaxSteps11"] = "ok 8 n=1 | t(3) | steps=11 chk=40 depth=6 items=6 binds=2",
        ["R03"] = "ok 15 n=1 | t(3) | steps=13 chk=49 depth=5 items=6 binds=1",
        ["R04"] = "ok 8 n=1 | t(3) | steps=9 chk=27 depth=6 items=2 binds=2",
        ["R05"] = "ok 8 n=1 | t(3) | steps=9 chk=33 depth=6 items=4 binds=2",
        ["R06"] = "ok 12 n=1 | t(3) | steps=14 chk=71 depth=6 items=9 binds=3",
        ["R07"] = "ok 19 n=1 | t(3) | steps=17 chk=48 depth=6 items=8 binds=4",
        ["R08"] = "ok 4 n=1 | t(1) | steps=8 chk=27 depth=5 items=4 binds=2",
        ["R09"] = "ok 4 n=1 | t(1) | steps=8 chk=27 depth=5 items=4 binds=2",
        ["R10"] = "ok S[4, 6] n=2 | t(1),t(2) | steps=18 chk=66 depth=6 items=10 binds=4",
        ["R11"] = "ok S[4, 4] n=2 | t(1),t(1) | steps=18 chk=66 depth=6 items=10 binds=4",
        ["R12"] = "ok 6 n=1 |  | steps=27 chk=95 depth=16 items=8 binds=7",
        ["R13"] = "ok S[2, 2, 5] n=3 | tick#1,tick#2,tick#3 | steps=15 chk=50 depth=10 items=9 binds=3",
        ["R14"] = "ok S[2, 2, 5] n=3 | tick#1,tick#2,tick#3 | steps=17 chk=84 depth=12 items=13 binds=3",
        ["R15"] = "ok S[6, 5, 6] n=3 | tick#1,tick#2,tick#3 | steps=14 chk=49 depth=10 items=9 binds=3",
        ["R16"] = "ok 2 n=1 |  | steps=16 chk=63 depth=3 items=6 binds=3",
        ["R17"] = "ok 0 n=1 |  | steps=4 chk=12 depth=3 items=2 binds=1",
        ["R18"] = "ok 13 n=1 | t(3) | steps=13 chk=40 depth=5 items=2 binds=2",
        ["R19"] = "ok 8 n=1 | t(3) | steps=11 chk=62 depth=6 items=9 binds=2",
        ["R20"] = "ok S[true, true] n=1 |  | steps=12 chk=57 depth=6 items=8 binds=2",
        ["R21"] = "ok 14 n=1 | t(3) | steps=13 chk=51 depth=6 items=4 binds=2",
        ["R22"] = "ok 8 n=1 | t(3) | steps=11 chk=37 depth=7 items=4 binds=2",
        ["R23"] = "err DivisionByZero: while evaluating call to F: Division by zero @ [2:22, 2:27) | t(3) | steps=5 chk=15 depth=5 items=0 binds=1",
        ["R24"] = "ok 3 n=1 |  | steps=1 chk=3 depth=1 items=0 binds=0",
        ["R25"] = "ok 8 n=1 | t(3) | steps=9 chk=42 depth=6 items=6 binds=2",
        ["R26"] = "ok 3 n=1 |  | steps=12 chk=48 depth=3 items=6 binds=3",
        ["R27"] = "ok L[11, 22, 33] n=1 |  | steps=24 chk=96 depth=5 items=18 binds=6",
        ["R28"] = "ok 10 n=1 | t(3) | steps=11 chk=50 depth=6 items=6 binds=2",
        ["R29"] = "ok S[2, 6] n=2 | tick#1,tick#2,tick#3,tick#4,tick#5,tick#6,tick#7,tick#8 | steps=24 chk=114 depth=12 items=14 binds=4",
        ["X01"] = "ok 14 n=1 | t(3) | steps=12 chk=51 depth=6 items=4 binds=2",
        ["X04"] = "ok 16 n=1 | t(3),t(3) | steps=20 chk=74 depth=7 items=8 binds=4",
        ["V01"] = "ok 9 n=1 | t(3) | steps=17 chk=69 depth=6 items=15 binds=4",
        ["V02-MaxItems11"] = "err MaterializationLimitExceeded: Evaluation materialization limit of 11 items was exceeded @ [3:28, 3:31) | t(3) | steps=14 chk=63 depth=6 items=10 binds=3",
        ["V03"] = "ok 8 n=1 | t(3) | steps=11 chk=35 depth=7 items=4 binds=2",
        ["V04"] = "ok 0 n=1 |  | steps=0 chk=3 depth=0 items=0 binds=0",
        ["V08-MaxDepth5"] = "err EvaluationDepthExceeded: Evaluation recursion limit of 5 was exceeded @ [2:18, 2:19) |  | steps=5 chk=16 depth=5 items=1 binds=1",
        ["V09"] = "ok 16 n=1 | t(3),t(3) | steps=20 chk=78 depth=7 items=8 binds=4",
        ["V10"] = "ok 16 n=1 | t(3),t(3) | steps=19 chk=70 depth=7 items=8 binds=4",
        ["V11"] = "ok 9 n=1 | t(3),t(3) | steps=13 chk=47 depth=6 items=4 binds=2",
        ["ALIAS-RHS"] = "ok S[4, 1, 2] n=3 | t(1) | steps=11 chk=30 depth=6 items=7 binds=2",
        ["WIDE-BODY"] = "ok S[21, 6, 1] n=3 |  | steps=15 chk=34 depth=3 items=9 binds=1",
        ["COLLECT-WIDE"] = "ok 15 n=1 | t(3) | steps=11 chk=62 depth=5 items=8 binds=1",
    };

    public static TheoryData<string, Route> SurfaceCases()
    {
        var data = new TheoryData<string, Route>();
        foreach (var (id, _, _) in SurfaceCorpus)
            foreach (var route in Enum.GetValues<Route>())
                data.Add(id, route);
        return data;
    }

    /// <summary>
    /// Every observed field of every surface case equals HEAD's on every route: the correction keeps the
    /// memo sharing parser output had (R01's single bind, the wide body's single bind), the per-consumer
    /// binds (R02, R05–R11), the group-wide guard's recursive accounting (R12's seven binds — a full-key
    /// guard would store the inner activations' binds and lower it), the R02 step refusal at
    /// <c>MaxSteps = 10</c> and the V02 collector refusal at <c>MaxMaterializedItems = 11</c>.
    /// </summary>
    [Theory]
    [MemberData(nameof(SurfaceCases))]
    public async Task SurfaceProgram_KeepsItsEstablishedAccounting(string id, Route route)
    {
        var (_, source, limits) = SurfaceCorpus.Single(entry => entry.Id == id);
        var observed = await Observe(new Expr.AlgorithmExpr(Parse(source)), route, limits);
        Assert.Equal(SurfaceExpectations[id], observed.ToString());
    }

    /// <summary>
    /// The memo-enabled run of every unlimited surface case computes exactly what its ORDINARY
    /// helper execution computes — value, emitted count, error kind and host effects in order —
    /// on every route (resource limits are excluded: the ordinary helper call is accounted
    /// differently, and limits observe accounting).
    /// </summary>
    [Theory]
    [MemberData(nameof(SurfaceCases))]
    public async Task SurfaceProgram_MatchesItsOrdinaryHelperExecution(string id, Route route)
    {
        var (_, source, limits) = SurfaceCorpus.Single(entry => entry.Id == id);
        if (limits is not null)
            return;
        var root = Parse(source);
        var memo = await Observe(new Expr.AlgorithmExpr(root), route);
        var ordinary = await Observe(new Expr.AlgorithmExpr(WithoutDeconstructionMetadata(root)), route);
        Assert.Equal(ordinary.Comparable, memo.Comparable);
    }

    /// <summary>The memo-enabled program of host witness <paramref name="id"/> (shared with <c>HostParentDifferentialCorpus</c>'s HP-15 cases).</summary>
    internal static Expr HostWitness(string id) => HostCorpus.Single(entry => entry.Id == id).Build(false);

    private static Expr Program(Algorithm.User root, bool ordinary)
        => new Expr.AlgorithmExpr(ordinary ? WithoutDeconstructionMetadata(root) : root);

    internal static readonly (string Id, Func<bool, Expr> Build)[] HostCorpus =
    [
        ("H01", ordinary => Program(DirectSourceRead("$deconstruct$0", "b"), ordinary)),
        ("H02", ordinary => Program(DirectSourceRead("a", "b"), ordinary)),
        ("H03", ordinary => Program(DirectSourceRead("$deconstruct$0", "a", "b"), ordinary)),
        ("H04", ordinary => Program(OtherArgumentCopy("c", "a"), ordinary)),
        ("H05", ordinary => Program(OtherArgumentCopy("a", "c"), ordinary)),
        ("V05", ordinary => Program(ChangedPatternCopy("c", "a"), ordinary)),
        ("V06", ordinary => Program(ChangedPatternCopy("a", "c"), ordinary)),
        ("V07", ordinary => Program(LocallyShadowedSourceCopy("a", "c"), ordinary)),
        ("V07-C-FIRST", ordinary => Program(LocallyShadowedSourceCopy("c", "a"), ordinary)),
        ("D3-SAME", ordinary => HostScopes("a, b = tick(), tick()\na", "same", "a", "b", ordinary)),
        ("D3-FRESH", ordinary => HostScopes("a, b = tick(), tick()\na", "fresh", "a", "b", ordinary)),
        ("D3-COPY", ordinary => HostScopes("a, b = tick(), tick()\na", "copy", "a", "b", ordinary)),
        ("D3-FRESH-BB", ordinary => HostScopes("a, b = tick(), tick()\na", "fresh", "b", "b", ordinary)),
        ("D3-COPY-PURE", ordinary => HostScopes("a, b = 1, 2\na", "copy", "a", "b", ordinary)),
        ("L01", ordinary => TwoDeclarationsOneList("a, b = tick(), tick()\na", "a", "b", ordinary)),
        ("L02", ordinary => TwoDeclarationsOneList("P = tick()\nP", "P", "P", ordinary)),
    ];

    /// <summary>
    /// The reviewed reference of each witness (uncached C# and, for H04/H05/V05–V07, Lean — pinned on the
    /// Lean side by the HP-15 cases of <c>HostParentDifferentialCorpus</c>). HEAD c6b77992 returned
    /// H01 <c>S[S[10, 4], 3]</c>, H03 <c>S[S[10, 4], 0, 3]</c>, H04 <c>S[7, 7]</c>, H05 <c>S[1, 1]</c>,
    /// V05 <c>S[1, 1]</c>, V06 <c>S[L[1], L[1]]</c>, D3-FRESH/D3-COPY/L01 <c>S[1, 2]</c> with two ticks and
    /// D3-FRESH-BB <c>S[2, 2]</c>; V07 was already right and is the regression control of the falsified
    /// source-key prototypes (they returned <c>S[1, 1]</c>). Which mechanism each one kills:
    /// <list type="bullet">
    ///   <item>H01/H03 — omitting the publication check (the memo stored a bind of the re-entrant,
    ///   unpublished intermediate source value <c>(0, 3)</c>);</item>
    ///   <item>D3-FRESH/D3-COPY/D3-FRESH-BB/L01 — collapsing host owners (a structural owner identity
    ///   over one shared property list instead of the source entry's own key);</item>
    ///   <item>H04/H05 — ignoring the helper's actual argument;</item>
    ///   <item>V05/V06 — ignoring the helper's actual pattern under its retained group token;</item>
    ///   <item>V07 — replacing the actual lexical source by a parent-scope guess.</item>
    /// </list>
    /// H02, D3-SAME, D3-COPY-PURE and L02 are the controls that already agreed.
    /// </summary>
    private static readonly Dictionary<string, string> HostExpectations = new(StringComparer.Ordinal)
    {
        ["H01"] = "ok S[S[10, 4], 4] n=2 | tick#1,tick#2,tick#3,tick#4",
        ["H02"] = "ok S[10, 4] n=2 | tick#1,tick#2,tick#3,tick#4",
        ["H03"] = "ok S[S[10, 4], 0, 4] n=3 | tick#1,tick#2,tick#3,tick#4",
        ["H04"] = "ok S[7, 1] n=2 | ",
        ["H05"] = "ok S[1, 7] n=2 | ",
        ["V05"] = "ok S[1, L[1]] n=2 | ",
        ["V06"] = "ok S[L[1], 1] n=2 | ",
        ["V07"] = "ok S[1, 7] n=2 | ",
        ["V07-C-FIRST"] = "ok S[7, 1] n=2 | ",
        ["D3-SAME"] = "ok S[1, 2] n=2 | tick#1,tick#2",
        ["D3-FRESH"] = "ok S[1, 4] n=2 | tick#1,tick#2,tick#3,tick#4",
        ["D3-COPY"] = "ok S[1, 4] n=2 | tick#1,tick#2,tick#3,tick#4",
        ["D3-FRESH-BB"] = "ok S[2, 4] n=2 | tick#1,tick#2,tick#3,tick#4",
        ["D3-COPY-PURE"] = "ok S[1, 2] n=2 | ",
        ["L01"] = "ok S[1, 4] n=2 | tick#1,tick#2,tick#3,tick#4",
        ["L02"] = "ok S[1, 2] n=2 | tick#1,tick#2",
    };

    public static TheoryData<string, Route> HostCases()
    {
        var data = new TheoryData<string, Route>();
        foreach (var (id, _) in HostCorpus)
            foreach (var route in Enum.GetValues<Route>())
                data.Add(id, route);
        return data;
    }

    [Theory]
    [MemberData(nameof(HostCases))]
    public async Task HostTransformedAst_MatchesItsOrdinaryHelperExecution(string id, Route route)
    {
        var build = HostCorpus.Single(entry => entry.Id == id).Build;
        var memo = await Observe(build(false), route);
        var ordinary = await Observe(build(true), route);
        Assert.Equal(HostExpectations[id], ordinary.Comparable);
        Assert.Equal(ordinary.Comparable, memo.Comparable);
    }

    /// <summary>
    /// The memo still shares what it may: one exact host scope (D3-SAME) and a parsed group read from one
    /// context bind once, while two host scopes over one list, a locally shadowed copy and a copy over a
    /// different argument bind per actual source; a copied pattern takes the ordinary call path.
    /// H01's direct source read makes the
    /// re-entrant inner bind unstorable, so the later target binds the published source again.
    /// </summary>
    [Theory]
    [InlineData("D3-SAME", 1)]
    [InlineData("D3-COPY-PURE", 2)]
    [InlineData("D3-FRESH", 2)]
    [InlineData("L01", 2)]
    [InlineData("H01", 2)]
    [InlineData("H04", 2)]
    [InlineData("V05", 1)]
    [InlineData("V07", 2)]
    [InlineData("L02", 0)]
    public async Task HostTransformedAst_SharesExactlyTheBindsOfOneActualSourceAndPattern(string id, long binds)
    {
        foreach (var route in Enum.GetValues<Route>())
            Assert.Equal(binds, (await Observe(HostCorpus.Single(entry => entry.Id == id).Build(false), route)).Binds);
    }

    /// <summary>
    /// A cache that publishes nothing (<see cref="UncachedZeroArgPropertyResultCache"/>) gives every source
    /// read a fresh evaluation, so no two targets may share a bind: each binds its own read, exactly as the
    /// ordinary helpers do (formerly the memo silently reused the first read).
    /// </summary>
    [Fact]
    public void ACacheThatPublishesNothing_NeverSharesABind()
    {
        static string Run(Algorithm.User root)
        {
            var ticks = 0;
            var operations = HostOperations.Create(
                HostOperation.Create("tick", (_, _) => new Result.Atom(++ticks)),
                HostOperation.Create("trace", (args, _) => args[0], "x"));
            var observations = new EvaluationObservations();
            var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(root), zeroArgPropertyResultCache: UncachedZeroArgPropertyResultCache.Instance,
                observations: observations, hostOperations: operations);
            Assert.True(result.IsOk);
            return $"{SixRouteAgreement.Neutral(result.Value.Value)} ticks={ticks} binds={observations.DeconstructionFullBindCount}";
        }

        var root = Parse("a, b = tick(), tick()\na, b");
        Assert.Equal("S[1, 4] ticks=4 binds=2", Run(root));
        Assert.Equal("S[1, 4] ticks=4 binds=0", Run(WithoutDeconstructionMetadata(root)));
    }

    /// <summary>
    /// A host-modified helper whose one output row reads a binding of a CHANGED pattern still projects that
    /// binding (V05 reads <c>a</c> of <c>([a], b)</c>); one whose output reads nothing its pattern binds is
    /// no projection at all and runs as the ordinary call it is.
    /// </summary>
    [Fact]
    public async Task AHelperWhoseOutputReadsNoOwnBinding_RunsAsAnOrdinaryCall()
    {
        var root = Parse("a, b = (1, 2)\nk = 5\na");
        var aBody = TargetBody(root, "a");
        var call = HelperCall(aBody);
        var helper = Helper(call);
        // `c` returns `b + 0` (no parameter read): not a projection, its ordinary body runs.
        var computed = aBody with { Output = [call with { Function = new Expr.AlgorithmExpr(helper with { Output = [new Expr.Binary(BinaryOp.Add, new Expr.Param("b"), new Expr.Num(0))] }) }] };
        // `d` returns the parameter `b`, not its target `a`: the projection follows the output.
        var other = aBody with { Output = [call with { Function = new Expr.AlgorithmExpr(helper with { Output = [new Expr.Param("b")] }) }] };
        var program = WithPropertyAndRows(root, null, "a", "c", "d") with
        {
            Properties = [.. root.Properties, new Property("c", computed), new Property("d", other)],
        };
        foreach (var route in Enum.GetValues<Route>())
        {
            var memo = await Observe(new Expr.AlgorithmExpr(program), route);
            var ordinary = await Observe(new Expr.AlgorithmExpr(WithoutDeconstructionMetadata(program)), route);
            Assert.Equal("ok S[1, 2, 2] n=3 | ", memo.Comparable);
            Assert.Equal(ordinary.Comparable, memo.Comparable);
        }
    }

    // ───────────────────────── store invariant, cleanup, cancellation ─────────────────────────

    private static DeconstructionBindingExecution Execution(object group)
        => new(group, new object(), new object(), new object(),
            new ZeroArgPropertyCacheKey(ZeroArgPropertyCacheAccessShape.Lexical, new object(), new object(), new object(), new object()));

    private static IReadOnlyDictionary<string, NeedCell> Bound(int value)
        => new Dictionary<string, NeedCell>(StringComparer.Ordinal) { ["x"] = NeedCell.Ready(new(new Result.Atom(value), 1)) };

    [Fact]
    public void FailedOrNestedBinds_AreNeverStored_AndTheGuardIsReleased()
    {
        var cache = new RunScopedDeconstructionBindingCache();
        var group = new object();
        var outer = Execution(group);
        var inner = Execution(group);

        var failed = cache.GetOrBind(outer, () => new EvalError.ArityMismatch(2, 1));
        Assert.True(failed.IsError);
        Assert.Equal(0, cache.Count);
        Assert.Equal(0, cache.RunningGroupCount);

        // A bind started while another bind of its group runs is never stored; the outer one is.
        var binds = 0;
        var result = cache.GetOrBind(outer, () =>
        {
            binds++;
            Assert.Equal(1, cache.RunningGroupCount);
            var nested = cache.GetOrBind(inner, () => { binds++; return EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(1)); });
            Assert.True(nested.IsOk);
            return EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(2));
        });
        Assert.True(result.IsOk);
        Assert.Equal(2, binds);
        Assert.Equal(1, cache.Count);
        Assert.Equal(0, cache.RunningGroupCount);
        Assert.Same(result.Value, cache.GetOrBind(outer, () => throw new InvalidOperationException("a stored bind must hit")).Value);

        // The nested execution was not stored: outside any running bind it binds again, and is stored now.
        Assert.True(cache.GetOrBind(inner, () => { binds++; return EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(3)); }).IsOk);
        Assert.Equal(3, binds);
        Assert.Equal(2, cache.Count);
        Assert.Equal(0, cache.RunningGroupCount);
    }

    [Fact]
    public void ACancelledBind_LeavesNoGuardAndNoEntry_AndTheNextBindRuns()
    {
        var cache = new RunScopedDeconstructionBindingCache();
        var execution = Execution(new object());
        using var cts = new CancellationTokenSource();
        cts.Cancel();

        Assert.Throws<OperationCanceledException>(() => cache.GetOrBind(execution, () => throw new OperationCanceledException(cts.Token)));
        Assert.Equal(0, cache.RunningGroupCount);
        Assert.Equal(0, cache.Count);
        Assert.True(cache.GetOrBind(execution, () => EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(1))).IsOk);
        Assert.Equal(1, cache.Count);
    }

    [Fact]
    public async Task AGenuinelySuspendedBind_CancelledBehindAGate_LeavesNoGuardAndNoEntry()
    {
        var cache = new RunScopedDeconstructionBindingCache();
        var execution = Execution(new object());
        using var cts = new CancellationTokenSource();
        var gate = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);

        var pending = cache.GetOrBindAsync(execution, async () =>
        {
            entered.SetResult();
            await gate.Task.WaitAsync(cts.Token);
            return EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(1));
        }).AsTask();
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(30));
        Assert.False(pending.IsCompleted);
        Assert.Equal(1, cache.RunningGroupCount);

        cts.Cancel();
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => pending.WaitAsync(TimeSpan.FromSeconds(30)));
        Assert.Equal(0, cache.RunningGroupCount);
        Assert.Equal(0, cache.Count);
        Assert.True((await cache.GetOrBindAsync(execution, () => new(EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(2))))).IsOk);
        Assert.Equal(1, cache.Count);
    }

    /// <summary>
    /// End to end: a run cancelled inside a deconstruction's right-hand side (synchronously, and on the
    /// genuinely suspending async route behind a gate) throws the host's cancellation, and a fresh run of
    /// the SAME host-transformed AST then computes the ordinary value with ordinary accounting.
    /// </summary>
    [Fact]
    public async Task CancellationInsideTheRightHandSide_LeavesNothingForAFreshRun()
    {
        // H04's shape with effects: `c` applies a's helper to `q`, rows c, a, b.
        static Algorithm.User Transformed()
        {
            var root = Parse("a, b = trace(1), 2\nq = (7, trace(8))\na");
            var aBody = TargetBody(root, "a");
            return WithPropertyAndRows(root, new Property("c", aBody with { Output = [HelperCall(aBody) with { Args = [new Expr.Resolve("q")] }] }), "c", "a", "b");
        }

        var source = new Expr.AlgorithmExpr(Transformed());

        using (var cts = new CancellationTokenSource())
        {
            var operations = HostOperations.Create(
                HostOperation.Create("tick", (_, _) => new Result.Atom(0)),
                HostOperation.Create("trace", (args, _) => { cts.Cancel(); return args[0]; }, "x"));
            Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(source, hostOperations: operations, cancellationToken: cts.Token));
        }

        using (var cts = new CancellationTokenSource())
        {
            var gate = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var operations = HostOperations.Create(
                HostOperation.Create("tick", (_, _) => new Result.Atom(0)),
                HostOperation.CreateAsync("trace", async (args, token) =>
                {
                    entered.TrySetResult();
                    await gate.Task.WaitAsync(token);
                    return args[0];
                }, "x"));
            var pending = Evaluator.RunCountedObservedAsync(source, hostOperations: operations, cancellationToken: cts.Token).AsTask();
            await entered.Task.WaitAsync(TimeSpan.FromSeconds(30));
            Assert.False(pending.IsCompleted);
            cts.Cancel();
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => pending.WaitAsync(TimeSpan.FromSeconds(30)));
        }

        var reference = await Observe(source, Route.Generic);
        Assert.Equal("ok S[7, 1, 2] n=3 | t(8),t(1)", reference.Comparable);
        foreach (var route in Enum.GetValues<Route>())
        {
            var fresh = await Observe(source, route);
            Assert.Equal(reference.ToString(), fresh.ToString());
            Assert.Equal(reference.Comparable, (await Observe(new Expr.AlgorithmExpr(WithoutDeconstructionMetadata(Transformed())), route)).Comparable);
        }
    }

    /// <summary>
    /// One shared, host-transformed AST graph evaluated by many concurrent runs: each run has its own memo
    /// and property cache, so every run computes the ordinary values (no cross-run aliasing).
    /// </summary>
    [Fact]
    public void ConcurrentRunsOverOneTransformedGraph_StayIsolated()
    {
        var cases = new[] { "H04", "V05", "V07", "D3-FRESH", "L01" }
            .Select(id => (Id: id, Program: HostCorpus.Single(entry => entry.Id == id).Build(false)))
            .ToArray();
        var outcomes = new string[cases.Length * 16];
        Parallel.For(0, outcomes.Length, index =>
        {
            var (id, program) = cases[index % cases.Length];
            outcomes[index] = id + " " + Observe(program, index % 2 == 0 ? Route.Generic : Route.Optimized).GetAwaiter().GetResult().Comparable;
        });
        for (var index = 0; index < outcomes.Length; index++)
        {
            var id = cases[index % cases.Length].Id;
            Assert.Equal(id + " " + HostExpectations[id], outcomes[index]);
        }
    }

    /// <summary>
    /// A loaded module is spliced as its import view, which rewrites a collecting group's pattern list
    /// ONCE (the collect marker's span is cleared) and shares the rewritten list among the group's helpers:
    /// the module's targets read from one context still share one bind.
    /// </summary>
    [Fact]
    public async Task ImportViewOfAModuleGroup_StillSharesOneBind()
    {
        var options = new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("h, *t = 1, 2, 3\npublic H = h\npublic T = t\n0") };
        var parsed = await Parser.ParseAsync("M = load('https://katlang.org/decon/group.kat')\nM.H, M.T, M.H", options);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var observations = new EvaluationObservations();
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), observations: observations);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        Assert.Equal("S[1, L[2, 3], 1]", SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(1, observations.DeconstructionFullBindCount);
    }
}
