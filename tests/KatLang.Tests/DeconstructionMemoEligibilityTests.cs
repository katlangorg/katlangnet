using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// DECON-CACHE-2 (October 2026): the run-scoped shared bind of an assignment-deconstruction group
/// (<see cref="RunScopedDeconstructionBindingCache"/>) must never change what a target computes. A
/// memo result is trusted only when the helper that would run ordinarily binds the SAME actual
/// pattern to the SAME actual source entry and that read obtains the source's PUBLISHED value (Q-37);
/// every other helper shape executes its ordinary bind. Since OD-1 (October 2026) the reader is no part
/// of the key: every consumer of one published source entry through one pattern list — callbacks,
/// helpers, explicit <c>a()</c> calls, structural and opened reads of one declaring activation — shares
/// ONE bind. Local-only sources separate declaring activations and loop rounds; exported sources keep
/// one entry across activations. Distinct source owners and host scopes keep distinct entries and binds.
///
/// <para>The host witnesses are the DECON-CACHE-1 research's (`experimental/features/decon-cache-1-research.md`
/// §4): parsed ASTs transformed with public record copies (<c>with</c>), shared property lists and
/// ownerless host scopes. Each is checked on the generic, optimized and genuinely suspending async
/// routes against its ORDINARY reference — the same AST whose target helpers carry no
/// deconstruction metadata, so every target runs its helper as an ordinary call — and against the
/// reviewed expected value (uncached C# and, for the pure cases, Lean). The surface corpus pins the
/// OD-1 accounting of ordinary parser output (values, effects, steps, checkpoints, peak depth,
/// materialized items and full binds) on every route next to the DECON-CACHE-2 baseline it replaced,
/// and checks that the difference is exactly the eliminated binds.</para>
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

    /// <summary>
    /// The run's property cache, wrapped so that it states NO publication provenance when
    /// <paramref name="shareBinds"/> is false: every helper then takes its own unshared bind — the
    /// specialized binder with the memo out of the picture, i.e. the deconstruction cache uncached
    /// while the property cache keeps its ordinary law.
    /// </summary>
    private static IAsyncZeroArgPropertyResultCache? PropertyCache(Route route, bool shareBinds)
        => (route, shareBinds) switch
        {
            (Route.SuspendingAsync, true) => new SuspendingAsyncZeroArgPropertyResultCache(),
            (Route.SuspendingAsync, false) => new NoBindSharingPropertyCache(new SuspendingAsyncZeroArgPropertyResultCache()),
            (_, true) => null,
            (_, false) => new NoBindSharingPropertyCache(new RunScopedAsyncZeroArgPropertyResultCache()),
        };

    /// <summary>Forwards everything except <see cref="IZeroArgPropertyResultCache.ReadObtainsPublishedValue"/> (default <c>false</c>).</summary>
    private sealed class NoBindSharingPropertyCache(IAsyncZeroArgPropertyResultCache inner) : IAsyncZeroArgPropertyResultCache
    {
        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
            => inner.GetOrEvaluate(execution, evaluate);

        public EvalResult<ZeroArgPropertyResult> Invoke(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
            => inner.Invoke(execution, evaluate);

        public ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
            ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
            => inner.GetOrEvaluateAsync(execution, evaluateAsync);

        public ValueTask<EvalResult<ZeroArgPropertyResult>> InvokeAsync(
            ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
            => inner.InvokeAsync(execution, evaluateAsync);
    }

    internal static async Task<Observation> Observe(Expr program, Route route, EvaluationLimits? limits = null, bool shareBinds = true)
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
                program, limits, PropertyCache(route, shareBinds), observations: observations,
                hostOperations: operations, randomSeed: 7));
        }
        else
        {
            var operations = HostOperations.Create(
                HostOperation.Create("tick", (_, _) => Tick()),
                HostOperation.Create("trace", (args, _) => Trace(args[0]), "x"));
            (result, budget) = Evaluator.RunCountedObserved(
                program, limits, enableOptimizations: route == Route.Optimized, zeroArgPropertyResultCache: PropertyCache(route, shareBinds), observations: observations,
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

    /// <summary>
    /// COPY: <c>c</c> is an UNCHANGED copy of target <c>a</c>'s body (same helper, same pattern list, same
    /// argument), so it reads the same published source entry through the same pattern and shares a's bind.
    /// </summary>
    private static Algorithm.User UnchangedHelperCopy(params string[] rows)
    {
        var root = Parse("a, b = tick(), 2\na");
        return WithPropertyAndRows(root, new Property("c", TargetBody(root, "a") with { }), rows);
    }

    /// <summary>
    /// IDX: <c>c</c> is <c>a</c>'s body whose helper copy records target index 1 while its output still reads
    /// <c>a</c> — metadata no longer describes the helper, so it runs as the ordinary call (returning <c>a</c>).
    /// </summary>
    private static Algorithm.User ChangedTargetIndexCopy(params string[] rows)
    {
        var root = Parse("a, b = tick(), 2\na");
        var aBody = TargetBody(root, "a");
        var call = HelperCall(aBody);
        var helper = Helper(call);
        var moved = helper with { AssignmentDeconstructionTarget = helper.AssignmentDeconstructionTarget!.Value with { Index = 1 } };
        return WithPropertyAndRows(root, new Property("c", aBody with { Output = [call with { Function = new Expr.AlgorithmExpr(moved) }] }), rows);
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

    // ───────────────────────── surface accounting (OD-1 cross-consumer sharing) ─────────────────────────

    /// <summary>
    /// The DECON-CACHE-1 surface corpus (R01–R29, X01, X04, V01–V11 and three extra shapes) plus the OD-1
    /// additions: property-cache RHS sharing, read orders (both directions), sibling callbacks and helpers,
    /// collecting targets demanded early, late or never, opened targets, explicit <c>a()</c>, equal and
    /// distinct activations, recursion, Q-37 re-entry, loops (zero rounds, entered rounds, per-round
    /// activations, steps reading targets), nested unpacking, seeded random, META capture and runtime
    /// aliases, forwarding, an alias right-hand side, a failing right-hand side first demanded from a
    /// callback, and step/materialization limits on both sides of the bound.
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
        // OD-1 additions: read-order reversal, sibling callbacks, collectors demanded late / never, loop
        // steps reading targets, nested unpacking, a failing right-hand side first demanded from a
        // callback, and near-limit runs that still fail after the eliminated binds.
        ("R02-REVERSED", "F(k) = {\n    B = {\n        a, b = trace(k), k + 1\n        a + b\n    }\n    B.b + [1, 2].map{ n + B.a }[0]\n}\nF(3)", null),
        ("R02-MaxSteps9", "F(k) = {\n    B = {\n        a, b = trace(k), k + 1\n        a + b\n    }\n    [1, 2].map{ n + B.a }[0] + B.b\n}\nF(3)", new EvaluationLimits { MaxSteps = 9 }),
        ("V02-MaxItems10", "F(k) = {\n    h, *t = trace(k), k + 1, k + 2\n    [1, 2, 3].map{ n * 0 + t().count }.sum + h\n}\nF(3)", new EvaluationLimits { MaxMaterializedItems = 10 }),
        ("SIBLING-CALLBACKS", "F(k) = {\n    a, b = trace(k), k + 1\n    [1].map{ n + a }[0] + [2].map{ n + b }[0] + [3].map{ n + a() }[0] + b()\n}\nF(3)", null),
        ("UNUSED-COLLECTOR", "F(k) = {\n    h, *t = trace(k), k + 1, k + 2\n    [1].map{ n + h }[0] + h\n}\nF(3)", null),
        ("LATE-COLLECTOR", "F(k) = {\n    h, *t = trace(k), k + 1, k + 2\n    [1].map{ n + h }[0] + [1].map{ n * 0 + t().count }[0] + t.count + t().count\n}\nF(3)", null),
        ("LOOP-STEP-READS", "F(k) = {\n    a, b = trace(k), k + 1\n    Step(s) = s + a + [0].map{ n + b }[0]\n    Step(0).repeat(3), Step(0).repeat(0)\n}\nF(3)", null),
        ("NESTED-UNPACK", "F(k) = {\n    p, *r = trace(k), (k, k + 1), k + 2\n    x, y = r[0]\n    [0].map{ n + x }[0] + y + [0].map{ n + p }[0] + r.count\n}\nF(3)", null),
        ("FAIL-FROM-CALLBACK", "F(k) = {\n    a, b = trace(k), 1 / 0\n    [1].map{ n + a }[0] + b\n}\nF(3)", null),
    ];

    /// <summary>
    /// The DECON-CACHE-2 baseline (HEAD 852d0b3c, the integrated correctness fix, before OD-1): the
    /// observation of every surface case under the former per-reader key, identical on all three routes.
    /// Kept beside <see cref="SurfaceExpectations"/> as the record of what OD-1 changed; checked against
    /// it by <see cref="Od1AccountingChange_IsExactlyTheEliminatedBinds"/>.
    /// </summary>
    private static readonly Dictionary<string, string> Decon2Baseline = new(StringComparer.Ordinal)
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
        ["R02-REVERSED"] = "ok 8 n=1 | t(3) | steps=11 chk=40 depth=5 items=6 binds=2",
        ["R02-MaxSteps9"] = "err EvaluationStepLimitExceeded: Evaluation step limit of 9 was exceeded @ [6:32, 6:35) | t(3) | steps=9 chk=38 depth=6 items=6 binds=1",
        ["V02-MaxItems10"] = "err MaterializationLimitExceeded: Evaluation materialization limit of 10 items was exceeded @ [3:28, 3:31) | t(3) | steps=14 chk=63 depth=6 items=10 binds=3",
        ["SIBLING-CALLBACKS"] = "ok 20 n=1 | t(3) | steps=17 chk=71 depth=6 items=8 binds=4",
        ["UNUSED-COLLECTOR"] = "ok 7 n=1 | t(3) | steps=7 chk=37 depth=6 items=5 binds=1",
        ["LATE-COLLECTOR"] = "ok 10 n=1 | t(3) | steps=14 chk=69 depth=6 items=11 binds=3",
        ["LOOP-STEP-READS"] = "ok S[21, 0] n=1 | t(3) | steps=18 chk=89 depth=5 items=10 binds=2",
        ["NESTED-UNPACK"] = "ok 12 n=1 | t(3) | steps=17 chk=73 depth=9 items=11 binds=4",
        ["FAIL-FROM-CALLBACK"] = "err DivisionByZero: while evaluating call to F: while evaluating dotCall .map of [1]: while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact): Division by zero @ [2:22, 2:27) | t(3) | steps=6 chk=24 depth=6 items=1 binds=1",
    };

    /// <summary>
    /// The OD-1 observation of every surface case (identical on all three routes): one full bind per
    /// published source entry and pattern list in every shape that does not re-enter its group — R02,
    /// R04–R09, R18–R22, R25, R28, X01, V01, V03, V11 and the additions bind once where the per-reader key
    /// bound per consumer —, one per ACTIVATION where activations differ (R10/R11 and X04/V09/V10 two,
    /// R27 three, R16/R26 one per loop round), and unchanged counts under re-entry (R12's seven binds, the
    /// Q-37 cases R13–R15 and R29).
    /// </summary>
    private static readonly Dictionary<string, string> SurfaceExpectations = new(StringComparer.Ordinal)
    {
        ["R01"] = "ok 15 n=1 | t(3) | steps=13 chk=49 depth=7 items=6 binds=1",
        ["R02"] = "ok 8 n=1 | t(3) | steps=10 chk=39 depth=6 items=6 binds=1",
        ["R02-MaxSteps10"] = "ok 8 n=1 | t(3) | steps=10 chk=39 depth=6 items=6 binds=1",
        ["R02-MaxSteps11"] = "ok 8 n=1 | t(3) | steps=10 chk=39 depth=6 items=6 binds=1",
        ["R03"] = "ok 15 n=1 | t(3) | steps=13 chk=49 depth=5 items=6 binds=1",
        ["R04"] = "ok 8 n=1 | t(3) | steps=8 chk=26 depth=6 items=2 binds=1",
        ["R05"] = "ok 8 n=1 | t(3) | steps=8 chk=32 depth=6 items=4 binds=1",
        ["R06"] = "ok 12 n=1 | t(3) | steps=12 chk=69 depth=6 items=9 binds=1",
        ["R07"] = "ok 19 n=1 | t(3) | steps=14 chk=45 depth=6 items=8 binds=1",
        ["R08"] = "ok 4 n=1 | t(1) | steps=7 chk=26 depth=5 items=4 binds=1",
        ["R09"] = "ok 4 n=1 | t(1) | steps=7 chk=26 depth=5 items=4 binds=1",
        ["R10"] = "ok S[4, 6] n=2 | t(1),t(2) | steps=16 chk=64 depth=6 items=10 binds=2",
        ["R11"] = "ok S[4, 4] n=2 | t(1),t(1) | steps=16 chk=64 depth=6 items=10 binds=2",
        ["R12"] = "ok 6 n=1 |  | steps=27 chk=95 depth=16 items=8 binds=7",
        ["R13"] = "ok S[2, 2, 5] n=3 | tick#1,tick#2,tick#3 | steps=15 chk=50 depth=10 items=9 binds=3",
        ["R14"] = "ok S[2, 2, 5] n=3 | tick#1,tick#2,tick#3 | steps=17 chk=84 depth=12 items=13 binds=3",
        ["R15"] = "ok S[6, 5, 6] n=3 | tick#1,tick#2,tick#3 | steps=14 chk=49 depth=10 items=9 binds=3",
        ["R16"] = "ok 2 n=1 |  | steps=16 chk=63 depth=3 items=6 binds=3",
        ["R17"] = "ok 0 n=1 |  | steps=4 chk=12 depth=3 items=2 binds=1",
        ["R18"] = "ok 13 n=1 | t(3) | steps=12 chk=39 depth=5 items=2 binds=1",
        ["R19"] = "ok 8 n=1 | t(3) | steps=10 chk=61 depth=6 items=9 binds=1",
        ["R20"] = "ok S[true, true] n=1 |  | steps=11 chk=56 depth=6 items=8 binds=1",
        ["R21"] = "ok 14 n=1 | t(3) | steps=12 chk=50 depth=6 items=4 binds=1",
        ["R22"] = "ok 8 n=1 | t(3) | steps=10 chk=36 depth=7 items=4 binds=1",
        ["R23"] = "err DivisionByZero: while evaluating call to F: Division by zero @ [2:22, 2:27) | t(3) | steps=5 chk=15 depth=5 items=0 binds=1",
        ["R24"] = "ok 3 n=1 |  | steps=1 chk=3 depth=1 items=0 binds=0",
        ["R25"] = "ok 8 n=1 | t(3) | steps=8 chk=41 depth=6 items=6 binds=1",
        ["R26"] = "ok 3 n=1 |  | steps=12 chk=48 depth=3 items=6 binds=3",
        ["R27"] = "ok L[11, 22, 33] n=1 |  | steps=21 chk=93 depth=5 items=18 binds=3",
        ["R28"] = "ok 10 n=1 | t(3) | steps=10 chk=49 depth=6 items=6 binds=1",
        ["R29"] = "ok S[2, 6] n=2 | tick#1,tick#2,tick#3,tick#4,tick#5,tick#6,tick#7,tick#8 | steps=24 chk=114 depth=12 items=14 binds=4",
        ["X01"] = "ok 14 n=1 | t(3) | steps=11 chk=50 depth=6 items=4 binds=1",
        ["X04"] = "ok 16 n=1 | t(3),t(3) | steps=18 chk=72 depth=7 items=8 binds=2",
        ["V01"] = "ok 9 n=1 | t(3) | steps=14 chk=66 depth=6 items=11 binds=1",
        ["V02-MaxItems11"] = "ok 9 n=1 | t(3) | steps=14 chk=66 depth=6 items=11 binds=1",
        // M4★: `public A = a` and `public Z = b` are transparent aliases, so their two property reads are
        // gone (formerly steps=10 chk=34 depth=7; Od1AccountingChange_IsExactlyTheEliminatedBinds).
        ["V03"] = "ok 8 n=1 | t(3) | steps=8 chk=32 depth=6 items=4 binds=1",
        ["V04"] = "ok 0 n=1 |  | steps=0 chk=3 depth=0 items=0 binds=0",
        ["V08-MaxDepth5"] = "err EvaluationDepthExceeded: Evaluation recursion limit of 5 was exceeded @ [2:18, 2:19) |  | steps=5 chk=16 depth=5 items=1 binds=1",
        ["V09"] = "ok 16 n=1 | t(3),t(3) | steps=18 chk=76 depth=7 items=8 binds=2",
        ["V10"] = "ok 16 n=1 | t(3),t(3) | steps=17 chk=68 depth=7 items=8 binds=2",
        ["V11"] = "ok 9 n=1 | t(3),t(3) | steps=12 chk=46 depth=6 items=4 binds=1",
        ["ALIAS-RHS"] = "ok S[4, 1, 2] n=3 | t(1) | steps=10 chk=29 depth=6 items=7 binds=1",
        ["WIDE-BODY"] = "ok S[21, 6, 1] n=3 |  | steps=15 chk=34 depth=3 items=9 binds=1",
        ["COLLECT-WIDE"] = "ok 15 n=1 | t(3) | steps=11 chk=62 depth=5 items=8 binds=1",
        ["R02-REVERSED"] = "ok 8 n=1 | t(3) | steps=10 chk=39 depth=5 items=6 binds=1",
        ["R02-MaxSteps9"] = "err EvaluationStepLimitExceeded: Evaluation step limit of 9 was exceeded @ [6:32, 6:35) | t(3) | steps=9 chk=38 depth=6 items=6 binds=1",
        ["V02-MaxItems10"] = "err MaterializationLimitExceeded: Evaluation materialization limit of 10 items was exceeded @ [3:5, 3:39) | t(3) | steps=12 chk=62 depth=6 items=8 binds=1",
        ["SIBLING-CALLBACKS"] = "ok 20 n=1 | t(3) | steps=14 chk=68 depth=6 items=8 binds=1",
        ["UNUSED-COLLECTOR"] = "ok 7 n=1 | t(3) | steps=7 chk=37 depth=6 items=5 binds=1",
        ["LATE-COLLECTOR"] = "ok 10 n=1 | t(3) | steps=12 chk=67 depth=6 items=9 binds=1",
        ["LOOP-STEP-READS"] = "ok S[21, 0] n=1 | t(3) | steps=17 chk=88 depth=5 items=10 binds=1",
        ["NESTED-UNPACK"] = "ok 12 n=1 | t(3) | steps=15 chk=71 depth=9 items=11 binds=2",
        ["FAIL-FROM-CALLBACK"] = "err DivisionByZero: while evaluating call to F: while evaluating dotCall .map of [1]: while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact): Division by zero @ [2:22, 2:27) | t(3) | steps=6 chk=24 depth=6 items=1 binds=1",
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
    /// Every observed field of every surface case equals its OD-1 expectation on every route: one bind
    /// per published source entry across consumers (R02, R06, R07 — a key that still named the reader
    /// would bind per consumer and fail these), one per activation and loop round (R10, R11, R16, R26,
    /// R27), the group-wide guard's recursive accounting (R12's seven binds — a full-key guard would
    /// store the inner activations' binds and lower it), and the limit verdicts the eliminated work
    /// moves: R02 now completes at <c>MaxSteps = 10</c> and still refuses at 9; V02 now completes at
    /// <c>MaxMaterializedItems = 11</c> and still refuses at 10.
    /// </summary>
    [Theory]
    [MemberData(nameof(SurfaceCases))]
    public async Task SurfaceProgram_HasItsOd1Accounting(string id, Route route)
    {
        var (_, source, limits) = SurfaceCorpus.Single(entry => entry.Id == id);
        var observed = await Observe(new Expr.AlgorithmExpr(Parse(source)), route, limits);
        Assert.Equal(SurfaceExpectations[id], observed.ToString());
    }

    private static readonly System.Text.RegularExpressions.Regex ObservationShape = new(
        @"^(?<outcome>.*) \| (?<effects>[^|]*) \| steps=(?<steps>\d+) chk=(?<chk>\d+) depth=(?<depth>\d+) items=(?<items>\d+) binds=(?<binds>\d+)$");

    /// <summary>
    /// THE OD-1 ACCOUNTING LAW FOR THIS CORPUS, checked between the two pinned tables. Under the former per-reader key a
    /// consumer whose first read of a target missed the memo performed one more full bind than OD-1 does,
    /// and that bind's only extra charged work was its read of the hoisted source — one step and one
    /// expression checkpoint (the RHS itself ran once either way: the property cache) — plus, for a
    /// collector it materialized, that list's reservation. So for every case the run reaches in both
    /// configurations: the outcome, the host effects and their order, and the peak depth are equal; the
    /// bind count never grows; the steps AND the checkpoints fall by exactly the number of eliminated
    /// binds; materialized items never grow and fall only where a collector stopped being
    /// re-materialized. Every remaining operation is still charged. Peak-depth equality is specific to
    /// this original corpus; <see cref="DeeperConsumer_SkipsTheRepeatedSourceReadDepth"/> pins a case
    /// where eliminating the source-read invocation also lowers peak depth.
    /// The verdicts that change are exactly the near-limit runs whose limit sat inside the eliminated
    /// work (R02 at <c>MaxSteps = 10</c>, V02 at <c>MaxMaterializedItems = 11</c>), and the one refusal
    /// that moves is V02 at 10: with the collector materialized once, the run reaches the limit later, at
    /// the <c>map</c> result's reservation instead of the second <c>t()</c> collector.
    /// </summary>
    [Fact]
    public void Od1AccountingChange_IsExactlyTheEliminatedBinds()
    {
        Assert.Equal(Decon2Baseline.Keys.Order(StringComparer.Ordinal), SurfaceExpectations.Keys.Order(StringComparer.Ordinal));
        Assert.Equal(SurfaceCorpus.Select(entry => entry.Id).Order(StringComparer.Ordinal), SurfaceExpectations.Keys.Order(StringComparer.Ordinal));
        var changedVerdicts = new HashSet<string>(StringComparer.Ordinal) { "R02-MaxSteps10", "V02-MaxItems11" };
        var movedRefusals = new HashSet<string>(StringComparer.Ordinal) { "V02-MaxItems10" };
        var collectorSavings = new HashSet<string>(StringComparer.Ordinal) { "V01", "LATE-COLLECTOR" };
        // M4★: V03's `public A = a` and `public Z = b` became transparent aliases, so beside the bind OD-1
        // eliminated their two property READS are gone as well — one step and one checkpoint each, and the
        // alias hop's depth level (an alias charges nothing of its own). Decon2Baseline stays the measured
        // pre-M4★ record.
        var aliasReclassified = new Dictionary<string, (long Reads, long Depth)>(StringComparer.Ordinal) { ["V03"] = (2, 1) };
        var reduced = new List<string>();
        foreach (var id in SurfaceExpectations.Keys)
        {
            var before = ObservationShape.Match(Decon2Baseline[id]);
            var after = ObservationShape.Match(SurfaceExpectations[id]);
            Assert.True(before.Success && after.Success, id);
            long Field(System.Text.RegularExpressions.Match match, string name) => long.Parse(match.Groups[name].Value);
            Assert.Equal(before.Groups["effects"].Value, after.Groups["effects"].Value);
            var eliminated = Field(before, "binds") - Field(after, "binds");
            Assert.True(eliminated >= 0, id);
            if (eliminated > 0)
                reduced.Add(id);
            if (changedVerdicts.Contains(id))
            {
                Assert.StartsWith("err ", before.Groups["outcome"].Value);
                Assert.StartsWith("ok ", after.Groups["outcome"].Value);
                continue;
            }

            if (movedRefusals.Contains(id))
            {
                Assert.StartsWith("err MaterializationLimitExceeded", before.Groups["outcome"].Value);
                Assert.StartsWith("err MaterializationLimitExceeded", after.Groups["outcome"].Value);
                Assert.NotEqual(before.Groups["outcome"].Value, after.Groups["outcome"].Value);
                continue;
            }

            Assert.Equal(before.Groups["outcome"].Value, after.Groups["outcome"].Value);
            var (aliasReads, aliasDepth) = aliasReclassified.GetValueOrDefault(id);
            Assert.Equal(Field(before, "depth") - aliasDepth, Field(after, "depth"));
            Assert.Equal(eliminated + aliasReads, Field(before, "steps") - Field(after, "steps"));
            Assert.Equal(eliminated + aliasReads, Field(before, "chk") - Field(after, "chk"));
            if (collectorSavings.Contains(id))
                Assert.True(Field(after, "items") < Field(before, "items"), id);
            else
                Assert.Equal(Field(before, "items"), Field(after, "items"));
        }

        // Exactly the cross-consumer shapes changed; recursion, Q-37 re-entry, per-round loops, single-
        // context reads and unreached groups keep their counts.
        Assert.Equal(
            ["ALIAS-RHS", "LATE-COLLECTOR", "LOOP-STEP-READS", "NESTED-UNPACK", "R02", "R02-MaxSteps10", "R02-MaxSteps11",
             "R02-REVERSED", "R04", "R05", "R06", "R07", "R08", "R09", "R10", "R11", "R18", "R19", "R20", "R21", "R22", "R25",
             "R27", "R28", "SIBLING-CALLBACKS", "V01", "V02-MaxItems10", "V02-MaxItems11", "V03", "V09", "V10", "V11", "X01", "X04"],
            reduced.Order(StringComparer.Ordinal));
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

    /// <summary>
    /// The memo-vs-no-memo differential of OD-1: the same parsed program run with bind sharing and with
    /// every helper taking its own unshared bind (<see cref="NoBindSharingPropertyCache"/>, the
    /// deconstruction memo uncached) gives the same value, emitted count, full error text and span, and
    /// host effects in order, on every route, for every unlimited surface case and every host witness.
    /// Only the accounting may differ, and only downward: sharing never binds MORE often than not
    /// sharing, never charges more steps, and never materializes more items.
    /// </summary>
    [Theory]
    [MemberData(nameof(SurfaceCases))]
    public async Task SurfaceProgram_MatchesItsUnsharedBindExecution(string id, Route route)
    {
        var (_, source, limits) = SurfaceCorpus.Single(entry => entry.Id == id);
        if (limits is not null)
            return;
        var program = new Expr.AlgorithmExpr(Parse(source));
        AssertSharingOnlyLowersAccounting(await Observe(program, route), await Observe(program, route, shareBinds: false));
    }

    [Theory]
    [MemberData(nameof(HostCases))]
    public async Task HostTransformedAst_MatchesItsUnsharedBindExecution(string id, Route route)
    {
        var build = HostCorpus.Single(entry => entry.Id == id).Build;
        AssertSharingOnlyLowersAccounting(await Observe(build(false), route), await Observe(build(false), route, shareBinds: false));
    }

    private static void AssertSharingOnlyLowersAccounting(Observation shared, Observation unshared)
    {
        Assert.Equal(unshared.Outcome + " | " + unshared.Effects, shared.Outcome + " | " + shared.Effects);
        Assert.True(shared.Binds <= unshared.Binds, $"{shared} vs {unshared}");
        Assert.True(shared.Steps <= unshared.Steps, $"{shared} vs {unshared}");
        Assert.True(shared.Materialized <= unshared.Materialized, $"{shared} vs {unshared}");
    }

    /// <summary>
    /// A deeper consumer can avoid the source read's invocation level as well as its step. This is
    /// deliberate accounting for eliminated work: peak depth may fall, and a depth limit can change
    /// verdict even though the original corpus happened to keep its peak depth. The source is first
    /// bound by the owner, then its second target is demanded through two nested helpers.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task DeeperConsumer_SkipsTheRepeatedSourceReadDepth(Route route)
    {
        const string source = "F(k) = {\n a, b = k, k + 1\n a\n G(x) = {\n H(y) = y + b\n H(x)\n }\n G(0)\n}\nF(3)";
        var program = new Expr.AlgorithmExpr(Parse(source));
        var shared = await Observe(program, route);
        var unshared = await Observe(program, route, shareBinds: false);
        Assert.Equal("ok S[3, 4] n=1 | ", shared.Comparable);
        AssertSharingOnlyLowersAccounting(shared, unshared);
        Assert.Equal(1, shared.Binds);
        Assert.Equal(2, unshared.Binds);
        Assert.Equal(5, shared.PeakDepth);
        Assert.Equal(6, unshared.PeakDepth);
        Assert.Equal(8, shared.Steps);
        Assert.Equal(9, unshared.Steps);
        Assert.Equal(22, shared.Checkpoints);
        Assert.Equal(23, unshared.Checkpoints);
        Assert.Equal(4, shared.Materialized);
        Assert.Equal(shared.Materialized, unshared.Materialized);

        var limit = new EvaluationLimits { MaxDepth = 5 };
        Assert.Equal(shared.Comparable, (await Observe(program, route, limit)).Comparable);
        Assert.StartsWith("err EvaluationDepthExceeded:", (await Observe(program, route, limit, shareBinds: false)).Outcome);
        var lowerLimit = new EvaluationLimits { MaxDepth = 4 };
        Assert.StartsWith("err EvaluationDepthExceeded:", (await Observe(program, route, lowerLimit)).Outcome);
        Assert.StartsWith("err EvaluationDepthExceeded:", (await Observe(program, route, lowerLimit, shareBinds: false)).Outcome);
    }

    /// <summary>
    /// Exported sources already have one published entry across owner activations. Different calls
    /// can first demand different targets of that entry and share its bind; local-only sources keep
    /// the per-activation separation pinned by R10/R11. Ownership follows the source cache law.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task ExportedSource_DifferentActivationsShareItsPublishedEntry(Route route)
    {
        const string source = "F(k) = {\n a, b = trace(1), 2\n if(k == 1, [0].map{ n + a }[0], b)\n}\nF(1), F(2)";
        var program = new Expr.AlgorithmExpr(Parse(source));
        var shared = await Observe(program, route);
        var unshared = await Observe(program, route, shareBinds: false);
        Assert.Equal("ok S[1, 2] n=2 | t(1)", shared.Comparable);
        AssertSharingOnlyLowersAccounting(shared, unshared);
        Assert.Equal(1, shared.Binds);
        Assert.Equal(2, unshared.Binds);
    }

    /// <summary>
    /// Keeping an undemanded collector alive must not keep its original consumer alive. Its Ready
    /// slice and run budget suffice; first demand still reserves the exact list once, and subsequent
    /// demands reuse that completion. This tests reachability rather than compiler closure layout.
    /// </summary>
    [Fact]
    public void UndemandedCollector_ReleasesItsConsumer_AndReservesOnlyOnFirstDemand()
    {
        var (cell, budget, consumer) = CollectorWithUnrelatedConsumer();
        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
        Assert.False(consumer.IsAlive);
        Assert.Equal(0, budget.MaterializedItems);
        var first = cell.Demand();
        Assert.True(first.IsOk);
        Assert.Equal("L[1, 2]", SixRouteAgreement.Neutral(first.Value.Value));
        Assert.Equal(2, budget.MaterializedItems);
        var again = cell.Demand();
        Assert.True(again.IsOk);
        Assert.Same(first.Value.Value, again.Value.Value);
        Assert.Equal(2, budget.MaterializedItems);
        GC.KeepAlive(cell);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static (NeedCell Cell, EvaluationBudget Budget, WeakReference Consumer) CollectorWithUnrelatedConsumer()
    {
        var consumer = Parse("123");
        var ctx = Evaluator.EvalCtx.Empty.Push(consumer);
        var slice = new[] { NeedCell.Ready(new(new Result.Atom(1), 1)), NeedCell.Ready(new(new Result.Atom(2), 1)) };
        var cell = (NeedCell)typeof(Evaluator).GetMethod("CollectorCell", System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Static)!
            .Invoke(null, [slice, ctx])!;
        return (cell, ctx.Budget, new WeakReference(consumer));
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
        ("COPY", ordinary => Program(UnchangedHelperCopy("c", "a", "b"), ordinary)),
        ("IDX", ordinary => Program(ChangedTargetIndexCopy("c", "b"), ordinary)),
        ("IDX-B-FIRST", ordinary => Program(ChangedTargetIndexCopy("b", "c"), ordinary)),
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
        ["COPY"] = "ok S[1, 1, 2] n=3 | tick#1",
        ["IDX"] = "ok S[1, 2] n=2 | tick#1",
        ["IDX-B-FIRST"] = "ok S[2, 1] n=2 | tick#1",
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
    /// re-entrant inner bind unstorable, so the later target binds the published source again. An
    /// unchanged helper copy under another property (COPY) reads the same entry through the same pattern
    /// and shares the bind (OD-1: the key names no reader or caller scope); a copy whose target index no
    /// longer matches its output (IDX) runs the ordinary call and binds nothing.
    /// </summary>
    [Theory]
    [InlineData("COPY", 1)]
    [InlineData("IDX", 1)]
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
        => new(group, new object(),
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
    /// The optimized route of the loop cases really runs the PLANNED loop (not a generic fallback), and the
    /// planned iterations keep OD-1's accounting: a per-round deconstruction (R16, R26) still binds once per
    /// round — the planned loop's per-iteration identity keeps the rounds' local-only sources apart — while
    /// steps reading an enclosing activation's targets (R18, LOOP-STEP-READS) share its one bind.
    /// </summary>
    [Theory]
    [InlineData("R16")]
    [InlineData("R18")]
    [InlineData("R26")]
    [InlineData("LOOP-STEP-READS")]
    public void PlannedLoopRoute_KeepsTheOd1Accounting(string id)
    {
        var program = new Expr.AlgorithmExpr(Parse(SurfaceCorpus.Single(entry => entry.Id == id).Source));
        var diagnostics = new LoopOptimizationDiagnostics();
        var observations = new EvaluationObservations();
        var operations = HostOperations.Create(
            HostOperation.Create("tick", (_, _) => new Result.Atom(0)),
            HostOperation.Create("trace", (args, _) => args[0], "x"));
        var (result, budget) = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics, observations: observations,
            hostOperations: operations, randomSeed: 7);
        Assert.True(result.IsOk);
        Assert.True(diagnostics.OptimizedLoopHits > 0, $"{id} must take the planned loop");
        var expected = ObservationShape.Match(SurfaceExpectations[id]);
        Assert.Equal(long.Parse(expected.Groups["binds"].Value), observations.DeconstructionFullBindCount);
        Assert.Equal(long.Parse(expected.Groups["steps"].Value), budget.ConsumedSteps);
    }

    /// <summary>
    /// OD-1 isolation across runs: concurrent independent runs of programs that share a bind across
    /// consumers (R02, V01's collector, R10/R11's two activations, R27's per-item activations) each observe
    /// exactly their own one-run accounting — the bind counts and materializations included — so no shared
    /// bind, collector cell or completion leaks between runs or activations.
    /// </summary>
    [Fact]
    public void ConcurrentRunsOfSharingPrograms_KeepTheirOwnAccounting()
    {
        var ids = new[] { "R02", "V01", "R10", "R11", "R27", "SIBLING-CALLBACKS" };
        var programs = ids.Select(id => (Id: id, Program: (Expr)new Expr.AlgorithmExpr(Parse(SurfaceCorpus.Single(entry => entry.Id == id).Source)))).ToArray();
        var outcomes = new string[programs.Length * 16];
        Parallel.For(0, outcomes.Length, index =>
        {
            var (id, program) = programs[index % programs.Length];
            outcomes[index] = id + " " + Observe(program, index % 2 == 0 ? Route.Generic : Route.Optimized).GetAwaiter().GetResult();
        });
        for (var index = 0; index < outcomes.Length; index++)
        {
            var id = programs[index % programs.Length].Id;
            Assert.Equal(id + " " + SurfaceExpectations[id], outcomes[index]);
        }
    }

    /// <summary>
    /// Cancellation inside a bind that later consumers would share (V01: a collecting group first demanded
    /// from a callback), synchronously and on the genuinely suspending async route behind a gate, stores
    /// nothing a later run could see: a fresh run of the SAME AST then has exactly the OD-1 accounting on
    /// every route (one bind, eleven materialized items).
    /// </summary>
    [Fact]
    public async Task CancellationInsideASharedBind_LeavesNothingForAFreshRun()
    {
        var source = new Expr.AlgorithmExpr(Parse(SurfaceCorpus.Single(entry => entry.Id == "V01").Source));

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

        foreach (var route in Enum.GetValues<Route>())
            Assert.Equal(SurfaceExpectations["V01"], (await Observe(source, route)).ToString());
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
