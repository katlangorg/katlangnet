using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Nameless host properties in pre-evaluation alias validation and in the duplicate-property check (2026-11-23,
/// follow-up of <c>4bce6327</c>). A host-built property list can hold a property whose name is null; no front end
/// builds one. The host contract (<c>docs/design/language-rules/evaluator-and-hosting.md</c>) is the ordered scan,
/// which compares that name like any other: a named lookup never selects such a property, a null lookup selects the
/// first one, and the empty name is an ordinary name, distinct from null.
/// <para>Two places did not follow it. Pre-evaluation validation of a tree with a callable alias threw
/// <see cref="ArgumentNullException"/> at every width, in tree from <c>RegionFreeNames</c> (the canonical name-set
/// interner refuses a null element) and through a prewired host parent from <c>StaticAliasTargets.Lookup</c> (its
/// name index refused a null key). And the duplicate verdict was the duplicated NAME, so a nameless pair answered
/// null, which also means "no duplicate": <c>[null, null, D, D]</c> was evaluated as if every name were unique.
/// Since this change the alias validator selects as the ordered scan does, and the verdict is the duplicating
/// property, so a nameless pair is a duplicate like any other name, refused in declaration order with
/// <see cref="EvalError.DuplicateProperty"/> whose name is null.</para>
/// <para>Every program runs on the public synchronous entry point, the public asynchronous one (without host
/// operations, and with an asynchronous host operation, which takes the async twin), the generic and optimized
/// evaluators and the forced async twin, which must agree. Each nameless case is compared with a NAMED control:
/// the same program with every null name replaced by a fresh name behaves the same way.</para>
/// </summary>
public class NamelessHostPropertyPreflightTests
{
    // ── AST vocabulary ───────────────────────────────────────────────────────────────────────────

    private static Algorithm.User Body(IReadOnlyList<Property> properties, params Expr[] rows)
        => new(null, [], [], properties, new OutputBundle(rows));

    private static Property Constant(string name, int value) => new(name, Body([], new Expr.Num(value)));

    // `x => x + delta`, so each callable a lookup can select returns a value of its own.
    private static Algorithm.User Inc(int delta)
        => new(null, [new CaptureParameterPattern("x")], [], [],
            new OutputBundle([new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(delta))]));

    private static Property AliasOf(string name, Expr target) => new(name, new Algorithm.Alias(null, [], [], target));

    private static Expr R(string name) => new Expr.Resolve(name);

    private static Expr Dot(Expr target, string name) => new Expr.DotCall(target, name);

    private static Expr Call(Expr callee, params Expr[] args) => new Expr.Call(callee, new OutputBundle(args));

    private static Expr CallA(int argument = 5) => Call(R("A"), new Expr.Num(argument));

    private static Expr Root(IReadOnlyList<Property> properties, params Expr[] rows) => new Expr.AlgorithmExpr(Body(properties, rows));

    // `members`, padded with distinct constants to `width` properties.
    private static List<Property> Padded(int width, params Property[] members)
        => [.. members, .. Enumerable.Range(0, Math.Max(0, width - members.Length)).Select(i => Constant($"Pad{i}", i))];

    /// <summary>The established host pattern: <c>open { public Run = rows }</c> whose PREWIRED parent is <paramref name="scope"/>; output <c>Run</c>.</summary>
    private static Expr OpenedThrough(ScopeCtx scope, params Expr[] rows)
        => new Expr.AlgorithmExpr(new Algorithm.User(null, [],
            [new Expr.AlgorithmExpr(new Algorithm.User(scope, [], [], [new Property("Run", Body([], rows), IsPublic: true)], OutputBundle.Empty))],
            [], new OutputBundle([R("Run")])));

    private static ScopeCtx Scope(IReadOnlyList<Property> properties) => new(null, [], properties);

    // ── Routes ───────────────────────────────────────────────────────────────────────────────────

    private static string Quote(string? name) => name is null ? "<null>" : "\"" + name + "\"";

    // An outcome that tells a null name from the empty one, which the errors' own text does not.
    private static string Describe(EvalResult<Result> result)
    {
        if (result.IsOk)
            return "ok " + SixRouteAgreement.Neutral(result.Value);
        var inner = result.Error;
        while (inner is EvalError.WithContext frame)
            inner = frame.Inner;
        var name = inner switch
        {
            EvalError.DuplicateProperty duplicate => " name=" + Quote(duplicate.Name),
            EvalError.UnknownName unknown => " name=" + Quote(unknown.Name),
            _ => "",
        };
        return $"err {inner.Code}{name} @ {result.Error.Span} | {KatLangError.FromEvalError(result.Error).Message}";
    }

    private static EvalResult<Result> ToResult(EvalResult<Evaluator.CountedResult> counted)
        => counted.IsError ? counted.Error : EvalResult<Result>.Ok(counted.Value.Value);

    /// <summary>
    /// <paramref name="program"/> on every route — the public synchronous and asynchronous entry points (the latter
    /// also with an asynchronous host operation configured, so it runs the async twin), the generic and optimized
    /// evaluators and the forced async twin — one host-built tree for all of them. They must agree; the agreed
    /// outcome is returned.
    /// </summary>
    private static async Task<string> OnEveryRouteAsync(Expr program)
    {
        static Result Seven() => new Result.Atom((Decimal128)7);
        var synchronous = HostOperations.Create(HostOperation.Create("tock", (_, _) => Seven()));
        var suspending = HostOperations.Create(HostOperation.CreateAsync("tock", async (_, _) => { await Task.Yield(); return Seven(); }));
        string[] outcomes =
        [
            Describe(Evaluator.Run(program)),
            Describe(Evaluator.Run(program, synchronous, limits: null, randomSeed: null, CancellationToken.None)),
            Describe(await Evaluator.RunAsync(program)),
            Describe(await Evaluator.RunAsync(program, suspending, limits: null, randomSeed: null, CancellationToken.None)),
            Describe(ToResult(Evaluator.RunCountedObserved(program, enableOptimizations: false).Result)),
            Describe(ToResult(Evaluator.RunCountedObserved(program, enableOptimizations: true).Result)),
            Describe(ToResult((await Evaluator.RunCountedObservedAsync(program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache())).Result)),
        ];
        Assert.All(outcomes, outcome => Assert.Equal(outcomes[0], outcome));
        return outcomes[0];
    }

    /// <summary>
    /// Runs the program <paramref name="build"/> makes for the name null, and its NAMED control: the same program
    /// built for the name <c>"N"</c>. Returns both agreed outcomes.
    /// </summary>
    private static async Task<(string Nameless, string Named)> WithNamedControlAsync(Func<string, Expr> build)
        => (await OnEveryRouteAsync(build(null!)), await OnEveryRouteAsync(build("N")));

    public static TheoryData<int> AliasWidths => [3, 31, 32];

    // ── Pre-evaluation alias validation ─────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(AliasWidths))]
    public async Task AnAliasBesideNamelessRows_IsValidatedAndCalled_InTreeAndThroughAPrewiredParent(int width)
    {
        // Each program held one nameless row (or a pair, where no body evaluation checks duplicates) and a callable
        // alias, and threw ArgumentNullException before this change. Each now runs as its named control does.
        (string, string)[] observed =
        [
            // In tree: the root declares the nameless row beside the alias and its target.
            await WithNamedControlAsync(n => Root(Padded(width, Constant(n, 99), new("F", Inc(1)), AliasOf("A", R("F"))), CallA())),
            // In tree: a nameless pair in a receiver, which a member read never checks for duplicates, read through the
            // alias path and directly.
            await WithNamedControlAsync(n => Root(
                [new("R", Body(Padded(width, Constant(n, 99), Constant(n, 98), Constant("V", 4), new("F", Inc(1))))), AliasOf("A", Dot(R("R"), "F"))],
                CallA(), Dot(R("R"), "V"))),
            // In tree: the alias's own declarations hold the nameless row.
            await WithNamedControlAsync(n => Root(
                Padded(width, new("F", Inc(1)), new("A", new Algorithm.Alias(null, [], [Constant(n, 7)], R("F")))), CallA())),
            // Prewired parent: one nameless row, and a pair (a scope is no body evaluation), beside the alias.
            await WithNamedControlAsync(n => OpenedThrough(Scope(Padded(width, Constant(n, 99), new("F", Inc(1)), AliasOf("A", R("F")))), CallA())),
            await WithNamedControlAsync(n => OpenedThrough(Scope(Padded(width, Constant(n, 99), Constant(n, 98), new("F", Inc(1)), AliasOf("A", R("F")))), CallA())),
            // Prewired parent whose own parent declares the alias.
            await WithNamedControlAsync(n => OpenedThrough(
                new ScopeCtx(Scope([new("F", Inc(1)), AliasOf("A", R("F"))]), [], Padded(width, Constant(n, 99), Constant("V", 4))), CallA(), R("V"))),
        ];

        Assert.Equal(["ok 6", "ok S[6, 4]", "ok 6", "ok 6", "ok 6", "ok S[6, 4]"], observed.Select(static pair => pair.Item1));
        Assert.All(observed, static pair => Assert.Equal(pair.Item2, pair.Item1));
    }

    [Theory]
    [MemberData(nameof(AliasWidths))]
    public async Task AnAliasTargetingTheNullName_SelectsTheFirstNamelessProperty_AndTheEmptyNameIsAnOrdinaryName(int width)
    {
        // The static chase and the call select what the ordered scan selects: `Resolve(null)` the first nameless
        // property, `Resolve("")` the property named "", in tree, through a receiver and through a prewired parent.
        Assert.Equal("ok S[15, 105]", await OnEveryRouteAsync(Root(
            Padded(width, new("", Inc(100)), new(null!, Inc(10)), AliasOf("A", R(null!)), AliasOf("E", R(""))), CallA(), Call(R("E"), new Expr.Num(5)))));
        Assert.Equal("ok S[25, 205]", await OnEveryRouteAsync(Root(
            [new("R", Body(Padded(width, new(null!, Inc(20)), new("", Inc(200)), new(null!, Inc(21))))),
             AliasOf("A", Dot(R("R"), null!)), AliasOf("E", Dot(R("R"), ""))],
            CallA(), Call(R("E"), new Expr.Num(5)))));
        Assert.Equal("ok 35", await OnEveryRouteAsync(OpenedThrough(Scope(Padded(width, new(null!, Inc(30)), AliasOf("A", R(null!)))), CallA())));

        // Missing-name controls: with no such property the null target and the empty target are distinct unknown names.
        var missingNull = await OnEveryRouteAsync(Root(Padded(width, AliasOf("A", R(null!))), CallA()));
        var missingEmpty = await OnEveryRouteAsync(Root(Padded(width, AliasOf("A", R(""))), CallA()));
        Assert.StartsWith("err UnknownName name=<null>", missingNull, StringComparison.Ordinal);
        Assert.StartsWith("err UnknownName name=\"\"", missingEmpty, StringComparison.Ordinal);
        var (missing, missingNamed) = await WithNamedControlAsync(n => Root(Padded(width, Constant(n, 99), AliasOf("A", R("Missing"))), CallA()));
        Assert.StartsWith("err UnknownName name=\"Missing\"", missing, StringComparison.Ordinal);
        Assert.Equal(missingNamed, missing);
    }

    [Theory]
    [MemberData(nameof(AliasWidths))]
    public async Task AliasViolations_BesideAndThroughNamelessRows_AreRefusedAsTheirNamedControls(int width)
    {
        const string cycle = "err IllegalInEval @  | Illegal in eval: callable alias cycle: an alias target leads back to an alias already on its chain";
        // A cycle closed through a nameless alias, a cycle beside a nameless row, and a target that is no static path.
        var (through, throughNamed) = await WithNamedControlAsync(n => Root(Padded(width, AliasOf(n, R("A")), AliasOf("A", R(n))), CallA()));
        var (beside, besideNamed) = await WithNamedControlAsync(n => Root(Padded(width, Constant(n, 99), AliasOf("A", R("B")), AliasOf("B", R("A"))), CallA()));
        var (notStatic, notStaticNamed) = await WithNamedControlAsync(n => Root(Padded(width, Constant(n, 99), AliasOf("A", new Expr.Num(1))), CallA()));
        var (parent, parentNamed) = await WithNamedControlAsync(n => OpenedThrough(Scope(Padded(width, AliasOf(n, R("A")), AliasOf("A", R(n)))), CallA()));

        Assert.Equal(cycle, through);
        Assert.Equal(cycle, beside);
        Assert.Equal(cycle, parent);
        Assert.StartsWith("err IllegalInEval @  | Illegal in eval: callable alias target 1 is not a name or a declared member path", notStatic, StringComparison.Ordinal);
        Assert.Equal([throughNamed, besideNamed, notStaticNamed, parentNamed], [through, beside, notStatic, parent]);
    }

    [Fact]
    public async Task ASharedBodyReachedInTwoContexts_IsCheckedInEachForANullAliasHead_AsForANamedOne()
    {
        // ONE body B = { A1 = <head> } under two parents. Under P1 the head selects P1's callable; under P2 it selects
        // P2's alias T = S.A1, which leads back to A1. Validation checks B again under P2 only if B's region tells the
        // two parents apart, and then reports the cycle while visiting A1, closed by T: the error carries T's target
        // span. A free null head must split the regions; otherwise B is skipped under P2
        // and the cycle is reported later, from T, with A1's target span — where the named control reports T's.
        var headSpan = new SourceSpan(3, 1, 3, 2);
        var closingSpan = new SourceSpan(7, 1, 7, 5);
        Expr Build(string head)
        {
            var shared = Body([AliasOf("A1", new Expr.Resolve(head) { Span = headSpan })], new Expr.Num(0));
            var closing = new Algorithm.Alias(null, [], [], new Expr.DotCall(R("S"), "A1") { Span = closingSpan });
            return Root(
                [new("P1", Body([new(head, Inc(1)), new("S", shared)], new Expr.Num(1))),
                 new("P2", Body([new("S", shared), new(head, closing)], new Expr.Num(2)))],
                new Expr.Num(0));
        }

        var nameless = await OnEveryRouteAsync(Build(null!));
        Assert.Equal(await OnEveryRouteAsync(Build("N")), nameless);
        Assert.StartsWith($"err IllegalInEval @ {closingSpan} | Illegal in eval: callable alias cycle", nameless, StringComparison.Ordinal);
    }

    [Fact]
    public void AnAliasWithALocallyBoundNullHead_ValidatesASharedGraphOncePerRelevantContext()
    {
        const int depth = 8;
        long Expansions(string head)
        {
            Algorithm shared = Body([], new Expr.Num(1));
            for (var level = 0; level < depth; level++)
            {
                Algorithm Branch() => new Algorithm.Alias(null, [], [new Property(head, shared)], R(head));
                shared = Body([new("L", Branch()), new("R", Branch())], R("L"));
            }

            var observations = new FrontEndTraversalObservations();
            Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(new Expr.AlgorithmExpr(shared), observations));
            return observations.WalkerAlgorithmExpansions;
        }

        var named = Expansions("S");
        Assert.Equal(3 * depth + 1, named);
        Assert.Equal(named, Expansions(null!));
    }

    [Theory]
    [MemberData(nameof(AliasWidths))]
    public async Task AliasLookupOfANamelessMember_PreservesOpenVisibilityAndLocalOnlyAccess(int width)
    {
        Expr Opened(string head) => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [R("M")],
            [new("M", Body(Padded(width, new(head, Inc(100)), new Property(head, Inc(10), IsPublic: true)))),
                AliasOf("A", R(head))], new OutputBundle([CallA()])));
        var opened = await WithNamedControlAsync(Opened);
        Assert.Equal(("ok 15", "ok 15"), opened);

        Expr LocalOnly(string head)
        {
            var hidden = new Property(head, Inc(1), IsPublic: false, PropertyExposure.LocalOnlyCapturedAncestorParameters)
                { RequiredAncestorParameters = ["p"] };
            return Root([new("R", Body(Padded(width, hidden))), AliasOf("A", Dot(R("R"), head))], CallA());
        }

        var (nameless, named) = await WithNamedControlAsync(LocalOnly);
        Assert.StartsWith("err LocalOnlyProperty", nameless, StringComparison.Ordinal);
        Assert.Equal(named.Replace("'N'", "''"), nameless);
    }

    // ── The duplicate-property check ─────────────────────────────────────────────────────────────

    // Both sides of the pairwise scan limit (16) and the set scan beyond it.
    public static TheoryData<int> DuplicateWidths => [4, AlgorithmAccessors.LinearDuplicatePropertyScanLimit, AlgorithmAccessors.LinearDuplicatePropertyScanLimit + 1, 40];

    [Theory]
    [MemberData(nameof(DuplicateWidths))]
    public async Task ANamelessPair_IsADuplicateLikeAnyName_FirstInDeclarationOrder_OnBothScanWidths(int width)
    {
        // An evaluated root holding the rows (padded to `width`). The first duplicate in declaration order is
        // reported; a nameless pair no longer reads as "no duplicate" and so no longer hides a later named one.
        async Task<string> Check(params string?[] names)
        {
            Expr Build(string nameless) => Root(Padded(width, [.. names.Select((name, i) => Constant(name ?? nameless, i + 1))]), new Expr.Num(1));
            var outcome = await OnEveryRouteAsync(Build(null!));
            // The named control: a fresh name where each null stood behaves the same, with that name reported.
            Assert.Equal((await OnEveryRouteAsync(Build("N"))).Replace("name=\"N\"", "name=<null>").Replace("'N'", "''"), outcome);
            return outcome;
        }

        const string namelessDuplicate = "err DuplicateProperty name=<null> @  | Property '' is already defined";
        Assert.Equal(namelessDuplicate, await Check(null, null, "D", "D"));
        Assert.Equal(namelessDuplicate, await Check(null, "D", null, "D"));
        Assert.Equal(namelessDuplicate, await Check(null, null));
        Assert.Equal("err DuplicateProperty name=\"D\" @  | Property 'D' is already defined", await Check(null, "D", "D", null));
        Assert.Equal("err DuplicateProperty name=\"D\" @  | Property 'D' is already defined", await Check(null, "D", "D"));
        Assert.Equal("err DuplicateProperty name=\"D\" @  | Property 'D' is already defined", await Check("D", "D"));
        // The empty name is an ordinary name, distinct from null: its duplicate names "", and one of each is unique.
        Assert.Equal("err DuplicateProperty name=\"\" @  | Property '' is already defined", await Check("", ""));
        Assert.Equal("ok 1", await Check(null, ""));
        Assert.Equal("ok 1", await Check([null]));

        // The public name-valued accessor is unchanged: a nameless first duplicate's name is null, as is "none".
        var refused = Body(Padded(width, Constant(null!, 1), Constant(null!, 2), Constant("D", 3), Constant("D", 4)));
        Assert.Null(refused.FindDuplicatePropName());
        Assert.Same(refused.Properties[1], Evaluator.FirstDuplicateProperty(refused, Evaluator.EvalCtx.Empty.Budget));
    }

    [Theory]
    [MemberData(nameof(DuplicateWidths))]
    public async Task ANamelessDuplicate_IsRefusedWhereverABodyIsEntered(int width)
    {
        // A called body, and the step of each loop builtin (a raw builtin block: a host chain has no prelude).
        Algorithm.User Step(string nameless, bool isWhile)
            => new(null, [new CaptureParameterPattern("s")], [], Padded(width, Constant(nameless, 1), Constant(nameless, 2)),
                new OutputBundle(isWhile
                    ? [new Expr.Binary(BinaryOp.Add, new Expr.Param("s"), new Expr.Num(1)), new Expr.Comparison(new Expr.Param("s"), [new ComparisonLink(ComparisonOp.Lt, new Expr.Num(3))])]
                    : [new Expr.Binary(BinaryOp.Add, new Expr.Param("s"), new Expr.Num(1))]));
        Expr Loop(string nameless, BuiltinId loop)
            => Root([new("Step", Step(nameless, loop == BuiltinId.@while))], Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(loop)),
                loop == BuiltinId.@while ? [Call(R("Step"), new Expr.Num(0))] : [Call(R("Step"), new Expr.Num(0)), new Expr.Num(3)]));

        var (called, calledNamed) = await WithNamedControlAsync(n => Root([new("F", Step(n, isWhile: false))], Call(R("F"), new Expr.Num(1))));
        var (repeated, repeatedNamed) = await WithNamedControlAsync(n => Loop(n, BuiltinId.@repeat));
        var (whiled, whiledNamed) = await WithNamedControlAsync(n => Loop(n, BuiltinId.@while));
        foreach (var (outcome, named) in new[] { (called, calledNamed), (repeated, repeatedNamed), (whiled, whiledNamed) })
        {
            Assert.StartsWith("err DuplicateProperty name=<null> @  | ", outcome, StringComparison.Ordinal);
            Assert.Equal(named.Replace("name=\"N\"", "name=<null>").Replace("'N'", "''"), outcome);
        }

        // One nameless row is no duplicate.
        Assert.Equal("ok 3", await OnEveryRouteAsync(Root([new("Step", new Algorithm.User(null, [new CaptureParameterPattern("s")], [],
            Padded(width, Constant(null!, 1)), new OutputBundle([new Expr.Binary(BinaryOp.Add, new Expr.Param("s"), new Expr.Num(1))])))],
            Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.@repeat)), Call(R("Step"), new Expr.Num(0)), new Expr.Num(3)))));
    }

    [Theory]
    [InlineData(1, false)]
    [InlineData(2, true)]
    public void TheLoopPlanner_RefusesAStepWithANamelessPair_AsAStepWithANamedPair(int namelessRows, bool refused)
    {
        // The planner binds a step only if its body has no duplicate property; it asks the evaluator's verdict, so a
        // nameless pair falls back to the generic loop, which refuses it, exactly like a named pair.
        foreach (var name in new[] { null!, "N" })
        {
            var properties = Enumerable.Range(0, namelessRows).Select(i => Constant(name, i)).ToArray();
            var step = new Algorithm.User(null, [new CaptureParameterPattern("s")], [], properties, OutputBundle.From([new Expr.Num(0)]));
            var diagnostics = new LoopOptimizationDiagnostics();
            var ctx = Evaluator.EvalCtx.Empty with
            {
                Budget = EvaluationBudget.Create(null),
                Services = Evaluator.RunServices.Unconfigured with { LoopDiagnostics = diagnostics },
            };
            var planned = LoopOptimizer.TryEvaluateRepeat(step, count: 2, [new Result.Atom(0)], ctx, [],
                (_, _, _) => throw new Xunit.Sdk.XunitException("no generic continuation is expected"), out var result);

            Assert.Equal(!refused, planned);
            if (refused)
                Assert.Equal(1, Assert.Contains("loop plan parameter/property shape mismatch", diagnostics.FallbackReasons));
            else
                Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        }
    }
}
