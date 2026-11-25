using KatLang.Evaluation;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Host-built PARENT scopes are validated before evaluation (owner decision, 2026-10-12).
/// <para>A user algorithm, a clause family and a callable alias each carry an optional parent
/// <see cref="ScopeCtx"/>. No front end builds one; a host may. Wiring a property or a program root
/// replaces it, but an <c>open</c> block target that already has one KEEPS it
/// (<c>Evaluator.WireOpenBlockToGlobalScope</c>), and the opened block's members then resolve names
/// in that scope. Its members are reachable at run time.</para>
/// <para>The pre-evaluation walker (<c>AlgorithmValidation.FindFirstPreEvaluationViolation</c>) now
/// walks every parent scope a tree carries (<c>PreEvaluationValidationWalker.VisitParentScopes</c>),
/// wherever the scope sits and whether or not anything reads it. It covers each scope's <c>open</c>
/// targets and property algorithms, after the carrying algorithm's own content, then the scope's own
/// parent. A member is held to the same rules, with the same error, as an ordinary property.
/// Formerly the walk never entered a parent scope, which let an unbuildable loop step reach the
/// planner (F7-D6, <see cref="LoopPlanEligibilityFailClosedTests"/>).</para>
/// <para>Lean: <c>validateScopeTree</c>, guarded by <c>lean/CoreTests/ParentScopeValidation.lean</c>,
/// whose sections these tests mirror. The collecting clause binder rule is C#-only, as everywhere.</para>
/// </summary>
public class HostBuiltParentScopeValidationTests
{
    private static readonly Expr Seven = new Expr.Num(7);
    private static readonly Expr FortyTwo = new Expr.Num(42);

    // ── 1. Valid parent scopes keep working ──────────────────────────────────────────────────

    [Fact]
    public async Task OpenedBlock_ReadsItsParentScopesMembers()
    {
        await AssertAccepted(OpenedThrough(Scope([ValueMember()]), new Expr.Resolve("V")), new Result.Atom(7));
        await AssertAccepted(
            OpenedThrough(Scope([StepMember()]), new Expr.Call(new Expr.Resolve("Step"), [new Expr.Num(4)])),
            new Result.Atom(5));
        await AssertAccepted(OpenedThrough(Scope([], Scope([ValueMember()])), new Expr.Resolve("V")), new Result.Atom(7));
        await AssertAccepted(HeldBy(Scope([ValueMember()])), new Result.Atom(42));
    }

    /// <summary>
    /// A valid alias chain in a parent scope is no cycle, and an alias whose target the OUTER scope
    /// declares resolves there: the members are validated against the scope chain they resolve
    /// names in. (Lean also counts the chain's aliases as the static chase's fuel; C# chases with a
    /// visited set.)
    /// </summary>
    [Fact]
    public async Task ValidAliasesInParentScopes_AreNoCycle()
    {
        Property[] chain =
        [
            new("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("B"))),
            new("B", new Algorithm.Alias(null, [], [], new Expr.Resolve("F"))),
            new("F", Callable([Capture("x")], new Expr.Param("x"))),
        ];
        var callA = new Expr.Call(new Expr.Resolve("A"), [new Expr.Num(5)]);

        await AssertAccepted(OpenedThrough(Scope(chain), callA), new Result.Atom(5));
        await AssertAccepted(HeldBy(Scope(chain)), new Result.Atom(42));
        await AssertAccepted(
            OpenedThrough(
                Scope([new("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("F")))],
                    Scope([new("F", Callable([Capture("x")], new Expr.Param("x")))])),
                callA),
            new Result.Atom(5));
    }

    // ── 2. Every rule holds in a parent scope, in every placement, with the same error ───────

    /// <summary>One invalid member set per pre-evaluation rule, with the error it must produce.</summary>
    private static readonly IReadOnlyDictionary<string, (Func<Property[]> Members, EvalError Expected)> Rules =
        new Dictionary<string, (Func<Property[]>, EvalError)>
        {
            ["two collectors at one level"] = (
                () => [new("Bad", Callable([Collecting("a"), Collecting("b")], new Expr.Param("a")))],
                new EvalError.IllegalInEval(Parser.MultipleCollectingBindingsPerLevelDiagnostic)),
            ["a one-item sequence pattern"] = (
                () => [new("Bad", Callable([new SequenceValueParameterPattern([Capture("x")])], new Expr.Param("x")))],
                new EvalError.IllegalInEval(Parser.SingletonSequencePatternDiagnostic)),
            ["a repeated name that collects"] = (
                () => [new("Bad", Callable([Capture("x"), Collecting("x")], new Expr.Param("x")))],
                new EvalError.IllegalInEval(Parser.RepeatedNameIncludesCollectingDiagnostic)),
            ["parameters without output"] = (
                () => [new("Bad", Callable([Capture("x")]))],
                new EvalError.ExplicitParametersRequireOutput()),
            ["unequal branch arities"] = (
                () => [new("Bad", Family(
                    new CondBranch(new Pattern.LitInt(0), Callable([], new Expr.Num(1))),
                    new CondBranch(new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]),
                        Callable([], new Expr.Param("x")))))],
                new EvalError.BranchArityMismatch("Bad", 1, 2)),
            ["unequal branch output arities"] = (
                () => [new("Bad", Family(
                    new CondBranch(new Pattern.LitInt(0), Callable([], new Expr.Num(1))),
                    new CondBranch(new Pattern.Bind("x"), Callable([], new Expr.Param("x"), new Expr.Param("x")))))],
                new EvalError.BranchOutputArityMismatch("Bad", 1, 2)),
            ["a collecting clause binder (C#-only)"] = (
                () => [new("Bad", Family(
                    new CondBranch(new Pattern.Bind("xs") { ParameterKind = ParameterKind.Collecting }, Callable([], new Expr.Num(0)))))],
                new EvalError.IllegalInEval(Parser.CollectingClauseBinderDiagnostic)),
            ["an alias target that is no static path"] = (
                () => [new("Bad", new Algorithm.Alias(null, [], [], new Expr.Num(1)))],
                new EvalError.IllegalInEval(Evaluator.AliasTargetNotStaticPathMessage(new Expr.Num(1)))),
            ["an alias cycle"] = (
                () =>
                [
                    new("X", new Algorithm.Alias(null, [], [], new Expr.Resolve("Y"))),
                    new("Y", new Algorithm.Alias(null, [], [], new Expr.Resolve("X"))),
                ],
                new EvalError.IllegalInEval(Evaluator.AliasCycleMessage)),
        };

    /// <summary>
    /// Where a member set can sit: an ordinary property of the root (the CONTROL), the opened
    /// block's parent scope (REACHABLE), a property's parent scope (DISCARDED), the parent of the
    /// opened block's parent (GRANDPARENT), a family's, an alias's and a block row's parent scope,
    /// and the program root's own.
    /// </summary>
    private static readonly IReadOnlyDictionary<string, Func<Property[], Expr>> Placements =
        new Dictionary<string, Func<Property[], Expr>>
        {
            ["control"] = members => Root(members, Seven),
            ["reachable"] = members => OpenedThrough(Scope(members), Seven),
            ["discarded"] = members => HeldBy(Scope(members)),
            ["grandparent"] = members => OpenedThrough(Scope([], Scope(members)), Seven),
            ["family"] = members => Root(
                [new("P", new Algorithm.Conditional(Scope(members), [],
                    [new CondBranch(new Pattern.Bind("x"), Callable([], new Expr.Param("x")))]))],
                FortyTwo),
            ["alias"] = members => Root(
                [new("F", Callable([Capture("x")], new Expr.Param("x"))),
                    new("P", new Algorithm.Alias(Scope(members), [], [], new Expr.Resolve("F")))],
                FortyTwo),
            ["row block"] = members => Root([], new Expr.AlgorithmExpr(
                new Algorithm.User(Parent: Scope(members), ParameterPatterns: [], Opens: [], Properties: [],
                    Output: OutputBundle.From([Seven])))),
            ["root"] = members => new Expr.AlgorithmExpr(
                new Algorithm.User(Parent: Scope(members), ParameterPatterns: [], Opens: [], Properties: [],
                    Output: OutputBundle.From([FortyTwo]))),
        };

    public static TheoryData<string, string> RuleAndPlacement
    {
        get
        {
            var cases = new TheoryData<string, string>();
            foreach (var rule in Rules.Keys)
                foreach (var placement in Placements.Keys)
                    cases.Add(rule, placement);
            return cases;
        }
    }

    [Theory]
    [MemberData(nameof(RuleAndPlacement))]
    public async Task EveryRule_HoldsInEveryPlacement_WithTheControlsError(string rule, string placement)
    {
        var (members, expected) = Rules[rule];
        var control = Placements["control"](members());
        var program = Placements[placement](members());

        Assert.Equal(Describe(expected), Describe(RefusedBeforeEvaluation(control)));
        Assert.Equal(Describe(expected), Describe(RefusedBeforeEvaluation(program)));

        var (asyncResult, asyncBudget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new SuspendingAsyncZeroArgPropertyResultCache()));
        Assert.True(asyncResult.IsError);
        Assert.Equal(Describe(expected), Describe(asyncResult.Error));
        Assert.Equal(0, asyncBudget.ConsumedSteps);
    }

    /// <summary>The same placements accept valid members, so the refusals above are the rules'.</summary>
    [Fact]
    public void EveryPlacement_AcceptsValidMembers()
    {
        foreach (var (placement, place) in Placements)
        {
            var program = place([ValueMember(), StepMember()]);
            Assert.True(AlgorithmValidation.FindFirstPreEvaluationViolation(program) is null, placement);
            var result = Evaluator.Run(program);
            Assert.False(result.IsError, $"{placement}: {(result.IsError ? result.Error.ToString() : "")}");
        }
    }

    // ── 3. A scope's own open targets are validated too ───────────────────────────────────────

    [Fact]
    public void ParentScopesOpenTargets_AreValidated()
    {
        var expected = new EvalError.IllegalInEval(Parser.MultipleCollectingBindingsPerLevelDiagnostic);
        Expr BadBlock() => new Expr.AlgorithmExpr(new Algorithm.User(Parent: null, ParameterPatterns: [], Opens: [],
            Properties: [new("Bad", Callable([Collecting("a"), Collecting("b")], new Expr.Param("a")), IsPublic: true)],
            Output: OutputBundle.Empty));

        Assert.Equal(Describe(expected),
            Describe(RefusedBeforeEvaluation(OpenedThrough(Scope([ValueMember()], opens: [BadBlock()]), new Expr.Resolve("V")))));
        Assert.Equal(Describe(expected), Describe(RefusedBeforeEvaluation(HeldBy(Scope([], opens: [BadBlock()])))));
    }

    // ── 4. Order: own content, then the parent scope (innermost first), opens before properties ─

    private static Property MultiCollector() => new("Bad", Callable([Collecting("a"), Collecting("b")], new Expr.Param("a")));
    private static Property Singleton() => new("Odd", Callable([new SequenceValueParameterPattern([Capture("x")])], new Expr.Param("x")));
    private static readonly string MultiCollectorFirst = Describe(new EvalError.IllegalInEval(Parser.MultipleCollectingBindingsPerLevelDiagnostic));
    private static readonly string SingletonFirst = Describe(new EvalError.IllegalInEval(Parser.SingletonSequencePatternDiagnostic));

    [Fact]
    public void TheCarryingAlgorithmsOwnContent_IsReportedBeforeItsParentScope()
    {
        Assert.Equal(MultiCollectorFirst, Describe(RefusedBeforeEvaluation(OpenedThrough(Scope([Singleton()]), Seven, MultiCollector()))));
        Assert.Equal(SingletonFirst, Describe(RefusedBeforeEvaluation(OpenedThrough(Scope([MultiCollector()]), Seven, Singleton()))));
    }

    [Fact]
    public void AnInnerScope_IsReportedBeforeItsOuterScope()
    {
        Assert.Equal(MultiCollectorFirst,
            Describe(RefusedBeforeEvaluation(OpenedThrough(Scope([MultiCollector()], Scope([Singleton()])), Seven))));
        Assert.Equal(SingletonFirst,
            Describe(RefusedBeforeEvaluation(OpenedThrough(Scope([Singleton()], Scope([MultiCollector()])), Seven))));
    }

    [Fact]
    public void AScopesOpens_AreReportedBeforeItsProperties()
    {
        var singletonBlock = new Expr.AlgorithmExpr(new Algorithm.User(Parent: null, ParameterPatterns: [], Opens: [],
            Properties: [Singleton() with { IsPublic = true }], Output: OutputBundle.Empty));

        Assert.Equal(SingletonFirst, Describe(RefusedBeforeEvaluation(HeldBy(Scope([MultiCollector()], opens: [singletonBlock])))));
    }

    [Fact]
    public void AnEarlierPropertysParentScope_IsReportedBeforeALaterProperty()
    {
        var program = Root(
            [new("P", new Algorithm.User(Parent: Scope([Singleton()]), ParameterPatterns: [], Opens: [], Properties: [],
                Output: OutputBundle.From([new Expr.Num(1)]))), MultiCollector()],
            FortyTwo);

        Assert.Equal(SingletonFirst, Describe(RefusedBeforeEvaluation(program)));
    }

    /// <summary>
    /// An inner scope's declarations shadow its outer scope's: the members' chain is outermost first.
    /// A cycle among an inner scope's aliases is found although the outer scope declares terminal
    /// callables of the same names.
    /// </summary>
    [Fact]
    public void AnInnerScopesDeclarations_ShadowItsOuterScopes()
    {
        var program = OpenedThrough(
            Scope(
                [
                    new("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("F"))),
                    new("F", new Algorithm.Alias(null, [], [], new Expr.Resolve("A"))),
                ],
                Scope(
                [
                    new("A", Callable([Capture("x")], new Expr.Param("x"))),
                    new("F", Callable([Capture("x")], new Expr.Param("x"))),
                ])),
            Seven);

        Assert.Equal(Describe(new EvalError.IllegalInEval(Evaluator.AliasCycleMessage)), Describe(RefusedBeforeEvaluation(program)));
    }

    /// <summary>
    /// The converse: an outer scope's members resolve names in the outer chain only, never in an
    /// inner scope. A cycle among an outer scope's aliases is found although an inner scope declares
    /// terminal callables of the same names.
    /// </summary>
    [Fact]
    public void AnOuterScopesMembers_NeverResolveInAnInnerScope()
    {
        var program = OpenedThrough(
            Scope(
                [
                    new("A", Callable([Capture("x")], new Expr.Param("x"))),
                    new("F", Callable([Capture("x")], new Expr.Param("x"))),
                ],
                Scope(
                [
                    new("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("F"))),
                    new("F", new Algorithm.Alias(null, [], [], new Expr.Resolve("A"))),
                ])),
            Seven);

        Assert.Equal(Describe(new EvalError.IllegalInEval(Evaluator.AliasCycleMessage)), Describe(RefusedBeforeEvaluation(program)));
    }

    /// <summary>
    /// The walk restores the enclosing chain after a parent scope: a cycle among the root's later
    /// properties is still found once an earlier property's parent scope has been walked.
    /// </summary>
    [Fact]
    public void TheEnclosingChain_IsRestoredAfterAParentScope()
    {
        var program = Root(
            [
                new("P", new Algorithm.User(Parent: Scope([ValueMember()]), ParameterPatterns: [], Opens: [], Properties: [],
                    Output: OutputBundle.From([new Expr.Num(1)]))),
                new("X", new Algorithm.Alias(null, [], [], new Expr.Resolve("Y"))),
                new("Y", new Algorithm.Alias(null, [], [], new Expr.Resolve("X"))),
            ],
            FortyTwo);

        Assert.Equal(Describe(new EvalError.IllegalInEval(Evaluator.AliasCycleMessage)), Describe(RefusedBeforeEvaluation(program)));
    }

    // ── 5. One alias object shared by two parent scopes is judged in each scope's chain ───────

    /// <summary>
    /// The same alias object <c>A = F</c> sits in two parent scopes: one declares a terminal
    /// <c>F</c>, the other <c>F = A</c>, a cycle. The cycle is reported whichever block the root
    /// opens first. The walker keys its alias memo by the scope chain, never by the alias alone,
    /// so settling <c>A</c> in the safe scope must not excuse it in the cyclic one.
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void SharedAliasObject_IsJudgedInEachParentScopesChain(bool cyclicFirst)
    {
        var shared = new Algorithm.Alias(null, [], [], new Expr.Resolve("F"));
        var safe = Scope([new("A", shared), new("F", Callable([Capture("x")], new Expr.Param("x")))]);
        var cyclic = Scope([new("A", shared), new("F", new Algorithm.Alias(null, [], [], new Expr.Resolve("A")))]);
        Expr Opened(ScopeCtx scope) => new Expr.AlgorithmExpr(new Algorithm.User(Parent: scope, ParameterPatterns: [], Opens: [],
            Properties: [], Output: OutputBundle.Empty));
        var program = new Expr.AlgorithmExpr(new Algorithm.User(Parent: null, ParameterPatterns: [],
            Opens: cyclicFirst ? [Opened(cyclic), Opened(safe)] : [Opened(safe), Opened(cyclic)],
            Properties: [], Output: OutputBundle.From([Seven])));

        Assert.Equal(Describe(new EvalError.IllegalInEval(Evaluator.AliasCycleMessage)), Describe(RefusedBeforeEvaluation(program)));
        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(
            new Expr.AlgorithmExpr(new Algorithm.User(Parent: null, ParameterPatterns: [], Opens: [Opened(safe)],
                Properties: [], Output: OutputBundle.From([Seven])))));
    }

    // ── 6. The walk stays linear on shared scopes, and iterative along a deep chain ────────────

    /// <summary>
    /// K holders share ONE parent scope of M members: each holder reaches the scope, but it is
    /// validated once, so the walker expands the root, the K holders and the M members, never K × M.
    /// </summary>
    [Fact]
    public void ASharedParentScope_IsValidatedOnce()
    {
        const int K = 200, M = 200;
        var scope = Scope([.. Enumerable.Range(0, M).Select(i => new Property($"V{i}", Callable([], new Expr.Num(i))))]);
        var program = Root(
            [.. Enumerable.Range(0, K).Select(i => new Property($"P{i}", new Algorithm.User(Parent: scope,
                ParameterPatterns: [], Opens: [], Properties: [], Output: OutputBundle.From([new Expr.Num(1)]))))],
            FortyTwo);

        var observations = new FrontEndTraversalObservations();
        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(program, observations));
        Assert.Equal(1, observations.PreEvaluationParentScopeExpansions);
        Assert.Equal(K, observations.PreEvaluationParentScopeLinks);
        Assert.Equal(1 + K + M, observations.WalkerAlgorithmExpansions);
    }

    /// <summary>
    /// K distinct inner scopes, one per holder, share ONE outer chain of N scopes. Each scope is
    /// validated once, and a walk stops at the first scope already validated: the first holder's
    /// walk reaches its inner scope and the N outer ones, every later one its inner scope and the
    /// innermost outer one, N + 2K - 1 scopes in all, never K × N.
    /// </summary>
    [Fact]
    public void ASharedOuterChain_IsValidatedOnce()
    {
        const int K = 150, N = 150;
        ScopeCtx? outer = null;
        for (var level = 0; level < N; level++)
            outer = Scope([new Property($"O{level}", Callable([], new Expr.Num(level)))], outer);
        var program = Root(
            [.. Enumerable.Range(0, K).Select(i => new Property($"P{i}", new Algorithm.User(
                Parent: Scope([new Property($"I{i}", Callable([], new Expr.Num(i)))], outer),
                ParameterPatterns: [], Opens: [], Properties: [], Output: OutputBundle.From([new Expr.Num(1)]))))],
            FortyTwo);

        var observations = new FrontEndTraversalObservations();
        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(program, observations));
        Assert.Equal(K + N, observations.PreEvaluationParentScopeExpansions);
        Assert.Equal(N + 2 * K - 1, observations.PreEvaluationParentScopeLinks);
        Assert.Equal(1 + 2 * K + N, observations.WalkerAlgorithmExpansions);
    }

    /// <summary>
    /// A chain of 250 parent scopes, within the supported AST depth
    /// (<see cref="EvaluationLimits.MaxSupportedAstDepth"/>): the walk along it is iterative, a valid
    /// member at the outermost level is read through the whole chain, and an invalid one there is
    /// refused.
    /// </summary>
    [Fact]
    public async Task ADeepChain_IsWalkedToItsOutermostScope()
    {
        static ScopeCtx Chain(Property outermost)
        {
            var scope = Scope([outermost]);
            for (var level = 1; level < 250; level++)
                scope = Scope([new Property($"L{level}", Callable([], new Expr.Num(level)))], scope);
            return scope;
        }

        await AssertAccepted(OpenedThrough(Chain(ValueMember()), new Expr.Resolve("V")), new Result.Atom(7));
        Assert.Equal(MultiCollectorFirst, Describe(RefusedBeforeEvaluation(OpenedThrough(Chain(MultiCollector()), Seven))));
    }

    // ── Helpers ──────────────────────────────────────────────────────────────────────────────

    private static CaptureParameterPattern Capture(string name) => new(name);

    private static CaptureParameterPattern Collecting(string name) => new(name, Kind: ParameterKind.Collecting);

    private static Algorithm.User Callable(IReadOnlyList<ParameterPattern> head, params Expr[] rows)
        => new(Parent: null, ParameterPatterns: head, Opens: [], Properties: [], Output: OutputBundle.From(rows));

    private static Algorithm.Conditional Family(params CondBranch[] branches) => new(null, [], branches);

    private static Property ValueMember() => new("V", Callable([], Seven));

    private static Property StepMember()
        => new("Step", Callable([Capture("x")], new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1))));

    /// <summary>A host-built scope declaring <paramref name="properties"/>, with <paramref name="outer"/> its parent.</summary>
    private static ScopeCtx Scope(IReadOnlyList<Property> properties, ScopeCtx? outer = null, IReadOnlyList<Expr>? opens = null)
        => new(outer, opens ?? [], properties);

    private static Expr Root(IReadOnlyList<Property> properties, Expr row)
        => new Expr.AlgorithmExpr(new Algorithm.User(Parent: null, ParameterPatterns: [], Opens: [], Properties: properties,
            Output: OutputBundle.From([row])));

    /// <summary>
    /// REACHABLE: the program <c>open { public Run = row }</c>, run as <c>Run</c>, whose opened block
    /// carries <paramref name="scope"/>; <paramref name="own"/> adds properties to the block itself.
    /// </summary>
    private static Expr OpenedThrough(ScopeCtx scope, Expr row, params Property[] own)
    {
        var block = new Algorithm.User(Parent: scope, ParameterPatterns: [], Opens: [],
            Properties: [new Property("Run", Callable([], row), IsPublic: true), .. own], Output: OutputBundle.Empty);
        return new Expr.AlgorithmExpr(new Algorithm.User(Parent: null, ParameterPatterns: [],
            Opens: [new Expr.AlgorithmExpr(block)], Properties: [], Output: OutputBundle.From([new Expr.Resolve("Run")])));
    }

    /// <summary>DISCARDED: the program holding <c>P</c>, an algorithm carrying <paramref name="scope"/>.</summary>
    private static Expr HeldBy(ScopeCtx scope)
        => Root([new Property("P", new Algorithm.User(Parent: scope, ParameterPatterns: [], Opens: [], Properties: [],
            Output: OutputBundle.From([new Expr.Num(1)])))], FortyTwo);

    /// <summary>
    /// The pre-evaluation walker refuses <paramref name="program"/>, and the run reports the refusal
    /// with nothing evaluated: the run's fresh budget charged nothing.
    /// </summary>
    private static EvalError RefusedBeforeEvaluation(Expr program)
    {
        Assert.NotNull(AlgorithmValidation.FindFirstPreEvaluationViolation(program));
        var (result, budget) = Evaluator.RunCountedObserved(program);
        Assert.True(result.IsError, "expected a refusal");
        Assert.Equal(0, budget.ConsumedSteps);
        Assert.Equal(0, budget.ConsumedExpressionCheckpoints);
        Assert.Equal(0, budget.PeakDepth);
        return result.Error;
    }

    /// <summary>The walker accepts <paramref name="program"/>, and both routes produce <paramref name="expected"/>.</summary>
    private static async Task AssertAccepted(Expr program, Result expected)
    {
        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(program));
        var sync = Evaluator.RunCounted(program);
        Assert.False(sync.IsError, sync.IsError ? sync.Error.ToString() : null);
        Assert.Equal(expected, sync.Value.Value);

        var (asyncResult, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new SuspendingAsyncZeroArgPropertyResultCache()));
        Assert.False(asyncResult.IsError, asyncResult.IsError ? asyncResult.Error.ToString() : null);
        Assert.Equal(expected, asyncResult.Value.Value);
    }

    /// <summary>The error's variant, public code and message: a host-built tree has no spans.</summary>
    private static string Describe(EvalError error)
    {
        var reported = KatLangError.FromEvalError(error);
        return $"{error.GetType().Name} {reported.Code}: {reported.Message}";
    }
}
