using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// The evaluation-error policy decided by Q-27 + Q-06 (P2, 2026-10-05): an evaluation error names the
/// FIRST semantic contract the executed operation cannot satisfy, in that operation's own evaluation
/// order. Missing CALLABLE capability in any invoking position is <c>NotAnAlgorithm</c> — a user
/// parameter, a builtin callback and a loop step alike — diagnosed by CALLABLE projection only, when an
/// invocation is needed, never by demanding the VALUE and never for a slot that is not invoked. A
/// callable whose parameter interface cannot bind the supply, or a wrong emitted slot count, is
/// <c>ArityMismatch</c>; a present VALUE of the wrong kind is <c>TypeMismatch</c>; a selection naming no
/// position (<c>first</c>/<c>last</c> included, SEQ-04) is <c>BadIndex</c>; a value of the accepted kind
/// outside the operation's domain is <c>DivisionByZero</c> or <c>IllegalInEval</c>. NEED-04's
/// repeated-name verdicts are frozen and unchanged. Every program runs on the six established routes
/// (<see cref="SixRouteAgreement"/>), which must agree on outcome, code, message, span and host log.
/// Lean: <c>CoreTests/ErrorTaxonomy.lean</c>; laws <c>first_empty_is_badIndex</c> /
/// <c>last_empty_is_badIndex</c> / <c>first_is_select_zero_total</c> / <c>last_is_select_last_total</c>.
/// </summary>
public class ErrorTaxonomyPolicyTests
{
    private static string CodeOf(SixRouteAgreement.Observation observation)
        => observation.Kind == "err"
            ? observation.Errors[0][..observation.Errors[0].IndexOf(':')]
            : observation.Kind + (observation.Value is null ? "" : " " + observation.Value);

    // ── Q-06: no CALLABLE identity in an invoking position ───────────────────────────────────

    public static TheoryData<string> NoCallableIdentity() => new()
    {
        // map / filter / reduce, with values that would fail, log or draw if demanded
        "map([1, 2], 5)",
        "map([1, 2], 1 / 0)",
        "map([1, 2], trace(1) / 0)",
        "map([1, 2], tick())",
        "map([1, 2], 'f')",
        "map([1, 2], ())",
        "map([1, 2], [1])",
        "map(5, 5)",
        "Inc(x) = x + 1\nmap([1, 2], Inc(1))",
        "Inc(x) = x + 1\nmap([1, 2], 1.Inc)",
        "A = 1, 2\nmap([1, 2], A:0)",
        "filter([1], true)",
        "filter([1, 2], 1 / 0)",
        "reduce([1, 2], 5, 0)",
        "reduce([1, 2], trace(5), 0)",
        // the fused filter→count pipeline and the dot forms
        "count(filter([1, 2], trace(5)))",
        "count(filter(range(1, 3), 5))",
        "[1, 2].filter(5).count",
        "[1, 2].map(5)",
        "[1, 2].reduce(trace(5), 0)",
        // forwarding: one level, several levels, a collector, a qualified and an opened route, an alias
        "Through(xs, f) = map(xs, f)\nThrough([1], trace(1) / 0)",
        "Through(xs, f) = map(xs, f)\nOuter(xs, g) = Through(xs, g)\nOuter([1], 5)",
        "Through(xs, f) = map(xs, f)\nMiddle(xs, g) = Through(xs, g)\nOuter(xs, h) = Middle(xs, h)\nOuter([1], tick())",
        "F(*fs) = map([1], fs)\nInc(x) = x + 1\nF(Inc)",
        "Lib = { public Apply(xs, f) = map(xs, f) }\nLib.Apply([1], 5)",
        "open Lib\nLib = { public Apply(xs, f) = filter(xs, f) }\nApply([1], 5)",
        "M = map\nM([1, 2], 5)",
        "Each(xs, f) = xs.map(f)\nEach([1], 5)",
        // loop steps and a builtin used as a step
        "repeat(5, 1, 0)",
        "repeat(trace(1) / 0, 1, 0)",
        "while(true, 0)",
        "while(tick(), 0)",
        "5.repeat(1, 0)",
        "Run(f) = repeat(f, 1, 0)\nRun(trace(7))",
        "Run(f) = while(f, 0)\nTwice(g) = Run(g)\nTwice(1 / 0)",
        "repeat(map, 1, [1, 2], 5)",
        "repeat(filter, 1, [1, 2], trace(5))",
        // the user higher-order parameter
        "App(f, x) = f(x)\nApp(trace(5), 1)",
        "App(f, x) = f(x)\nApp(1 / 0, 1)",
    };

    [Theory]
    [MemberData(nameof(NoCallableIdentity))]
    public async Task NoCallableIdentity_InAnInvokingPosition_IsNotAnAlgorithm_WithNoValueDemand(string source)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("NotAnAlgorithm", CodeOf(observation));
        Assert.Empty(observation.HostCalls);
    }

    /// <summary>
    /// The structured result of the Q-06 rejection: the innermost variant is
    /// <see cref="EvalError.NotAnAlgorithm"/> whose description is the slot's ROLE, rendered as a
    /// sentence that names the slot (never a fake zero-parameter callable), positioned at the written
    /// callback/step argument, under the builtin's call frame (no per-item invocation frame).
    /// </summary>
    [Theory]
    [InlineData("map([1, 2], 5)", "map transform", "[1:13, 1:14)")]
    [InlineData("[1, 2].map(5)", "map transform", "[1:12, 1:13)")]
    [InlineData("filter([1], true)", "filter predicate", "[1:13, 1:17)")]
    [InlineData("reduce([1, 2], 5, 0)", "reduce reducer", "[1:16, 1:17)")]
    [InlineData("count(filter([1, 2], 5))", "filter predicate", "[1:22, 1:23)")]
    [InlineData("repeat(5, 1, 0)", "repeat step", "[1:8, 1:9)")]
    [InlineData("while(true, 0)", "while step", "[1:7, 1:11)")]
    [InlineData("repeat(map, 1, [1, 2], 5)", "map transform", "[1:24, 1:25)")]
    // a cell keeps the ORIGINAL written argument's span across transport (argument blame)
    [InlineData("Through(xs, f) = map(xs, f)\nThrough([1], 5)", "map transform", "[2:14, 2:15)")]
    public void TheRejection_NamesTheSlotRole_AtTheWrittenArgument(string source, string role, string span)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.NotAnAlgorithm, error.Code);
        var inner = Innermost(error.Source!);
        Assert.Equal(role, Assert.IsType<EvalError.NotAnAlgorithm>(inner).Description);
        Assert.Contains(
            $"The {role} is not callable: the argument supplied for it is a value, not an algorithm. Pass an algorithm: a named algorithm, a builtin, or a block {{ ... }}.",
            error.Message,
            StringComparison.Ordinal);
        Assert.DoesNotContain("Expected 0 parameters", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("for item", error.Message, StringComparison.Ordinal);
        Assert.Equal(span, error.Span?.ToString());
    }

    // ── a real zero-parameter callable is a callable: its interface mismatch is ArityMismatch ──

    public static TheoryData<string, string> ZeroParameterCallableVersusPlainValue() => new()
    {
        // property
        { "A = 7\nmap([1, 2], A)", "map([1, 2], 7)" },
        { "A = 7\nfilter([1], A)", "filter([1], 7)" },
        { "A = 7\nreduce([1], A, 0)", "reduce([1], 7, 0)" },
        { "A = tick()\nmap([1], A)", "map([1], tick())" },
        { "Bad = trace(1) / 0\nmap([1], Bad)", "map([1], trace(1) / 0)" },
        // block
        { "map([1, 2], { 5 })", "map([1, 2], 5)" },
        // member and opened member
        { "Lib = { public V = 5 }\nmap([1], Lib.V)", "map([1], 5)" },
        { "open Lib\nLib = { public V = 5 }\nfilter([1], V)", "filter([1], 5)" },
        // Math constant: a zero-parameter member, in both spellings
        { "map([1], Math.Pi)", "map([1], 3.14)" },
        { "map([1], pi)", "map([1], 3.14)" },
        // loop step
        { "Z = 5\nrepeat(Z, 1, 0)", "repeat(5, 1, 0)" },
        { "W = true\nwhile(W, 0)", "while(true, 0)" },
        // builtin callback whose own interface cannot bind one item
        { "map([1, 2], take)", "map([1, 2], 2)" },
        // user higher-order parameter
        { "A = 7\nApp(f, x) = f(x)\nApp(A, 1)", "App(f, x) = f(x)\nApp(7, 1)" },
    };

    [Theory]
    [MemberData(nameof(ZeroParameterCallableVersusPlainValue))]
    public async Task AZeroParameterCallable_IsArityMismatch_WhereThePlainValueIsNotAnAlgorithm(string callable, string value)
    {
        var callableObservation = await SixRouteAgreement.OnEveryRouteAsync(callable);
        Assert.Equal("ArityMismatch", CodeOf(callableObservation));
        Assert.Empty(callableObservation.HostCalls);
        var valueObservation = await SixRouteAgreement.OnEveryRouteAsync(value);
        Assert.Equal("NotAnAlgorithm", CodeOf(valueObservation));
        Assert.Empty(valueObservation.HostCalls);
    }

    public static TheoryData<string, string> SameCellEveryConsumer() => new()
    {
        { "App(f, x) = f(x)\nApp(5, 1)", "map([1], 5)" },
        { "App(f, x) = f(x)\nApp(5, 1)", "repeat(5, 1, 1)" },
        { "App(f, x) = f(x)\nApp(5, 1)", "while(5, 1)" },
        { "App(f, x) = f(x)\nApp(1 / 0, 1)", "filter([1], 1 / 0)" },
        { "App(f, x) = f(x)\nApp(1 / 0, 1)", "reduce([1], 1 / 0, 0)" },
        { "App(f, x) = f(x)\nA = 7\nApp(A, 1)", "A = 7\nmap([1], A)" },
        { "App(f, x) = f(x)\nA = 7\nApp(A, 1)", "A = 7\nrepeat(A, 1, 1)" },
    };

    [Theory]
    [MemberData(nameof(SameCellEveryConsumer))]
    public async Task UserParameterAndBuiltinSlot_ReportTheSameCapabilityVerdict(string user, string builtin)
        => Assert.Equal(CodeOf(await SixRouteAgreement.OnEveryRouteAsync(user)), CodeOf(await SixRouteAgreement.OnEveryRouteAsync(builtin)));

    // ── an invoking slot that is never invoked is neither projected nor demanded ─────────────

    public static TheoryData<string, string> NeverInvoked() => new()
    {
        { "map([], 5)", "ok L[]" },
        { "map((), 1 / 0)", "ok L[]" },
        { "map([], tick())", "ok L[]" },
        { "filter([], 5)", "ok L[]" },
        { "filter([], tick())", "ok L[]" },
        { "filter([], 1 / 0)", "ok L[]" },
        { "count(filter([], 5))", "ok 0" },
        { "[].filter(trace(5)).count", "ok 0" },
        { "reduce([], 5, 7)", "ok 7" },
        { "reduce([], trace(5), 7)", "ok 7" },
        { "reduce([], 1 / 0, 7)", "ok 7" },
        { "repeat(5, 0, 1)", "ok 1" },
        { "repeat(trace(5), 0, 1)", "ok 1" },
        { "repeat(1 / 0, 0, 1)", "ok 1" },
        { "[].map(5)", "ok L[]" },
        { "Through(xs, f) = map(xs, f)\nThrough([], 5)", "ok L[]" },
        { "Run(f) = repeat(f, 0, 1)\nRun(trace(3))", "ok 1" },
    };

    [Theory]
    [MemberData(nameof(NeverInvoked))]
    public async Task AnInvokingSlotThatIsNeverInvoked_IsNeitherProjectedNorDemanded(string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal(expected, CodeOf(observation));
        Assert.Empty(observation.HostCalls);
    }

    /// <summary>
    /// Neither a never-invoked slot nor a rejected one draws from the run's random stream: after the
    /// run, the stream's next raw draw is the seeded stream's FIRST draw.
    /// </summary>
    [Theory]
    [InlineData("map([], Math.Random(0, 1))", false)]
    [InlineData("reduce([], Math.Random(0, 1), 7)", false)]
    [InlineData("repeat(Math.RandomInt(1, 9), 0, 1)", false)]
    [InlineData("map([1], Math.Random(0, 1))", true)]
    [InlineData("repeat(Math.Random(0, 1), 1, 0)", true)]
    public void NoRandomDraw_ForAnUninvokedOrRejectedSlot(string source, bool rejected)
    {
        const long seed = 20261005;
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var (result, budget) = Evaluator.RunCountedObserved(program, randomSeed: seed);
        Assert.Equal(rejected, result.IsError);
        if (rejected)
            Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(result.Error));
        var (_, fresh) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid("0").Root), randomSeed: seed);
        Assert.Equal(fresh.RandomSource.NextUInt64(), budget.RandomSource.NextUInt64());
    }

    /// <summary>
    /// A slot whose VALUE would never terminate: rejected without demanding it when the slot is
    /// invoked, and never touched when it is not. The token only bounds a regression; neither run
    /// may observe it.
    /// </summary>
    [Theory]
    [InlineData("W(x) = x, true\nmap([1], while(W, 0))", true)]
    [InlineData("W(x) = x, true\nrepeat(while(W, 0), 1, 0)", true)]
    [InlineData("W(x) = x, true\nmap([], while(W, 0))", false)]
    [InlineData("W(x) = x, true\nreduce([], while(W, 0), 7)", false)]
    public void ANonTerminatingSlotValue_IsNeverDemanded(string source, bool rejected)
    {
        using var guard = new CancellationTokenSource(TimeSpan.FromSeconds(30));
        var result = KatLangEngine.Run(source, new RunOptions { EvaluationCancellationToken = guard.Token });
        Assert.False(guard.IsCancellationRequested);
        if (rejected)
            Assert.Equal(KatLangErrorCode.NotAnAlgorithm, Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors).Code);
        else
            Assert.IsType<RunResult.Success>(result);
    }

    // ── error precedence: the category changes only at the old rejection seam ────────────────

    public static TheoryData<string, string> Precedence() => new()
    {
        { "map([1], 5, 6)", "ArityMismatch" },          // builtin call arity before callback validity
        { "map(1 / 0, 5)", "DivisionByZero" },          // the collection VALUE before callback validity
        { "map(trace(1) / 0, 5)", "DivisionByZero" },
        { "reduce([1], 5, 1 / 0)", "DivisionByZero" },  // reduce's initial VALUE before reducer projection
        { "repeat(5, 'x', 0)", "TypeMismatch" },        // the repeat count's kind before step projection
        { "repeat(5, -1, 0)", "IllegalInEval" },        // the repeat count's domain before step projection
        { "repeat(5, 1.5, 0)", "IllegalInEval" },
        { "App(f, x) = f(x)\nApp(5)", "ArityMismatch" }, // user call arity before parameter callability
        { "map([], 5, 6)", "ArityMismatch" },
    };

    [Theory]
    [MemberData(nameof(Precedence))]
    public async Task ThePolicyReordersNoCheck(string source, string code)
        => Assert.Equal(code, CodeOf(await SixRouteAgreement.OnEveryRouteAsync(source)));

    // ── Q-27: a present VALUE of the wrong kind is TypeMismatch ──────────────────────────────

    public static TheoryData<string> PresentValueOfTheWrongKind() => new()
    {
        // unary minus
        "-()", "-(1, 2)", "-[1]", "-[]", "A = 1, 2\n-A", "-true", "-'a'",
        // Math numeric arguments
        "sqrt((4, 9))", "abs(())", "sqrt(true)", "Math.Abs([1])", "sqrt('x')", "Math.Pow(2, (1, 2))",
        // selector
        "A = 1, 2\nA:[0]", "A = 1, 2\nA:(0, 1)", "A = 1, 2\nA:()", "A = 1, 2\nA:'x'", "A = 1, 2\nA:true",
        // range bounds
        "range([1], 3)", "range(1, ())", "range('a', 2)", "range(1, true)",
        // repeat count
        "repeat({ x }, [1], 0)", "repeat({ x }, 'a', 0)", "repeat({ x }, true, 0)", "repeat({ x }, (1, 2), 0)",
        // take / skip count
        "take([1, 2], 'x')", "take([1, 2], [1])", "skip([1, 2], ())", "take([1, 2], true)", "skip([1, 2], (1, 2))",
        // collection elements
        "sum((1, true))", "avg((1, true))", "min((1, 'a'))", "max((1, ()))", "order((3, [1]))",
        "orderDesc(('a', 'b'))", "sum(true)", "sum([[1]])",
        // Boolean, sequence and list numeric misuse through the operators (unchanged)
        "true + 1", "(1, 2) + 1", "[1] * 2", "not ()", "() + 1",
        // a structural pattern of another kind (PAT-06, unchanged)
        "P((a, b)) = a\nP(5)",
    };

    [Theory]
    [MemberData(nameof(PresentValueOfTheWrongKind))]
    public async Task APresentValueOfTheWrongKind_IsTypeMismatch(string source)
        => Assert.Equal("TypeMismatch", CodeOf(await SixRouteAgreement.OnEveryRouteAsync(source)));

    [Theory]
    [InlineData("-()", "Type mismatch: operator `-` expects a numeric scalar operand, but the operand was a sequence value with 0 sequence elements: () @ [1:1, 1:4)")]
    [InlineData("-[1]", "Type mismatch: operator `-` expects a numeric scalar operand, but the operand was a list value with 1 element: [1] @ [1:1, 1:5)")]
    [InlineData("-'a'", "Type mismatch: operator `-` expects a numeric scalar operand, but the operand was a string: 'a' @ [1:1, 1:5)")]
    [InlineData("-true", "Type mismatch: operator `-` expects a numeric scalar operand, but the operand was a Boolean value: true @ [1:1, 1:6)")]
    public async Task UnaryMinus_ReportsOneKindErrorNamingTheOperand(string source, string expected)
        => Assert.Equal("TypeMismatch: " + expected, (await SixRouteAgreement.OnEveryRouteAsync(source)).Errors[0]);

    // ── Q-27: domains, bounds and empty collections ──────────────────────────────────────────

    public static TheoryData<string, string> OutsideTheDomain() => new()
    {
        // aggregates: a non-empty collection is their domain
        { "min(())", "IllegalInEval" }, { "max([])", "IllegalInEval" }, { "avg([])", "IllegalInEval" },
        { "avg(())", "IllegalInEval" }, { "min(filter([1], { x > 5 }))", "IllegalInEval" },
        // whole-number controls: a number, but not a whole one
        { "take([1, 2], 1.5)", "IllegalInEval" }, { "skip([1, 2], 2.5)", "IllegalInEval" },
        { "range(1.5, 3)", "IllegalInEval" }, { "repeat({ x }, -1, 0)", "IllegalInEval" },
        { "repeat({ x }, 0.5, 0)", "IllegalInEval" }, { "0 ^ -1", "IllegalInEval" },
        { "Math.RandomInt(1.5, 3)", "IllegalInEval" }, { "Math.Random(3, 1)", "IllegalInEval" },
        { "1 / 0", "DivisionByZero" }, { "5 mod 0", "DivisionByZero" },
        // selection naming no position
        { "():0", "BadIndex" }, { "[1]:1", "BadIndex" }, { "A = 1, 2\nA:(-1)", "BadIndex" }, { "A = 1, 2\nA:1.5", "BadIndex" },
        { "first(())", "BadIndex" }, { "first([])", "BadIndex" }, { "last(())", "BadIndex" }, { "last([])", "BadIndex" },
        { "().first", "BadIndex" }, { "[].last", "BadIndex" }, { "E = ()\nlast(E)", "BadIndex" },
        { "A = (), 1\nfirst(A:0)", "BadIndex" }, { "first(filter([1, 2], { x > 5 }))", "BadIndex" },
        { "[1].skip(1).first", "BadIndex" },
    };

    [Theory]
    [MemberData(nameof(OutsideTheDomain))]
    public async Task AValueOutsideTheOperationsDomain_ReportsTheDomainOrBoundsCode(string source, string code)
        => Assert.Equal(code, CodeOf(await SixRouteAgreement.OnEveryRouteAsync(source)));

    // ── SEQ-04 made total: first(A) ≡ A:0 and last(A) ≡ A:(count(A) - 1), errors included ──

    public static TheoryData<string> SelectionTargets() => new()
    {
        "()", "[]", "7", "'ab'", "true", "(1, 2)", "[1, 2]", "[(1, 2), 3]", "((), 1)", "(1, ())",
        "([], [1])", "[[]]", "(Pair*, 3)", "Pair", "Empty", "filter([1, 2, 3], { x > 1 })",
        "filter([1, 2], { x > 5 })", "range(1, 3)",
    };

    [Theory]
    [MemberData(nameof(SelectionTargets))]
    public void FirstAndLast_AreTheExplicitSelection_ValueCountAndErrorIncluded(string target)
    {
        const string prelude = "Pair = 1, 2\nEmpty = ()\n";
        AssertSameCountedOutcome(prelude + $"first({target})", prelude + $"({target}):0");
        AssertSameCountedOutcome(prelude + $"last({target})", prelude + $"({target}):(count(({target})) - 1)");
    }

    // ── genuine cardinality stays ArityMismatch (the cleanup does not over-reach) ────────────

    public static TheoryData<string> GenuineCardinality() => new()
    {
        "F(x) = x\nF(1, 2)", "Add(x, y) = x + y\nAdd((1, 2))", "count()", "count([1], [2])", "range(1)",
        "H(x, *rest) = x\nH()", "S(a, b) = a, b\nrepeat(S, 1, 1)", "P((a, b)) = a\nP((1, 2, 3))",
        "a, b = 1, 2, 3\na", "D(x) = x, x\nmap([1], D)", "R(x, acc) = ()\nreduce([1], R, 0)",
        "while(W, ())\nW(x) = x*", "Same(x, x) = x\nSame(4, 5)", "5.string(1)",
        "F(g) = g\nInc(x) = x + 1\nF(Inc)",
        // the clause-family supply cardinality witness the investigation's mutation sweep found missing
        "F(0) = 0\nF(n) = n\nF(1, 2)",
    };

    [Theory]
    [MemberData(nameof(GenuineCardinality))]
    public async Task GenuineCardinalityAndBinderAgreement_StayArityMismatch(string source)
        => Assert.Equal("ArityMismatch", CodeOf(await SixRouteAgreement.OnEveryRouteAsync(source)));

    /// <summary>
    /// The builtin arity payload reports the real fixed arity or loop minimum (formerly a placeholder
    /// 0 for every builtin but <c>if</c>); Lean <c>builtinArityError</c> reports the same.
    /// </summary>
    [Theory]
    [InlineData("range(1)", 2, 1)]
    [InlineData("atoms(1, 2)", 1, 2)]
    [InlineData("W(x) = x, false\nwhile(W)", 2, 1)]
    [InlineData("S(x) = x\nrepeat(S, 1)", 3, 2)]
    [InlineData("A = 1, 2\nA.if(2)", 3, 2)]
    [InlineData("count", 1, 0)]
    [InlineData("take", 2, 0)]
    public void BuiltinArityPayload_IsTheRealMinimum(string source, int expected, int actual)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var mismatch = Assert.IsType<EvalError.ArityMismatch>(Innermost(Assert.Single(failure.Errors).Source!));
        Assert.Equal((expected, actual), (mismatch.Expected, mismatch.Actual));
    }

    // ── NEED-04 (frozen): the repeated-name verdicts keep their categories ───────────────────

    [Theory]
    [InlineData("Same(x, x) = x\nSame(4, 5)", "ArityMismatch")]
    [InlineData("A = 5\nB = 5\nP(f, f) = f\nP(A, B)", "TypeMismatch")]
    public async Task RepeatedNameVerdicts_KeepTheirNeed04Categories(string source, string code)
        => Assert.Equal(code, CodeOf(await SixRouteAgreement.OnEveryRouteAsync(source)));

    /// <summary>The cardinality verdicts name the contract they enforce (wording only: the
    /// innermost variant stays <c>BadArity</c>, NEED-04 and the loop-output rule unchanged).</summary>
    [Theory]
    [InlineData("Same(x, x) = x\nSame(4, 5)", "repeated parameter 'x' requires equal arguments: Bad arity")]
    [InlineData("while(W, ())\nW(x) = x*", "a while step must output at least its continuation flag: Bad arity")]
    public void CardinalityVerdicts_NameTheirContract(string source, string message)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        Assert.IsType<EvalError.BadArity>(Innermost(error.Source!));
        Assert.EndsWith(message, error.Message, StringComparison.Ordinal);
    }

    // ── the public projection ────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("map([1], 5)", KatLangErrorCode.NotAnAlgorithm, typeof(EvalError.NotAnAlgorithm))]
    [InlineData("repeat(5, 1, 0)", KatLangErrorCode.NotAnAlgorithm, typeof(EvalError.NotAnAlgorithm))]
    [InlineData("A = 7\nmap([1], A)", KatLangErrorCode.ArityMismatch, typeof(EvalError.ArityMismatch))]
    [InlineData("-()", KatLangErrorCode.TypeMismatch, typeof(EvalError.TypeMismatch))]
    [InlineData("sum((1, true))", KatLangErrorCode.TypeMismatch, typeof(EvalError.TypeMismatch))]
    [InlineData("take([1], 'x')", KatLangErrorCode.TypeMismatch, typeof(EvalError.TypeMismatch))]
    [InlineData("take([1], 1.5)", KatLangErrorCode.IllegalInEval, typeof(EvalError.IllegalInEval))]
    [InlineData("first(())", KatLangErrorCode.BadIndex, typeof(EvalError.BadIndex))]
    [InlineData("min(())", KatLangErrorCode.IllegalInEval, typeof(EvalError.IllegalInEval))]
    [InlineData("F(x) = x\nF(1, 2)", KatLangErrorCode.ArityMismatch, typeof(EvalError.ArityMismatch))]
    [InlineData("F(0) = 0\nF(n) = n\nF(1, 2)", KatLangErrorCode.ArityMismatch, typeof(EvalError.ArityMismatch))]
    public void PublicCodeAndStructuredSource_AgreeWithTheInnermostVariant(string source, KatLangErrorCode code, Type variant)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(code, error.Code);
        var inner = Innermost(error.Source!);
        Assert.IsType(variant, inner);
        Assert.Equal(code, inner.Code);
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    /// <summary>The generic and the optimized evaluator give both programs the same counted outcome:
    /// the same value and emitted count, or the same innermost error category.</summary>
    private static void AssertSameCountedOutcome(string left, string right)
    {
        foreach (var optimized in new[] { false, true })
        {
            var a = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(left).Root), enableOptimizations: optimized).Result;
            var b = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(right).Root), enableOptimizations: optimized).Result;
            Assert.Equal(b.IsError, a.IsError);
            if (a.IsError)
            {
                Assert.Equal(Innermost(b.Error).GetType(), Innermost(a.Error).GetType());
                Assert.Equal(b.Error.Code, a.Error.Code);
            }
            else
            {
                Assert.True(Result.ValueComparer.Equals(b.Value.Value, a.Value.Value), $"{left} vs {right}");
                Assert.Equal(b.Value.EmittedCount, a.Value.EmittedCount);
            }
        }
    }
}
