using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// Q-23 (owner decision, October 2026): A LOOP STEP IS AN ORDINARY CALLABLE INVOKED OVER THE CURRENT
/// STATE SUPPLY (LOOP-08). Any callable is eligible as a <c>while</c>/<c>repeat</c> step; an iteration
/// supplies the current state cells to it through its OWN ordinary invocation — a user algorithm through
/// its binder, a clause family through the ordinary family dispatcher, a builtin through its ordinary
/// argument roles, an alias as its target — and the loop specializes only the RECEIVER: the invocation's
/// row supply is the next state (Q-24), a builtin's one result value being one non-spread row. Eligibility
/// never depends on the callable's category, representation, clause count, spelling or planner support;
/// a value with no callable identity is still no step (NEED-06); a zero-iteration <c>repeat</c> never
/// projects its step (LOOP-05). Every case runs on the six established routes (sync and async engines,
/// the engine's suspending twin, the generic and optimized evaluators, the forced twin) and requires the
/// same value, errors and host-call log on all of them and identical budget counters on the three
/// evaluator routes (Q-09). Lean: <c>CoreTests/LoopSteps.lean</c>, laws <c>loop_step_builtin_*</c>.
/// </summary>
public partial class LoopStepCallableDispatchTests
{
    private const string Step = "Step(0) = 0\nStep(n) = n - 1\n";
    private const string Countdown = "Countdown(0) = 0, false\nCountdown(n) = n - 1, true\n";
    private const string Gcd = "Gcd(a, 0) = a, 0, false\nGcd(a, b) = b, a mod b, true\n";
    private const string Partial = "F(0) = 1\nF(1) = 2\n";
    private const string Lib = "Lib = {\n  public Step(0) = 0\n  public Step(n) = n - 1\n  public C = count\n}\n";
    private const string Forward = "Run(f, *s) = repeat(f, 2, s*)\nRun1(f, *s) = repeat(f, 1, s*)\nRun2(g, *s) = Run(g, s*)\n";
    private const string NoStepParameter = "but the loop found no step parameter to bind";

    // ── 1. The callable-category matrix: no privileged category ────────────────────────────────

    /// <summary>category, source, expected outcome: <c>ok VALUE</c> (accepted), <c>err CODE</c> (an
    /// eligible step whose ordinary invocation fails), or <c>unbound</c> (the loop-state binding failure a
    /// value with no callable identity and a genuinely zero-parameter callable both report).</summary>
    public static TheoryData<string, string, string> CallableCategories() => new()
    {
        { "user algorithm", "S(n) = n - 1\nrepeat(S, 2, 3)", "ok 1" },
        { "inferred user algorithm", "S = n - 1\nrepeat(S, 2, 3)", "ok 1" },
        { "block", "repeat({ x - 1 }, 2, 3)", "ok 1" },
        { "single-clause structural user definition", "Sw((a, b)) = (b, a)\nrepeat(Sw, 1, (1, 2))", "ok S[2, 1]" },
        { "clause family", Step + "repeat(Step, 2, 3)", "ok 1" },
        { "clause family, while", Countdown + "while(Countdown, 3)", "ok 0" },
        { "builtin", "repeat(count, 1, [1, 2])", "ok 2" },
        { "lazy builtin", "repeat(if, 1, true, 1, 2)", "ok 1" },
        { "Math function", "repeat(abs, 2, -3)", "ok 3" },
        { "Math function, canonical", "repeat(Math.Pow, 1, 2, 3)", "ok 8" },
        { "host operation", "repeat(trace, 2, 5)", "ok 5" },
        { "alias of a user algorithm", "S(n) = n - 1\nA = S\nB = A\nrepeat(B, 2, 3)", "ok 1" },
        { "alias of a clause family", Step + "A = Step\nB = A\nrepeat(B, 2, 3)", "ok 1" },
        { "alias of a builtin", "A = count\nB = A\nrepeat(B, 1, [1, 2])", "ok 2" },
        { "alias of a Math function", "A = abs\nB = A\nrepeat(B, 2, -3)", "ok 3" },
        { "alias of a host operation", "A = trace\nB = A\nrepeat(B, 2, 5)", "ok 5" },
        { "inline-block alias of a family", Step + "repeat({ Step }, 2, 3)", "ok 1" },
        { "inline-block alias of a builtin", "repeat({ count }, 1, [1, 2])", "ok 2" },
        { "forwarded user algorithm", Forward + "S(n) = n - 1\nRun(S, 3)", "ok 1" },
        { "forwarded clause family", Forward + Step + "Run(Step, 3)", "ok 1" },
        { "forwarded builtin", Forward + "Run1(count, [1, 2])", "ok 2" },
        { "forwarded Math function", Forward + "Run(abs, -3)", "ok 3" },
        { "forwarded host operation", Forward + "Run(trace, 5)", "ok 5" },
        { "forwarded alias of a family", Forward + Step + "A = Step\nRun(A, 3)", "ok 1" },
        { "family forwarded through two levels", Forward + Step + "Run2(Step, 3)", "ok 1" },
        { "qualified family member", Lib + "repeat(Lib.Step, 2, 3)", "ok 1" },
        { "fluent family member", Lib + "Lib.Step.repeat(2, 3)", "ok 1" },
        { "opened family member", "open Lib\n" + Lib + "repeat(Step, 2, 3)", "ok 1" },
        { "alias member of a builtin", Lib + "repeat(Lib.C, 1, [1, 2])", "ok 2" },
        { "forwarded family member", Forward + Lib + "Run(Lib.Step, 3)", "ok 1" },
        { "dot spelling of a family", Step + "Step.repeat(2, 3)", "ok 1" },
        { "dot spelling of a builtin", "count.repeat(1, [1, 2])", "ok 2" },
        { "dot spelling of a Math function", "abs.repeat(2, -3)", "ok 3" },
        { "clause family, wrong state arity", Step + "repeat(Step, 1, 1, 2)", "err ArityMismatch" },
        { "clause family, no matching clause", Partial + "repeat(F, 1, 5)", "err NoMatchingBranch" },
        { "builtin, wrong state arity", "repeat(take, 1, [1, 2])", "err ArityMismatch" },
        { "builtin, wrong argument kind", "repeat(if, 1, 5, 1, 2)", "err TypeMismatch" },
        { "Math function, wrong state arity", "repeat(Math.Pow, 1, 2)", "err ArityMismatch" },
        { "number", "repeat(5, 1, 0)", "unbound" },
        { "list", "repeat([1], 1, 0)", "unbound" },
        { "empty sequence", "repeat((), 1, 0)", "unbound" },
        { "call result", "Inc(x) = x + 1\nrepeat(Inc(1), 1, 0)", "unbound" },
        { "selection", "A = 1, 2\nrepeat(A:0, 1, 0)", "unbound" },
        { "zero-parameter property", "Z = 5\nrepeat(Z, 1, 0)", "unbound" },
        { "zero-parameter host operation", "repeat(tick, 1, 0)", "unbound" },
        { "zero-parameter Math member", "repeat(pi, 1, 0)", "unbound" },
    };

    [Theory]
    [MemberData(nameof(CallableCategories))]
    public async Task CallableCategory_IsEligibleByItsOrdinaryInvocation(string category, string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        if (expected.StartsWith("ok ", StringComparison.Ordinal))
        {
            Assert.True(observation.Kind == "ok", $"{category}: {observation}");
            Assert.Equal(expected[3..], observation.Value);
            return;
        }

        Assert.True(observation.Kind == "err", $"{category}: {observation}");
        var error = Assert.Single(observation.Errors);
        if (expected == "unbound")
        {
            // No callable identity (NEED-06), or a callable whose real arity is zero: the loop-state
            // binding failure (X-23's truthful wording), never a category rule.
            Assert.StartsWith("ArityMismatch: ", error, StringComparison.Ordinal);
            Assert.Contains(NoStepParameter, error, StringComparison.Ordinal);
            return;
        }

        // An eligible step whose ordinary invocation fails: the callable's own failure, never the
        // unbound-step rejection a family or builtin used to get.
        Assert.StartsWith(expected[4..] + ": ", error, StringComparison.Ordinal);
        Assert.DoesNotContain(NoStepParameter, error, StringComparison.Ordinal);
    }

    // ── 2. Clause families (canonical regressions) ─────────────────────────────────────────────

    [Fact]
    public async Task Family_CanonicalWitness_IteratesLikeNestedCalls()
    {
        var (observation, _) = await AllRoutesAsync(Step + "repeat(Step, 2, 3), Step.repeat(5, 3), Step(Step(3))");
        Assert.Equal(("ok", "S[1, 0, 1]"), (observation.Kind, observation.Value));
    }

    [Fact]
    public async Task Family_While_ReadsTheSelectedClausesLastRowAsTheFlag()
    {
        var (observation, _) = await AllRoutesAsync(Countdown + "Countdown.while(3), while(Countdown, 0), Countdown(3)");
        Assert.Equal(("ok", "S[0, 0, S[2, true]]"), (observation.Kind, observation.Value));
    }

    [Fact]
    public async Task Family_MultiSlotWhile_MatchesLiteralsAndSuppliesTheSelectedRows()
    {
        var (observation, _) = await AllRoutesAsync(Gcd + "while(Gcd, 48, 18), Gcd.while(48, 18):0, while(Gcd, 7, 0)");
        Assert.Equal(("ok", "S[S[6, 0], 6, S[7, 0]]"), (observation.Kind, observation.Value));
    }

    [Fact]
    public async Task Family_ClauseOrder_IsTheFamilysOwn()
    {
        // The first matching clause wins in the loop exactly as in the call: no specificity sorting.
        var (observation, _) = await AllRoutesAsync("F(x) = 1\nF(0) = 2\nrepeat(F, 1, 0), F(0)");
        Assert.Equal(("ok", "S[1, 1]"), (observation.Kind, observation.Value));
    }

    [Theory]
    [InlineData("Sw((a, b)) = (b, a)\nSw([a, b]) = [b, a]\nrepeat(Sw, 1, (1, 2)), repeat(Sw, 1, [1, 2])", "S[S[2, 1], L[2, 1]]")]
    [InlineData("P((0, b)) = (b, 1)\nP((a, b)) = (b, a + b)\nrepeat(P, 3, (0, 1)), P(P(P((0, 1))))", "S[S[2, 3], S[2, 3]]")]
    [InlineData("N(((a, b), c)) = ((c, b), a)\nN(x) = x\nrepeat(N, 2, ((1, 2), 3)), N(N(((1, 2), 3)))", "S[S[S[1, 2], 3], S[S[1, 2], 3]]")]
    [InlineData("R((x, x)) = 0\nR((x, y)) = 1\nrepeat(R, 1, (1, 1)), repeat(R, 1, (1, 2))", "S[0, 1]")]
    [InlineData("H(0) = 1\nH([x]) = x\nrepeat(H, 1, 0), repeat(H, 1, [5])", "S[1, 5]")]
    public async Task Family_StructuralClauses_BindThroughTheOrdinaryDispatcher(string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.Equal(("ok", expected), (observation.Kind, observation.Value));
    }

    [Fact]
    public async Task Family_RepeatedNames_BindTheIncomingStateOnly()
    {
        // E(0, 2) -> (1, 2) -> (2, 2) -> E(2, 2) = (0, 0): equality decides the clause.
        var (converge, _) = await AllRoutesAsync("E(x, x) = 0, 0\nE(a, b) = a + 1, b\nrepeat(E, 3, 0, 2)");
        Assert.Equal(("ok", "S[0, 0]"), (converge.Kind, converge.Value));

        // A repeated-name clause's spread row supplies its items: no pattern category repacks the
        // outgoing state (Q-24), so the second iteration re-binds two slots.
        var (spread, _) = await AllRoutesAsync("D(x, x) = { (x, x)* }\nD(a, b) = { (a, b)* }\nrepeat(D, 2, 1, 1)");
        Assert.Equal(("ok", "S[1, 1]"), (spread.Kind, spread.Value));
    }

    [Fact]
    public async Task Family_SelectedClauseRows_AreTheNextState_NotTheCallsOneValue()
    {
        // Two rows are two slots: a second iteration of the one-parameter family is its ordinary arity
        // failure. Reading the clause as the call's one value would re-bind the pair instead.
        var (twice, _) = await AllRoutesAsync("Two(0) = 9, 9\nTwo(n) = n, n\nrepeat(Two, 2, 1)");
        Assert.Equal("err", twice.Kind);
        Assert.StartsWith("ArityMismatch: while evaluating call to repeat: Property 'Two' expects 1 parameter, but was called with 2 arguments.",
            Assert.Single(twice.Errors), StringComparison.Ordinal);

        var (shapes, _) = await AllRoutesAsync(
            "One(0) = (9, 9)\nOne(n) = (n, n)\nSpread(0) = { (9, 9)* }\nSpread(n) = { (n, n)* }\nNone(0) = { ()* }\nNone(n) = { ()* }\nEmpty(0) = ()\nEmpty(n) = ()\n"
            + "repeat(One, 2, 1), repeat(Spread, 1, 1), repeat(None, 1, 1), repeat(Empty, 2, 1)");
        Assert.Equal(("ok", "S[S[S[1, 1], S[1, 1]], S[1, 1], S[], S[]]"), (shapes.Kind, shapes.Value));
    }

    [Fact]
    public async Task Family_NoMatch_IsTheOrdinaryNoMatchingBranch_NeverTermination()
    {
        var (first, _) = await AllRoutesAsync(Partial + "repeat(F, 1, 5)");
        Assert.Equal(
            ["NoMatchingBranch: while evaluating call to repeat: while evaluating call to F: No matching branch for 'F' @ [3:1, 3:16)"],
            first.Errors);

        // A non-match on a LATER iteration is the same failure; only a `false` flag ends a `while`.
        var (later, _) = await AllRoutesAsync("S(2) = 1, true\nS(1) = 0, true\nwhile(S, 2)");
        Assert.Equal("err", later.Kind);
        Assert.StartsWith("NoMatchingBranch: ", Assert.Single(later.Errors), StringComparison.Ordinal);
        var (stops, _) = await AllRoutesAsync("S(2) = 1, true\nS(1) = 0, false\nwhile(S, 2)");
        Assert.Equal(("ok", "1"), (stops.Kind, stops.Value));
    }

    [Fact]
    public async Task Family_NoMatch_ThroughForwarding_NamesTheArgumentWrittenForItsCell()
    {
        // The step's own frame names the expression its SUPPLY CELL retains (Lean `loopStepName`): a cell
        // transported through the parameter `f` is still the one written `F` at the outer call, so the
        // forwarded step reports exactly as the direct `repeat(F, 1, 5)` does.
        var (forwarded, _) = await AllRoutesAsync(Partial + Forward + "Run1(F, 5)");
        Assert.Equal("err", forwarded.Kind);
        Assert.Contains("while evaluating call to repeat: while evaluating call to F: No matching branch for 'F'",
            Assert.Single(forwarded.Errors), StringComparison.Ordinal);
        var error = GenericError(Partial + Forward + "Run1(F, 5)");
        Assert.Equal("F", Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error)).AlgorithmName);
    }

    [Fact]
    public async Task Family_WrongStateArity_IsTheFamilysOrdinaryArityFailure()
    {
        var (loop, _) = await AllRoutesAsync(Step + "repeat(Step, 1, 1, 2)");
        var (call, _) = await AllRoutesAsync(Step + "Step(1, 2)");
        Assert.Equal(
            ["ArityMismatch: while evaluating call to repeat: Property 'Step' expects 1 parameter, but was called with 2 arguments. @ [3:1, 3:22)"],
            loop.Errors);
        Assert.Equal(["ArityMismatch: Property 'Step' expects 1 parameter, but was called with 2 arguments. @ [3:1, 3:11)"], call.Errors);
        Assert.Equal(call.Causes, loop.Causes);

        // The structured error is the ordinary invocation's under the loop's frame: the inner frame
        // names the family, never the loop builtin.
        var error = GenericError(Step + "repeat(Step, 1, 1, 2)");
        Assert.Equal(["while evaluating call to repeat", "while evaluating call to Step"], Frames(error));
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal((1, 2), (arity.Expected, arity.Actual));
    }

    [Theory]
    [InlineData("F(0) = 1 / 0\nF(n) = n\n", "repeat(F, 1, 0)", "F(0)", "DivisionByZero")]
    [InlineData("F(0) = 0\nF(n) = n + 'x'\n", "repeat(F, 1, 2)", "F(2)", "TypeMismatch")]
    public async Task Family_SelectedBodyFailure_IsTheOrdinaryFailure(string definitions, string loop, string call, string code)
    {
        var (looped, _) = await AllRoutesAsync(definitions + loop);
        var (called, _) = await AllRoutesAsync(definitions + call);
        Assert.Equal("err", looped.Kind);
        Assert.StartsWith(code + ": while evaluating call to repeat: while evaluating call to F: ", Assert.Single(looped.Errors), StringComparison.Ordinal);
        Assert.Equal(called.Causes, looped.Causes);
    }

    // ── 3. Builtins (canonical regressions) ────────────────────────────────────────────────────

    [Fact]
    public async Task Builtin_IsItsOneRowWrapper()
    {
        var (observation, _) = await AllRoutesAsync(
            "C(c) = count(c)\nrepeat(count, 1, [1, 2]) == repeat(C, 1, [1, 2]), count.repeat(1, [1, 2]), repeat(count, 2, [1, 2]), count(count([1, 2]))");
        Assert.Equal(("ok", "S[true, 2, 1, 1]"), (observation.Kind, observation.Value));
    }

    [Theory]
    [InlineData("repeat(take, 1, [1, 2, 3], 2)", "L[1, 2]")]
    [InlineData("repeat(skip, 1, [1, 2, 3], 1)", "L[2, 3]")]
    [InlineData("repeat(order, 1, [3, 1, 2])", "L[1, 2, 3]")]
    [InlineData("repeat(orderDesc, 2, [1, 3, 2])", "L[3, 2, 1]")]
    [InlineData("repeat(distinct, 1, [1, 1, 2])", "L[1, 2]")]
    [InlineData("repeat(atoms, 1, (1, (2, 3)))", "L[1, 2, 3]")]
    [InlineData("repeat(range, 1, 1, 3)", "L[1, 2, 3]")]
    [InlineData("repeat(take, 1, [1, 2], 0)", "L[]")]
    public async Task Builtin_CollectionResult_IsOneStateSlot(string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.Equal(("ok", expected), (observation.Kind, observation.Value));
    }

    [Fact]
    public async Task Builtin_CollectionResult_NeverBecomesTheNextStateArity()
    {
        // take([1, 2, 3], 2) is ONE slot holding [1, 2]: the next `take` call has one argument.
        var (observation, _) = await AllRoutesAsync("repeat(take, 2, [1, 2, 3], 2)");
        Assert.Equal(
            ["ArityMismatch: while evaluating call to repeat: Callable `take(collection, count)` expects 2 arguments, but was called with 1 argument. @ [1:1, 1:30)"],
            observation.Errors);
    }

    [Theory]
    [InlineData("repeat(first, 1, [()])", "Fi(c) = first(c)\nrepeat(Fi, 1, [()])")]
    [InlineData("repeat(if, 1, true, (), 1)", "I(c, t, e) = if(c, t, e)\nrepeat(I, 1, true, (), 1)")]
    [InlineData("while(first, [()])", "Fi(c) = first(c)\nwhile(Fi, [()])")]
    public async Task Builtin_EmptyResult_IsOneEmptySlot_LikeItsWrapper(string direct, string wrapper)
    {
        var (builtin, _) = await AllRoutesAsync(direct);
        var (wrapped, _) = await AllRoutesAsync(wrapper);
        Assert.Equal(wrapped.Semantic, builtin.Semantic);
        if (direct.StartsWith("while", StringComparison.Ordinal))
        {
            // One `()` slot is the flag and must be a Boolean; zero slots would be "Bad arity" instead.
            Assert.Contains("while continuation flag (the step's last output) must be a Boolean value (true or false), but was a sequence value with 0 sequence elements: ()",
                Assert.Single(builtin.Errors), StringComparison.Ordinal);
        }
        else
        {
            Assert.Equal(("ok", "S[]"), (builtin.Kind, builtin.Value));
        }
    }

    [Fact]
    public async Task Builtin_If_KeepsItsLazyRoles()
    {
        var (unselected, _) = await AllRoutesAsync("repeat(if, 1, false, 1 / 0, 2)");
        Assert.Equal(("ok", "2"), (unselected.Kind, unselected.Value));

        var (loop, _) = await AllRoutesAsync("repeat(if, 1, trace(false), trace(1) / 0, trace(2))");
        var (call, _) = await AllRoutesAsync("if(trace(false), trace(1) / 0, trace(2))");
        Assert.Equal(call.Semantic, loop.Semantic);
        Assert.Equal(["trace(false)", "trace(2)"], loop.HostCalls);
    }

    [Theory]
    [InlineData("Go(f) = repeat(map, 1, [1, 2], f)\nInc(x) = trace(x) + 1\nGo(Inc)", "Go(f) = map([1, 2], f)\nInc(x) = trace(x) + 1\nGo(Inc)")]
    [InlineData("repeat(map, 1, [1, 2], { trace(x) + 1 })", "map([1, 2], { trace(x) + 1 })")]
    [InlineData("repeat(filter, 1, [1, 2, 3], { trace(x) mod 2 == 1 })", "filter([1, 2, 3], { trace(x) mod 2 == 1 })")]
    [InlineData("repeat(reduce, 1, [1, 2, 3], { trace(e) + a }, 0)", "reduce([1, 2, 3], { trace(e) + a }, 0)")]
    [InlineData("Go(f) = repeat(reduce, 1, [1, 2, 3], f, 0)\nAdd(e, a) = e + trace(a)\nGo(Add)", "Go(f) = reduce([1, 2, 3], f, 0)\nAdd(e, a) = e + trace(a)\nGo(Add)")]
    public async Task Builtin_CallbackTaking_InvokesTheCallableStateSlotLikeTheCall(string loop, string call)
    {
        var (looped, _) = await AllRoutesAsync(loop);
        var (called, _) = await AllRoutesAsync(call);
        Assert.Equal("ok", looped.Kind);
        Assert.Equal(called.Semantic, looped.Semantic);
    }

    [Fact]
    public async Task CallableCapability_ReachesOnlyTheFirstIteration_ThroughLegalTransport()
    {
        // A callable carried by a parameter cell into the initial state is invocable by the first
        // iteration (the state is a Model-C supply); a later state is the step's rows, and results
        // never export callable identity.
        var (first, _) = await AllRoutesAsync("Run(f) = repeat(S, 1, f, 0)\nS(g, y) = g(y), y\nInc(x) = x + 1\nRun(Inc), S(Inc, 0)");
        Assert.Equal(("ok", "S[S[1, 0], S[1, 0]]"), (first.Kind, first.Value));

        var (second, _) = await AllRoutesAsync("Run(f) = repeat(S, 2, f, 0)\nS(g, y) = g(y), y\nInc(x) = x + 1\nRun(Inc)");
        Assert.Equal("err", second.Kind);
        Assert.StartsWith("NotAnAlgorithm: ", Assert.Single(second.Errors), StringComparison.Ordinal);

        var (builtin, _) = await AllRoutesAsync("Go(f) = repeat(map, 2, [1, 2], f)\nInc(x) = x + 1\nGo(Inc)");
        Assert.Equal("err", builtin.Kind);
        Assert.Contains("Callable `map(collection, mapper)` expects 2 arguments, but was called with 1 argument.",
            Assert.Single(builtin.Errors), StringComparison.Ordinal);
    }

    [Fact]
    public async Task LoopBuiltins_AsSteps_NeedNoExclusion()
    {
        var (nested, _) = await AllRoutesAsync("repeat(repeat, 1, { x + 1 }, 2, 0), repeat(while, 1, { x + 1, x < 3 }, 0)");
        Assert.Equal(("ok", "S[2, 3]"), (nested.Kind, nested.Value));

        // The second iteration's state is the inner loop's one result: `repeat`'s own arity failure.
        var (second, _) = await AllRoutesAsync("repeat(repeat, 2, { x + 1 }, 2, 0)");
        Assert.Contains("Callable `repeat(step, count, initialState)` expects at least 3 arguments, but was called with 1 argument.",
            Assert.Single(second.Errors), StringComparison.Ordinal);

        // `while` over `repeat`: the one result slot is the flag.
        var (flag, _) = await AllRoutesAsync("while(repeat, { x + 1 }, 1, 0)");
        Assert.StartsWith("TypeMismatch: ", Assert.Single(flag.Errors), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("repeat(take, 1, [1, 2], 1.5)", "take([1, 2], 1.5)")]
    [InlineData("repeat(sum, 1, ['a'])", "sum(['a'])")]
    [InlineData("repeat(if, 1, 5, 1, 2)", "if(5, 1, 2)")]
    [InlineData("repeat(map, 1, [1, 2], 5)", "map([1, 2], 5)")]
    [InlineData("repeat(count, 1, [1], [2])", "count([1], [2])")]
    public async Task Builtin_Failures_AreTheOrdinaryInvocationFailures(string loop, string call)
    {
        var (looped, _) = await AllRoutesAsync(loop);
        var (called, _) = await AllRoutesAsync(call);
        Assert.Equal("err", looped.Kind);
        Assert.Equal(called.Causes, looped.Causes);
        Assert.DoesNotContain(NoStepParameter, Assert.Single(looped.Errors), StringComparison.Ordinal);

        // The loop adds its own frame around the builtin's ordinary frames; the inner chain is the call's.
        var loopFrames = Frames(GenericError(loop));
        var callFrames = Frames(GenericError(call));
        Assert.Equal("while evaluating call to repeat", loopFrames[0]);
        Assert.Equal(callFrames, loopFrames.Skip(1).ToArray());
    }

    [Theory]
    [InlineData("while(contains, [1, 2], 3)", "ok", "S[L[1, 2], 3]")]
    [InlineData("while(contains, [1, 2], 1)", "err", "Callable `contains(collection, item)` expects 2 arguments, but was called with 1 argument.")]
    [InlineData("while(count, [1, 2])", "err", "while continuation flag (the step's last output) must be a Boolean value (true or false), but was numeric value 2")]
    [InlineData("while(first, [false])", "ok", "L[false]")]
    public async Task Builtin_WhileStep_ItsOneResultRowIsAlsoTheFlag(string source, string kind, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.Equal(kind, observation.Kind);
        if (kind == "ok")
            Assert.Equal(expected, observation.Value);
        else
            Assert.Contains(expected, Assert.Single(observation.Errors), StringComparison.Ordinal);
    }

    // ── 4. η-expansion, alias and forwarding transparency ───────────────────────────────────────

    /// <summary>A direct step and its MATCHING user wrapper (LOOP-03: a one-row wrapper for a single-row
    /// callee, a spread wrapper for a multi-row one) are the same step: eligibility, value, next-state
    /// cardinality (exercised by the later iterations), error cause, effects and demand.</summary>
    public static TheoryData<string, string> DirectAndWrapper() => new()
    {
        { Step + "repeat(Step, 3, trace(3))", Step + "W(n) = Step(n)\nrepeat(W, 3, trace(3))" },
        { Step + "repeat(Step, 2, 1, 2)", Step + "W(a, b) = Step(a, b)\nrepeat(W, 2, 1, 2)" },
        { Countdown + "while(Countdown, trace(3))", Countdown + "W(n) = { Countdown(n)* }\nwhile(W, trace(3))" },
        { Gcd + "while(Gcd, trace(48), trace(18))", Gcd + "W(a, b) = { Gcd(a, b)* }\nwhile(W, trace(48), trace(18))" },
        { Partial + "repeat(F, 2, trace(0))", Partial + "W(n) = F(n)\nrepeat(W, 2, trace(0))" },
        { "Two(0) = 9, 9\nTwo(n) = n, n\nrepeat(Two, 2, 1)", "Two(0) = 9, 9\nTwo(n) = n, n\nW(n) = { Two(n)* }\nrepeat(W, 2, 1)" },
        { "repeat(count, 2, trace([1, 2]))", "W(c) = count(c)\nrepeat(W, 2, trace([1, 2]))" },
        { "repeat(take, 2, trace([1, 2, 3]), trace(2))", "W(c, n) = take(c, n)\nrepeat(W, 2, trace([1, 2, 3]), trace(2))" },
        { "repeat(if, 1, trace(true), trace(()), trace(1))", "W(c, t, e) = if(c, t, e)\nrepeat(W, 1, trace(true), trace(()), trace(1))" },
        { "while(contains, trace([1, 2]), trace(3))", "W(c, x) = contains(c, x)\nwhile(W, trace([1, 2]), trace(3))" },
        { "while(first, [()])", "W(c) = first(c)\nwhile(W, [()])" },
        { "repeat(range, 1, 1, trace(3))", "W(a, b) = range(a, b)\nrepeat(W, 1, 1, trace(3))" },
    };

    [Theory]
    [MemberData(nameof(DirectAndWrapper))]
    public async Task DirectStep_EqualsItsMatchingUserWrapper(string direct, string wrapper)
    {
        var (step, _) = await AllRoutesAsync(direct);
        var (wrapped, _) = await AllRoutesAsync(wrapper);
        Assert.Equal(wrapped.Semantic, step.Semantic);
    }

    [Theory]
    [InlineData(Step, "Step", "3")]
    [InlineData("", "count", "[1, 2]")]
    [InlineData("S(n) = n - 1\n", "S", "3")]
    [InlineData("", "abs", "-3")]
    [InlineData("", "trace", "5")]
    public async Task Aliases_AreTheirTargets(string definitions, string target, string state)
    {
        var (direct, _) = await AllRoutesAsync($"{definitions}repeat({target}, 1, {state}), repeat({target}, 0, {state})");
        var (alias, _) = await AllRoutesAsync($"{definitions}A = {target}\nrepeat(A, 1, {state}), repeat(A, 0, {state})");
        var (chain, _) = await AllRoutesAsync($"{definitions}A = {target}\nB = A\nrepeat(B, 1, {state}), repeat(B, 0, {state})");
        Assert.Equal("ok", direct.Kind);
        Assert.Equal(direct.Semantic, alias.Semantic);
        Assert.Equal(direct.Semantic, chain.Semantic);
    }

    [Theory]
    [InlineData(Step, "Step", "3")]
    [InlineData("", "count", "[1, 2]")]
    [InlineData("S(n) = n - 1\n", "S", "3")]
    [InlineData("", "abs", "-3")]
    [InlineData("", "trace", "5")]
    [InlineData(Step + "A = Step\n", "A", "3")]
    [InlineData(Gcd, "Gcd", "48, 18")]
    public async Task ForwardedCallables_FollowTheResolvedTarget(string definitions, string target, string state)
    {
        var (direct, _) = await AllRoutesAsync($"{definitions}repeat({target}, 2, {state})");
        var (once, _) = await AllRoutesAsync($"{definitions}{Forward}Run({target}, {state})");
        var (twice, _) = await AllRoutesAsync($"{definitions}{Forward}Run2({target}, {state})");
        Assert.Equal(direct.Semantic, once.Semantic);
        Assert.Equal(direct.Semantic, twice.Semantic);
    }

    // ── 5. Zero iterations never project the step (LOOP-05) ────────────────────────────────────

    [Theory]
    [InlineData(Step + "repeat(Step, 0, trace(1))")]
    [InlineData(Partial + "repeat(F, 0, trace(1))")]
    [InlineData("repeat(count, 0, trace(1))")]
    [InlineData("repeat(5, 0, trace(1))")]
    [InlineData("repeat(trace(9) / 0, 0, trace(1))")]
    [InlineData(Step + "A = Step\nrepeat(A, 0, trace(1))")]
    [InlineData("A = count\nB = A\nrepeat(B, 0, trace(1))")]
    public async Task ZeroIterations_NeverProjectOrInvokeTheStep(string source)
    {
        // The step expression is never evaluated (no trace(9)); the initial cell is demanded only by
        // the final materialization of the unchanged state.
        var (observation, budget) = await AllRoutesAsync(source);
        Assert.Equal(("ok", "1"), (observation.Kind, observation.Value));
        Assert.Equal(["trace(1)"], observation.HostCalls);
        var (_, reference) = await AllRoutesAsync("U(n) = n\nrepeat(U, 0, trace(1))");
        Assert.Equal(reference, budget);
    }

    // ── 6. Model C: the loop transports the state cells to the ordinary dispatcher ──────────────

    /// <summary>One iteration over a cell supply versus the ordinary call with the same written supply:
    /// the same demand (which cells, in which order, how often), effects and outcome.</summary>
    public static TheoryData<string, string, string> OneIterationAndCall() => new()
    {
        { "ready cells", "F(0, b) = 0, b\nF(a, b) = a - 1, b + 1\n", "2, trace(10)" },
        { "deferred success shared by clause attempts", "F(0, b) = 0\nF(1, b) = 1\nF(a, b) = b\n", "trace(1) + 1, 5" },
        { "undemanded deferred failure", "F(0, b) = 0\nF(a, b) = a\n", "2, trace(1) / 0" },
        { "demanded deferred failure", "F(0, b) = 0\nF(a, b) = b + b\n", "2, trace(1) / 0" },
        { "failure during clause inspection", "F(0, b) = 0, 0\nF(a, b) = 1, 1\n", "trace(1) / 0, 1" },
        { "first-demand order", "F(a, b, 0) = a\nF(a, b, c) = b + a\n", "trace(1), trace(2), trace(3)" },
        { "repeated-name inspection", "E(x, x) = 0\nE(a, b) = 1\n", "trace(2), trace(2)" },
        { "structural inspection", "S((a, b)) = a\nS([a, b]) = b\n", "trace([1, 2])" },
        { "builtin collection and control", "", "trace([1, 2, 3]), trace(2)" },
        { "builtin lazy branches", "", "trace(true), trace(1), trace(2) / 0" },
        { "builtin spread failure before arity", "", "trace(1), trace(2), trace(3)" },
    };

    [Theory]
    [MemberData(nameof(OneIterationAndCall))]
    public async Task OneIteration_DemandsExactlyWhatTheOrdinaryCallDemands(string scenario, string definitions, string supply)
    {
        var callee = definitions.Length == 0 ? scenario switch
        {
            "builtin collection and control" => "take",
            "builtin lazy branches" => "if",
            _ => "take",
        } : definitions[..definitions.IndexOf('(')];
        var (loop, _) = await AllRoutesAsync($"{definitions}repeat({callee}, 1, {supply})");
        var (call, _) = await AllRoutesAsync($"{definitions}{callee}({supply})");
        Assert.Equal(call.Semantic, loop.Semantic);
    }

    [Theory]
    [InlineData("Run(x, y) = repeat(F, 1, x, y)\nF(0, b) = b\nF(a, b) = a\nRun(trace(4), trace(5))",
        "Run(x, y) = F(x, y)\nF(0, b) = b\nF(a, b) = a\nRun(trace(4), trace(5))")]
    [InlineData("Outer(k) = {\n  S(0) = k\n  S(n) = n - 1\n  repeat(S, 2, 1)\n}\nOuter(trace(9))",
        "Outer(k) = {\n  S(0) = k\n  S(n) = n - 1\n  S(S(1))\n}\nOuter(trace(9))")]
    [InlineData("A = trace(7)\nF(0) = A\nF(n) = A + n\nrepeat(F, 2, 1), A",
        "A = trace(7)\nF(0) = A\nF(n) = A + n\nF(F(1)), A")]
    public async Task ForwardedAndCapturedCells_AreTransportedNotForced(string loop, string calls)
    {
        var (looped, _) = await AllRoutesAsync(loop);
        var (called, _) = await AllRoutesAsync(calls);
        Assert.Equal(called.Semantic, looped.Semantic);
    }

    [Fact]
    public async Task FamilyStep_LocalPropertiesBelongToEachIterationsActivation()
    {
        const string definitions = "A = tick()\nF(0) = 0\nF(n) = {\n  T = n + tick()\n  n - 1 + A - A + T - T\n}\n";
        var (loop, _) = await AllRoutesAsync(definitions + "repeat(F, 3, 3), A");
        var (call, _) = await AllRoutesAsync(definitions + "F(F(F(3))), A");
        Assert.Equal(call.Semantic, loop.Semantic);
        Assert.Equal(["tick#1", "tick#2", "tick#3", "tick#4"], loop.HostCalls);
    }

    [Theory]
    [InlineData("F(0, b) = b\nF(a, b) = a\n", "repeat(F, 1, randomInt(0, 1), random(0, 1))", "F(randomInt(0, 1), random(0, 1))")]
    [InlineData("F(0) = randomInt(0, 9)\nF(n) = n + randomInt(0, 9)\n", "repeat(F, 2, 0)", "F(F(0))")]
    [InlineData("", "repeat(range, 1, randomInt(1, 3), randomInt(3, 5))", "range(randomInt(1, 3), randomInt(3, 5))")]
    [InlineData("Go(f) = repeat(map, 1, [1, 2], f)\nR(x) = x + randomInt(0, 9)\n", "Go(R)", "map([1, 2], R)")]
    public async Task SeededRandomness_DrawsInTheOrdinaryOrder(string definitions, string loop, string call)
    {
        foreach (var seed in new long[] { 3, 7, 11 })
        {
            var (looped, _) = await AllRoutesAsync(definitions + loop, seed);
            var (called, _) = await AllRoutesAsync(definitions + call, seed);
            Assert.Equal("ok", looped.Kind);
            Assert.Equal(called.Semantic, looped.Semantic);
        }
    }

    [Theory]
    [InlineData(Step + "repeat(Step, cancel(1), trace(3))", null)]
    [InlineData("F(0, b) = 0\nF(a, b) = a + b\nrepeat(F, 1, cancel(5), trace(6))", "F(0, b) = 0\nF(a, b) = a + b\nF(cancel(5), trace(6))")]
    [InlineData("repeat(take, 1, cancel([1, 2]), trace(1))", "take(cancel([1, 2]), trace(1))")]
    [InlineData("F(0) = 0\nF(n) = cancel(n) - 1 + trace(100)\nrepeat(F, 3, 3)", "F(0) = 0\nF(n) = cancel(n) - 1 + trace(100)\nF(F(F(3)))")]
    [InlineData("Go(f) = repeat(map, 1, [1, 2], f)\nInc(x) = cancel(x) + trace(x)\nGo(Inc)", "Go(f) = map([1, 2], f)\nInc(x) = cancel(x) + trace(x)\nGo(Inc)")]
    public async Task Cancellation_IsObservedWhereTheOrdinaryCallObservesIt(string loop, string? call)
    {
        var (looped, _) = await AllRoutesAsync(loop);
        Assert.Equal("cancelled", looped.Kind);
        if (call is null)
        {
            // Cancelled while the count is demanded: the step is never projected or invoked.
            Assert.Equal(["cancel(1)"], looped.HostCalls);
            return;
        }

        var (called, _) = await AllRoutesAsync(call);
        Assert.Equal(called.Semantic, looped.Semantic);
    }

    // ── 7. Strategies, limits and accounting (Q-09) ─────────────────────────────────────────────

    public static TheoryData<string, string> LimitedPrograms() => new()
    {
        { Step + "repeat(Step, 50, 50)", "max-steps=40" },
        { Step + "repeat(Step, 50, 50)", "max-depth=1" },
        { "F(0) = 0\nF(n) = F(n - 1)\nrepeat(F, 1, 30)", "max-depth=12" },
        { "repeat(range, 1, 1, 50)", "max-coll=30" },
        { "repeat(order, 5, [5, 4, 3, 2, 1, 6, 7, 8, 9, 10])", "max-mat=40" },
        { "repeat(count, 1, 'abcdefghijkl')", "max-string=8" },
        { "F(0) = 'done'\nF(n) = n.string\nrepeat(F, 1, 12345)", "max-string-chars=3" },
        { "while(first, [true])", "max-steps=200" },
        { "F(0) = 0, false\nF(n) = n, true\nwhile(F, 1)", "max-steps=200" },
        { "S(x) = repeat(F, 2, x)\nF(0) = 0\nF(n) = n - 1\nrepeat(S, 3, 10)", "max-steps=9" },
        { "S(x) = repeat(W, 2, x)\nW(n) = F(n)\nF(0) = 0\nF(n) = n - 1\nrepeat(S, 3, 10)", "max-steps=9" },
        { "S(c) = repeat(order, 1, c)\nrepeat(S, 2, [3, 1, 2])", "default" },
        { "S(x) = repeat(F, 1, x + 2), x < 5\nF(0) = 0\nF(n) = n - 1\nwhile(S, 0)", "default" },
    };

    [Theory]
    [MemberData(nameof(LimitedPrograms))]
    public async Task NewStepShapes_ChargeIdenticallyOnEveryStrategy(string source, string limits)
    {
        // AllRoutesAsync requires the same outcome on all six routes and the same steps, expression
        // checkpoints, peak depth and materialization counters on Generic, Optimized and ForcedTwin.
        var (observation, budget) = await AllRoutesAsync(source, limits: ParseLimits(limits));
        Assert.NotEqual("parse", observation.Kind);
        Assert.True(budget.Steps > 0);
    }

    [Fact]
    public void DirectFamilyStep_ChargesExactlyAUserStepsIterationCost_AndNoInvocationDepth()
    {
        // One step per iteration and the step's own expression work; no hidden wrapper call and no
        // invocation level (a loop-step invocation is outside the depth protocol for every shape).
        var family = Observe(Step + "repeat(Step, 50, 50)", optimize: false);
        var user = Observe("U(n) = n - 1\nrepeat(U, 50, 50)", optimize: false);
        var wrapper = Observe(Step + "W(n) = Step(n)\nrepeat(W, 50, 50)", optimize: false);

        Assert.Equal("0", family.Value);
        Assert.Equal(user.Budget, family.Budget);
        Assert.Equal(0, family.Budget.PeakDepth);
        Assert.True(wrapper.Budget.Steps > family.Budget.Steps, "the wrapper genuinely performs an extra call per iteration");
        Assert.True(wrapper.Budget.PeakDepth > family.Budget.PeakDepth);
    }

    [Theory]
    [InlineData("repeat(range, 1, 1, 50)", "W(a, b) = range(a, b)\nrepeat(W, 1, 1, 50)")]
    [InlineData("repeat(order, 5, [5, 4, 3, 2, 1, 6, 7, 8, 9, 10])", "W(c) = order(c)\nrepeat(W, 5, [5, 4, 3, 2, 1, 6, 7, 8, 9, 10])")]
    [InlineData("repeat(first, 3, [[[7]]])", "W(c) = first(c)\nrepeat(W, 3, [[[7]]])")]
    public void BuiltinStep_OneRowReading_ChargesNoExtraWork(string direct, string wrapper)
    {
        // Reading the builtin's one result as one row is cardinality, not evaluation: the builtin's own
        // materialization is the wrapper's, and the direct step never costs more than the wrapper.
        var step = Observe(direct, optimize: false);
        var wrapped = Observe(wrapper, optimize: false);
        Assert.Equal(wrapped.Value, step.Value);
        Assert.Equal(wrapped.Budget.MaterializedItems, step.Budget.MaterializedItems);
        Assert.Equal(wrapped.Budget.Steps, step.Budget.Steps);
        Assert.True(step.Budget.Checkpoints < wrapped.Budget.Checkpoints);
    }

    [Fact]
    public void PlannedOuterLoop_RunsAFamilyOrBuiltinInnerLoopGenerically_WithIdenticalCharges()
    {
        foreach (var source in new[]
                 {
                     "S(x) = repeat(F, 2, x)\nF(0) = 0\nF(n) = n - 1\nrepeat(S, 3, 10)",
                     "S(c) = repeat(order, 1, c)\nrepeat(S, 2, [3, 1, 2])",
                     "S(x) = repeat(F, 1, x + 2), x < 5\nF(0) = 0\nF(n) = n - 1\nwhile(S, 0)",
                 })
        {
            var generic = Observe(source, optimize: false);
            var planned = Observe(source, optimize: true);
            Assert.Equal(generic.Value, planned.Value);
            Assert.Equal(generic.Budget, planned.Budget);

            // The outer user loop is planned; the inner family/builtin loop is not planner-supported and
            // runs on the generic route — validity never depends on planner support.
            Assert.Contains(planned.Loops!.LoopPlans, plan => plan.Optimized);
            Assert.True(planned.Loops.FallbackReasons.TryGetValue("loop plan unsupported step shape", out var refusals) && refusals > 0);
        }
    }

    [Fact]
    public void PlannedHandover_ContinuesGenerically_AroundFamilyAndBuiltinInnerLoops()
    {
        // The outer step's empty row forces the planned frame to hand the iteration over to the generic
        // continuation, whose iterations run the family/builtin inner loops as ordinary steps.
        foreach (var source in new[]
                 {
                     "I(0) = 0\nI(n) = n - 1\nS(p, n) = if(n < 2, repeat(I, 1, n + 1), ()), n + 1\nrepeat(S, 4, 0, 0)",
                     "S(p, n) = if(n < 2, repeat(count, 1, [n]), ()), n + 1\nrepeat(S, 4, 0, 0)",
                 })
        {
            var generic = Observe(source, optimize: false);
            var planned = Observe(source, optimize: true);
            Assert.Equal(generic.Value, planned.Value);
            Assert.Equal(generic.Budget, planned.Budget);
            Assert.Contains(planned.Loops!.FallbackReasons.Keys, reason => reason.Contains("did not emit exactly one", StringComparison.Ordinal));
        }
    }

    // ── 8. Source admission (Q-71): a selected clause's module is acquired only when selected ─────

    [Theory]
    [InlineData("repeat(F, 3, 2)", "11", 1)]
    [InlineData("repeat(F, 1, 2)", "1", 0)]
    [InlineData("repeat(F, 0, 0)", "0", 0)]
    [InlineData("F(F(F(2)))", "11", 1)]
    public async Task DeferredClauseSource_IsAcquiredOnlyWhenTheClauseIsSelected(string output, string expected, int expectedFetches)
    {
        const string module = "public A = 1";
        var fetches = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) => { Interlocked.Increment(ref fetches); return ValueTask.FromResult(module); },
        };
        var result = await KatLangEngine.RunAsync($"F(0) = {{\n  open 'https://katlang.org/q23/a.kat'\n  A + 10\n}}\nF(n) = n - 1\n{output}", options);
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(expected, SixRouteAgreement.Neutral(success.Value));
        Assert.Equal(expectedFetches, fetches);
    }

    // ── 9. The one-iteration law (Lean `lsOneIterationEqualsTheCall`) ─────────────────────────────

    private const string OneIterationDefinitions =
        Step + Countdown + Gcd + Partial
        + "E(x, x) = 0, 0\nE(a, b) = a + 1, b\nSw((a, b)) = (b, a)\nSw([a, b]) = [b, a]\nTwo(0) = 9, 9\nTwo(n) = n, n\n"
        + "Ord(x) = 1\nOrd(0) = 2\nA = Step\nCnt = count\nC(c) = count(c)\nFi(c) = first(c)\n";

    /// <summary>The Lean law's own case list: families, builtins, aliases and user wrappers, succeeding and failing.</summary>
    public static TheoryData<string, string> OneIterationCases() => new()
    {
        { "Step", "3" }, { "Step", "0" }, { "Countdown", "2" }, { "Gcd", "48, 18" },
        { "F", "1" }, { "F", "5" }, { "E", "2, 2" }, { "E", "0, 2" },
        { "Sw", "(1, 2)" }, { "Sw", "7" }, { "Two", "4" }, { "Ord", "0" },
        { "count", "[1, 2]" }, { "first", "[()]" },
        { "take", "[1, 2, 3], 2" }, { "take", "1" },
        { "if", "true, 1, 2" }, { "if", "5, 1, 2" },
        { "A", "3" }, { "Cnt", "[4]" }, { "C", "[1]" }, { "Fi", "[7, 8]" },
    };

    /// <summary>
    /// THE ONE-ITERATION LAW: one iteration over any callable equals the ordinary call with the same supply
    /// — the value, or each error's code and innermost kind, and the innermost error's whole payload (a
    /// family's no-match names the written callee on both programs; only the enclosing frames differ, the
    /// loop adding its own). LOOP-07: a one-iteration <c>repeat</c> equals the direct call in value and count.
    /// </summary>
    [Theory]
    [MemberData(nameof(OneIterationCases))]
    public async Task OneIteration_EqualsTheOrdinaryCall(string callee, string supply)
    {
        var loop = OneIterationDefinitions + $"repeat({callee}, 1, {supply})";
        var call = OneIterationDefinitions + $"{callee}({supply})";
        var (looped, _) = await AllRoutesAsync(loop);
        var (called, _) = await AllRoutesAsync(call);
        Assert.Equal(called.Semantic, looped.Semantic);
        if (called.Kind == "err")
            Assert.Equal(Innermost(GenericError(call)) with { Span = null }, Innermost(GenericError(loop)) with { Span = null });
    }

    // ── Helpers ──────────────────────────────────────────────────────────────────────────────────

    internal sealed record Budget(long Steps, long Checkpoints, int PeakDepth, long MaterializedItems, long MaterializedStringChars);

    /// <summary>
    /// One route's outcome: kind (<c>ok</c>, <c>err</c>, <c>parse</c>, <c>none</c>, <c>cancelled</c>),
    /// the neutral value, every error as <c>Code: message @ span</c>, every error's cause
    /// (<c>Code/innermost kind</c>), and the host-call log.
    /// </summary>
    internal sealed record Observation(string Kind, string? Value, IReadOnlyList<string> Errors, IReadOnlyList<string> Causes, IReadOnlyList<string> HostCalls)
    {
        public bool Equals(Observation? other)
            => other is not null && Kind == other.Kind && Value == other.Value
                && Errors.SequenceEqual(other.Errors) && Causes.SequenceEqual(other.Causes) && HostCalls.SequenceEqual(other.HostCalls);

        public override int GetHashCode() => HashCode.Combine(Kind, Value);

        /// <summary>The layer two DIFFERENT programs (a loop and the ordinary call, a step and its
        /// wrapper) are compared at: the value, or each error's code and innermost kind, and the host log.</summary>
        public string Semantic
            => (Kind == "ok" ? $"ok {Value}" : $"{Kind} [{string.Join(", ", Causes)}]") + $" host=[{string.Join(",", HostCalls)}]";

        public override string ToString()
            => $"{Kind} {Value} errors=[{string.Join(" | ", Errors)}] host=[{string.Join(",", HostCalls)}]";
    }

    private sealed class HostLog
    {
        private int _ticks;
        public List<string> Calls { get; } = [];
        public CancellationTokenSource Cancellation { get; } = new();

        private Result Log(string call, Result value)
        {
            lock (Calls)
                Calls.Add(call);
            return value;
        }

        public Result Tick() => Log($"tick#{Interlocked.Increment(ref _ticks)}", new Result.Atom(_ticks));

        public Result Trace(Result value) => Log($"trace({SixRouteAgreement.Neutral(value)})", value);

        public Result Cancel(Result value)
        {
            Log($"cancel({SixRouteAgreement.Neutral(value)})", value);
            Cancellation.Cancel();
            return value;
        }
    }

    private static HostOperations Operations(HostLog log, bool suspending)
        => suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x"),
                HostOperation.CreateAsync("cancel", async (args, _) => { await Task.Yield(); return log.Cancel(args[0]); }, "x"))
            : HostOperations.Create(
                HostOperation.Create("tick", (_, _) => log.Tick()),
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"),
                HostOperation.Create("cancel", (args, _) => log.Cancel(args[0]), "x"));

    private static async Task<(Observation Observation, Budget? Budget)> ObserveAsync(
        SixRouteAgreement.Route route, string source, long? seed, EvaluationLimits? limits)
    {
        var log = new HostLog();
        var operations = Operations(log, route is SixRouteAgreement.Route.EngineAsyncTwin or SixRouteAgreement.Route.ForcedTwin);
        var options = new RunOptions
        {
            HostOperations = operations,
            RandomSeed = seed,
            EvaluationLimits = limits,
            EvaluationCancellationToken = log.Cancellation.Token,
        };
        try
        {
            switch (route)
            {
                case SixRouteAgreement.Route.EngineSync:
                    return (FromRunResult(KatLangEngine.Run(source, options), log), null);
                case SixRouteAgreement.Route.EngineAsync:
                case SixRouteAgreement.Route.EngineAsyncTwin:
                    return (FromRunResult(await KatLangEngine.RunAsync(source, options), log), null);
            }

            var parsed = Parser.Parse(source, options);
            if (parsed.HasErrors)
                return (new Observation("parse", null, [.. parsed.Diagnostics.Select(static d => d.Message)], [], [.. log.Calls]), null);

            var program = new Expr.AlgorithmExpr(parsed.Root);
            var (result, budget) = route switch
            {
                SixRouteAgreement.Route.Generic => Evaluator.RunCountedObserved(program, limits: limits, enableOptimizations: false,
                    hostOperations: operations, randomSeed: seed, cancellationToken: log.Cancellation.Token),
                SixRouteAgreement.Route.Optimized => Evaluator.RunCountedObserved(program, limits: limits, enableOptimizations: true,
                    hostOperations: operations, randomSeed: seed, cancellationToken: log.Cancellation.Token),
                SixRouteAgreement.Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(program, limits: limits,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                    hostOperations: operations, randomSeed: seed, cancellationToken: log.Cancellation.Token),
                _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
            };
            var counters = new Budget(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
                budget.MaterializedItems, budget.MaterializedStringChars);
            return result.IsError
                ? (FromError(KatLangError.FromEvalError(result.Error), log), counters)
                : (new Observation("ok", SixRouteAgreement.Neutral(result.Value.Value), [], [], [.. log.Calls]), counters);
        }
        catch (OperationCanceledException)
        {
            return (new Observation("cancelled", null, [], [], [.. log.Calls]), null);
        }
    }

    /// <summary>
    /// Runs <paramref name="source"/> on every route; requires every route to agree with the synchronous
    /// engine and the three evaluator routes to report identical budget counters. Returns the oracle and
    /// the evaluator routes' counters.
    /// </summary>
    private static async Task<(Observation Observation, Budget Budget)> AllRoutesAsync(string source, long? seed = null, EvaluationLimits? limits = null)
    {
        var (oracle, _) = await ObserveAsync(SixRouteAgreement.Route.EngineSync, source, seed, limits);
        Assert.True(oracle.Kind != "parse", $"source must parse cleanly: {oracle}\nsource:\n{source}");
        Budget? counters = null;
        foreach (var route in SixRouteAgreement.Routes.Skip(1))
        {
            var (observation, budget) = await ObserveAsync(route, source, seed, limits);
            Assert.True(oracle.Equals(observation), $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
            if (budget is null)
                continue;
            if (counters is null)
                counters = budget;
            else
                Assert.True(counters == budget, $"{route}: budget {budget} differs from {counters}\nsource:\n{source}");
        }

        return (oracle, counters ?? new Budget(0, 0, 0, 0, 0));
    }

    private sealed record Run(string? Value, Budget Budget, LoopOptimizationDiagnosticsSnapshot? Loops);

    /// <summary>The generic or optimized evaluator alone, with its loop diagnostics.</summary>
    private static Run Observe(string source, bool optimize)
    {
        var log = new HostLog();
        var operations = Operations(log, suspending: false);
        var program = new Expr.AlgorithmExpr(ParseValid(source, operations));
        var loops = new LoopOptimizationDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: optimize, loopDiagnostics: loops, hostOperations: operations);
        return new Run(result.IsOk ? SixRouteAgreement.Neutral(result.Value.Value) : "err " + result.Error.Code,
            new Budget(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth, budget.MaterializedItems, budget.MaterializedStringChars),
            loops.GetSnapshot());
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", SixRouteAgreement.Neutral(success.Value), [], [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(Describe)], [.. failure.Errors.Select(Cause)], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", null, [.. failure.Errors.Select(Describe)], [.. failure.Errors.Select(Cause)], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, [none.Diagnostic.Code.ToString()], [], [.. log.Calls]),
    };

    private static Observation FromError(KatLangError error, HostLog log)
        => new("err", null, [Describe(error)], [Cause(error)], [.. log.Calls]);

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";

    private static string Cause(KatLangError error)
        => $"{error.Code}/{(error.Source is EvalError evalError ? Innermost(evalError).GetType().Name : "front-end")}";

    private static EvalError GenericError(string source)
    {
        var log = new HostLog();
        var operations = Operations(log, suspending: false);
        var program = new Expr.AlgorithmExpr(ParseValid(source, operations));
        var (result, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false, hostOperations: operations);
        Assert.True(result.IsError, source);
        return result.Error;
    }

    /// <summary>A source the front end accepts, parsed with the host operations its names resolve to.</summary>
    private static Algorithm.User ParseValid(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return parsed.Root;
    }

    private static string[] Frames(EvalError error)
    {
        var frames = new List<string>();
        while (error is EvalError.WithContext context)
        {
            frames.Add(context.ErrorContext.ToString() ?? "");
            error = context.Inner;
        }

        return [.. frames];
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static EvaluationLimits? ParseLimits(string text)
    {
        if (text == "default")
            return null;
        var (key, value) = (text[..text.IndexOf('=')], long.Parse(text[(text.IndexOf('=') + 1)..], System.Globalization.CultureInfo.InvariantCulture));
        return key switch
        {
            "max-steps" => new EvaluationLimits { MaxSteps = value },
            "max-depth" => new EvaluationLimits { MaxDepth = (int)value },
            "max-coll" => new EvaluationLimits { MaxCollectionItems = (int)value },
            "max-mat" => new EvaluationLimits { MaxMaterializedItems = value },
            "max-string" => new EvaluationLimits { MaxStringLength = (int)value },
            "max-string-chars" => new EvaluationLimits { MaxMaterializedStringChars = value },
            _ => throw new ArgumentOutOfRangeException(nameof(text), text, null),
        };
    }
}
