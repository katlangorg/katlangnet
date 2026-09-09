using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Semantics;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// SYN-05. Builtin callables are ORDINARY prelude bindings. Lexical resolution
/// selects exactly one binding without considering arity; the resolved callable
/// then determines its signature and semantics:
///
/// <code>
/// resolve the lexical name
///   -> select exactly one callable identity
///   -> construct the ordinary argument supply (written slots, dot-call receiver
///      injection, explicit spread)
///   -> bind against THAT callable's signature
///   -> invoke it
/// </code>
///
/// <para>Never <c>name + argument count -&gt; choose matching callable</c>: KatLang has
/// no overloading by arity, so a user-defined <c>if</c> shadows the builtin
/// COMPLETELY rather than coexisting beside it at a different arity.</para>
///
/// <para><c>if</c> is the interesting instance because its INVOCATION is intrinsic
/// (evaluate the condition, then only the selected branch) — but that is a property
/// of the resolved identity, never of the written spelling <c>"if"</c>. Before
/// SYN-05 the parser counted the arguments of any call whose callee was spelled
/// <c>if</c> before resolution ever ran, so the direct spelling disagreed with the
/// dot-call and spread surfaces and — with a user <c>if</c> in scope — with the
/// callable the program actually invoked.</para>
///
/// <para>Companion suites: <see cref="IfBuiltinArityPayloadTests"/> pins the
/// structured arity payload, <c>EvaluatorIfBuiltinTests</c> pins builtin
/// <c>if</c> value semantics, and <c>ParserTests</c> pins that the parser stays
/// purely syntactic about callee spellings.</para>
/// </summary>
public class BuiltinCallableIdentityTests
{
    // ── A. Builtin direct composition ───────────────────────────────────────

    /// <summary>
    /// With no nearer <c>if</c> binding, every spelling that assembles three
    /// arguments resolves the builtin and selects the same branch: written slots,
    /// dot-call receiver injection, spread in any position, spread through a
    /// dot-call, and invocation through a higher-order parameter.
    /// </summary>
    [Theory]
    [InlineData("if(1, 10, 20)")]
    [InlineData("1.if(10, 20)")]
    [InlineData("if((1, 10, 20)*)")]
    [InlineData("if(1, (10, 20)*)")]
    [InlineData("1.if((10, 20)*)")]
    [InlineData("Args = (1, 10, 20)\nif(Args*)")]
    [InlineData("Branches = (10, 20)\nif(1, Branches*)")]
    [InlineData("Branches = (10, 20)\n1.if(Branches*)")]
    [InlineData("Cond = 1\nBranches = (10, 20)\nCond.if(Branches*)")]
    [InlineData("Apply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, 10, 20)")]
    [InlineData("Args = (1, 10, 20)\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, Args*)")]
    [InlineData("Apply(f) = f(1, 10, 20)\nApply(if)")]
    [InlineData("MyIf(a, b, c) = if(a, b, c)\nMyIf(1, 10, 20)")]
    public void BuiltinIf_EveryThreeArgumentSpelling_SelectsTheTrueBranch(string source)
        => AssertEval(source, 10);

    [Theory]
    [InlineData("if(0, 10, 20)")]
    [InlineData("0.if(10, 20)")]
    [InlineData("Args = (0, 10, 20)\nif(Args*)")]
    [InlineData("Branches = (10, 20)\n0.if(Branches*)")]
    [InlineData("Apply3(f, a, b, c) = f(a, b, c)\nApply3(if, 0, 10, 20)")]
    public void BuiltinIf_EveryThreeArgumentSpelling_SelectsTheFalseBranchAlike(string source)
        => AssertEval(source, 20);

    /// <summary>
    /// Dynamically produced supplies, not just literal syntax: the spread operand is
    /// computed at run time and still lands in the ordinary three slots.
    /// </summary>
    [Theory]
    [InlineData("Args = range(1, 3)\nif(Args*)", 2)]
    [InlineData("Pick(n) = (n, 10, 20)\nif(Pick(1)*)", 10)]
    [InlineData("Pick(n) = (n, 10, 20)\nif(Pick(0)*)", 20)]
    [InlineData("Tail(n) = (n, n * 2)\nif(1, Tail(10)*)", 10)]
    public void BuiltinIf_DynamicallyProducedSupplies_BindTheSameWay(string source, int expected)
        => AssertEval(source, expected);

    // ── B/C. Property shadowing, at any arity ───────────────────────────────

    /// <summary>
    /// A nearer property shadows the builtin COMPLETELY, and every spelling agrees
    /// on that one selected callable. <c>7.if</c> is the lexical dot-call fallback
    /// <c>if(7)</c>, and <c>if((7)*)</c> spreads a one-item supply into one slot.
    /// </summary>
    [Theory]
    [InlineData("if(x) = x + 1\nif(7)")]
    [InlineData("if(x) = x + 1\n7.if")]
    [InlineData("if(x) = x + 1\nif((7)*)")]
    [InlineData("if(x) = x + 1\nSeven = 7\nif(Seven*)")]
    [InlineData("if(x) = x + 1\nApply(f, a) = f(a)\nApply(if, 7)")]
    public void UserIf_ShadowsTheBuiltin_OnEverySpelling(string source)
        => AssertEval(source, 8);

    /// <summary>
    /// The critical no-overloading case: a three-argument call against a
    /// one-parameter user <c>if</c> must NOT fall back to the builtin <c>if/3</c>.
    /// The diagnostic names the signature lexical resolution actually selected.
    /// </summary>
    [Theory]
    [InlineData("if(1, 2, 3)")]
    [InlineData("1.if(2, 3)")]
    [InlineData("if((1, 2, 3)*)")]
    [InlineData("(1, 2, 3)*.if")]
    [InlineData("Apply(if) = if(1, 2, 3)\nApply(if)")]
    public void UserIf_WrongArityCall_DoesNotFallBackToTheBuiltin(string call)
    {
        var arity = AssertEvalFailsWithArityMismatch(
            "if(x) = x + 1\n" + call, expected: 1, actual: 3);

        Assert.Equal("if", arity.Signature?.Name);
        Assert.Equal(
            "Callable `if(x)` expects 1 argument, but was called with 3 arguments.",
            KatLangError.FromEvalError(arity).Message);
    }

    /// <summary>
    /// Same-arity shadowing: the user callable wins even though the builtin would
    /// have accepted the identical argument count. This is what proves builtin
    /// behavior comes from resolved IDENTITY — not from the spelling, and not from a
    /// matching arity. 31 is the user's sum; 10 would be the builtin's branch.
    /// </summary>
    [Theory]
    [InlineData("if(a, b, c) = a + b + c\nif(1, 10, 20)")]
    [InlineData("if(a, b, c) = a + b + c\n1.if(10, 20)")]
    [InlineData("if(a, b, c) = a + b + c\nif((1, 10, 20)*)")]
    [InlineData("if(a, b, c) = a + b + c\nBranches = (10, 20)\n1.if(Branches*)")]
    [InlineData("if(a, b, c) = a + b + c\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, 10, 20)")]
    public void UserIf_OfTheSameArity_StillWins(string source)
        => AssertEval(source, 31);

    /// <summary>
    /// A shadowing user <c>if</c> is an ordinary callable in every other respect, so
    /// intrinsic branch laziness goes away with the builtin identity. The failure is
    /// observed by READING the would-be-unselected branch: an ordinary user call
    /// binds every parameter eagerly, and a failing value binding is retained on the
    /// binding rather than raised, so an unread parameter would hide the difference.
    /// (<see cref="OnlyTheSelectedBranch_RunsItsHostCallback"/> observes the same
    /// distinction by counting invocations instead, where nothing can be retained.)
    /// </summary>
    [Fact]
    public void UserIf_IsNotLazy_BecauseLazinessBelongsToTheBuiltinIdentity()
    {
        AssertEval("Boom = 1 / 0\nif(1, 10, Boom)", 10);
        AssertDivisionByZero("if(a, b, c) = b + c\nBoom = 1 / 0\nif(1, 10, Boom)");
    }

    // ── D. Parameter shadowing ──────────────────────────────────────────────

    /// <summary>
    /// A parameter is a binding like any other, so it shadows the prelude too, and
    /// invoking it invokes whatever callable it denotes. Covered at the owning
    /// algorithm, from a nested body that captures it, and beside the
    /// still-visible builtin in an unrelated scope.
    /// </summary>
    [Theory]
    [InlineData("Apply(if, x) = if(x)\nInc(x) = x + 1\nApply(Inc, 7)", 8)]
    [InlineData("Apply(if, x) = { Inner = if(x)\n  Inner }\nInc(x) = x + 1\nApply(Inc, 7)", 8)]
    [InlineData("Apply(if, x) = if(x)\nInc(x) = x + 1\nApply(Inc, 7) + if(1, 0, 100)", 8)]
    [InlineData("Apply(if, x) = x.if\nInc(x) = x + 1\nApply(Inc, 7)", 8)]
    [InlineData("Apply(if, x) = if(x*)\nInc(x) = x + 1\nApply(Inc, 7)", 8)]
    [InlineData("Outer = { if(x) = x + 1\n Inner = if(7)\n Inner }\nOuter + if(1, 10, 20)", 18)]
    [InlineData("Obj = { if(x) = x + 1 }\nObj.if(7)", 8)]
    [InlineData("F(count) = count + 1\nF(4)", 5)]
    public void AParameter_ShadowsThePreludeBinding(string source, int expected)
        => AssertEval(source, expected);

    /// <summary>
    /// The shadowed name is genuinely gone from that scope: a supplied callable of a
    /// different arity fails against ITS signature, never against the builtin's. The
    /// reported shape is the SUPPLIED callable's (one parameter, spelled <c>x</c> by
    /// <c>Inc</c>) under the name the call site wrote — builtin <c>if/3</c> would have
    /// accepted these three arguments, and is never consulted.
    /// </summary>
    [Fact]
    public void AShadowingParameter_IsTheOnlyCandidate()
    {
        var arity = AssertEvalFailsWithArityMismatch(
            "Apply(if) = if(1, 2, 3)\nInc(x) = x + 1\nApply(Inc)", expected: 1, actual: 3);

        Assert.Equal(
            "Callable `if(x)` expects 1 argument, but was called with 3 arguments.",
            KatLangError.FromEvalError(arity).Message);
    }

    // ── E. Higher-order builtin identity ────────────────────────────────────

    /// <summary>
    /// Bare <c>if</c> is a legal higher-order reference: the ordinary algorithm
    /// channel carries the builtin identity, and the callee invokes it. Shadowing
    /// swaps the identity the SAME reference carries, with no change to the calling
    /// code.
    /// </summary>
    [Fact]
    public void HigherOrder_CarriesTheResolvedIdentity()
    {
        const string caller = "Apply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, 10, 20)";
        AssertEval(caller, 10);
        AssertEval("if(a, b, c) = a + b + c\n" + caller, 31);
    }

    // ── F/H. One arity contract, validated at ONE boundary ──────────────────

    /// <summary>
    /// Every assembled supply of other than three fails with the same structured
    /// payload, whichever surface built it: <c>Expected</c> is 3 from the builtin
    /// registry's signature metadata and <c>Actual</c> is the count AFTER receiver
    /// injection and spread expansion. Nothing here is an <c>if</c> rule — it is the
    /// resolved signature being validated once, after the supply exists.
    /// </summary>
    [Theory]
    // Direct written slots — these were the parser-gated forms before SYN-05.
    [InlineData("if()", 0)]
    [InlineData("if(1)", 1)]
    [InlineData("if(1, 2)", 2)]
    [InlineData("if(1, 2, 3, 4)", 4)]
    // Explicit spread, literal and via a property.
    [InlineData("if(()*)", 0)]
    [InlineData("if((1, 2)*)", 2)]
    [InlineData("if((1, 2, 3, 4)*)", 4)]
    [InlineData("Two = 1, 2\nif(Two*)", 2)]
    [InlineData("Four = 1, 2, 3, 4\nif(Four*)", 4)]
    [InlineData("Pair = 2, 3\nif(1, 2, Pair*)", 4)]
    // Dot-call: the injected receiver counts as one argument.
    [InlineData("1.if(2)", 2)]
    [InlineData("1.if(2, 3, 4)", 4)]
    [InlineData("Pair = 2, 3\n1.if(2, Pair*)", 4)]
    [InlineData("A = 1\nA.if(2)", 2)]
    // Through a higher-order parameter.
    [InlineData("Apply2(f, a, b) = f(a, b)\nApply2(if, 1, 2)", 2)]
    [InlineData("Apply4(f, a, b, c, d) = f(a, b, c, d)\nApply4(if, 1, 2, 3, 4)", 4)]
    [InlineData("Args = (1, 2)\nApply(f, a) = f(a*)\nApply(if, Args)", 2)]
    public void BuiltinIf_EveryWrongArity_FailsWithTheSameStructuredPayload(string source, int actual)
    {
        var arity = AssertEvalFailsWithArityMismatch(source, expected: 3, actual: actual);

        Assert.Equal("if", arity.Signature?.Name);
        var noun = actual == 1 ? "argument" : "arguments";
        Assert.Equal(
            $"Callable `if(condition, whenTrue, whenFalse)` expects 3 arguments, but was called with {actual} {noun}.",
            KatLangError.FromEvalError(arity).Message);
    }

    /// <summary>
    /// A bare <c>if</c> demanded as a VALUE is the ordinary zero-argument demand of
    /// a three-parameter callable, not a special "if is not a value" rule.
    /// </summary>
    [Fact]
    public void BareIf_InValuePosition_IsAnOrdinaryZeroArgumentDemand()
        => AssertEvalFailsWithArityMismatch("if", expected: 3, actual: 0);

    /// <summary>
    /// The arity failure is an EVALUATION error, not a parse error: a malformed
    /// <c>if</c> call in an unreachable property is inert, exactly like every other
    /// fixed-arity builtin. That partition alignment is what removing the parser's
    /// raw-spelling gate bought.
    /// </summary>
    [Theory]
    [InlineData("Unused = if(1, 2)\n7")]
    [InlineData("Unused = count(1, 2, 3)\n7")]
    [InlineData("Unused = range(1)\n7")]
    [InlineData("if(1, 7, if(1, 2))")]
    [InlineData("0.if(if(1, 2), 7)")]
    public void MalformedBuiltinCall_InAnUnevaluatedProperty_IsInert(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        AssertEval(source, 7);
    }

    /// <summary>
    /// The diagnostic anchors on the whole call — the span coverage the removed
    /// parser gate used to provide, now supplied by the authoritative binding
    /// boundary instead of duplicated ahead of it.
    /// </summary>
    [Theory]
    [InlineData("if(1, 2)", 1, 1, 1, 8)]
    [InlineData("if()", 1, 1, 1, 4)]
    [InlineData("if(1, 2, 3, 4)", 1, 1, 1, 14)]
    [InlineData("P = if(1, 2)\nP", 1, 5, 1, 12)]
    [InlineData("X = 1\nif(1, 2)\nX", 2, 1, 2, 8)]
    [InlineData("X = 1\nif(1, 2)\nLongIdentifierHere = 3\nLongIdentifierHere", 2, 1, 2, 8)]
    [InlineData("if(\n  1,\n  2\n)", 1, 1, 4, 1)]
    [InlineData("1.if(2)", 1, 1, 1, 7)]
    [InlineData("if((1, 2)*)", 1, 1, 1, 11)]
    public void ArityDiagnostic_SpansTheWholeCall(
        string source, int startLine, int startColumn, int endLine, int endColumn)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);

        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        Assert.Equal(startLine, error.StartLine);
        Assert.Equal(startColumn, error.StartColumn);
        Assert.Equal(endLine, error.EndLine);
        Assert.Equal(endColumn, error.EndColumn);
    }

    // ── G. Laziness belongs to the builtin identity ─────────────────────────

    /// <summary>
    /// The builtin does not demand the unselected branch. A user wrapper may already
    /// have attempted its value evaluation and retained a failing algorithm binding;
    /// success alone does not prove non-execution. Callback tests below observe that.
    /// </summary>
    [Theory]
    [InlineData("if(1, 10, 1 / 0)", 10)]
    [InlineData("if(0, 1 / 0, 20)", 20)]
    [InlineData("1.if(10, 1 / 0)", 10)]
    [InlineData("0.if(1 / 0, 20)", 20)]
    [InlineData("Boom = 1 / 0\nif(1, 10, Boom)", 10)]
    [InlineData("Boom = 1 / 0\n0.if(Boom, 20)", 20)]
    [InlineData("Boom = 1 / 0\nMyIf(a, b, c) = if(a, b, c)\nMyIf(1, 10, Boom)", 10)]
    [InlineData("Boom = 1 / 0\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, 10, Boom)", 10)]
    [InlineData("Boom = 1 / 0\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, 0, Boom, 20)", 20)]
    [InlineData("Boom = 1 / 0\nApply(f) = f(1, 10, Boom)\nApply(if)", 10)]
    public void BuiltinIf_DoesNotDemandTheUnselectedBranch(string source, int expected)
        => AssertEval(source, expected);

    /// <summary>The other direction: the SELECTED branch genuinely is demanded.</summary>
    [Theory]
    [InlineData("if(1, 1 / 0, 20)")]
    [InlineData("if(0, 10, 1 / 0)")]
    [InlineData("1.if(1 / 0, 20)")]
    [InlineData("Boom = 1 / 0\nif(1, Boom, 20)")]
    [InlineData("Boom = 1 / 0\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, Boom, 20)")]
    public void TheSelectedBranch_IsDemanded(string source)
        => AssertDivisionByZero(source);

    /// <summary>
    /// Laziness is a property of INVOCATION, not a promise about arguments the
    /// caller already evaluated. Building a value evaluates its rows; spreading that
    /// finished value into argument slots happens afterwards:
    /// <c>expression -&gt; value -&gt; supply -&gt; argument binding</c>. Pinned
    /// separately so a future reader cannot mistake this for a laziness regression —
    /// it is not an <c>if</c> exception, and a user callable of the same shape
    /// behaves identically.
    /// </summary>
    [Theory]
    [InlineData("Risky = (10, 1 / 0)\nif(1, Risky*)")]
    [InlineData("Risky = (10, 1 / 0)\n1.if(Risky*)")]
    [InlineData("Risky = (1, 10, 1 / 0)\nif(Risky*)")]
    [InlineData("Risky = (10, 1 / 0)\nMyIf(a, b, c) = if(a, b, c)\nMyIf(1, Risky*)")]
    [InlineData("Risky = (10, 1 / 0)\nPick3(a, b, c) = b\nPick3(1, Risky*)")]
    public void ConstructingAValueBeforeSpreadingIt_IsNotLazy(string source)
        => AssertDivisionByZero(source);

    private static void AssertDivisionByZero(string source)
    {
        var result = Eval(source);
        Assert.True(result.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(result.Error));
    }

    /// <summary>
    /// The same distinction on the higher-order path: the CALLER's own argument
    /// binding is the ordinary eager user-call value channel, so a failing argument
    /// expression fails before <c>if</c> is ever reached. Not an <c>if</c> rule
    /// either — the identical wrapper without <c>if</c> fails the same way.
    /// </summary>
    [Fact]
    public void HigherOrderCallerArgumentBinding_IsEagerLikeAnyUserCall()
    {
        AssertDivisionByZero("Apply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, 10, 1 / 0)");
        AssertDivisionByZero("Pick3(a, b, c) = b\nPick3(1, 10, 1 / 0)");

        // A named property also supplies an algorithm binding when its eager value
        // evaluation fails. The builtin can leave that binding unused; this success
        // does not mean the caller never attempted to evaluate Boom.
        AssertEval("Boom = 1 / 0\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, 10, Boom)", 10);
    }

    /// <summary>
    /// Runs <paramref name="source"/> with a host operation <c>Tick(value)</c> that
    /// records every invocation and returns its argument, and returns the recorded
    /// invocations. Counting is a stronger laziness observation than failure: a
    /// failing value binding can be RETAINED on a parameter and never surface, but an
    /// invocation that happened cannot be taken back.
    /// </summary>
    private static IReadOnlyList<Decimal128> RunRecordingTicks(string source, int expected)
    {
        var ticks = new List<Decimal128>();
        var operations = HostOperations.Create(HostOperation.Create(
            "Tick",
            (args, _) =>
            {
                var value = ((Result.Atom)args[0]).Value;
                ticks.Add(value);
                return new Result.Atom(value);
            },
            "value"));

        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));

        var result = Evaluator.Run(
            new Expr.AlgorithmExpr(parsed.Root), operations, limits: null, CancellationToken.None);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal([(Decimal128)expected], result.Value.ToHostAtoms());
        return ticks;
    }

    /// <summary>
    /// Laziness observed by COUNTING rather than by failure: when the builtin identity
    /// is the one INVOKING the branches — a direct call or a dot-call — the unselected
    /// branch is proven never to run and the selected one to run exactly once.
    /// </summary>
    [Theory]
    [InlineData("if(1, Tick(10), Tick(20))", 10)]
    [InlineData("if(0, Tick(10), Tick(20))", 20)]
    [InlineData("1.if(Tick(10), Tick(20))", 10)]
    [InlineData("0.if(Tick(10), Tick(20))", 20)]
    [InlineData("Apply(f) = f(1, Tick(10), Tick(20))\nApply(if)", 10)]
    [InlineData("Apply(f) = f(0, Tick(10), Tick(20))\nApply(if)", 20)]
    [InlineData("Apply(if) = 1.if(Tick(10), Tick(20))\nApply(if)", 10)]
    [InlineData("Apply(if) = 0.if(Tick(10), Tick(20))\nApply(if)", 20)]
    public void OnlyTheSelectedBranch_RunsItsHostCallback(string source, int expected)
        => Assert.Equal([(Decimal128)expected], RunRecordingTicks(source, expected));

    /// <summary>
    /// The counted mirror of <see cref="HigherOrderCallerArgumentBinding_IsEagerLikeAnyUserCall"/>:
    /// when a USER call sits between the branch expressions and <c>if</c>, that call
    /// binds its own arguments eagerly, so both branches have already run before the
    /// builtin ever chooses. Laziness is a property of the invocation that receives
    /// the branch EXPRESSIONS, not of the name <c>if</c> appearing somewhere below.
    /// </summary>
    [Theory]
    [InlineData("Apply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, Tick(10), Tick(20))", 10)]
    [InlineData("MyIf(a, b, c) = if(a, b, c)\nMyIf(1, Tick(10), Tick(20))", 10)]
    [InlineData("A = Tick(10)\nB = Tick(20)\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, A, B)", 10)]
    public void AUserCallBetweenTheBranchesAndIf_EvaluatesBoth(string source, int expected)
        => Assert.Equal([(Decimal128)10, (Decimal128)20], RunRecordingTicks(source, expected));

    [Theory]
    [InlineData("if(1, (Tick(10), Tick(20))*)")]
    [InlineData("1.if((Tick(10), Tick(20))*)")]
    [InlineData("Branches = Tick(10), Tick(20)\nif(1, Branches*)")]
    public void SpreadConstructsBothBranchValues_ExactlyOnce(string source)
        => Assert.Equal([(Decimal128)10, (Decimal128)20], RunRecordingTicks(source, 10));

    /// <summary>
    /// And with the builtin identity shadowed away entirely, both branches run even
    /// with no wrapper in between: the user callable binds them eagerly like any
    /// other. Same source shape as the first theory above, opposite outcome — which
    /// is exactly the point that laziness follows resolved identity.
    /// </summary>
    [Fact]
    public void AShadowingUserIf_EvaluatesBothBranches()
        => Assert.Equal(
            [(Decimal128)10, (Decimal128)20],
            RunRecordingTicks("if(a, b, c) = b\nif(1, Tick(10), Tick(20))", 10));

    // ── Cross-path parity ───────────────────────────────────────────────────

    /// <summary>
    /// Loop optimizer: the planned <c>if</c> path recognizes the builtin by RESOLVED
    /// identity, so it agrees with the generic path both when <c>if</c> is the
    /// builtin and when a nearer binding has shadowed it into an ordinary user call.
    /// </summary>
    [Theory]
    [InlineData("Step(n, acc) = n - 1, acc + if(n mod 2 == 0, n, 0), n > 1\nStep.while(10, 0):1", 30)]
    [InlineData("Step(n, acc) = n - 1, acc + n.if(1, 0), n > 1\nStep.while(5, 0):1", 4)]
    [InlineData("Step(n, acc) = n - 1, acc + if(n > 3, n, 1)\nStep.repeat(5, 5, 0):1", 12)]
    [InlineData("Args = (1, 10, 20)\nStep(n, acc) = n - 1, acc + if(Args*), n > 1\nStep.while(3, 0):1", 20)]
    // A user `if` in the step body: planning must NOT treat the spelling as the
    // intrinsic conditional. Builtin `if(n, 1, 0)` would add 1 per iteration;
    // the user callable adds n + 1 + 0.
    // (`while` discards the state whose continue condition is false, so only the
    // n = 3 and n = 2 iterations contribute: 4 + 3 = 7, and 30 + 20 = 50.)
    [InlineData("if(a, b, c) = a + b + c\nStep(n, acc) = n - 1, acc + if(n, 1, 0), n > 1\nStep.while(3, 0):1", 7)]
    [InlineData("if(x) = x * 10\nStep(n, acc) = n - 1, acc + if(n), n > 1\nStep.while(3, 0):1", 50)]
    public void OptimizedAndGenericLoops_Agree(string source, int expected)
        => AssertEvalLoopModes(source, expected);

    [Fact]
    public void ALocalUserIf_UsesUserCallFallbackInsideAnOptimizedLoop()
    {
        const string source = "Step(a, b, c) = { if(a, b, c) = a + b + c\n if(a, b, c), b, c }\nrepeat(Step, 2, 1, 10, 20):0";
        AssertEvalLoopModes(source, 61);

        var (result, diagnostics, _) = LoopDiagnosticParityAssertions.RunObserved(source, true);
        Assert.True(result.IsOk);
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.True(diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops > 0);
        var plan = Assert.Single(diagnostics.LoopPlans);
        var output = Assert.Single(plan.Expressions, expression => expression.Role == "output" && expression.Index == 0);
        // Explicit-parameter local calls are not planned. The surrounding loop
        // is optimized, but this call must retain ordinary user-call dispatch.
        Assert.False(output.Planned);
        Assert.Contains("unsupported call: if", output.FallbackReason);
    }

    /// <summary>
    /// Twin routing with completing and yielding caches. Literal-only programs
    /// need not access the cache; deterministic suspension is tested separately.
    /// </summary>
    [Theory]
    [InlineData("if(1, 10, 20)")]
    [InlineData("1.if(10, 20)")]
    [InlineData("Args = (1, 10, 20)\nif(Args*)")]
    [InlineData("Branches = (10, 20)\n1.if(Branches*)")]
    [InlineData("Apply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, 10, 20)")]
    [InlineData("Boom = 1 / 0\nif(1, 10, Boom)")]
    [InlineData("Boom = 1 / 0\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, 10, Boom)")]
    [InlineData("if(1, 2)")]
    [InlineData("1.if(2, 3, 4)")]
    [InlineData("Risky = (10, 1 / 0)\nif(1, Risky*)")]
    [InlineData("if(x) = x + 1\nif(7)")]
    [InlineData("if(x) = x + 1\nif(1, 2, 3)")]
    [InlineData("if(a, b, c) = a + b + c\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, 10, 20)")]
    [InlineData("Apply(if, x) = if(x)\nInc(x) = x + 1\nApply(Inc, 7)")]
    public async Task AsyncTwin_MatchesTheSynchronousOutcome(string source)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        var expected = Evaluator.RunCounted(ast);
        AssertPlainProjection(expected, Evaluator.Run(ast));

        AssertSameOutcome(expected, await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache())));

        AssertSameOutcome(expected, await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, new SuspendingAsyncZeroArgPropertyResultCache())));
        AssertPlainProjection(expected, await AsyncEvaluationHarness.Complete(
            Evaluator.RunAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache())));
    }

    private static void AssertPlainProjection(
        EvalResult<Evaluator.CountedResult> expected, EvalResult<Result> actual)
    {
        Assert.Equal(expected.IsError, actual.IsError);
        if (expected.IsError)
            Assert.Equal(
                LoopDiagnosticParityAssertions.DescribeErrorTree(expected.Error),
                LoopDiagnosticParityAssertions.DescribeErrorTree(actual.Error));
        else
            Assert.True(Result.ValueComparer.Equals(expected.Value.Value, actual.Value));
    }

    private static void AssertSameOutcome(
        EvalResult<Evaluator.CountedResult> expected, EvalResult<Evaluator.CountedResult> actual)
    {
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(expected), AsyncEvaluationHarness.NeutralOf(actual));
        if (expected.IsError)
            Assert.Equal(
                LoopDiagnosticParityAssertions.DescribeErrorTree(expected.Error),
                LoopDiagnosticParityAssertions.DescribeErrorTree(actual.Error));
    }

    /// <summary>
    /// Hold the first host callback on an incomplete task, then resume it. Trace
    /// assertions prove condition-before-branch order, non-execution of unselected
    /// expressions, eager spread construction, and no callback replay. Failures
    /// compare complete structured payloads and spans with the synchronous oracle.
    /// </summary>
    [Theory]
    [InlineData("if(Tick(1), Tick(10), Tick(20))", "ok raw=10 n=1", 1, 10)]
    [InlineData("if(Tick(0), Tick(10), Tick(20))", "ok raw=20 n=1", 0, 20)]
    [InlineData("Tick(1).if(Tick(10), Tick(20))", "ok raw=10 n=1", 1, 10)]
    [InlineData("Tick(0).if(Tick(10), Tick(20))", "ok raw=20 n=1", 0, 20)]
    [InlineData("Apply(f) = f(Tick(1), Tick(10), Tick(20))\nApply(if)", "ok raw=10 n=1", 1, 10)]
    [InlineData("Apply(if) = Tick(0).if(Tick(10), Tick(20))\nApply(if)", "ok raw=20 n=1", 0, 20)]
    [InlineData("if(a, b, c) = a + b + c\nif(Tick(1), Tick(10), Tick(20))", "ok raw=31 n=1", 1, 10, 20)]
    [InlineData("if((Tick(1), Tick(10), Tick(20))*)", "ok raw=10 n=1", 1, 10, 20)]
    [InlineData("Branches = Tick(10), Tick(20)\n0.if(Branches*)", "ok raw=20 n=1", 10, 20)]
    [InlineData("Apply(f, *args) = f(args*)\nApply(if, Tick(1), Tick(10), Tick(20))", "ok raw=10 n=1", 1, 10, 20)]
    [InlineData("if(Tick(1), 1 / 0, 20)", "err div0", 1)]
    [InlineData("Tick(0).if(10, 1 / 0)", "err div0", 0)]
    [InlineData("if((Tick(1), 2)*)", "err arity", 1)]
    [InlineData("1.if((Tick(2), 3, 4)*)", "err arity", 2)]
    [InlineData("Apply(f, *args) = f(args*)\nApply(if, Tick(1), 2)", "err arity", 1)]
    [InlineData("if(x) = x + 1\nif((Tick(1), 2, 3)*)", "err arity", 1)]
    [InlineData("Risky = Tick(10), 1 / 0\nif(1, Risky*)", "err div0", 10)]
    public async Task SuspendedInvocation_PreservesIdentityEffectsAndDiagnostics(
        string source, string expectedOutcome, params int[] expectedTicks)
    {
        var syncTicks = new List<Decimal128>();
        var syncOperations = HostOperations.Create(HostOperation.Create("Tick", (args, _) =>
        {
            syncTicks.Add(Assert.IsType<Result.Atom>(args[0]).Value);
            return args[0];
        }, "value"));
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = syncOperations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        var ast = new Expr.AlgorithmExpr(parsed.Root);
        var expected = Evaluator.RunCounted(ast, new RunScopedZeroArgPropertyResultCache(), hostOperations: syncOperations);
        Assert.Equal(expectedOutcome, AsyncEvaluationHarness.NeutralOf(expected));
        Assert.Equal(expectedTicks.Select(value => (Decimal128)value), syncTicks);

        var ticks = new List<Decimal128>();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var asyncOperations = HostOperations.Create(HostOperation.CreateAsync("Tick", async (args, _) =>
        {
            ticks.Add(Assert.IsType<Result.Atom>(args[0]).Value);
            if (ticks.Count == 1)
            {
                reached.SetResult();
                await release.Task;
            }
            return args[0];
        }, "value"));
        var pending = Evaluator.RunCountedAsync(
            ast, new PassThroughAsyncZeroArgPropertyResultCache(), hostOperations: asyncOperations).AsTask();
        try
        {
            await reached.Task.WaitAsync(TimeSpan.FromSeconds(45));
            Assert.False(pending.IsCompleted);
            Assert.Equal([(Decimal128)expectedTicks[0]], ticks);
        }
        finally
        {
            release.TrySetResult();
        }
        var actual = await pending.WaitAsync(TimeSpan.FromSeconds(45));
        AssertSameOutcome(expected, actual);
        Assert.Equal(expectedTicks.Select(value => (Decimal128)value), ticks);
    }

    /// <summary>
    /// Counted/plain parity: the plain result is the counted result's value
    /// projection on every composition surface, including <c>if</c>'s own
    /// value-boundary re-counting of the selected branch.
    /// </summary>
    [Theory]
    [InlineData("X = 1, 2, 3\nif(1, X, X)", 1)]
    [InlineData("X = 1, 2, 3\n1.if(X, X)", 1)]
    [InlineData("X = 1, 2, 3\nif(1, X, X)*", 3)]
    [InlineData("X = 1, 2, 3\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, 1, X, X)", 1)]
    [InlineData("if(x) = x\nX = 1, 2, 3\nif(X)", 1)]
    public void CountedAndPlain_Agree(string source, int expectedEmittedCount)
    {
        var ast = new Expr.AlgorithmExpr(ParseValidRoot(source));
        var counted = Evaluator.RunCounted(ast);
        var plain = Evaluator.Run(ast);

        Assert.False(counted.IsError);
        Assert.False(plain.IsError);
        Assert.Equal(expectedEmittedCount, counted.Value.EmittedCount);
        Assert.True(Result.ValueComparer.Equals(counted.Value.Value, plain.Value));
    }

    // ── I. The rule is general, not an `if` exception ───────────────────────

    /// <summary>
    /// SYN-05 changes nothing about the other builtins: they were already ordinary
    /// prelude bindings, and they stay ordinary prelude bindings. This guards the
    /// opposite regression — that fixing <c>if</c> accidentally privileged some
    /// other spelling, or that a general "builtins are unshadowable" rule crept in.
    /// </summary>
    [Theory]
    [InlineData("count(x) = x + 1\ncount(7)", 8)]
    [InlineData("sum(x) = x + 100\nsum(5)", 105)]
    [InlineData("range = 7\nrange", 7)]
    [InlineData("map = 7\nmap", 7)]
    [InlineData("first(a, b) = b\nfirst(1, 2)", 2)]
    [InlineData("Apply(map, x) = map(x)\nInc(x) = x + 1\nApply(Inc, 7)", 8)]
    public void OtherBuiltins_StayOrdinaryShadowablePreludeBindings(string source, int expected)
        => AssertEval(source, expected);

    // ── Editor surface ──────────────────────────────────────────────────────

    /// <summary>
    /// The semantic model sees a shadowing user <c>if</c> as the ordinary property it
    /// is: the call site is a property reference resolving to the local declaration,
    /// and the name appears once in the visible-symbol view (the shadowed prelude
    /// member does not also show up). The semantic model has never had
    /// <c>if</c>-specific code — this pins that it stays that way, and that removing
    /// the parser gate did not leave editors reporting a phantom error on a call the
    /// program resolves perfectly well.
    /// </summary>
    [Fact]
    public void SemanticModel_TreatsAShadowingUserIf_AsAnOrdinaryProperty()
    {
        const string source = "if(x) = x + 1\nif(7)";
        var parsed = SourceProvenance.ParseValid(source);
        var model = SemanticModelBuilder.Build(parsed.Parsed);

        var declaration = model.FindPropertyAt(1, 1);
        Assert.Equal("if", declaration!.Name);
        Assert.Equal("if(x)", declaration.DisplaySignature);

        var reference = model.FindResolutionAt(2, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, reference!.Classification);
        Assert.Equal(declaration.Declaration!.Span, reference.ResolvedDeclaration!.Span);

        var visible = Assert.Single(model.GetVisibleSymbolsAt(2, 1), symbol => symbol.Name == "if");
        Assert.Equal(declaration.Declaration!.Span, visible.Declaration!.Span);
    }

    /// <summary>
    /// With nothing shadowing it, the same call site classifies against the prelude
    /// member instead — a real symbol with no document declaration to point at.
    /// </summary>
    [Fact]
    public void SemanticModel_ResolvesAnUnshadowedIf_ToThePreludeMember()
    {
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid("if(1, 10, 20)").Parsed);

        var reference = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(1, 1));
        Assert.Equal(IdentifierClassification.Builtin, reference.Classification);
        Assert.Null(reference.ResolvedDeclaration);
        var property = Assert.IsType<PropertyInfo>(model.FindPropertyAt(1, 1));
        Assert.Equal("if(condition, whenTrue, whenFalse)", property.DisplaySignature);
        var visible = Assert.Single(model.GetVisibleSymbolsAt(1, 1), symbol => symbol.Name == "if");
        Assert.Null(visible.Declaration);
    }

    [Fact]
    public void SemanticModel_ResolvesAParameterNamedIf_ToItsOwner()
    {
        const string source = "Apply(if, x) = {\n Inner = if(x)\n Inner\n}\nInc(x) = x + 1\nApply(Inc, 7)";
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        var reference = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(2, 10));
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, reference.Classification);
        Assert.Equal(new SourceSpan(1, 7, 1, 8), reference.ResolvedDeclaration!.Span);
        var visible = Assert.Single(model.GetVisibleSymbolsAt(2, 10), symbol => symbol.Name == "if");
        Assert.Equal(reference.ResolvedDeclaration, visible.Declaration);
    }

    [Fact]
    public void OtherBuiltins_HaveNoArityFallbackEither()
    {
        AssertEval("count((1, 2, 3))", 3);

        var arity = AssertEvalFailsWithArityMismatch(
            "count(x) = x + 1\ncount(1, 2)", expected: 1, actual: 2);
        Assert.Equal("count", arity.Signature?.Name);
        Assert.Equal(
            "Callable `count(x)` expects 1 argument, but was called with 2 arguments.",
            KatLangError.FromEvalError(arity).Message);
    }
}
