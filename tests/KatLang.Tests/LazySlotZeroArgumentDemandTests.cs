using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// F9 — a builtin VALUE slot demands its algorithm with zero explicit arguments
/// through the ONE zero-argument value-demand law
/// (<c>Evaluator.ZeroArgumentValueDemandError</c>, Lean <c>zeroArgumentDemandError?</c>):
/// the same rejection a bare property reference, an algorithm-channel parameter,
/// or a written block reports in value position.
///
/// <para>Before the fix the lazy slots (<c>if</c> condition and branches,
/// <c>while</c>/<c>repeat</c> initial state, the <c>repeat</c> count, <c>atoms</c>,
/// <c>range</c>, the <c>.string</c> receiver) evaluated a resolved parameterized
/// algorithm's body directly, so <c>if(1, Inc, 0)</c> with <c>Inc(x) = x + 1</c>
/// reported <c>Unknown name: x</c> from inside <c>Inc</c> — and a body that never
/// read its parameter (<c>K(x) = 5</c>) silently ran. The rule closes that back
/// door: the decision is the effective signature's, made at the demand boundary
/// before any body is entered, and only for the slot the builtin selects.</para>
/// </summary>
public class LazySlotZeroArgumentDemandTests
{
    private const string Inc = "Inc(x) = x + 1\n";

    private static EvalError FailingError(string source)
    {
        var result = EvaluatorTestSupport.EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");
        return result.Error;
    }

    private static Result SuccessfulValue(string source)
    {
        var result = EvaluatorTestSupport.EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {KatLangError.FromEvalError(result.Error).Message}");
        return result.Value;
    }

    private static void AssertEvaluatesTo(Result expected, string source)
    {
        var actual = SuccessfulValue(source);
        Assert.True(Result.ValueComparer.Equals(expected, actual), $"Expected {expected} but got {actual} for:\n{source}");
    }

    private static Result List(params Result[] items) => new Result.ListValue(items);

    /// <summary>
    /// The rejection of a selected slot naming a parameterized PROPERTY: the ordinary
    /// property-context arity mismatch (no call signature — this is a demand, not a
    /// call), rendered as the canonical property message at the reference's span,
    /// and never the body's unresolved parameter.
    /// </summary>
    private static EvalError.ArityMismatch AssertPropertyZeroArgumentDemand(
        string source,
        string propertyName,
        int expectedParameters,
        int line,
        int column)
    {
        var error = FailingError(source);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(expectedParameters, arity.Expected);
        Assert.Equal(0, arity.Actual);
        Assert.Null(arity.Signature);
        Assert.Contains($"while evaluating property {propertyName}", ContextChain(error));

        var rendered = KatLangError.FromEvalError(error);
        Assert.Equal(KatLangErrorCode.ArityMismatch, rendered.Code);
        Assert.Contains($"Property '{propertyName}' expects {expectedParameters} parameter", rendered.Message);
        Assert.Contains("was called with 0 arguments", rendered.Message);
        Assert.DoesNotContain("Unknown name", rendered.Message);
        Assert.Equal(line, rendered.StartLine);
        Assert.Equal(column, rendered.StartColumn);
        return arity;
    }

    // ── 1. The selected branch is an ordinary zero-argument value demand ──────

    [Theory]
    [InlineData("if(1, Inc, 0)", 7)]
    [InlineData("if(0, 0, Inc)", 10)]
    [InlineData("if(Inc, 1, 0)", 4)]
    public void SelectedIfSlot_ParameterizedProperty_IsTheOrdinaryZeroArgumentArityError(string row, int column)
        => AssertPropertyZeroArgumentDemand(Inc + row, "Inc", expectedParameters: 1, line: 2, column: column);

    [Fact]
    public void SelectedIfSlot_ReportsExactlyWhatTheBarePropertyReferenceReports()
    {
        // The demand law is ONE law: the lazy slot's innermost error and message
        // are those of `Inc` written as an output row (only the enclosing call
        // context differs).
        var bare = FailingError(Inc + "Inc");
        var slot = FailingError(Inc + "if(1, Inc, 0)");

        Assert.Equal(DescribeErrorTree(Innermost(bare)), DescribeErrorTree(Innermost(slot)));
        Assert.Equal(
            KatLangError.FromEvalError(bare).Message,
            KatLangError.FromEvalError(slot).Message.Replace("while evaluating call to if: ", string.Empty));
        Assert.Equal(["while evaluating property Inc"], ContextChain(bare));
        Assert.Equal(["while evaluating call to if", "while evaluating property Inc"], ContextChain(slot));
    }

    // ── 2. The unselected branch stays lazy ──────────────────────────────────

    [Theory]
    [InlineData("if(0, Inc, 7)")]
    [InlineData("if(1, 7, Inc)")]
    public void UnselectedIfSlot_ParameterizedProperty_IsNeverDemanded(string row)
        => AssertEvaluatesTo(new Result.Atom(7), Inc + row);

    [Fact]
    public void UnselectedIfSlot_CostsExactlyWhatALiteralSlotCosts()
    {
        // Not merely "no error": the unselected parameterized slot is never even
        // evaluated — the run's operational counters
        // equal those of the same program with a literal in that slot.
        var (parameterized, parameterizedBudget) = Evaluator.RunCountedObserved(
            Program(Inc + "if(0, Inc, 7)"), enableOptimizations: false);
        var (literal, literalBudget) = Evaluator.RunCountedObserved(
            Program(Inc + "if(0, 5, 7)"), enableOptimizations: false);

        Assert.False(parameterized.IsError);
        Assert.False(literal.IsError);
        Assert.True(Result.ValueComparer.Equals(new Result.Atom(7), parameterized.Value.Value));
        Assert.Equal(literalBudget.ConsumedSteps, parameterizedBudget.ConsumedSteps);
        Assert.Equal(literalBudget.PeakDepth, parameterizedBudget.PeakDepth);
    }

    // ── 3. Zero-parameter algorithms remain valid lazy values ───────────────

    [Fact]
    public void ZeroParameterProperty_IsAnOrdinaryLazyValue()
        => AssertEvaluatesTo(new Result.Atom(7), "A = 7\nif(1, A, 0)");

    [Fact]
    public void ZeroParameterPropertyCapturingAnEnclosingBinding_IsNotMistakenForAMissingArgument()
    {
        // `Inner` reads Outer's parameter `v` by lexical capture; it declares no
        // parameter of its own, so it is a value in the selected slot.
        var source = """
            Outer(v) = { Inner = v + 1
             if(1, Inner, 0) }
            Outer(7)
            """;
        AssertEvaluatesTo(new Result.Atom(8), source);
    }

    [Fact]
    public void ExplicitCallsInASlot_AreValues()
    {
        AssertEvaluatesTo(new Result.Atom(5), Inc + "if(1, Inc(4), 0)");
        AssertEvaluatesTo(List(), "Collect(*xs) = xs\nif(1, Collect(), 0)");
    }

    // ── 4. A body failure of a zero-parameter algorithm stays a body failure ─

    [Fact]
    public void ZeroParameterBodyFailure_IsStillTheBodyFailure()
    {
        Assert.IsType<EvalError.DivByZero>(Innermost(FailingError("Boom = 1 / 0\nif(1, Boom, 0)")));
        Assert.IsType<EvalError.MissingOutput>(Innermost(FailingError("Empty = { P = 1 }\nif(1, Empty, 0)")));
    }

    [Fact]
    public void InferredImplicitParameter_IsAnUnsatisfiedParameter_ReportedWithItsProvenance()
    {
        // `A = Missing + 1` does not have a zero-parameter body with an unknown
        // name: KatLang infers `Missing` as A's implicit parameter, so the slot's
        // demand is a genuine zero-argument arity failure. The report carries the
        // provenance note pointing at the unresolved identifier, exactly as the
        // bare reference `A` does — never `Unknown name: Missing` from inside A.
        var arity = AssertPropertyZeroArgumentDemand(
            "A = Missing + 1\nif(1, A, 0)", "A", expectedParameters: 1, line: 2, column: 7);
        var provenance = Assert.Single(arity.InferredImplicitParameters!);
        Assert.Equal("Missing", provenance.Name);
        Assert.NotNull(provenance.Span);

        var rendered = KatLangError.FromEvalError(FailingError("A = Missing + 1\nif(1, A, 0)"));
        Assert.Contains("An implicit parameter 'Missing' was inferred at [1:5].", rendered.Message);
    }

    // ── 5. Explicit parameterized calls are unchanged ─────────────────────────

    [Fact]
    public void ExplicitParameterizedCall_IsUnchanged()
        => AssertEvaluatesTo(new Result.Atom(5), Inc + "Inc(4)");

    [Fact]
    public void ExplicitZeroArgumentCall_IsTheOrdinaryCallArityError_NotTheDemandRejection()
    {
        // `Inc()` is a CALL with zero arguments: its arity error carries the callee
        // signature and renders through the callable message — a different
        // operation from demanding `Inc` as a value.
        var error = FailingError(Inc + "if(1, Inc(), 0)");
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal("Inc", arity.Signature?.Name);
        Assert.DoesNotContain("while evaluating property Inc", ContextChain(error));
        Assert.Contains("Callable `Inc(x)` expects 1 argument", KatLangError.FromEvalError(error).Message);
    }

    [Fact]
    public void BuiltinInAValueSlot_KeepsItsOwnSignatureArityError()
    {
        // A builtin algorithm declares no parameters of its own, so the demand law
        // passes it through to its established value-position rejection.
        var error = FailingError("if(1, count, 0)");
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal("count", arity.Signature?.Name);
    }

    // ── 6. Every builtin value slot — and the .string receiver ──────────────

    [Theory]
    [InlineData("Step(s) = s + 1\nrepeat(Step, 1, Inc)", 3, 17)]
    [InlineData("Step(s) = s + 1\nrepeat(Step, Inc, 0)", 3, 14)]
    [InlineData("Down(s) = s - 1, s\nwhile(Down, Inc)", 3, 13)]
    [InlineData("atoms(Inc)", 2, 7)]
    [InlineData("range(1, Inc)", 2, 10)]
    [InlineData("Inc.string", 2, 1)]
    public void EveryBuiltinValueSlot_AppliesTheZeroArgumentDemandLaw(string rows, int line, int column)
        => AssertPropertyZeroArgumentDemand(Inc + rows, "Inc", expectedParameters: 1, line: line, column: column);

    [Theory]
    [InlineData("count(K)", 7)]
    [InlineData("contains([1], K)", 15)]
    [InlineData("take([1], K)", 11)]
    [InlineData("skip([1], K)", 11)]
    public void CollectionValuePositions_KeepTheDemandSignatureAndSource(string row, int column)
        => AssertPropertyZeroArgumentDemand("K(x) = 5\n" + row, "K", 1, 2, column);

    [Theory]
    [InlineData("count(F)", 7)]
    [InlineData("contains([1], F)", 15)]
    [InlineData("Add(e, a) = e + a\nreduce([], Add, F)", 17)]
    public void CollectionValuePositions_NameTheDemandedConditionalFamily(string rows, int column)
    {
        var error = FailingError("F(0) = 10\nF(x) = x + 1\n" + rows);
        Assert.Equal("F", Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error)).AlgorithmName);
        var rendered = KatLangError.FromEvalError(error);
        Assert.Equal(rows.Contains('\n') ? 4 : 3, rendered.StartLine);
        Assert.Equal(column, rendered.StartColumn);
    }

    [Fact]
    public void EveryBuiltinValueSlot_ZeroParameterControlsEvaluate()
    {
        AssertEvaluatesTo(new Result.Atom(1), "A = 0\nStep(s) = s + 1\nrepeat(Step, 1, A)");
        AssertEvaluatesTo(new Result.Atom(2), "A = 2\nStep(s) = s + 1\nrepeat(Step, A, 0)");
        AssertEvaluatesTo(new Result.Atom(0), "A = 3\nDown(s) = s - 1, s\nwhile(Down, A)");
        AssertEvaluatesTo(List(new Result.Atom(7)), "A = 7\natoms(A)");
        AssertEvaluatesTo(List(new Result.Atom(1), new Result.Atom(2), new Result.Atom(3)), "A = 3\nrange(1, A)");
        AssertEvaluatesTo(new Result.Str("7"), "A = 7\nA.string");
        AssertEvaluatesTo(new Result.Str("3"), "Lib = { Sub = 3 }\nLib.Sub.string");
        AssertEvaluatesTo(new Result.Str("5"), Inc + "Inc(4).string");
    }

    [Fact]
    public void CallbackSlots_SupplyArguments_AndNeverConsultTheLaw()
    {
        AssertEvaluatesTo(new Result.Atom(2), Inc + "repeat(Inc, 2, 0)");
        AssertEvaluatesTo(new Result.Atom(0), "Down(s) = s - 1, s\nwhile(Down, 3)");
        AssertEvaluatesTo(List(new Result.Atom(2), new Result.Atom(3)), Inc + "map([1, 2], Inc)");
        AssertEvaluatesTo(List(new Result.Atom(2), new Result.Atom(3)), "IsBig(n) = n > 1\nfilter([1, 2, 3], IsBig)");
        AssertEvaluatesTo(new Result.Atom(3), "Add(e, a) = e + a\nreduce([1, 2], Add, 0)");
        AssertEvaluatesTo(new Result.SequenceValue([new Result.Atom(2), new Result.Atom(14)]),
            "Step(a, b) = a + 1, b + 2\nrepeat(Step, 2, 0, 10)");
        AssertEvaluatesTo(List(List(new Result.Atom(1)), List(new Result.Atom(2))),
            "Collect(*xs) = xs\nmap([1, 2], Collect)");
        AssertEvaluatesTo(List(new Result.Atom(10), new Result.Atom(2)),
            "F(0) = 10\nF(x) = x + 1\nmap([0, 1], F)");
    }

    [Theory]
    [InlineData("Boom.string")]
    [InlineData("count(Boom)")]
    [InlineData("contains([1], Boom)")]
    [InlineData("take([1], Boom)")]
    [InlineData("reduce([], Add, Boom)")]
    [InlineData("reduce([1], BadStep, 0)")]
    public void ValidValueDemand_PreservesTheBodyFailure(string row)
    {
        const string definitions = "Boom = 1 / 0\nAdd(e, a) = e + a\nBadStep(e, a) = 1 / 0\n";
        var error = FailingError(definitions + row);
        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.DoesNotContain("initial accumulator", KatLangError.FromEvalError(error).Message);
    }

    [Theory]
    [InlineData("if(1, K, 0)")]
    [InlineData("if(0, 0, K)")]
    [InlineData("if(K, 1, 0)")]
    [InlineData("repeat(Step, 1, K)")]
    [InlineData("repeat(Step, K, 0)")]
    [InlineData("while(Step, K)")]
    [InlineData("reduce([], Add, K)")]
    [InlineData("K.string")]
    [InlineData("atoms(K)")]
    [InlineData("range(K, 3)")]
    [InlineData("count(K)")]
    [InlineData("contains([1], K)")]
    [InlineData("take([1], K)")]
    public async Task RejectedDemand_NeverEntersTheBody_EvenAfterGenuineSuspension(string row)
    {
        var touches = 0;
        var touch = HostOperation.Create("Touch", (_, _) => new Result.Atom(++touches));
        var syncOperations = HostOperations.Create(touch,
            HostOperation.Create("Gate", (_, _) => new Result.Atom(1)));
        var source = "K(x) = Touch()\nStep(s) = s\nAdd(e, a) = e + a\nGate()\n" + row;
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = syncOperations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var ast = new Expr.AlgorithmExpr(parsed.Root);

        var (sync, syncBudget) = Evaluator.RunCountedObserved(ast,
            enableOptimizations: false, hostOperations: syncOperations);
        Assert.True(sync.IsError);
        Assert.Equal(KatLangErrorCode.ArityMismatch, KatLangError.FromEvalError(sync.Error).Code);
        Assert.Equal(0, touches);

        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var gateCalls = 0;
        var asyncOperations = HostOperations.Create(touch, HostOperation.CreateAsync("Gate", (_, _) =>
        {
            gateCalls++;
            return new ValueTask<Result>(gate.Task);
        }));
        var pending = Evaluator.RunCountedObservedAsync(ast, hostOperations: asyncOperations);
        Assert.Equal(1, gateCalls);
        Assert.False(pending.IsCompleted);
        Assert.Equal(0, touches);
        gate.SetResult(new Result.Atom(1));
        var (resumed, resumedBudget) = await AsyncEvaluationHarness.Complete(pending);
        Assert.True(resumed.IsError);
        Assert.Equal(DescribeErrorTree(sync.Error), DescribeErrorTree(resumed.Error));
        Assert.Equal(syncBudget.ConsumedSteps, resumedBudget.ConsumedSteps);
        Assert.Equal(syncBudget.PeakDepth, resumedBudget.PeakDepth);
        Assert.Equal(syncBudget.MaterializedItems, resumedBudget.MaterializedItems);
        Assert.Equal(syncBudget.MaterializedStringChars, resumedBudget.MaterializedStringChars);
        Assert.Equal(0, resumedBudget.CurrentDepth);
        Assert.Equal(1, gateCalls);
        Assert.Equal(0, touches);
    }

    [Theory]
    [InlineData("Inc(x) = x + 1")]
    [InlineData("Inc(x) = 5")]
    [InlineData("Inc(x) = 1 / 0")]
    public void ReduceInitialAccumulator_KeepsItsDedicatedHint_DecidedFromTheSignature(string definition)
    {
        // reduce's initial slot already had a dedicated diagnostic; what changes is
        // that it is decided from the signature at the boundary. A body that never
        // reads its parameter used to run (and yield 8), and a body failing for
        // another reason used to leak that failure instead — neither body is
        // entered now.
        var error = FailingError(definition + "\nAdd(e, a) = e + a\nreduce([1, 2], Add, Inc)");
        Assert.IsType<EvalError.BadArity>(Innermost(error));

        var rendered = KatLangError.FromEvalError(error);
        Assert.Equal(KatLangErrorCode.ArityMismatch, rendered.Code);
        Assert.Contains("the last argument must be an initial accumulator value", rendered.Message);
        Assert.Contains("still needs 'x'", rendered.Message);
        Assert.DoesNotContain("Division by zero", rendered.Message);
        Assert.DoesNotContain("Unknown name", rendered.Message);
    }

    // ── 7. Effective signatures ─────────────────────────────────────────────

    [Fact]
    public void ABodyThatNeverReadsItsParameter_IsStillRejected()
    {
        // The decision is the signature's: before the fix `K`'s body ran and the
        // program produced 5.
        AssertPropertyZeroArgumentDemand("K(x) = 5\nif(1, K, 0)", "K", expectedParameters: 1, line: 2, column: 7);
    }

    [Fact]
    public void InferredParameter_CountsLikeAnExplicitOne()
    {
        var arity = AssertPropertyZeroArgumentDemand("A = q + 1\nif(1, A, 0)", "A", expectedParameters: 1, line: 2, column: 7);
        Assert.Equal("q", Assert.Single(arity.InferredImplicitParameters!).Name);
    }

    [Fact]
    public void LiftedParameter_CountsLikeAnExplicitOne()
    {
        // `Use = Need` lifts Need's implicit `v` into Use's signature, so Use is
        // parameterized even though it declares nothing itself.
        AssertPropertyZeroArgumentDemand("Need = v\nUse = Need\nif(1, Use, 0)", "Use", expectedParameters: 1, line: 3, column: 7);
    }

    [Fact]
    public void CollectingParameter_CountsLikeAnExplicitOne()
        => AssertPropertyZeroArgumentDemand("Collect(*xs) = xs\nif(1, Collect, 0)", "Collect", expectedParameters: 1, line: 2, column: 7);

    [Fact]
    public void TwoParameters_ReportBothExpected()
        => AssertPropertyZeroArgumentDemand("Add(a, b) = a + b\nif(1, Add, 0)", "Add", expectedParameters: 2, line: 2, column: 7);

    [Fact]
    public void ClauseFamily_CannotBeAccessedAsAValue()
    {
        // A conditional cannot select a branch without arguments: the demand law's
        // conditional rule names the family (never the generic "conditional").
        var error = FailingError("F(0) = 10\nF(x) = x + 1\nif(1, F, 0)");
        var branch = Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error));
        Assert.Equal("F", branch.AlgorithmName);
    }

    [Fact]
    public void AlgorithmChannelParameterInASlot_IsTheParameterArmsBareRejection()
    {
        // `Apply(Inc)` binds `g` only on the algorithm channel; demanding it in the
        // slot is the same bare arity mismatch as reading `g` in value position —
        // no property context, and never the callee's own `x`. The span is the
        // `g` reference inside `if(1, g, 0)`.
        var error = FailingError(Inc + "Apply(g) = if(1, g, 0)\nApply(Inc)");
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(1, arity.Expected);
        Assert.Equal(0, arity.Actual);
        Assert.Equal(["while evaluating call to Apply", "while evaluating call to if"], ContextChain(error));

        var rendered = KatLangError.FromEvalError(error);
        Assert.Contains("Expected 1 parameter, but was called with 0 arguments.", rendered.Message);
        Assert.DoesNotContain("Unknown name", rendered.Message);
        Assert.Equal(2, rendered.StartLine);
        Assert.Equal(18, rendered.StartColumn);
    }

    [Fact]
    public void WrittenBlockWithAnImplicitParameter_ReportsUnresolvedImplicitParams()
    {
        // A brace block in the slot is judged like a block in value position: its
        // inferred `x` cannot be supplied by anyone, so the report is the
        // unresolved-implicit-parameters diagnostic, not `Unknown name: x`.
        var error = FailingError("if(1, {x + 1}, 0)");
        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(error));
        Assert.Equal(["x"], unresolved.ParamNames);
        Assert.DoesNotContain("Unknown name", KatLangError.FromEvalError(error).Message);
    }

    [Fact]
    public void DotStringReceiverShapes_FollowTheSameLaw()
    {
        // An algorithm-channel parameter receiver: the bare rejection.
        var parameter = FailingError(Inc + "F(g) = g.string\nF(Inc)");
        Assert.Equal(1, Assert.IsType<EvalError.ArityMismatch>(Innermost(parameter)).Expected);
        Assert.DoesNotContain("Unknown name", KatLangError.FromEvalError(parameter).Message);

        // A navigated structural member: the bare rejection, at the receiver.
        var navigated = FailingError("Lib = { Sub(x) = x }\nLib.Sub.string");
        Assert.Equal(1, Assert.IsType<EvalError.ArityMismatch>(Innermost(navigated)).Expected);
        var rendered = KatLangError.FromEvalError(navigated);
        Assert.DoesNotContain("Unknown name", rendered.Message);
        Assert.Equal(2, rendered.StartLine);
        Assert.Equal(1, rendered.StartColumn);
    }

    // ── 8. Execution parity: plain, counted, forced async, suspending async, planned loops

    public static TheoryData<string> ParityMatrix() =>
        new()
        {
            Inc + "if(1, Inc, 0)",
            Inc + "if(0, 0, Inc)",
            Inc + "if(0, Inc, 7)",
            Inc + "if(Inc, 1, 0)",
            "A = 7\nif(1, A, 0)",
            "K(x) = 5\nif(1, K, 0)",
            "A = q + 1\nif(1, A, 0)",
            "Collect(*xs) = xs\nif(1, Collect, 0)",
            "Collect(*xs) = xs\nif(1, Collect(), 0)",
            "F(0) = 10\nF(x) = x + 1\nif(1, F, 0)",
            Inc + "Apply(g) = if(1, g, 0)\nApply(Inc)",
            "if(1, {x + 1}, 0)",
            Inc + "Step(s) = s + 1\nrepeat(Step, 1, Inc)",
            Inc + "Step(s) = s + 1\nrepeat(Step, Inc, 0)",
            Inc + "Down(s) = s - 1, s\nwhile(Down, Inc)",
            Inc + "atoms(Inc)",
            Inc + "range(1, Inc)",
            Inc + "Inc.string",
            Inc + "F(g) = g.string\nF(Inc)",
            "Lib = { Sub(x) = x }\nLib.Sub.string",
            "K(x) = 5\nAdd(e, a) = e + a\nreduce([1, 2], Add, K)",
            "K(x) = 5\ncount(K)",
            "K(x) = 5\ncontains([1], K)",
            "K(x) = 5\ntake([1], K)",
            "K(x) = 5\nskip([1], K)",
            "F(0) = 10\nF(x) = x + 1\ncount(F)",
            "F(0) = 10\nF(x) = x + 1\nAdd(e, a) = e + a\nreduce([], Add, F)",
            Inc + "repeat(Inc, 2, 0)",
            Inc + "map([1, 2], Inc)",
            "Outer(v) = { Inner = v + 1\n if(1, Inner, 0) }\nOuter(7)",
        };

    [Theory]
    [MemberData(nameof(ParityMatrix))]
    public async Task PlainCountedAndAsyncPaths_AgreeOnOutcomeAndCounters(string source)
    {
        var ast = Program(source);

        // Plain versus counted: the same value (or the same structured error tree).
        var plain = Evaluator.Run(ast);
        var (counted, countedBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        Assert.Equal(plain.IsError, counted.IsError);
        if (plain.IsOk)
            Assert.True(Result.ValueComparer.Equals(plain.Value, counted.Value.Value));
        else
            Assert.Equal(DescribeErrorTree(plain.Error), DescribeErrorTree(counted.Error));

        // Forced async twin path, completing synchronously: same outcome, same counters.
        var passThrough = new PassThroughAsyncZeroArgPropertyResultCache();
        var (forced, forcedBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: passThrough));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(counted), AsyncEvaluationHarness.NeutralOf(forced));
        Assert.Equal(countedBudget.ConsumedSteps, forcedBudget.ConsumedSteps);
        Assert.Equal(countedBudget.PeakDepth, forcedBudget.PeakDepth);
        Assert.Equal(0, passThrough.SyncAccesses);
        if (counted.IsError)
            Assert.Equal(DescribeErrorTree(counted.Error), DescribeErrorTree(forced.Error));

        // Suspend at every property access that occurs. Cases with no cache access
        // complete synchronously; the gated host test above independently proves
        // actual suspension before rejected demands.
        var suspending = new SuspendingAsyncZeroArgPropertyResultCache();
        var (suspended, suspendedBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: suspending));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(counted), AsyncEvaluationHarness.NeutralOf(suspended));
        Assert.Equal(countedBudget.ConsumedSteps, suspendedBudget.ConsumedSteps);
        Assert.Equal(countedBudget.PeakDepth, suspendedBudget.PeakDepth);
        Assert.Equal(0, suspending.SyncAccesses);
    }

    [Fact]
    public void PlannedLoop_ParameterizedPropertyInAnIfSlot_FallsBackTransparently()
    {
        // The loop planner never plans a parameterized local property as an `if`
        // argument: the step output falls back to the generic evaluator inside the
        // optimized loop, so the optimized and generic strategies must report the
        // identical structured rejection.
        var source = """
            Step(s) = { Inc(x) = x + 1
             if(s < 3, Inc, 0) }
            repeat(Step, 2, 0)
            """;

        var error = AssertOptimizerTransparentFailure(source);
        Assert.Equal(1, Assert.IsType<EvalError.ArityMismatch>(Innermost(error)).Expected);
        Assert.Equal(
            ["while evaluating call to repeat", "while evaluating call to if", "while evaluating property Inc"],
            ContextChain(error));

        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == "Step.repeat");
        var output = Assert.Single(plan.Expressions, expression => expression.Role == "output" && expression.Index == 0);
        Assert.False(output.Planned, "a parameterized local property in an `if` slot must never be planned");
    }

    [Fact]
    public void PlannedLoop_AlgorithmChannelParameterInAnIfSlot_FallsBackTransparently()
    {
        var source = """
            Inc(x) = x + 1
            Run(g) = repeat({if(s < 1, g, 0)}, 1, 0)
            Run(Inc)
            """;

        var error = AssertOptimizerTransparentFailure(source);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(1, arity.Expected);
        Assert.Equal(0, arity.Actual);
    }

    [Fact]
    public void PlannedLoop_ZeroParameterPropertyInAnIfSlot_IsPlannedAndAgreesWithGeneric()
    {
        var source = """
            Step(s) = { T = s + 1
             if(s < 3, T, 0) }
            repeat(Step, 2, 0)
            """;

        EvaluatorTestSupport.AssertEvalLoopModes(source, 2m);

        var (result, loop, _) = RunObserved(source, enableLoopOptimization: true);
        Assert.False(result.IsError);
        Assert.Equal(1, loop.OptimizedLoopHits);
        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == "Step.repeat");
        var output = Assert.Single(plan.Expressions, expression => expression.Role == "output" && expression.Index == 0);
        Assert.True(output.Planned);
    }
}
