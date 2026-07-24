using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Focused coverage for the shared call argument pipeline
/// (<c>BuildCallArgumentInputs</c>; Lean <c>collectVariadicCallItems</c>):
/// every callable shape — flat fixed, flat/mixed variadic, patterned
/// (repeated-name / sequence-value patterns), and multi-clause conditional —
/// receives its argument supply from ONE assembly stage that evaluates each
/// written slot, reifies every non-spread slot as exactly one argument value,
/// and expands every explicit spread slot by exactly one value boundary.
/// Arity checking, clause selection, and pattern binding all happen strictly
/// AFTER that assembly, so the callee's internal representation never changes
/// the meaning of caller-side spread. Lean twins: the
/// <c>call-spread-into-*</c> LanguageSpec cases.
/// </summary>
public class CallArgumentAssemblyTests
{
    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result.ListValue List(params Result[] items) => new(items);

    private static Result.SequenceValue Seq(params Result[] items) => new(items);

    private static void AssertSemanticallyEqual(Result expected, Result actual)
        => Assert.True(
            Result.ValueComparer.Equals(expected, actual),
            $"Expected {expected} but got {actual}");

    /// <summary>
    /// Same 4-way parity matrix as <c>RestCollectionTests</c>: public engine,
    /// plain evaluation with optimizers on and off, and counted evaluation
    /// must agree on one result value.
    /// </summary>
    private static Result EvaluateAllModes(string source)
    {
        var ast = Parser.Parse(source).Root;
        var expr = new Expr.Block(ast);

        var plainOptimized = Evaluator.Run(
            expr, new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true, loopDiagnostics: null,
            enableSequencePipelineOptimization: true, sequenceDiagnostics: null);
        var plainGeneric = Evaluator.Run(
            expr, new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: false, loopDiagnostics: null,
            enableSequencePipelineOptimization: false, sequenceDiagnostics: null);
        var counted = Evaluator.RunCounted(expr);
        var engineRun = KatLangEngine.Run(source);

        Assert.True(plainOptimized.IsOk, $"optimizer-on evaluation failed: {(plainOptimized.IsError ? plainOptimized.Error.ToString() : "")}");
        Assert.True(plainGeneric.IsOk, $"optimizer-off evaluation failed: {(plainGeneric.IsError ? plainGeneric.Error.ToString() : "")}");
        Assert.True(counted.IsOk, $"counted evaluation failed: {(counted.IsError ? counted.Error.ToString() : "")}");
        var success = Assert.IsType<RunResult.Success>(engineRun);

        AssertSemanticallyEqual(plainOptimized.Value, plainGeneric.Value);
        AssertSemanticallyEqual(plainOptimized.Value, counted.Value.Value);
        AssertSemanticallyEqual(plainOptimized.Value, success.Value);
        return plainOptimized.Value;
    }

    private static void AssertEvaluates(string source, Result expected)
        => AssertSemanticallyEqual(expected, EvaluateAllModes(source));

    private static EvalError AssertFails(string source)
    {
        var plain = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root));
        var counted = Evaluator.RunCounted(new Expr.Block(Parser.Parse(source).Root));
        Assert.True(plain.IsError, "expected plain evaluation to fail");
        Assert.True(counted.IsError, "expected counted evaluation to fail");
        Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        return plain.Error;
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private const string TwoClauseConditional =
        "F(0, 0) = 100\nF(x, y) = x + y\n";

    // ── Spread has identical meaning for every callee shape ─────────────────

    [Fact]
    public void SequenceSpread_FlatCallee_SuppliesOpenedItemsAsSlots()
        => AssertEvaluates("G(x, y) = x + y\nA = (1, 2)\nG(A...)", Atom(3));

    [Fact]
    public void SequenceSpread_PatternedCallee_SuppliesOpenedItemsAsSlots()
        => AssertEvaluates("F(x, x) = x + 1\nA = (7, 7)\nF(A...)", Atom(8));

    [Fact]
    public void SequenceSpread_ConditionalCallee_SuppliesOpenedItemsBeforeClauseSelection()
        => AssertEvaluates(TwoClauseConditional + "A = (1, 2)\nF(A...)", Atom(3));

    [Fact]
    public void SequenceSpread_ConditionalCallee_DispatchHappensAfterExpansion()
    {
        // Dispatch-after-expansion proof: the literal clause F(0, 0) can only
        // win if the spread supplied TWO slots before clause selection.
        AssertEvaluates(TwoClauseConditional + "A = (0, 0)\nF(A...)", Atom(100));
    }

    [Fact]
    public void ListSpread_PatternedAndConditionalCallees_SupplyOpenedItems()
    {
        AssertEvaluates("F(x, x) = x\nB = [7, 7]\nF(B...)", Atom(7));
        AssertEvaluates(TwoClauseConditional + "B = [1, 2]\nF(B...)", Atom(3));
    }

    // ── A catch-all clause can no longer absorb a spread as one closed value ─

    [Fact]
    public void SequenceSpread_ConditionalCallee_CatchAllCannotAbsorbClosedValue()
    {
        // The clause family has arity 2; the spread supplies 2 slots that no
        // clause matches (neither literal pair (9, 9) nor... both binder
        // clause DOES match here) — so pin the 1-vs-family case: the unspread
        // argument is ONE closed value, which no two-argument clause matches.
        var error = AssertFails(TwoClauseConditional + "A = (1, 2)\nF(A)");
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error));
    }

    // ── Total spread: atoms, strings, empties ───────────────────────────────

    [Fact]
    public void AtomSpread_ConditionalCallee_SuppliesTheAtomItself()
        => AssertEvaluates("F(0) = 100\nF(x) = x + 1\nF(7...)", Atom(8));

    [Fact]
    public void StringSpread_ConditionalCallee_SuppliesTheStringItself()
        => AssertEvaluates("F('a') = 1\nF(other) = 0\nF('a'...)", Atom(1));

    [Fact]
    public void EmptySequenceSpread_IsNeutralForEveryCalleeShape()
    {
        AssertEvaluates("G(x, y) = x + y\nG(()..., 1, 2)", Atom(3));
        AssertEvaluates("F(x, x) = x\nF(()..., 7, 7)", Atom(7));
        AssertEvaluates(TwoClauseConditional + "F(()..., 1, 2)", Atom(3));
    }

    [Fact]
    public void EmptyListSpread_IsNeutralForEveryCalleeShape()
    {
        AssertEvaluates("G(x, y) = x + y\nG([]..., 1, 2)", Atom(3));
        AssertEvaluates("F(x, x) = x\nF([]..., 7, 7)", Atom(7));
        AssertEvaluates(TwoClauseConditional + "F([]..., 1, 2)", Atom(3));
    }

    // ── Mixed fixed and spread slots ────────────────────────────────────────

    [Fact]
    public void MixedFixedAndSpreadSlots_ConditionalCallee_FormOneArgumentSupply()
        => AssertEvaluates(
            "F(0, 0, 0) = 100\nF(x, y, z) = x + y + z\nA = (2, 3)\nF(1, A...)",
            Atom(6));

    // ── Arity is checked after expansion ────────────────────────────────────

    [Fact]
    public void SequenceSpread_PatternedCallee_ArityCheckedAfterExpansion()
    {
        var error = AssertFails("F(x, x) = x\nA = (7, 7, 7)\nF(A...)");
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(3, arity.Actual);
    }

    [Fact]
    public void SequenceSpread_ConditionalCallee_UnmatchedExpandedArityIsNoMatchingBranch()
    {
        var error = AssertFails(TwoClauseConditional + "A = (1, 2, 3)\nF(A...)");
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error));
    }

    [Fact]
    public void SequenceSpread_PatternedCallee_NoLongerArrivesAsOneClosedValue()
    {
        // Migration fact of the uniform rule: the old per-shape assembler let
        // a spread reach a patterned callee as ONE closed value, so
        // `F(A..., 9)` bound the (x, y) pattern from A. Spread now supplies
        // ordinary argument slots — three slots against two parameters is an
        // arity error; write `F(A, 9)` for the destructuring reading.
        var error = AssertFails("F((x, y), z) = (x, y, z)\nA = (1, 2)\nF(A..., 9)");
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(3, arity.Actual);

        AssertEvaluates("F((x, y), z) = x + y + z\nA = (1, 2)\nF(A, 9)", Atom(12));
    }

    // ── Ordinary vs extension-property (dotted) form agree ──────────────────

    [Fact]
    public void DottedCallWithSpreadArguments_AgreesWithOrdinaryForm()
    {
        const string Defs = "F(0, 0, 0) = 100\nF(x, y, z) = x + y + z\nB = (2, 3)\n";
        AssertEvaluates(Defs + "(1).F(B...)", Atom(6));
        AssertEvaluates(Defs + "F(1, B...)", Atom(6));
    }

    // ── Non-spread sequence/list arguments remain closed ────────────────────

    [Fact]
    public void NonSpreadArguments_RemainOneClosedValue_ForPatternedCallees()
    {
        var error = AssertFails("F(x, x) = x\nA = (7, 7)\nF(A)");
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(1, arity.Actual);
    }

    [Fact]
    public void NonSpreadArguments_RemainOneClosedValue_ForConditionalCallees()
    {
        var sequenceError = AssertFails(TwoClauseConditional + "A = (1, 2)\nF(A)");
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(sequenceError));

        var listError = AssertFails(TwoClauseConditional + "B = [1, 2]\nF(B)");
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(listError));
    }

    // ── Function-valued argument in a rest binding (targeted diagnostic) ─────

    [Fact]
    public void FunctionValuedArgument_InRestBinding_ReportsTargetedDiagnostic()
    {
        var error = AssertFails("F(...fs) = fs\nF(sum)");
        var mismatch = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.Contains("Rest parameter `...fs` collects values", mismatch.Message, StringComparison.Ordinal);
        Assert.Contains("a supplied argument is a function", mismatch.Message, StringComparison.Ordinal);

        // A parameterized user function is function-shaped too.
        var userError = AssertFails("H(x) = x\nF(...fs) = fs\nF(H)");
        Assert.IsType<EvalError.TypeMismatch>(Innermost(userError));

        // Fixed parameters keep the dual algorithm channel: the same argument
        // is legal where a fixed parameter receives it.
        AssertEvaluates("Apply(f, ...xs) = f(xs)\nApply(sum, 1, 2)", Atom(3));
    }

    [Fact]
    public void ErroredValuePropertyArgument_InRestBinding_SurfacesTheRealError()
    {
        // A zero-parameter VALUE property is NOT function-shaped: when its
        // body fails, the rest binding surfaces the genuine evaluation error
        // instead of misdescribing the argument as "a function".
        var divisionError = AssertFails("Bad = 1 / 0\nG(...items) = items.count\nG(Bad)");
        Assert.IsType<EvalError.DivByZero>(Innermost(divisionError));

        var emptyError = AssertFails("Data = first([])\nG(...items) = items\nG(Data)");
        Assert.IsType<EvalError.BadArity>(Innermost(emptyError));
    }
}
