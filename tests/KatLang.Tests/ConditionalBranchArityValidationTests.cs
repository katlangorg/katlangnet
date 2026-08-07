using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Pre-evaluation validation of the uniform conditional branch arity invariants
/// for HAND-BUILT ASTs reaching the public evaluator entry points.
///
/// Lean is authoritative: <c>runResultM</c> (lean/KatLang.lean) runs
/// <c>validateExplicitParamOutputInvariantExpr</c> over the whole tree BEFORE any
/// evaluation, and <c>validateConditionalBranchArities</c> rejects a conditional
/// whose branches disagree on top-level pattern arity
/// (<c>Error.branchArityMismatch name expected actual</c>) or top-level output
/// arity (<c>Error.branchOutputArityMismatch name expected actual</c>), input
/// arity checked first. Expected comes from the FIRST branch, actual from the
/// first mismatching branch; the diagnostic name is the nearest enclosing
/// property name, with the Lean default label <c>"conditional"</c> for a
/// conditional reached through expression position.
///
/// The C# parser rejects mismatched clause families during clause elaboration,
/// so surface programs can never contain one — these invariants are only
/// observable for preconstructed ASTs handed to <see cref="Evaluator.Run(Expr)"/>
/// and its sibling entry points. Lean twins: the CoreTests guards
/// <c>branchInputArityMismatchIsRejected</c>,
/// <c>branchOutputArityMismatchIsRejected</c>,
/// <c>nestedUnusedConditionalIsStillValidated</c>,
/// <c>sequenceValuePatternsWithSameTopLevelArityPass</c>, and
/// <c>uniformBranchOutputArityPasses</c>.
/// </summary>
public class ConditionalBranchArityValidationTests
{
    // ----- hand-built AST helpers ----------------------------------------------

    private static Algorithm.User Body(params Expr[] output) =>
        new(null, [], [], [], [.. output]);

    /// <summary>Branch input arities 1 vs 2 (Lean: litInt 0 / sequenceValue [x, y]).</summary>
    private static Algorithm.Conditional InputArityMismatchConditional() => new(
        Parent: null,
        Opens: [],
        Branches:
        [
            new CondBranch(new Pattern.LitInt(0), Body(new Expr.Num(1))),
            new CondBranch(
                new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]),
                Body(new Expr.Param("x"))),
        ]);

    /// <summary>Branch output arities 1 vs 2 (Lean: bodies [1] / [1, 2]).</summary>
    private static Algorithm.Conditional OutputArityMismatchConditional() => new(
        Parent: null,
        Opens: [],
        Branches:
        [
            new CondBranch(new Pattern.LitInt(0), Body(new Expr.Num(1))),
            new CondBranch(new Pattern.Bind("x"), Body(new Expr.Num(1), new Expr.Num(2))),
        ]);

    /// <summary>Input arities 1 vs 2 AND output arities 1 vs 2 in one conditional.</summary>
    private static Algorithm.Conditional BothMismatchConditional() => new(
        Parent: null,
        Opens: [],
        Branches:
        [
            new CondBranch(new Pattern.Bind("x"), Body(new Expr.Param("x"))),
            new CondBranch(
                new Pattern.SequenceValue([new Pattern.Bind("a"), new Pattern.Bind("b")]),
                Body(new Expr.Num(1), new Expr.Num(2))),
        ]);

    private static Algorithm.Conditional ValidConditional() => new(
        Parent: null,
        Opens: [],
        Branches:
        [
            new CondBranch(new Pattern.LitInt(0), Body(new Expr.Num(100))),
            new CondBranch(new Pattern.Bind("x"), Body(new Expr.Param("x"))),
        ]);

    /// <summary>Program block with one property <c>F</c> and the given output rows.</summary>
    private static Expr ProgramWithF(Algorithm f, params Expr[] outputRows) =>
        new Expr.Block(new Algorithm.User(null, [], [], [new Property("F", f)], [.. outputRows]));

    private static Expr CallF(params Expr[] args) =>
        new Expr.Call(new Expr.Resolve("F"), new Algorithm.User(null, [], [], [], [.. args]));

    private static EvalError.BranchArityMismatch AssertBranchArityMismatch<T>(
        EvalResult<T> result, string name, int expected, int actual)
    {
        Assert.True(result.IsError, "expected a pre-evaluation rejection");
        var error = Assert.IsType<EvalError.BranchArityMismatch>(result.Error);
        Assert.Equal(name, error.AlgorithmName);
        Assert.Equal(expected, error.Expected);
        Assert.Equal(actual, error.Actual);
        return error;
    }

    private static EvalError.BranchOutputArityMismatch AssertBranchOutputArityMismatch<T>(
        EvalResult<T> result, string name, int expected, int actual)
    {
        Assert.True(result.IsError, "expected a pre-evaluation rejection");
        var error = Assert.IsType<EvalError.BranchOutputArityMismatch>(result.Error);
        Assert.Equal(name, error.AlgorithmName);
        Assert.Equal(expected, error.Expected);
        Assert.Equal(actual, error.Actual);
        return error;
    }

    // ----- Lean-aligned rejections ----------------------------------------------

    [Fact]
    public void InputArityMismatch_HandBuiltConditional_IsRejectedWithLeanPayload()
    {
        // Lean twin: branchInputArityMismatchIsRejected — F(0) would match the
        // first branch, but validation rejects the whole tree first.
        var result = Evaluator.Run(ProgramWithF(InputArityMismatchConditional(), CallF(new Expr.Num(0))));
        AssertBranchArityMismatch(result, "F", expected: 1, actual: 2);
    }

    [Fact]
    public void OutputArityMismatch_HandBuiltConditional_IsRejectedWithLeanPayload()
    {
        // Lean twin: branchOutputArityMismatchIsRejected.
        var result = Evaluator.Run(ProgramWithF(OutputArityMismatchConditional(), CallF(new Expr.Num(0))));
        AssertBranchOutputArityMismatch(result, "F", expected: 1, actual: 2);
    }

    [Fact]
    public void ExpectedComesFromFirstBranch_ActualFromFirstMismatch()
    {
        // Reversed branch order: first branch has arity 2, second has arity 1,
        // so the payload orientation flips to (expected 2, actual 1).
        var reversed = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(
                    new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]),
                    Body(new Expr.Param("x"))),
                new CondBranch(new Pattern.LitInt(0), Body(new Expr.Num(1))),
            ]);
        var result = Evaluator.Run(ProgramWithF(reversed, new Expr.Num(42)));
        AssertBranchArityMismatch(result, "F", expected: 2, actual: 1);
    }

    [Fact]
    public void FirstMismatchPayload_IsSelectedAcrossMoreThanTwoBranches()
    {
        var inputMismatch = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(
                    new Pattern.SequenceValue([new Pattern.Bind("a"), new Pattern.Bind("b")]),
                    Body(new Expr.Num(1))),
                new CondBranch(
                    new Pattern.SequenceValue([new Pattern.Bind("c"), new Pattern.Bind("d")]),
                    Body(new Expr.Num(2))),
                new CondBranch(new Pattern.Bind("firstMismatch"), Body(new Expr.Num(3))),
                new CondBranch(
                    new Pattern.SequenceValue(
                        [new Pattern.Bind("e"), new Pattern.Bind("f"), new Pattern.Bind("g")]),
                    Body(new Expr.Num(4))),
            ]);
        AssertBranchArityMismatch(
            Evaluator.Run(ProgramWithF(inputMismatch, new Expr.Num(42))),
            "F", expected: 2, actual: 1);

        var outputMismatch = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(new Pattern.LitInt(0), Body(new Expr.Num(1), new Expr.Num(2))),
                new CondBranch(new Pattern.LitInt(1), Body(new Expr.Num(3), new Expr.Num(4))),
                new CondBranch(new Pattern.LitInt(2), Body()),
                new CondBranch(new Pattern.Bind("x"), Body(new Expr.Num(5))),
            ]);
        AssertBranchOutputArityMismatch(
            Evaluator.Run(ProgramWithF(outputMismatch, new Expr.Num(42))),
            "F", expected: 2, actual: 0);
    }

    [Fact]
    public void MalformedConditional_IsRejectedBeforeBranchMatchingAndEvaluation()
    {
        // A call the first branch would happily match (before this validation the
        // evaluator returned 1 here) is still rejected — validation runs before
        // branch matching.
        var called = Evaluator.Run(ProgramWithF(BothMismatchConditional(), CallF(new Expr.Num(1))));
        AssertBranchArityMismatch(called, "F", expected: 1, actual: 2);

        // Lean twin: nestedUnusedConditionalIsStillValidated — a malformed
        // conditional nested inside an inner property is rejected even though
        // nothing ever references it, so the program cannot evaluate to 42.
        var outer = new Algorithm.User(
            null, [], [], [new Property("Bad", InputArityMismatchConditional())], [new Expr.Num(1)]);
        var uncalled = Evaluator.Run(new Expr.Block(new Algorithm.User(
            null, [], [], [new Property("Outer", outer)], [new Expr.Num(42)])));
        AssertBranchArityMismatch(uncalled, "Bad", expected: 1, actual: 2);
    }

    // ----- validation precedence ------------------------------------------------

    [Fact]
    public void InputArityMismatch_TakesPrecedenceOverOutputArityMismatch()
    {
        // Lean validateConditionalBranchArities checks input arity first; an input
        // mismatch suppresses the output check for the same conditional.
        var result = Evaluator.Run(ProgramWithF(BothMismatchConditional(), new Expr.Num(42)));
        AssertBranchArityMismatch(result, "F", expected: 1, actual: 2);
    }

    [Fact]
    public void ValidationPrecedence_FollowsLeanTraversalOrder_AcrossViolationKinds()
    {
        // One depth-first walk in declaration order decides which violation is
        // reported, exactly like Lean's single validation pass: whichever
        // malformed node comes first in traversal order wins.
        var branchViolation = new Property("A", OutputArityMismatchConditional());
        var explicitParamViolation = new Property(
            "B", new Algorithm.User(null, [new ParameterDeclaration("p")], [], [], []));

        var branchFirst = Evaluator.Run(new Expr.Block(new Algorithm.User(
            null, [], [], [branchViolation, explicitParamViolation], [new Expr.Num(42)])));
        AssertBranchOutputArityMismatch(branchFirst, "A", expected: 1, actual: 2);

        var explicitParamFirst = Evaluator.Run(new Expr.Block(new Algorithm.User(
            null, [], [], [explicitParamViolation, branchViolation], [new Expr.Num(42)])));
        Assert.True(explicitParamFirst.IsError);
        Assert.IsType<EvalError.ExplicitParametersRequireOutput>(explicitParamFirst.Error);
    }

    [Fact]
    public void ConditionalMismatch_PrecedesExplicitParameterViolationInsideFirstBranch()
    {
        var explicitParamViolation = new Algorithm.User(
            null, [new ParameterDeclaration("p")], [], [], []);

        var inputMismatch = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(new Pattern.Bind("x"), explicitParamViolation),
                new CondBranch(
                    new Pattern.SequenceValue([new Pattern.Bind("y"), new Pattern.Bind("z")]),
                    Body()),
            ]);
        AssertBranchArityMismatch(
            Evaluator.Run(ProgramWithF(inputMismatch, new Expr.Num(42))),
            "F", expected: 1, actual: 2);

        var outputMismatch = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(new Pattern.LitInt(0), explicitParamViolation),
                new CondBranch(new Pattern.Bind("x"), Body(new Expr.Num(1))),
            ]);
        AssertBranchOutputArityMismatch(
            Evaluator.Run(ProgramWithF(outputMismatch, new Expr.Num(42))),
            "F", expected: 0, actual: 1);
    }

    [Fact]
    public void CallTraversal_VisitsFunctionBeforeArgumentAlgorithm()
    {
        var expression = new Expr.Call(
            new Expr.Block(OutputArityMismatchConditional()),
            InputArityMismatchConditional());

        AssertBranchOutputArityMismatch(
            Evaluator.Run(expression), "conditional", expected: 1, actual: 2);
    }

    [Fact]
    public void DotCallArgumentAlgorithm_IsValidatedBeforeTargetEvaluation()
    {
        var expression = new Expr.DotCall(
            new Expr.Num(1),
            "Missing",
            InputArityMismatchConditional());

        AssertBranchArityMismatch(
            Evaluator.Run(expression), "conditional", expected: 1, actual: 2);
    }

    // ----- diagnostic name threading (Lean name parameter) ----------------------

    [Fact]
    public void ConditionalReachedThroughExpressionPosition_ReportsLeanDefaultName()
    {
        // Lean's expression walker validates a block's algorithm under the default
        // label "conditional" — the enclosing property name does not flow through
        // expression descent.
        var propertyBody = Body(new Expr.Block(InputArityMismatchConditional()));
        var program = new Expr.Block(new Algorithm.User(
            null, [], [], [new Property("Outer", propertyBody)], [new Expr.Num(42)]));
        AssertBranchArityMismatch(Evaluator.Run(program), "conditional", expected: 1, actual: 2);
    }

    [Fact]
    public void ConditionalBranchBody_InheritsEnclosingName_AndNestedPropertyOverridesIt()
    {
        // A conditional directly in branch-body position keeps the enclosing
        // conditional's name (Lean passes `name` through to branch bodies).
        var branchBodyConditional = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.Bind("x"), InputArityMismatchConditional())]);
        var inherited = Evaluator.Run(ProgramWithF(branchBodyConditional, new Expr.Num(42)));
        AssertBranchArityMismatch(inherited, "F", expected: 1, actual: 2);

        // A property nested inside a branch body relabels its own algorithm.
        var branchBodyWithProperty = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(
                    new Pattern.Bind("x"),
                    new Algorithm.User(
                        null, [], [],
                        [new Property("G", InputArityMismatchConditional())],
                        [new Expr.Num(1)])),
            ]);
        var overridden = Evaluator.Run(ProgramWithF(branchBodyWithProperty, new Expr.Num(42)));
        AssertBranchArityMismatch(overridden, "G", expected: 1, actual: 2);
    }

    // ----- valid hand-built conditionals keep working ---------------------------

    [Fact]
    public void ValidHandBuiltConditional_StillEvaluates()
    {
        var literalBranch = Evaluator.RunFlat(ProgramWithF(ValidConditional(), CallF(new Expr.Num(0))));
        Assert.False(literalBranch.IsError);
        Assert.Equal([100m], literalBranch.Value);

        var binderBranch = Evaluator.RunFlat(ProgramWithF(ValidConditional(), CallF(new Expr.Num(7))));
        Assert.False(binderBranch.IsError);
        Assert.Equal([7m], binderBranch.Value);
    }

    [Fact]
    public void UniformMultiOutputBranches_AreValid()
    {
        // Lean twin: uniformBranchOutputArityPasses — both branches emit TWO
        // top-level outputs, so the conditional is uniform and evaluates.
        var cond = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(new Pattern.LitInt(0), Body(new Expr.Num(1), new Expr.Num(2))),
                new CondBranch(new Pattern.Bind("x"), Body(new Expr.Param("x"), new Expr.Param("x"))),
            ]);
        var result = Evaluator.RunFlat(ProgramWithF(cond, CallF(new Expr.Num(0)), CallF(new Expr.Num(7))));
        Assert.False(result.IsError);
        Assert.Equal([1m, 2m, 7m, 7m], result.Value);
    }

    [Fact]
    public void SingleBranchAndEmptyConditionals_PassValidation()
    {
        // Lean validateBranchArities: [] and [b] have no rest to mismatch.
        var single = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.Bind("x"), Body(new Expr.Param("x")))]);
        var singleResult = Evaluator.RunFlat(ProgramWithF(single, CallF(new Expr.Num(5))));
        Assert.False(singleResult.IsError);
        Assert.Equal([5m], singleResult.Value);

        var empty = new Algorithm.Conditional(Parent: null, Opens: [], Branches: []);
        var emptyResult = Evaluator.RunFlat(ProgramWithF(empty, new Expr.Num(42)));
        Assert.False(emptyResult.IsError);
        Assert.Equal([42m], emptyResult.Value);
    }

    // ----- entry-point agreement ------------------------------------------------

    [Fact]
    public void AllPrebuiltAstEntryPoints_AgreeOnTheRejection()
    {
        Expr Malformed() => ProgramWithF(InputArityMismatchConditional(), CallF(new Expr.Num(0)));

        AssertBranchArityMismatch(Evaluator.Run(Malformed()), "F", 1, 2);
        AssertBranchArityMismatch(Evaluator.Run(Malformed(), limits: null), "F", 1, 2);
        AssertBranchArityMismatch(Evaluator.RunFlat(Malformed()), "F", 1, 2);
        AssertBranchArityMismatch(Evaluator.RunFlat(Malformed(), limits: null), "F", 1, 2);
        AssertBranchArityMismatch(Evaluator.RunCounted(Malformed()), "F", 1, 2);
        AssertBranchArityMismatch(Evaluator.RunCountedObserved(Malformed()).Result, "F", 1, 2);
        AssertBranchArityMismatch(
            Evaluator.RunCountedObserved(Malformed(), enableOptimizations: false).Result,
            "F", 1, 2);
        AssertBranchArityMismatch(
            Evaluator.RunCountedWithTopLevelProperty(
                Malformed(), "F", UncachedZeroArgPropertyResultCache.Instance),
            "F", 1, 2);
        AssertBranchArityMismatch(
            Evaluator.RunObserved(Malformed(), new EvaluationObservations(), enableOptimizations: false),
            "F", 1, 2);
        AssertBranchArityMismatch(
            Evaluator.RunObserved(Malformed(), new EvaluationObservations(), enableOptimizations: true),
            "F", 1, 2);
    }

    [Fact]
    public void AllDistinctPrebuiltAstExecutionPaths_AcceptAValidConditional()
    {
        Expr Valid() => ProgramWithF(ValidConditional(), CallF(new Expr.Num(7)));

        Assert.False(Evaluator.Run(Valid()).IsError);
        Assert.False(Evaluator.RunObserved(
            Valid(), new EvaluationObservations(), enableOptimizations: false).IsError);
        Assert.False(Evaluator.RunObserved(
            Valid(), new EvaluationObservations(), enableOptimizations: true).IsError);
        Assert.False(Evaluator.RunCounted(Valid()).IsError);
        Assert.False(Evaluator.RunCountedObserved(
            Valid(), enableOptimizations: false).Result.IsError);
        Assert.False(Evaluator.RunCountedObserved(
            Valid(), enableOptimizations: true).Result.IsError);
        Assert.False(Evaluator.RunCountedWithTopLevelProperty(
            Valid(), "Missing", UncachedZeroArgPropertyResultCache.Instance).IsError);
    }

    [Fact]
    public void BranchMismatchErrors_HaveStructuredPublicMessages()
    {
        var input = AssertBranchArityMismatch(
            Evaluator.Run(ProgramWithF(InputArityMismatchConditional(), new Expr.Num(42))),
            "F", 1, 2);
        Assert.Equal(
            "All branches of conditional algorithm 'F' must have the same top-level pattern arity. " +
            "Expected 1 (from first branch), but a branch has arity 2",
            KatLangError.FromEvalError(input).Message);

        var output = AssertBranchOutputArityMismatch(
            Evaluator.Run(ProgramWithF(OutputArityMismatchConditional(), new Expr.Num(42))),
            "F", 1, 2);
        Assert.Equal(
            "All branches of conditional algorithm 'F' must have the same top-level output arity. " +
            "Expected 1 (from first branch), but a branch has output arity 2",
            KatLangError.FromEvalError(output).Message);
    }

    // ----- surface programs are unchanged ---------------------------------------

    [Fact]
    public void ParserCreatedConditionals_EvaluateExactlyAsBefore()
    {
        var parsed = Parser.Parse("F(0) = 1\nF(x) = x + 1\nF(0), F(5)");
        Assert.False(parsed.HasErrors);
        var result = Evaluator.RunFlat(new Expr.Block(parsed.Root));
        Assert.False(result.IsError);
        Assert.Equal([1m, 6m], result.Value);
    }

    [Fact]
    public void SurfaceClauseFamilyMismatches_StillFailAtParseTime()
    {
        // The parser owns this diagnostic for surface programs; the pre-evaluation
        // validation is only reachable with hand-built trees.
        var inputMismatch = Parser.Parse("F(0) = 1\nF(x, y) = x + y\nF(0)");
        Assert.True(inputMismatch.HasErrors);
        Assert.Contains(inputMismatch.Diagnostics, d => d.Message.Contains("same top-level pattern arity"));

        var outputMismatch = Parser.Parse("F(0) = 1\nF(x) = x, x\nF(0)");
        Assert.True(outputMismatch.HasErrors);
        Assert.Contains(outputMismatch.Diagnostics, d => d.Message.Contains("same top-level output arity"));
    }
}
