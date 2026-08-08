using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Pre-evaluation validation of the explicit-parameters-require-output invariant
/// against the STORED parameter-pattern list, for HAND-BUILT ASTs reaching the
/// public evaluator entry points.
///
/// Lean is authoritative: <c>Algorithm.mk</c> stores the parameter-pattern list,
/// and <c>validateExplicitParamOutputInvariant</c> (lean/KatLang.lean) rejects
/// <c>!parameterPatterns.isEmpty &amp;&amp; output.isEmpty</c> with
/// <c>Error.explicitParamsRequireOutput</c>. A legal parameter pattern may
/// contain ZERO captures (<c>ParameterPattern.sequenceValue []</c>), so an
/// algorithm can have one explicit parameter pattern while its flattened
/// capture list is empty — the invariant must test the pattern list, not the
/// flattened captures. The C# parser never produces a zero-capture pattern, so
/// this shape is only reachable through preconstructed ASTs handed to
/// <see cref="Evaluator.Run(Expr)"/> and its sibling entry points. Lean twins:
/// the CoreTests guards <c>zeroCapturePatternWithoutOutputRejectedAtRoot</c> and
/// <c>zeroCapturePatternWithoutOutputRejectedInPropertyPosition</c>.
/// </summary>
public class ExplicitParameterOutputValidationTests
{
    // ----- hand-built AST helpers ----------------------------------------------

    /// <summary>
    /// The canonical divergent shape: ONE explicit parameter pattern, ZERO
    /// flattened captures, EMPTY output (Lean:
    /// <c>.mk none [ParameterPattern.sequenceValue []] [] [] []</c>).
    /// </summary>
    private static Algorithm.User ZeroCaptureNoOutput() =>
        (Algorithm.User)new Algorithm.User(null, [], [], [], [])
            .WithParameterPatterns([new SequenceValueParameterPattern([])]);

    private static Expr RootPlacement() => new Expr.Block(ZeroCaptureNoOutput());

    private static Expr PropertyPlacement() => new Expr.Block(
        new Algorithm.User(
            null,
            [],
            [],
            [new Property("G", ZeroCaptureNoOutput())],
            [new Expr.Num(7)]));

    private static Expr CallG(params Expr[] args) =>
        new Expr.Call(new Expr.Resolve("G"), new Algorithm.User(null, [], [], [], [.. args]));

    /// <summary>
    /// Full structured comparison: exactly the bare validation error — the
    /// Lean-aligned kind, no <see cref="EvalError.WithContext"/> nesting, and a
    /// null span (a zero-capture pattern carries no source-backed declaration).
    /// </summary>
    private static void AssertBareRejection<T>(EvalResult<T> result)
    {
        Assert.True(result.IsError, "expected a pre-evaluation rejection");
        Assert.Equal(new EvalError.ExplicitParametersRequireOutput(), result.Error);
    }

    private sealed class CountingZeroArgPropertyResultCache : IZeroArgPropertyResultCache
    {
        public int Requests { get; private set; }

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Requests++;
            return evaluate();
        }
    }

    // ----- the canonical divergent shape ----------------------------------------

    [Fact]
    public void ZeroCapturePattern_HasOnePatternButZeroFlattenedCaptures()
    {
        var zeroCapture = ZeroCaptureNoOutput();

        var pattern = Assert.Single(zeroCapture.ParameterPatterns);
        var sequencePattern = Assert.IsType<SequenceValueParameterPattern>(pattern);
        Assert.Empty(sequencePattern.Items);
        Assert.Empty(zeroCapture.Parameters);
        Assert.Empty(zeroCapture.Output);
    }

    // ----- Lean-aligned rejections ----------------------------------------------

    [Fact]
    public void RootPlacement_IsRejectedWithTheBareStructuredError()
    {
        // Lean twin: zeroCapturePatternWithoutOutputRejectedAtRoot. Without the
        // pattern-list check this reached evaluation and reported the DIFFERENT
        // root MissingOutput error (wrapped in program context).
        var result = Evaluator.Run(RootPlacement());

        AssertBareRejection(result);
        Assert.Equal(
            AlgorithmValidation.ExplicitParametersRequireOutputMessage,
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void PropertyPlacement_IsRejectedWithTheBareStructuredError()
    {
        // Lean twin: zeroCapturePatternWithoutOutputRejectedInPropertyPosition.
        // Without the pattern-list check this program evaluated to 7 — the
        // malformed uncalled property was silently accepted.
        var result = Evaluator.Run(PropertyPlacement());

        AssertBareRejection(result);
        Assert.Equal(
            AlgorithmValidation.ExplicitParametersRequireOutputMessage,
            KatLangError.FromEvalError(result.Error).Message);
    }

    // ----- entry-point agreement ------------------------------------------------

    [Fact]
    public void RootPlacement_IsRejectedByEveryPrebuiltAstEntryPoint()
    {
        AssertAllEntryPointsReject(RootPlacement, topLevelPropertyName: "Missing");
    }

    [Fact]
    public void PropertyPlacement_IsRejectedByEveryPrebuiltAstEntryPoint()
    {
        AssertAllEntryPointsReject(PropertyPlacement, topLevelPropertyName: "G");
    }

    private static void AssertAllEntryPointsReject(Func<Expr> program, string topLevelPropertyName)
    {
        AssertBareRejection(Evaluator.Run(program()));
        AssertBareRejection(Evaluator.Run(program(), limits: null));
        AssertBareRejection(Evaluator.Run(program(), new RunScopedZeroArgPropertyResultCache()));
        AssertBareRejection(Evaluator.Run(
            program(),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: false,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: false,
            sequenceDiagnostics: null));
        AssertBareRejection(Evaluator.RunFlat(program()));
        AssertBareRejection(Evaluator.RunFlat(program(), limits: null));
        AssertBareRejection(Evaluator.RunCounted(program()));
        AssertBareRejection(Evaluator.RunCounted(program(), new RunScopedZeroArgPropertyResultCache()));
        AssertBareRejection(Evaluator.RunCountedObserved(program()).Result);
        AssertBareRejection(Evaluator.RunCountedObserved(program(), enableOptimizations: false).Result);
        AssertBareRejection(Evaluator.RunCountedWithTopLevelProperty(
            program(), topLevelPropertyName, UncachedZeroArgPropertyResultCache.Instance));
        AssertBareRejection(Evaluator.RunObserved(program(), new EvaluationObservations(), enableOptimizations: false));
        AssertBareRejection(Evaluator.RunObserved(program(), new EvaluationObservations(), enableOptimizations: true));
    }

    // ----- validation precedes root-context/cache creation -----------------------

    [Fact]
    public void CallerSuppliedZeroArgPropertyCache_IsNeverTouchedByARejectedRun()
    {
        // Control first: the spy counts requests when evaluation actually runs
        // (lexical property-style access `H` goes through the per-run cache), so
        // the zero-interaction assertions below cannot pass vacuously.
        var control = new Expr.Block(new Algorithm.User(
            null, [], [],
            [new Property("H", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]))],
            [new Expr.Resolve("H")]));
        var controlCache = new CountingZeroArgPropertyResultCache();
        Assert.False(Evaluator.Run(control, controlCache).IsError);
        Assert.True(controlCache.Requests > 0, "control run should consult the caller-supplied cache");

        var runCache = new CountingZeroArgPropertyResultCache();
        AssertBareRejection(Evaluator.Run(PropertyPlacement(), runCache));
        Assert.Equal(0, runCache.Requests);

        var countedCache = new CountingZeroArgPropertyResultCache();
        AssertBareRejection(Evaluator.RunCounted(PropertyPlacement(), countedCache));
        Assert.Equal(0, countedCache.Requests);

        var observedCache = new CountingZeroArgPropertyResultCache();
        AssertBareRejection(Evaluator.RunCountedObserved(
            PropertyPlacement(), zeroArgPropertyResultCache: observedCache).Result);
        Assert.Equal(0, observedCache.Requests);

        var topLevelCache = new CountingZeroArgPropertyResultCache();
        AssertBareRejection(Evaluator.RunCountedWithTopLevelProperty(
            PropertyPlacement(), "G", topLevelCache));
        Assert.Equal(0, topLevelCache.Requests);
    }

    // ----- the parser-facing scan shares the corrected walker --------------------

    [Fact]
    public void FindExplicitParameterOutputViolations_ReportsTheZeroCapturePattern()
    {
        var direct = AlgorithmValidation.FindExplicitParameterOutputViolations(ZeroCaptureNoOutput());
        var directViolation = Assert.Single(direct);
        Assert.Null(directViolation.Span);

        var nested = AlgorithmValidation.FindExplicitParameterOutputViolations(
            new Algorithm.User(
                null, [], [], [new Property("G", ZeroCaptureNoOutput())], [new Expr.Num(7)]));
        Assert.Single(nested);
    }

    // ----- valid shapes keep working --------------------------------------------

    [Fact]
    public void CapturePatternsWithNonemptyOutput_RemainValid()
    {
        var identity = (Algorithm.User)new Algorithm.User(null, [], [], [], [new Expr.Param("x")])
            .WithParameterPatterns([new CaptureParameterPattern("x")]);
        var program = new Expr.Block(new Algorithm.User(
            null,
            [],
            [],
            [new Property("F", identity)],
            [new Expr.Call(new Expr.Resolve("F"), new Algorithm.User(null, [], [], [], [new Expr.Num(41)]))]));

        Assert.Empty(AlgorithmValidation.FindExplicitParameterOutputViolations(identity));

        var result = Evaluator.RunFlat(program);
        Assert.False(result.IsError);
        Assert.Equal([41m], result.Value);
    }

    [Fact]
    public void ZeroCapturePatternWithOutput_KeepsItsCallAndMatchingSemantics()
    {
        // A zero-capture pattern stays ONE explicit parameter slot — it is not
        // reinterpreted as "no explicit patterns". With an output the algorithm
        // is valid: `G(())` binds the empty sequence argument against the empty
        // pattern, and a zero-argument call is an ordinary arity mismatch.
        var zeroCaptureWithOutput = (Algorithm.User)new Algorithm.User(
                null, [], [], [], [new Expr.Num(7)])
            .WithParameterPatterns([new SequenceValueParameterPattern([])]);

        Assert.Empty(AlgorithmValidation.FindExplicitParameterOutputViolations(zeroCaptureWithOutput));

        Expr Program(params Expr[] outputRows) => new Expr.Block(new Algorithm.User(
            null, [], [], [new Property("G", zeroCaptureWithOutput)], [.. outputRows]));

        var matched = Evaluator.RunFlat(Program(CallG(new Expr.EmptySequence(0))));
        Assert.False(matched.IsError);
        Assert.Equal([7m], matched.Value);

        var zeroArguments = Evaluator.Run(Program(CallG()));
        Assert.True(zeroArguments.IsError);
        var arityMismatch = Assert.IsType<EvalError.ArityMismatch>(
            Assert.IsType<EvalError.WithContext>(zeroArguments.Error).Inner);
        Assert.Equal(1, arityMismatch.Expected);
        Assert.Equal(0, arityMismatch.Actual);
    }
}
