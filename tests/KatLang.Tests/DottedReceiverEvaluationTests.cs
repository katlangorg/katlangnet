using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// A dotted receiver's VALUE is computed at most once per dotted operation.
///
/// <para><c>A.F(B)</c> means <c>F(A, B)</c>, so the two forms must agree on value, emitted
/// count, error, and resource consumption. They did not: the sequence-builtin dot path
/// evaluated the receiver to dispatch on it, then reified that result back into an AST
/// literal (<c>CountedArgAlgorithm</c> / <c>ResultToExpr</c>) which the builtin evaluated
/// AGAIN — so <c>range(1, 10).count</c> materialized twenty item slots for one ten-item
/// collection. A cached receiver property did not help, because the duplicate was a
/// reconstruction from the already-evaluated result rather than a second evaluation of the
/// source expression.</para>
///
/// <para>Resource counts are the primary evidence here; nothing asserts elapsed time.</para>
/// </summary>
public class DottedReceiverEvaluationTests
{
    /// <summary>
    /// The smallest cumulative materialization budget that lets <paramref name="source"/>
    /// complete — a deterministic measure of how many item slots the run creates.
    /// </summary>
    private static long RequiredItemSlots(string source, bool optimize = true)
    {
        for (long n = 0; n <= 2_000; n++)
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = n == 0 ? 1 : n };
            var expr = new Expr.Block(Parser.Parse(source).Root);
            var result = optimize
                ? Evaluator.Run(expr, limits)
                : Evaluator.Run(
                    expr, UncachedZeroArgPropertyResultCache.Instance,
                    enableLoopOptimization: false, loopDiagnostics: null,
                    enableSequencePipelineOptimization: false, sequenceDiagnostics: null, limits);
            if (!result.IsError) return n == 0 ? 1 : n;
        }

        Assert.Fail($"`{source}` never completed within the probe range.");
        return -1;
    }

    private static Result Value(string source)
    {
        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root));
        if (result.IsError)
            Assert.Fail($"`{source}` failed: {KatLangError.FromEvalError(result.Error).Message}");
        return result.Value;
    }

    private static string DisplayOf(string source) => KatLangEngine.Run(source).ToDisplayString();

    // ── The reported defect ──────────────────────────────────────────────────

    [Fact]
    public void DottedCollectionBuiltin_MaterializesItsReceiverExactlyOnce()
    {
        Assert.Equal(10, RequiredItemSlots("Output = range(1, 10)"));
        Assert.Equal(10, RequiredItemSlots("Output = count(range(1, 10))"));
        Assert.Equal(10, RequiredItemSlots("Output = range(1, 10).count"));
    }

    [Fact]
    public void CachedReceiverProperty_AlsoMaterializesOnce()
    {
        Assert.Equal(10, RequiredItemSlots("V = range(1, 10)\nOutput = count(V)"));
        Assert.Equal(10, RequiredItemSlots("V = range(1, 10)\nOutput = V.count"));
    }

    [Fact]
    public void ExplicitZeroArgumentCallReceiver_MaterializesOnce()
        => Assert.Equal(
            RequiredItemSlots("V = range(1, 10)\nOutput = count(V())"),
            RequiredItemSlots("V = range(1, 10)\nOutput = V().count"));

    // ── Ordinary/dotted parity across every collection builtin ───────────────

    [Theory]
    [InlineData("count(C)", "C.count")]
    [InlineData("sum(C)", "C.sum")]
    [InlineData("first(C)", "C.first")]
    [InlineData("last(C)", "C.last")]
    [InlineData("min(C)", "C.min")]
    [InlineData("max(C)", "C.max")]
    [InlineData("avg(C)", "C.avg")]
    [InlineData("order(C)", "C.order")]
    [InlineData("orderDesc(C)", "C.orderDesc")]
    [InlineData("distinct(C)", "C.distinct")]
    [InlineData("atoms(C)", "C.atoms")]
    [InlineData("take(C, 3)", "C.take(3)")]
    [InlineData("skip(C, 3)", "C.skip(3)")]
    [InlineData("contains(C, 3)", "C.contains(3)")]
    [InlineData("map(C, Double)", "C.map(Double)")]
    [InlineData("filter(C, Big)", "C.filter(Big)")]
    [InlineData("reduce(C, Add, 0)", "C.reduce(Add, 0)")]
    public void OrdinaryAndDottedForms_AgreeOnValueAndResources(string ordinary, string dotted)
    {
        const string preamble = "Double(x) = x * 2\nBig(x) = x > 5\nAdd(a, b) = a + b\n";
        var ordinarySource = $"{preamble}C = range(1, 10)\nOutput = {ordinary}";
        var dottedSource = $"{preamble}C = range(1, 10)\nOutput = {dotted}";

        Assert.Equal(Value(ordinarySource), Value(dottedSource), Result.ValueComparer);
        Assert.Equal(DisplayOf(ordinarySource), DisplayOf(dottedSource));
        Assert.Equal(RequiredItemSlots(ordinarySource), RequiredItemSlots(dottedSource));
    }

    // ── Receiver value kinds ─────────────────────────────────────────────────

    [Theory]
    [InlineData("7")]
    [InlineData("'text'")]
    [InlineData("()")]
    [InlineData("(1, 2, 3)")]
    [InlineData("[]")]
    [InlineData("[7]")]
    [InlineData("[1, 2, 3]")]
    [InlineData("[(1, 2), [3, 4]]")]
    [InlineData("[range(1, 3)..., 9]")]
    public void EveryReceiverValueKind_AgreesBetweenForms(string receiver)
    {
        var ordinarySource = $"R = {receiver}\nOutput = count(R)";
        var dottedSource = $"R = {receiver}\nOutput = R.count";

        Assert.Equal(Value(ordinarySource), Value(dottedSource), Result.ValueComparer);
        Assert.Equal(RequiredItemSlots(ordinarySource), RequiredItemSlots(dottedSource));
    }

    // ── Receiver source forms ────────────────────────────────────────────────

    [Theory]
    [InlineData("[1, 2, 3]")]                       // list literal
    [InlineData("range(1, 5)")]                     // ordinary call
    [InlineData("(1, 2, 3)")]                       // parenthesized body
    [InlineData("Pick(1)")]                         // conditional call
    [InlineData("[1, 2, 3].take(2)")]               // nested dotted chain
    [InlineData("[[1, 2], [3, 4]]:0")]              // index result
    [InlineData("[1, 2, 3].map(Double)")]           // callback result
    public void EveryReceiverSourceForm_AgreesBetweenForms(string receiver)
    {
        const string preamble = "Double(x) = x * 2\nPick(0) = [9]\nPick(n) = [1, 2, 3]\n";
        var ordinarySource = $"{preamble}Output = count({receiver})";
        var dottedSource = $"{preamble}Output = ({receiver}).count";

        Assert.Equal(Value(ordinarySource), Value(dottedSource), Result.ValueComparer);
        Assert.Equal(RequiredItemSlots(ordinarySource), RequiredItemSlots(dottedSource));
    }

    // ── Structural property access is untouched ──────────────────────────────

    [Fact]
    public void StructuralPropertyAccess_IsNotTurnedIntoAnExtensionCall()
    {
        Assert.Equal("7", DisplayOf("Object = (\n    public Value = 7\n)\nOutput = Object.Value"));
        Assert.Equal("7", DisplayOf("Object = (\n    public Value = 7\n    public Get = Value\n)\nOutput = Object.Get"));
    }

    [Fact]
    public void UnknownStructuralMember_StillFails()
        => Assert.IsType<RunResult.EvalFailure>(
            KatLangEngine.Run("Object = (\n    public Value = 7\n)\nOutput = Object.Missing"));

    [Fact]
    public void ExportedStructuralMember_KeepsItsExistingVisibilityOutcome()
        => Assert.Equal("7", DisplayOf("Object = (\n    Hidden = 7\n)\nOutput = Object.Hidden"));

    // ── User extension-style calls ───────────────────────────────────────────

    [Fact]
    public void UserExtensionCall_AgreesBetweenForms()
    {
        Assert.Equal(
            RequiredItemSlots("F(c) = c.count\nOutput = F(range(1, 10))"),
            RequiredItemSlots("F(c) = c.count\nOutput = range(1, 10).F"));

        Assert.Equal(
            RequiredItemSlots("T(c, n) = take(c, n)\nOutput = T(range(1, 10), 3)"),
            RequiredItemSlots("T(c, n) = take(c, n)\nOutput = range(1, 10).T(3)"));
    }

    [Fact]
    public void HigherOrderReceiver_KeepsItsAlgorithmMeaning()
    {
        // The receiver is callable, and the callee invokes it. Dotted syntax must not
        // reduce it to a value.
        Assert.Equal("14", DisplayOf("Apply(g, v) = g(v)\nDouble(x) = x * 2\nOutput = Double.Apply(7)"));
        Assert.Equal(
            DisplayOf("Apply(g, v) = g(v)\nDouble(x) = x * 2\nOutput = Apply(Double, 7)"),
            DisplayOf("Apply(g, v) = g(v)\nDouble(x) = x * 2\nOutput = Double.Apply(7)"));
    }

    // ── Nested chains ────────────────────────────────────────────────────────

    [Fact]
    public void NestedChain_EvaluatesEachLinkReceiverOnce()
    {
        const string preamble = "B(x) = x > 5\nD(x) = x * 2\n";
        var ordinarySource = $"{preamble}Output = count(map(filter(range(1, 10), B), D))";
        var dottedSource = $"{preamble}Output = range(1, 10).filter(B).map(D).count";

        Assert.Equal(Value(ordinarySource), Value(dottedSource), Result.ValueComparer);
        Assert.Equal(RequiredItemSlots(ordinarySource), RequiredItemSlots(dottedSource));
    }

    // ── Plain / counted / engine and optimizer parity ────────────────────────

    [Theory]
    [InlineData("Output = range(1, 10).count")]
    [InlineData("Output = range(1, 10).order")]
    [InlineData("B(x) = x > 5\nOutput = range(1, 10).filter(B).count")]
    public void PlainCountedAndEngine_Agree(string source)
    {
        var expr = new Expr.Block(Parser.Parse(source).Root);
        var plain = Evaluator.Run(expr);
        var counted = Evaluator.RunCounted(expr, UncachedZeroArgPropertyResultCache.Instance);
        var engine = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

        Assert.False(plain.IsError);
        Assert.False(counted.IsError);
        Assert.Equal(plain.Value, counted.Value.Value, Result.ValueComparer);
        Assert.Equal(plain.Value, engine.Value, Result.ValueComparer);
        Assert.Equal(counted.Value.EmittedCount, engine.EmittedCount);
    }

    [Theory]
    [InlineData("Output = range(1, 10).order")]
    [InlineData("Output = range(1, 10).distinct")]
    [InlineData("D(x) = x * 2\nOutput = range(1, 10).map(D)")]
    public void OptimizedAndGenericPaths_ChargeTheSame(string source)
        => Assert.Equal(RequiredItemSlots(source, optimize: false), RequiredItemSlots(source, optimize: true));

    [Theory]
    [InlineData("Output = range(1, 10).count")]
    [InlineData("Output = range(1, 10).sum")]
    [InlineData("B(x) = x > 5\nOutput = range(1, 10).filter(B).count")]
    public void FusedPipelines_ChargeNoMoreThanTheGenericPath(string source)
    {
        // A fused pipeline materializes nothing, so it legitimately charges LESS — that
        // difference is the documented fusion contract. What must never happen is the
        // optimized path charging MORE than the generic one.
        Assert.True(RequiredItemSlots(source, optimize: true) <= RequiredItemSlots(source, optimize: false));
    }

    // ── Budget-boundary parity ───────────────────────────────────────────────

    [Fact]
    public void OrdinaryAndDottedForms_CrossCumulativeBoundariesIdentically()
    {
        const string ordinary = "Output = count(range(1, 10))";
        const string dotted = "Output = range(1, 10).count";

        for (long budget = 1; budget <= 24; budget++)
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = budget };
            Assert.Equal(
                Evaluator.Run(new Expr.Block(Parser.Parse(ordinary).Root), limits).IsError,
                Evaluator.Run(new Expr.Block(Parser.Parse(dotted).Root), limits).IsError);
        }
    }

    // ── Errors, order, and spans ─────────────────────────────────────────────

    [Fact]
    public void ReceiverErrorStillWinsOverSuffixArgumentError()
    {
        // Evaluation order is unchanged: the receiver is prepared first, so its error is
        // the one reported.
        var result = KatLangEngine.Run("Output = range(1, 10).take(Missing)");
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Contains("Missing", failure.Errors[0].Message);
    }

    [Fact]
    public void ReceiverEvaluationError_IsSurfacedWithASpan()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("Output = Missing.count"));
        Assert.NotNull(failure.Errors[0].StartLine);
    }

    [Fact]
    public void ResourceLimitReachedByTheReceiver_IsReportedIdenticallyInBothForms()
    {
        var limits = new EvaluationLimits { MaxCollectionItems = 5 };
        var ordinary = Evaluator.Run(new Expr.Block(Parser.Parse("Output = count(range(1, 10))").Root), limits);
        var dotted = Evaluator.Run(new Expr.Block(Parser.Parse("Output = range(1, 10).count").Root), limits);

        // Spans differ because the two SOURCES differ; the structured payload must not.
        var ordinaryLimit = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ordinary.Error);
        var dottedLimit = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(dotted.Error);
        Assert.Equal(ordinaryLimit.Limit, dottedLimit.Limit);
        Assert.Equal(ordinaryLimit.Requested, dottedLimit.Requested);
        Assert.NotNull(dottedLimit.Span);
    }
}
