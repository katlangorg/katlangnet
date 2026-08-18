using KatLang.Rendering;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// Source-level regressions for bounded diagnostic value rendering: real KatLang programs whose
/// evaluation FAILS while holding a shared value DAG, so the failing operand is quoted into the
/// message by <see cref="Evaluator.FormatResultForDiagnostic"/>.
///
/// <para>The program that reaches this is three lines long. <c>Wrap = [x, x]</c> stores its one
/// bound argument in both element slots, so <c>Wrap.repeat(n, 1)</c> is an ordinary in-budget loop
/// producing n+1 distinct nodes reachable through 2^n paths; adding <c>A + 1</c> asks the evaluator
/// to explain that a list is not a numeric operand. The unbounded renderer answered with
/// <c>5*2^n - 4</c> UTF-16 units — 327,676 at depth 16, and roughly 5.5 x 10^12 at depth 40, which
/// no host can allocate. The message is now bounded before it is built, and the SEMANTIC error is
/// unchanged: only the quoted fragment shortens.</para>
/// </summary>
public class BoundedDiagnosticSourceIntegrationTests
{
    private const int Cap = DiagnosticValueRenderer.MaxRenderedValueLength;

    private const string Marker = DiagnosticValueRenderer.TruncationMarker;

    /// <summary>The doubling-DAG program, deep enough that the pre-fix message was unbuildable.</summary>
    private static string DagProgram(string body, int depth = 40)
        => $"""
            Wrap = [x, x]
            A = Wrap.repeat({depth}, 1)
            {body}
            """;

    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext(_, var inner))
            error = inner;
        return error;
    }

    /// <summary>Every context message plus the innermost message, as the user would read them.</summary>
    private static IReadOnlyList<string> MessageParts(EvalError error)
    {
        var parts = new List<string>();
        while (error is EvalError.WithContext(var context, var inner))
        {
            parts.Add(context.ToLegacyString());
            error = inner;
        }

        parts.Add(error is EvalError.TypeMismatch(var message) ? message : error.ToString());
        return parts;
    }

    private static EvalError ExpectError(string source, EvaluationLimits? limits = null)
    {
        var result = Evaluator.Run(Program(source), limits);
        Assert.True(result.IsError, "expected the program to fail");
        return result.Error;
    }

    private static (
        EvalResult<Evaluator.CountedResult> Result,
        EvaluationObservations Observations,
        SequencePipelineDiagnostics Diagnostics) ObserveCounted(
            string source,
            bool enableOptimizations,
            EvaluationLimits? limits = null)
    {
        var observations = new EvaluationObservations();
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source),
            limits,
            enableOptimizations: enableOptimizations,
            sequenceDiagnostics: diagnostics,
            observations: observations);
        return (result, observations, diagnostics);
    }

    // ── The shared DAG reaches a real diagnostic, bounded ────────────────────────────────────

    [Fact]
    public void SharedDagInNumericOperand_ProducesABoundedTypeMismatch()
    {
        var error = ExpectError(DagProgram("A + 1"));

        // The semantic error is untouched — bounding is presentation, never classification.
        Assert.IsType<EvalError.TypeMismatch>(Innermost(error));

        var operandMessage = Assert.IsType<EvalError.TypeMismatch>(Innermost(error)).Message;

        // The message names the value's kind and element count in full, and quotes only a
        // bounded fragment of its content.
        Assert.Contains("expects numeric scalar operands", operandMessage);
        Assert.Contains("a list value with 2 elements", operandMessage);
        Assert.Contains(Marker, operandMessage);

        // The quoted fragment is bounded; the surrounding explanatory text is short and fixed.
        Assert.True(operandMessage.Length < Cap + 256, $"operand message was {operandMessage.Length} units");
    }

    [Fact]
    public void SharedDagDiagnostic_IsBoundedAtEveryEntryPoint()
    {
        var source = DagProgram("A + 1");
        var expr = Program(source);

        var plain = Evaluator.Run(expr);
        var counted = Evaluator.RunCounted(expr);
        var flat = Evaluator.RunFlat(expr);

        Assert.True(plain.IsError);
        Assert.True(counted.IsError);
        Assert.True(flat.IsError);

        // Same semantic error and the same bounded text on every entry point.
        Assert.IsType<EvalError.TypeMismatch>(Innermost(plain.Error));
        Assert.IsType<EvalError.TypeMismatch>(Innermost(counted.Error));
        Assert.IsType<EvalError.TypeMismatch>(Innermost(flat.Error));

        Assert.Equal(MessageParts(plain.Error), MessageParts(counted.Error));
        Assert.Equal(MessageParts(plain.Error), MessageParts(flat.Error));

        foreach (var part in MessageParts(plain.Error))
            Assert.True(part.Length < Cap + 256, $"message part was {part.Length} units");
    }

    [Fact]
    public void SharedDagDiagnostic_RendersThroughThePublicDisplaySurface()
    {
        var run = KatLangEngine.Run(DagProgram("A + 1"));

        var failure = Assert.IsType<RunResult.EvalFailure>(run);
        var display = run.ToDisplayString();

        Assert.NotEmpty(failure.Errors);
        Assert.Contains(Marker, display);

        // The whole rendered failure stays small — before the fix this one string was the
        // 327,676-unit expansion at depth 16, and unbuildable at depth 40.
        Assert.True(display.Length < 2_048, $"display string was {display.Length} units");
    }

    [Fact]
    public void SmallValueDiagnostic_IsUnchangedAndUntruncated()
    {
        // The ordinary case must look exactly as it always did.
        var error = ExpectError("[1, 2] + 1");
        var message = Assert.IsType<EvalError.TypeMismatch>(Innermost(error)).Message;

        Assert.Equal(
            "operator `+` expects numeric scalar operands, but the left operand was a list value with 2 elements: [1, 2]",
            message);
        Assert.DoesNotContain(Marker, message);
    }

    [Fact]
    public void SequenceOperandDiagnostic_IsUnchangedAndUntruncated()
    {
        var error = ExpectError("(1, 2) * 2");
        var message = Assert.IsType<EvalError.TypeMismatch>(Innermost(error)).Message;

        Assert.Equal(
            "operator `*` expects numeric scalar operands, but the left operand was a sequence value with 2 sequence elements: (1, 2)",
            message);
        Assert.DoesNotContain(Marker, message);
    }

    // ── The filter-predicate item context ────────────────────────────────────────────────────

    [Fact]
    public void FailingFilterPredicate_ReportsTheItemBounded()
    {
        // The predicate fails on the item, so the per-item context IS produced — bounded.
        var error = ExpectError(DagProgram("Bad(v) = v + 1\n[A].filter(Bad)"));

        var parts = MessageParts(error);
        var itemContext = Assert.Single(parts, p => p.StartsWith("while evaluating filter predicate for item "));

        Assert.Contains(Marker, itemContext);
        Assert.True(itemContext.Length < Cap + 256, $"item context was {itemContext.Length} units");
        Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PassingFilterPredicate_DoesNotConstructItemDiagnostics(bool enableOptimizations)
    {
        // The per-item context is pure diagnostic work and must be built ONLY on the error
        // path: this runs once per item, and rendering an item is path-proportional, so a
        // passing predicate that formatted its item charged every successful filter for a
        // message nothing would ever read.
        var items = string.Join(", ", Enumerable.Repeat("A", 50));
        var observed = ObserveCounted(
            DagProgram($"Keep(v) = 1\n[{items}].filter(Keep).count", depth: 18),
            enableOptimizations);

        Assert.False(observed.Result.IsError);
        Assert.Equal(0, observed.Observations.FilterItemDiagnosticContextCount);
        Assert.Equal(enableOptimizations ? 1 : 0, observed.Diagnostics.FilterCountFusionHits);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void OnlyTheFailingFilterItemConstructsOneDiagnostic(bool enableOptimizations)
    {
        var source = "BadOnFive(x) = if(x == 5, 1 / 0, 1)\nrange(1, 10).filter(BadOnFive).count";
        var observed = ObserveCounted(source, enableOptimizations);

        Assert.True(observed.Result.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(observed.Result.Error));
        Assert.Equal(1, observed.Observations.FilterItemDiagnosticContextCount);
        Assert.Equal(enableOptimizations ? 1 : 0, observed.Diagnostics.FilterCountFusionHits);

        var context = Assert.Single(
            MessageParts(observed.Result.Error),
            part => part.StartsWith("while evaluating filter predicate for item "));
        Assert.Equal(
            "while evaluating filter predicate for item 4: 5 (filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)",
            context);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FirstFailingFilterItemConstructsOneDiagnostic(bool enableOptimizations)
    {
        var source = "Bad(x) = 1 / 0\nrange(1, 10).filter(Bad).count";
        var observed = ObserveCounted(source, enableOptimizations);

        Assert.True(observed.Result.IsError);
        Assert.Equal(1, observed.Observations.FilterItemDiagnosticContextCount);
        Assert.Contains(
            MessageParts(observed.Result.Error),
            part => part.StartsWith("while evaluating filter predicate for item 0: 1 "));
        Assert.Equal(enableOptimizations ? 1 : 0, observed.Diagnostics.FilterCountFusionHits);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ResourceLimitedFilterPredicateConstructsNoItemDiagnostic(bool enableOptimizations)
    {
        var source = "Recur(0) = 1\nRecur(n) = Recur(n - 1)\nBad(x) = Recur(10)\nrange(1, 3).filter(Bad).count";
        var observed = ObserveCounted(
            source,
            enableOptimizations,
            new EvaluationLimits { MaxDepth = 4 });

        Assert.True(observed.Result.IsError);
        Assert.True(observed.Result.Error.IsResourceLimit);
        Assert.Equal(0, observed.Observations.FilterItemDiagnosticContextCount);
        Assert.Equal(enableOptimizations ? 1 : 0, observed.Diagnostics.FilterCountFusionHits);
    }

    [Fact]
    public void NumericCollectionStringItem_UsesABoundedDoubleQuotedFragment()
    {
        var payload = new string('x', 100_000);
        var error = ExpectError($"sum('{payload}')");
        var context = Assert.Single(
            MessageParts(error),
            part => part.StartsWith("sum expects each collection element"));

        Assert.Contains("item 0 was string value \"", context);
        Assert.EndsWith(Marker, context);
        Assert.True(context.Length < Cap + 256, $"numeric item context was {context.Length} units");
    }

    // ── Diagnostic bounding does not touch semantic budgets ──────────────────────────────────

    [Fact]
    public void DiagnosticRendering_DoesNotConsumeSemanticBudgets()
    {
        // Rendering a message is host presentation work, not evaluation: it must not charge
        // steps, materialized items, or string units, so a program that fails with a huge
        // operand still fails with THAT error under budgets tight enough to expose any
        // charging. The formatter is reached only after the failing operation was admitted.
        var source = DagProgram("A + 1");

        foreach (var limits in new[]
        {
            new EvaluationLimits { MaxDepth = EvaluationLimits.MaxSupportedDepth },
            new EvaluationLimits { MaxCollectionItems = 2 },
            new EvaluationLimits { MaxStringLength = 16 },
            new EvaluationLimits { MaxMaterializedStringChars = 16 },
            new EvaluationLimits { MaxMaterializedItems = 4_096 },
        })
        {
            var error = ExpectError(source, limits);
            Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        }
    }

    [Fact]
    public void DiagnosticRendering_DoesNotChangeResourceVerdicts()
    {
        // A program that must fail on a resource limit still fails on THAT limit, and a
        // program that must fail semantically still fails semantically. Bounding the message
        // may not turn one into the other.
        var stepStarved = Evaluator.Run(Program(DagProgram("A + 1")), new EvaluationLimits { MaxSteps = 4 });
        Assert.True(stepStarved.IsError);
        Assert.True(stepStarved.Error.IsResourceLimit);

        var semantic = ExpectError(DagProgram("A + 1"), new EvaluationLimits { MaxSteps = 1_000_000 });
        Assert.False(semantic.IsResourceLimit);
        Assert.IsType<EvalError.TypeMismatch>(Innermost(semantic));
    }

    [Fact]
    public void DisplayConfiguration_ChangesPresentationOnly()
    {
        // MaxDisplayLength bounds the RENDERED string. It must not reclassify the error, and
        // the structured diagnostics must survive whatever the display surface decided.
        var source = DagProgram("A + 1");

        var wide = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = new EvaluationLimits() });
        var narrow = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 32 } });
        var maximum = KatLangEngine.Run(
            source,
            new RunOptions
            {
                EvaluationLimits = new EvaluationLimits
                {
                    MaxDisplayLength = EvaluationLimits.MaxSupportedDisplayLength,
                },
            });

        var wideFailure = Assert.IsType<RunResult.EvalFailure>(wide);
        var narrowFailure = Assert.IsType<RunResult.EvalFailure>(narrow);
        var maximumFailure = Assert.IsType<RunResult.EvalFailure>(maximum);

        // Same structured errors either way.
        Assert.Equal(wideFailure.Errors.Count, narrowFailure.Errors.Count);
        Assert.Equal(wideFailure.Errors[0].Message, narrowFailure.Errors[0].Message);
        Assert.Equal(wideFailure.Errors[0].Message, maximumFailure.Errors[0].Message);

        Assert.True(narrow.ToDisplayString().Length <= 32);
    }
}
