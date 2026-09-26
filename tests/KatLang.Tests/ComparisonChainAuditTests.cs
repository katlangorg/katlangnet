using System.Numerics;
using KatLang.Optimizations.Loops;
using KatLang.Semantics;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The September 2026 hostile audit of comparison chaining, prompted by a downstream integration
/// review sentence claiming "`a &lt; b == c` is false" — a claim no chain can satisfy without its
/// operand values, since `a &lt; b == c` is the two adjacent comparisons `a &lt; b` and `b == c`.
/// The audit found no layer that reads a chain left-associatively; this class pins the audited
/// examples end to end so none can start to: ONE flat <see cref="Expr.Comparison"/> node per
/// written chain, adjacent-pair truth on every execution strategy, the left-associated reading
/// reachable only through written parentheses (and then disagreeing), every operand evaluated
/// once, left to right, past a <c>false</c> link and stopped by an error, and an editor model that
/// classifies every chain operand from the public AST. The same audited sources are Lean/C#
/// differential cases (<c>special__chainLtThenEq</c>, <c>special__chainLtThenGt</c>,
/// <c>special__chainNeThenLt</c>, <c>special__chainFalseFirstThenEqFalse</c>) whose Lean programs
/// are derived from the parsed chain.
/// </summary>
public class ComparisonChainAuditTests
{
    /// <summary>
    /// The audited chains: source, the written operators, the chain's value, and what the
    /// left-associated reading <c>(a op1 b) op2 c</c> would produce instead — a different Boolean
    /// or the ordering rejection of a Boolean operand. Every row discriminates the two readings.
    /// </summary>
    public static TheoryData<string, ComparisonOp[], bool, string> AuditedChains() => new()
    {
        { "1 < 2 == 2", [ComparisonOp.Lt, ComparisonOp.Eq], true, "false" },
        { "1 < 2 < 3", [ComparisonOp.Lt, ComparisonOp.Lt], true, "type" },
        { "1 < 2 > 1", [ComparisonOp.Lt, ComparisonOp.Gt], true, "type" },
        { "1 == 1 < 2", [ComparisonOp.Eq, ComparisonOp.Lt], true, "type" },
        { "1 != 2 < 3", [ComparisonOp.Ne, ComparisonOp.Lt], true, "type" },
        { "2 < 1 == false", [ComparisonOp.Lt, ComparisonOp.Eq], false, "true" },
        { "3 > 2 == 1 < 2", [ComparisonOp.Gt, ComparisonOp.Eq, ComparisonOp.Lt], false, "type" },
    };

    [Theory]
    [MemberData(nameof(AuditedChains))]
    public void EachAuditedChain_IsOneFlatNode_WithItsWrittenOperatorsInOrder(
        string source, ComparisonOp[] ops, bool expected, string leftAssociated)
    {
        _ = (expected, leftAssociated);
        var chain = Assert.IsType<Expr.Comparison>(Assert.Single(SourceProvenance.ParseValid(source).Root.Output));

        Assert.Equal(ops, chain.Links.Select(link => link.Op));
        // Every operand is a plain numeric or Boolean literal: nothing nested, nothing lowered.
        Assert.All(chain.Links.Select(link => link.Operand).Prepend(chain.First),
            operand => Assert.True(operand is Expr.Num or Expr.BoolLiteral, $"unexpected operand {operand.GetType().Name} in `{source}`"));
        // The diagnostic rendering reads back as the flat chain that was written.
        Assert.Equal(source, ExprNameRenderer.Render(chain, ExprNameMode.DiagnosticName));
    }

    [Theory]
    [MemberData(nameof(AuditedChains))]
    public async Task EachAuditedChain_EvaluatesByAdjacentPairs_OnEveryStrategy(
        string source, ComparisonOp[] ops, bool expected, string leftAssociated)
    {
        _ = (ops, leftAssociated);
        var display = expected ? "true" : "false";
        Assert.Equal(display, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
        Assert.Equal(display, Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source)).ToDisplayString());

        // The async twin and the planned loop reach the same verdict.
        var ast = AsyncEvaluationHarness.Ast(source);
        var (sync, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (twin, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(twin));

        var loop = new Expr.AlgorithmExpr(SourceProvenance.ParseValid($"Step = {{\n    n + if({source}, 1, 0)\n}}\nStep.repeat(3, 0)").Root);
        var diagnostics = new LoopOptimizationDiagnostics();
        var (planned, _) = Evaluator.RunCountedObserved(loop, enableOptimizations: true, loopDiagnostics: diagnostics);
        var (generic, _) = Evaluator.RunCountedObserved(loop, enableOptimizations: false);
        var iterations = expected ? 3 : 0;
        Assert.Equal($"ok raw={iterations} n=1", AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal($"ok raw={iterations} n=1", AsyncEvaluationHarness.NeutralOf(generic));
        var snapshot = diagnostics.GetSnapshot();
        Assert.Equal(1, snapshot.OptimizedLoopHits);
        Assert.Equal(0, snapshot.PlannedExpressionFallbacks);
    }

    [Theory]
    [MemberData(nameof(AuditedChains))]
    public void TheLeftAssociatedReading_ExistsOnlyThroughWrittenParentheses_AndDisagrees(
        string source, ComparisonOp[] ops, bool expected, string leftAssociated)
    {
        _ = expected;
        // The left-associated reading written out: `((a op1 b) op2 c) op3 d` — every link but the
        // last a parenthesized comparison, which is an ordinary Boolean operand of the next one.
        var parts = source.Split(' ');
        var parenthesized = new string('(', ops.Length - 1) + parts[0];
        for (var link = 0; link < ops.Length; link++)
            parenthesized += $" {parts[(2 * link) + 1]} {parts[(2 * link) + 2]}" + (link < ops.Length - 1 ? ")" : "");

        var outer = Assert.IsType<Expr.Comparison>(Assert.Single(SourceProvenance.ParseValid(parenthesized).Root.Output));
        Assert.Single(outer.Links);
        Assert.IsType<Expr.Comparison>(outer.First);

        var result = KatLangEngine.Run(parenthesized);
        if (leftAssociated == "type")
        {
            var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
            Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        }
        else
        {
            Assert.Equal(leftAssociated, Assert.IsType<RunResult.Success>(result).ToDisplayString());
        }

        Assert.NotEqual(KatLangEngine.Run(source).ToDisplayString(), result.ToDisplayString());
    }

    /// <summary>
    /// The questioned SHAPE `a &lt; b == c` with observable operands: host operations record every
    /// evaluation. Every operand runs exactly once and left to right — the middle operand's value
    /// serves both links — a <c>false</c> first link never short-circuits the second, and an error
    /// stops the chain before any later operand runs. Generic, planned-free optimized, and async
    /// evaluation agree on value, error, and trace.
    /// </summary>
    [Theory]
    [InlineData("One() < Two() == Two2()", "1 2 2'", "true", null)]
    [InlineData("One() < Two() == Three()", "1 2 3", "false", null)]
    [InlineData("Two() < One() == One2()", "2 1 1'", "false", null)]
    [InlineData("Two() < One() == Two2()", "2 1 2'", "false", null)]
    [InlineData("One() < Two() == true < Three()", "1 2 3", null, KatLangErrorCode.TypeMismatch)]
    [InlineData("One() < true == Two()", "1", null, KatLangErrorCode.TypeMismatch)]
    [InlineData("Two() < One() == 1 / 0 == Three()", "2 1", null, KatLangErrorCode.DivisionByZero)]
    public async Task TheQuestionedShape_EvaluatesEveryOperandOnce_LeftToRight_EagerPastFalse_StoppedByErrors(
        string chain, string expectedTrace, string? expectedDisplay, KatLangErrorCode? expectedError)
    {
        foreach (var mode in new[] { "generic", "optimized", "async" })
        {
            var trace = new List<string>();
            HostOperation Traced(string name, string label, Decimal128 value)
                => mode == "async"
                    ? HostOperation.CreateAsync(name, async (_, _) => { await Task.Yield(); trace.Add(label); return new Result.Atom(value); })
                    : HostOperation.Create(name, (_, _) => { trace.Add(label); return new Result.Atom(value); });
            var operations = HostOperations.Create(
                Traced("One", "1", 1), Traced("One2", "1'", 1), Traced("Two", "2", 2), Traced("Two2", "2'", 2), Traced("Three", "3", 3));
            var parsed = Parser.Parse(chain, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, chain + ": " + string.Join(';', parsed.Diagnostics));
            var ast = new Expr.AlgorithmExpr(parsed.Root);

            var result = mode == "async"
                ? (await Evaluator.RunCountedObservedAsync(ast, hostOperations: operations)).Result
                : Evaluator.RunCountedObserved(ast, enableOptimizations: mode == "optimized", hostOperations: operations).Result;

            Assert.Equal(expectedTrace, string.Join(' ', trace));
            Assert.Equal(expectedError.HasValue, result.IsError);
            if (expectedError is { } code)
                Assert.Equal(code, result.Error.Code);
            else
                Assert.Equal(expectedDisplay == "true", Assert.IsType<Result.Bool>(result.Value.Value).Value);
        }
    }

    /// <summary>
    /// A link's rejection names the two ADJACENT operands it compared — never a left-associated
    /// grouping of the chain so far.
    /// </summary>
    [Theory]
    [InlineData("1 < 2 == true < 3", "true < 3")]
    [InlineData("1 < 2 > false", "2 > false")]
    [InlineData("1 == 1 < true", "1 < true")]
    public void ALinkRejection_NamesItsTwoAdjacentOperands(string source, string link)
    {
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.Contains($"while evaluating `{link}`", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("(1 < 2)", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("(1 == 1)", error.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// Editor integrations need not recreate chain semantics: the public AST carries the chain as
    /// one <see cref="Expr.Comparison"/>, and the semantic model classifies every operand — a
    /// property, a call, a dot member, a selection target, a parameter — at its exact site, in
    /// source order, with no unresolved or indeterminate site.
    /// </summary>
    [Fact]
    public void TheEditorModel_ClassifiesEveryChainOperand_AtItsSite()
    {
        const string source = "P = 2\nF(x) = x + 1\nObj = { V = 3 }\nXs = [1, 2]\nCheck(y) = F(P) < Obj.V <= Xs:1 == P != y\nCheck(9)";
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var check = Assert.Single(parsed.Root.Properties, property => property.Name == "Check");
        var chain = Assert.IsType<Expr.Comparison>(Assert.Single(check.Value.Output));
        Assert.Equal([ComparisonOp.Lt, ComparisonOp.Le, ComparisonOp.Eq, ComparisonOp.Ne], chain.Links.Select(link => link.Op));

        var model = SemanticModelBuilder.Build(parsed);
        var line5 = model.IdentifierResolutions.Where(resolution => resolution.Occurrence.Span.Start.Line == 5).ToList();
        Assert.Equal(
            [
                "Check:PropertyDefinition", "y:ExplicitParameterDefinition", "F:PropertyReference", "P:PropertyReference",
                "Obj:PropertyReference", "V:PropertyReference", "Xs:PropertyReference", "P:PropertyReference",
                "y:ExplicitParameterReference",
            ],
            line5.Select(resolution => $"{resolution.Occurrence.Name}:{resolution.Classification}"));
        Assert.True(line5.Zip(line5.Skip(1)).All(pair => pair.First.Occurrence.Span.Start < pair.Second.Occurrence.Span.Start));
        Assert.All(line5.Where(resolution => resolution.Classification == IdentifierClassification.PropertyReference),
            resolution => Assert.NotNull(resolution.ResolvedDeclaration));
    }
}
