using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorConditionalTests
{
    // ── Clause definitions and conditional algorithms ───────────────────────

    [Fact]
    public void Eval_ClauseDefinition_KCombinator_OrdinarySingleClause()
    {
        // K(a, b) = a  ⟹  K(10, 20) => 10
        var source = """
            K(a, b) = a
            K(10, 20)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_ClauseDefinition_SecondProjection_OrdinarySingleClause()
    {
        // Verify we can return the second binding too
        var source = """
            Snd(a, b) = b
            Snd(10, 20)
            """;
        AssertEval(source, 20);
    }

    [Fact]
    public void Eval_RepeatedBinder_OrdinaryArgumentsRequireEquality()
    {
        AssertEval(
            """
            F(x, x) = x
            F(1, 1)
            """,
            1);

        var error = GetEvalError(
            """
            F(x, x) = x
            F(1, 2)
            """);
        Assert.IsType<EvalError.BadArity>(Innermost(error!));
    }

    [Fact]
    public void Eval_RepeatedBinder_SequenceValuePatternRequiresEquality()
    {
        AssertEval(
            """
            F((x, x)) = x
            F((1, 1))
            """,
            1);

        var error = GetEvalError(
            """
            F((x, x)) = x
            F((1, 2))
            """);
        Assert.IsType<EvalError.BadArity>(Innermost(error!));
    }

    [Fact]
    public void Eval_RepeatedBinder_AcrossNestedPatternRequiresEquality()
    {
        AssertEval(
            """
            F(x, (x)) = x
            F(1, (1))
            """,
            1);

        var error = GetEvalError(
            """
            F(x, (x)) = x
            F(1, (2))
            """);
        Assert.IsType<EvalError.BadArity>(Innermost(error!));
    }

    [Fact]
    public void Eval_RepeatedBinder_UsesStructuralSequenceValueEquality()
    {
        AssertEval(
            """
            F(x, x) = x
            F((1, 2), (1, 2))
            """,
            1, 2);

        var error = GetEvalError(
            """
            F(x, x) = x
            F((1, 2), (1, 3))
            """);
        Assert.IsType<EvalError.BadArity>(Innermost(error!));
    }

    [Fact]
    public void Eval_RepeatedBinder_RetainsFirstEqualBinding()
    {
        AssertEvalString(
            """
            F(x, x) = x.string
            F(1.0, 1.00)
            """,
            "1.0");
    }

    [Fact]
    public void Eval_RepeatedBinder_AlgorithmOnlyArgumentsReportUnsupportedEquality()
    {
        var error = GetEvalError(
            """
            Inc(x) = x + 1
            ApplySame(f, f) = f(1)
            ApplySame(Inc, Inc)
            """);

        var typeMismatch = Assert.IsType<EvalError.TypeMismatch>(Innermost(error!));
        Assert.Contains("algorithm-only arguments", typeMismatch.Message);
    }

    [Fact]
    public void Eval_RepeatedBinder_ConditionalFallbackSelectsNextClause()
    {
        AssertEval(
            """
            Equal(x, x) = 1
            Equal(x, y) = 0
            Equal(1, 1)
            Equal(1, 2)
            """,
            1, 0);
    }

    [Fact]
    public void Eval_RepeatedBinder_SequenceValueConditionalFallbackSelectsNextClause()
    {
        AssertEval(
            """
            SamePair((x, x)) = 1
            SamePair((x, y)) = 0
            SamePair((5, 5))
            SamePair((5, 6))
            """,
            1, 0);
    }

    [Fact]
    public void Eval_SameParameterNameInSeparateAlgorithms_RemainsIndependent()
    {
        AssertEval(
            """
            A(x) = x
            B(x) = x + 1
            A(4)
            B(4)
            """,
            4, 5);
    }

    [Fact]
    public void Eval_OrdinarySingletonGroupParameter_RejectsMultiItemGroup()
    {
        // K(a, (b)) = a  ⟹  K(1, (2, 3)) should fail
        // because (b) is a 1-element sequence-value pattern that does not match (2, 3).
        var source = """
            K(a, (b)) = a
            K(1, (2, 3))
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.WithContext>(error);
        // The mismatch is attributed to the nested pattern `(b)` (a
        // SequenceValueParameterBindingContext layer may sit between the call
        // context and the innermost arity error).
        var inner = Innermost(error!);
        Assert.True(inner is EvalError.ArityMismatch or EvalError.BadArity);
    }

    [Fact]
    public void Eval_ClauseDefinition_OrdinarySingleClause_AcceptsSequenceValueSecondArgument()
    {
        // K(a, b) = a  ⟹  K(1, (2, 3)) => 1
        // Ordinary call binding still accepts a sequence-value second argument as one value.
        var source = """
            K(a, b) = a
            K(1, (2, 3))
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_OrdinarySingletonGroupParameter_MatchesNormalizedSingleton()
    {
        // K(a, (b)) = a  ⟹  K(1, (2)) => 1
        // (2) normalizes to Atom(2); (b) is a 1-element sequence-value pattern
        // that matches the normalized singleton.
        var source = """
            K(a, (b)) = a
            K(1, (2))
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Conditional_MultipleBranches_LiteralMatch()
    {
        // Else(1, (a, b)) = a
        // Else(c, (a, b)) = b
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(1, (2, 3))
            """;
        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_Conditional_MultipleBranches_FallbackBranch()
    {
        // Same as above but first branch doesn't match (c != 1)
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(0, (2, 3))
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Conditional_NonExhaustive_NoMatch()
    {
        // Sign(1) = 1
        // Sign(-1) = -1
        // Sign(0) should fail with NoMatchingBranch
        var source = """
            Sign(1) = 1
            Sign(-1) = -1
            Sign(0)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.WithContext>(error);
        var inner = ((EvalError.WithContext)error!).Inner;
        Assert.IsType<EvalError.NoMatchingBranch>(inner);
    }

    [Fact]
    public void Eval_Conditional_NonExhaustive_MatchExists()
    {
        var source = """
            Sign(1) = 100
            Sign(-1) = -100
            Sign(1)
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_Conditional_BareReference_NoMatchingBranch()
    {
        // A bare property-style reference to a clause family cannot select a
        // branch; it must fail like no-argument dot-call access instead of
        // silently forcing the conditional's empty output list.
        var source = """
            Sign(1) = 1
            Sign(-1) = -1
            Sign
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error!));
    }

    [Fact]
    public void Eval_Conditional_BareReferenceInSequenceBuiltinArg_NoMatchingBranch()
    {
        // Forcing a conditional through a sequence-builtin collection argument
        // fails instead of silently contributing nothing to the collection.
        var source = """
            Sign(1) = 1
            Sign(-1) = -1
            sum(Sign)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error!));
    }

    [Fact]
    public void Eval_Conditional_HigherOrderThunkReference_NoMatchingBranch()
    {
        // A conditional bound as a higher-order argument fails when the callee
        // references it as a bare zero-argument thunk.
        var source = """
            Sign(1) = 1
            Sign(-1) = -1
            Apply = f
            Apply(Sign)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error!));
    }

    [Fact]
    public void Eval_Conditional_FirstMatchWins()
    {
        // F(x) = 1  (catch-all, always matches)
        // F(1) = 2  (never reached)
        // F(1) => 1 (first branch wins)
        var source = """
            F(x) = 1
            F(1) = 2
            F(1)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Conditional_NestedPatternShapeMismatch()
    {
        // Else expects (c, (a, b)) but we pass three flat args
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(1, 2, 3)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.WithContext>(error);
        var inner = ((EvalError.WithContext)error!).Inner;
        Assert.IsType<EvalError.NoMatchingBranch>(inner);
    }

    [Fact]
    public void Eval_Conditional_OrdinaryAlgorithmUnchanged()
    {
        // Ordinary (non-conditional) algorithms should still work
        var source = """
            Add = a + b
            Add(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_Conditional_BinderUsedInExpression()
    {
        // Branch body can use binders in arithmetic
        var source = """
            Double(x) = x + x
            Double(5)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Conditional_NegativeLiteralPattern()
    {
        var source = """
            F(-1) = 100
            F(x) = 0
            F(-1)
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_Conditional_NegativeLiteralPattern_NoMatch()
    {
        var source = """
            F(-1) = 100
            F(x) = 0
            F(5)
            """;
        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_Conditional_MultipleOutputInBranch()
    {
        // Branch body returns multiple values
        var source = """
            Swap(a, b) = b, a
            Swap(1, 2)
            """;
        AssertEval(source, 2, 1);
    }

    [Fact]
    public void Eval_Conditional_DirectCountedCall_PreservesSelectedBranchOutputCount()
    {
        var source = """
            Choose(1) = 10, 20
            Choose(x) = x, x
            Choose(1).count
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_Conditional_DotCallAccess()
    {
        // Access conditional property via dot syntax with args
        var source = """
            M = { F(x) = x + 1
            F }
            M.F(10)
            """;
        AssertEval(source, 11);
    }

    [Fact]
    public void Eval_PublicConditional_DotCallAccess()
    {
        var source = """
                Lib = {
                    public Sign(1) = 100
                    public Sign(x) = 0
                }
                Lib.Sign(1), Lib.Sign(2)
                """;

        AssertEval(source, 100, 0);
    }

    [Fact]
    public void Eval_Conditional_SingleArg()
    {
        // Single argument pattern
        var source = """
            Inc(x) = x + 1
            Inc(5)
            """;
        AssertEval(source, 6);
    }

    // ── Regression: conditional branch body accesses enclosing scope (issue #19) ──

    [Fact]
    public void Eval_Conditional_BranchBody_AccessesSiblingProperty()
    {
        // Branch bodies must be able to read sibling properties of the enclosing algorithm.
        // Before the fix, branch.Body had no parent wiring → UnknownName for Price.
        var source = """
            Price = 0.80
            Discount(1) = Price * 0.9
            Discount(x) = Price
            Discount(1)
            """;
        AssertEval(source, 0.72m);
    }

    [Fact]
    public void Eval_Conditional_BranchBody_AccessesSiblingProperty_AllBranches()
    {
        // Verify every branch (not just the first) can access sibling properties.
        var source = """
            TomatoPrice = 1.20
            ApplePrice = 0.80
            CucumberPrice = 0.60
            Expense(1, qty) = TomatoPrice * qty
            Expense(2, qty) = ApplePrice * qty
            Expense(3, qty) = CucumberPrice * qty
            Expense(1, 10), Expense(2, 10), Expense(3, 10)
            """;
        AssertEval(source, 12.0m, 8.0m, 6.0m);
    }

    [Fact]
    public void Eval_Conditional_BranchBody_AccessesGrandparentProperty()
    {
        // Sibling properties defined one level higher than the conditional algorithm
        // must also be reachable from branch bodies.
        var source = """
            Outer = {
                Price = 2.50
                Inner = {
                    F(x) = Price * x
                    F(4)
                }
                Inner
            }
            Outer
            """;
        AssertEval(source, 10.0m);
    }

    [Fact]
    public void Eval_Conditional_BranchBody_BinderAndSiblingCombined()
    {
        // Branch body uses both a pattern binder (qty) and a sibling property (Rate).
        var source = """
            Rate = 1.5
            Scale(qty) = Rate * qty
            Scale(4)
            """;
        AssertEval(source, 6.0m);
    }

    // ── Full-input-specification rule: conditional branch params ─────────

    [Fact]
    public void Eval_ClauseDefinition_OrdinarySingleClause_IgnoredBinderPreserved()
    {
        // K(a, b) = a — b is intentionally unused, no error
        var source = """
            K(a, b) = a
            K(10, 20)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Conditional_FullPattern_StructuredBranches()
    {
        // Each branch pattern fully describes accepted input shape
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(1, (20, 30))
            """;
        AssertEval(source, 20);
    }

    [Fact]
    public void Eval_Conditional_FullPattern_CatchAllBranch()
    {
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(0, (20, 30))
            """;
        AssertEval(source, 30);
    }

    [Fact]
    public void Eval_Conditional_ExtraImplicitParam_Rejected()
    {
        // F(1, a) = a + b — b is not bound by pattern and not a resolved name.
        //
        // Track 13: the rejection is a FRONT-END diagnostic (clause bodies take
        // binders only from their pattern, so a free identifier is an
        // elaboration error, not an evaluator one). The test previously routed
        // through a helper that ignored parser diagnostics and evaluated the
        // recovery tree, so it asserted "something failed" without saying which
        // layer decided. Assert the owning layer explicitly.
        var source = """
            F(1, a) = a + b
            F(1, 5)
            """;

        var diagnostics = SourceProvenance.ExpectFrontEndError(source);
        Assert.Contains(
            diagnostics,
            d => d.Message.Contains("is used in conditional branch", StringComparison.Ordinal)
                && d.Message.Contains("not declared in the branch pattern", StringComparison.Ordinal));
    }

    [Fact]
    public void Eval_Conditional_FreeIdResolvedLexically_Succeeds()
    {
        // Pattern binder + lexically resolvable name: Rate is a sibling property
        var source = """
            Rate = 2
            F(x) = x * Rate
            F(5)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Conditional_OrdinaryAlgorithmStillInfersParams()
    {
        // Ordinary (non-conditional) algorithms still infer implicit parameters
        var source = """
            Add = a + b
            Add(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_Conditional_OrdinaryAlgorithmGraceStillWorks()
    {
        // Grace still works in ordinary algorithms
        var source = """
            Sub = a - ~b
            Sub(3, 10)
            """;
        AssertEval(source, 7);
    }

    // ── Uniform top-level output arity: valid multi-output branches ─────

    [Fact]
    public void Eval_Conditional_SameOutputArity2_BothBranches()
    {
        // Both branches return top-level arity 2 — valid
        var source = """
            F(1, x) = x, x + 1
            F(2, x) = 0, x
            F(1, 5)
            """;
        AssertEval(source, 5, 6);
    }

    [Fact]
    public void Eval_Conditional_SameOutputArity2_SecondBranch()
    {
        // Second branch matches, also returns arity 2
        var source = """
            F(1, x) = x, x + 1
            F(2, x) = 0, x
            F(2, 5)
            """;
        AssertEval(source, 0, 5);
    }

    [Fact]
    public void Eval_Conditional_SameOutputArity1_WithSiblingProperties()
    {
        // Classic example: same output arity 1 across branches with sibling properties
        var source = """
            TomatoPrice = 1.20
            ApplePrice = 0.80
            Expense(1, qty) = TomatoPrice * qty
            Expense(2, qty) = ApplePrice * qty
            Expense(1, 10)
            """;
        AssertEval(source, 12.0m);
    }

    [Fact]
    public void Eval_Conditional_SameOutputArity2_NestedStructureDiffers()
    {
        // Both branches return top-level arity 2; nested internal structure differs — valid
        var source = """
            G(1, x) = x, (x + 1, x + 2)
            G(2, x) = x, x * 2
            G(1, 10)
            """;
        AssertEval(source, 10, 11, 12);
    }

    // ── Additional conditional algorithm tests ──────────────────────────────

    [Fact]
    public void Eval_Conditional_DefinitionAndCallDisambiguated()
    {
        // First two lines: definitions; third line: call
        var source = """
            F(1) = 100
            F(x) = 0
            F(1)
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_Conditional_CallInExpressionContext()
    {
        // G = F(1) is a property definition where F(1) is a call expression
        var source = """
            F(1) = 100
            F(x) = 0
            G = F(1)
            G
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_ConditionalSugar_FirstMatchWins()
    {
        var source = """
            F(x) = 1
            F(1) = 2
            F(1)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_ConditionalSugar_ExtraImplicitParam_Rejected()
    {
        // b is not bound in the pattern; should be rejected
        var source = """
            F(1, a) = a + b
            F(2, a) = a
            F(1, 5)
            """;
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);
        Assert.Contains(parseResult.Diagnostics, d =>
            d.Message.Contains("Identifier 'b' is used in conditional branch 'F'") &&
            d.Message.Contains("not declared in the branch pattern") &&
            d.Message.Contains("A(y) = y"));
    }

    [Fact]
    public void Eval_Conditional_ClauseSyntax_MultipleCallResults()
    {
        // Clause-style branch syntax works for multiple calls
        var source = """
            F(1) = 100
            F(x) = 0
            F(1), F(42)
            """;
        AssertEval(source, 100, 0);
    }
}
