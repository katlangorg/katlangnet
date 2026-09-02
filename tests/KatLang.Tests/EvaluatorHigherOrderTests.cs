using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorHigherOrderTests
{
    // ── Higher-Order Algorithm Parameters ────────────────────────────────────

    [Fact]
    public void Eval_HigherOrder_AlgoCallsPassedAlgorithm()
    {
        // Algo = func(9); F = a + 1; Algo(F) → F(9) → 9+1 = 10
        AssertEval("Algo = func(9)\nF = a + 1\nAlgo(F)", 10);
    }

    [Fact]
    public void Eval_HigherOrder_PassAlgorithmWithArgs()
    {
        // Apply = func(x); F = a + 1; Apply(F, 5) → F(5) → 5+1 = 6
        AssertEval("Apply = func(x)\nF = a + 1\nApply(F, 5)", 6);
    }

    [Fact]
    public void Eval_HigherOrder_MultiParamNeedsExplicitCall()
    {
        // Use = func; F = a + 1; Use(F) → F has params, used bare → arityMismatch
        AssertEvalFails("Use = func\nF = a + 1\nUse(F)");
    }

    [Fact]
    public void Eval_HigherOrder_NonAlgorithmArg_NotAnAlgorithm()
    {
        // Algo = func(9); Algo(5) → 5 is not an algorithm → notAnAlgorithm
        AssertEvalFails("Algo = func(9)\nAlgo(5)");
    }

    [Fact]
    public void Eval_HigherOrder_NestedAlgorithmPassing()
    {
        // Outer = func(10); Inner = func(a); F = a * 2; Inner(F, Outer(F))
        // Outer(F) → F(10) → 20; Inner(F, 20) → F(20) → 40
        AssertEval("Outer = func(10)\nInner = func(a)\nF = a * 2\nInner(F, Outer(F))", 40);
    }

    [Fact]
    public void Eval_HigherOrder_AlgorithmWithMultipleParams()
    {
        // Algo = func(3, 4); F = a + b; Algo(F) → F(3, 4) → 7
        AssertEval("Algo = func(3, 4)\nF = a + b\nAlgo(F)", 7);
    }

    [Fact]
    public void Eval_HigherOrder_DualView_BothAlgAndValueMeaning()
    {
        // Named algorithm V = 42 resolves structurally and also evaluates to a value.
        // This is about lexical algorithm lookup, not zero-parameter inline blocks.
        // Use = func; V = 42; Use(V) → ValEnv has func=42, AlgEnv has func=V
        // Param("func") checks ValEnv first → 42
        AssertEval("Use = func\nV = 42\nUse(V)", 42);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_StructuralPropertyWithHOF()
    {
        // Structural property Apply takes a higher-order func param + value param
        // Must use same dual-view binding logic as normal user-defined calls
        var source = """
            A = { Apply = func(x)
            0 }
            F = a + 1
            A.Apply(F, 5)
            """;
        AssertEvalAllPublic(source, 6);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_StructuralPropertyPassesAlgorithm()
    {
        // Structural property Algo calls a passed algorithm with fixed value
        var source = """
            A = { Algo = func(9)
            0 }
            F = a + 1
            A.Algo(F)
            """;
        AssertEvalAllPublic(source, 10);
    }

    [Fact]
    public void Eval_HigherOrder_SequenceValueBeforeAlgorithmOnlyArg_KeepsFilteredGroupCountAsOne()
    {
        var source = """
            OccurrenceCount = filter(values, predicate).count
            OccurrenceCount((1, 2), {n:0 mod 2 == 1})
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_HigherOrder_InlinePredicate_CapturesOuterValueParameter_ReturnsKeptItemAsListElement()
    {
        var source = """
            OccurrenceCount(target) = {
                MatchesTarget(pair) = pair:1 == target:1
                filter(((1, 10), (2, 20), (2, 30)), MatchesTarget)
            }
            OccurrenceCount((2, 20))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Only (2, 20) matches; it stays an exact list element, and the list
        // [(2, 20)] passes through the user-call boundary unchanged.
        AssertListOfSequenceValueAtoms(result.Value, [2m, 20m]);
    }

    [Fact]
    public void Eval_HigherOrder_FinalSequenceValueAfterAlgorithmOnlyArgumentDoesNotUnpack()
    {
        var source = """
            Inc = x + 1
            UsePair(f, x, y) = f(x) + y
            UsePair(Inc, (10, 20))
            """;

        AssertEvalFailsWithArityMismatch(source, expected: 2, actual: 1);
    }

    [Fact]
    public void Eval_HigherOrder_GraceReordersCallableParameter()
    {
        var source = """
            IsEven = x mod 2 == 0
            Choose = if(predicate~(x), x, 0)
            Choose(3, IsEven)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_HigherOrder_FlatMultiBinderClause_UsesOrdinaryBinding()
    {
        var source = """
            IsEven = y mod 2 == 0
            Choose(x, predicate) = if(predicate(x), x, 0)
            Choose(4, IsEven)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_HigherOrder_FlatMultiBinderClause_FalsePredicate_UsesElseBranch()
    {
        var source = """
            IsEven = y mod 2 == 0
            Choose(x, predicate) = if(predicate(x), x, 0)
            Choose(3, IsEven)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_HigherOrder_FlatMultiBinderClause_DotCallUsesOrdinaryBinding()
    {
        var source = """
            Holder = {
                Apply(x, transform) = transform(x)
                Apply
            }
            Increment = y + 1
            Holder.Apply(9, Increment)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_ClauseDefinition_SingleBinder_ElaboratesToOrdinaryAlgorithm()
    {
        var source = """
            Id(x) = x
            Id(7)
            """;

        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_ClauseDefinition_SingleBinder_HigherOrderCallUsesOrdinaryBinding()
    {
        var source = """
            Apply(f) = f(4)
            Double(x) = x * 2
            Apply(Double)
            """;

        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_ClauseDefinition_SingleBinder_RejectsExtraArguments()
    {
        var error = GetEvalError("""
            Id(x) = x
            Id(1, 2)
            """);

        Assert.NotNull(error);

        while (error is EvalError.WithContext withContext)
            error = withContext.Inner;

        var arity = Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.Equal(1, arity.Expected);
        Assert.Equal(2, arity.Actual);
    }

    [Fact]
    public void Eval_DirectCall_UsesAlgorithmLevelExplicitParameters()
    {
        var source = """
            Algo(x) = {
              x + 1
            }
            Algo(6)
            """;

        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_DirectCall_MultiParameterAlgorithmLevelDefinition_SupportsBraceBodyOutputRow()
    {
        var source = """
            ImpactOnEarth(mass, height) = {
              Gravity = 9.81
              mass * Gravity * height
            }
            ImpactOnEarth(3, 2)
            """;

        AssertEval(source, 58.86m);
    }

    [Fact]
    public void Eval_DirectCall_ShorthandBodyStillWorks()
    {
        AssertEval(
            """
            Algo(x) = x + 1
            Algo(6)
            """,
            7);
    }

    [Fact]
    public void Eval_DirectCall_UsesAlgorithmArityInDiagnostics()
    {
        AssertArityMismatchMessage(
            """
            Algo(x) = {
              x + 1
            }
            Algo()
            """,
            "Callable `Algo(x)` expects 1 argument, but was called with 0 arguments.");
    }

    [Fact]
    public void Eval_DirectCall_ZeroParamBraceBody_PreservesExistingBehavior()
    {
        AssertEval(
            """
            Algo = {
              5
            }
            Algo()
            """,
            5);

        AssertArityMismatchMessage(
            """
            Algo = {
              5
            }
            Algo(6)
            """,
            "Callable `Algo` expects 0 arguments, but was called with 1 argument.");
    }

    [Fact]
    public void Eval_DirectCall_DoesNotMakeHelperCallableThroughAlgorithmName()
    {
        AssertArityMismatchMessage(
            """
            Algo = {
              Helper(x) = x * 2
              5
            }
            Algo(6)
            """,
            "Callable `Algo` expects 0 arguments, but was called with 1 argument.");
    }

    [Fact]
    public void Eval_DirectCall_PreservesHelperDotCall()
    {
        var source = """
            Algo = {
              Helper(x) = x * 2
              5
            }
            Algo.Helper(6)
            """;

        AssertEval(source, 12);
    }

    [Fact]
    public void Eval_NestedHelperCapture_RemainsCallableLocally()
    {
        AssertEval(
                """
                        Algo(x) = {
                            Prop = x + 1
                            Prop * 2
                        }
                        Algo(6)
                        """,
                14);
    }

    [Fact]
    public void Eval_ImplicitAndExplicitOuterOwnership_StayEquivalentForLocalUse()
    {
        AssertEval(
                """
                        Algo = {
                            Prop = x + 1
                            x
                        }
                        Algo(6)
                        """,
                6);

        AssertEval(
                """
                        Algo(x) = {
                            Prop = x + 1
                            x
                        }
                        Algo(6)
                        """,
                6);
    }

    [Fact]
    public void Eval_CapturedNestedProperty_DotAccess_IsLocalOnly()
    {
        AssertLocalOnlyPropertyMessage(
                """
                        Algo(x) = {
                            Prop = x + 1
                            x
                        }
                        Algo.Prop
                        """,
                "Property 'Prop' on `Algo` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
    }

    [Fact]
    public void Eval_CapturedNestedProperty_DotCall_IsLocalOnly()
    {
        AssertLocalOnlyPropertyMessage(
                """
                        Algo(x) = {
                            Prop = x + 1
                            x
                        }
                        Algo.Prop(6)
                        """,
                "Property 'Prop' on `Algo` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
    }

    [Fact]
    public void Eval_ImplicitlyOwnedCapturedNestedProperty_DotAccess_IsLocalOnly()
    {
        AssertLocalOnlyPropertyMessage(
                """
                        Algo = {
                            Prop = x + 1
                            x
                        }
                        Algo.Prop
                        """,
                "Property 'Prop' on `Algo` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
    }

    [Fact]
    public void Eval_CapturedNestedProperty_ThroughCallArguments_DotAccess_IsLocalOnly()
    {
        // The capture sits inside a call-argument OutputBundle slot; the
        // property still depends on the enclosing algorithm's parameter, so it
        // is local-only exactly like the directly written capture above.
        AssertLocalOnlyPropertyMessage(
                """
                        Algo(x) = {
                            Helper(y) = y + 10
                            Prop = Helper(x)
                            x
                        }
                        Algo.Prop
                        """,
                "Property 'Prop' on `Algo` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
    }

    [Fact]
    public void Eval_ContainerWithParametrizedChildProperty_RemainsCallable()
    {
        AssertEval(
            """
            Algo = {
              Prop(x, y) = 7
            }
            Algo.Prop(1, 2)
            """,
            7);
    }

    [Fact]
    public void Eval_PlainContainerAlgorithm_RemainsValid()
    {
        AssertEval(
            """
            Algo = {
              Prop = 7
            }
            Algo.Prop
            """,
            7);
    }

    [Fact]
    public void Eval_DirectCall_NestedAlgorithmLevelDefinition_PreservesNestedCalls()
    {
        var source = """
            Outer = {
              Inner(x) = {
                x + 10
              }
              Inner(5)
            }
            Outer, Outer.Inner(5)
            """;

        AssertEval(source, 15, 15);
    }

    [Fact]
    public void Eval_ConditionalBranchProperty_IsLocalOnly()
    {
        AssertLocalOnlyPropertyMessage(
                """
                        Outer(0) = {
                            Inner = 1
                            0
                        }
                        Outer(x) = {
                            Inner = x + 1
                            x
                        }
                        Outer.Inner
                        """,
                "Property 'Inner' on `Outer` is local-only because properties defined inside conditional algorithms are not publicly visible.");
    }

    [Fact]
    public void Eval_ConditionalBranchProperties_AreNeverExposedThroughParent()
    {
        AssertLocalOnlyPropertyMessage(
                """
                        Outer(0) = {
                            First = 1
                            0
                        }
                        Outer(x) = {
                            Second = x + 1
                            x
                        }
                        Outer.Second
                        """,
                "Property 'Second' on `Outer` is local-only because properties defined inside conditional algorithms are not publicly visible.");
    }

    [Fact]
    public void Eval_ManualAlgorithmWithExplicitParametersWithoutOutput_IsRejected()
    {
        var invalid = new Algorithm.User(
            Parent: null,
            Parameters: Algorithm.NormalParameters(["x"]),
            Opens: [],
            Properties:
            [
                new Property(
                    "Prop",
                    new Algorithm.User(
                        Parent: null,
                        Parameters: [],
                        Opens: [],
                        Properties: [],
                        Output: [new Expr.Num(7m)]))
            ],
            Output: [])
        {
            ExplicitParameters = [new ParameterDeclaration("x", new SourceSpan(1, 6, 1, 6))]
        };

        var result = Evaluator.Run(new Expr.AlgorithmExpr(invalid));

        Assert.True(result.IsError);
        Assert.IsType<EvalError.ExplicitParametersRequireOutput>(result.Error);
        Assert.Equal(
            AlgorithmValidation.ExplicitParametersRequireOutputMessage,
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void Eval_ManualOutputDotCall_IsOrdinaryStructuralCall()
    {
        // `Output` is an ordinary member name: a hand-built dot-call binds the
        // structural property named `Output` exactly like any other member.
        var callee = new Algorithm.User(
            Parent: null,
            Parameters: Algorithm.NormalParameters(["x"]),
            Opens: [],
            Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1m))]);

        var container = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Output", callee)],
            Output: []);

        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Algo", container)],
            Output:
            [
                new Expr.DotCall(
                    new Expr.Resolve("Algo"),
                    "Output",
                    new OutputBundle([new Expr.Num(6m)]))
            ]);

        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(root));

        Assert.False(result.IsError);
        Assert.Equal([7m], result.Value);
    }

    [Fact]
    public void Eval_ClauseDefinition_SequenceValuePattern_RemainsConditionalWholeArgument()
    {
        var source = """
            Stats(x, (acc, counter)) = (x + acc, counter + 1)
            Stats(3, (0, 0))
            """;

        AssertEval(source, 3, 1);
    }

    [Fact]
    public void Eval_ClauseGroup_DoubleParenSequenceValuePattern_MatchesSingleBinderArity()
    {
        var source = """
            MarkSequenceValueRange((a, b, c)) = 1
            MarkSequenceValueRange(x) = 0
            MarkSequenceValueRange(5)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_ClauseGroup_DoubleParenSequenceValuePattern_FallsThroughForListRangeArgument()
    {
        // range returns an exact list value, and multi-clause conditional
        // sequence-value patterns match sequence values only (list patterns are
        // deferred by design), so the list argument takes the fallback clause.
        var source = """
            MarkSequenceValueRange((a, b, c)) = 1
            MarkSequenceValueRange(x) = 0
            MarkSequenceValueRange(range(1, 3))
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_ClauseGroup_DoubleParenSequenceValuePattern_MatchesSpreadRangeArgument()
    {
        // Spreading the range list inside parentheses builds a sequence value
        // (1, 2, 3), which the sequence-value pattern clause matches.
        var source = """
            MarkSequenceValueRange((a, b, c)) = 1
            MarkSequenceValueRange(x) = 0
            MarkSequenceValueRange((range(1, 3)*))
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_ClauseGroup_LiteralThenPlainBinder_RemainsConditional()
    {
        var source = """
            F(0) = 0
            F(x) = 1
            F(2)
            """;

        AssertEval(source, 1);
    }

    // ── Inline block arguments (higher-order) ────────────────────────────────

    [Fact]
    public void Eval_InlineBlock_PassedInParens()
    {
        // Apply = func(x); Apply({a + 1}, 5) → {a+1}(5) → 6
        AssertEval("Apply = func(x)\nApply({a + 1}, 5)", 6);
    }

    [Fact]
    public void Eval_InlineBlock_DotCall_PassedInParens()
    {
        // A.Apply = func(x); A.Apply({a + 1}, 5) → 6
        var source = """
            A = { Apply = func(x)
            0 }
            A.Apply({a + 1}, 5)
            """;
        AssertEvalAllPublic(source, 6);
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamSingleOutputInParens_RemainsValueStructure()
    {
        // Zero-parameter inline blocks stay value/output structures in
        // higher-order argument position.
        AssertEval("Apply(f) = f\nApply({123})", 123);
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamSingleOutput_CrossesHigherOrderBoundary()
    {
        // An algorithm block always provides its contained Algorithm on the
        // algorithm channel, regardless of parameter/declaration/output
        // count: `f()` invokes the zero-parameter brace algorithm exactly
        // like a named zero-parameter property.
        AssertEval("Apply(f) = f()\nApply({123})", 123);
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamMultiOutputInParens_RemainsValueStructure()
    {
        // Output count does not change higher-order binding mode.
        AssertEval("Apply(f) = f\nApply({1, 2})", 1, 2);
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamMultiOutput_CrossesHigherOrderBoundary()
    {
        // Output count never gates algorithm identity: calling the bound
        // multi-output brace algorithm emits its outputs, observed at the
        // call's value boundary as one sequence value.
        AssertEval("Apply(f) = f()\nApply({1, 2})", 1, 2);
    }

    [Fact]
    public void Eval_InlineBlock_TrailingBrace_SingleArg()
    {
        // Algo = func(9); Algo{a + 1} → {a+1}(9) → 10
        AssertEval("Algo = func(9)\nAlgo{a + 1}", 10);
    }

    [Fact]
    public void Eval_InlineBlock_TrailingBrace_ZeroParam()
    {
        // Use = func; Use{42} → 42
        AssertEval("Use = func\nUse{42}", 42);
    }

    [Fact]
    public void Eval_InlineBlock_TrailingBrace_ArityMismatch()
    {
        // Use = func; Use{a + 1} → block has param a, bare usage → arityMismatch
        AssertEvalFails("Use = func\nUse{a + 1}");
    }
}
