using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorProgramOutputTests
{
    [Fact]
    public void Eval_MixedOutput_LeadingNonSpreadEmptyIsVisibleSlot()
    {
        // A normal non-spread `()` output is a visible slot beside `1`, not dropped.
        var result = EvalFull("()\n1");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Equal(2, outer.Items.Count);
        Assert.Empty(Assert.IsType<Result.SequenceValue>(outer.Items[0]).Items);
        Assert.Equal(1m, Assert.IsType<Result.Atom>(outer.Items[1]).Value);
    }

    [Fact]
    public void Eval_MixedOutput_MiddleNonSpreadEmptyIsVisibleSlot()
    {
        var result = EvalFull("1\n()\n2");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Equal(3, outer.Items.Count);
        Assert.Equal(1m, Assert.IsType<Result.Atom>(outer.Items[0]).Value);
        Assert.Empty(Assert.IsType<Result.SequenceValue>(outer.Items[1]).Items);
        Assert.Equal(2m, Assert.IsType<Result.Atom>(outer.Items[2]).Value);
    }

    [Fact]
    public void Eval_MixedOutput_SpreadOfEmptyContributesNoSlot()
        // Only an explicit spread drops to zero: `()*` adds no slot, so `()*` then `1` is just `1`.
        => AssertEval("()*\n1", 1);

    [Fact]
    public void Eval_PropertyOnlyProgram_HasNoDefinedOutput()
        => AssertMissingOutputMessage(
            "T = 4",
            RunResult.NoProgramOutput.DefaultMessage);

    [Fact]
    public void Eval_PropertyOnlyProgram_WithTrailingOutput_ReturnsValue()
        => AssertEval("T = 4\nT", 4);

    [Fact]
    public void Eval_PropertyOnlyProgram_WithEmptySequenceOutput_ReturnsEmptySequence()
        => AssertEvalEmptyOutput("T = 4\n()");

    [Fact]
    public void Eval_PropertyValue_DoesNotCompareEqualToEmptySequence()
        => AssertEval("T = 4\nT == ()", 0);

    [Fact]
    public void Eval_MultiplePropertyDefinitionsWithoutOutput_HasNoDefinedOutput()
        => AssertMissingOutputMessage(
            """
            Price = 10
            Tax = 2
            Total = Price + Tax
            """,
            RunResult.NoProgramOutput.DefaultMessage);

    [Fact]
    public void Eval_MultiplePropertyDefinitionsWithOutput_ReturnsValue()
        => AssertEval(
            """
            Price = 10
            Tax = 2
            Total = Price + Tax
            Total
            """,
            12);

    [Fact]
    public void Eval_Empty_IsOrdinaryIdentifier()
        => AssertEval("empty = 123\nempty", 123);

    [Fact]
    public void Eval_EmptySequence_Equality()
    {
        AssertEval("() == ()", 1);
        AssertEval("() != ()", 0);
        AssertEval("() == (())", 1);
        AssertEval("() != (())", 0);
        AssertEval("(()) == (())", 1);
        AssertEval("A = ()\nA == ()", 1);
        // Collection-builtin results are exact lists: the empty list [] is NOT
        // equal to the empty sequence ().
        AssertEval(
            """
            IsEven = x mod 2 == 0
            filter((1, 3, 5), IsEven) == ()
            """,
            0);
        AssertEval(
            """
            IsEven = x mod 2 == 0
            () == filter((1, 3, 5), IsEven)
            """,
            0);
        AssertEval("(0).skip(1) == ()", 0);
    }

    [Fact]
    public void Eval_NoOutputBody_IsNotTheEmptySequenceValue()
    {
        // `{}` and other no-output bodies are not values: they have no defined
        // output and so are not comparable with the empty sequence value `()`.
        foreach (var source in new[]
        {
            "{}",
            "{}.count",
            "count({})",
            "{} == ()",
            "() == {}",
            "C = {}\nC.count",
            "Lib = {\n  Prop = 7\n}\nLib.count",
            "Lib = {\n  Prop = 7\n}\nLib == ()",
        })
        {
            AssertEvalFailsWithMissingOutput(source);
        }
    }

    [Fact]
    public void Eval_EmptySequence_IsAValue_NotMissingOutput()
    {
        // In contrast to no-output bodies, `()` is a real value: it can be stored,
        // counted, and compared.
        AssertEvalEmptyOutput("()");
        AssertEval("().count", 0);
        AssertEval("D = ()\nD.count", 0);
        AssertEval("D = ()\nD == ()", 1);
    }

    [Fact]
    public void Eval_MissingOutput_EmptyBraceBody_UsesEmptySequenceHint()
        => AssertMissingOutputMessage(
            "{}",
            "Algorithm has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended.",
            expectedLine: 1,
            expectedColumn: 1);

    [Fact]
    public void Eval_NamedEmptySequenceVersusNoOutputBody_StayDistinct()
    {
        // `()` stored in a property is a real value: returning it directly yields `()`,
        // and it compares equal to `()`.
        AssertEvalEmptyOutput("A = ()\nA");
        AssertEval("A = ()\nA == ()", 1);

        // `{}` stored in a property is no-output: forcing it (directly, or as an operand
        // of `==`) fails with missing-output before any value or equality is produced.
        // It must not behave like `()` — neither `1` nor `0`.
        AssertEvalFailsWithMissingOutput("A = {}\nA");
        AssertEvalFailsWithMissingOutput("A = {}\nA == ()");

        // A no-output body must not become a visible empty-sequence slot in mixed output:
        // evaluating the `{}` slot fails with missing-output rather than contributing `()`.
        AssertEvalFailsWithMissingOutput("{}, 1");
    }

    [Fact]
    public void Eval_MissingOutput_DefinitionOnlyProgram_FailsWhenResultIsRequested()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            """,
            RunResult.NoProgramOutput.DefaultMessage);

    [Fact]
    public void Eval_MissingOutput_PropertyAccess_RemainsValid()
        => AssertEval(
            """
            A = {
                X = 1
            }
            A.X
            """,
            1);

    [Fact]
    public void Eval_MissingOutput_HigherOrderArgument_RemainsValid()
        => AssertEval(
            """
            Apply(f) = f(4)
            Inc(x) = x + 1
            Apply(Inc)
            """,
            5);

    [Fact]
    public void Eval_MissingOutput_NestedNoOutputProperty_RemainsValidWhenNotForced()
        => AssertEval(
            """
            Holder = {
                F = {
                    X = 1
                }
                0
            }
            Holder
            """,
            0);

    [Fact]
    public void Eval_MissingOutput_FinalPropertyUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            A
            """,
            $"Property 'A' has no defined output.\nAdd an output expression to 'A', or use `()` if the empty sequence value was intended. To use one of its properties, write `A.X`.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_CallUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            A()
            """,
            $"Cannot call 'A' because it has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_CallUse_CarriesStructuredCallContext()
    {
        var result = EvalFull(
            """
            A = {
                X = 1
            }
            A()
            """);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
        var callContext = Assert.IsType<CallContext>(contextual.ErrorContext);
        Assert.Equal("A", callContext.CalleeDescription);
        Assert.IsType<EvalError.MissingOutput>(contextual.Inner);

        Assert.Equal(
            $"Cannot call 'A' because it has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.",
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void Eval_MissingOutput_CallWithArgument_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            Algo = {
                Prop = 7
            }
            Algo(6)
            """,
            $"Cannot call 'Algo' because it has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_BinaryUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            A + 1
            """,
            $"Property 'A' has no defined output.\nAdd an output expression to 'A', or use `()` if the empty sequence value was intended. To use one of its properties, write `A.X`.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_UnaryUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            -A
            """,
            $"Property 'A' has no defined output.\nAdd an output expression to 'A', or use `()` if the empty sequence value was intended. To use one of its properties, write `A.X`.",
            expectedLine: 4,
            expectedColumn: 2);

    [Fact]
    public void Eval_MissingOutput_AssignmentOnlyFailsWhenForcedLater()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            B = A
            B
            """,
            $"Property 'A' has no defined output.\nAdd an output expression to 'A', or use `()` if the empty sequence value was intended. To use one of its properties, write `A.X`.");

    [Fact]
    public void Eval_MissingOutput_StructuralArgumentUse_CanStillSucceed()
        => AssertEval(
            """
            A = {
                X = 1
            }
            Use(f) = 0
            Use(A)
            """,
            0);

    // ── `Output` as an ordinary identifier ──────────────────────────────────
    // Output rows are the only output mechanism; `Output` and `output` follow
    // ordinary property, call, visibility, and access rules.

    [Fact]
    public void Eval_OutputProperty_IsOrdinary()
    {
        AssertEval("Output = 5\nOutput", 5);
    }

    [Fact]
    public void Eval_LowercaseOutputProperty_IsOrdinary()
    {
        AssertEval("output = 6\noutput", 6);
    }

    [Fact]
    public void Eval_OutputCallableProperty_IsOrdinary()
    {
        AssertEval("Output(x) = x * 2\nOutput(4)", 8);
    }

    [Fact]
    public void Eval_PublicOutputProperty_IsOrdinary()
    {
        AssertEval("public Output = 7\nOutput", 7);
    }

    [Fact]
    public void Eval_OutputAndLowercaseOutput_AreDistinctCaseSensitiveNames()
    {
        AssertEval("Output = 1\noutput = 2\nOutput + output", 3);
    }

    [Fact]
    public void Eval_OutputRow_InterleavedWithProperties()
    {
        AssertEval("A = 3\nA + B\nB = 2", 5);
    }

    [Fact]
    public void Eval_MultipleOutputRows_KeepMultiOutputSemantics()
    {
        AssertEval("A = 3\nA\nA + 1", 3, 4);
    }

    [Fact]
    public void Eval_OutputNamedProperty_WithoutReference_LeavesNoOutput()
    {
        // The former explicit syntax is now just a property definition, so
        // this program has properties `A` and `Output` and no output rows.
        var result = EvalFull("A = 3\nOutput = A + 2");

        Assert.True(result.IsError);
        AssertInnermostMissingOutput(result.Error);
    }

    [Fact]
    public void Eval_OutputNamedProperty_ReferencedByRow_ContributesItsValue()
    {
        AssertEval("A = 3\nOutput = A + 2\nOutput", 5);
    }

    [Fact]
    public void Eval_OutputProperty_WithFollowingRows_HasNoMixingRule()
    {
        AssertEval("Output = 4\nOutput\n5", 4, 5);
    }

    [Fact]
    public void Eval_OutputProperty_DottedAccess_IsOrdinary()
    {
        var source = """
            A = {
                Output = 9
            }

            A.Output
            """;
        AssertEval(source, 9);
    }

    [Fact]
    public void Eval_OutputRows_InterleavedInsideBlock()
    {
        var source = """
            X = {
              A = 3
              A + 1
              B = 2
            }
            X
            """;
        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_OutputRow_WithParametrizedProperty()
    {
        AssertEval("Add = x + y\nAdd(3, 4)", 7);
    }
}
