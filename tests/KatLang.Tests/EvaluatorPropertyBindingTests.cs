using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorPropertyBindingTests
{
    [Fact]
    public void Eval_RepeatedEligiblePropertyWithinSingleRun()
    {
        var source = """
            Values = range(1, 5)
            Values.count + Values.count
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([10m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_ClosedLexicalProperty_RemainsCorrectAcrossCallerContexts()
    {
        var source = """
            Measure(values) = {
                Count = values.count
                Count + Count
            }
            Measure((1, 2)) + Measure((3, 4, 5))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([10m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_Distinguishes_SamePropertyTextAcrossReceiverContexts()
    {
        var source = """
                        Left = {
                            Value = 1
                        }
                        Right = {
                            Value = 2
                        }
                        Left.Value + Left.Value + Right.Value + Right.Value
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([6m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_ParameterizedCallResults_RemainDistinct()
    {
        var source = """
            Inc = x + 1
            Inc(1) + Inc(2)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_RepeatedRuns_AreConsistent()
    {
        var source = """
            Values = range(1, 5)
            Values.count + Values.count
            """;

        var ast = ParseValidRoot(source);

        var first = Evaluator.Run(new Expr.AlgorithmExpr(ast));
        var second = Evaluator.Run(new Expr.AlgorithmExpr(ast));

        if (first.IsError)
            Assert.Fail($"Expected first run success but got error: {first.Error}");
        if (second.IsError)
            Assert.Fail($"Expected second run success but got error: {second.Error}");

        Assert.Equal(first.Value.ToAtoms(), second.Value.ToAtoms());
    }

    [Fact]
    public void Eval_PreservesRecursivePropertyBehavior()
    {
        var source = """
            Recursive = {
              Step = if(n == 0, 0, Step(n - 1))
              Step(4)
            }
            Recursive + Recursive
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([0m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_RecursiveDotCallArgumentUsesCurrentValueBinding()
    {
        // `atoms` now traverses list values directly, so `atoms(values)` on a
        // spread-recaptured list works without a workaround. The explicit
        // spread (`rest = list.skip(1)*`) is kept because a sequence-shaped
        // recursion argument is what exercises the current-value binding here.
        var source = """
            reduceCollection(values) = {
                list = atoms(values)
                rest = list.skip(1)*
                if(
                    list.count <= 1,
                    list,
                    rest.reduceCollection
                )
            }
            reduceCollection((1,2,3,4))
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Distinguishes_HigherOrderAlgorithmContexts()
    {
        var source = """
                        Left = {
                            Step = x + 1
                            Value = Step(10)
            }
                        Right = {
                            Step = x + 2
                            Value = Step(10)
                        }
                        Left.Value + Left.Value + Right.Value + Right.Value
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([46m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_Distinguishes_SameLexicalPropertyTextAcrossNestedBindings()
    {
        var source = """
            Outer = {
                Left = {
                    Value = 10
                    Value + Value
                }
                Right = {
                    Value = 20
                    Value + Value
                }
                Left + Right
            }
            Outer
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([60m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_Keeps_CallerBoundZeroParamLexicalProperty_Contextual()
    {
        var shared = new Property(
            "Shared",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Param("x")]));

        var caller = new Property(
            "Caller",
            new Algorithm.User(
                Parent: null,
                Parameters: Algorithm.NormalParameters(["x"]),
                Opens: [],
                Properties: [shared],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        OutputBundle oneArg = [new Expr.Num(1)];

        OutputBundle twoArg = [new Expr.Num(2)];

        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [caller],
            Output:
            [
                new Expr.Binary(
                    BinaryOp.Add,
                    new Expr.Call(new Expr.Resolve("Caller"), oneArg),
                    new Expr.Call(new Expr.Resolve("Caller"), twoArg))
            ]);

        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([6m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_SharedBindingAcrossDefinitionScopes_DoesNotContaminateOpenDependentMeaning()
    {
        var sharedClosedBinding = new Property(
            "Shared",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Resolve("Base")]));

        var localBaseBinding = new Property(
            "Base",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(1)]));

        var openBaseBinding = new Property(
            "Base",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(2)]),
            IsPublic: true);

        var libraryBinding = new Property(
            "Lib",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [openBaseBinding],
                Output: []),
            IsPublic: true);

        var structuralWrapperBinding = new Property(
            "StructuralWrapper",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [localBaseBinding, sharedClosedBinding],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        var openWrapperBinding = new Property(
            "OpenWrapper",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [new Expr.Resolve("Lib")],
                Properties: [sharedClosedBinding],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [libraryBinding, structuralWrapperBinding, openWrapperBinding],
            Output:
            [
                new Expr.Binary(
                    BinaryOp.Add,
                    new Expr.Resolve("StructuralWrapper"),
                    new Expr.Resolve("OpenWrapper"))
            ]);

        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal(
            [6m],
            result.Value.ToAtoms());
    }

    // â”€â”€ Properties â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Property_ReturnsValue()
    {
        var source = """
            X = 5
            X
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_Property_WithExpression()
    {
        var source = """
            X = 2 + 3
            X
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_Property_MultipleOutputs()
    {
        var source = """
            X = 1, 2, 3
            X
            """;
        AssertEval(source, 1, 2, 3);
    }

    [Fact]
    public void Eval_Property_ReferenceAnother()
    {
        var source = """
            A = 5
            B = A + 1
            B
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_PropertyAccess_SubProperty()
    {
        var source = """
            X = { Y = 42
            Y }
            X.Y
            """;
        AssertEval(source, 42);
    }

    // â”€â”€ Blocks â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Block_ReturnsOutput()
        => AssertEval("{1 + 2}", 3);

    [Fact]
    public void Eval_InlineBlock_ReturnsOutput()
        => AssertEval("(1, 2, 3)", 1, 2, 3);

    // â”€â”€ call args wiring (Lean: wireToCaller in user-defined call path) â”€â”€

    [Fact]
    public void Eval_CallArgsWiring_PropertyAsArgument()
    {
        // Caller property usable as argument: G resolves in caller scope
        var source = """
            G = 7
            F = x + 1
            F(G)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_CallArgsWiring_PropertyDotAccessAsArgument()
    {
        // Property with dot-access usable as argument
        var source = """
            G = { public Val = 7 }
            F = x + 1
            F(G.Val)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_CallArgsWiring_MultiplePropertyArgs()
    {
        // Multiple properties as arguments
        var source = """
            A = 3
            B = 5
            Add = x + y
            Add(A, B)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_CallArgsWiring_NestedBlockScopeNotSmuggled()
    {
        // Block introduces its own scope â€” inner names don't leak
        var source = """
            F = x + 1
            F({10})
            """;
        AssertEval(source, 11);
    }

    // â”€â”€ NetSalary scenario (dotCall on parameterised algorithm) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_NetSalary_DotCallIncomeTax_FailsWhenOuterParamsAreCaptured()
    {
        var source = @"
                        NetSalary = {
                            SocialSecurityTax = grossSalary * 0.105
                            NonTaxableMinimum = grossSalary - SocialSecurityTax - 75
                            ChildTaxCredit = numberOfChildren * 162
                            TaxableIncome = NonTaxableMinimum - ChildTaxCredit
                            IncomeTax = TaxableIncome * 0.24

                            grossSalary - SocialSecurityTax - IncomeTax
                        }
                        NetSalary.IncomeTax(1000, 2)
                        ";

        AssertLocalOnlyPropertyMessage(
                        source,
                        "Property 'IncomeTax' on `NetSalary` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
    }

    [Fact]
    public void Eval_NetSalary_DirectCall_UsesAlgorithmParameters()
    {
        // NetSalary(1000, 2) binds the algorithm-level interface directly.
        // Output = 1000 - 105 - 119.04 = 775.96
        var source = """
            NetSalary = {
              SocialSecurityTax = grossSalary * 0.105
              NonTaxableMinimum = grossSalary - SocialSecurityTax - 75
              ChildTaxCredit = numberOfChildren * 162
              TaxableIncome = NonTaxableMinimum - ChildTaxCredit
              IncomeTax = TaxableIncome * 0.24
              
              grossSalary - SocialSecurityTax - IncomeTax
            }
            NetSalary(1000, 2)
            """;
        AssertEval(source, 775.96m);
    }

    [Fact]
    public void Eval_NetSalary_SelfContainedProperty_DotCall()
    {
        // Working approach: IncomeTax explicitly uses its own free variables.
        // grossSalary=1000, numberOfChildren=2:
        // (1000 - 1000*0.105 - 75 - 2*162) * 0.24 = 496 * 0.24 = 119.04
        var source = """
            NetSalary = {
              IncomeTax = (grossSalary - grossSalary * 0.105 - 75 - numberOfChildren * 162) * 0.24
            }
            NetSalary.IncomeTax(1000, 2)
            """;
        AssertEval(source, 119.04m);
    }
}
