namespace KatLang.Tests;

public class ImplicitArgumentResolverTests
{
    private static Algorithm Resolve(string source)
        => Parser.Parse(source).Root;

    private static EvalResult<IReadOnlyList<decimal>> Eval(string source)
        => Evaluator.RunFlat(new Expr.Block(Resolve(source)));

    /// <summary>
    /// Evaluate to the single structured root value. Unlike <see cref="Eval"/>
    /// (which flattens through the host-atom boundary), this preserves list
    /// and sequence kinds so tests can assert exact value structure.
    /// </summary>
    private static Result EvalValue(string source)
    {
        var result = Evaluator.RunCounted(new Expr.Block(Resolve(source)));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        return result.Value.Value;
    }

    private static void AssertEval(string source, params decimal[] expected)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    // â”€â”€ AST-level tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Resolve_BasicLift_RewritesResolveToCall()
    {
        var source = """
            F = a
            G = F + b
            """;
        var root = Resolve(source);

        var g = root.Properties.Single(p => p.Name == "G").Value;

        Assert.Equal(["b", "a"], g.Params);

        var output = Assert.Single(g.Output);
        var binary = Assert.IsType<Expr.Binary>(output);
        Assert.Equal(BinaryOp.Add, binary.Op);

        var call = Assert.IsType<Expr.Call>(binary.Left);
        Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("F", ((Expr.Resolve)call.Function).Name);

        var callArg = Assert.Single(call.Args.Output);
        var param = Assert.IsType<Expr.Param>(callArg);
        Assert.Equal("a", param.Name);

        Assert.IsType<Expr.Param>(binary.Right);
        Assert.Equal("b", ((Expr.Param)binary.Right).Name);
    }

    [Fact]
    public void Resolve_ExplicitCallUnchanged_NoLifting()
    {
        var source = """
            F = a
            G = F(1) + b
            """;
        var root = Resolve(source);

        var g = root.Properties.Single(p => p.Name == "G").Value;
        Assert.Equal(["b"], g.Params);
    }

    [Fact]
    public void Resolve_SharedParamName_NoDuplication()
    {
        var source = """
            F = a + b
            G = a + F
            """;
        var root = Resolve(source);

        var g = root.Properties.Single(p => p.Name == "G").Value;
        Assert.Equal(["a", "b"], g.Params);
    }

    [Fact]
    public void Resolve_TransitiveLift_ChainsCorrectly()
    {
        var source = """
            E = x
            F = E + y
            G = F + z
            """;
        var root = Resolve(source);

        var f = root.Properties.Single(p => p.Name == "F").Value;
        Assert.Equal(["y", "x"], f.Params);

        var g = root.Properties.Single(p => p.Name == "G").Value;
        Assert.Equal(["z", "y", "x"], g.Params);
    }

    [Fact]
    public void Resolve_MultipleRefs_LiftsFromAll()
    {
        var source = """
            A = x
            B = y
            C = A + B + z
            """;
        var root = Resolve(source);

        var c = root.Properties.Single(p => p.Name == "C").Value;
        Assert.Equal(["z", "x", "y"], c.Params);
    }

    [Fact]
    public void Resolve_NonParametrizedRef_NoLifting()
    {
        var source = """
            X = 5
            G = X + b
            """;
        var root = Resolve(source);

        var g = root.Properties.Single(p => p.Name == "G").Value;
        Assert.Equal(["b"], g.Params);
    }

    [Fact]
    public void Resolve_NestedBlock_IsolatedScope()
    {
        var source = """
            F = a
            G = {F + b} + c
            """;
        var root = Resolve(source);

        var g = root.Properties.Single(p => p.Name == "G").Value;
        Assert.Equal(["c"], g.Params);

        var binary = Assert.IsType<Expr.Binary>(Assert.Single(g.Output));
        var block = Assert.IsType<Expr.Block>(binary.Left);
        Assert.Contains("b", block.Algorithm.Params);
        Assert.Contains("a", block.Algorithm.Params);
    }

    [Fact]
    public void Resolve_NoImplicitArgs_NoOpTransformation()
    {
        var source = """
            X = 5
            Y = X + 1
            Y
            """;
        var root = Resolve(source);

        var y = root.Properties.Single(p => p.Name == "Y").Value;
        Assert.Empty(y.Params);
    }

    [Fact]
    public void Resolve_DotCallArgumentDependenciesLiftThroughContainingProperty()
    {
        var source = """
            Quadratic = {
                Discriminant = b ^ 2 - 4 * a * c
                Root1 = (-b + Math.Sqrt(Discriminant)) / (2 * a)
                Root2 = (-b - Math.Sqrt(Discriminant)) / (2 * a)

                Root1, Root2
            }
            Quadratic(1, -5, 6)
            """;
        var root = Resolve(source);

        var quadratic = root.Properties.Single(p => p.Name == "Quadratic").Value;
        Assert.Equal(["b", "a", "c"], quadratic.Params);

        var discriminant = quadratic.Properties.Single(p => p.Name == "Discriminant").Value;
        Assert.Equal(["b", "a", "c"], discriminant.Params);

        var root1 = quadratic.Properties.Single(p => p.Name == "Root1").Value;
        Assert.Equal(["b", "a", "c"], root1.Params);

        var root2 = quadratic.Properties.Single(p => p.Name == "Root2").Value;
        Assert.Equal(["b", "a", "c"], root2.Params);
    }

    [Fact]
    public void Resolve_VariadicImplicitCall_NameMismatchForwardsCallerStreamAsSpreadWithoutLiftingCalleeName()
    {
        var source = """
            CountItems(...items) = items.count
            Use(...values) = CountItems
            """;
        var root = Resolve(source);

        var use = root.Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(["values"], use.Params);
        Assert.Equal(["...values"], use.ParameterPatterns.Select(parameter => parameter.DisplayName).ToList());
        Assert.DoesNotContain("items", use.Params);

        var call = Assert.IsType<Expr.Call>(Assert.Single(use.Output));
        var function = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("CountItems", function.Name);

        // Variadic forwarding synthesizes a SPREAD argument (`CountItems(values...)`):
        // the caller's rest holds one exact list, and the spread re-supplies its
        // collected items so the callee's rest re-collects exactly them.
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args.Output));
        var param = Assert.IsType<Expr.Param>(spread.Operand);
        Assert.Equal("values", param.Name);
    }

    [Fact]
    public void Resolve_ExplicitParameterList_DoesNotLiftBareParameterizedHelper()
    {
        var source = """
            CountItems(...items) = items.count
            Use(value) = CountItems
            """;
        var root = Resolve(source);

        var use = root.Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(["value"], use.Params);
        Assert.Equal(["value"], use.ParameterPatterns.Select(parameter => parameter.DisplayName).ToList());
        Assert.DoesNotContain("items", use.Params);

        var resolve = Assert.IsType<Expr.Resolve>(Assert.Single(use.Output));
        Assert.Equal("CountItems", resolve.Name);
    }

    [Fact]
    public void Resolve_BareMathCallableAlias_LiftsMemberSignature()
    {
        var source = """
            RoundB = Math.Round
            """;
        var root = Resolve(source);

        var roundB = root.Properties.Single(p => p.Name == "RoundB").Value;
        Assert.Equal(["x", "y"], roundB.Params);

        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(roundB.Output));
        Assert.NotNull(dotCall.Args);
        Assert.Equal("Round", dotCall.Name);
        Assert.Equal(["x", "y"], dotCall.Args.Output
            .Select(expr => Assert.IsType<Expr.Param>(expr).Name)
            .ToArray());
    }

    [Fact]
    public void Resolve_BareMathCallableAlias_DoesNotUseNativeSignatureWhenMathIsShadowed()
    {
        var source = """
            Math = (Round = 42
            Round)
            RoundB = Math.Round
            """;
        var root = Resolve(source);

        var roundB = root.Properties.Single(p => p.Name == "RoundB").Value;
        Assert.Empty(roundB.Params);

        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(roundB.Output));
        Assert.Null(dotCall.Args);
        Assert.Equal("Round", dotCall.Name);
    }

    [Fact]
    public void Resolve_BareBuiltinCallableAlias_DoesNotResolveThroughArbitraryOwnerExpression()
    {
        var source = """
            GetMath = Math
            RoundB = GetMath.Round
            """;
        var root = Resolve(source);

        var roundB = root.Properties.Single(p => p.Name == "RoundB").Value;
        Assert.Empty(roundB.Params);

        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(roundB.Output));
        Assert.Null(dotCall.Args);
        Assert.Equal("Round", dotCall.Name);
    }

    // â”€â”€ End-to-end evaluation tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_BasicImplicit_ReturnsCorrectResult()
    {
        var source = """
            F = a
            G = F + b
            G(1, 2)
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_TransitiveImplicit_ReturnsCorrectResult()
    {
        var source = """
            E = x
            F = E + y
            G = F + z
            G(1, 2, 3)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_SharedParam_ReturnsCorrectResult()
    {
        var source = """
            F = a + b
            G = a + F
            G(1, 2)
            """;
        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_ExplicitCallNotAffected_ReturnsCorrectResult()
    {
        var source = """
            F = a
            G = F(5) + b
            G(10)
            """;
        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_BareUserAlias_StillPropagatesImplicitParameters()
    {
        var source = """
            Test1 = x
            Test2 = Test1
            Test2(7)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_ExplicitMathRoundWrapper_StillWorks()
    {
        var source = """
            RoundA = Math.Round(x, y)
            RoundA(1.234, 2)
            """;
        AssertEval(source, 1.23m);
    }

    [Fact]
    public void Eval_BareMathRoundAlias_ForwardsMemberSignature()
    {
        var source = """
            RoundB = Math.Round
            RoundB(1.234, 2)
            """;
        AssertEval(source, 1.23m);
    }

    [Fact]
    public void Eval_BareMathAbsAlias_ForwardsMemberSignature()
    {
        var source = """
            AbsAlias = Math.Abs
            AbsAlias(-5)
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_ExistingSumExample_StillWorks()
    {
        var source = """
            Numbers = 3, 5, 9, 1, 0, 6
            Add = a + 1, total + Numbers:a
            Sum = repeat(Add, (6), 0, 0) : 1
            Sum
            """;
        AssertEval(source, 24);
    }

    [Fact]
    public void Eval_ExistingFibonacci_StillWorks()
    {
        var source = """
            Fib = a + b, a
            repeat(Fib, (10), 1, 0):0
            """;
        AssertEval(source, 89);
    }

    [Fact]
    public void Eval_ImplicitWithMultipleOutputs()
    {
        var source = """
            F = a, a * 2
            G = F:0 + b
            G(3, 10)
            """;
        AssertEval(source, 13);
    }

    [Fact]
    public void Eval_ImplicitRef_MultipleParams()
    {
        var source = """
            Add = a + b
            G = Add + c
            G(1, 2, 3)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_ImplicitQuadratic_DotCallArgumentDependencies_ReturnsRoots()
    {
        var source = """
            Quadratic = {
                Discriminant = b ^ 2 - 4 * a * c
                Root1 = (-b + Math.Sqrt(Discriminant)) / (2 * a)
                Root2 = (-b - Math.Sqrt(Discriminant)) / (2 * a)

                Root1, Root2
            }
            Quadratic(1, -5, 6)
            """;

        AssertEval(source, -1, 1.2m);
    }

    [Fact]
    public void Eval_VariadicImplicitCall_SameNameTopLevelVariadic_ForwardsCallerStream()
    {
        // The root spread supplies the three items, and the synthesized spread
        // forwarding re-supplies them to the callee's rest binding.
        var source = """
            CountValues(...values) = values.count
            Use(...values) = CountValues
            Use((1, 2, 3)...)
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_VariadicImplicitCall_NameMismatchTopLevelVariadic_ForwardsCallerStream()
    {
        var source = """
            CountItems(...items) = items.count
            Use(...values) = CountItems
            Use((1, 2, 3)...)
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_SequenceValueVariadicImplicitCall_SameNameCalleePattern_ForwardsCallerStream()
    {
        var source = """
            CountSequenceValue((...values)) = values.count
            Use(...values) = CountSequenceValue
            Use((1, 2, 3)...)
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_SequenceValueVariadicImplicitCall_NameMismatchCalleePattern_ForwardsCallerStream()
    {
        var source = """
            CountSequenceValue((...items)) = items.count
            Use(...values) = CountSequenceValue
            Use((1, 2, 3)...)
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_OrdinarySourceParameter_ForwardsAsOneArgumentIntoVariadicCallee()
    {
        // The implicit spread decision is made from the SOURCE binding kind:
        // `Use.items` is an ordinary fixed parameter, so the synthesized call
        // is `Target(items)` — one argument — and the callee's rest collects
        // exactly one slot. The destination being variadic must not open it.
        var source = """
            Target(...items) = items
            Use(items) = Target
            Use([1, 2])
            """;

        var listResult = Assert.IsType<Result.ListValue>(EvalValue(source));
        var element = Assert.IsType<Result.ListValue>(Assert.Single(listResult.Items));
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], element.Items, Result.ValueComparer);

        var sequenceSource = """
            Target(...items) = items
            Use(items) = Target
            Use((1, 2))
            """;
        var sequenceList = Assert.IsType<Result.ListValue>(EvalValue(sequenceSource));
        var sequenceElement = Assert.IsType<Result.SequenceValue>(Assert.Single(sequenceList.Items));
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], sequenceElement.Items, Result.ValueComparer);

        var scalarSource = """
            Target(...items) = items
            Use(items) = Target
            Use(7)
            """;
        var scalarList = Assert.IsType<Result.ListValue>(EvalValue(scalarSource));
        Assert.Equal([new Result.Atom(7)], scalarList.Items, Result.ValueComparer);
    }

    [Fact]
    public void Resolve_OrdinarySourceParameter_SynthesizesUnspreadArgument()
    {
        // The synthesized implicit call passes the ordinary source parameter
        // as a bare Expr.Param — never wrapped in Expr.SequenceSpread.
        var root = Resolve("""
            Target(...items) = items
            Use(items) = Target
            """);

        var use = root.Properties.Single(p => p.Name == "Use").Value;
        var call = Assert.IsType<Expr.Call>(Assert.Single(use.Output));
        var param = Assert.IsType<Expr.Param>(Assert.Single(call.Args.Output));
        Assert.Equal("items", param.Name);
    }

    [Fact]
    public void Eval_RestSourceParameter_ForwardsCollectedItemsAsSpread()
    {
        // Genuine rest forwarding: the caller's own rest is the source, so
        // the synthesized call is `Target(items...)` and the collected items
        // round-trip exactly (open(collect(xs)) = xs).
        var source = """
            Target(...items) = items
            Use(...items) = Target
            Use(1, 2)
            """;
        var list = Assert.IsType<Result.ListValue>(EvalValue(source));
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], list.Items, Result.ValueComparer);

        var listArgSource = """
            Target(...items) = items
            Use(...items) = Target
            Use([1, 2])
            """;
        var outerList = Assert.IsType<Result.ListValue>(EvalValue(listArgSource));
        var innerList = Assert.IsType<Result.ListValue>(Assert.Single(outerList.Items));
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], innerList.Items, Result.ValueComparer);
    }

    [Fact]
    public void Eval_SequenceValueOrdinaryCaller_NameMismatchStaysUnresolved()
    {
        // The callee's parameter name does not match any caller parameter, so
        // the reference is not rewritten and fails at runtime instead of
        // silently spreading the ordinary sequence-value parameter.
        var result = Eval(
            """
            CountValues(...values) = values.count
            Use(sequenceValue) = CountValues
            Use((1, 2, 3))
            """);

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.Expected);
        Assert.Equal(0, arity.Actual);
    }

    // â”€â”€ Transitive ordering: zero-param intermediaries â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Resolve_TransitiveViaZeroParamSibling_LiftsCorrectly()
    {
        // A has params, B references A (gains A's params), C references B.
        // Without correct topo ordering, C would not see B's lifted params.
        // A: params=[x] (direct free var)
        // B: refs A (uppercase, 0 own free vars) â†’ after resolver: params=[x]
        // C: refs B â†’ after resolver: params=[x]
        var source = """
            A = x + 1
            B = A * 2
            C = B + 3
            """;
        var root = Resolve(source);

        var b = root.Properties.Single(p => p.Name == "B").Value;
        Assert.Equal(["x"], b.Params);

        var c = root.Properties.Single(p => p.Name == "C").Value;
        Assert.Equal(["x"], c.Params);
    }

    [Fact]
    public void Resolve_TransitiveChainAllUppercase_LiftsCorrectly()
    {
        // All intermediate properties reference only uppercase siblings,
        // so ParameterDetector assigns them 0 params. Only the leaf has
        // a direct free variable. Resolver propagates transitively.
        var source = """
            Leaf = x * 2
            Mid = Leaf + 1
            Top = Mid - 5
            """;
        var root = Resolve(source);

        var mid = root.Properties.Single(p => p.Name == "Mid").Value;
        Assert.Equal(["x"], mid.Params);

        var top = root.Properties.Single(p => p.Name == "Top").Value;
        Assert.Equal(["x"], top.Params);
    }

    [Fact]
    public void Resolve_TransitiveMultipleLeaves_MergesParams()
    {
        // Two leaves with different params, an intermediary referencing both,
        // and a top property referencing the intermediary.
        var source = """
            Left = a + 1
            Right = b * 2
            Mid = Left - Right
            Top = Mid + 10
            """;
        var root = Resolve(source);

        var mid = root.Properties.Single(p => p.Name == "Mid").Value;
        Assert.Equal(["a", "b"], mid.Params);

        var top = root.Properties.Single(p => p.Name == "Top").Value;
        Assert.Equal(["a", "b"], top.Params);
    }

    [Fact]
    public void Eval_TransitiveViaZeroParamSibling_ReturnsCorrectResult()
    {
        // A(5) = 6, B(5) = 12, C(5) = 15
        var source = """
            A = x + 1
            B = A * 2
            C = B + 3
            C(5)
            """;
        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_NetSalarySiblingChain_ReturnsCorrectResult()
    {
        // Simplified NetSalary pattern: multi-step computation via
        // sibling properties, accessed through dotCall.
        // Tax = 1000 * 0.2 = 200
        // Net = 1000 - 200 = 800
        var source = """
            Salary = {
              Tax = income * 0.2
              Net = income - Tax
            }
            Salary.Net(1000)
            """;
        AssertEval(source, 800);
    }
}
