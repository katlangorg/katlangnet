using System.Numerics;
namespace KatLang.Tests;

public class ImplicitArgumentResolverTests
{
    private static Algorithm Resolve(string source)
        => SourceProvenance.ParseValid(source).Root;

    /// <summary>
    /// Elaborated root for a source the closed-list strict-value refinement REJECTS at the
    /// front end (a registry-proven value-demanding position whose referenced callable needs
    /// implicit parameters the closed explicit list cannot supply).
    ///
    /// <para>The rewrite is still the subject of these tests: what makes the new diagnostic
    /// honest rather than a cover story is that the resolver, on refusing to lift, leaves the
    /// reference bare and invents no parameter. So this states the rejection explicitly —
    /// never <c>ParseValid</c>, which would silently evaluate a recovery tree — and hands back
    /// the tree the resolver actually produced. The diagnostic's own content is owned by
    /// <see cref="ClosedListStrictValueDiagnosticTests"/>.</para>
    /// </summary>
    private static Algorithm ResolveRejected(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.True(
            parsed.HasErrors,
            "Expected the closed-list strict-value diagnostic, but the front end accepted:"
            + Environment.NewLine + source);
        return parsed.Root;
    }

    private static EvalResult<IReadOnlyList<Decimal128>> Eval(string source)
        => Evaluator.RunFlat(new Expr.AlgorithmExpr(Resolve(source)));

    /// <summary>
    /// Evaluate to the single structured root value. Unlike <see cref="Eval"/>
    /// (which flattens through the host-atom boundary), this preserves list
    /// and sequence kinds so tests can assert exact value structure.
    /// </summary>
    private static Result EvalValue(string source)
    {
        var result = Evaluator.RunCounted(new Expr.AlgorithmExpr(Resolve(source)));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        return result.Value.Value;
    }

    private static void AssertEval(string source, params Decimal128[] expected)
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

        var callArg = Assert.Single(call.Args);
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
    public void Resolve_ReferenceToZeroParameterProperty_NoLifting()
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
        var block = Assert.IsType<Expr.AlgorithmExpr>(binary.Left);
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
    public void Resolve_VariadicImplicitCall_NameMismatch_OnlyAFormulaForwardsTheStreamByShape()
    {
        // A LONE row is bare forwarding BY NAME (FWD-02): `Use(*values) = CountItems` declares no
        // parameter `(*items)`, so it is rejected — the caller's stream is never renamed into the
        // callee's name nor reshaped into its group — and the callee's binder is never lifted.
        var source = """
            CountItems((*items)) = items.count
            Use(*values) = CountItems
            """;
        var rejection = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(DiagnosticCode.UnforwardableParameter, rejection.Code);
        Assert.Contains("'(*items)'", rejection.Message, StringComparison.Ordinal);
        var use = SourceProvenance.ParseAllowingDiagnostics(source).Root.Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(["*values"], use.ParameterPatterns.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal("CountItems", Assert.IsType<Expr.Resolve>(Assert.Single(use.Output)).Name);

        // In a FORMULA the callee's one grouped stream is still forwarded BY SHAPE: the callee's
        // SEQUENCE group is rebuilt, as a sequence, from a SPREAD argument
        // (`CountItems((values*)) + 0`), so the group's collecting parameter re-collects exactly
        // the caller's items.
        var formula = Resolve(source.Replace("= CountItems", "= CountItems + 0", StringComparison.Ordinal))
            .Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(["values"], formula.Params);
        var lifted = Assert.IsType<Expr.Call>(Assert.IsType<Expr.Binary>(Assert.Single(formula.Output)).Left);
        var group = Assert.IsType<Expr.Capture>(Assert.Single(lifted.Args));
        var grouped = Assert.IsType<Expr.SequenceSpread>(Assert.Single(group.Body));
        Assert.Equal("values", Assert.IsType<Expr.Param>(grouped.Operand).Name);
    }

    [Theory]
    [InlineData("Use = CountItems + 1")]
    [InlineData("Use(*values) = Math.Abs(CountItems)")]
    [InlineData("Use(*values) = [CountItems]:0")]
    public void Resolve_ZeroArgumentVariadicHelper_IsNeverLifted(string use)
    {
        // Q-03: `CountItems(*items)` accepts zero supplied arguments, so its bare name in a
        // FORMULA is a property-style value demand whatever the caller binds — by name or by
        // shape. Nothing is lifted into `Use` and no call is synthesized.
        var source = "CountItems(*items) = items.count\n" + use;
        var written = SourceProvenance.ParseSyntaxValidRoot(source).Properties.Single(p => p.Name == "Use").Value;
        var resolved = Resolve(source).Properties.Single(p => p.Name == "Use").Value;

        Assert.Equal(written.Params, resolved.Params);
        Assert.Empty(CallsTo(resolved, "CountItems"));
    }

    [Theory]
    [InlineData("Use(*values) = CountItems", "*values", null)]
    [InlineData("Use(*items) = CountItems", "*items", "items*")]
    [InlineData("Use(items) = CountItems", "items", "items")]
    [InlineData("Use = CountItems", "", "alias")]
    public void Resolve_ZeroArgumentVariadicHelper_AsALoneRow_IsAliasedForwardedOrRead(string use, string signature, string? arguments)
    {
        // A lone row reads the callee's DECLARED structure (FWD-02, superseding Q-03's alias
        // clause): an open body is a callable alias of CountItems — binding indirection, no
        // signature of its own — because CountItems declares a parameter, although it also accepts
        // zero supplied arguments; a written list forwards BY NAME — the same-named collector
        // re-spread, a same-named fixed parameter as one argument — and when no binding has the
        // collector's name nothing is forwarded, so the row is the callee's bare name, its cached
        // zero-argument value (Q-03).
        var resolved = Resolve("CountItems(*items) = items.count\n" + use).Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(signature, string.Join(", ", resolved.ParameterPatterns.Select(static pattern => pattern.DisplayName)));
        if (arguments == "alias")
        {
            var alias = Assert.IsType<Algorithm.Alias>(resolved);
            Assert.Equal("CountItems", Assert.IsType<Expr.Resolve>(alias.Target).Name);
            Assert.Equal("*items", string.Join(", ", alias.ResolvedTarget!.Signature.Signature!.ParameterPatterns.Select(static pattern => pattern.DisplayName)));
            Assert.Empty(CallsTo(resolved, "CountItems"));
            return;
        }

        if (arguments is null)
        {
            Assert.Empty(CallsTo(resolved, "CountItems"));
            Assert.Equal("CountItems", Assert.IsType<Expr.Resolve>(Assert.Single(resolved.Output)).Name);
            return;
        }

        var call = Assert.Single(CallsTo(resolved, "CountItems"));
        Assert.Equal(arguments, string.Join(", ", call.Args.Select(static argument => argument switch
        {
            Expr.SequenceSpread { Operand: Expr.Param spread } => spread.Name + "*",
            Expr.Param param => param.Name,
            _ => argument.GetType().Name,
        })));
    }

    private static List<Expr.Call> CallsTo(Algorithm algorithm, string callee)
    {
        var collector = new CallCollector(callee);
        collector.VisitAlgorithm(algorithm);
        return collector.Calls;
    }

    private sealed class CallCollector(string callee) : AstWalker
    {
        public List<Expr.Call> Calls { get; } = [];

        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.Call { Function: Expr.Resolve(var name) } call && name == callee)
                Calls.Add(call);
            base.VisitExpr(expr);
        }
    }

    [Fact]
    public void Resolve_ExplicitParameterList_DoesNotLiftBareParameterizedHelper()
    {
        // The helper REQUIRES its `first` argument. In a FORMULA the closed list must refuse to
        // forward the names it does not declare, so the reference stays bare.
        var source = """
            CountItems(first, *items) = items.count
            Use(value) = CountItems + 0
            """;
        var root = Resolve(source);

        var use = root.Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(["value"], use.Params);
        Assert.Equal(["value"], use.ParameterPatterns.Select(parameter => parameter.DisplayName).ToList());
        Assert.DoesNotContain("items", use.Params);
        var resolve = Assert.IsType<Expr.Resolve>(Assert.IsType<Expr.Binary>(Assert.Single(use.Output)).Left);
        Assert.Equal("CountItems", resolve.Name);

        // A LONE row is bare forwarding BY NAME: the list declares no `first`, so the row is
        // rejected at the front end — never renamed from `value`, never added to the closed list
        // (FWD-02) — and stays as written.
        var lone = source.Replace(" + 0", "", StringComparison.Ordinal);
        var rejection = Assert.Single(SourceProvenance.ExpectFrontEndError(lone));
        Assert.Equal(DiagnosticCode.UnforwardableParameter, rejection.Code);
        Assert.Contains("'first'", rejection.Message, StringComparison.Ordinal);
        var rejected = SourceProvenance.ParseAllowingDiagnostics(lone).Root.Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(["value"], rejected.Params);
        Assert.Equal("CountItems", Assert.IsType<Expr.Resolve>(Assert.Single(rejected.Output)).Name);
    }

    [Fact]
    public void Resolve_BareMathCallableAlias_IsACallableAliasOfTheMember()
    {
        // `Math.Round` is a parameterized callable, so the lone row makes RoundB a callable alias
        // of it: binding indirection, never a wrapper with a copied signature or a synthesized call.
        var source = """
            RoundB = Math.Round
            """;
        var root = Resolve(source);

        var roundB = Assert.IsType<Algorithm.Alias>(root.Properties.Single(p => p.Name == "RoundB").Value);
        Assert.Empty(roundB.Params);

        var dotCall = Assert.IsType<Expr.DotCall>(roundB.Target);
        Assert.Null(dotCall.Args);
        Assert.Equal("Round", dotCall.Name);
        Assert.Equal(["value", "digits"], roundB.ResolvedTarget!.Signature.Signature!.ParameterNames);
    }

    [Fact]
    public void Resolve_BareMathCallableAlias_DoesNotUseNativeSignatureWhenMathIsShadowed()
    {
        var source = """
            Math = { Round = 42
            Round }
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

        // GetMath is an ordinary value property with no members, not a namespace alias, so the edge cannot
        // resolve `Round` through Math's native signature: it is an ordinary
        // dot edge whose lexical fallback is the only possible resolution, and
        // its callable becomes the property's own inferred parameter.
        Assert.Equal(["Round"], roundB.Params);

        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(roundB.Output));
        Assert.Null(dotCall.Args);
        Assert.Equal("Round", dotCall.Name);
        Assert.Equal("Round", Assert.IsType<Expr.Param>(dotCall.EffectiveLexicalFallback).Name);
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
    public void Eval_VariadicImplicitCall_SameNameCollectingParameter_ForwardsCallerStreamIntoARequiredCallee()
    {
        // The root spread supplies the three items, and the synthesized spread
        // forwarding re-supplies them to the callee's collecting binding.
        var source = """
            CountValues(tag, *values) = values.count
            Use(tag, *values) = CountValues
            Use(0, (1, 2, 3)*)
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_ZeroArgumentVariadicCallee_IsReadNotForwarded()
    {
        // Q-03: a callee whose only parameter is a top-level collector works with no arguments,
        // so its bare name in a FORMULA is ITS zero-argument value (0) — never a forwarding call —
        // whether the caller's collector has the same name or another one. A LONE row is bare
        // forwarding BY NAME (FWD-02): the same-named collector is re-spread (3), while a caller
        // stream of another name is never renamed into the callee's, so nothing is forwarded and
        // the row is the callee's zero-argument value again (0); the written call forwards (3).
        AssertEval("CountValues(*values) = values.count\nUse(*values) = CountValues + 0\nUse((1, 2, 3)*)", 0);
        AssertEval("CountItems(*items) = items.count\nUse(*values) = CountItems + 0\nUse((1, 2, 3)*)", 0);
        AssertEval("CountValues(*values) = values.count\nUse(*values) = CountValues\nUse((1, 2, 3)*)", 3);
        AssertEval("CountItems(*items) = items.count\nUse(*values) = CountItems\nUse((1, 2, 3)*)", 0);
        AssertEval("CountItems(*items) = items.count\nUse(*values) = CountItems(values*)\nUse((1, 2, 3)*)", 3);
    }

    [Fact]
    public void Eval_SequenceValueVariadicImplicitCall_SameNameCalleePattern_ForwardsCallerStream()
    {
        var source = """
            CountSequenceValue((*values)) = values.count
            Use(*values) = [CountSequenceValue]:0
            Use((1, 2, 3)*)
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_SequenceValueVariadicImplicitCall_NameMismatchCalleePattern_ForwardsCallerStream()
    {
        var source = """
            CountSequenceValue((*items)) = items.count
            Use(*values) = [CountSequenceValue]:0
            Use((1, 2, 3)*)
            """;
        AssertEval(source, 3);

        // A LONE row is bare forwarding by name: `Use(*values)` declares no `(*items)`, so it is
        // rejected at the front end — the caller's stream is neither renamed nor reshaped — while
        // the written `CountSequenceValue(values*)` passes three arguments the callee's one sequence
        // parameter rejects at run time.
        var rejection = Assert.Single(SourceProvenance.ExpectFrontEndError(
            "CountSequenceValue((*items)) = items.count\nUse(*values) = CountSequenceValue\nUse((1, 2, 3)*)"));
        Assert.Equal(DiagnosticCode.UnforwardableParameter, rejection.Code);
        var written = Eval("CountSequenceValue((*items)) = items.count\nUse(*values) = CountSequenceValue(values*)\nUse((1, 2, 3)*)");
        Assert.True(written.IsError);
        Assert.IsType<EvalError.ArityMismatch>(Innermost(written.Error));
    }

    [Fact]
    public void Eval_OrdinarySourceParameter_ForwardsAsOneArgumentIntoVariadicCallee()
    {
        // The implicit spread decision is made from the SOURCE binding kind:
        // `Use.items` is an ordinary fixed parameter, so the synthesized call
        // is `Target(tag, items)` — ONE argument, collected as one item whatever its
        // value (the destination being collecting must not open it): a list, a
        // sequence, and a scalar alike — exactly as for the explicitly written
        // `Target(tag, items)`. (The lone row under a written list is bare forwarding: Use's
        // same-named bindings supply Target's parameters, FWD-02.)
        var source = """
            Target(tag, *items) = items
            Use(tag, items) = Target
            Use(0, [1, 2])
            """;

        var listResult = Assert.IsType<Result.ListValue>(EvalValue(source));
        var element = Assert.IsType<Result.ListValue>(Assert.Single(listResult.Items));
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], element.Items, Result.ValueComparer);

        var sequenceSource = """
            Target(tag, *items) = items
            Use(tag, items) = Target
            Use(0, (1, 2))
            """;
        var sequenceList = Assert.IsType<Result.ListValue>(EvalValue(sequenceSource));
        var sequenceElement = Assert.IsType<Result.SequenceValue>(Assert.Single(sequenceList.Items));
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], sequenceElement.Items, Result.ValueComparer);

        var scalarSource = """
            Target(tag, *items) = items
            Use(tag, items) = Target
            Use(0, 7)
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
            Target(tag, *items) = items
            Use(tag, items) = Target
            """);

        var use = root.Properties.Single(p => p.Name == "Use").Value;
        var call = Assert.IsType<Expr.Call>(Assert.Single(use.Output));
        Assert.Equal(2, call.Args.Count);
        Assert.Equal("tag", Assert.IsType<Expr.Param>(call.Args[0]).Name);
        var param = Assert.IsType<Expr.Param>(call.Args[1]);
        Assert.Equal("items", param.Name);
    }

    [Fact]
    public void Eval_CollectingSourceParameter_ForwardsCollectedItemsAsSpread()
    {
        // Genuine variadic forwarding: the caller's own collected list is the source, so
        // the synthesized call is `Target(tag, items*)` and the collected items
        // round-trip exactly (spread(collect(xs)) = xs).
        var source = """
            Target(tag, *items) = items
            Use(tag, *items) = Target
            Use(0, 1, 2)
            """;
        var list = Assert.IsType<Result.ListValue>(EvalValue(source));
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], list.Items, Result.ValueComparer);

        var listArgSource = """
            Target(tag, *items) = items
            Use(tag, *items) = Target
            Use(0, [1, 2])
            """;
        var outerList = Assert.IsType<Result.ListValue>(EvalValue(listArgSource));
        var innerList = Assert.IsType<Result.ListValue>(Assert.Single(outerList.Items));
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], innerList.Items, Result.ValueComparer);
    }

    [Fact]
    public void Eval_SequenceValueOrdinaryCaller_NameMismatchStaysUnresolved()
    {
        // Nothing ever silently spreads — or renames — the caller's ordinary sequence-value
        // parameter. In a FORMULA the callee works with no arguments, so its bare name is its
        // zero-argument value demand (Q-03), which collects NOTHING: 0. As a LONE row, bare
        // forwarding is BY NAME (FWD-02) and no binding is named `values`, so nothing is forwarded
        // and the row is the same zero-argument value: 0. Silently spreading `sequenceValue`
        // would give 3, forwarding it under another name 1 — that difference is what this pins.
        foreach (var (body, expected) in new[] { ("CountValues + 0", 0m), ("CountValues", 0m) })
        {
            var result = Eval($"CountValues(*values) = values.count\nUse(sequenceValue) = {body}\nUse((1, 2, 3))");
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal([(Decimal128)expected], result.Value);
        }
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

    // -- Math value-demanding lifting carries the caller's rewrite context (K1-03 / K1-04) --
    //
    // A registry-provably strict-value Math consumer decides only THAT its argument slots are
    // value positions; the rewriting inside them is the ordinary implicit-argument rewriting,
    // under the ENCLOSING algorithm's caller configuration. Wrapping an ordinary value-position
    // reference in `Math.Abs(...)` -- the identity on the positive values used below -- must
    // therefore not change which caller name is forwarded, whether it is forwarded as a spread,
    // or whether a closed explicit parameter list permits lifting at all.

    /// <summary>
    /// Projects a <c>Math.X(arg)</c> row down to its single argument, so a wrapped form can be
    /// compared against the unwrapped form's row directly.
    /// </summary>
    private static Expr MathArgument(Expr row)
    {
        var dotCall = Assert.IsType<Expr.DotCall>(row);
        Assert.Equal("Math", Assert.IsType<Expr.Resolve>(dotCall.Target).Name);
        Assert.NotNull(dotCall.Args);
        return Assert.Single(dotCall.Args);
    }

    private static Expr PropertyOutputRow(Algorithm root, string propertyName)
        => Assert.Single(root.Properties.Single(p => p.Name == propertyName).Value.Output);

    private sealed class ParamNameCollector : AstWalker
    {
        public HashSet<string> ParamNames { get; } = [];

        protected override void VisitParameterIdentifier(Expr.Param expr)
            => ParamNames.Add(expr.Name);
    }

    private static HashSet<string> ParamNamesIn(Algorithm algorithm)
    {
        var collector = new ParamNameCollector();
        collector.VisitAlgorithm(algorithm);
        return collector.ParamNames;
    }

    /// <summary>
    /// Structural equality over the shapes these tests synthesize (calls with Param /
    /// SequenceSpread-of-Param arguments, and bare Resolve). Spans are deliberately ignored:
    /// the wrapped and unwrapped spellings occupy different columns, but must otherwise
    /// elaborate to the same tree.
    /// </summary>
    private static void AssertSameLiftingShape(Expr expected, Expr actual)
    {
        switch (expected)
        {
            case Expr.Resolve resolve:
                Assert.Equal(resolve.Name, Assert.IsType<Expr.Resolve>(actual).Name);
                break;
            case Expr.Param param:
                Assert.Equal(param.Name, Assert.IsType<Expr.Param>(actual).Name);
                break;
            case Expr.SequenceSpread spread:
                AssertSameLiftingShape(spread.Operand, Assert.IsType<Expr.SequenceSpread>(actual).Operand);
                break;
            case Expr.Capture capture:
                var actualCapture = Assert.IsType<Expr.Capture>(actual);
                Assert.Equal(capture.Body.Count, actualCapture.Body.Count);
                for (var i = 0; i < capture.Body.Count; i++)
                    AssertSameLiftingShape(capture.Body[i], actualCapture.Body[i]);
                break;
            case Expr.ListLiteral list:
                // A forwarded LIST group is rebuilt as a list literal of its items.
                var actualList = Assert.IsType<Expr.ListLiteral>(actual);
                Assert.Equal(list.Items.Count, actualList.Items.Count);
                for (var i = 0; i < list.Items.Count; i++)
                    AssertSameLiftingShape(list.Items[i], actualList.Items[i]);
                break;
            case Expr.Call call:
                var actualCall = Assert.IsType<Expr.Call>(actual);
                AssertSameLiftingShape(call.Function, actualCall.Function);
                Assert.Equal(call.Args.Count, actualCall.Args.Count);
                for (var i = 0; i < call.Args.Count; i++)
                    AssertSameLiftingShape(call.Args[i], actualCall.Args[i]);
                break;
            default:
                Assert.Fail($"Unexpected shape in lifting comparison: {expected.GetType().Name}");
                break;
        }
    }

    // The K1-03 forwarding tests below use callees that REQUIRE supplied arguments — a required
    // `t` beside the collecting destination, or a group holding the collector — because only
    // such a callee is lifted and forwarded to: a callee that works with no arguments (a lone
    // `*xs`) is read as a value by its bare name (Q-03), so it could not exercise forwarding.

    [Fact]
    public void Resolve_MathArgument_FixedSourceIntoCollectingCallee_SynthesizesUnspreadArgument()
    {
        // K1-03. `K` binds `xs` as a FIXED parameter (lifted from `B(xs)`), so the collecting
        // destination `A(t, *xs)` must receive ONE argument for it. Deciding the spread from the
        // CALLEE's collecting kind -- the last resort an ERASED caller configuration always falls
        // through to -- produced `A(t, xs*)` and silently turned a 1 into a 3.
        var root = Resolve("""
            A(t, *xs) = xs.count
            B(xs) = xs
            K = B, Math.Abs(A)
            """);

        var k = root.Properties.Single(p => p.Name == "K").Value;
        Assert.Equal(["xs", "t"], k.Params);
        Assert.Equal(["xs", "t"], k.ParameterPatterns.Select(parameter => parameter.DisplayName).ToList());

        var call = Assert.IsType<Expr.Call>(MathArgument(k.Output[1]));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(call.Function).Name);
        Assert.Equal(2, call.Args.Count);
        Assert.Equal("t", Assert.IsType<Expr.Param>(call.Args[0]).Name);
        var argument = call.Args[1];
        Assert.IsNotType<Expr.SequenceSpread>(argument);
        Assert.Equal("xs", Assert.IsType<Expr.Param>(argument).Name);
    }

    [Fact]
    public void Resolve_MathArgument_FixedSourceIntoCollectingCallee_MatchesUnwrappedValuePosition()
    {
        // The differential property: the Math wrapper is the ONLY difference between the two
        // programs, so the lifted inner call must be identical.
        var wrapped = Resolve("""
            A(t, *xs) = xs.count
            B(xs) = xs
            K = B, Math.Abs(A)
            """);
        var unwrapped = Resolve("""
            A(t, *xs) = xs.count
            B(xs) = xs
            K = B, A
            """);

        Assert.IsType<Expr.Call>(unwrapped.Properties.Single(p => p.Name == "K").Value.Output[1]);
        AssertSameLiftingShape(
            unwrapped.Properties.Single(p => p.Name == "K").Value.Output[1],
            MathArgument(wrapped.Properties.Single(p => p.Name == "K").Value.Output[1]));
    }

    [Fact]
    public void Eval_MathArgument_FixedSourceIntoCollectingCallee_AgreesWithUnwrappedValuePosition()
    {
        // End-to-end K1-03: `Math.Abs` is the identity on the correct result 1 (the
        // forwarded `A(t, xs)` passes the sequence value as ONE argument, which the
        // collector collects as one item), so any divergence from the unwrapped
        // control is a front-end divergence.
        AssertEval(
            """
            A(t, *xs) = xs.count
            B(xs) = xs
            K = B, Math.Abs(A)
            K((1, 2, 3), 0)
            """,
            1, 2, 3, 1);
        AssertEval(
            """
            A(t, *xs) = xs.count
            B(xs) = xs
            K = B, A
            K((1, 2, 3), 0)
            """,
            1, 2, 3, 1);
        AssertEval(
            """
            A(t, *xs) = xs.count
            B(xs) = xs
            K = B, Math.Abs(A)
            K([1, 2, 3], 0)
            """,
            1, 2, 3, 1);
    }

    [Fact]
    public void Resolve_MathArgument_CollectingSourceNameMismatch_ForwardsCallerName()
    {
        // K1-03's name half. `Use` declares `items`, never `xs`; forwarding under the CALLEE's
        // capture name synthesized a reference to a name the enclosing algorithm does not bind
        // (`Unknown name: xs` at runtime) and mis-marked `Use` as capturing an ancestor's
        // parameter. The callee's one grouped stream is forwarded BY SHAPE from `Use`'s own
        // collector: `Target((items*))`.
        var root = Resolve("""
            Target((*xs)) = xs.count
            Use(*items) = Math.Abs(Target)
            """);

        var use = root.Properties.Single(p => p.Name == "Use");
        Assert.Equal(["items"], use.Value.Params);
        Assert.DoesNotContain("xs", ParamNamesIn(use.Value));
        Assert.Equal(PropertyExposure.Exported, use.Exposure);

        var call = Assert.IsType<Expr.Call>(MathArgument(Assert.Single(use.Value.Output)));
        Assert.Equal("Target", Assert.IsType<Expr.Resolve>(call.Function).Name);
        var group = Assert.IsType<Expr.Capture>(Assert.Single(call.Args));
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(group.Body));
        Assert.Equal("items", Assert.IsType<Expr.Param>(spread.Operand).Name);
    }

    /// <summary>The one element of a list-element formula row <c>[e]:0</c>: an ordinary value position.</summary>
    private static Expr ListElement(Expr row)
        => Assert.Single(Assert.IsType<Expr.ListLiteral>(Assert.IsType<Expr.Index>(row).Target).Items);

    [Fact]
    public void Resolve_MathArgument_CollectingSourceNameMismatch_MatchesUnwrappedValuePosition()
    {
        var wrapped = Resolve("""
            Target((*xs)) = xs.count
            Use(*items) = Math.Abs(Target)
            """);
        var unwrapped = Resolve("""
            Target((*xs)) = xs.count
            Use(*items) = [Target]:0
            """);

        Assert.IsType<Expr.Call>(ListElement(PropertyOutputRow(unwrapped, "Use")));
        AssertSameLiftingShape(
            ListElement(PropertyOutputRow(unwrapped, "Use")),
            MathArgument(PropertyOutputRow(wrapped, "Use")));
    }

    [Fact]
    public void Eval_MathArgument_CollectingSourceNameMismatch_AgreesWithUnwrappedValuePosition()
    {
        AssertEval(
            """
            Target((*xs)) = xs.count
            Use(*items) = Math.Abs(Target)
            Use(1, 2, 3)
            """,
            3);
        AssertEval(
            """
            Target((*xs)) = xs.count
            Use(*items) = [Target]:0
            Use(1, 2, 3)
            """,
            3);
    }

    [Fact]
    public void Resolve_MathArgument_CollectingSourceIntoCollectingCallee_KeepsForwardingSpread()
    {
        // The legal forwarding direction must survive the fix: a COLLECTING caller binding
        // still re-spreads into a collecting destination (spread(collect(xs)) = xs).
        var root = Resolve("""
            Target(t, *items) = items.count
            Use(t, *items) = Math.Abs(Target)
            """);

        var call = Assert.IsType<Expr.Call>(MathArgument(PropertyOutputRow(root, "Use")));
        Assert.Equal(2, call.Args.Count);
        Assert.Equal("t", Assert.IsType<Expr.Param>(call.Args[0]).Name);
        var spread = Assert.IsType<Expr.SequenceSpread>(call.Args[1]);
        Assert.Equal("items", Assert.IsType<Expr.Param>(spread.Operand).Name);

        AssertEval(
            """
            Target(t, *items) = items.count
            Use(t, *items) = Math.Abs(Target)
            Use(0, 1, 2)
            """,
            2);
    }

    [Fact]
    public void Resolve_MathArgument_FixedSourceIntoFixedCallee_ForwardsCallerParameter()
    {
        // Ordinary fixed -> fixed lifting inside a Math argument keeps working: the value
        // position still lifts (that is what makes Math arguments value-demanding at all).
        var root = Resolve("""
            Helper(n) = n + 1
            Use = Math.Abs(Helper)
            """);

        var use = root.Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(["n"], use.Params);

        var call = Assert.IsType<Expr.Call>(MathArgument(Assert.Single(use.Output)));
        Assert.Equal("Helper", Assert.IsType<Expr.Resolve>(call.Function).Name);
        Assert.Equal("n", Assert.IsType<Expr.Param>(Assert.Single(call.Args)).Name);

        AssertEval(
            """
            Helper(n) = n + 1
            Use = Math.Abs(Helper)
            Use(4)
            """,
            5);
    }

    [Fact]
    public void Resolve_MathAliasArgument_CarriesCallerContextLikeCanonicalSpelling()
    {
        // Both value-demanding spellings share one implementation: the prelude ALIAS call
        // `abs(...)` must carry the caller's configuration exactly like `Math.Abs(...)`.
        var root = Resolve("""
            A(t, *xs) = xs.count
            B(xs) = xs
            K = B, abs(A)
            """);

        var aliasCall = Assert.IsType<Expr.Call>(root.Properties.Single(p => p.Name == "K").Value.Output[1]);
        Assert.Equal("abs", Assert.IsType<Expr.Resolve>(aliasCall.Function).Name);

        var lifted = Assert.IsType<Expr.Call>(Assert.Single(aliasCall.Args));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(lifted.Function).Name);
        Assert.Equal(2, lifted.Args.Count);
        var argument = lifted.Args[1];
        Assert.IsNotType<Expr.SequenceSpread>(argument);
        Assert.Equal("xs", Assert.IsType<Expr.Param>(argument).Name);
    }

    [Fact]
    public void Resolve_MathArgument_ClosedExplicitParameterList_DoesNotLiftBareParameterizedHelper()
    {
        // K1-04, the Math-wrapped twin of
        // Resolve_ExplicitParameterList_DoesNotLiftBareParameterizedHelper. An explicit
        // parameter list is CLOSED; a strict-value Math wrapper is not an escape hatch from it.
        // The helper REQUIRES its `first` argument, so its value can only come from a
        // forwarding the closed list refuses — the front end rejects the position.
        var root = ResolveRejected("""
            CountItems(first, *items) = items.count
            Use(value) = Math.Abs(CountItems)
            """);

        var use = root.Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(["value"], use.Params);
        Assert.DoesNotContain("items", use.Params);

        var resolve = Assert.IsType<Expr.Resolve>(MathArgument(Assert.Single(use.Output)));
        Assert.Equal("CountItems", resolve.Name);
    }

    [Fact]
    public void Resolve_MathArgument_ClosedExplicitParameterList_ReadsAZeroArgumentHelperAsAValue()
    {
        // Q-03 (formerly PV-27): a helper that works with no arguments is never a forwarding
        // candidate, so a closed list has nothing to refuse — the strict Math position demands
        // its zero-argument value, which is legal, and the front end accepts the program.
        var root = Resolve("""
            CountItems(*items) = items.count
            Use(value) = Math.Abs(CountItems)
            """);

        var use = root.Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(["value"], use.Params);
        Assert.Equal("CountItems", Assert.IsType<Expr.Resolve>(MathArgument(Assert.Single(use.Output))).Name);

        AssertEval(
            """
            CountItems(*items) = items.count
            Use(value) = Math.Abs(CountItems) + value
            Use(5)
            """,
            5);
    }

    [Fact]
    public void Resolve_MathArgument_ClosedExplicitParameterList_ForwardsTheCapturedAncestorParameter()
    {
        // The audit's K1-04 repro, under the Q-04 decision (September 28 2026). `F`'s explicit
        // list is `(x)`, but G's rows use `y`, so a `y` written in F already denotes G's parameter:
        // automatic forwarding reuses that captured ancestor binding for `A`, exactly as it does in
        // an inferring body, and adds nothing to F's closed list. (Before the decision the closed
        // list refused the forwarding and the program was a front-end error; K1-04 had observed
        // the same forwarding produced by a degenerate caller configuration that the unwrapped
        // control did NOT share — both spellings now agree, see the next test.)
        var root = Resolve("""
            A = y + 1
            G = {
              F(x) = Math.Abs(A)
              F(1) + y
            }
            """);

        var g = root.Properties.Single(p => p.Name == "G").Value;
        var f = g.Properties.Single(p => p.Name == "F");

        Assert.Equal(["y"], g.Params);
        Assert.Equal(["x"], f.Value.Params);
        // F reads G's `y`, so it is local to G's activation.
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, f.Exposure);

        var call = Assert.IsType<Expr.Call>(MathArgument(Assert.Single(f.Value.Output)));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(call.Function).Name);
        Assert.Equal("y", Assert.IsType<Expr.Param>(Assert.Single(call.Args)).Name);
    }

    [Fact]
    public void Resolve_MathArgument_ClosedExplicitParameterList_MatchesUnwrappedValuePosition()
    {
        var wrapped = Resolve("""
            A = y + 1
            G = {
              F(x) = Math.Abs(A)
              F(1) + y
            }
            """);
        var unwrapped = Resolve("""
            A = y + 1
            G = {
              F(x) = [A]:0
              F(1) + y
            }
            """);

        static Property NestedF(Algorithm root)
            => root.Properties.Single(p => p.Name == "G").Value.Properties.Single(p => p.Name == "F");

        AssertSameLiftingShape(
            ListElement(Assert.Single(NestedF(unwrapped).Value.Output)),
            MathArgument(Assert.Single(NestedF(wrapped).Value.Output)));
        Assert.Equal(NestedF(unwrapped).Exposure, NestedF(wrapped).Exposure);
        Assert.Equal(NestedF(unwrapped).Value.Params, NestedF(wrapped).Value.Params);
    }

    [Theory]
    [InlineData("F(x) = Math.Abs(A)")]
    [InlineData("F(x) = [A]:0")]
    public void Eval_ClosedExplicitParameterList_ReadsTheCapturedAncestorParameter(string f)
    {
        // Q-04: `A`'s `y` is G's `y` (10) — the binding a `y` written in F denotes — so F(1) is
        // |10 + 1| = 11 and G(10) is 21, whether or not a strict Math consumer wraps the reference.
        // F's own closed list is unchanged: forwarding reuses the ancestor binding, it never adds
        // a parameter F did not write.
        var source = $"A = y + 1\nG = {{\n  {f}\n  F(1) + y\n}}\nG(10)";
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(Resolve(source)));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
        Assert.Equal<Decimal128>([21], result.Value);
    }

    [Fact]
    public void Eval_ClosedExplicitParameterList_LoneRow_ForwardsByName()
    {
        // FWD-02 bare forwarding: the lone row `F(x) = A` hands A the EXISTING binding of A's own
        // parameter name `y` — the one a `y` written in F denotes, G's inferred `y` (Q-04) — and
        // never renames F's `x` to it: F(1) is 11 and G(10) is 21, exactly the formula's answer.
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(Resolve("A = y + 1\nG = {\n  F(x) = A\n  F(1) + y\n}\nG(10)")));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
        Assert.Equal<Decimal128>([21], result.Value);
    }

    [Theory]
    // The Math-ALIAS Resolve arm and the bare canonical `Math.X` argumentless-DotCall arm are
    // the other two gated lift sites. Both are reachable inside a value-demanding bundle, and
    // pre-fix both invented the member's own parameter names (`value`, `digits`) inside a
    // CLOSED explicit list, exactly like the ordinary Resolve arm.
    [InlineData("Use(v) = Math.Abs(round)")]
    [InlineData("Use(v) = Math.Abs(Math.Round)")]
    public void Resolve_MathArgument_ClosedExplicitParameterList_DoesNotLiftBareMathMemberReference(string source)
    {
        var root = ResolveRejected(source);
        var use = root.Properties.Single(p => p.Name == "Use").Value;

        Assert.Equal(["v"], use.Params);
        Assert.Empty(ParamNamesIn(use));

        var argument = MathArgument(Assert.Single(use.Output));
        Assert.False(
            argument is Expr.Call or Expr.DotCall { Args: not null },
            $"The closed list of Use must not lift the Math member reference: {argument}");
    }

    [Theory]
    // The open-list twins of the two arms above: lifting there is legal and must still happen,
    // so the gate cannot be over-blocking.
    [InlineData("Use = Math.Abs(round)")]
    [InlineData("Use = Math.Abs(Math.Round)")]
    public void Resolve_MathArgument_OpenParameterList_StillLiftsBareMathMemberReference(string source)
    {
        var root = Resolve(source);
        var use = root.Properties.Single(p => p.Name == "Use").Value;

        Assert.NotEmpty(use.Params);

        var liftedArgs = MathArgument(Assert.Single(use.Output)) switch
        {
            Expr.Call call => call.Args,
            Expr.DotCall { Args: { } dotArgs } => dotArgs,
            var other => throw new Xunit.Sdk.XunitException($"Expected a lifted call, got {other}"),
        };
        Assert.Equal(
            use.Params,
            liftedArgs.Select(argument => Assert.IsType<Expr.Param>(argument).Name).ToList());
    }

    [Fact]
    public void Resolve_MathArgument_ClosedExplicitListStillLiftsWhatItDeclares()
    {
        // The gate must not over-block: when the closed list DOES declare the capture the
        // synthesized argument needs, the Math argument lifts exactly like the bare row.
        var root = Resolve("""
            A = y + 1
            Use(y) = Math.Abs(A)
            """);

        var use = root.Properties.Single(p => p.Name == "Use").Value;
        Assert.Equal(["y"], use.Params);

        var call = Assert.IsType<Expr.Call>(MathArgument(Assert.Single(use.Output)));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(call.Function).Name);
        Assert.Equal("y", Assert.IsType<Expr.Param>(Assert.Single(call.Args)).Name);

        AssertEval(
            """
            A = y + 1
            Use(y) = Math.Abs(A)
            Use(10)
            """,
            11);
    }

    // -- The value-demanding rewrite memo must stay caller-context sound -----------

    [Fact]
    public void Resolve_MathArgument_FixedAndCollectingCallers_DoNotShareRewrite()
    {
        // Two callers, ONE destination and one written argument shape. The fixed caller must
        // forward one argument and the collecting caller must forward a spread -- in BOTH
        // declaration orders, so the result cannot come from whichever context happened to
        // populate a memo first.
        static void AssertBothCallers(string source)
        {
            var root = Resolve(source);

            var fixedCall = Assert.IsType<Expr.Call>(MathArgument(PropertyOutputRow(root, "FixedCaller")));
            Assert.Equal(2, fixedCall.Args.Count);
            var fixedArgument = fixedCall.Args[1];
            Assert.IsNotType<Expr.SequenceSpread>(fixedArgument);
            Assert.Equal("zs", Assert.IsType<Expr.Param>(fixedArgument).Name);

            var collectingCall = Assert.IsType<Expr.Call>(MathArgument(PropertyOutputRow(root, "CollectingCaller")));
            Assert.Equal(2, collectingCall.Args.Count);
            var collectingSpread = Assert.IsType<Expr.SequenceSpread>(collectingCall.Args[1]);
            Assert.Equal("zs", Assert.IsType<Expr.Param>(collectingSpread.Operand).Name);
        }

        AssertBothCallers("""
            Target(t, *zs) = zs.count
            FixedCaller(t, zs) = Math.Abs(Target)
            CollectingCaller(t, *zs) = Math.Abs(Target)
            """);

        AssertBothCallers("""
            Target(t, *zs) = zs.count
            CollectingCaller(t, *zs) = Math.Abs(Target)
            FixedCaller(t, zs) = Math.Abs(Target)
            """);
    }

    [Fact]
    public void Eval_MathArgument_FixedAndCollectingCallers_ProduceTheirOwnResults()
    {
        // The same separation, end to end: the fixed caller forwards ONE argument —
        // a list and a sequence value alike stay one collected item — while the
        // collecting caller re-supplies its three collected items.
        AssertEval(
            """
            Target(t, *zs) = zs.count
            FixedCaller(t, zs) = Math.Abs(Target)
            CollectingCaller(t, *zs) = Math.Abs(Target)
            FixedCaller(0, [1, 2, 3]), FixedCaller(0, (1, 2, 3)), CollectingCaller(0, 1, 2, 3)
            """,
            1, 1, 3);
    }

    [Fact]
    public void Resolve_MathArgument_DifferentCallerNames_ForwardTheirOwnName()
    {
        // Two callers spell the same callee capture differently; each rewritten call must use
        // its OWN caller name, in both declaration orders (forwarding by shape into the
        // callee's one grouped stream).
        static void AssertBothNames(string source)
        {
            var root = Resolve(source);

            foreach (var (property, expectedName) in new[] { ("UseItems", "items"), ("UseValues", "values") })
            {
                var call = Assert.IsType<Expr.Call>(MathArgument(PropertyOutputRow(root, property)));
                var group = Assert.IsType<Expr.Capture>(Assert.Single(call.Args));
                var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(group.Body));
                Assert.Equal(expectedName, Assert.IsType<Expr.Param>(spread.Operand).Name);
            }
        }

        AssertBothNames("""
            Target((*xs)) = xs.count
            UseItems(*items) = Math.Abs(Target)
            UseValues(*values) = Math.Abs(Target)
            """);

        AssertBothNames("""
            Target((*xs)) = xs.count
            UseValues(*values) = Math.Abs(Target)
            UseItems(*items) = Math.Abs(Target)
            """);
    }

    [Fact]
    public void Resolve_MathArgument_ClosedAndOpenParameterLists_DoNotShareRewrite()
    {
        // The same Math argument shape in an algorithm where lifting is legal and in one whose
        // explicit list forbids it. Neither context may inherit the other's rewrite, in either
        // declaration order.
        static void AssertBothGates(string source)
        {
            var root = ResolveRejected(source);

            var lifted = Assert.IsType<Expr.Call>(MathArgument(PropertyOutputRow(root, "OpenList")));
            Assert.Equal("Helper", Assert.IsType<Expr.Resolve>(lifted.Function).Name);
            Assert.Equal("n", Assert.IsType<Expr.Param>(Assert.Single(lifted.Args)).Name);
            Assert.Equal(["n"], root.Properties.Single(p => p.Name == "OpenList").Value.Params);

            var blocked = Assert.IsType<Expr.Resolve>(MathArgument(PropertyOutputRow(root, "ClosedList")));
            Assert.Equal("Helper", blocked.Name);
            Assert.Equal(["other"], root.Properties.Single(p => p.Name == "ClosedList").Value.Params);
        }

        AssertBothGates("""
            Helper(n) = n + 1
            OpenList = Math.Abs(Helper)
            ClosedList(other) = Math.Abs(Helper)
            """);

        AssertBothGates("""
            Helper(n) = n + 1
            ClosedList(other) = Math.Abs(Helper)
            OpenList = Math.Abs(Helper)
            """);
    }

    [Fact]
    public void Resolve_SharedNodeInMathArgumentAndValueRow_RewritesIdentically()
    {
        // A host-built DAG puts ONE Expr.Resolve node in an ordinary value row AND inside a
        // Math argument of the SAME algorithm. Value-demanding is WHERE lifting happens, never
        // HOW, so both reaches must produce the SAME rewrite -- which is exactly why the
        // region's rewrite memo may unify them. Pre-fix the two sub-contexts rewrote under
        // different configurations and produced `Target(items*)` and `Target(xs*)`.
        var scope = (Algorithm.User)SourceProvenance.ParseValid("""
            Target((*xs)) = xs.count
            Use(*items) = 0
            """).Root;

        var shared = new Expr.Resolve("Target");
        var root = scope with
        {
            Properties = scope.Properties
                .Select(p => p.Name == "Use"
                    ? p.WithValue(Assert.IsType<Algorithm.User>(p.Value) with
                    {
                        Output = new OutputBundle([
                            shared,
                            new Expr.DotCall(new Expr.Resolve("Math"), "Abs", new OutputBundle([shared])),
                        ]),
                    })
                    : p)
                .ToList(),
        };

        var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(root);
        Assert.Empty(detectorDiagnostics);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected);

        var resolvedUse = resolved.Properties.Single(p => p.Name == "Use").Value;
        var valueRow = resolvedUse.Output[0];

        var call = Assert.IsType<Expr.Call>(valueRow);
        Assert.Equal("Target", Assert.IsType<Expr.Resolve>(call.Function).Name);
        var group = Assert.IsType<Expr.Capture>(Assert.Single(call.Args));
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(group.Body));
        Assert.Equal("items", Assert.IsType<Expr.Param>(spread.Operand).Name);

        // Same node reference in, same rewritten node out: the region's memo unifies the two
        // positions precisely because they carry ONE caller configuration.
        Assert.Same(valueRow, MathArgument(resolvedUse.Output[1]));
    }

    [Fact]
    public void Resolve_SharedNodeInMathArgumentsOfDifferentCallers_RewritesPerCaller()
    {
        // The cross-region tripwire: ONE shared Expr.Resolve node reached from the Math
        // arguments of two DIFFERENT algorithms whose bindings disagree. A rewrite memo shared
        // across algorithms (or keyed structurally rather than per region) would serve the
        // first caller's rewrite to the second.
        var scope = (Algorithm.User)SourceProvenance.ParseValid("""
            Target(t, *zs) = zs.count
            FixedCaller(t, zs) = 0
            CollectingCaller(t, *zs) = 0
            """).Root;

        var shared = new Expr.Resolve("Target");
        var root = scope with
        {
            Properties = scope.Properties
                .Select(p => p.Name is "FixedCaller" or "CollectingCaller"
                    ? p.WithValue(Assert.IsType<Algorithm.User>(p.Value) with
                    {
                        Output = new OutputBundle([
                            new Expr.DotCall(new Expr.Resolve("Math"), "Abs", new OutputBundle([shared])),
                        ]),
                    })
                    : p)
                .ToList(),
        };

        var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(root);
        Assert.Empty(detectorDiagnostics);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected);

        var fixedCall = Assert.IsType<Expr.Call>(MathArgument(PropertyOutputRow(resolved, "FixedCaller")));
        Assert.Equal(2, fixedCall.Args.Count);
        var fixedArgument = fixedCall.Args[1];
        Assert.IsNotType<Expr.SequenceSpread>(fixedArgument);
        Assert.Equal("zs", Assert.IsType<Expr.Param>(fixedArgument).Name);

        var collectingCall = Assert.IsType<Expr.Call>(MathArgument(PropertyOutputRow(resolved, "CollectingCaller")));
        Assert.Equal(2, collectingCall.Args.Count);
        var collectingSpread = Assert.IsType<Expr.SequenceSpread>(collectingCall.Args[1]);
        Assert.Equal("zs", Assert.IsType<Expr.Param>(collectingSpread.Operand).Name);
    }

    [Fact]
    public void Resolve_MathArgument_NestedExplicitAlgorithmUsesItsOwnFixedContext()
    {
        var root = Resolve("""
            Target(t, *value) = value.count
            Outer(*outer) = {
              Inner(t, value) = Math.Abs(Target)
              Inner(0, outer)
            }
            """);

        var outer = root.Properties.Single(property => property.Name == "Outer").Value;
        var inner = outer.Properties.Single(property => property.Name == "Inner").Value;
        Assert.Equal(["t", "value"], inner.Params);

        var call = Assert.IsType<Expr.Call>(MathArgument(Assert.Single(inner.Output)));
        Assert.Equal(2, call.Args.Count);
        var argument = call.Args[1];
        Assert.IsNotType<Expr.SequenceSpread>(argument);
        Assert.Equal("value", Assert.IsType<Expr.Param>(argument).Name);
    }

    [Fact]
    public void Resolve_NestedValueDemandingCallsCarryOneCallerContext()
    {
        var root = Resolve("""
            Target((*xs)) = xs.count
            Use(*items) = Math.Abs(abs(Target))
            """);

        var aliasCall = Assert.IsType<Expr.Call>(MathArgument(PropertyOutputRow(root, "Use")));
        Assert.Equal("abs", Assert.IsType<Expr.Resolve>(aliasCall.Function).Name);
        var targetCall = Assert.IsType<Expr.Call>(Assert.Single(aliasCall.Args));
        var group = Assert.IsType<Expr.Capture>(Assert.Single(targetCall.Args));
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(group.Body));
        Assert.Equal("items", Assert.IsType<Expr.Param>(spread.Operand).Name);

        AssertEval("""
            Target((*xs)) = xs.count
            Use(*items) = Math.Abs(abs(Target))
            Use(1, 2, 3)
            """, 3);
    }

    [Theory]
    [InlineData("Math.Round(Target, 0)")]
    [InlineData("round(Target, 0)")]
    public void Resolve_NonUnaryMathArgument_CanonicalAndAliasCarryCallerContext(string expression)
    {
        var root = Resolve($$"""
            Target((*xs)) = xs.count
            Use(*items) = {{expression}}
            """);

        var mathCall = PropertyOutputRow(root, "Use");
        var targetCall = mathCall switch
        {
            Expr.DotCall { Args: { } args } => Assert.IsType<Expr.Call>(args[0]),
            Expr.Call { Args: { } args } => Assert.IsType<Expr.Call>(args[0]),
            _ => throw new Xunit.Sdk.XunitException($"Expected a Math call, got {mathCall}"),
        };
        var group = Assert.IsType<Expr.Capture>(Assert.Single(targetCall.Args));
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(group.Body));
        Assert.Equal("items", Assert.IsType<Expr.Param>(spread.Operand).Name);
    }

    [Theory]
    [InlineData("Math.Abs(Target)")]
    [InlineData("abs(Target)")]
    public void Resolve_MathArgument_CollectingSourceIntoFixedCalleeDoesNotSpread(string expression)
    {
        var root = Resolve($$"""
            Target(items) = items.count
            Use(*items) = {{expression}}
            """);

        var mathCall = PropertyOutputRow(root, "Use");
        var targetCall = mathCall switch
        {
            Expr.DotCall { Args: { } args } => Assert.IsType<Expr.Call>(Assert.Single(args)),
            Expr.Call { Args: { } args } => Assert.IsType<Expr.Call>(Assert.Single(args)),
            _ => throw new Xunit.Sdk.XunitException($"Expected a Math call, got {mathCall}"),
        };
        var argument = Assert.Single(targetCall.Args);
        Assert.IsNotType<Expr.SequenceSpread>(argument);
        Assert.Equal("items", Assert.IsType<Expr.Param>(argument).Name);

        AssertEval($$"""
            Target(items) = items.count
            Use(*items) = {{expression}}
            Use(1, 2, 3)
            """, 3);
    }

    [Fact]
    public void Resolve_SharedArgumentBundleAcrossMathSpellingsPreservesSharedRewrite()
    {
        var parsed = (Algorithm.User)Resolve("""
            Target((*xs)) = xs.count
            Use(*items) = 0
            """);
        var sharedResolve = new Expr.Resolve("Target");
        var sharedArgs = new OutputBundle([sharedResolve]);
        var root = parsed with
        {
            Properties = parsed.Properties
                .Select(property => property.Name == "Use"
                    ? property.WithValue(Assert.IsType<Algorithm.User>(property.Value) with
                    {
                        Output = new OutputBundle([
                            new Expr.DotCall(new Expr.Resolve("Math"), "Abs", sharedArgs),
                            new Expr.Call(new Expr.Resolve("abs"), sharedArgs),
                        ]),
                    })
                    : property)
                .ToList(),
        };

        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(root);
        var use = resolved.Properties.Single(property => property.Name == "Use").Value;
        var canonicalArgument = MathArgument(use.Output[0]);
        var aliasArgument = Assert.Single(Assert.IsType<Expr.Call>(use.Output[1]).Args);

        Assert.Same(canonicalArgument, aliasArgument);
        var targetCall = Assert.IsType<Expr.Call>(canonicalArgument);
        var group = Assert.IsType<Expr.Capture>(Assert.Single(targetCall.Args));
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(group.Body));
        Assert.Equal("items", Assert.IsType<Expr.Param>(spread.Operand).Name);
    }

    [Fact]
    public async Task Eval_MathArgumentRewrite_AgreesAcrossSyncGenericAndSuspendingTwin()
    {
        // `Target` requires its `t`, so both Math arguments are genuine forwarding rewrites:
        // the fixed caller forwards `Target(t, xs)` (one collected item) and the collecting
        // caller `Target(t, xs*)` (three).
        const string source = """
            Seed = 0
            Target(t, *xs) = t + xs.count
            Fixed(t, xs) = Math.Abs(Target)
            Collecting(t, *xs) = abs(Target)
            Fixed(0, (1, 2, 3)) + Seed, Collecting(0, 1, 2, 3)
            """;
        var ast = new Expr.AlgorithmExpr(Resolve(source));
        var syncDefault = Evaluator.RunCounted(ast);
        var (syncGeneric, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var cache = new AsyncEvaluation.SuspendingAsyncZeroArgPropertyResultCache();
        var pendingAsyncTwin = Evaluator.RunCountedAsync(ast, cache);
        var asyncTwin = await AsyncEvaluation.AsyncEvaluationHarness.Complete(
            pendingAsyncTwin);

        Assert.Equal("ok raw=S[1, 3] n=2", AsyncEvaluation.AsyncEvaluationHarness.NeutralOf(syncDefault));
        Assert.Equal(
            AsyncEvaluation.AsyncEvaluationHarness.NeutralOf(syncDefault),
            AsyncEvaluation.AsyncEvaluationHarness.NeutralOf(syncGeneric));
        Assert.Equal(
            AsyncEvaluation.AsyncEvaluationHarness.NeutralOf(syncDefault),
            AsyncEvaluation.AsyncEvaluationHarness.NeutralOf(asyncTwin));
        Assert.True(cache.AsyncAccesses > 0);
        Assert.Equal(cache.AsyncAccesses, cache.ThreadHops.Count);
    }

    // ── Conditional branch bodies resolve under the closed branch-pattern rule (B2b) ──
    //
    // A branch pattern is the same kind of CLOSED input specification as a written explicit
    // parameter list: the body's only inputs are its pattern binders, and its Parameters
    // stay empty by invariant. The open implicit-lifting path used to run on branch bodies
    // and invented body parameters that nothing ever bound (`Unknown name` at runtime).

    [Fact]
    public void Resolve_ConditionalBranch_LiftsThroughBinder_WithoutInventingBodyParameters()
    {
        var source = """
            A = n + 1
            F(0) = 0
            F(n) = A
            """;
        var root = Resolve(source);

        var f = Assert.IsType<Algorithm.Conditional>(root.Properties.Single(p => p.Name == "F").Value);
        var body = f.Branches[1].Body;
        Assert.Empty(body.Params);

        var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(call.Function).Name);
        Assert.Equal("n", Assert.IsType<Expr.Param>(Assert.Single(call.Args)).Name);

        Assert.Equal([5m], Eval(source + "\nF(4)").Value);
    }

    [Fact]
    public void Resolve_ConditionalBranch_DoesNotLiftBareParameterizedHelper()
    {
        // Mirror of Resolve_ExplicitParameterList_DoesNotLiftBareParameterizedHelper: in a FORMULA
        // `A` needs `x`, which the pattern `0` does not bind, so the reference stays bare and the
        // body invents no parameter. Evaluation then reports the ordinary arity error of the
        // zero-argument value demand — never `Unknown name` for a parameter nobody binds.
        var source = """
            A = x + 1
            F(0) = A + 0
            F(n) = n
            """;
        var root = Resolve(source);

        var f = Assert.IsType<Algorithm.Conditional>(root.Properties.Single(p => p.Name == "F").Value);
        var body = f.Branches[0].Body;
        Assert.Empty(body.Params);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.IsType<Expr.Binary>(Assert.Single(body.Output)).Left).Name);

        var result = Eval(source + "\nF(0)");
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext withContext)
            error = withContext.Inner;
        Assert.IsType<EvalError.ArityMismatch>(error);

        // A LONE row is bare forwarding BY NAME (FWD-02): the head `0` binds no `x` and a literal is
        // never forwarded, so `F(0) = A` is rejected at the front end, naming `x`; the row stays
        // as written and the branch invents no parameter.
        var lone = source.Replace(" + 0", "", StringComparison.Ordinal);
        var rejection = Assert.Single(SourceProvenance.ExpectFrontEndError(lone));
        Assert.Equal(DiagnosticCode.UnforwardableParameter, rejection.Code);
        Assert.Contains("'x'", rejection.Message, StringComparison.Ordinal);
        var rejected = SourceProvenance.ParseAllowingDiagnostics(lone).Root;
        var rejectedBody = Assert.IsType<Algorithm.Conditional>(rejected.Properties.Single(p => p.Name == "F").Value).Branches[0].Body;
        Assert.Empty(rejectedBody.Params);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(rejectedBody.Output)).Name);
    }
}
