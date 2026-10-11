using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// The Model-C binder's cardinality structure (C# evaluator cleanup, October 2026; no observable
/// change for any validated program). The tests pin four things:
/// <list type="bullet">
///   <item>ONE supplied-slot rule, <see cref="PatternLevelArity"/>, read by every layer that decides or
///   reports a cardinality.</item>
///   <item>Exactly ONE cardinality decision per pattern level: a caller's own shaped report or the
///   binder's gate at the top, and the binder's gate at each structural level.</item>
///   <item>The pure allocation of an accepted level, <see cref="Evaluator.NeedSourceRange"/>, which
///   stays inside the supply for every count the rule accepts.</item>
///   <item>Every caller's own diagnostic shape for its top-level rejection. It is decided after
///   supply formation's explicit spreads and before any VALUE demand, on all six routes.</item>
/// </list>
/// </summary>
public sealed class BinderCardinalityGateTests
{
    [Fact]
    public void PatternLevelArity_IsOneRule_ForEveryLevelShape()
    {
        for (var count = 0; count <= 8; count++)
        {
            foreach (var collects in new[] { false, true })
            {
                if (collects && count == 0)
                    continue;

                var arity = new PatternLevelArity(count, collects);
                Assert.Equal(collects ? count - 1 : count, arity.Minimum);
                Assert.Equal(collects ? null : count, arity.Maximum);
                for (var supplied = 0; supplied <= count + 4; supplied++)
                {
                    var expected = supplied >= arity.Minimum && (arity.Maximum is null || supplied <= arity.Maximum);
                    Assert.Equal(expected, arity.Accepts(supplied));
                }
            }
        }
    }

    public static TheoryData<string> SignatureHeads => new()
    {
        "F(a)",
        "F(a, b)",
        "F(*xs)",
        "F(a, *xs)",
        "F(*xs, z)",
        "F(a, *xs, z)",
        "F(a, b, *xs, y, z)",
        "F((a, b))",
        "F([a, b])",
        "F((a, *r))",
        "F([a, *r], b)",
        "F((a, b), *rest)",
        "F(x, (a, (b, c)), [d, *e])",
    };

    /// <summary>
    /// The signature minimum, zero-supply acceptance, the evaluator's zero-argument law, the
    /// signature arity facts, the binding plan, and the binder's own call gate all read one rule.
    /// An ordinary call with <c>n</c> scalar arguments is refused at its own gate exactly when the
    /// rule refuses <c>n</c>. Scalars never satisfy a structural pattern, so an accepted count with a
    /// structural head fails later as a KIND mismatch, never as a top-level arity rejection.
    /// </summary>
    [Theory]
    [MemberData(nameof(SignatureHeads))]
    public void EveryLayer_ReadsTheOneSuppliedSlotRule(string head)
    {
        var user = Definition(head);
        var patterns = user.ParameterPatterns;
        var arity = PatternLevelArity.Of(patterns);

        Assert.Equal(arity.Minimum, ParameterPattern.MinimumSuppliedSlots(patterns));
        Assert.Equal(arity.Accepts(0), ParameterPattern.AcceptsZeroSuppliedSlots(patterns));
        Assert.Equal(arity.Accepts(0), Evaluator.AcceptsZeroSuppliedArguments(user));

        var signature = CallableSignature.FromUserAlgorithm("F", user);
        Assert.Equal(arity.Accepts(0), signature.AcceptsZeroSuppliedArguments);
        var facts = CallableSignatureDiagnostics.GetArityFacts(signature);
        Assert.Equal(arity.Minimum, facts.MinTopLevelArgumentCount);
        Assert.Equal(arity.Maximum, facts.MaxTopLevelArgumentCount);
        var plan = CallableBindingPlan.FromSignature(signature);
        Assert.Equal(arity.Minimum, plan.TopLevelPatternList.MinSlotCount);
        Assert.Equal(arity.Maximum, plan.TopLevelPatternList.MaxSlotCount);

        for (var supplied = 0; supplied <= patterns.Count + 2; supplied++)
        {
            var call = $"F({string.Join(", ", Enumerable.Repeat("1", supplied))})";
            var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid($"{head} = 0\n{call}").Root));
            var refusedAtTheGate = result.IsError && Innermost(result.Error) switch
            {
                EvalError.ArityMismatch mismatch => (mismatch.Expected, mismatch.Actual) == (arity.Minimum, supplied),
                EvalError.VariadicArityMismatch mismatch => (mismatch.ExpectedMinimum, mismatch.Actual) == (arity.Minimum, supplied),
                _ => false,
            };
            Assert.True(refusedAtTheGate == !arity.Accepts(supplied), $"{call}: {(result.IsError ? result.Error : "ok")}");
        }
    }

    /// <summary>
    /// The allocation of every accepted level, for every level shape up to eight patterns and every
    /// position of its FIRST collecting capture (the only one allocation reads; none is -1), places
    /// each supplied cell in exactly one range, in written order, with no gap. The first collecting
    /// capture collects the leftover. A later collecting capture, on a level X-02 refuses before
    /// evaluation, takes one cell like a fixed pattern, and the level keeps the one-collector minimum.
    /// So even there no accepted count reaches an index outside the supply.
    /// </summary>
    [Fact]
    public void Allocation_OfEveryAcceptedLevel_CoversTheSupplyExactlyOnceInOrder()
    {
        for (var count = 0; count <= 8; count++)
        {
            for (var collector = -1; collector < count; collector++)
            {
                var arity = new PatternLevelArity(count, collector >= 0);
                Assert.Equal(collector >= 0 ? count - 1 : count, arity.Minimum);
                for (var supplied = 0; supplied <= count + 5; supplied++)
                {
                    if (!arity.Accepts(supplied))
                        continue;

                    var next = 0;
                    for (var index = 0; index < count; index++)
                    {
                        var (start, length) = Evaluator.NeedSourceRange(count, collector, supplied, index);
                        Assert.Equal(next, start);
                        Assert.Equal(index == collector ? supplied - count + 1 : 1, length);
                        Assert.True(length >= 0);
                        next = start + length;
                    }

                    Assert.Equal(supplied, next);
                }
            }
        }
    }

    public static TheoryData<string, string, string> TopLevelRejections => new()
    {
        // An ordinary call: its own report (the callee's signature). The explicit spread ran during
        // supply formation; the suspended ordinary argument trace(1) never ran.
        {
            "F(a, b) = a + b\nF(trace(1), [trace(2), trace(3)]*)",
            "ArityMismatch: Callable `F(a, b)` expects 2 arguments, but was called with 3 arguments. @ [2:1, 2:35)",
            "trace(2),trace(3)"
        },
        {
            "F(a, b) = a + b\nF(trace(1))",
            "ArityMismatch: Callable `F(a, b)` expects 2 arguments, but was called with 1 argument. @ [2:1, 2:12)",
            ""
        },
        // A flat collecting callee keeps the variadic report.
        {
            "F(a, b, *r) = a\nF([trace(1)]*)",
            "ArityMismatch: while evaluating call to F: Callable `F(a, b, *r)` expects at least 2 items, but received 1 item. @ [2:1, 2:15)",
            "trace(1)"
        },
        {
            "F((a, b), *r) = a\nF()",
            "ArityMismatch: Callable `F((a, b), *r)` expects at least 1 argument, but was called with 0 arguments. @ [2:1, 2:4)",
            ""
        },
        {
            "F(a, b) = a\n5.F",
            "ArityMismatch: Callable `F(a, b)` expects 2 arguments, but was called with 1 argument. @ [2:1, 2:4)",
            ""
        },
        {
            "F(a, b) = a\nA = F\nA(1)",
            "ArityMismatch: Callable `A(a, b)` expects 2 arguments, but was called with 1 argument. @ [3:1, 3:5)",
            ""
        },
        // A callback keeps the plain shape, named by its role, even for a collecting callee.
        {
            "Add(a, b) = a + b\nmap([1, 2], Add)",
            "ArityMismatch: while evaluating call to map: while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact): Callable `map transform(a, b)` expects 2 arguments, but was called with 1 argument. @ [2:1, 2:17)",
            ""
        },
        {
            "C(a, b, *r) = a\nmap([1, 2], C)",
            "ArityMismatch: while evaluating call to map: while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact): Callable `map transform(a, b, *r)` expects at least 2 arguments, but was called with 1 argument. @ [2:1, 2:15)",
            ""
        },
        // A user loop step: the loop-state report, after the spread of the initial state.
        {
            "Step(a, b) = a, b\nrepeat(Step, 1, trace(1), [trace(2), trace(3)]*)",
            "ArityMismatch: while evaluating call to repeat: `repeat` step expects 2 state values for 2 parameters 'a' and 'b', but the current loop state has 3 state values. Loop state values are bound positionally to the step's parameters. If this is a nested step with inferred parameters, remember that names already bound by an enclosing algorithm are captured, not added as step parameters; use a distinct state-slot name such as `candidate` when threading an outer value through the loop state. @ [2:1, 2:49)",
            "trace(2),trace(3)"
        },
        {
            "Step(a, b, *r) = a, b\nrepeat(Step, 1, trace(1))",
            "ArityMismatch: while evaluating call to repeat: `repeat` variadic step expects at least 2 state values for fixed parameter(s) 'a' and 'b', but the current loop state has 1 state value. A collecting loop parameter collects the remaining state values as an exact list with `*name`; ordinary parameters still bind one state value each. @ [2:1, 2:26)",
            ""
        },
        // A clause family: the family-level decision before any clause.
        {
            "G(0) = 1\nG(n) = n\nG(trace(5), [trace(6)]*)",
            "ArityMismatch: Property 'G' expects 1 parameter, but was called with 2 arguments. @ [3:1, 3:25)",
            "trace(6)"
        },
        {
            "Fam(0, acc) = 0, acc\nFam(n, acc) = n - 1, acc + n\nrepeat(Fam, 1, 1)",
            "ArityMismatch: while evaluating call to repeat: Property 'Fam' expects 2 parameters, but was called with 1 argument. @ [3:1, 3:18)",
            ""
        },
        // The zero-argument value demand.
        {
            "Head(x, *rest) = x\nHead",
            "ArityMismatch: Property 'Head' expects 1 parameter, but was called with 0 arguments. @ [2:1, 2:5)",
            ""
        },
        // A structural level's own gate, after its parent value was demanded.
        {
            "P((a, b)) = a + b\nP((trace(1), trace(2), trace(3)))",
            "ArityMismatch: Sequence pattern `(a, b)` expects 2 elements, but received 3 elements. @ [2:1, 2:34)",
            "trace(1),trace(2),trace(3)"
        },
        {
            "P([a, b]) = a\nP([1])",
            "ArityMismatch: List pattern `[a, b]` expects 2 elements, but received 1 element. @ [2:1, 2:7)",
            ""
        },
        // The deconstruction's unpacking level, named by its assignment pattern.
        {
            "x, y = 1, 2, 3\nx",
            "ArityMismatch: Assignment pattern `x, y` expects 2 values from the right-hand side, but it supplied 3 values. @ [2:1, 2:2)",
            ""
        },
        // A repeated name's value conflict and an explicit spread's own failure keep their reports.
        {
            "R(x, x) = x\nR(1, 2)",
            "ArityMismatch: while evaluating call to R: repeated parameter 'x' requires equal arguments: Bad arity @ [2:1, 2:8)",
            ""
        },
        {
            "F(a) = a\nF(1, [1 / 0]*)",
            "DivisionByZero: while evaluating call to F: Division by zero @ [2:7, 2:12)",
            ""
        },
    };

    [Theory]
    [MemberData(nameof(TopLevelRejections))]
    public async Task EachRejection_KeepsItsOwnReport_AfterSpreadsAndBeforeAnyDemand(string source, string error, string hostCalls)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", observation.Kind);
        Assert.Equal([error], observation.Errors);
        Assert.Equal(hostCalls, string.Join(",", observation.HostCalls));
    }

    [Theory]
    [InlineData("Only(*xs) = count(xs)\nOnly", "0", "")]
    [InlineData("P((a, *r)) = count(r)\nP((1, 2, 3))", "2", "")]
    [InlineData("x, *y = trace(1), trace(2), trace(3)\ny", "L[2, 3]", "trace(1),trace(2),trace(3)")]
    [InlineData("F(a, *xs, z) = a * 100 + count(xs) * 10 + z\nF(1, 2)", "102", "")]
    [InlineData("F(*xs, z) = count(xs) * 10 + z\nF((1, 2)*, [3, 4]*)", "34", "")]
    public async Task AcceptedCounts_BindAsBefore(string source, string value, string hostCalls)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", observation.Kind);
        Assert.Equal(value, observation.Value);
        Assert.Equal(hostCalls, string.Join(",", observation.HostCalls));
    }

    /// <summary>
    /// The CLR variant and payload of each top-level report. A flat collecting callee's ordinary call
    /// is <see cref="EvalError.VariadicArityMismatch"/>. Every other report is
    /// <see cref="EvalError.ArityMismatch"/> with the level's minimum against the complete supply
    /// count. A call or callback carries the callee's signature.
    /// </summary>
    [Fact]
    public void EachReport_KeepsItsVariantAndPayload()
    {
        var variadic = Assert.IsType<EvalError.VariadicArityMismatch>(Innermost(RunError("F(a, b, *r) = a\nF(1)")));
        Assert.Equal((2, 1), (variadic.ExpectedMinimum, variadic.Actual));
        Assert.NotNull(variadic.Signature);

        var call = Assert.IsType<EvalError.ArityMismatch>(Innermost(RunError("F(a, b) = a\nF(1, 2, 3)")));
        Assert.Equal((2, 3), (call.Expected, call.Actual));
        Assert.NotNull(call.Signature);

        var callback = Assert.IsType<EvalError.ArityMismatch>(Innermost(RunError("C(a, b, *r) = a\nmap([1, 2], C)")));
        Assert.Equal((2, 1), (callback.Expected, callback.Actual));
        Assert.NotNull(callback.Signature);

        var family = RunError("G(0) = 1\nG(n) = n\nG(1, 2)");
        Assert.Equal((1, 2), Payload(Innermost(family)));

        var structural = RunError("P((a, b)) = a\nP((1, 2, 3))");
        Assert.Equal((2, 3), Payload(Innermost(structural)));
        Assert.Contains(Contexts(structural), context => context is SequenceValueParameterBindingContext);

        var unpacking = RunError("x, y = 1, 2, 3\nx");
        Assert.Equal((2, 3), Payload(Innermost(unpacking)));
        Assert.Contains(Contexts(unpacking), context => context is DeconstructionBindingContext);

        var loop = RunError("Step(a, b) = a, b\nrepeat(Step, 1, 1, 2, 3)");
        Assert.Equal((2, 3), Payload(Innermost(loop)));
        Assert.Contains(Contexts(loop), context => context is LoopStateBindingContext);

        var zeroArgument = RunError("Head(x, *rest) = x\nHead");
        Assert.Equal((1, 0), Payload(Innermost(zeroArgument)));
    }

    /// <summary>
    /// A deconstruction's own cardinality is decided before any demand (NEED-05). A parser helper
    /// always takes its one right-hand side. A host can still rewrite the helper, because a record
    /// <c>with</c> copy keeps its internal deconstruction target. The rewritten helper requires two
    /// values while its call supplies one, so it is refused before its right-hand side runs. The
    /// pre-demand that keeps a right-hand side's own failure unwrapped comes after the gate. Until
    /// the October 2026 cleanup that pre-demand ran first, and the right-hand side's effect preceded
    /// the arity report.
    /// </summary>
    [Fact]
    public async Task HostModifiedDeconstructionHelper_IsRefusedBeforeItsRightHandSideRuns()
    {
        const string source = "x, y = trace(1), 2\nx";
        var log = new List<string>();
        var synchronous = HostOperations.Create(HostOperation.Create("trace", (args, _) => { lock (log) log.Add("trace"); return args[0]; }, "x"));
        var program = new Expr.AlgorithmExpr(WithTwoParameterHelper(ParseValid(source, synchronous), "x"));
        AssertRefusedBeforeDemand(Evaluator.Run(program, synchronous, limits: null, randomSeed: null, CancellationToken.None), log);

        log.Clear();
        var suspending = HostOperations.Create(HostOperation.CreateAsync("trace", async (args, _) =>
        {
            await Task.Yield();
            lock (log) log.Add("trace");
            return args[0];
        }, "x"));
        program = new Expr.AlgorithmExpr(WithTwoParameterHelper(ParseValid(source, suspending), "x"));
        AssertRefusedBeforeDemand(await Evaluator.RunAsync(program, suspending, limits: null, randomSeed: null, CancellationToken.None), log);

        // The unmodified program reads its right-hand side as written.
        Assert.Equal("1", SixRouteAgreement.Neutral(Evaluator.Run(
            new Expr.AlgorithmExpr(ParseValid(source, synchronous)), synchronous, limits: null, randomSeed: null, CancellationToken.None).Value));

        static void AssertRefusedBeforeDemand(EvalResult<Result> result, List<string> log)
        {
            Assert.True(result.IsError);
            Assert.Empty(log);
            Assert.Equal((2, 1), Payload(Innermost(result.Error)));
            Assert.Contains(Contexts(result.Error), context => context is DeconstructionBindingContext);
        }
    }

    /// <summary>
    /// The pre-evaluation gate refuses a level with two collecting captures (X-02). Such a level
    /// reaches the binder only if a host mutates a caller-owned pattern list after the gate, which
    /// the AST contract forbids. Even then the binder reads the one supplied-slot rule, which keeps the
    /// one-collector minimum, so it never allocates outside the supply. It refuses <c>F()</c> as a
    /// language error and binds <c>F(1)</c>. Until the October 2026 cleanup the binder's own
    /// minimum dropped every collector: <c>F()</c> was accepted and indexed the supply at -1, and a
    /// raw <see cref="ArgumentOutOfRangeException"/> escaped <c>Evaluator.Run</c>. This pins
    /// robustness, not a language rule.
    /// </summary>
    [Theory]
    [InlineData("mutate(0)\nF()", null)]
    [InlineData("mutate(0)\nF(1)", "S[0, 7]")]
    [InlineData("mutate(0)\nF(1, 2, 3)", "S[0, 7]")]
    public void ARefusedMultiCollectorLevel_NeverAllocatesOutsideTheSupply(string rows, string? value)
    {
        var parameters = new List<ParameterPattern> { new CaptureParameterPattern(new ParameterDeclaration("x")) };
        var operations = HostOperations.Create(HostOperation.Create("mutate", (_, _) =>
        {
            parameters.Clear();
            parameters.Add(new CaptureParameterPattern(new ParameterDeclaration("a", Kind: ParameterKind.Collecting)));
            parameters.Add(new CaptureParameterPattern(new ParameterDeclaration("b", Kind: ParameterKind.Collecting)));
            return new Result.Atom(0);
        }, "x"));
        var root = ParseValid("F(x) = 7\n" + rows, operations);
        var properties = root.Properties.ToArray();
        var index = Array.FindIndex(properties, property => property.Name == "F");
        properties[index] = properties[index] with { Value = Assert.IsType<Algorithm.User>(properties[index].Value) with { ParameterPatterns = parameters } };

        var result = Evaluator.Run(new Expr.AlgorithmExpr(root with { Properties = properties }), operations, limits: null, randomSeed: null, CancellationToken.None);

        if (value is null)
        {
            var mismatch = Assert.IsType<EvalError.VariadicArityMismatch>(Innermost(result.Error));
            Assert.Equal((1, 0), (mismatch.ExpectedMinimum, mismatch.Actual));
        }
        else
        {
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
            Assert.Equal(value, SixRouteAgreement.Neutral(result.Value));
        }
    }

    private static Algorithm.User WithTwoParameterHelper(Algorithm.User root, string target)
    {
        var properties = root.Properties.ToArray();
        var index = Array.FindIndex(properties, property => property.Name == target);
        var body = Assert.IsType<Algorithm.User>(properties[index].Value);
        var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
        var helper = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(call.Function).Algorithm);
        Assert.NotNull(helper.AssignmentDeconstructionTarget);

        var rewritten = helper with
        {
            ParameterPatterns = [new CaptureParameterPattern(new ParameterDeclaration("a")), new CaptureParameterPattern(new ParameterDeclaration("b"))],
        };
        Assert.NotNull(rewritten.AssignmentDeconstructionTarget);
        properties[index] = properties[index] with { Value = body with { Output = [call with { Function = new Expr.AlgorithmExpr(rewritten) }] } };
        return root with { Properties = properties };
    }

    /// <summary>A source the front end accepts, parsed with the host operations its names resolve to.</summary>
    private static Algorithm.User ParseValid(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return parsed.Root;
    }

    private static Algorithm.User Definition(string head)
    {
        var root = SourceProvenance.ParseValid($"{head} = 0\n0").Root;
        return Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == "F").Value);
    }

    private static EvalError RunError(string source)
    {
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.True(result.IsError, source);
        return result.Error;
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext wrapped)
            error = wrapped.Inner;
        return error;
    }

    private static IReadOnlyList<ErrorContext> Contexts(EvalError error)
    {
        var contexts = new List<ErrorContext>();
        while (error is EvalError.WithContext wrapped)
        {
            contexts.Add(wrapped.ErrorContext);
            error = wrapped.Inner;
        }

        return contexts;
    }

    private static (int Expected, int Actual) Payload(EvalError error)
    {
        var mismatch = Assert.IsType<EvalError.ArityMismatch>(error);
        return (mismatch.Expected, mismatch.Actual);
    }
}
