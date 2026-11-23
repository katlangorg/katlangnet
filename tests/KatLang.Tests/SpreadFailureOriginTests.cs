using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// X-29 / Q-36 (owner decision 2026-10-24): spread preserves failures originating within its
/// operand's dependencies or arguments, including their category, cause and blame; only the
/// operand's OWN missing output becomes <see cref="EvalError.SpreadMissingOutput"/>, and the spread
/// site adds context (<see cref="SpreadOperandContext"/>) without claiming that an output-bearing
/// operand lacks output. The origin is part of the completed failure
/// (<see cref="EvalError.MissingOutput.IsNested"/>, Lean <c>MissingOutputOrigin</c>), so it survives
/// memoization and is decided without evaluating anything. Lean twins:
/// <c>lean/CoreTests/SpreadFailureOrigin.lean</c>; every source case here is also run on all six
/// routes (<see cref="SixRouteAgreement"/>), and the differential corpora pin the Lean agreement.
/// </summary>
public class SpreadFailureOriginTests
{
    private const string Prelude = "G = {\n    public X = 1\n}\nH = G + 1\nF(x) = x\nP(x) = x*\n";

    // The row is line 7; `G` inside `H` is (4, 5).
    private const int RowLine = 7;

    private static KatLangError Fails(string row, KatLangErrorCode code)
    {
        var source = Prelude + row;
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);
        Assert.True(code == error.Code, $"expected {code}, got {error.Code}: {error.Message}\nsource:\n{source}");
        return error;
    }

    private static EvalError EvalFailure(string row)
    {
        var parsed = SourceProvenance.ParseValid(Prelude + row);
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsError, $"expected a failure for:\n{row}");
        return result.Error;
    }

    private static IEnumerable<EvalError> Chain(EvalError error)
    {
        for (var current = error; ; current = ((EvalError.WithContext)current).Inner)
        {
            yield return current;
            if (current is not EvalError.WithContext) yield break;
        }
    }

    private static EvalError Innermost(EvalError error) => Chain(error).Last();

    private static IReadOnlyList<ErrorContext> Contexts(EvalError error)
        => [.. Chain(error).OfType<EvalError.WithContext>().Select(static frame => frame.ErrorContext)];

    // ── 1. The accepted category boundary ──────────────────────────────────────────────

    [Theory]
    [InlineData("{}*", 1)]
    [InlineData("G*", 1)]
    [InlineData("G()*", 1)]
    // A parameter denotes its supplied computation: a directly output-less argument is the spread's own.
    [InlineData("P({})", null)]
    [InlineData("P(G)", null)]
    // An inner spread's own report is kept, at the inner site.
    [InlineData("({}*)*", 2)]
    public void OwnMissingOutput_IsSpreadMissingOutput(string row, int? column)
    {
        var error = Fails(row, KatLangErrorCode.SpreadMissingOutput);
        Assert.Contains("Cannot spread because the spread operand has no defined output", error.Message, StringComparison.Ordinal);
        if (column is { } atColumn)
        {
            Assert.Equal(RowLine, error.Span!.Value.Start.Line);
            Assert.Equal(atColumn, error.Span!.Value.Start.Column);
        }

        Assert.IsType<EvalError.SpreadMissingOutput>(Innermost(EvalFailure(row)));
    }

    [Theory]
    [InlineData("G*")]
    [InlineData("G()*")]
    [InlineData("P(G)")]
    public void OwnMissingOutput_PreservesTheNamedDemandContext(string row)
    {
        var structured = EvalFailure(row);
        Assert.IsType<EvalError.SpreadMissingOutput>(Innermost(structured));
        Assert.Contains(Contexts(structured), context => context is PropertyEvaluationContext("G") or CallContext("G"));
        Assert.Contains("G", Fails(row, KatLangErrorCode.SpreadMissingOutput).Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("C(*xs) = xs*\nC(G)")]
    [InlineData("C(*xs) = P(xs)\nC(G)")]
    public async Task CollectorMaterialization_PreservesAnElementsFailure(string row)
    {
        var error = Fails(row, KatLangErrorCode.MissingOutput);
        Assert.Contains("Property 'G' has no defined output", error.Message, StringComparison.Ordinal);
        Assert.Equal(new SourcePosition(8, 3), error.Span!.Value.Start);
        var observation = await SixRouteAgreement.OnEveryRouteAsync(Prelude + row);
        Assert.Equal("err", observation.Kind);
    }

    [Theory]
    // The nested cause `G` keeps its blame and its own location inside `H`.
    [InlineData("H*", 4, 5, "H")]
    [InlineData("H()*", 4, 5, "H(...)")]
    [InlineData("P(H)", 4, 5, "x")]
    // A written output row of the operand body fails: the operand HAS output.
    [InlineData("{ G }*", RowLine, 3, "{...}")]
    // Constructing the operand fails.
    [InlineData("(G, 1)*", RowLine, 2, "(G, 1)")]
    // A builtin's argument, a clause pattern's and a binder's inspection, an intrinsic receiver.
    [InlineData("if(true, G, 1)*", RowLine, 10, "if(...)")]
    [InlineData("count(G)*", RowLine, 7, "count(...)")]
    [InlineData("G.string*", RowLine, 1, "G.string")]
    [InlineData("G[0]*", RowLine, 1, "G[0]")]
    public void NestedMissingOutput_KeepsItsCategoryCauseAndBlame(string row, int line, int column, string operand)
    {
        var error = Fails(row, KatLangErrorCode.MissingOutput);
        Assert.Contains("Property 'G' has no defined output", error.Message, StringComparison.Ordinal);
        Assert.Contains($"while evaluating spread operand {operand}", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("Cannot spread", error.Message, StringComparison.Ordinal);
        Assert.Equal(line, error.Span!.Value.Start.Line);
        Assert.Equal(column, error.Span!.Value.Start.Column);

        var structured = EvalFailure(row);
        var missing = Assert.IsType<EvalError.MissingOutput>(Innermost(structured));
        Assert.True(missing.IsNested);
        var contexts = Contexts(structured);
        // Exactly one spread frame, outside the cause's own property frame.
        var spread = Assert.Single(contexts.OfType<SpreadOperandContext>());
        Assert.Equal(operand, spread.OperandDescription);
        // The cause keeps its own blame frame: the property `G` (for a `.string` receiver, the
        // dot-call frame that renders it as that property).
        Assert.True(
            contexts[^1] is PropertyEvaluationContext("G") or DotCallContext("G", "string"),
            $"unexpected innermost frame {contexts[^1]}");
        Assert.True(contexts.ToList().IndexOf(spread) < contexts.Count - 1);
    }

    // Lazy collections (issue #204): a list literal defers its elements, so `[G]` is built and
    // the operand evaluates. The failure is the POSITION's, raised when the spread reads the
    // level it opens: nested, at `G`, under the position's own frames — with no spread frame.
    [Theory]
    [InlineData("[G]*", RowLine, 2)]
    [InlineData("P([G])", RowLine, 4)]
    public void ADeferredListElement_FailsAsItsOwnPosition_WithoutASpreadFrame(string row, int line, int column)
    {
        var error = Fails(row, KatLangErrorCode.MissingOutput);
        Assert.Contains("Property 'G' has no defined output", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("while evaluating spread operand", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("Cannot spread", error.Message, StringComparison.Ordinal);
        Assert.Equal(line, error.Span!.Value.Start.Line);
        Assert.Equal(column, error.Span!.Value.Start.Column);

        var structured = EvalFailure(row);
        var missing = Assert.IsType<EvalError.MissingOutput>(Innermost(structured));
        Assert.True(missing.IsNested);
        var contexts = Contexts(structured);
        Assert.Empty(contexts.OfType<SpreadOperandContext>());
        Assert.True(contexts[^1] is PropertyEvaluationContext("G"), $"unexpected innermost frame {contexts[^1]}");
    }

    [Fact]
    public void WrittenArgument_KeepsTheFixedArgumentBlame_UnderTheSpreadFrame()
    {
        var plain = Fails("F({})", KatLangErrorCode.MissingOutput);
        var spread = Fails("F({})*", KatLangErrorCode.MissingOutput);
        Assert.Equal("while evaluating spread operand F(...): " + plain.Message, spread.Message);
        Assert.Equal(plain.Span, spread.Span);
        Assert.Contains("Parameter 'x' has no defined output", spread.Message, StringComparison.Ordinal);

        var plainContexts = Contexts(EvalFailure("F({})"));
        var spreadContexts = Contexts(EvalFailure("F({})*"));
        Assert.IsType<SpreadOperandContext>(spreadContexts[0]);
        Assert.Equal(plainContexts, spreadContexts.Skip(1));
    }

    [Theory]
    [InlineData("()*")]
    [InlineData("[]*")]
    [InlineData("{ []* }*")]
    public void EmptyValuesAndSupplies_AreNotMissingOutput(string row)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(Prelude + row + ", 7"));

    [Theory]
    [InlineData("(1 / 0)*", KatLangErrorCode.DivisionByZero)]
    [InlineData("(1 + 'a')*", KatLangErrorCode.TypeMismatch)]
    [InlineData("[1][5]*", KatLangErrorCode.BadIndex)]
    public void OtherFailures_AreTheOperandsOwn_Unchanged(string row, KatLangErrorCode code)
    {
        var error = Fails(row, code);
        Assert.DoesNotContain("spread operand", error.Message, StringComparison.Ordinal);
        Assert.Empty(Contexts(EvalFailure(row)).OfType<SpreadOperandContext>());
    }

    [Fact]
    public void ResourceLimits_StayTerminal_AndAreNeverReclassified()
    {
        var error = Fails("R(n) = R(n + 1)\nR(0)*", KatLangErrorCode.EvaluationDepthExceeded);
        Assert.DoesNotContain("spread operand", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Cancellation_KeepsItsExceptionAndToken()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var thrown = Assert.ThrowsAny<OperationCanceledException>(
            () => KatLangEngine.Run(Prelude + "H*", new RunOptions { EvaluationCancellationToken = cts.Token }));
        Assert.Equal(cts.Token, thrown.CancellationToken);
    }

    // ── 2. Nested spreads ──────────────────────────────────────────────────────────────

    [Fact]
    public void NestedSpreads_KeepTheInnermostCause_AndAddOneFramePerSpread()
    {
        // `X`'s row is the spread `H*`; spreading `X` meets that already-reported nested failure.
        var error = Fails("X = H*\nX*", KatLangErrorCode.MissingOutput);
        Assert.Equal(4, error.Span!.Value.Start.Line);
        Assert.Equal(5, error.Span!.Value.Start.Column);
        Assert.StartsWith("while evaluating spread operand X: while evaluating spread operand H: Property 'G'", error.Message, StringComparison.Ordinal);

        // An own report of an inner spread is never relabeled by an outer one.
        var inner = Fails("Y = {}*\nY*", KatLangErrorCode.SpreadMissingOutput);
        Assert.Equal(RowLine, inner.Span!.Value.Start.Line);
        Assert.Equal(5, inner.Span!.Value.Start.Column);
    }

    // ── 3. Supply failure order: a failed spread supplies nothing ──────────────────────

    [Theory]
    [InlineData("count(1, H*)", KatLangErrorCode.MissingOutput)]
    [InlineData("map([], H*)", KatLangErrorCode.MissingOutput)]
    [InlineData("count(1, {}*)", KatLangErrorCode.SpreadMissingOutput)]
    [InlineData("map([], G*)", KatLangErrorCode.SpreadMissingOutput)]
    public void FailedSpreadSlot_PrecedesArityAndCallbackRoles(string row, KatLangErrorCode code)
    {
        var error = Fails(row, code);
        Assert.DoesNotContain("but was called with", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("callback", error.Message, StringComparison.OrdinalIgnoreCase);
    }

    // ── 4. Every route agrees ───────────────────────────────────────────────────────────

    [Theory]
    [InlineData("{}*")]
    [InlineData("G*")]
    [InlineData("G()*")]
    [InlineData("H*")]
    [InlineData("H()*")]
    [InlineData("F({})*")]
    [InlineData("{ G }*")]
    [InlineData("(G, 1)*")]
    [InlineData("[G]*")]
    [InlineData("({}*)*")]
    [InlineData("count(1, H*)")]
    [InlineData("map([], H*)")]
    [InlineData("count(1, {}*)")]
    [InlineData("P({})")]
    [InlineData("P(H)")]
    [InlineData("P([G])")]
    [InlineData("K(0) = 1\nK(n) = 2\nK(G)*")]
    [InlineData("Q((a, b)) = a\nQ(G)*")]
    [InlineData("V(x) = true\nG.filter(V).count*")]
    [InlineData("S(n) = n + 1\nrepeat(S(G), 2)*")]
    [InlineData("G.string*")]
    public async Task EveryRoute_ReportsTheSameCategoryCauseAndBlame(string row)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(Prelude + row);
        Assert.Equal("err", observation.Kind);
    }

    [Theory]
    [InlineData("V(x) = true\nG.filter(V).count*")]
    [InlineData("S(n) = n + 1\nrepeat(S(G), 2)*")]
    public void FusedAndPlannedBuiltins_NestLikeTheGenericDispatch(string row)
    {
        var error = Fails(row, KatLangErrorCode.MissingOutput);
        Assert.Contains("Property 'G' has no defined output", error.Message, StringComparison.Ordinal);
    }

    // ── 5. No extra evaluation ──────────────────────────────────────────────────────────

    [Theory]
    [InlineData("T = trace(1) + G\nT*", "trace(1)")]
    [InlineData("T = trace(1) + G\ncount(1, T*)", "trace(1)")]
    [InlineData("Q(x) = x*\nQ(trace(2) + G)", "trace(2)")]
    [InlineData("C(*xs) = xs*\nC(trace(1), G)", "trace(1)")]
    public async Task TheDecisionEvaluatesNothing(string row, string onlyHostCall)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(Prelude + row);
        Assert.Equal("err", observation.Kind);
        Assert.Equal([onlyHostCall], observation.HostCalls);
    }

    // ── 6. Stored failures: the origin is the computation's, never a consumer's ────────

    [Fact]
    public void StoredFailure_KeepsItsOrigin_AndNoConsumerRewritesIt()
    {
        var own = new EvalError.WithContext(new PropertyEvaluationContext("G"), new EvalError.MissingOutput());
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Compute() { starts++; return own; }
        var cell = new NeedCell(Compute, () => new(Compute()));

        // A consuming computation nests its own copy; the stored failure stays the computation's own.
        var nested = Evaluator.NestMissingOutput(cell.Demand().Error);
        Assert.NotSame(own, nested);
        Assert.True(Assert.IsType<EvalError.MissingOutput>(Innermost(nested)).IsNested);
        Assert.Same(own, cell.Demand().Error);
        Assert.False(Assert.IsType<EvalError.MissingOutput>(own.Inner).IsNested);

        // A spread over the cell after that consumer still reads the computation's own outcome.
        var operand = new Expr.Param("x");
        var converted = Evaluator.SpreadOperandFailure(operand, null, cell.Demand().Error);
        Assert.IsType<EvalError.SpreadMissingOutput>(Innermost(converted));
        Assert.Equal(Contexts(own), Contexts(converted));
        Assert.Equal(1, starts);

        // A nested stored failure is preserved by the spread, carried as the frame's inner error.
        var preserved = Evaluator.SpreadOperandFailure(operand, null, nested);
        var frame = Assert.IsType<EvalError.WithContext>(preserved);
        Assert.IsType<SpreadOperandContext>(frame.ErrorContext);
        Assert.Same(nested, frame.Inner);

        // Nesting is idempotent and leaves every other failure alone.
        Assert.Same(nested, Evaluator.NestMissingOutput(nested));
        var other = new EvalError.DivByZero();
        Assert.Same(other, Evaluator.NestMissingOutput(other));
        Assert.Same(other, Evaluator.SpreadOperandFailure(operand, null, other));
    }

    [Fact]
    public void TransportedContextWithoutASpan_KeepsItsCausesBlame()
    {
        var origin = new SourceSpan(3, 4, 3, 5);
        var operand = new Expr.Param("x") { Span = new SourceSpan(9, 2, 9, 3) };
        var cause = new EvalError.MissingOutput { IsNested = true, Span = origin };
        var stored = new EvalError.WithContext(new PropertyEvaluationContext("G"), cause);
        var spread = Evaluator.SpreadOperandFailure(operand, operand.Span, stored);
        Assert.Equal(origin, spread.Span);
        Assert.Same(stored, Assert.IsType<EvalError.WithContext>(spread).Inner);
        Assert.Null(stored.Span);
        Assert.Equal(origin, cause.Span);
    }

    [Fact]
    public void NestedCopy_KeepsSpanAndSlots_AndEqualityIsCategoryOnly()
    {
        var span = new SourceSpan(3, 4, 3, 5);
        var own = new EvalError.MissingOutput { Span = span, IsSelectedMemberOutput = true };
        var nested = Assert.IsType<EvalError.MissingOutput>(Evaluator.NestMissingOutput(own));
        Assert.Equal(span, nested.Span);
        Assert.True(nested.IsSelectedMemberOutput);
        Assert.True(nested.IsNested);
        Assert.False(own.IsNested);
        // The origin is diagnostic provenance in an equality-transparent slot, like the other slots.
        Assert.Equal<EvalError>(own, nested);
        Assert.Equal(KatLangErrorCode.MissingOutput, nested.Code);
    }

    // ── 7. The context-chain readers are loops with the recursive definitions' outcomes ──

    // The definitions the readers had until November 2026, one native frame per context frame (Lean:
    // `isOwnMissingOutputError`, `Error.nestMissingOutput`, the own arm of `spreadOperandFailure`). They are
    // the oracle here; the evaluator's readers are loops, because a run's chain grows with its nesting, which
    // the async route does not bound by the stack (EvaluationLimitsProcessTests covers the depth).
    private static bool OwnOracle(EvalError error) => error switch
    {
        EvalError.MissingOutput missing => !missing.IsNested,
        EvalError.WithContext(_, var inner) => OwnOracle(inner),
        _ => false,
    };

    private static bool MissingOracle(EvalError error) => error switch
    {
        EvalError.MissingOutput => true,
        EvalError.WithContext(_, var inner) => MissingOracle(inner),
        _ => false,
    };

    private static EvalError NestOracle(EvalError error) => error switch
    {
        EvalError.MissingOutput { IsNested: false } missing => missing with { IsNested = true },
        EvalError.WithContext { Inner: EvalError.MissingOutput { IsNested: false } framed } context
            => context.WithInner(framed with { IsNested = true, KeepsOwnBlame = true }),
        EvalError.WithContext context when OwnOracle(context.Inner)
            => context.WithInner(NestOracle(context.Inner)),
        _ => error,
    };

    private static EvalError ConvertOracle(EvalError error, SourceSpan? span)
        => error is EvalError.WithContext context
            ? context.WithInner(ConvertOracle(context.Inner, span))
            : new EvalError.SpreadMissingOutput { Span = span };

    private static bool LiftableOracle(EvalError error) => !error.IsProjectionFailure && error switch
    {
        EvalError.NotAnAlgorithm => true,
        EvalError.IllegalInEval => true,
        EvalError.WithContext(_, var inner) => LiftableOracle(inner),
        _ => false,
    };

    /// <summary>Everything a chain node carries: kind, span, context, and the equality-transparent slots.</summary>
    private sealed record NodeFacts(
        Type Kind, SourceSpan? Span, ErrorContext? Context, bool ProjectionFailure, bool Nested, bool KeepsOwnBlame, bool SelectedMember);

    private static NodeFacts[] Facts(EvalError error)
        => [.. Chain(error).Select(static node => new NodeFacts(
            node.GetType(), node.Span, (node as EvalError.WithContext)?.ErrorContext, node.IsProjectionFailure,
            node is EvalError.MissingOutput { IsNested: true }, node is EvalError.MissingOutput { KeepsOwnBlame: true },
            node is EvalError.MissingOutput { IsSelectedMemberOutput: true }))];

    private static void AssertSameOutcome(EvalError input, EvalError expected, EvalError actual, string what)
    {
        Assert.True(Facts(expected).SequenceEqual(Facts(actual)), $"{what}: the chains differ");
        // Unchanged means the SAME object; a changed chain shares no node with the input (a memoized
        // failure is shared by every consumer) and keeps every frame's own context object.
        Assert.Equal(ReferenceEquals(expected, input), ReferenceEquals(actual, input));
        if (ReferenceEquals(actual, input))
            return;
        var before = Chain(input).ToArray();
        var after = Chain(actual).ToArray();
        Assert.Equal(before.Length, after.Length);
        for (var i = 0; i < before.Length; i++)
        {
            Assert.NotSame(before[i], after[i]);
            if (before[i] is EvalError.WithContext frame)
                Assert.Same(frame.ErrorContext, Assert.IsType<EvalError.WithContext>(after[i]).ErrorContext);
        }
    }

    public static TheoryData<int, int> ChainShapes()
    {
        var shapes = new TheoryData<int, int>();
        for (var terminal = 0; terminal < 9; terminal++)
        {
            foreach (var frames in new[] { 0, 1, 2, 3, 7, 64 })
                shapes.Add(terminal, frames);
        }

        return shapes;
    }

    [Theory]
    [MemberData(nameof(ChainShapes))]
    public void ChainReaders_AgreeWithTheRecursiveDefinitions(int terminalKind, int frames)
    {
        var origin = new SourceSpan(3, 4, 3, 5);
        EvalError terminal = terminalKind switch
        {
            0 => new EvalError.MissingOutput { Span = origin, IsSelectedMemberOutput = true },
            1 => new EvalError.MissingOutput(),
            2 => new EvalError.MissingOutput { IsNested = true, Span = origin },
            3 => new EvalError.MissingOutput { IsNested = true, KeepsOwnBlame = true },
            4 => new EvalError.DivByZero { Span = origin },
            5 => new EvalError.NotAnAlgorithm("x"),
            6 => new EvalError.IllegalInEval("x") { Span = origin },
            7 => new EvalError.NotAnAlgorithm("x") { IsProjectionFailure = true },
            _ => new EvalError.SpreadMissingOutput { Span = origin },
        };

        // Every third frame has no span, every fifth carries the projection mark, and the contexts alternate.
        foreach (var marked in new[] { false, true })
        {
            var input = terminal;
            for (var i = frames - 1; i >= 0; i--)
            {
                ErrorContext context = i % 2 == 0 ? new CallContext("F" + i) : new PropertyEvaluationContext("P" + i);
                var frame = new EvalError.WithContext(context, input) { Span = i % 3 == 0 ? null : new SourceSpan(i + 1, 1, i + 1, 2) };
                input = marked && i % 5 == 4 ? frame with { IsProjectionFailure = true } : frame;
            }

            var what = $"terminal {terminalKind} under {frames} frame(s), marked={marked}";
            var untouched = Facts(input);

            Assert.Equal(OwnOracle(input), Evaluator.IsOwnMissingOutputError(input));
            Assert.Equal(LiftableOracle(input), Evaluator.IsLiftableError(input));
            AssertSameOutcome(input, NestOracle(input), Evaluator.NestMissingOutput(input), what + ", nest");

            var operand = new Expr.Param("x") { Span = new SourceSpan(9, 2, 9, 3) };
            foreach (var span in new SourceSpan?[] { operand.Span, null })
            {
                var spread = Evaluator.SpreadOperandFailure(operand, span, input);
                if (OwnOracle(input))
                {
                    AssertSameOutcome(input, ConvertOracle(input, span), spread, what + ", spread of an own missing output");
                }
                else if (MissingOracle(input))
                {
                    // A nested missing output keeps its chain: one spread frame is added around the same object.
                    var added = Assert.IsType<EvalError.WithContext>(spread);
                    Assert.IsType<SpreadOperandContext>(added.ErrorContext);
                    Assert.Same(input, added.Inner);
                    Assert.Equal(Chain(input).Select(static node => node.Span).FirstOrDefault(static s => s is not null) ?? span, added.Span);
                }
                else
                {
                    Assert.Same(input, spread);
                }
            }

            // No reader mutates the failure it reads.
            Assert.True(untouched.SequenceEqual(Facts(input)), $"{what}: a reader changed its input");
        }
    }
}
