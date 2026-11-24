using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// THE TERMINAL A CONTEXT FRAME RECORDS WHEN IT IS BUILT (November 2026; C# implementation only, no
/// semantic, API or equality change). Every <see cref="EvalError.WithContext"/> records the error below
/// all of its frames from its inner error's own record, so <see cref="EvalError.UnwrapContext"/> — the
/// one door of <see cref="EvalError.IsResourceLimit"/>, <see cref="EvalError.IsHostTermination"/>,
/// <see cref="EvalError.IsTerminalForRun"/>, <see cref="EvalError.Code"/> and the evaluator's Q-36
/// readers — answers in constant work. Those classifications are asked once per level a failure leaves,
/// and walking the chain for each answer made unwinding a deep failure quadratic in its depth.
///
/// <para>Here: the record is the terminal the walk finds, for every frame of every host-built chain
/// (both constructors, null inner errors and contexts included); every copy keeps or recomputes it
/// (<c>with</c> copies of the span or a runtime slot, <see cref="EvalError.WithContext.WithInner"/>,
/// the Q-36 rebuilds), never changing the source; and classifying a 200,000-frame chain reads none of
/// its frames (<see cref="ContextChainReadTestSeam"/>), while the one nesting rebuild reads each frame once.
/// The record's place in record equality and hashing is pinned by
/// <see cref="EvalErrorRecordEqualityTests"/>.</para>
/// </summary>
public class ContextFrameTerminalRecordTests
{
    private static readonly SourceSpan SpanA = new(1, 2, 1, 3);
    private static readonly SourceSpan SpanB = new(2, 1, 2, 2);

    /// <summary>The walk the record replaces: the error below every frame (null below a host-built null inner error).</summary>
    private static EvalError? WalkedTerminal(EvalError? error)
    {
        while (error is EvalError.WithContext frame)
            error = frame.Inner;
        return error;
    }

    /// <summary>Every frame of <paramref name="error"/>'s chain records the terminal the walk finds below it.</summary>
    private static int AssertEveryFrameRecordsItsTerminal(EvalError error, string what)
    {
        var frames = 0;
        var expected = WalkedTerminal(error);
        if (!ReferenceEquals(expected, error.UnwrapContext()))
            Assert.Fail($"{what}: UnwrapContext is not the walked terminal");
        for (EvalError? current = error; current is EvalError.WithContext frame; current = frame.Inner)
        {
            // Every frame of one chain shares the one terminal.
            if (!ReferenceEquals(expected, frame.RecordedTerminal) || !ReferenceEquals(expected, frame.UnwrapContext()))
                Assert.Fail($"{what}: frame {frames} records another terminal");
            frames++;
        }

        return frames;
    }

    private static EvalError.WithContext Chain(EvalError terminal, int frames)
    {
        var frame = new EvalError.WithContext(new CallContext("F0"), terminal) { Span = SpanA };
        for (var i = 1; i < frames; i++)
            frame = new EvalError.WithContext(i % 2 == 0 ? new CallContext("F" + i) : new TextErrorContext("frame " + i), frame);
        return frame;
    }

    [Fact]
    public void EveryFrameRecordsTheTerminalTheWalkFinds_OnEveryHostConstruction()
    {
        var unknown = new EvalError.UnknownName("x");
        var own = new EvalError.MissingOutput { Span = SpanA };
        var nested = new EvalError.MissingOutput { IsNested = true };
        var limit = new EvalError.EvaluationDepthExceeded(128);
        var nullInner = new EvalError.WithContext("empty", null!);
        EvalError[] corpus =
        [
            unknown,
            own,
            new EvalError.WithContext(new CallContext("F"), unknown),
            new EvalError.WithContext("text overload", own),
            new EvalError.WithContext((ErrorContext)null!, unknown),
            new EvalError.WithContext(new CallContext("outer"), new EvalError.WithContext("inner", nested)) { Span = SpanB },
            new EvalError.WithContext("projection", unknown with { IsProjectionFailure = true }) { IsProjectionFailure = true },
            new EvalError.WithContext("limit", limit),
            new EvalError.WithContext("marker", EvalError.HostTermination.Marker),
            new EvalError.WithContext("pending", EvalError.ObservationPending.Instance),
            nullInner,
            new EvalError.WithContext(new CallContext("over null"), nullInner),
            new EvalError.WithContext((ErrorContext)null!, null!),
            Chain(unknown, 1_000),
            Chain(own, 1_000),
            Chain(new EvalError.WithContext("shared", limit), 500),
        ];

        var frames = 0;
        foreach (var (error, index) in corpus.Select((error, index) => (error, index)))
            frames += AssertEveryFrameRecordsItsTerminal(error, $"corpus[{index}]");
        Assert.True(frames > 2_500, $"{frames} frames checked");

        // Two chains over one shared inner chain record the same terminal object.
        var shared = Chain(unknown, 10);
        Assert.Same(unknown, new EvalError.WithContext("a", shared).RecordedTerminal);
        Assert.Same(unknown, new EvalError.WithContext("b", shared).RecordedTerminal);

        // A null inner error stays the answer it always was: no terminal, and the classifications that
        // read the inner error's classification fail as they did.
        Assert.Null(nullInner.RecordedTerminal);
        Assert.Null(new EvalError.WithContext("over null", nullInner).UnwrapContext());
        Assert.Throws<NullReferenceException>(() => nullInner.IsResourceLimit);
        Assert.Throws<NullReferenceException>(() => new EvalError.WithContext("over null", nullInner).IsResourceLimit);
    }

    [Fact]
    public void CopiesKeepTheRecord_AndAReplacedInnerErrorRecordsItsOwn()
    {
        var unknown = new EvalError.UnknownName("x");
        var chain = Chain(unknown, 8);

        // `with` copies of the frame's own span or runtime slots keep the inner error and its record.
        foreach (var copy in new[]
        {
            chain with { },
            chain with { Span = SpanB },
            chain with { Span = null },
            chain with { IsProjectionFailure = true },
            chain with { OutputSpreadNotes = [new OutputSpreadNote("F(x)", "F", 1, 2)] },
        })
        {
            Assert.Same(chain.Inner, copy.Inner);
            Assert.Same(unknown, copy.RecordedTerminal);
            AssertEveryFrameRecordsItsTerminal(copy, "with copy");
        }

        // A replaced inner error: the copy records the new terminal (bare or below more frames), the source is untouched.
        var divide = new EvalError.DivByZero { Span = SpanA };
        var bare = chain.WithInner(divide);
        Assert.Same(divide, bare.RecordedTerminal);
        Assert.Equal(1, AssertEveryFrameRecordsItsTerminal(bare, "WithInner over a bare error"));
        var framed = chain.WithInner(Chain(divide, 3));
        Assert.Same(divide, framed.RecordedTerminal);
        Assert.Equal(4, AssertEveryFrameRecordsItsTerminal(framed, "WithInner over frames"));
        Assert.Equal(8, AssertEveryFrameRecordsItsTerminal(chain, "the source after WithInner"));
        Assert.Same(unknown, chain.RecordedTerminal);

        // The Q-36 rebuilds copy every frame around the new terminal; every copy records it, the original keeps its own.
        var own = new EvalError.MissingOutput { Span = SpanA };
        var ownChain = Chain(own, 6);
        var nestedChain = Evaluator.NestMissingOutput(ownChain);
        var nestedTerminal = Assert.IsType<EvalError.MissingOutput>(nestedChain.UnwrapContext());
        Assert.True(nestedTerminal.IsNested && nestedTerminal.KeepsOwnBlame);
        Assert.Equal(6, AssertEveryFrameRecordsItsTerminal(nestedChain, "nested rebuild"));
        Assert.Equal(6, AssertEveryFrameRecordsItsTerminal(ownChain, "the source of the nested rebuild"));
        Assert.Same(own, ownChain.RecordedTerminal);
        Assert.Same(nestedChain, Evaluator.NestMissingOutput(nestedChain));

        var operand = new Expr.Param("x") { Span = SpanB };
        var spread = Evaluator.SpreadOperandFailure(operand, operand.Span, ownChain);
        Assert.Equal(SpanB, Assert.IsType<EvalError.SpreadMissingOutput>(spread.UnwrapContext()).Span);
        Assert.Equal(6, AssertEveryFrameRecordsItsTerminal(spread, "spread rebuild"));
        Assert.Same(own, ownChain.RecordedTerminal);
    }

    [Fact]
    public void ClassifyingADeepChain_ReadsNoFrame_AndNestingItReadsEachFrameOnce()
    {
        const int depth = 200_000;
        var marker = EvalError.HostTermination.Marker;
        var ordinary = Chain(new EvalError.DivByZero(), depth);
        var limit = Chain(new EvalError.EvaluationStepLimitExceeded(10), depth);
        var terminal = Chain(marker, depth);
        var pending = Chain(EvalError.ObservationPending.Instance, depth);
        var nested = Chain(new EvalError.MissingOutput { IsNested = true }, depth);
        var own = Chain(new EvalError.MissingOutput(), depth);

        using (var reads = ContextChainReadTestSeam.Activate())
        {
            Assert.False(ordinary.IsResourceLimit || ordinary.IsHostTermination || ordinary.IsTerminalForRun);
            Assert.Equal(KatLangErrorCode.DivisionByZero, ordinary.Code);
            Assert.True(limit.IsResourceLimit && limit.IsTerminalForRun && !limit.IsHostTermination);
            Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, limit.Code);
            Assert.True(terminal.IsHostTermination && terminal.IsTerminalForRun && !terminal.IsResourceLimit);
            Assert.True(NeedCell.IsObservationPending(pending));
            Assert.False(NeedCell.IsObservationPending(ordinary));
            Assert.True(Evaluator.IsOwnMissingOutputError(own));
            Assert.False(Evaluator.IsOwnMissingOutputError(nested));
            Assert.False(Evaluator.IsOwnMissingOutputError(ordinary));
            Assert.Same(nested, Evaluator.NestMissingOutput(nested));
            Assert.Same(ordinary, Evaluator.NestMissingOutput(ordinary));
            Assert.Same(terminal, Evaluator.NestMissingOutput(terminal));
            Assert.True(reads.Reads == 0, $"classifying {depth}-frame chains read {reads.Reads} frames");
        }

        // The one rebuild that changes a terminal copies every frame: one read each, once.
        using (var reads = ContextChainReadTestSeam.Activate())
        {
            var rebuilt = Evaluator.NestMissingOutput(own);
            Assert.True(reads.Reads == depth, $"nesting read {reads.Reads} frames of {depth}");
            Assert.True(Assert.IsType<EvalError.MissingOutput>(rebuilt.UnwrapContext()).IsNested);
            Assert.False(Evaluator.IsOwnMissingOutputError(rebuilt));
            Assert.Same(rebuilt, Evaluator.NestMissingOutput(rebuilt));
            Assert.True(reads.Reads == depth, "asking again read more frames");
        }

        // The observation counts every walk of its own flow, and nothing once closed.
        var observation = ContextChainReadTestSeam.Activate();
        Assert.IsType<EvalError.DivByZero>(WalkedTerminal(ordinary));
        Assert.Equal(depth, observation.Reads);
        observation.Dispose();
        _ = WalkedTerminal(ordinary);
        Assert.Equal(depth, observation.Reads);
    }

    [Fact]
    public async Task AnObservation_CountsItsOwnFlowAcrossAwaits_AndNoOtherFlow()
    {
        var chain = Chain(new EvalError.UnknownName("x"), 100);
        using var reads = ContextChainReadTestSeam.Activate();

        // Another flow's walk is not counted: a thread started without this flow's execution context
        // (a task waited on could run inline, in this flow).
        var other = new Thread(() => WalkedTerminal(chain));
        other.UnsafeStart();
        other.Join();
        Assert.Equal(0, reads.Reads);

        // This flow's walk after a genuine suspension, on whatever thread resumes it, is counted.
        await Task.Yield();
        _ = WalkedTerminal(chain);
        await Task.Run(() => WalkedTerminal(chain));
        Assert.Equal(200, reads.Reads);

        // A nested observation counts its own reads; the enclosing one resumes afterwards.
        var inner = ContextChainReadTestSeam.Activate();
        ExecutionContext captured;
        using (inner)
        {
            captured = ExecutionContext.Capture()!;
            _ = WalkedTerminal(chain);
            Assert.Equal(100, inner.Reads);
        }

        // The outer recorder still enables the getter hook when a captured inner flow resumes.
        ExecutionContext.Run(captured, _ => WalkedTerminal(chain), null);
        Assert.Equal(100, inner.Reads);
        _ = WalkedTerminal(chain);
        Assert.Equal(300, reads.Reads);
    }
}
