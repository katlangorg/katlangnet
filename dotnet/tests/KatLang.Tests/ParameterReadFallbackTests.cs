using System.Reflection;
using ValEnv = System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Result Value)>;

namespace KatLang.Tests;

/// <summary>
/// The value-position read of a parameter that has no supplied cell (an internally
/// constructed context: every Model-C parameter a call binds is a supplied cell) reads its
/// value binding, and with none it is <see cref="EvalError.UnknownName"/> at the read's span —
/// nothing is evaluated. The legacy algorithm-channel and counted tiers that once sat between
/// those two had no production writer and were retired on 2026-10-13 (together with the
/// algorithm-only <c>BadArity</c> read P3 had pinned); this pins the remaining fallbacks in
/// the sync dispatcher and its async twin. Lean: the <c>.param</c> arm of <c>evalCounted</c>,
/// pinned by CoreTests <c>ArgumentValueOutcome.readOfValuedBinding</c> and
/// <c>readOfUnboundParameter</c>.
/// </summary>
public class ParameterReadFallbackTests
{
    private static readonly SourceSpan ReadSpan = new(3, 5, 3, 6);

    private static Expr ReadX() => new Expr.Param("x") { Span = ReadSpan };

    private static async Task<EvalResult<Evaluator.CountedResult>> EvalCountedAsync(ValEnv values)
    {
        var method = typeof(Evaluator).GetMethod("EvalCountedAsync", BindingFlags.Static | BindingFlags.NonPublic,
            [typeof(Expr), typeof(Evaluator.EvalCtx), typeof(IReadOnlyList<(string Name, Result Value)>)])!;
        var pending = (ValueTask<EvalResult<Evaluator.CountedResult>>)method.Invoke(null,
            [ReadX(), Evaluator.EvalCtx.Empty, values])!;
        return await pending;
    }

    [Fact]
    public async Task ValueBinding_IsRead_OnBothPaths()
    {
        ValEnv values = [("x", new Result.Atom(7))];

        var sync = Evaluator.EvalCounted(ReadX(), Evaluator.EvalCtx.Empty, values);
        var twin = await EvalCountedAsync(values);

        Assert.False(sync.IsError);
        Assert.Equal(new Result.Atom(7), sync.Value.Value);
        Assert.False(twin.IsError);
        Assert.Equal(new Result.Atom(7), twin.Value.Value);
    }

    [Fact]
    public async Task NoBinding_IsUnknownName_AtTheReadSpan_OnBothPaths()
    {
        var sync = Evaluator.EvalCounted(ReadX(), Evaluator.EvalCtx.Empty, []);
        var twin = await EvalCountedAsync([]);

        foreach (var result in new[] { sync, twin })
        {
            Assert.True(result.IsError);
            var error = Assert.IsType<EvalError.UnknownName>(result.Error);
            Assert.Equal("x", error.Name);
            Assert.Equal(ReadSpan, error.Span);
        }
    }
}
