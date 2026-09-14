using System.Globalization;
using System.Numerics;
using static KatLang.Tests.Randomness.SeededRun;

namespace KatLang.Tests.Randomness;

/// <summary>
/// A seed makes draw COUNT and ORDER observable, so these tests pin — with exact
/// seeded values — that the existing evaluation rules decide which random calls
/// execute: the zero-argument property cache, left-to-right argument evaluation,
/// once-only evaluation of written arguments (including the patterned-call
/// regression class), lazy <c>if</c> branches, callbacks in sequence order,
/// deconstruction, and the engine's output-then-<c>DisplayDecimals</c> order.
///
/// <para>Every program draws through <c>R = Math.RandomInt(0, 4294967296)</c>: a 2^32
/// span divides 2^128, so each <c>R()</c> is exactly one un-rejected 128-bit draw
/// (two raw words) whose value is the LOW word modulo 2^32. Call k of a run therefore
/// returns reference word 2k, which makes "which draw did this position get" a direct
/// assertion against the test-side stream.</para>
/// </summary>
public class SeededEvaluationOrderTests
{
    private const long Seed = 0x5EED;

    private const string R = "R = Math.RandomInt(0, 4294967296)\n";

    /// <summary>The first <paramref name="count"/> draw values of the seed's stream, in draw order.</summary>
    private static Decimal128[] Draws(int count)
    {
        var words = Words(Seed);
        return Enumerable.Range(0, count).Select(_ => LowWordMod2Pow32(words)).ToArray();
    }

    private static Decimal128[] Run(string body) => [.. Atoms(R + body, Seed)];

    // ── Zero-argument property cache ──────────────────────────────────────────

    [Fact]
    public void PropertyStyleAccess_ReusesOneDraw_WhileExplicitCallsDrawAgain()
    {
        var d = Draws(3);

        // Fun, Fun: ONE evaluation, reused; the trailing R() proves only one draw
        // was consumed before it.
        Assert.Equal([d[0], d[0], d[1]], Run("Fun = R()\nFun, Fun, R()"));

        // Fun(), Fun(): explicit calls evaluate the body each time.
        Assert.Equal([d[0], d[1], d[2]], Run("Fun = R()\nFun(), Fun(), R()"));
    }

    [Fact]
    public void CacheHit_OfAMultiDrawProperty_ConsumesNoFurtherWords()
    {
        var d = Draws(3);

        // Both draws happen when the body evaluates; the hit replays them without
        // touching the stream, so the trailing R() is the THIRD draw.
        Assert.Equal([d[0], d[1], d[0], d[1], d[2]], Run("Fun = R(), R()\nFun, Fun, R()"));
    }

    [Fact]
    public void ExplicitCall_NeverReadsOrReplacesTheCachedEntry()
    {
        var d = Draws(3);

        // A = first draw (cached); A() = second draw (bypass, not stored); A again = the
        // cached first draw; R() = third.
        Assert.Equal([d[0], d[1], d[0], d[2]], Run("A = R()\nA, A(), A, R()"));
    }

    [Fact]
    public void LocalOnlyProperty_IsDrawnOncePerBindingContext()
    {
        // Tutorial contract: a property capturing a parameter is cached per binding
        // context; property-style reads in one context share one draw, and every
        // explicit call opens a NEW context whose A is drawn afresh.
        var d = Draws(4);
        var atoms = Run("F(x) = {\n    A = R() + x\n    B = A, A\n    B, B, B(), B()\n}\nF(0), R()");

        Assert.Equal([d[0], d[0], d[0], d[0], d[1], d[1], d[2], d[2], d[3]], atoms);
    }

    [Fact]
    public void SelfContainedProperty_ReadFromSeveralCalls_YieldsOneDrawForTheWholeRun()
    {
        var d = Draws(2);

        Assert.Equal([d[0], d[0], d[0], d[1]], Run("A = R()\nF(x) = A + x\nF(0), F(0), F(0), R()"));
    }

    // ── Written order ─────────────────────────────────────────────────────────

    [Fact]
    public void CallArguments_DrawLeftToRight()
    {
        var d = Draws(4);

        Assert.Equal([d[2], d[1], d[0], d[3]], Run("F(a, b, c) = c, b, a\nF(R(), R(), R()), R()"));
    }

    [Fact]
    public void NestedCalls_DrawInEvaluationOrder()
    {
        var d = Draws(4);

        // Outer first argument, then the inner call's two arguments, then the row.
        Assert.Equal([d[0], d[1], d[2], d[3]], Run("H(a, b) = a, b\nH(R(), H(R(), R())), R()"));
    }

    [Fact]
    public void GroupedAndSpreadArguments_DrawOnceInWrittenOrder()
    {
        var d = Draws(3);

        Assert.Equal([d[0], d[1], d[2]], Run("P((x, y)) = x, y\nP((R(), R())), R()"));
        Assert.Equal([d[1], d[0], d[2]], Run("F(a, b) = b, a\nF((R(), R())*), R()"));
        Assert.Equal([d[1], d[0], d[2]], Run("S = R(), R()\nF(a, b) = b, a\nF(S*), R()"));
    }

    [Fact]
    public void DeconstructionRightHandSide_IsDrawnOnce()
    {
        var d = Draws(3);

        Assert.Equal([d[0], d[1], d[0], d[1], d[2]], Run("x, y = R(), R()\nx, y, x, y, R()"));
    }

    [Fact]
    public void Callbacks_DrawInSequenceOrder()
    {
        var d = Draws(4);

        var mapped = Run("M(v) = v * 0 + R()\n[10, 20, 30].map(M)*, R()");
        Assert.Equal([d[0], d[1], d[2], d[3]], mapped);

        // reduce supplies (element, accumulator) to its reducer.
        var reduced = Run("Acc(v, total) = total + R()\nreduce((1, 2, 3), Acc, 0), R()");
        Assert.Equal([d[0] + d[1] + d[2], d[3]], reduced);
    }

    // ── Patterned-call single evaluation (historical regression class) ────────

    [Fact]
    public void PatternedCall_EvaluatesItsGroupedRandomArgumentExactlyOnce()
    {
        // The prepared call-argument path once evaluated a zero-parameter parenthesized
        // block twice (combined value + written-slot view). Under a seed a double
        // evaluation would consume four draws and shift the trailing R() to the
        // FIFTH; exactly one logical evaluation puts it at the third.
        var d = Draws(3);

        Assert.Equal([d[0], d[1], d[2]], Run("Pair((a, b)) = a, b\nPair((R(), R())), R()"));
        Assert.Equal([d[0], d[1], d[2]], Run("Pair((a, b)) = a, b\n(R(), R()).Pair, R()"));
        Assert.Equal([D(4), d[0], d[1], d[2]], Run("Pair((items, marker)) = items.count + marker * 0, marker\nPair((range(1, 4), R())), R(), R()"));
    }

    // ── Laziness ──────────────────────────────────────────────────────────────

    [Fact]
    public void BuiltinIf_DrawsTheConditionAndOnlyTheSelectedBranch()
    {
        var d = Draws(3);

        // Condition: first draw (always true); selected branch: second draw; the
        // unselected branch never draws, so the trailing R() is the third.
        Assert.Equal([d[1], d[2]], Run("if(R() >= 0, R(), R()), R()"));
        // Condition false: the THIRD written argument is the second draw.
        Assert.Equal([d[1], d[2]], Run("if(R() < 0, R(), R()), R()"));
        // A user clause family selects by pattern: only the matched body draws.
        Assert.Equal([d[0], d[1]], Run("C(0) = R()\nC(x) = R() * 0 - 1\nC(0), R()"));
    }

    // ── DisplayDecimals ───────────────────────────────────────────────────────

    [Fact]
    public void DisplayDecimals_IsEvaluatedAfterTheOutputRows_AndOccupiesTheLaterStreamPosition()
    {
        var words = Words(Seed);
        var expectedFraction = ReferenceRandomOracle.Random(words, D(0), D(1));
        var expectedDecimals = ReferenceRandomOracle.RandomInt(words, 2, 5);

        var success = Success("Math.Random(0, 1)\nDisplayDecimals = Math.RandomInt(2, 5)", Seed);

        Assert.True(expectedFraction == Assert.Single(success.Atoms));
        Assert.Equal((int)expectedDecimals, success.DisplayOptions.Decimals);
        var rendered = Display(success);
        Assert.Equal((int)expectedDecimals, rendered.Length - rendered.IndexOf('.', StringComparison.Ordinal) - 1);
        Assert.Equal(rendered, Display(Success("Math.Random(0, 1)\nDisplayDecimals = Math.RandomInt(2, 5)", Seed)));
    }

    [Fact]
    public void DisplayDecimals_ReadByAnOutputRow_IsDrawnThereAndReusedByTheEngine()
    {
        var words = Words(Seed);
        var expectedDecimals = ReferenceRandomOracle.RandomInt(words, 2, 5);
        var expectedFraction = ReferenceRandomOracle.Random(words, D(0), D(1));

        var success = Success("DisplayDecimals = Math.RandomInt(2, 5)\nDisplayDecimals, Math.Random(0, 1)", Seed);

        Assert.Equal(2, success.Atoms.Count);
        Assert.True(expectedDecimals == success.Atoms[0]);
        Assert.True(expectedFraction == success.Atoms[1]);
        // The engine's later property read is a cache hit: the same value, no new draw
        // (a fresh draw would have taken the fraction's stream position instead).
        Assert.Equal((int)expectedDecimals, success.DisplayOptions.Decimals);
        var fractionRow = Display(success).Split('\n')[1];
        Assert.Equal((int)expectedDecimals, fractionRow.Length - fractionRow.IndexOf('.', StringComparison.Ordinal) - 1);
    }
}
