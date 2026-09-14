using System.Globalization;
using System.Numerics;

namespace KatLang.Tests.Randomness;

/// <summary>Shared plumbing for the seeded-randomness suites.</summary>
internal static class SeededRun
{
    public static RunOptions Options(long seed) => new() { RandomSeed = seed };

    public static Decimal128 D(string text)
        => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);

    public static Decimal128 D(long value) => (Decimal128)value;

    /// <summary>A fresh reference word stream for <paramref name="seed"/>.</summary>
    public static ReferenceSplitMix64 Words(long seed) => new(ReferenceSplitMix64.StateOf(seed));

    public static string Display(RunResult result) => result.ToDisplayString().ReplaceLineEndings("\n");

    public static RunResult.Success Success(string source, long? seed)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, seed is { } value ? Options(value) : null));

    public static async Task<RunResult.Success> SuccessAsync(string source, long? seed)
        => Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync(source, seed is { } value ? Options(value) : null));

    public static IReadOnlyList<Decimal128> Atoms(string source, long seed) => Success(source, seed).Atoms;

    public static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    public static void AssertSameAtoms(IReadOnlyList<Decimal128> expected, IReadOnlyList<Decimal128> actual)
    {
        Assert.Equal(expected.Count, actual.Count);
        for (var i = 0; i < expected.Count; i++)
        {
            Assert.True(
                expected[i] == actual[i],
                $"atom {i}: expected {expected[i].ToString(CultureInfo.InvariantCulture)} but got {actual[i].ToString(CultureInfo.InvariantCulture)}");
        }
    }

    public static void AssertSameValue(Result expected, Result actual)
        => Assert.True(Result.ValueComparer.Equals(expected, actual), $"expected {expected} but got {actual}");

    /// <summary>Two-word 128-bit draw with a power-of-two span never rejects, so the value is the LOW word modulo 2^32.</summary>
    public static Decimal128 LowWordMod2Pow32(ReferenceSplitMix64 words)
    {
        _ = words.Next(); // high half
        return D((long)(words.Next() % (1UL << 32)));
    }
}
