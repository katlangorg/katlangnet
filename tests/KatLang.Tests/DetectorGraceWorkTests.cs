namespace KatLang.Tests;

/// <summary>
/// The detector's free-name walk sums no Grace weight (November 2026; finding <c>names-detection-grace-dead-grace-vectors</c> of the 2026-11-21
/// investigation, baseline <c>8947d21e</c>). Since ALIAS-UNIFY-1 (October 2026) an inferring body's signature is Q7's
/// (<c>StaticStructureQueries.Inputs</c>), which sums each inferred name's Grace weight over its occurrences, a shared
/// node counted with its exact occurrence multiplicity, and applies <see cref="GraceMovement"/>. Detection's own free-name
/// walk still kept a weight vector for every in-progress node, added every graced occurrence to the vector of each of its
/// ancestors, replayed a completed node's vector at every later reach, and summed the weights into a dictionary that
/// every caller then discarded: Q7's signature replaced the collection's names and order, and the two closed-body checks
/// passed throwaway dictionaries. That work was quadratic in a nested sum of graced names and fed nothing. The walk now
/// keeps only the completed nodes of its DAG memo. Signatures, Grace movement, eligibility and diagnostics are Q7's and
/// the rewrite's, as before.
/// </summary>
public sealed class DetectorGraceWorkTests
{
    /// <summary>One inferring body summing <paramref name="names"/> names in one row, each written with <paramref name="marker"/>.</summary>
    private static string Sum(int names, string marker)
        => "F = {\n    " + string.Join(" + ", Enumerable.Range(0, names).Select(i => $"{marker}x{i}")) + "\n}\n0\n";

    private static (FrontEndTraversalObservations Observations, DetectedProgram Program) Detect(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var program = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source), observations: observations);
        Assert.Empty(program.Diagnostics);
        return (observations, program);
    }

    private static IReadOnlyList<string> Signature(DetectedProgram program, string name)
        => program.Root.Properties.Single(property => property.Name == name).Value.Params;

    /// <summary>
    /// The walk of a graced body is its ungraced twin's plus the one expansion of each marker node, and the detected
    /// signature is Q7's: equal prefix markers block each other, so the order is the written one.
    /// </summary>
    [Theory]
    [InlineData(1)]
    [InlineData(32)]
    [InlineData(200)]
    public void AGracedBody_IsWalkedLikeItsUngracedTwin(int names)
    {
        var (gracedObservations, graced) = Detect(Sum(names, "~"));
        var (plainObservations, plain) = Detect(Sum(names, ""));
        Assert.Equal(plainObservations.DetectorCollectExpansions + names, gracedObservations.DetectorCollectExpansions);
        Assert.Equal(Enumerable.Range(0, names).Select(i => $"x{i}"), Signature(plain, "F"));
        Assert.Equal(Signature(plain, "F"), Signature(graced, "F"));
    }

    /// <summary>Q7's movement, read through detection alone (the law's own cases: <see cref="GraceMovementLawTests"/>).</summary>
    [Theory]
    [InlineData("F = ~a * 100 + b * 10 + ~~c", "a,c,b")]
    [InlineData("F = a~~ * 10 + b~", "b,a")]
    [InlineData("F = s~ * 100 + x~ * 10 + y", "y,s,x")]
    [InlineData("F = s * 100 + ~x * 10 + ~y", "x,y,s")]
    [InlineData("F = a~ + ~a + b", "a,b")]
    public void DetectedSignatures_AreQ7sGraceMovedOrder(string declaration, string expected)
    {
        var (_, program) = Detect(declaration + "\n0\n");
        Assert.Equal(expected.Split(','), Signature(program, "F"));
    }

    /// <summary>
    /// Q7 counts repeated reaches of a marked name while the detector records its first occurrence: under a 40-level diamond the marked
    /// <c>g</c> has 2^40 occurrences of weight −1, moving it to the front, while the walk expands each of the diamond's
    /// 41 distinct nodes once.
    /// </summary>
    [Fact]
    public void ASharedGracedSubtree_IsWalkedOnce_AndMovesPastTwoNames()
    {
        const int Depth = 40;
        Expr diamond = new Expr.Grace(new Expr.Resolve("g"), -1);
        for (var i = 0; i < Depth; i++) diamond = new Expr.Binary(BinaryOp.Add, diamond, diamond);
        var root = new Algorithm.User(null, [], [], [], [new Expr.Resolve("a"), new Expr.Resolve("b"), diamond]);
        var observations = new FrontEndTraversalObservations();
        var program = ParameterDetector.DetectPrevalidated(root, observations: observations);
        Assert.Empty(program.Diagnostics);
        Assert.Equal(["g", "a", "b"], program.Root.Params);
        Assert.Equal(Depth + 1, observations.DetectorCollectExpansions);
    }

    /// <summary>
    /// Detection of the graced and ungraced bodies differs only in the
    /// marked names. Eight times the names cost about four times more now (32 → 256 names: 81 KB → 345 KB measured); the
    /// per-visit vectors made it 26.8 times (146 KB → 3.9 MB), each marker adding a weight to the vector of every enclosing
    /// node. A coarse ratio: each figure is the least of five warmed-up runs on this thread.
    /// </summary>
    [Fact]
    public void GracedMinusUnmarkedDetectionBytes_StayWithinTheMeasuredGrowthBound()
    {
        long Cost(int names) => DetectionBytes(Sum(names, "~")) - DetectionBytes(Sum(names, ""));
        var few = Cost(32);
        var many = Cost(256);
        Assert.True(few > 0, $"{few} bytes");
        Assert.True(many < 12 * few, $"32 marked names cost {few} bytes, 256 cost {many}");
    }

    private static long DetectionBytes(string source)
    {
        for (var warm = 0; warm < 3; warm++)
            _ = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        var least = long.MaxValue;
        for (var run = 0; run < 5; run++)
        {
            var root = SourceProvenance.ParseSyntaxValidRoot(source);
            var before = GC.GetAllocatedBytesForCurrentThread();
            var program = ParameterDetector.DetectPrevalidated(root);
            var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.Empty(program.Diagnostics);
            least = Math.Min(least, bytes);
        }
        return least;
    }
}
