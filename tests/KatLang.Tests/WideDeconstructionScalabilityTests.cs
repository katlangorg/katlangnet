using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Regression coverage for wide assignment-deconstruction scalability. A comma binding pattern
/// <c>x0, ..., x{N-1} = RHS</c> elaborates to one shared <c>$deconstruct$N</c> source property
/// plus one target property per name, each binding through a synthetic inline helper that carries
/// the full N-capture sequence-value pattern. These tests pin the observable semantics (property
/// order, per-position values, collision/duplicate/recovery diagnostics, deferred arity errors, and
/// the retained helper pattern) AND the linear growth of the parse + front-end work in the number
/// of targets. That work was previously O(N^2): each of the N helpers carried the full N-capture
/// parameter list, and three front-end passes plus a parser validation walk each did O(N) work per
/// helper. The correction keeps the elaboration identical while making each helper cost O(1) to
/// process, so a wide deconstruction is now linear.
/// </summary>
public class WideDeconstructionScalabilityTests
{
    private static decimal[] Atoms(string source) => KatLangEngine.EvaluateToAtoms(source).ToArray();

    /// <summary>Builds <c>x0, x1, ..., x{n-1} = rhs</c> (n >= 2 targets).</summary>
    private static string WideSource(int n, string rhs)
    {
        var sb = new StringBuilder();
        for (var i = 0; i < n; i++)
            sb.Append(i == 0 ? "x0" : $", x{i}");
        return sb.Append(" = ").Append(rhs).ToString();
    }

    // ───────────────────────── structure / order / helper pattern ─────────────────────────

    [Fact]
    public void Elaboration_HoistsOneSharedSourceThenTargetsInWrittenOrder()
    {
        const int n = 400;
        var root = (Algorithm.User)Parser.Parse(WideSource(n, $"range(1, {n})") + "\nOutput = x0").Root;

        var expected = new List<string> { "$deconstruct$0" };
        for (var i = 0; i < n; i++)
            expected.Add($"x{i}");

        // Exactly one shared source, then every target property in written order (Output is not
        // a property). A re-evaluation regression would produce several sources or reorder targets.
        Assert.Equal(expected, root.Properties.Select(property => property.Name));
    }

    [Fact]
    public void Elaboration_EachTargetBindsSharedSourceThroughFullPatternHelper()
    {
        const int n = 60;
        var root = (Algorithm.User)Parser.Parse(WideSource(n, $"range(1, {n})") + "\nOutput = x0").Root;

        foreach (var i in new[] { 0, 23, n - 1 })
        {
            var body = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == $"x{i}").Value);
            var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
            var helper = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.Block>(call.Function).Algorithm);

            // The helper is the synthetic assignment-deconstruction leaf and STILL carries the full
            // N-capture sequence-value pattern — the frontend leaf guards must preserve it, because
            // the evaluator needs it for arity binding and written-pattern error phrasing.
            Assert.True(helper.IsAssignmentDeconstructionHelper);
            var sequence = Assert.IsType<SequenceValueParameterPattern>(Assert.Single(helper.ParameterPatterns));
            Assert.Equal(n, sequence.Items.Count);
            Assert.Equal(n, helper.Params.Count);

            // Its output is the single bound target, rewritten to a Param by ParameterDetector.
            var selected = Assert.IsType<Expr.Param>(Assert.Single(helper.Output));
            Assert.Equal($"x{i}", selected.Name);

            // Its argument resolves the one shared source.
            var argument = Assert.IsType<Expr.Resolve>(Assert.Single(((Algorithm.User)call.Args).Output));
            Assert.Equal("$deconstruct$0", argument.Name);
        }
    }

    // ───────────────────────── per-position values ─────────────────────────

    [Fact]
    public void Semantics_WideFixedTargets_BindByPosition()
    {
        const int n = 120;
        // range(1, n) has n items; x{i} binds item i+1.
        Assert.Equal([1m, 60m, 120m], Atoms(WideSource(n, $"range(1, {n})") + "\nx0, x59, x119"));
    }

    [Fact]
    public void Semantics_WidePrefixCollectingSuffix_BindsMovableMiddleAtScale()
    {
        // 100 fixed prefix, one movable collecting binding, two fixed suffix, over range(1, 150):
        // x0=1..x99=100, rest=[101..148] (48 items), y=149, z=150.
        var sb = new StringBuilder();
        for (var i = 0; i < 100; i++)
            sb.Append(i == 0 ? "x0" : $", x{i}");
        sb.Append(", *rest, y, z = range(1, 150)\nx0, x99, rest.count, y, z");
        Assert.Equal([1m, 100m, 48m, 149m, 150m], Atoms(sb.ToString()));
    }

    [Fact]
    public void Semantics_CaseSensitiveTargetsStayDistinct()
    {
        // `A` and `a` are different targets under ordinal name comparison.
        Assert.Equal([1m, 2m], Atoms("A, a = (1, 2)\nA, a"));
    }

    // ───────────────────────── deferred arity + written-pattern phrasing ─────────────────────────

    [Fact]
    public void Semantics_ArityMismatch_StaysDeferredAndPhrasedAgainstWrittenPattern()
    {
        // The frontend leaf guards must not strip the helper's full pattern: a wrong-arity
        // deconstruction still fails at evaluation time (deferred), and the diagnostic describes
        // the WRITTEN pattern, not the synthetic helper call.
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("x, y, z = (1, 2)\nz"));
        var message = failure.ToDisplayString();
        Assert.Contains("Assignment pattern `x, y, z`", message, StringComparison.Ordinal);
        Assert.DoesNotContain("(inline library)", message, StringComparison.Ordinal);
    }

    [Fact]
    public void Semantics_UnreferencedWrongArityDeconstruction_DoesNotError()
    {
        // Deferred semantics: an unused deconstruction never binds, so a wrong arity is silent.
        Assert.Equal([5m], Atoms("x, y, z = (1, 2)\nOutput = 5"));
    }

    // ───────────────────────── collision + duplicate + recovery diagnostics ─────────────────────────

    [Fact]
    public void Diagnostics_DuplicateTargetsWithinOnePattern_ReportedInOrder()
    {
        var result = Parser.ParseSyntax("a, b, a, c, b = range(1, 5)\nOutput = a");
        var duplicates = result.Diagnostics
            .Where(d => d.Message.Contains("already defined", StringComparison.Ordinal))
            .ToList();

        // The repeated `a` (3rd target) then the repeated `b` (5th target), in declaration order.
        Assert.Collection(
            duplicates,
            d => Assert.Contains("Property 'a'", d.Message, StringComparison.Ordinal),
            d => Assert.Contains("Property 'b'", d.Message, StringComparison.Ordinal));
        Assert.True(duplicates[0].Span.StartColumn < duplicates[1].Span.StartColumn);
    }

    [Fact]
    public void Diagnostics_TargetsCollideWithOrdinaryPropertyFunctionAndPriorTarget()
    {
        // A deconstruction target collides with an earlier ordinary property (P), a clause-defined
        // function (F), and a prior deconstruction's target (a) — the same collision mechanism,
        // reported in declaration order with the offending declaration's span.
        var result = Parser.ParseSyntax(
            """
            P = 1
            F(x) = x
            a, b = (1, 2)
            P, Q = (3, 4)
            F, R = (5, 6)
            a, S = (7, 8)
            Output = 1
            """);

        var lines = result.Diagnostics
            .Where(d => d.Message.Contains("already defined", StringComparison.Ordinal))
            .Select(d => d.Span.StartLineNumber)
            .ToList();

        Assert.Equal([4, 5, 6], lines);
    }

    [Fact]
    public void Recovery_MalformedTargetInPattern_DoesNotThrowAndReports()
    {
        // A non-identifier target (`5`) breaks the binding-pattern lookahead; the parser recovers,
        // reports, and still returns a well-formed root instead of throwing.
        var result = Parser.ParseSyntax("x, 5, z = (1, 2, 3)\nOutput = 1");
        Assert.NotNull(result.Root);
        Assert.NotEmpty(result.Diagnostics);
    }

    // ───────────────────────── scaling regression (allocation growth, never time) ─────────────────────────

    [Fact]
    public void Scaling_ParseAndFrontEndAllocation_GrowsLinearlyInTargetCount()
    {
        // Deterministic scaling guard. Parse + front-end allocation for 2N targets must grow by only
        // a small linear factor over N. Under the previous O(N^2) elaboration (each of the N helpers
        // carrying and being re-walked over its full N-capture pattern), doubling the target count
        // roughly quadrupled the work (~4x); the corrected path is ~2x. Thread-local allocation is
        // measured so parallel tests never pollute the count, and only the GROWTH RATIO is asserted
        // (never elapsed time), so the guard is robust across machines yet fails under the old path.
        Warm();
        var baseAllocation = MeasureParseAllocation(2000);
        var doubleAllocation = MeasureParseAllocation(4000);

        var ratio = (double)doubleAllocation / baseAllocation;
        Assert.True(
            ratio < 3.0,
            $"parse+front-end allocation for 2N targets grew {ratio:F2}x over N " +
            $"(expected ~2x linear; the previous quadratic path was ~4x). " +
            $"N={baseAllocation} bytes, 2N={doubleAllocation} bytes.");
    }

    private static void Warm() => _ = Parser.Parse(WideSource(256, "range(1, 256)"));

    private static long MeasureParseAllocation(int n)
    {
        var source = WideSource(n, $"range(1, {n})");
        _ = Parser.Parse(source); // JIT this exact size path before measuring.

        var before = GC.GetAllocatedBytesForCurrentThread();
        _ = Parser.Parse(source);
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    // ───────────────────────── large deterministic case ─────────────────────────

    [Fact]
    public void LargeCase_TenThousandTargets_ParsesAndElaboratesWithoutBlowup()
    {
        const int n = 10_000;
        var result = Parser.Parse(WideSource(n, $"range(1, {n})") + "\nOutput = x0");

        // Parsing AND front-end elaboration both complete with no errors and no stack failure.
        Assert.False(
            result.HasErrors,
            string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));

        var root = (Algorithm.User)result.Root;

        // Expected target/source counts are preserved: one shared source + n ordered targets.
        Assert.Equal(n + 1, root.Properties.Count);
        Assert.Equal("$deconstruct$0", root.Properties[0].Name);
        Assert.Equal("x0", root.Properties[1].Name);
        Assert.Equal($"x{n - 1}", root.Properties[n].Name);

        // No source/module resource limit is incorrectly triggered by an in-budget program.
        Assert.DoesNotContain(
            result.Diagnostics,
            d => d.Message.Contains("maximum", StringComparison.OrdinalIgnoreCase));
    }
}
