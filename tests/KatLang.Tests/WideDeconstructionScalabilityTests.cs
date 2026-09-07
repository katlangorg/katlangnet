using System.Text;
using System.Numerics;
using KatLang.ParserFuzz;
using Xunit.Abstractions;

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
public class WideDeconstructionScalabilityTests(ITestOutputHelper output)
{
    private static Decimal128[] Atoms(string source) => KatLangEngine.EvaluateToAtoms(source).ToArray();

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
        var root = (Algorithm.User)SourceProvenance.ParseValid(WideSource(n, $"range(1, {n})") + "\nx0").Root;

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
        var root = (Algorithm.User)SourceProvenance.ParseValid(WideSource(n, $"range(1, {n})") + "\nx0").Root;

        foreach (var i in new[] { 0, 23, n - 1 })
        {
            var body = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == $"x{i}").Value);
            var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
            var helper = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(call.Function).Algorithm);

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
            var argument = Assert.IsType<Expr.Resolve>(Assert.Single(call.Args));
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
        Assert.Equal([5m], Atoms("x, y, z = (1, 2)\n5"));
    }

    // ───────────────────────── collision + duplicate + recovery diagnostics ─────────────────────────

    [Fact]
    public void Diagnostics_DuplicateTargetsWithinOnePattern_ReportedInOrder()
    {
        var result = Parser.ParseSyntax("a, b, a, c, b = range(1, 5)\na");
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
            1
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
        var result = Parser.ParseSyntax("x, 5, z = (1, 2, 3)\n1");
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

    // ───────────────────────── scaling regression (load-guard walk work, never time) ─────────────────────────

    /// <summary>Builds <c>x0 = 1</c> … <c>x{n-1} = 1</c> then <c>x0</c>: N ordinary definitions (control).</summary>
    private static string SeparateDefinitionsSource(int n)
    {
        var sb = new StringBuilder();
        for (var i = 0; i < n; i++)
            sb.Append('x').Append(i).Append(" = 1\n");
        return sb.Append("x0").ToString();
    }

    /// <summary>Builds N/2 two-target groups <c>a{i}, b{i} = (1, 2)</c> then <c>a0</c>: N targets in narrow groups (control).</summary>
    private static string NarrowGroupsSource(int n)
    {
        var sb = new StringBuilder();
        for (var i = 0; i < n / 2; i++)
            sb.Append('a').Append(i).Append(", b").Append(i).Append(" = (1, 2)\n");
        return sb.Append("a0").ToString();
    }

    private sealed record LoadGuardWalk(int Targets, long Steps, long DeclarationVisits, long NodeExpansions);

    /// <summary>
    /// Runs the load-elaboration guard — the first post-parse stage of <c>Parser.Parse</c> — over the
    /// SYNTAX root exactly as the pipeline does, observed through the base walker's passive step
    /// counters (<see cref="FrontEndTraversalObservations.WalkerSteps"/>).
    /// </summary>
    private static LoadGuardWalk MeasureLoadGuardWalk(int targets, string source)
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(source);

        var observations = new FrontEndTraversalObservations();
        var diagnostics = LoadElaborationGuard.CreateUnavailableDiagnostics(root, observations);
        Assert.Empty(diagnostics);
        // Each shape has at least one body and one expression per target. Check EVERY size,
        // including the last doubling, so a detached or partially disabled observer cannot pass.
        Assert.True(observations.WalkerAlgorithmExpansions >= targets);
        Assert.True(observations.WalkerExpressionExpansions >= targets);

        return new LoadGuardWalk(
            targets,
            observations.WalkerSteps,
            observations.WalkerParameterDeclarationVisits,
            observations.WalkerAlgorithmExpansions + observations.WalkerExpressionExpansions);
    }

    /// <summary>
    /// Every target of <c>x0, …, x{N-1} = RHS</c> contributes a fixed number of nodes to the syntax
    /// tree the guard walks: the target property's body algorithm, that body's call expression, the
    /// helper literal (<c>AlgorithmExpr</c>), the helper algorithm, the helper's one output row, and
    /// the call's one argument — six walker steps. The shared <c>$deconstruct$N</c> source, the root,
    /// and the report row are a constant on top.
    /// </summary>
    private const int LoadGuardStepsPerTarget = 6;

    private const int LoadGuardStepsConstant = 32;

    private static void AssertWideWalkBudget(LoadGuardWalk walk)
        => Assert.True(
            walk.Steps <= (long)LoadGuardStepsPerTarget * walk.Targets + LoadGuardStepsConstant,
            $"N={walk.Targets}: {walk.Steps} walker steps exceed the linear budget "
            + $"{(long)LoadGuardStepsPerTarget * walk.Targets + LoadGuardStepsConstant}; "
            + $"declaration visits={walk.DeclarationVisits}, node expansions={walk.NodeExpansions}.");

    [Fact]
    public void Scaling_LoadGuardWideWalk_StaysWithinLinearBudget()
    {
        // Bounded negative-control target: restoring only LoadWalker's declaration loop must
        // fail this WORK budget, even with linear node expansions and unchanged diagnostics.
        const int n = 256;
        var walk = MeasureLoadGuardWalk(n, WideSource(n, $"range(1, {n + 1})") + "\nx0");
        AssertWideWalkBudget(walk);
        Assert.Equal(6L * n + 7, walk.NodeExpansions);
        Assert.Equal(0, walk.DeclarationVisits);
    }

    private static void AssertPerDoublingGrowth(string scenario, IReadOnlyList<LoadGuardWalk> walks, string report)
    {
        for (var i = 1; i < walks.Count; i++)
        {
            Assert.True(walks[i - 1].Steps > 0, $"{scenario}: the guard walk recorded no work at N={walks[i - 1].Targets}.{report}");
            var ratio = (double)walks[i].Steps / walks[i - 1].Steps;
            Assert.True(
                ratio <= 2.2,
                $"{scenario}: load-guard walk work grew {ratio:F2}x from N={walks[i - 1].Targets} to N={walks[i].Targets} "
                + $"(linear growth is ~2x per doubling; the quadratic per-helper declaration rescan was ~4x).{report}");
        }
    }

    /// <summary>
    /// K2-R2 (September 2026). The load-elaboration guard (<see cref="LoadElaborationGuard"/>, the
    /// first post-parse stage of <c>Parser.Parse</c>, also run by <c>ParseAsync</c>, on deferred branches,
    /// and by semantic-model building) is an <see cref="AstWalker"/> that never took the walker's
    /// <c>VisitsExplicitParameterDeclarations</c> opt-out, so it iterated the shared N-declaration
    /// list of every one of the N deconstruction helpers: O(N²) no-op declaration visits, measured
    /// 0.5 s / 2.3 s / 9.7 s at 10k / 20k / 40k targets while every other front-end stage stayed
    /// linear, and ~114 s for a legal 629 KB program of 80k targets. The observed metric is the base
    /// walker's total step count INCLUDING every declaration the per-declaration loop examines, so a
    /// walker cannot pass by moving the rescans out of an expansion count. Deterministic: counts, never
    /// time. Both controls keep the same target count and shrink only the group width, so a failure
    /// here is attributed to the width of one group.
    /// </summary>
    [Fact]
    public void Scaling_LoadGuardWalk_GrowsLinearlyInTargetCount()
    {
        int[] sizes = [10_000, 20_000, 40_000];

        var wide = sizes.Select(n => MeasureLoadGuardWalk(n, WideSource(n, $"range(1, {n + 1})") + "\nx0")).ToList();
        var separate = sizes.Select(n => MeasureLoadGuardWalk(n, SeparateDefinitionsSource(n))).ToList();
        var narrow = sizes.Select(n => MeasureLoadGuardWalk(n, NarrowGroupsSource(n))).ToList();

        var report = Environment.NewLine + "load-guard walk work (steps / declaration visits / node expansions):" + Environment.NewLine
            + string.Join(Environment.NewLine, new[] { ("wide deconstruction", wide), ("separate definitions", separate), ("narrow groups", narrow) }
                .SelectMany(scenario => scenario.Item2.Select(w =>
                    $"  {scenario.Item1} N={w.Targets}: {w.Steps} / {w.DeclarationVisits} / {w.NodeExpansions}")));
        output.WriteLine(report);

        // 1. The guard inspects expression nodes only — a load directive is an expression, and a
        //    parameter declaration carries a name and spans, never an expression — so it examines NO
        //    explicit parameter declaration: in particular none of the N shared declarations of each
        //    of the N helpers (the former N² term).
        Assert.All(wide, w => Assert.True(
            w.DeclarationVisits == 0,
            $"the load guard examined {w.DeclarationVisits} explicit parameter declarations at N={w.Targets}; "
            + "it needs none, and per-helper visits of the shared declaration list are O(N^2)." + report));

        // 2. Justified absolute linear bound (see LoadGuardStepsPerTarget).
        Assert.All(wide, AssertWideWalkBudget);

        // 3. Per-doubling growth for the wide case and both controls.
        AssertPerDoublingGrowth("wide deconstruction", wide, report);
        AssertPerDoublingGrowth("separate definitions", separate, report);
        AssertPerDoublingGrowth("narrow groups", narrow, report);
    }

    /// <summary>
    /// The opt-out changes nothing the guard reports: with explicit parameter lists and a wide
    /// deconstruction present (the declarations it no longer iterates), every load directive is still
    /// found — a root <c>open 'url'</c>, a property value <c>load('url')</c>, and a nested block's own
    /// open — in document order, with the same message, code, severity and span whether or not the
    /// walk is observed. The observed walk records steps, and zero declaration visits.
    /// </summary>
    [Fact]
    public void LoadGuard_StillFindsEveryLoad_AndObservationChangesNoDiagnostic()
    {
        const string source = """
            open 'https://example.test/lib.kat'
            Lib = load('https://example.test/other.kat')
            F(a, b) = a + b
            x0, x1, x2, x3 = (1, 2, 3, 4)
            M = {
              open 'https://example.test/nested.kat'
              F(x0, x1)
            }
            x2
            """;
        var root = SourceProvenance.ParseSyntaxValidRoot(source);

        var unobserved = LoadElaborationGuard.CreateUnavailableDiagnostics(root);
        var observations = new FrontEndTraversalObservations();
        var observed = LoadElaborationGuard.CreateUnavailableDiagnostics(root, observations);

        Assert.Equal(3, unobserved.Count);
        Assert.All(unobserved, d => Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, d.Code));
        Assert.Equal([1, 2, 6], unobserved.Select(d => d.Span.StartLineNumber));
        Assert.Equal(
            unobserved.Select(d => (d.Message, d.Code, d.Severity, d.Span)),
            observed.Select(d => (d.Message, d.Code, d.Severity, d.Span)));

        Assert.True(observations.WalkerSteps > 0);
        Assert.True(observations.WalkerExpressionExpansions > 0);
        Assert.Equal(0, observations.WalkerParameterDeclarationVisits);
    }

    [Theory]
    [InlineData("x, *rest, y = (1, 2, 3)\nx, rest, y", 0)]
    [InlineData("x, y = (load('https://example.test/a'), load('https://example.test/b'))\nx", 2)]
    [InlineData("F((x, *rest)) = { open 'https://example.test/a'\nx }\nF((1, 2))", 1)]
    [InlineData("F(0) = load('https://example.test/a')\nF(x) = x\nF(0)", 1)]
    [InlineData("[1 + -load('https://example.test/a'), (load('https://example.test/b'))]:0", 2)]
    [InlineData("load('https://example.test/a').F(load('https://example.test/b'))", 2)]
    public async Task LoadGuard_ObservationIsNeutral_AndPublicParsersReportTheSameDiagnostics(string source, int loads)
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        var before = FrontEndFingerprint.ComputeParseResult(root, []);
        var unobserved = LoadElaborationGuard.CreateUnavailableDiagnostics(root);
        Assert.Equal(before, FrontEndFingerprint.ComputeParseResult(root, []));

        var observations = new FrontEndTraversalObservations();
        var observed = LoadElaborationGuard.CreateUnavailableDiagnostics(root, observations);
        Assert.Equal(before, FrontEndFingerprint.ComputeParseResult(root, []));
        Assert.Equal(loads, observed.Count);
        Assert.All(observed, d => Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, d.Code));
        // Diagnostic is a value record including message, code, severity and the complete span.
        Assert.Equal(unobserved, observed);
        Assert.Equal(unobserved, Parser.Parse(source).Diagnostics);
        Assert.Equal(unobserved, (await Parser.ParseAsync(source)).Diagnostics);
        Assert.True(observations.WalkerSteps > 0);
        Assert.Equal(0, observations.WalkerParameterDeclarationVisits);

        // A second walk of the SAME root needs its own visited set; concurrent parses/walks with
        // distinct observers must neither suppress diagnostics nor add to this observer's counts.
        var steps = observations.WalkerSteps;
        var repeated = await Task.WhenAll(Enumerable.Range(0, 4).Select(_ => Task.Run(() =>
        {
            var independent = new FrontEndTraversalObservations();
            Assert.Equal(observed, LoadElaborationGuard.CreateUnavailableDiagnostics(root, independent));
            Assert.Equal(observed, Parser.Parse(source).Diagnostics);
            return independent.WalkerSteps;
        })));
        Assert.All(repeated, count => Assert.Equal(steps, count));
        Assert.Equal(steps, observations.WalkerSteps);
    }

    // ───────────────────────── large deterministic case ─────────────────────────

    [Fact]
    public void LargeCase_TenThousandTargets_ParsesAndElaboratesWithoutBlowup()
    {
        const int n = 10_000;
        var result = Parser.Parse(WideSource(n, $"range(1, {n})") + "\nx0");

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
