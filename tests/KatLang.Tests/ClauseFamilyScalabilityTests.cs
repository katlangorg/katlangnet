using System.Text;
using System.Threading.Tasks;

namespace KatLang.Tests;

/// <summary>
/// Regression coverage for conditional clause-family duplicate/equivalence matching. A same-name
/// clause group <c>F(p0) = ... F(pK) = ...</c> must reject a branch whose pattern is match-equivalent
/// to an earlier one (<see cref="Pattern.IsMatchEquivalent"/> — spelling-independent, but repeated
/// binder positions must agree). That check was an all-pairs scan: inserting the k-th clause compared
/// it against all k-1 earlier clauses, so a family of C clauses did O(C^2) exact comparisons both at
/// parse time (the insert scan) and at evaluation time (<see cref="Algorithm.HasDuplicateBranchPatterns"/>).
/// The correction indexes patterns in a hashed set whose equality IS <c>IsMatchEquivalent</c> and whose
/// hash is a deterministic structural fingerprint consistent with it, making both checks O(C) while
/// preserving branch order, the duplicate diagnostics, and their order/spans.
///
/// <para>These tests pin (a) the equivalence SEMANTICS across the pattern kinds it distinguishes,
/// (b) the diagnostics and their order, and (c) the linear growth of the duplicate-detection work.
/// The comparison count is measured through a passive OPERATION-SCOPED
/// <see cref="PatternComparisonObservations"/> passed to the indexed comparer for one parse (no static
/// state, no reset), proving the indexed lookup does O(C) exact comparisons. A separate allocation-ratio
/// guard is design-independent and fails under the old all-pairs implementation even though that
/// implementation would bypass the observed comparer entirely.</para>
/// </summary>
public class ClauseFamilyScalabilityTests
{
    private static decimal[] Atoms(string source) => KatLangEngine.EvaluateToAtoms(source).ToArray();

    private static IReadOnlyList<Diagnostic> DuplicateBranchDiagnostics(string source)
        => Parser.ParseSyntax(source).Diagnostics
            .Where(d => d.Message.Contains("Duplicate branch pattern", StringComparison.Ordinal))
            .ToList();

    // ───────────────────────── equivalence semantics ─────────────────────────

    [Fact]
    public void FirstClause_OfManyLiteralClauses_Evaluates()
    {
        var sb = new StringBuilder();
        for (var i = 0; i < 50; i++)
            sb.Append($"F({i}) = {i * 10}\n");
        sb.Append("F(0), F(25), F(49)");
        Assert.Equal([0m, 250m, 490m], Atoms(sb.ToString()));
    }

    [Fact]
    public void BinderSpelling_IsIrrelevant_SoTwoSingleBinderClausesAreDuplicates()
    {
        // F(a) and F(b) match the same inputs (any one value): match-equivalent, so the second is a
        // duplicate branch even though the binder names differ.
        var duplicates = DuplicateBranchDiagnostics("F(a) = 1\nF(b) = 2\nF(3)");
        Assert.Single(duplicates);
    }

    [Fact]
    public void LiteralAndBinder_AreNotEquivalent()
    {
        // F(0) matches only 0; F(x) matches anything. Distinct — no duplicate — and both dispatch.
        Assert.Empty(DuplicateBranchDiagnostics("F(0) = 1\nF(x) = 2\nF(0)"));
        Assert.Equal([1m, 2m], Atoms("F(0) = 1\nF(x) = 2\nF(0), F(7)"));
    }

    [Fact]
    public void DistinctLiteralClauses_AreNotDuplicates()
        => Assert.Empty(DuplicateBranchDiagnostics("F(0) = 1\nF(1) = 2\nF(2) = 3\nF(1)"));

    [Fact]
    public void RepeatedBinderStructure_MustAgree_ForEquivalence()
    {
        // (a, a) constrains the two positions to be EQUAL; (b, c) does not. Different match sets, so
        // NOT equivalent — no duplicate.
        Assert.Empty(DuplicateBranchDiagnostics("F((a, a)) = 1\nF((b, c)) = 2\nF((1, 2))"));

        // (a, a) and (b, b) impose the same equality constraint: equivalent, so a duplicate.
        Assert.Single(DuplicateBranchDiagnostics("F((a, a)) = 1\nF((b, b)) = 2\nF((1, 1))"));
    }

    [Fact]
    public void NestedSequencePatterns_CompareStructurally()
    {
        // (0, x) vs (0, y): literal 0 equal, binder renamed — equivalent, duplicate.
        Assert.Single(DuplicateBranchDiagnostics("F((0, x)) = 1\nF((0, y)) = 2\nF((0, 9))"));

        // (0, x) vs (1, x): leading literals differ — not equivalent, no duplicate.
        Assert.Empty(DuplicateBranchDiagnostics("F((0, x)) = 1\nF((1, x)) = 2\nF((0, 9))"));
    }

    [Fact]
    public void DifferentArityNestedPatterns_AreNotEquivalent()
        => Assert.Empty(DuplicateBranchDiagnostics("F((a, b)) = 1\nF((a, b, c)) = 2\nF((1, 2))"));

    // ───────────────────────── diagnostics: presence, order, spans ─────────────────────────

    [Fact]
    public void DuplicateNearBeginning_IsReportedOnce()
    {
        var sb = new StringBuilder("F(0) = 0\nF(0) = 1\n");
        for (var i = 1; i < 40; i++)
            sb.Append($"F({i}) = {i}\n");
        sb.Append("F(0)");
        Assert.Single(DuplicateBranchDiagnostics(sb.ToString()));
    }

    [Fact]
    public void DuplicateNearEnd_IsReportedOnce()
    {
        var sb = new StringBuilder();
        for (var i = 0; i < 40; i++)
            sb.Append($"F({i}) = {i}\n");
        sb.Append("F(39) = 999\nF(0)"); // duplicates the last distinct clause
        Assert.Single(DuplicateBranchDiagnostics(sb.ToString()));
    }

    [Fact]
    public void SeveralDuplicates_AreReportedInDeclarationOrder()
    {
        // Distinct clauses 0..9, then re-declare 2, 5, 8 (in that order). Each re-declaration is
        // match-equivalent to its earlier twin and is flagged, in written order.
        var sb = new StringBuilder();
        for (var i = 0; i < 10; i++)
            sb.Append($"F({i}) = {i}\n");
        sb.Append("F(2) = 20\nF(5) = 50\nF(8) = 80\nF(0)");

        var duplicates = DuplicateBranchDiagnostics(sb.ToString());
        Assert.Equal(3, duplicates.Count);

        var lines = duplicates.Select(d => d.Span.StartLineNumber).ToList();
        Assert.Equal(lines.OrderBy(line => line).ToList(), lines); // strictly increasing (declaration order)
    }

    [Fact]
    public void DuplicateDiagnostic_CarriesTheDuplicateClauseSpan()
    {
        var duplicates = DuplicateBranchDiagnostics("F(0) = 1\nF(1) = 2\nF(0) = 3\nF(0)");
        var duplicate = Assert.Single(duplicates);
        Assert.Equal(3, duplicate.Span.StartLineNumber); // the offending re-declaration, not the original
    }

    // ───────────────────────── executable behavior of a compact family ─────────────────────────

    [Fact]
    public void ValidCompactFamily_DispatchesEveryBranch()
    {
        const string source =
            """
            Classify(0) = 100
            Classify(1) = 200
            Classify(n) = n
            Classify(0), Classify(1), Classify(2), Classify(7)
            """;
        Assert.Equal([100m, 200m, 2m, 7m], Atoms(source));
    }

    [Fact]
    public void FamilyWithMatchEquivalentDuplicate_IsRejected()
    {
        // A family containing a match-equivalent duplicate is rejected. For parsed source the
        // duplicate is caught at parse time (the runtime HasDuplicateBranchPatterns guard reaches the
        // same verdict for hand-built ASTs); the indexed single-pass check preserves that rejection.
        var failure = Assert.IsType<RunResult.ParseFailure>(
            KatLangEngine.Run("F(a) = 1\nF(b) = 2\nF(3)"));
        Assert.Contains(
            failure.Errors,
            e => e.Message.Contains("Duplicate branch", StringComparison.Ordinal));
    }

    // ───────────────────────── scaling regression: exact-comparison work is linear ─────────────

    [Fact]
    public void DistinctClauseFamily_ExactComparisonWork_IsLinearNotQuadratic()
    {
        // A family of N DISTINCT literal clauses has no duplicates, so the indexed set resolves every
        // insertion by hash with at most a rare structural-collision comparison: O(N) exact
        // comparisons total. This measures the indexed comparer directly through a fresh operation-scoped
        // observer (no static state, no reset). We assert a generous linear bound: for N = 3000 the
        // indexed lookup does ~0 exact comparisons, far below 4*N = 12000, while an all-pairs scan
        // routed through this comparer would do ~4.5 million. (Allocation-ratio guard below catches an
        // all-pairs reversion that bypasses the comparer entirely.)
        const int n = 3000;
        var comparisons = MeasureComparisons(n);

        Assert.True(
            comparisons <= 4L * n,
            $"clause-family duplicate detection did {comparisons} exact IsMatchEquivalent comparisons for " +
            $"{n} distinct clauses (expected O(N) <= {4L * n}); an all-pairs scan would do ~{(long)n * (n - 1) / 2}.");
    }

    [Fact]
    public void ExactComparisonWork_GrowsLinearlyWhenClauseCountDoubles()
    {
        // Growth form: doubling the clause count must not roughly quadruple the exact-comparison work.
        // Both counts are near zero for distinct clauses, so guard the absolute linear bound rather than
        // a brittle ratio of small numbers; an all-pairs scan through this comparer blows past it.
        var atN = MeasureComparisons(1500);
        var at2N = MeasureComparisons(3000);

        Assert.True(atN <= 3L * 1500, $"comparisons at N=1500 were {atN}");
        Assert.True(at2N <= 3L * 3000, $"comparisons at 2N=3000 were {at2N}");
    }

    private static long MeasureComparisons(int n)
    {
        var source = DistinctFamily(n);
        _ = Parser.ParseSyntax(source, new PatternComparisonObservations()); // JIT the observed path first

        // A fresh observer belongs to this one parse; nothing crosses parses or threads.
        var observations = new PatternComparisonObservations();
        _ = Parser.ParseSyntax(source, observations);
        return observations.MatchEquivalenceComparisonCount;
    }

    [Fact]
    public void ParseAllocation_GrowsLinearlyInClauseCount()
    {
        // Design-independent scaling guard that fails under the old all-pairs implementation regardless
        // of where comparisons are counted. Parse allocation for 2N distinct clauses must grow only a
        // small linear factor over N. The old all-pairs duplicate scan allocated two dictionaries per
        // exact comparison and did ~C^2/2 comparisons, so its parse allocation was O(C^2) and doubling C
        // roughly quadrupled it (~4x); the indexed hashed lookup is ~2x. Thread-local allocation is
        // measured (parallel tests never pollute it) and only the GROWTH RATIO is asserted, never elapsed
        // time, so the guard is machine-independent yet fails under the quadratic implementation.
        _ = Parser.ParseSyntax(DistinctFamily(256)); // warm

        var baseAllocation = MeasureParseAllocation(1500);
        var doubleAllocation = MeasureParseAllocation(3000);

        var ratio = (double)doubleAllocation / baseAllocation;
        Assert.True(
            ratio < 3.0,
            $"clause-family parse allocation for 2N clauses grew {ratio:F2}x over N (expected ~2x linear; " +
            $"the previous all-pairs O(C^2) scan was ~4x). N={baseAllocation} bytes, 2N={doubleAllocation} bytes.");
    }

    private static long MeasureParseAllocation(int n)
    {
        var source = DistinctFamily(n);
        _ = Parser.ParseSyntax(source); // JIT this exact size before measuring

        var before = GC.GetAllocatedBytesForCurrentThread();
        _ = Parser.ParseSyntax(source);
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    [Fact]
    public void ConcurrentParses_ObserveIndependentComparisonCounts()
    {
        // Each parse owns its own PatternComparisonObservations, passed explicitly to the comparer, so
        // concurrent parses never contend or leak — the exact failure mode a static/ambient counter
        // risks. Every parallel parse must observe the SAME small linear count for the same source.
        var source = DistinctFamily(500);
        var counts = new long[32];

        Parallel.For(0, counts.Length, i =>
        {
            var observations = new PatternComparisonObservations();
            _ = Parser.ParseSyntax(source, observations);
            counts[i] = observations.MatchEquivalenceComparisonCount;
        });

        Assert.All(counts, count => Assert.True(count <= 3L * 500, $"a concurrent parse observed {count} comparisons"));
    }

    private static string DistinctFamily(int n)
    {
        var sb = new StringBuilder(n * 12);
        for (var i = 0; i < n; i++)
            sb.Append("F(").Append(i).Append(") = ").Append(i).Append('\n');
        return sb.Append("F(0)").ToString();
    }
}
