using System.Text;
using System.Numerics;
using System.Threading.Tasks;

namespace KatLang.Tests;

/// <summary>
/// Regression coverage for conditional clause-family duplicate/equivalence matching. A same-name
/// clause group <c>F(p0) = ... F(pK) = ...</c> must reject a branch whose pattern is match-equivalent
/// to an earlier one (<see cref="Pattern.IsMatchEquivalent"/> — spelling-independent, but repeated
/// binder positions must agree). That check was an all-pairs scan: inserting the k-th clause compared
/// it against all k-1 earlier clauses, so a family of C clauses did O(C^2) exact comparisons both at
/// parse time (the insert scan) and at evaluation time (<see cref="Algorithm.Conditional.HasDuplicateBranchPatterns"/>).
/// Both checks now go through <see cref="PatternMatchEquivalenceIndex"/>: exact canonical keys (equal
/// exactly when the patterns are match-equivalent) in a balanced ordered set, O(S log C) for C literal
/// clauses of total key size S; binder numbering adds O(T log(B + 1)) for T name units and at most B
/// names/head (SEC-03 replaced a hashed set whose deterministic fingerprint
/// let colliding literals force all-pairs work; see <see cref="ClauseFamilyCollisionSecurityTests"/>),
/// preserving branch order, the duplicate diagnostics, and their order/spans.
///
/// <para>These tests pin (a) the equivalence SEMANTICS across the pattern kinds it distinguishes,
/// (b) the diagnostics and their order, and (c) the near-linear growth of the duplicate-detection work.
/// The work is measured through a passive OPERATION-SCOPED <see cref="PatternComparisonObservations"/>
/// passed to the family indexes of one parse (no static state, no reset): traversal, key writing/copying,
/// binder names and both indexes' comparison units. A separate allocation-ratio guard is
/// design-independent and fails under the old all-pairs implementation even though that implementation
/// would bypass the observed index entirely.</para>
/// </summary>
public class ClauseFamilyScalabilityTests
{
    private static Decimal128[] Atoms(string source) => KatLangEngine.EvaluateToAtoms(source).ToArray();

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

        var lines = duplicates.Select(d => Assert.NotNull(d.Span).Start.Line).ToList();
        Assert.Equal(lines.OrderBy(line => line).ToList(), lines); // strictly increasing (declaration order)
    }

    [Fact]
    public void DuplicateDiagnostic_CarriesTheDuplicateClauseSpan()
    {
        var duplicates = DuplicateBranchDiagnostics("F(0) = 1\nF(1) = 2\nF(0) = 3\nF(0)");
        var duplicate = Assert.Single(duplicates);
        Assert.Equal(3, Assert.NotNull(duplicate.Span).Start.Line); // the offending re-declaration, not the original
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

    // ───────────────────────── scaling regression: index work is O(S log N) ─────────────

    [Fact]
    public void DistinctClauseFamily_IndexWork_IsNearLinearNotQuadratic()
    {
        // A family of N DISTINCT literal clauses has no duplicates; every insertion builds one short key
        // and does O(log N) ordinal comparisons each bounded by that key's length. Assert the claimed
        // O(S log N) bound with a generous constant: an all-pairs scan would examine ~N^2/2 keys.
        const int n = 3000;
        var observations = MeasureIndexWork(n);
        var log2N = Math.Log2(n);

        Assert.Equal(n, observations.CanonicalKeyCount);
        Assert.True(
            observations.TotalIndexWork <= 2.0 * observations.CanonicalKeyUnits * (log2N + 2),
            $"clause-family duplicate detection did {observations.TotalIndexWork} work units for {n} distinct clauses " +
            $"of total key size {observations.CanonicalKeyUnits} (expected O(S log N)); " +
            $"{observations.KeyComparisonCount} key comparisons, an all-pairs scan would do ~{(long)n * (n - 1) / 2}.");
        Assert.True(observations.KeyComparisonCount <= (long)(2 * n * (log2N + 2)), $"{observations.KeyComparisonCount} key comparisons");
    }

    [Fact]
    public void IndexWork_GrowsNearLinearlyWhenClauseCountDoubles()
    {
        // Growth form: doubling the clause count must not roughly quadruple the index work. O(N log N)
        // gives ~2.2x here; an all-pairs scan gives ~4x.
        var atN = MeasureIndexWork(1500).TotalIndexWork;
        var at2N = MeasureIndexWork(3000).TotalIndexWork;

        var ratio = (double)at2N / atN;
        Assert.True(ratio < 2.6, $"index work grew {ratio:F2}x when the clause count doubled (N={atN}, 2N={at2N}).");
    }

    private static PatternComparisonObservations MeasureIndexWork(int n)
    {
        // A fresh observer belongs to this one parse; nothing crosses parses or threads.
        var observations = new PatternComparisonObservations();
        _ = Parser.ParseSyntax(DistinctFamily(n), observations);
        return observations;
    }

    [Fact]
    public void ParseAllocation_GrowsLinearlyInClauseCount()
    {
        // Design-independent scaling guard that fails under the old all-pairs implementation regardless
        // of where comparisons are counted. Parse allocation for 2N distinct clauses must grow only a
        // small linear factor over N. The old all-pairs duplicate scan allocated two dictionaries per
        // exact comparison and did ~C^2/2 comparisons, so its parse allocation was O(C^2) and doubling C
        // roughly quadrupled it (~4x); the ordered key index allocates one key and one tree node per
        // distinct clause, ~2x. Thread-local allocation is
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
    public void ConcurrentParses_ObserveIndependentIndexWork()
    {
        // Each parse owns its own PatternComparisonObservations, passed explicitly to its indexes, so
        // concurrent parses never contend or leak — the exact failure mode a static/ambient counter
        // risks. The index is deterministic, so every parallel parse must observe EXACTLY the work a
        // sequential parse of the same source observes.
        var source = DistinctFamily(500);
        var sequential = new PatternComparisonObservations();
        _ = Parser.ParseSyntax(source, sequential);
        var counts = new long[32];

        Parallel.For(0, counts.Length, i =>
        {
            var observations = new PatternComparisonObservations();
            _ = Parser.ParseSyntax(source, observations);
            counts[i] = observations.TotalIndexWork;
        });

        Assert.All(counts, count => Assert.Equal(sequential.TotalIndexWork, count));
    }

    private static string DistinctFamily(int n)
    {
        var sb = new StringBuilder(n * 12);
        for (var i = 0; i < n; i++)
            sb.Append("F(").Append(i).Append(") = ").Append(i).Append('\n');
        return sb.Append("F(0)").ToString();
    }
}
