using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace KatLang.Tests;

/// <summary>
/// SEC-03 regressions: clause-family duplicate detection must not be driven into quadratic work by
/// attacker-chosen literals. The retired index was a <c>HashSet&lt;Pattern&gt;</c> keyed by a
/// deterministic 32-bit FNV-1a structural fingerprint, so distinct string literals sharing one
/// fingerprint fell into one bucket and every insertion compared against all of them
/// (N(N-1)/2 exact comparisons, two dictionaries allocated per comparison). The replacement,
/// <see cref="PatternMatchEquivalenceIndex"/>, orders EXACT canonical keys in a balanced tree, so no
/// hash exists for an input to collide in. Literal-only families cost O(S log N) for N clauses of
/// total key size S; binder numbering adds O(T log(B + 1)) for T name units and at most B names/head.
/// There is therefore no hash seam to force (T1); the forced-collision workload is instead the
/// REAL historical fixture below, a deterministic set of 1024 distinct strings verified (by an
/// independent re-implementation of the retired fingerprint) to share one old fingerprint.
///
/// <para>Work is read from a passive, operation-scoped <see cref="PatternComparisonObservations"/>
/// (traversal, key writing/copying, binder names and both indexes' comparison units), never
/// from elapsed time. Cancellation is placed deterministically through the observer's checkpoint
/// hook.</para>
/// </summary>
public class ClauseFamilyCollisionSecurityTests
{
    // ───────────────────────── the historical collision fixture ─────────────────────────

    // Ten two-code-unit blocks, each with two alternatives; every choice of alternatives yields a
    // distinct 20-code-unit string, and all 1024 strings share ONE retired FNV-1a fingerprint as a
    // `F("...")` clause head (a LitString pattern). Found by a birthday search per block over the
    // retired fold's running state (a Joux-style multicollision). Code points, not literals, so no
    // editor or escape decoding can alter them.
    private static readonly (int[] First, int[] Second)[] CollisionBlocks = BuildCollisionBlocks();

    private static (int[] First, int[] Second)[] BuildCollisionBlocks()
    {
        var blocks = new (int[] First, int[] Second)[10];
        blocks[0] = ([0x9E5B, 0x4ED7], [0x62B6, 0x5000]);
        for (var i = 1; i < blocks.Length; i++)
            blocks[i] = ([0x9E23, 0x4ED7], [0x62CE, 0x5000]);
        return blocks;
    }

    private static string CollidingString(int selector)
    {
        var builder = new StringBuilder(2 * CollisionBlocks.Length);
        for (var i = 0; i < CollisionBlocks.Length; i++)
        {
            foreach (var codePoint in ((selector >> i) & 1) == 0 ? CollisionBlocks[i].First : CollisionBlocks[i].Second)
                builder.Append((char)codePoint);
        }
        return builder.ToString();
    }

    /// <summary>
    /// An independent re-implementation of the RETIRED clause-family fingerprint (32-bit FNV-1a over
    /// type tags, counts, literal values, and first-occurrence binder numbers), used only to prove the
    /// fixture really collides under it.
    /// </summary>
    private static uint RetiredFingerprint(Pattern pattern)
    {
        var hash = 2166136261u;
        var firstOccurrence = new Dictionary<string, int>(StringComparer.Ordinal);

        void Mix(uint value)
        {
            for (var shift = 0; shift < 32; shift += 8)
                hash = (hash ^ ((value >> shift) & 0xFF)) * 16777619u;
        }

        void Visit(Pattern node)
        {
            switch (node)
            {
                case Pattern.Bind bind:
                    Mix(1);
                    if (!firstOccurrence.TryGetValue(bind.Name, out var index))
                        firstOccurrence[bind.Name] = index = firstOccurrence.Count;
                    Mix((uint)index);
                    break;
                case Pattern.LitInt litInt:
                    Mix(2);
                    Mix(unchecked((uint)litInt.Value.GetHashCode()));
                    break;
                case Pattern.LitString litString:
                    Mix(3);
                    Mix((uint)litString.Value.Length);
                    foreach (var ch in litString.Value)
                        Mix(ch);
                    break;
                case Pattern.LitBool litBool:
                    Mix(5);
                    Mix(litBool.Value ? 1u : 0u);
                    break;
                case Pattern.SequenceValue sequence:
                    Mix(4);
                    Mix((uint)sequence.Items.Count);
                    foreach (var item in sequence.Items)
                        Visit(item);
                    break;
                case Pattern.ListValue list:
                    Mix(6);
                    Mix((uint)list.Items.Count);
                    foreach (var item in list.Items)
                        Visit(item);
                    break;
            }
        }

        Visit(pattern);
        return hash;
    }

    private static string CollidingFamily(int count, int duplicatesEvery = 0)
    {
        var builder = new StringBuilder();
        for (var i = 0; i < count; i++)
        {
            builder.Append("F(\"").Append(CollidingString(i)).Append("\") = ").Append(i).Append('\n');
            if (duplicatesEvery > 0 && i % duplicatesEvery == duplicatesEvery - 1)
                builder.Append("F(\"").Append(CollidingString(i / 2)).Append("\") = 0\n");
        }
        return builder.Append("F(1)").ToString();
    }

    private static PatternComparisonObservations ObserveParse(string source)
    {
        var observations = new PatternComparisonObservations();
        _ = Parser.ParseSyntax(source, observations);
        return observations;
    }

    private static List<(DiagnosticCode Code, string Message, SourceSpan? Span)> Triples(SyntaxParseResult result)
        => result.Diagnostics.Select(d => (d.Code, d.Message, d.Span)).ToList();

    private static List<(DiagnosticCode Code, string Message, SourceSpan? Span)> Triples(ParseResult result)
        => result.Diagnostics.Select(d => (d.Code, d.Message, d.Span)).ToList();

    [Fact]
    public void HistoricalFixture_IsDistinctStrings_SharingOneRetiredFingerprint()
    {
        var strings = Enumerable.Range(0, 1024).Select(CollidingString).ToList();
        Assert.Equal(1024, strings.Distinct(StringComparer.Ordinal).Count());
        Assert.All(strings, s => Assert.Equal(20, s.Length));

        var fingerprints = strings.Select(s => RetiredFingerprint(new Pattern.LitString(s))).Distinct().ToList();
        Assert.Single(fingerprints);

        // The parser really produces a LitString head for `F("...")`, the shape fingerprinted above.
        var parsed = Parser.ParseSyntax(CollidingFamily(4));
        Assert.False(parsed.HasErrors);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        Assert.All(family.Branches, branch => Assert.IsType<Pattern.LitString>(branch.Pattern));

        // Control: the fingerprint re-implementation is not trivially constant.
        Assert.NotEqual(
            RetiredFingerprint(new Pattern.LitString("a")),
            RetiredFingerprint(new Pattern.LitString("b")));
    }

    // ───────────────────────── T1/T2/T3 — bounded work under collisions ─────────────────────────

    [Fact]
    public void CollidingFamily_IsClassifiedExactly_WithinTheOrderedIndexBound()
    {
        const int n = 1024;
        var result = Parser.ParseSyntax(CollidingFamily(n));
        Assert.DoesNotContain(result.Diagnostics, d => d.Code == DiagnosticCode.DuplicateBranchPattern);

        var observations = ObserveParse(CollidingFamily(n));
        var log2N = Math.Log2(n);
        Assert.Equal(n, observations.CanonicalKeyCount);
        Assert.True(
            observations.KeyComparisonCount <= (long)(2 * n * (log2N + 2)),
            $"{observations.KeyComparisonCount} key comparisons for {n} colliding clauses (retired index: ~{(long)n * (n - 1) / 2}).");
        Assert.True(
            observations.TotalIndexWork <= 2.0 * observations.CanonicalKeyUnits * (log2N + 2),
            $"index work {observations.TotalIndexWork} exceeds O(S log N) for S={observations.CanonicalKeyUnits}.");
    }

    [Fact]
    public void CollidingFamily_WithInterleavedDuplicates_ReportsExactlyTheLaterClauses()
    {
        // Every 8th clause is followed by a re-declaration of an earlier colliding string; each one is
        // reported, on its own clause, in written order, and nothing else is.
        var source = CollidingFamily(256, duplicatesEvery: 8);
        var duplicates = Parser.ParseSyntax(source).Diagnostics
            .Where(d => d.Code == DiagnosticCode.DuplicateBranchPattern)
            .ToList();
        Assert.Equal(32, duplicates.Count);
        var lines = duplicates.Select(d => Assert.NotNull(d.Span).Start.Line).ToList();
        Assert.Equal(Enumerable.Range(1, 32).Select(k => 9 * k).ToList(), lines);
        Assert.All(duplicates, d => Assert.Equal("Duplicate branch pattern for conditional algorithm 'F'.", d.Message));
    }

    [Fact]
    public void CollidingFamily_TotalIndexWork_DoesNotQuadrupleWhenClauseCountDoubles()
    {
        // All of canonicalization and every key comparison is counted, not just exact equality calls.
        var atN = ObserveParse(CollidingFamily(512)).TotalIndexWork;
        var at2N = ObserveParse(CollidingFamily(1024)).TotalIndexWork;
        var ratio = (double)at2N / atN;
        Assert.True(ratio < 2.6, $"colliding-family index work grew {ratio:F2}x when N doubled (N={atN}, 2N={at2N}); quadratic is ~4x.");
    }

    // ───────────────────────── T4 — allocation growth ─────────────────────────

    [Fact]
    public void BinderNumbering_WorkIncludesLongNames_AndDoesNotRetainAWideHashTable()
    {
        static PatternComparisonObservations Observe(int count)
        {
            var observations = new PatternComparisonObservations();
            var index = new PatternMatchEquivalenceIndex(observations);
            var prefix = new string('a', 64);
            var wide = Enumerable.Range(0, count).Select(i => B(prefix + i.ToString("D5"))).ToArray();
            Assert.True(index.TryAdd(Seq(wide)));
            // The first small head materializes the pending wide head; all later heads have one
            // binder. A reused hash map's large bucket array must not be cleared once per head.
            for (var i = 0; i < count; i++)
                Assert.True(index.TryAdd(Seq(B("x"), I(i))));
            Assert.Equal(count + 1, observations.CanonicalKeyCount);
            Assert.Equal(observations.CanonicalKeyUnits, observations.KeyCopyUnits);
            Assert.Equal((long)count * (prefix.Length + 6), observations.BinderNameUnits);
            Assert.True(observations.BinderComparisonCount > count);
            var size = observations.CanonicalKeyUnits + observations.BinderNameUnits;
            Assert.True(observations.TotalIndexWork < 8 * size * (Math.Log2(count + 1) + 2));
            return observations;
        }

        var small = Observe(512);
        var large = Observe(1024);
        Assert.True((double)large.TotalIndexWork / small.TotalIndexWork < 2.8);
    }

    [Fact]
    public void CollidingFamily_ParseAllocation_GrowsLinearly()
    {
        // The retired index allocated two dictionaries per exact comparison: ~22 MB at 512 and ~86 MB
        // at 1024 colliding clauses (3.9x). The ordered index allocates one key and one node per clause.
        var small = CollidingFamily(512);
        var large = CollidingFamily(1024);
        _ = Parser.ParseSyntax(small);
        _ = Parser.ParseSyntax(large);

        var smallBytes = MeasureAllocation(small);
        var largeBytes = MeasureAllocation(large);
        var ratio = (double)largeBytes / smallBytes;
        Assert.True(ratio < 3.0, $"parse allocation grew {ratio:F2}x for 2N colliding clauses ({smallBytes} -> {largeBytes} bytes).");
        Assert.True(largeBytes < 16L * 1024 * 1024, $"1024 colliding clauses allocated {largeBytes} bytes.");
    }

    private static long MeasureAllocation(string source)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        _ = Parser.ParseSyntax(source);
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    // ───────────────────────── T5/T6/T7 — exact equivalence ─────────────────────────

    private static Pattern B(string name) => new Pattern.Bind(name);
    private static Pattern I(Decimal128 value) => new Pattern.LitInt(value);
    private static Pattern S(string value) => new Pattern.LitString(value);
    private static Pattern Seq(params Pattern[] items) => new Pattern.SequenceValue(items);
    private static Pattern List(params Pattern[] items) => new Pattern.ListValue(items);
    private static Decimal128 D(string text) => Decimal128.Parse(text, System.Globalization.CultureInfo.InvariantCulture);

    private static IReadOnlyList<Pattern> EquivalenceCorpus()
    {
        var decomposedE = new string(['e', (char)0x0301]);
        var precomposedE = new string([(char)0x00E9]);
        return
        [
            // binders: spelling, repetition, positions, parameter kind
            B("a"), B("b"), new Pattern.Bind("c") { ParameterKind = ParameterKind.Collecting },
            Seq(B("a"), B("a")), Seq(B("b"), B("b")), Seq(B("a"), B("b")), Seq(B("x"), B("y")), Seq(B("b"), B("a")),
            Seq(B("a"), B("b"), B("a")), Seq(B("a"), B("b"), B("b")), Seq(B("x"), B("y"), B("x")),
            Seq(B("a"), Seq(B("a"), B("b"))), Seq(B("b"), Seq(B("b"), B("a"))), Seq(B("a"), Seq(B("b"), B("a"))),
            // numbers: quantum, zero sign, NaN, infinities, subnormal extremes, distinct values
            I(D("1")), I(D("1.0")), I(D("1.00")), I(D("10")), I(D("1E+1")), I(D("100E-1")), I(D("0.1")), I(D("-1")),
            I(Decimal128.Zero), I(Decimal128.NegativeZero), I(D("0.000")), I(D("0E+5")),
            I(Decimal128.NaN), I(-Decimal128.NaN),
            I(Decimal128.PositiveInfinity), I(Decimal128.NegativeInfinity),
            I(Decimal128.MaxValue), I(Decimal128.MinValue), I(Decimal128.Epsilon), I(-Decimal128.Epsilon),
            I(D("123456789012345678901234567890123.4")), I(D("123456789012345678901234567890123.40")),
            // strings: ordinal, case, Unicode composition, digits vs numbers, length prefixes
            S(""), S("a"), S("A"), S("ab"), S("a;"), S("1"), S("true"), S(precomposedE), S(decomposedE),
            S("s1:a"), S(CollidingString(0)), S(CollidingString(1)),
            // Booleans vs numbers vs strings
            new Pattern.LitBool(true), new Pattern.LitBool(false),
            // structure: kind, cardinality, order, nesting, emptiness
            Seq(), List(), Seq(Seq()), List(List()), Seq(List()), List(Seq()),
            List(B("a")), List(B("b")), List(B("a"), B("a")), List(B("a"), B("b")),
            Seq(I(D("1")), B("x")), Seq(I(D("1.0")), B("y")), Seq(B("x"), I(D("1"))), List(I(D("1")), B("x")),
            Seq(Seq(I(D("0")), B("x")), List(B("y"), S("k"))), Seq(Seq(I(D("0.0")), B("p")), List(B("q"), S("k"))),
            Seq(Seq(I(D("0")), B("x")), List(B("x"), S("k"))), Seq(Seq(I(D("0")), B("x")), List(B("y"), S("K"))),
            Seq(Seq(I(D("0")), B("x")), List(B("y"), S("k"), S("k"))),
        ];
    }

    [Fact]
    public void CanonicalKeyEquality_IsExactlyMatchEquivalence_OverTheCorpus()
    {
        // The key's defining law, checked pairwise: CanonicalKey(a) == CanonicalKey(b) ⇔ a ≈ b. The
        // corpus covers binder renaming and repetition (T5), numeric/string/Boolean literals (T6), and
        // nested structures (T7), including every distinction the relation draws.
        var corpus = EquivalenceCorpus();
        var keys = corpus.Select(PatternMatchEquivalenceIndex.CanonicalKey).ToList();
        var equivalentPairs = 0;
        for (var i = 0; i < corpus.Count; i++)
        {
            for (var j = 0; j < corpus.Count; j++)
            {
                var equivalent = corpus[i].IsMatchEquivalent(corpus[j]);
                Assert.True(
                    equivalent == string.Equals(keys[i], keys[j], StringComparison.Ordinal),
                    $"pattern {i} vs {j}: IsMatchEquivalent={equivalent}, keys '{keys[i]}' / '{keys[j]}'");
                if (equivalent && i != j)
                    equivalentPairs++;
            }
        }

        // The corpus is not vacuous: it contains many non-identical equivalent pairs.
        Assert.True(equivalentPairs >= 30, $"only {equivalentPairs} equivalent pairs");
    }

    [Fact]
    public void Index_AgreesWithAllPairsOracle_InEveryInsertionOrder()
    {
        // For several deterministic orders of the corpus (which crosses the small-list → tree switch),
        // TryAdd must report a duplicate exactly when an earlier pattern is match-equivalent.
        var corpus = EquivalenceCorpus();
        var random = new Random(3);
        for (var round = 0; round < 12; round++)
        {
            var order = corpus.OrderBy(_ => random.Next()).ToList();
            var index = new PatternMatchEquivalenceIndex();
            for (var k = 0; k < order.Count; k++)
            {
                var expectedDistinct = !order.Take(k).Any(earlier => earlier.IsMatchEquivalent(order[k]));
                Assert.Equal(expectedDistinct, index.TryAdd(order[k]));
            }
        }
    }

    [Theory]
    [InlineData("F(a) = 1\nF(b) = 2\nF(1)", 1)]
    [InlineData("F(a, a) = 1\nF(b, b) = 2\nF(1, 1)", 1)]
    [InlineData("F(a, b) = 1\nF(x, y) = 2\nF(1, 2)", 1)]
    [InlineData("F(a, b) = 1\nF(b, a) = 2\nF(1, 2)", 1)]
    [InlineData("F(a, a) = 1\nF(a, b) = 2\nF(1, 2)", 0)]
    [InlineData("F(a, b, a) = 1\nF(a, b, b) = 2\nF(1, 2, 3)", 0)]
    [InlineData("F(1.5) = 1\nF(1.50) = 2\nF(1.5)", 1)]
    [InlineData("F(10) = 1\nF(10.0) = 2\nF(10)", 1)]
    [InlineData("F(1) = 1\nF(2) = 2\nF(1)", 0)]
    [InlineData("F(\"a\") = 1\nF(\"a\") = 2\nF(1)", 1)]
    [InlineData("F(\"a\") = 1\nF(\"A\") = 2\nF(1)", 0)]
    [InlineData("F(true) = 1\nF(true) = 2\nF(true)", 1)]
    [InlineData("F(true) = 1\nF(false) = 2\nF(true)", 0)]
    [InlineData("F(1) = 1\nF(true) = 2\nF(\"1\") = 3\nF(1)", 0)]
    [InlineData("F((x, [y, 1])) = 1\nF((p, [q, 1.0])) = 2\nF(1)", 1)]
    [InlineData("F((x, y)) = 1\nF([x, y]) = 2\nF(1)", 0)]
    [InlineData("F((x, y)) = 1\nF((x, y, z)) = 2\nF(1)", 0)]
    [InlineData("F([]) = 1\nF([]) = 2\nF(1)", 1)]
    [InlineData("F([]) = 1\nF(()) = 2\nF(1)", 0)]
    public void SourceFamilies_ReportDuplicatesExactly(string source, int expectedDuplicates)
        => Assert.Equal(
            expectedDuplicates,
            Parser.ParseSyntax(source).Diagnostics.Count(d => d.Code == DiagnosticCode.DuplicateBranchPattern));

    [Fact]
    public void UnicodeStringLiterals_AreComparedOrdinally_WithoutNormalization()
    {
        var precomposed = new string([(char)0x00E9]);
        var decomposed = new string(['e', (char)0x0301]);
        var distinct = $"F(\"{precomposed}\") = 1\nF(\"{decomposed}\") = 2\nF(1)";
        Assert.DoesNotContain(Parser.ParseSyntax(distinct).Diagnostics, d => d.Code == DiagnosticCode.DuplicateBranchPattern);
        var same = $"F(\"{decomposed}\") = 1\nF(\"{decomposed}\") = 2\nF(1)";
        Assert.Single(Parser.ParseSyntax(same).Diagnostics, d => d.Code == DiagnosticCode.DuplicateBranchPattern);
    }

    [Fact]
    public void DeeplyNestedValidPatterns_AreIndexedExactly()
    {
        // Deep but parser-admissible nesting through source, and far deeper host-built nesting through
        // the iterative key builder (no recursion on the caller's stack).
        static string Nested(int depth, string leaf)
        {
            var builder = new StringBuilder();
            for (var i = 0; i < depth; i++) builder.Append('(');
            builder.Append(leaf);
            for (var i = 0; i < depth; i++) builder.Append(", ").Append(i).Append(')');
            return builder.ToString();
        }

        var source = $"F({Nested(40, "a, 0")}) = 1\nF({Nested(40, "b, 0")}) = 2\nF({Nested(40, "b, 1")}) = 3\nF(1)";
        var result = Parser.ParseSyntax(source);
        Assert.DoesNotContain(result.Diagnostics, d => d.Code is DiagnosticCode.NestingTooDeep);
        Assert.Single(result.Diagnostics, d => d.Code == DiagnosticCode.DuplicateBranchPattern);

        Pattern deep = B("x");
        Pattern deepRenamed = B("y");
        Pattern deepOther = I(D("1"));
        for (var i = 0; i < 100_000; i++)
        {
            deep = Seq(deep, I(D("0")));
            deepRenamed = Seq(deepRenamed, I(D("0.0")));
            deepOther = Seq(deepOther, I(D("0")));
        }

        var index = new PatternMatchEquivalenceIndex();
        Assert.True(index.TryAdd(deep));
        Assert.True(index.TryAdd(deepOther));
        Assert.False(index.TryAdd(deepRenamed));
    }

    // ───────────────────────── T8/T9 — diagnostics, order, recovery ─────────────────────────

    [Fact]
    public void InterleavedFamilies_KeepExactDiagnosticsAndFirstSeenOrder()
    {
        const string source =
            "Z(0) = 0\nA(\"x\") = 1\nZ(1) = 1\nA(\"y\") = 2\nZ(0) = 9\nM(a, a) = 0\nA(\"x\") = 3\n" +
            "M(b, c) = 1\nZ(2) = 2\nM(q, q) = 2\nA(\"z\") = 4\nZ(1.0) = 5\nZ(1), A(\"x\"), M(1, 1)";
        var result = Parser.ParseSyntax(source);
        Assert.Equal(
            [
                (DiagnosticCode.DuplicateBranchPattern, "Duplicate branch pattern for conditional algorithm 'Z'.", (SourceSpan?)new SourceSpan(5, 1, 5, 9)),
                (DiagnosticCode.DuplicateBranchPattern, "Duplicate branch pattern for conditional algorithm 'A'.", (SourceSpan?)new SourceSpan(7, 1, 7, 11)),
                (DiagnosticCode.DuplicateBranchPattern, "Duplicate branch pattern for conditional algorithm 'M'.", (SourceSpan?)new SourceSpan(10, 1, 10, 12)),
                (DiagnosticCode.DuplicateBranchPattern, "Duplicate branch pattern for conditional algorithm 'Z'.", (SourceSpan?)new SourceSpan(12, 1, 12, 11)),
            ],
            Triples(result));

        // Families keep first-seen order and every written clause, in written order.
        var families = result.Root.Properties.Select(p => (p.Name, Assert.IsType<Algorithm.Conditional>(p.Value).Branches.Count)).ToList();
        Assert.Equal([("Z", 5), ("A", 4), ("M", 3)], families);
    }

    [Fact]
    public void RecoveredHeads_AreNotIndexed_AndDoNotSuppressLaterDuplicates()
    {
        // `F(x +)` needs recovery: it is kept in the family but takes part in no duplicate check, so
        // the clean `F(x)` after it is NOT its duplicate, while `F(y)` IS a duplicate of `F(x)`.
        const string source = "F(x +) = 0\nF(x) = 1\nF(0) = 2\nF(y) = 3\nF(1)";
        var result = Parser.ParseSyntax(source);
        var duplicates = result.Diagnostics.Where(d => d.Code == DiagnosticCode.DuplicateBranchPattern).ToList();
        var duplicate = Assert.Single(duplicates);
        Assert.Equal(4, Assert.NotNull(duplicate.Span).Start.Line);

        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(result.Root.Properties).Value);
        Assert.Equal(4, family.Branches.Count);
        Assert.Equal([true, false, false, false], family.Branches.Select(b => b.HasRecoveredHead).ToList());

        // Two recovered heads never report each other either.
        var twoRecovered = Parser.ParseSyntax("F(x +) = 0\nF(x +) = 1\nF(1)");
        Assert.DoesNotContain(twoRecovered.Diagnostics, d => d.Code == DiagnosticCode.DuplicateBranchPattern);

        // The recovery diagnostics precede the duplicate in written order, unchanged.
        var codes = result.Diagnostics.Select(d => d.Code).ToList();
        Assert.True(codes.IndexOf(DiagnosticCode.DuplicateBranchPattern) > 0);
    }

    // ───────────────────────── T10 — cancellation ─────────────────────────

    [Fact]
    public void AlreadyCancelledToken_StopsTheFirstIndexedClause()
    {
        using var source = new CancellationTokenSource();
        source.Cancel();
        var observations = new PatternComparisonObservations();
        var exception = Assert.ThrowsAny<OperationCanceledException>(
            () => Parser.ParseSyntax(CollidingFamily(16), observations, cancellationToken: source.Token));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(1, observations.CancellationCheckpointCount);
    }

    [Fact]
    public void CancellationRequestedInsideDuplicateDetection_StopsAtThatCheckpoint()
    {
        using var source = new CancellationTokenSource();
        var observations = new PatternComparisonObservations
        {
            CheckpointReached = count =>
            {
                if (count == 300)
                    source.Cancel();
            },
        };

        var exception = Assert.ThrowsAny<OperationCanceledException>(
            () => Parser.ParseSyntax(CollidingFamily(1024), observations, cancellationToken: source.Token));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(300, observations.CancellationCheckpointCount);
        Assert.True(observations.CanonicalKeyCount < 300, $"{observations.CanonicalKeyCount} keys built");
    }

    [Fact]
    public void CancellationRequestedDuringOneLongCanonicalization_StopsInsideIt()
    {
        // Two clauses: the second head has 20,000 items, so its key spans many canonicalization blocks.
        // Checkpoints 1 and 2 are the two insertions; every later one is inside that key's construction.
        var head = string.Join(", ", Enumerable.Range(0, 20_000));
        var text = $"F(0) = 0\nF(({head})) = 1\nF(0)";
        using var source = new CancellationTokenSource();
        var observations = new PatternComparisonObservations
        {
            CheckpointReached = count =>
            {
                if (count == 5)
                    source.Cancel();
            },
        };

        var exception = Assert.ThrowsAny<OperationCanceledException>(
            () => Parser.ParseSyntax(text, observations, cancellationToken: source.Token));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(5, observations.CancellationCheckpointCount);
        Assert.Equal(1, observations.CanonicalKeyCount); // only F(0)'s key completed

        // Uncancelled, the same source completes and identically to the token-free parse.
        var live = new PatternComparisonObservations();
        using var never = new CancellationTokenSource();
        var completed = Parser.ParseSyntax(text, live, cancellationToken: never.Token);
        Assert.Equal(Triples(Parser.ParseSyntax(text)), Triples(completed));
        Assert.True(live.CancellationCheckpointCount > 2 + 20_000 * 3 / PatternMatchEquivalenceIndex.CanonicalizationCheckpointInterval);
    }

    [Fact]
    public void CancellationRequestedDuringOneLongString_StopsBeforeItsKeyCompletes()
    {
        var text = $"F(0) = 0\nF(\"{new string('a', 40_000)}\") = 1\nF(0)";
        using var source = new CancellationTokenSource();
        var observations = new PatternComparisonObservations
        {
            CheckpointReached = count =>
            {
                if (count == 5)
                    source.Cancel();
            },
        };

        var exception = Assert.ThrowsAny<OperationCanceledException>(
            () => Parser.ParseSyntax(text, observations, cancellationToken: source.Token));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(5, observations.CancellationCheckpointCount);
        Assert.Equal(1, observations.CanonicalKeyCount);
    }

    [Fact]
    public void CancellationRequestedDuringLongKeyComparison_StopsInsideTheComparison()
    {
        using var source = new CancellationTokenSource();
        PatternComparisonObservations observations = null!;
        observations = new PatternComparisonObservations
        {
            CheckpointReached = _ =>
            {
                if (observations.KeyComparisonCount != 0)
                    source.Cancel();
            },
        };
        var index = new PatternMatchEquivalenceIndex(observations);
        var prefix = new string('a', 40_000);
        Assert.True(index.TryAdd(S(prefix + "x"), source.Token));

        var exception = Assert.ThrowsAny<OperationCanceledException>(
            () => index.TryAdd(S(prefix + "y"), source.Token));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(2, observations.CanonicalKeyCount);
        Assert.Equal(1, observations.KeyComparisonCount);
    }

    [Fact]
    public void CancellationRequestedDuringLongBinderNameComparison_StopsInsideTheComparison()
    {
        using var source = new CancellationTokenSource();
        PatternComparisonObservations observations = null!;
        observations = new PatternComparisonObservations
        {
            CheckpointReached = _ =>
            {
                if (observations.BinderComparisonCount != 0)
                    source.Cancel();
            },
        };
        var index = new PatternMatchEquivalenceIndex(observations);
        var prefix = new string('a', 40_000);
        Assert.True(index.TryAdd(I(0), source.Token));
        var exception = Assert.ThrowsAny<OperationCanceledException>(
            () => index.TryAdd(Seq(B(prefix + "x"), B(prefix + "y")), source.Token));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(1, observations.CanonicalKeyCount);
        Assert.Equal(1, observations.BinderComparisonCount);
    }

    [Fact]
    public void CancellationRequestedDuringKeyMaterialization_StopsInsideTheCopy()
    {
        using var source = new CancellationTokenSource();
        PatternComparisonObservations observations = null!;
        observations = new PatternComparisonObservations
        {
            CheckpointReached = _ =>
            {
                // The pending numeric key is copied first; cancel when copying the long key.
                if (observations.KeyCopyUnits > 100)
                    source.Cancel();
            },
        };
        var index = new PatternMatchEquivalenceIndex(observations);
        Assert.True(index.TryAdd(I(0), source.Token));
        var exception = Assert.ThrowsAny<OperationCanceledException>(
            () => index.TryAdd(S(new string('a', 40_000)), source.Token));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(1, observations.CanonicalKeyCount);
        Assert.InRange(observations.KeyCopyUnits, 101, 8192);
    }

    [Fact]
    public void ConfiguredSourceProcessingToken_ReachesDuplicateDetection_SyncAndAsync()
    {
        var text = CollidingFamily(256);
        foreach (var asynchronous in new[] { false, true })
        {
            using var source = new CancellationTokenSource();
            var observations = new PatternComparisonObservations
            {
                CheckpointReached = count =>
                {
                    if (count == 50)
                        source.Cancel();
                },
            };
            var options = new RunOptions { SourceProcessingCancellationToken = source.Token };

            var exception = Assert.ThrowsAny<OperationCanceledException>(() =>
            {
                if (asynchronous)
                    FrontEndPipeline.ProcessAsync(text, options, observations).AsTask().GetAwaiter().GetResult();
                else
                    FrontEndPipeline.Process(text, options, observations);
            });
            Assert.Equal(source.Token, exception.CancellationToken);
            Assert.Equal(50, observations.CancellationCheckpointCount);
        }
    }

    [Fact]
    public async Task ConfiguredSourceProcessingToken_ReachesModuleParseDuplicateDetection()
    {
        // The main program has no clause family, so every checkpoint belongs to the module's parse.
        var module = CollidingFamily(256).Replace("F(1)", "public G = 1", StringComparison.Ordinal);
        using var source = new CancellationTokenSource();
        var downloads = 0;
        var observations = new PatternComparisonObservations
        {
            CheckpointReached = count =>
            {
                if (count == 40)
                    source.Cancel();
            },
        };
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = source.Token,
            DownloadCode = (_, _) =>
            {
                downloads++;
                return ValueTask.FromResult(module);
            },
        };

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            async () => await FrontEndPipeline.ProcessAsync("public M = load('https://katlang.org/m.kat')\nM.G", options, observations));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(1, downloads);
        Assert.Equal(40, observations.CancellationCheckpointCount);
    }

    [Fact]
    public void ModuleLoaderParse_ObservesTheConfiguredTokenFirst()
    {
        var module = CollidingFamily(64).Replace("F(1)", "public G = 1", StringComparison.Ordinal);
        using var source = new CancellationTokenSource();
        var loader = new ModuleLoader(
            new DiagnosticBag(),
            (_, _) => ValueTask.FromResult(module),
            allowedHosts: null,
            sourceProcessingCancellationToken: source.Token)
        {
            ComparisonObservations = new PatternComparisonObservations
            {
                CheckpointReached = count =>
                {
                    if (count == 10)
                        source.Cancel();
                },
            },
        };
        var syntax = Parser.ParseSyntax("public M = load('https://katlang.org/m.kat')\nM.G");
        Assert.False(syntax.HasErrors);
        var root = syntax.Root;

        var exception = Assert.ThrowsAny<OperationCanceledException>(
            () => loader.ElaborateAsync(root).AsTask().GetAwaiter().GetResult());
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(10, loader.ComparisonObservations.CancellationCheckpointCount);
    }

    [Fact]
    public async Task DeferredModuleMaterialization_ObservesCancellationInsideDuplicateDetection()
    {
        using var source = new CancellationTokenSource();
        var downloads = 0;
        var observations = new PatternComparisonObservations
        {
            CheckpointReached = count =>
            {
                if (downloads != 0 && count >= 40)
                    source.Cancel();
            },
        };
        var module = CollidingFamily(256).Replace("F(1)", "public G = 1", StringComparison.Ordinal);
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = source.Token,
            DownloadCode = (_, _) =>
            {
                downloads++;
                return ValueTask.FromResult(module);
            },
        };
        const string text = "F(0) = 42\nF(n) = { open 'https://katlang.org/deferred.kat'\nG }\nF(0)";
        var frontEnd = await FrontEndPipeline.ProcessAsync(text, options, observations);
        Assert.False(frontEnd.HasErrors, string.Join("\n", frontEnd.Diagnostics));
        Assert.True(frontEnd.HasDeferredModuleRegions);
        Assert.Equal(0, downloads);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(frontEnd.ElaboratedRoot.Properties).Value);
        var region = Assert.IsType<DeferredModuleRegion>(family.Branches[1].Body.DeferredRegion);

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            async () => await region.MaterializeAsync(CancellationToken.None));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(1, downloads);
        Assert.Equal(40, observations.CancellationCheckpointCount);
        Assert.False(region.TryGetMaterialized(out _));
    }

    [Fact]
    public void ConcurrentParses_WithIndependentTokens_CancelIndependently()
    {
        var text = CollidingFamily(256, duplicatesEvery: 16);
        var expected = Triples(Parser.ParseSyntax(text));
        var outcomes = new string[16];

        Parallel.For(0, outcomes.Length, i =>
        {
            using var source = new CancellationTokenSource();
            var cancelThisOne = i % 2 == 0;
            var observations = new PatternComparisonObservations
            {
                CheckpointReached = count =>
                {
                    if (cancelThisOne && count == 20 + i)
                        source.Cancel();
                },
            };
            try
            {
                var result = Parser.ParseSyntax(text, observations, cancellationToken: source.Token);
                outcomes[i] = !cancelThisOne && Triples(result).SequenceEqual(expected) ? "completed" : "WRONG";
            }
            catch (OperationCanceledException exception) when (exception.CancellationToken == source.Token)
            {
                outcomes[i] = cancelThisOne && observations.CancellationCheckpointCount == 20 + i ? "cancelled" : "WRONG";
            }
        });

        Assert.Equal(
            Enumerable.Range(0, outcomes.Length).Select(i => i % 2 == 0 ? "cancelled" : "completed").ToList(),
            outcomes.ToList());
    }

    // ───────────────────────── T11 — runtime duplicate-branch guard ─────────────────────────

    private static Algorithm.User Body(int value)
        => new(Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: [new Expr.Num(value)]);

    private static Algorithm.Conditional CollidingConditional(int count, bool withDuplicate)
    {
        var branches = Enumerable.Range(0, count)
            .Select(i => new CondBranch(new Pattern.LitString(CollidingString(i)), Body(i)))
            .ToList();
        if (withDuplicate)
            branches.Add(new CondBranch(new Pattern.LitString(CollidingString(count / 3)), Body(-1)));
        return new Algorithm.Conditional(Parent: null, Opens: [], Branches: branches);
    }

    private static EvalResult<IReadOnlyList<Decimal128>> CallWithString(Algorithm.Conditional family, string argument)
    {
        var root = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: [new Property("F", family, IsPublic: true)],
            Output: [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.StringLiteral(argument)]))]);
        return Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
    }

    [Fact]
    public void RuntimeGuard_OnHostBuiltCollidingFamilies_AcceptsDistinctAndRejectsDuplicates()
    {
        var distinct = CollidingConditional(512, withDuplicate: false);
        Assert.False(distinct.HasDuplicateBranchPatterns());
        var call = CallWithString(distinct, CollidingString(300));
        Assert.False(call.IsError, call.IsError ? call.Error.ToString() : null);
        Assert.Equal((Decimal128)300, Assert.Single(call.Value));

        var duplicated = CollidingConditional(512, withDuplicate: true);
        Assert.True(duplicated.HasDuplicateBranchPatterns());
        var rejected = CallWithString(duplicated, CollidingString(1));
        Assert.True(rejected.IsError);
        var error = rejected.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        Assert.IsType<EvalError.DuplicateBranchPattern>(error);
    }

    [Fact]
    public void RuntimeGuard_WorkAndAllocation_StayNearLinearUnderCollisions()
    {
        // The guard shares the parser's index; observe the same index over the same branch sequence.
        static PatternComparisonObservations Observe(Algorithm.Conditional family)
        {
            var observations = new PatternComparisonObservations();
            var index = new PatternMatchEquivalenceIndex(observations);
            foreach (var branch in family.Branches)
                index.TryAdd(branch.Pattern);
            return observations;
        }

        var small = CollidingConditional(512, withDuplicate: false);
        var large = CollidingConditional(1024, withDuplicate: false);
        var workRatio = (double)Observe(large).TotalIndexWork / Observe(small).TotalIndexWork;
        Assert.True(workRatio < 2.6, $"guard index work grew {workRatio:F2}x when N doubled");

        _ = small.HasDuplicateBranchPatterns();
        _ = large.HasDuplicateBranchPatterns();
        var before = GC.GetAllocatedBytesForCurrentThread();
        _ = small.HasDuplicateBranchPatterns();
        var smallBytes = GC.GetAllocatedBytesForCurrentThread() - before;
        before = GC.GetAllocatedBytesForCurrentThread();
        _ = large.HasDuplicateBranchPatterns();
        var largeBytes = GC.GetAllocatedBytesForCurrentThread() - before;
        var allocationRatio = (double)largeBytes / smallBytes;
        Assert.True(allocationRatio < 3.0, $"guard allocation grew {allocationRatio:F2}x ({smallBytes} -> {largeBytes} bytes)");
        Assert.True(largeBytes < 1024 * 1024, $"guard over 1024 colliding branches allocated {largeBytes} bytes (retired index: ~84 MB)");
    }

    // ───────────────────────── T12 — parallel parse isolation ─────────────────────────

    [Fact]
    public void ParallelParses_OfTheSameSource_ProduceIdenticalTreesAndDiagnostics()
    {
        var text = CollidingFamily(256, duplicatesEvery: 7);
        static string Fingerprint(SyntaxParseResult result)
        {
            var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(result.Root.Properties).Value);
            return string.Join(
                "\n",
                family.Branches.Select(b => LeanAstEncoder.EncodePattern(b.Pattern) + "|" + b.HasRecoveredHead));
        }

        var expectedResult = Parser.ParseSyntax(text);
        var expectedTree = Fingerprint(expectedResult);
        var expectedDiagnostics = Triples(expectedResult);
        var observedWork = ObserveParse(text).TotalIndexWork;
        var mismatches = 0;

        Parallel.For(0, 24, _ =>
        {
            var observations = new PatternComparisonObservations();
            var result = Parser.ParseSyntax(text, observations);
            if (Fingerprint(result) != expectedTree
                || !Triples(result).SequenceEqual(expectedDiagnostics)
                || observations.TotalIndexWork != observedWork)
            {
                Interlocked.Increment(ref mismatches);
            }
        });

        Assert.Equal(0, mismatches);
    }
}
