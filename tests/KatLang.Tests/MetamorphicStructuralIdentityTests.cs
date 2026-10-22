using System.Globalization;
using System.Numerics;
using System.Text;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// SEM-2A: the metamorphic comparator's structural-value identity.
///
/// <para>The legacy neutral encoding (<see cref="MetamorphicValue.Neutral"/>, mirrored by
/// <c>SemanticExplorerHarness.Neutral</c> and frozen by FORMAL-06) is not injective, and the
/// comparator used to compare it as THE structural identity. These tests pin the original
/// collision, the typed <see cref="Result.ValueComparer"/> authority that replaced it, and the
/// supplementary versioned <c>kl-struct-v1</c> identity — through the real execution and
/// comparison path wherever a program can express the value.</para>
/// </summary>
public class MetamorphicStructuralIdentityTests
{
    /// <summary><c>["a', 'b", "c"]</c> — a list of TWO strings.</summary>
    private const string TwoStrings = "[\"a', 'b\", \"c\"]";

    /// <summary><c>["a", "b", "c"]</c> — a list of THREE strings.</summary>
    private const string ThreeStrings = "[\"a\", \"b\", \"c\"]";

    // ── T1: the original collision ───────────────────────────────────────────

    [Fact]
    public void T1_OriginalCollision_IsRejectedByTheRealComparisonPath()
    {
        var twoStrings = new Result.ListValue([new Result.Str("a', 'b"), new Result.Str("c")]);
        var threeStrings = new Result.ListValue([new Result.Str("a"), new Result.Str("b"), new Result.Str("c")]);

        // 1. The historical neutral text still collides, byte for byte, in both mirrors.
        Assert.Equal("L['a', 'b', 'c']", MetamorphicValue.Neutral(twoStrings));
        Assert.Equal(MetamorphicValue.Neutral(twoStrings), MetamorphicValue.Neutral(threeStrings));
        Assert.Equal(SemanticExplorerHarness.Neutral(twoStrings), SemanticExplorerHarness.Neutral(threeStrings));

        // 2. KatLang's structural equality distinguishes them.
        Assert.False(Result.ValueComparer.Equals(twoStrings, threeStrings));

        // 3. So does the durable identity.
        Assert.NotEqual(MetamorphicStructuralIdentity.Encode(twoStrings), MetamorphicStructuralIdentity.Encode(threeStrings));

        // 4. The real programs, executed and compared exactly as the fuzz target does.
        var testCase = CrossSourceCase(TwoStrings, ThreeStrings);
        var execution = MetamorphicExecutor.Execute(testCase);
        Assert.True(execution.Accepted, execution.RejectionReason);
        Assert.Equal(execution.Left!.Semantic.Structure, execution.Right!.Semantic.Structure);
        Assert.True(Result.ValueComparer.Equals(twoStrings, execution.Left.Semantic.Value!));
        Assert.True(Result.ValueComparer.Equals(threeStrings, execution.Right.Semantic.Value!));

        var mismatch = Require(MetamorphicComparator.Compare(testCase, execution.Left, execution.Right));
        Assert.Equal(MetamorphicMismatchKind.SemanticStructure, mismatch.Kind);
        Assert.Equal(MetamorphicMismatchClass.Semantic, mismatch.Class);
        Assert.Contains(MetamorphicStructuralIdentity.Version, mismatch.ComparedProperty, StringComparison.Ordinal);
        Assert.Contains("legacy neutral text is identical", mismatch.ComparedProperty, StringComparison.Ordinal);
        Assert.NotEqual(mismatch.LeftValue, mismatch.RightValue);

        // The pre-SEM-2A records have only the same neutral text and count: the old comparator
        // accepted them. They cannot establish equality and must now be refused. (This Phase 1
        // case also claims materialization equality, which happens
        // to differ for these two lists — 2 against 3 items — so the semantic verdict is isolated
        // by declaring no operational relation.)
        var semanticOnly = testCase with { OperationalRelation = MetamorphicOperationalRelation.NotCompared };
        var legacyLeft = execution.Left with { Semantic = Legacy(execution.Left.Semantic) };
        var legacyRight = execution.Right with { Semantic = Legacy(execution.Right.Semantic) };
        Assert.Throws<MetamorphicHarnessException>(() => MetamorphicComparator.Compare(semanticOnly, legacyLeft, legacyRight));
        Assert.Equal(
            MetamorphicMismatchKind.SemanticStructure,
            Require(MetamorphicComparator.Compare(semanticOnly, execution.Left, execution.Right)).Kind);
    }

    [Fact]
    public void T1_OriginalCollision_IsRejectedOnEverySharedStructureFacetAndUnderIsolation()
    {
        // Entry-point parity (shared facets) and run isolation compare structure through their own
        // paths; both must reject the colliding pair as well.
        var entry = MetamorphicFacetsCase(MetamorphicSemanticRelation.SameStructuredOutcome);
        var isolation = MetamorphicFacetsCase(MetamorphicSemanticRelation.IndependentRunStable);
        var left = ObserveThrough(MetamorphicSurface.EvaluatorRun, TwoStrings);
        var right = ObserveThrough(MetamorphicSurface.EvaluatorRun, ThreeStrings);

        Assert.Equal(MetamorphicMismatchKind.SemanticStructure, Require(MetamorphicComparator.Compare(entry, left, right)).Kind);
        var isolated = Require(MetamorphicComparator.Compare(isolation, left, right));
        Assert.Equal(MetamorphicMismatchKind.SemanticStructure, isolated.Kind);
        Assert.Equal(MetamorphicMismatchClass.StateIsolation, isolated.Class);

        // Record equality (replay determinism, bounded-parallel agreement) distinguishes them too.
        Assert.NotEqual(left.Semantic, right.Semantic);
    }

    // ── T2–T5: kinds, empties, order, nesting ────────────────────────────────

    [Fact]
    public void T2_T3_T4_T5_KindsEmptiesOrderAndNestingAreAllDistinct()
    {
        Result one = new Result.Atom(1m);
        Result two = new Result.Atom(2m);
        var values = new (string Name, Result Value)[]
        {
            ("1", one),
            ("true", new Result.Bool(true)),
            ("false", new Result.Bool(false)),
            ("'1'", new Result.Str("1")),
            ("'true'", new Result.Str("true")),
            ("''", new Result.Str("")),
            ("()", new Result.SequenceValue([])),
            ("[]", new Result.ListValue([])),
            ("[()]", new Result.ListValue([new Result.SequenceValue([])])),
            ("[[]]", new Result.ListValue([new Result.ListValue([])])),
            ("[[], []]", new Result.ListValue([new Result.ListValue([]), new Result.ListValue([])])),
            ("[[[]]]", new Result.ListValue([new Result.ListValue([new Result.ListValue([])])])),
            ("([])", new Result.SequenceValue([new Result.ListValue([])])),
            ("[1]", new Result.ListValue([one])),
            ("(1)", new Result.SequenceValue([one])),
            ("(1, 2)", new Result.SequenceValue([one, two])),
            ("[1, 2]", new Result.ListValue([one, two])),
            ("[2, 1]", new Result.ListValue([two, one])),
            ("[[1], 2]", new Result.ListValue([new Result.ListValue([one]), two])),
            ("[1, [2]]", new Result.ListValue([one, new Result.ListValue([two])])),
            ("[[1, 2]]", new Result.ListValue([new Result.ListValue([one, two])])),
            ("[(1, 2)]", new Result.ListValue([new Result.SequenceValue([one, two])])),
            ("['L[]']", new Result.ListValue([new Result.Str("L[]")])),
            ("[1, true]", new Result.ListValue([one, new Result.Bool(true)])),
            ("[true, 1]", new Result.ListValue([new Result.Bool(true), one])),
        };

        AssertPairwiseIdentityMatchesValueComparer(values);
        for (var i = 0; i < values.Length; i++)
        {
            for (var j = i + 1; j < values.Length; j++)
            {
                Assert.False(
                    Result.ValueComparer.Equals(values[i].Value, values[j].Value),
                    $"fixture '{values[i].Name}' and '{values[j].Name}' must be different values");
                Assert.False(
                    MetamorphicComparator.StructurallyEqual(Of(values[i].Value), Of(values[j].Value)),
                    $"comparator accepted '{values[i].Name}' against '{values[j].Name}'");
            }
        }
    }

    [Theory]
    [InlineData("[1, 2]", "1, 2")]
    [InlineData("[]", "[[]]")]
    [InlineData("[[]]", "[[], []]")]
    [InlineData("[1]", "1")]
    [InlineData("[1, 2]", "[2, 1]")]
    [InlineData("[[1], 2]", "[1, [2]]")]
    [InlineData("[1]", "[true]")]
    [InlineData("[\"1\"]", "[1]")]
    [InlineData("[\"true\"]", "[true]")]
    public void T2_T3_T4_T5_RealProgramsWithDifferentValuesAreRejectedThroughTheExecutor(string left, string right)
    {
        var testCase = CrossSourceCase(left, right);
        var execution = MetamorphicExecutor.Execute(testCase);
        Assert.True(execution.Accepted, execution.RejectionReason);
        Assert.Equal(
            MetamorphicMismatchKind.SemanticStructure,
            Require(MetamorphicComparator.Compare(testCase, execution.Left!, execution.Right!)).Kind);
    }

    // ── T6/T7: string delimiters and UTF-16 exactness ────────────────────────

    private static readonly string[] HostileStringValues =
    [
        "",
        "'",
        "\"",
        "\\",
        ",",
        "[",
        "]",
        "a', 'b",
        "L['a', 'b']",
        "S[]",
        "t3:abc",
        "n2:15e-1",
        "s0:;",
        "\\u0041",
        "\\\\u0041",
        "line\nbreak",
        "carriage\rreturn",
        "tab\there",
        "nul\0inside",
        "\u00E9\u4E2D\uFFFF",
        "\U0001F600",
        "\uD800",
        "\uDC00",
        "x\uDBFFy",
        "\uDC00\uD800",
        "kl-struct-v1:1:b1",
    ];

    // One fact, not a theory: xUnit derives a theory row's id from its serialized argument, and
    // lone surrogates serialize alike, so rows like "\uD800" and "\uDC00" would collapse into one.
    [Fact]
    public void T6_T7_EveryUtf16StringRoundTripsExactlyAndAsciiOnly()
    {
        foreach (var text in HostileStringValues) AssertRoundTripsExactlyAndAsciiOnly(text);
    }

    private static void AssertRoundTripsExactlyAndAsciiOnly(string text)
    {
        var value = new Result.ListValue([new Result.Str(text), new Result.Str(text + "|")]);
        var identity = MetamorphicStructuralIdentity.Encode(value);

        Assert.All(identity, unit => Assert.InRange(unit, ' ', '~'));
        Assert.True(MetamorphicStructuralIdentity.TryDecode(identity, out var decoded, out var problem), problem);
        var items = Assert.IsType<Result.ListValue>(decoded).Items;
        Assert.Equal(text, Assert.IsType<Result.Str>(items[0]).Value, StringComparer.Ordinal);
        Assert.Equal(text + "|", Assert.IsType<Result.Str>(items[1]).Value, StringComparer.Ordinal);

        // ASCII-only means a UTF-8 file round trip cannot touch it, lone surrogates included.
        Assert.Equal(identity, Encoding.UTF8.GetString(Encoding.UTF8.GetBytes(identity)));
    }

    [Fact]
    public void T6_T7_HostileStringsAreMutuallyDistinctAndDelimiterSplitsCannotCollide()
    {
        var strings = HostileStringValues;
        var values = strings.Select(text => ($"'{text}'", (Result)new Result.Str(text))).ToList();

        // Every way of cutting one text into list items is a different value with a different identity.
        foreach (var cut in new[] { "a', 'b', 'c", "x], [y", "t1:a,0,", ";", "1,2;" })
        {
            for (var at = 0; at <= cut.Length; at++)
            {
                values.Add(($"cut {cut} at {at}", new Result.ListValue([new Result.Str(cut[..at]), new Result.Str(cut[at..])])));
            }

            values.Add(($"whole {cut}", new Result.ListValue([new Result.Str(cut)])));
        }

        AssertPairwiseIdentityMatchesValueComparer([.. values]);
    }

    [Fact]
    public void T7_LegacyNeutralTextOfALoneSurrogateDoesNotSurviveUtf8ButTheIdentityDoes()
    {
        // A display-identical change: after a UTF-8 round trip the legacy text of a lone
        // surrogate and of U+FFFD are the same bytes; the identities never are.
        var lone = new Result.Str("\uD800");
        var replacement = new Result.Str("\uFFFD");
        static string Utf8(string text) => Encoding.UTF8.GetString(Encoding.UTF8.GetBytes(text));

        Assert.Equal(Utf8(MetamorphicValue.Neutral(lone)), Utf8(MetamorphicValue.Neutral(replacement)));
        Assert.NotEqual(Utf8(MetamorphicStructuralIdentity.Encode(lone)), Utf8(MetamorphicStructuralIdentity.Encode(replacement)));
        Assert.False(MetamorphicComparator.StructurallyEqual(Of(lone), Of(replacement)));

        // Composed and decomposed é render alike and are still different strings.
        Assert.False(MetamorphicComparator.StructurallyEqual(Of(new Result.Str("\u00E9")), Of(new Result.Str("e\u0301"))));
    }

    // ── T8: numeric equality compatibility ───────────────────────────────────

    [Theory]
    [InlineData("1.5", "1.50")]
    [InlineData("1.5", "150e-2")]
    [InlineData("100", "1e2")]
    [InlineData("100", "1.00e2")]
    [InlineData("0", "-0")]
    [InlineData("0", "0e5")]
    [InlineData("0", "0.000")]
    [InlineData("-0", "-0e-6176")]
    [InlineData("NaN", "NaN")]
    [InlineData("NaN", "-NaN")]
    [InlineData("Infinity", "Infinity")]
    [InlineData("1E+34", "10000000000000000000000000000000000")]
    [InlineData("9999999999999999999999999999999999e6111", "9.999999999999999999999999999999999E+6144")]
    [InlineData("1e-6176", "0.1e-6175")]
    public void T8_ValuesEqualUnderValueComparerHaveOneIdentityAndAreNeverRejected(string left, string right)
    {
        var a = new Result.Atom(Number(left));
        var b = new Result.Atom(Number(right));
        Assert.True(Result.ValueComparer.Equals(a, b));
        Assert.Equal(MetamorphicStructuralIdentity.Encode(a), MetamorphicStructuralIdentity.Encode(b));
        Assert.True(MetamorphicComparator.StructurallyEqual(Of(a), Of(b)));

        // Nested inside structures too, and through the real comparator.
        var wrappedA = new Result.ListValue([a, new Result.SequenceValue([a])]);
        var wrappedB = new Result.ListValue([b, new Result.SequenceValue([b])]);
        Assert.Null(MetamorphicComparator.Compare(
            CrossSourceCase("1", "1"), Observed(Of(wrappedA, 2)), Observed(Of(wrappedB, 2))));
    }

    [Theory]
    [InlineData("1.5", "1.51")]
    [InlineData("1.5", "-1.5")]
    [InlineData("Infinity", "-Infinity")]
    [InlineData("NaN", "Infinity")]
    [InlineData("NaN", "0")]
    [InlineData("0", "1e-6176")]
    [InlineData("-0", "-1e-6176")]
    [InlineData("1e-6176", "2e-6176")]
    [InlineData("9999999999999999999999999999999999e6111", "9999999999999999999999999999999998e6111")]
    [InlineData("1234567890123456789012345678901234e-17", "1234567890123456789012345678901235e-17")]
    [InlineData("1e2", "1e3")]
    [InlineData("10", "1")]
    public void T8_DifferentNumbersNeverCollide(string left, string right)
    {
        var a = new Result.Atom(Number(left));
        var b = new Result.Atom(Number(right));
        Assert.False(Result.ValueComparer.Equals(a, b));
        Assert.NotEqual(MetamorphicStructuralIdentity.Encode(a), MetamorphicStructuralIdentity.Encode(b));
        Assert.False(MetamorphicComparator.StructurallyEqual(Of(a), Of(b)));
    }

    [Fact]
    public void T8_RandomDecimal128QuantumVariantsAgreeExactlyWithValueComparer()
    {
        // Deterministic draws: a coefficient of up to 33 digits and an exponent across the whole
        // range, plus the SAME value with one more trailing zero (a different quantum) and a
        // neighbour. Identity equality must equal ValueComparer equality on every pair.
        var random = new Random(20261022);
        var checkedPairs = 0;
        for (var draw = 0; draw < 4000; draw++)
        {
            var digits = random.Next(1, 34);
            var coefficient = new StringBuilder(digits).Append((char)('1' + random.Next(9)));
            for (var d = 1; d < digits; d++) coefficient.Append((char)('0' + random.Next(10)));
            var exponent = random.Next(-6100, 6000);
            var sign = random.Next(2) == 0 ? "" : "-";

            var value = Number($"{sign}{coefficient}e{exponent}");
            var requantized = Number($"{sign}{coefficient}0e{exponent - 1}");
            var neighbour = Number($"{sign}{coefficient}1e{exponent - 1}");
            foreach (var (x, y) in new[] { (value, requantized), (value, neighbour), (requantized, neighbour) })
            {
                Result a = new Result.Atom(x);
                Result b = new Result.Atom(y);
                Assert.Equal(
                    Result.ValueComparer.Equals(a, b),
                    string.Equals(MetamorphicStructuralIdentity.Encode(a), MetamorphicStructuralIdentity.Encode(b), StringComparison.Ordinal));
                checkedPairs++;
            }

            Assert.True(MetamorphicStructuralIdentity.TryDecode(MetamorphicStructuralIdentity.Encode(new Result.Atom(value)), out var decoded, out var problem), problem);
            Assert.True(Result.ValueComparer.Equals(new Result.Atom(value), decoded));
        }

        Assert.Equal(12000, checkedPairs);
    }

    [Fact]
    public void T8_RealProgramsSpellingOneNumberDifferentlyAreNotRejected()
    {
        var testCase = CrossSourceCase("[1.5, 100]", "[1.50, 100.0]");
        var execution = MetamorphicExecutor.Execute(testCase);
        Assert.True(execution.Accepted, execution.RejectionReason);
        Assert.True(Result.ValueComparer.Equals(execution.Left!.Semantic.Value!, execution.Right!.Semantic.Value!));
        Assert.Null(MetamorphicComparator.Compare(testCase, execution.Left, execution.Right));
    }

    // ── T9/T10: deep and shared values ───────────────────────────────────────

    [Fact]
    public void T9_DeepValuesAreObservedComparedAndDecodedWithoutHostRecursion()
    {
        const int Depth = 200_000;
        Result left = new Result.Atom(1m);
        Result right = new Result.Atom(1m);
        Result different = new Result.Atom(2m);
        for (var level = 0; level < Depth; level++)
        {
            left = new Result.ListValue([left]);
            right = new Result.ListValue([right]);
            different = new Result.ListValue([different]);
        }

        var leftObservation = Of(left);
        Assert.True(MetamorphicComparator.StructurallyEqual(leftObservation, Of(right)));
        Assert.False(MetamorphicComparator.StructurallyEqual(leftObservation, Of(different)));
        Assert.True(MetamorphicStructuralIdentity.TryDecode(leftObservation.StructuralIdentity!, out var decoded, out var problem), problem);
        Assert.True(Result.ValueComparer.Equals(left, decoded));
    }

    [Fact]
    public void T10_SharingNeverChangesIdentityAndSharedDagsStayLinear()
    {
        // W = [x, x] applied n times: n + 1 distinct nodes, 2^n root-to-leaf paths.
        static Result Shared(int levels)
        {
            Result node = new Result.Str("leaf");
            for (var level = 0; level < levels; level++) node = new Result.ListValue([node, node]);
            return node;
        }

        static Result Independent(int levels)
            => levels == 0
                ? new Result.Str("leaf")
                : new Result.ListValue([Independent(levels - 1), Independent(levels - 1)]);

        // Equal values with different sharing: one identity, one verdict.
        var shared = Shared(12);
        var independent = Independent(12);
        Assert.Equal(MetamorphicStructuralIdentity.Encode(shared), MetamorphicStructuralIdentity.Encode(independent));
        Assert.True(MetamorphicComparator.StructurallyEqual(Of(shared), Of(independent)));

        // Partially shared: the left half shared, the right half rebuilt.
        var half = new Result.ListValue([Shared(11), Independent(11)]);
        Assert.Equal(MetamorphicStructuralIdentity.Encode(shared), MetamorphicStructuralIdentity.Encode(half));

        // 2^200 paths: the identity is still one definition per level, while the legacy neutral
        // text (one spelling per PATH) is beyond its observation bound and recorded as absent —
        // never truncated, and never needed for the verdict.
        var huge = Shared(200);
        var identity = MetamorphicStructuralIdentity.Encode(huge);
        Assert.True(identity.Length < 4_000, $"identity length {identity.Length}");
        var hugeObservation = Of(huge);
        Assert.Null(hugeObservation.Structure);
        Assert.Equal(identity, hugeObservation.StructuralIdentity);
        Assert.True(MetamorphicComparator.StructurallyEqual(hugeObservation, Of(Shared(200))));
        Assert.False(MetamorphicComparator.StructurallyEqual(hugeObservation, Of(Shared(199))));
        Assert.True(MetamorphicStructuralIdentity.TryDecode(identity, out var decoded, out var problem), problem);
        Assert.True(Result.ValueComparer.Equals(huge, decoded));

        var mismatch = Require(MetamorphicComparator.Compare(
            CrossSourceCase("1", "1"), Observed(hugeObservation), Observed(Of(Shared(199)))));
        Assert.Equal(MetamorphicMismatchKind.SemanticStructure, mismatch.Kind);
        Assert.Contains("unavailable", mismatch.ComparedProperty, StringComparison.Ordinal);
        Assert.True(mismatch.LeftValue.Length < 300);

        // The bound is exact: a value whose text fits keeps it byte for byte.
        var fits = Shared(10);
        Assert.Equal(MetamorphicValue.Neutral(fits), Of(fits).Structure);
        Assert.Null(MetamorphicValue.NeutralWithin(fits, MetamorphicValue.Neutral(fits).Length - 1));
        Assert.Equal(MetamorphicValue.Neutral(fits), MetamorphicValue.NeutralWithin(fits, MetamorphicValue.Neutral(fits).Length));
    }

    // ── T11: emitted count stays its own facet ───────────────────────────────

    [Fact]
    public void T11_EqualValuesWithDifferentEmittedCountsFailOnTheCountFacet()
    {
        var value = new Result.SequenceValue([new Result.Atom(1m), new Result.Atom(2m)]);
        var oneRow = Observed(Of(value, 1));
        var twoRows = Observed(Of(value, 2));

        var equal = Require(MetamorphicComparator.Compare(CrossSourceCase("1", "1"), oneRow, twoRows));
        Assert.Equal(MetamorphicMismatchKind.EmittedCount, equal.Kind);

        var shared = Require(MetamorphicComparator.Compare(MetamorphicFacetsCase(MetamorphicSemanticRelation.SameStructuredOutcome), oneRow, twoRows));
        Assert.Equal(MetamorphicMismatchKind.EmittedCount, shared.Kind);

        // A surface pair without the emitted-count facet does not compare it at all.
        var noCount = MetamorphicFacets.Outcome | MetamorphicFacets.StructuredError | MetamorphicFacets.Structure;
        Assert.Null(MetamorphicComparator.Compare(
            MetamorphicFacetsCase(MetamorphicSemanticRelation.SameStructuredOutcome),
            oneRow with { Facets = noCount }, twoRows with { Facets = noCount }));
    }

    // ── T12: the durable representation ──────────────────────────────────────

    [Fact]
    public void T12_DurableIdentityIsVersionedDeterministicAndPinned()
    {
        var value = new Result.ListValue(
        [
            new Result.Atom(Number("1.50")),
            new Result.Bool(true),
            new Result.Str("a\\'\n"),
            new Result.SequenceValue([]),
            new Result.ListValue([]),
            new Result.Atom(Number("1.5")),
        ]);

        const string Expected = "kl-struct-v1:6:n5:15e-1b1t4:a\\\\'\\u000As0:;l0:;l6:0,1,2,3,4,0,;";
        Assert.Equal(Expected, MetamorphicStructuralIdentity.Encode(value));
        Assert.StartsWith(MetamorphicStructuralIdentity.Version + ":", Expected, StringComparison.Ordinal);

        // Two independent runs of one program produce the same identity.
        var first = ObserveThrough(MetamorphicSurface.EvaluatorRunCountedObserved, "[1.5, \"x\", true, [[], ()]]");
        var second = ObserveThrough(MetamorphicSurface.EvaluatorRunCountedObserved, "[1.5, \"x\", true, [[], ()]]");
        Assert.NotSame(first.Semantic.Value, second.Semantic.Value);
        Assert.Equal(first.Semantic.StructuralIdentity, second.Semantic.StructuralIdentity);
        Assert.Equal(first, second);

        Assert.True(MetamorphicStructuralIdentity.TryDecode(first.Semantic.StructuralIdentity!, out var decoded, out var problem), problem);
        Assert.True(Result.ValueComparer.Equals(first.Semantic.Value!, decoded));
    }

    [Theory]
    [InlineData("", "missing")]
    [InlineData("kl-struct-v2:1:b1", "version")]
    [InlineData("kl-struct-v1:0:", "count")]
    [InlineData("kl-struct-v1:01:b1", "count")]
    [InlineData("kl-struct-v1:1:b2", "Boolean")]
    [InlineData("kl-struct-v1:1:b1b0", "trailing")]
    [InlineData("kl-struct-v1:2:b1", "count")]
    [InlineData("kl-struct-v1:1:n6:150e-2", "canonical number")]
    [InlineData("kl-struct-v1:1:n3:1E2", "canonical number")]
    [InlineData("kl-struct-v1:1:n2:-0", "canonical number")]
    [InlineData("kl-struct-v1:1:t1:\\u0041", "string unit")]
    [InlineData("kl-struct-v1:1:t1:\\u005C", "string unit")]
    [InlineData("kl-struct-v1:1:t1:\\u000a", "string unit")]
    [InlineData("kl-struct-v1:1:t2:a", "string framing")]
    [InlineData("kl-struct-v1:1:l1:0,;", "earlier node")]
    [InlineData("kl-struct-v1:2:b1l1:0;", "structure framing")]
    [InlineData("kl-struct-v1:3:b0b1l2:1,0,;", "canonical encoding")]
    [InlineData("kl-struct-v1:3:b1b1l2:0,1,;", "canonical encoding")]
    [InlineData("kl-struct-v1:3:b1b0l1:0,;", "canonical encoding")]
    public void T12_DecoderAcceptsOnlyTheCanonicalSpelling(string text, string reason)
    {
        Assert.False(MetamorphicStructuralIdentity.TryDecode(text, out _, out var problem));
        Assert.Contains(reason, problem, StringComparison.Ordinal);
    }

    [Fact]
    public void T12_MismatchDiagnosticsAreBounded()
    {
        var wide = new Result.ListValue(Enumerable.Range(0, 5_000).Select(i => (Result)new Result.Str("item" + i)));
        var other = new Result.ListValue(Enumerable.Range(0, 5_000).Select(i => (Result)new Result.Str("item" + (i + 1))));
        var leftObservation = Of(wide) with { Structure = "same" };
        var rightObservation = Of(other) with { Structure = "same" };
        var mismatch = Require(MetamorphicComparator.Compare(
            CrossSourceCase("1", "1"), Observed(leftObservation), Observed(rightObservation)));

        Assert.Equal(MetamorphicMismatchKind.SemanticStructure, mismatch.Kind);
        Assert.True(mismatch.LeftValue.Length < 300, mismatch.LeftValue);
        Assert.True(mismatch.RightValue.Length < 300, mismatch.RightValue);
        Assert.Contains("chars)", mismatch.LeftValue, StringComparison.Ordinal);
    }

    [Fact]
    public void Review_DecoderRejectsAnOverflowingNumberLengthWithoutThrowing()
    {
        Assert.False(MetamorphicStructuralIdentity.TryDecode(
            "kl-struct-v1:1:n2147483630:0", out _, out var problem));
        Assert.Contains("framing", problem, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("kl-struct-v1:2147483647:", "count")]
    [InlineData("kl-struct-v1:1:t2147483647:x", "string framing")]
    [InlineData("kl-struct-v1:1:l2147483647:;", "structure framing")]
    [InlineData("kl-struct-v1:1:n2147483647:0", "number framing")]
    public void Review_DecoderChecksDeclaredCountsBeforeAllocating(string text, string reason)
    {
        Assert.False(MetamorphicStructuralIdentity.TryDecode(text, out _, out var problem));
        Assert.Contains(reason, problem, StringComparison.Ordinal);
    }

    [Fact]
    public void Review_OrdinaryStructuralMismatchDiagnosticsAreBoundedAndEscaped()
    {
        var left = Of(new Result.Str("\n\0\uD800" + new string('a', 10_000)));
        var right = Of(new Result.Str("\r\t\uDC00" + new string('b', 10_000)));
        var mismatch = Require(MetamorphicComparator.Compare(
            CrossSourceCase("1", "1"), Observed(left), Observed(right)));

        Assert.Equal(MetamorphicMismatchKind.SemanticStructure, mismatch.Kind);
        foreach (var diagnostic in new[] { mismatch.LeftValue, mismatch.RightValue, left.ToString(), right.ToString() })
        {
            Assert.True(diagnostic.Length < 800, $"diagnostic length {diagnostic.Length}");
            Assert.DoesNotContain(diagnostic, unit => char.IsControl(unit) || char.IsSurrogate(unit));
        }
    }

    [Fact]
    public void Review_MissingSuccessfulStructureCannotPassAsTwoNulls()
    {
        var missing = Observed(new MetamorphicSemanticObservation("ok", null, 1, null, null, false));
        Assert.Throws<MetamorphicHarnessException>(() => MetamorphicComparator.Compare(
            MetamorphicFacetsCase(MetamorphicSemanticRelation.SameStructuredOutcome), missing, missing));

        var full = Of(new Result.Atom(1m));
        var legacy = Legacy(full);
        Assert.Throws<MetamorphicHarnessException>(() => MetamorphicComparator.StructurallyEqual(full, legacy));
        Assert.Throws<MetamorphicHarnessException>(() => MetamorphicComparator.StructurallyEqual(legacy, legacy));

        var durable = full with { Value = null, Structure = null };
        Assert.True(MetamorphicComparator.StructurallyEqual(full, durable));
        Assert.True(MetamorphicComparator.StructurallyEqual(durable, durable));
        Assert.False(MetamorphicComparator.StructurallyEqual(durable, Of(new Result.Atom(2m))));
        var invalid = durable with { StructuralIdentity = "not-a-versioned-value" };
        Assert.Throws<MetamorphicHarnessException>(() => MetamorphicComparator.StructurallyEqual(invalid, invalid));
    }

    [Fact]
    public void Review_NeutralLimitBoundsWorkBeforeAppendingALargeStringOrQueuingWideChildren()
    {
        const int Width = 100_000;
        Result wide = new Result.ListValue(Enumerable.Repeat<Result>(new Result.Atom(1m), Width));
        Result longString = new Result.Str(new string('x', Width));
        foreach (var value in new[] { wide, longString })
        {
            var before = GC.GetAllocatedBytesForCurrentThread();
            var neutral = MetamorphicValue.NeutralWithin(value, 2);
            var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.Null(neutral);
            Assert.True(allocated < Width, $"bounded neutral observation allocated {allocated} bytes");
        }
    }

    // ── Observer integrity: populated where required, consistent with the authority ──

    [Fact]
    public void EverySurfaceProjectingStructureCarriesTheTypedValueAndItsIdentity()
    {
        foreach (var surface in MetamorphicSurfaces.All)
        {
            var observation = ObserveThrough(surface.Surface, "[\"a', 'b\", 1.50, true, ()]");
            var semantic = observation.Semantic;
            if (surface.Facets.HasFlag(MetamorphicFacets.Structure))
            {
                Assert.NotNull(semantic.Structure);
                var value = Assert.IsAssignableFrom<Result>(semantic.Value);
                Assert.Equal(MetamorphicStructuralIdentity.Encode(value), semantic.StructuralIdentity);
                Assert.Equal(MetamorphicValue.Neutral(value), semantic.Structure);
            }
            else
            {
                // Never invented for a surface that does not hand back a value.
                Assert.Null(semantic.Structure);
                Assert.Null(semantic.Value);
                Assert.Null(semantic.StructuralIdentity);
            }
        }
    }

    [Fact]
    public void AnInconsistentObserverIsAHarnessDefectNotAVerdict()
    {
        // Typed values equal, identities forged to differ: neither "equal" nor "different" is safe.
        var value = new Result.Atom(1m);
        var forged = Of(value) with { StructuralIdentity = MetamorphicStructuralIdentity.Encode(new Result.Atom(2m)) };
        Assert.Throws<MetamorphicHarnessException>(() => MetamorphicComparator.StructurallyEqual(Of(value), forged));
    }

    [Fact]
    public void FaultInjection_ValueKindChangeWithSimilarTextIsDetected()
    {
        var testCase = CrossSourceCase("1", "1");
        foreach (var (left, right) in new (Result, Result)[]
        {
            (new Result.Atom(1m), new Result.Str("1")),
            (new Result.Bool(true), new Result.Str("true")),
            (new Result.ListValue([]), new Result.Str("L[]")),
            (new Result.ListValue([new Result.Atom(1m)]), new Result.SequenceValue([new Result.Atom(1m)])),
        })
        {
            Assert.Equal(
                MetamorphicMismatchKind.SemanticStructure,
                Require(MetamorphicComparator.Compare(testCase, Observed(Of(left)), Observed(Of(right)))).Kind);
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    private static void AssertPairwiseIdentityMatchesValueComparer((string Name, Result Value)[] values)
    {
        var identities = values.Select(entry => MetamorphicStructuralIdentity.Encode(entry.Value)).ToArray();
        for (var i = 0; i < values.Length; i++)
        {
            Assert.True(MetamorphicStructuralIdentity.TryDecode(identities[i], out var decoded, out var problem), $"{values[i].Name}: {problem}");
            Assert.True(Result.ValueComparer.Equals(values[i].Value, decoded), values[i].Name);
            for (var j = 0; j < values.Length; j++)
            {
                Assert.True(
                    Result.ValueComparer.Equals(values[i].Value, values[j].Value)
                        == string.Equals(identities[i], identities[j], StringComparison.Ordinal),
                    $"identity and ValueComparer disagree on '{values[i].Name}' vs '{values[j].Name}'");
            }
        }
    }

    private static Decimal128 Number(string text) => text switch
    {
        "NaN" => Decimal128.NaN,
        "-NaN" => -Decimal128.NaN,
        "Infinity" => Decimal128.PositiveInfinity,
        "-Infinity" => Decimal128.NegativeInfinity,
        _ => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture),
    };

    /// <summary>A full success observation of a value, as every value-projecting surface builds it.</summary>
    private static MetamorphicSemanticObservation Of(Result value, int emitted = 1)
        => MetamorphicSemanticObservation.OfValue(value, emitted);

    /// <summary>The pre-SEM-2A shape of a success observation: neutral text and count only.</summary>
    private static MetamorphicSemanticObservation Legacy(MetamorphicSemanticObservation observation)
        => MetamorphicSemanticObservation.Success(observation.Structure!, observation.EmittedCount!.Value);

    private static MetamorphicOperationalObservation Observed(MetamorphicSemanticObservation semantic)
        => new(semantic, 0, 0, 0, 0, "on");

    /// <summary>
    /// A Phase 1 (cross-source, normalized) case carrying two arbitrary programs; the decoded
    /// template only supplies the execution policy, the sources are the test's own.
    /// </summary>
    private static MetamorphicCase CrossSourceCase(string left, string right)
        => MetamorphicTemplates.Build(MetamorphicDecoder.Decode([0, 0, 0, 1, 1, 1])) with
        {
            LeftSource = left,
            RightSource = right,
        };

    private static MetamorphicCase MetamorphicFacetsCase(MetamorphicSemanticRelation relation)
        => CrossSourceCase("1", "1") with
        {
            SemanticRelation = relation,
            OperationalRelation = MetamorphicOperationalRelation.NotCompared,
        };

    private static MetamorphicOperationalObservation ObserveThrough(MetamorphicSurface surface, string source)
    {
        var profile = new MetamorphicExecutionProfile(surface, null, EnableOptimizations: true);
        Assert.True(
            MetamorphicSurfaces.TryObserve(
                source, profile, MetamorphicExecutor.OptionsFor(profile), collectEvidence: false,
                out var observation, out var reason),
            reason);
        return observation;
    }

    private static MetamorphicMismatch Require(MetamorphicMismatch? mismatch)
        => Assert.IsType<MetamorphicMismatch>(mismatch);
}
