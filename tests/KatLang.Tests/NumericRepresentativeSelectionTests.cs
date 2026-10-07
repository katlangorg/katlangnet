using System.Globalization;
using System.Numerics;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// Q-28, decided N-F (2026-10-07): "the same numeric value" is <c>==</c> — <c>Decimal128.Equals</c>
/// at numeric leaves, recursively structural over sequences and lists — for every consumer, and a
/// number's Decimal128 REPRESENTATION (quantum, zero sign, NaN sign) is data the value carries,
/// never part of its equality and never provenance. A repeated name keeps ONE richest compatible
/// complete contribution (NEED-04: VALUE + CALLABLE outranks VALUE only, in either order); among
/// equally rich contributions the FIRST in written pattern traversal order (left to right, depth
/// first) supplies the complete retained value, representation included — nothing is synthesized,
/// canonicalized, or merged from several arguments. Permutation preserves satisfiability and,
/// on success, callable identity, channel availability and the bound value up to <c>==</c>, but
/// may change the retained representation. Coexisting incompatibilities follow ordinary failure
/// order, so their reported categories may differ. Collections keep their own representative rules
/// (<c>distinct</c> the first of each class, <c>contains</c> membership by <c>==</c>, <c>order</c>
/// stable and representation-preserving, <c>orderDesc</c> its exact reverse under COLL-06's current
/// rule). Numeric literal patterns match by <c>==</c>, so equal literals are one clause head.
/// <para>Every observation runs on the six routes (<see cref="SixRouteAgreement"/>) and renders
/// numbers REPRESENTATION-EXACTLY (<see cref="Exact"/>): the canonical text plus what that text
/// cannot show — the NaN sign and a positive quantum exponent — so route agreement and every
/// expectation hold on representation, never merely on <c>==</c>. Decimal128-tier only: Lean's
/// <c>Int</c> model has one representation per value (FORMAL-04), so the matching canonical cases
/// are C#-only (<c>repeated-name-keeps-first-equally-rich-representative</c>,
/// <c>decimal-literal-patterns-match-by-value</c>).</para>
/// </summary>
public sealed class NumericRepresentativeSelectionTests
{
    /// <summary>
    /// (label, a, b, equal): <c>==</c>-equal numbers with different representations, the identical
    /// control, and one unequal control.
    /// </summary>
    public static readonly TheoryData<string, string, string, bool> Pairs = new()
    {
        { "same", "1.5", "1.5", true },
        { "quantum", "1.5", "1.50", true },
        { "quantum-reversed", "1.50", "1.5", true },
        { "integral-quantum", "1", "1.0", true },
        { "integral-quantum-reversed", "1.0", "1", true },
        { "two-quanta", "1.00", "1.0", true },
        { "zero-sign", "0", "-0", true },
        { "zero-sign-reversed", "-0", "0", true },
        { "fractional-zero-sign", "0.0", "-0.0", true },
        { "zero-quantum", "0", "0.0", true },
        { "zero-mixed", "-0.0", "0", true },
        { "nan-sign", "sqrt(-1)", "sign(sqrt(-1))", true },
        { "nan-sign-reversed", "sign(sqrt(-1))", "sqrt(-1)", true },
        { "independent-nans", "sqrt(-1)", "ln(-1)", true },
        { "positive-infinity", "(1e6144 * 10)", "(2e6144 * 10)", true },
        { "negative-infinity", "(-1e6144 * 10)", "(-2e6144 * 10)", true },
        { "positive-exponent", "1e3", "1000", true },
        { "positive-exponent-reversed", "1000", "1e3", true },
        { "arithmetic-origin", "(0.5 + 0.5)", "1", true },
        { "arithmetic-origin-reversed", "1", "(0.5 + 0.5)", true },
        { "subtraction-origin", "(3 - 1.0)", "2", true },
        { "unequal-control", "1.5", "1.6", false },
    };

    /// <summary>Scalar, sequence, list and nested shapes carrying the number at every depth.</summary>
    private static readonly string[] Shapes = ["{0}", "({0}, 7)", "[{0}, 7]", "(({0}, 7), [{0}])"];

    private const string Prelude =
        "Id(v) = v\nP(x, x) = x\nFwd(u, v) = P(u, v)\nQ((x, x)) = x\nStep(x, x) = x\n" +
        "E(x, x) = x\nE(x, y) = 'diff'\nEQ((x, x)) = x\nEQ((x, y)) = 'diff'\n";

    /// <summary>
    /// A number rendered representation-exactly: <c>.string</c>'s canonical text, the NaN sign
    /// (<c>sign(NaN)</c> is the BCL's negative NaN, computed NaNs are positive), and a positive
    /// quantum exponent (<c>1e3</c> and <c>1000</c> render alike as text).
    /// </summary>
    internal static string Number(Decimal128 value)
    {
        if (Decimal128.IsNaN(value))
            return Decimal128.IsNegative(value) ? "NaN(-)" : "NaN(+)";

        var text = ValueTextRenderer.FormatNumberInvariant(value);
        if (Decimal128.IsFinite(value))
        {
            var exponent = Decimal128.ILogB(Decimal128.GetQuantum(value));
            if (exponent > 0)
                return text + "{q=+" + exponent.ToString(CultureInfo.InvariantCulture) + "}";
        }

        return text;
    }

    /// <summary>A value rendered representation-exactly at every leaf, kinds kept.</summary>
    internal static string Exact(Result value) => value switch
    {
        Result.Atom atom => Number(atom.Value),
        Result.Str text => "'" + text.Value + "'",
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.SequenceValue sequence => "S[" + string.Join(", ", sequence.Items.Select(Exact)) + "]",
        Result.ListValue list => "L[" + string.Join(", ", list.Items.Select(Exact)) + "]",
    };

    /// <summary>The outcome every route agrees on, representation-exactly: <c>ok value</c> or <c>err Code</c>.</summary>
    private static async Task<string> AgreedAsync(string source)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source, Exact);
        return oracle.Kind switch
        {
            "ok" => "ok " + oracle.Value,
            "err" => "err " + oracle.Errors[0][..oracle.Errors[0].IndexOf(':', StringComparison.Ordinal)],
            _ => oracle.ToString(),
        };
    }

    private static async Task<string> ValueAsync(string source)
    {
        var outcome = await AgreedAsync(source);
        Assert.StartsWith("ok ", outcome, StringComparison.Ordinal);
        return outcome[3..];
    }

    private static string Bool(bool value) => value ? "true" : "false";

    /// <summary>The origins of two contributions: literal, call result, dot receiver, forwarded parameter, loop state.</summary>
    private static string[] Binders(string x, string y) =>
        [$"P({x}, {y})", $"P(Id({x}), Id({y}))", $"({x}).P({y})", $"Fwd({x}, {y})", $"repeat(Step, 1, {x}, {y})"];

    private static string[] Families(string x, string y) =>
        [$"E({x}, {y})", $"E(Id({x}), Id({y}))", $"repeat(E, 1, {x}, {y})"];

    // ── One equality: == ignores representation, at every depth ─────────────────

    [Theory]
    [MemberData(nameof(Pairs))]
    public async Task EqualityClass_IgnoresRepresentation_AtEveryShape(string label, string a, string b, bool equal)
    {
        _ = label;
        foreach (var shape in Shapes)
        {
            var (left, right) = (string.Format(CultureInfo.InvariantCulture, shape, a), string.Format(CultureInfo.InvariantCulture, shape, b));
            Assert.Equal(
                $"ok S[{Bool(equal)}, {Bool(equal)}, {Bool(!equal)}]",
                await AgreedAsync($"{left} == {right}, {right} == {left}, {left} != {right}"));
        }
    }

    [Fact]
    public async Task StructuralEquality_IgnoresRepresentation_AtEveryDepth_ButKeepsKinds()
    {
        Assert.Equal(
            "ok S[true, true, true, false]",
            await AgreedAsync("(1.0, [2]) == (1, [2.0]), [(0, 1)] == [(-0, 1.0)], (sqrt(-1), 1) == (ln(-1), 1), (1.0, [2]) == [1, [2]]"));
    }

    [Fact]
    public async Task NaN_IsOneValue_AndItsSignIsInvisibleToTheLanguage()
    {
        Assert.Equal(
            "ok S[true, true, 'NaN', 'NaN', true]",
            await AgreedAsync("sqrt(-1) == sign(sqrt(-1)), sqrt(-1) == ln(-1), sqrt(-1).string, sign(sqrt(-1)).string, sqrt(-1).string == (-sqrt(-1)).string"));
    }

    // ── Repeated names: the first equally rich complete contribution ────────────

    [Theory]
    [MemberData(nameof(Pairs))]
    public async Task RepeatedName_KeepsTheFirstEquallyRichContribution_OverEveryOriginAndShape(string label, string a, string b, bool equal)
    {
        _ = label;
        foreach (var shape in Shapes)
        {
            var (left, right) = (string.Format(CultureInfo.InvariantCulture, shape, a), string.Format(CultureInfo.InvariantCulture, shape, b));
            if (equal)
            {
                // The retained value is the FIRST contribution's own complete value — its exact
                // representation at every leaf — never the second's, never a merge of both.
                var first = await ValueAsync(left);
                foreach (var call in Binders(left, right).Concat(Families(left, right)))
                    Assert.Equal("ok " + first, await AgreedAsync(Prelude + call));
                Assert.Equal($"ok L[{first}]", await AgreedAsync(Prelude + $"map([({left}, {right})], Q)"));
                Assert.Equal($"ok L[{first}]", await AgreedAsync(Prelude + $"map([({left}, {right})], EQ)"));
            }
            else
            {
                // These VALUE-only unequal pairs fail in both orders with ArityMismatch.
                // Mixed independent incompatibilities may report different categories.
                var (forward, backward) = (Binders(left, right), Binders(right, left));
                for (var i = 0; i < forward.Length; i++)
                {
                    Assert.Equal("err ArityMismatch", await AgreedAsync(Prelude + forward[i]));
                    Assert.Equal("err ArityMismatch", await AgreedAsync(Prelude + backward[i]));
                }

                foreach (var call in Families(left, right).Concat(Families(right, left)))
                    Assert.Equal("ok 'diff'", await AgreedAsync(Prelude + call));
                Assert.Equal("ok L['diff']", await AgreedAsync(Prelude + $"map([({left}, {right})], EQ)"));
                Assert.Equal("err ArityMismatch", await AgreedAsync(Prelude + $"map([({left}, {right})], Q)"));
            }
        }
    }

    /// <summary>
    /// Successful compatible contributions remain successful when swapped and preserve the bound
    /// value up to <c>==</c>; the first equally rich representation may differ. This does not
    /// assert error-category invariance for arbitrary failing contribution sets.
    /// </summary>
    [Theory]
    [MemberData(nameof(Pairs))]
    public async Task Permutation_PreservesTheBoundValue_UpToEquality(string label, string a, string b, bool equal)
    {
        _ = label;
        if (!equal)
            return;

        Assert.Equal(
            "ok S[true, true]",
            await AgreedAsync(Prelude + $"P({a}, {b}) == P({b}, {a}), E({a}, {b}) == E({b}, {a})"));
    }

    [Fact]
    public async Task RepeatedName_StringObservesTheRetainedRepresentative()
    {
        // The canonical N-F examples: argument order may decide the representative of equally
        // rich contributions — the first written one — and nothing else.
        Assert.Equal(
            "ok S['1.5', '1.50', '0', '-0']",
            await AgreedAsync("P(x, x) = x.string\nP(1.5, 1.50), P(1.50, 1.5), P(0, -0), P(-0, 0)"));
        Assert.Equal(
            "ok S['1.5', '1.50', '1.50']",
            await AgreedAsync("P3(x, x, x) = x.string\nP3(1.5, 1.50, 1.500), P3(1.50, 1.5, 1.500), P3(1.50, 1.500, 1.5)"));
    }

    [Fact]
    public async Task RepeatedName_NestedValues_KeepTheFirstContributionWhole_NeverAMerge()
    {
        // (1.0, 2) and (1, 2.0) are == at every leaf; the binding is the first argument's own
        // pair — never (1.0, 2.0), (1, 2) or any other leaf-wise mixture of both arguments.
        Assert.Equal("ok S[1.0, 2]", await AgreedAsync("P(x, x) = x\nP((1.0, 2), (1, 2.0))"));
        Assert.Equal("ok S[1, 2.0]", await AgreedAsync("P(x, x) = x\nP((1, 2.0), (1.0, 2))"));
        Assert.Equal("ok L[-0, 1.50]", await AgreedAsync("P(x, x) = x\nP([-0, 1.50], [0, 1.5])"));
        Assert.Equal("ok S[S[0, 1.5], L[-0]]", await AgreedAsync("P(x, x) = x\nP(((0, 1.5), [-0]), ((-0, 1.50), [0]))"));
    }

    [Fact]
    public async Task RicherContribution_WinsInEitherOrder_WithoutSplicing()
    {
        // NEED-04 decides first: a contribution carrying VALUE and CALLABLE (a named property)
        // outranks a VALUE-only one in either order; N-F only breaks the equally rich tie.
        Assert.Equal(
            "ok S['1.50', '1.50', '1.50']",
            await AgreedAsync("A = 1.50\nP(x, x) = x.string\nP(1.5, A), P(A, 1.5), P3(1.5, 1.500, A)\nP3(x, x, x) = x.string"));
        Assert.Equal(
            "ok S[S['1.50', '1.50'], S['1.50', '1.50']]",
            await AgreedAsync("A = 1.50\nP(f, f) = f.string, f().string\nP(1.5, A), P(A, 1.5)"));
        Assert.Equal(
            "ok S['1.50', '1.50']",
            await AgreedAsync("Only(*xs) = 1.50 + xs.count\nP(x, x) = x.string\nP(1.5, Only), P(Only, 1.5)"));
        Assert.Equal("ok S['-0', '-0']", await AgreedAsync("Z = -0\nP(x, x) = x.string\nP(0, Z), P(Z, 0)"));
        Assert.Equal(
            "ok S['1.5', '1.50', '1.50', '1.50']",
            await AgreedAsync("A = 1.50\nP(x, x) = x.string\nFwd(a, b) = P(a, b)\nFwd(1.5, 1.50), Fwd(1.50, 1.5), Fwd(1.5, A), Fwd(A, 1.5)"));

        // Two different callable identities with == values never merge (NEED-04), whatever the order.
        Assert.Equal("err TypeMismatch", await AgreedAsync("A = 1.50\nB = 1.5\nP(x, x) = x\nP(A, B)"));
        Assert.Equal("err TypeMismatch", await AgreedAsync("A = 1.50\nB = 1.5\nP(x, x) = x\nP(B, A)"));
    }

    [Fact]
    public async Task Family_ComparesByValue_AndKeepsTheFirstEquallyRichRepresentative()
    {
        Assert.Equal(
            "ok S['1.5', '1.50', '0', '-0', 'diff']",
            await AgreedAsync("E(x, x) = x.string\nE(x, y) = 'diff'\nE(1.5, 1.50), E(1.50, 1.5), E(0, -0), E(-0, 0), E(1.5, 1.6)"));
        Assert.Equal(
            "ok S['zeros', 'zeros', '1.5']",
            await AgreedAsync("F(0, 0) = 'zeros'\nF(x, x) = x.string\nF(x, y) = 'diff'\nF(0, -0), F(0.0, -0.0), F(1.5, 1.50)"));
        Assert.Equal(
            "ok S['1.50', '1.50']",
            await AgreedAsync("A = 1.50\nE(x, x) = x.string\nE(x, y) = 'diff'\nE(1.5, A), E(A, 1.5)"));
    }

    // ── Literal patterns: matching by value ─────────────────────────────────────

    [Fact]
    public async Task LiteralPattern_MatchesEveryRepresentativeOfItsValue()
    {
        Assert.Equal("ok S['hit', 'hit', 'hit', 'miss']", await AgreedAsync("F(1.5) = 'hit'\nF(x) = 'miss'\nF(1.5), F(1.50), F(3 / 2), F(1.6)"));
        Assert.Equal("ok S['hit', 'hit', 'hit', 'hit']", await AgreedAsync("F(0) = 'hit'\nF(x) = 'miss'\nF(0), F(-0), F(0.0), F(0 * -1)"));
        Assert.Equal("ok S['hit', 'hit', 'hit']", await AgreedAsync("F(-0) = 'hit'\nF(x) = 'miss'\nF(0), F(-0.0), F(0.00)"));
        Assert.Equal("ok S['hit', 'hit', 'hit']", await AgreedAsync("F(1) = 'hit'\nF(x) = 'miss'\nF(1.0), F(0.5 + 0.5), F(1)"));
        Assert.Equal("ok S['hit', 'hit']", await AgreedAsync("F(1e3) = 'hit'\nF(x) = 'miss'\nF(1000), F(1e3)"));
        Assert.Equal("ok S[5, 6]", await AgreedAsync("G((0, x)) = x\nG((y, x)) = 'other'\nG((-0, 5)), G((0.0, 6))"));
        Assert.Equal("ok S[5, 6]", await AgreedAsync("H([1.5, x]) = x\nH([y, x]) = 'other'\nH([1.50, 5]), H([3 / 2, 6])"));
    }

    /// <summary>A literal retains nothing: the bound binder keeps the ARGUMENT's representation.</summary>
    [Fact]
    public async Task LiteralPattern_RetainsTheArgumentsOwnRepresentation()
    {
        Assert.Equal(
            "ok S['1.50', '-0']",
            await AgreedAsync("K((1.5, x)) = x.string\nK((y, x)) = 'other'\nM((0, z)) = z.string\nM((y, z)) = 'other'\nK((1.50, 1.50)), M((-0, -0))"));
    }

    [Theory]
    [InlineData("1.5", "1.50")]
    [InlineData("0", "-0")]
    [InlineData("0.0", "-0.0")]
    [InlineData("1e3", "1000")]
    [InlineData("1", "1.0")]
    public void EqualLiterals_AreTheSameClauseHead(string a, string b)
    {
        var parsed = Parser.Parse($"F({a}) = 1\nF({b}) = 2\nF(x) = 0\nF({a})");
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.DuplicateBranchPattern);
    }

    [Fact]
    public void UnequalLiterals_AreDistinctClauseHeads()
        => SourceProvenance.ParseValid("F(1.5) = 1\nF(1.6) = 2\nF(x) = 0\nF(1.5)");

    // ── Collections: operation-specific representative rules ────────────────────

    [Theory]
    [MemberData(nameof(Pairs))]
    public async Task Distinct_KeepsTheFirstOccurrence_AndContainsIsMembershipByValue(string label, string a, string b, bool equal)
    {
        _ = label;
        foreach (var shape in Shapes)
        {
            var (left, right) = (string.Format(CultureInfo.InvariantCulture, shape, a), string.Format(CultureInfo.InvariantCulture, shape, b));
            var (leftValue, rightValue) = (await ValueAsync(left), await ValueAsync(right));
            Assert.Equal(equal ? $"ok L[{leftValue}]" : $"ok L[{leftValue}, {rightValue}]", await AgreedAsync($"distinct(({left}, {right}))"));
            Assert.Equal(equal ? $"ok L[{rightValue}]" : $"ok L[{rightValue}, {leftValue}]", await AgreedAsync($"distinct(({right}, {left}))"));
            Assert.Equal($"ok S[{Bool(equal)}, {Bool(equal)}]", await AgreedAsync($"contains([{left}], {right}), contains([{right}], {left})"));
        }
    }

    [Fact]
    public async Task Distinct_OfNaNs_KeepsTheFirstNaN()
        => Assert.Equal("ok L[NaN(+)]", await AgreedAsync("distinct((sqrt(-1), sign(sqrt(-1)), ln(-1)))"));

    /// <summary>
    /// <c>order</c> keeps every input element and its representation, equal items in written
    /// order (a stable sort); <c>orderDesc</c> is the exact reverse of that ascending result — the
    /// current COLL-06 rule, whose equal-item question Q-28 does not decide.
    /// </summary>
    [Theory]
    [MemberData(nameof(Pairs))]
    public async Task Order_KeepsEveryRepresentative_TiesInWrittenOrder_AndOrderDescIsTheExactReverse(string label, string a, string b, bool equal)
    {
        _ = (label, equal);   // the unequal control is ascending as written (1.5 < 1.6), so one expectation covers it
        var (leftValue, rightValue) = (await ValueAsync(a), await ValueAsync(b));
        Assert.Equal(
            $"ok S[L[{leftValue}, {rightValue}], L[{rightValue}, {leftValue}], {leftValue}]",
            await AgreedAsync($"order(({a}, {b})), orderDesc(({a}, {b})), first(order(({a}, {b})))"));
    }

    // ── Representation is data: .string observes it, provenance is not kept ────

    [Fact]
    public async Task String_ObservesQuantumAndZeroSign_ButNotNaNSignOrPositiveExponent()
    {
        Assert.Equal(
            "ok S['1.5', '1.50', '1', '1.0', '0', '-0', '0.0', '-0.0', 'NaN', 'NaN', '1000', '1000', 'Infinity', '-Infinity']",
            await AgreedAsync("(1.5).string, (1.50).string, (1).string, (1.0).string, (0).string, (-0).string, (0.0).string, (-0.0).string, " +
                "sqrt(-1).string, sign(sqrt(-1)).string, (1e3).string, (1000).string, (1e6144 * 10).string, (-1e6144 * 10).string"));
    }

    [Fact]
    public async Task Representation_IsData_NotProvenance()
    {
        // The representation is what the operation produced, never a record of the route: the
        // computed 0.5 + 0.5 and the literal 1.0 are bit-identical.
        Assert.Equal(
            "ok S[true, true, '1.0', '1']",
            await AgreedAsync("(0.5 + 0.5).string == 1.0.string, (3 / 3).string == (1).string, (2 * 0.5).string, (6 / 6).string"));
    }

    [Fact]
    public async Task ValueCarryingOperations_PreserveTheRepresentation()
    {
        // Binding, storage, selection, passing, collecting and sorting carry the exact
        // representation unchanged.
        Assert.Equal(
            "ok S[1.50, -0, 1.50, L[-0, 1.50], 1.50, L[-0.0, 1.50]]",
            await AgreedAsync("A = 1.50\nB = -0\nId(v) = v\nColl(*xs) = xs\nA, Id(B), (A, B):0, Coll(B, A), [A, 2]:0, order((1.50, -0.0))"));
    }
}
