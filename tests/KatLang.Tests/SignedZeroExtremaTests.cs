using System.Numerics;
using KatLang.Optimizations.Loops;
using KatLang.Rendering;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The frozen SIGNED-ZERO EXTREMUM rule (September 2026; Decimal128 tier, C# only — Lean's
/// <c>Int</c> has one zero, so the rule is unobservable there).
///
/// <para>KatLang writes the two zeros <c>0</c> and <c>-0</c>: numeric literals are unsigned
/// and there is no unary <c>+</c>, so <c>+0</c> is a parse error. The zeros are ONE value to
/// <c>==</c>/<c>!=</c> and to the ordering operators (<c>-0 &lt; 0</c> is <c>false</c>), yet
/// <c>min</c> returns <c>-0</c> whenever a negative zero takes part in a zero minimum and
/// <c>max</c> returns <c>0</c> whenever an ordinary zero takes part in a zero maximum — in
/// every element order, only when zero IS the extremum, and always as one of the input
/// elements, so no sign is manufactured (<c>max((-0, -0))</c> stays <c>-0</c>). The owner is
/// IEEE 754 <c>minimum</c>/<c>maximum</c> (<c>Decimal128.Min</c>/<c>Max</c>) in
/// <c>Evaluator.EvalMinCounted</c>/<c>EvalMaxCounted</c>, the one implementation that the
/// synchronous dispatch, the async twin's dispatch, and the planned loop's fallback all
/// reach.</para>
///
/// <para>Which of several SAME-SIGNED equal values is returned (<c>1</c> vs <c>1.0</c>,
/// <c>-0</c> vs <c>-0.0</c>) is not part of the rule and is pinned here only as "one of the
/// input elements". Sign comparisons below always read <see cref="Decimal128.IsNegative"/> or
/// the sign- and quantum-faithful canonical text, never <see cref="Result.ValueComparer"/>,
/// which (like <c>==</c>) cannot see a zero's sign.</para>
/// </summary>
public class SignedZeroExtremaTests
{
    // ── Spellings: `0` and `-0`, and no unary plus ──────────────────────────────────────

    [Fact]
    public void ZeroSpellings_ZeroIsTheOrdinaryZero_AndMinusZeroNegatesIt()
    {
        var zero = Assert.IsType<Expr.Num>(Assert.Single(SourceProvenance.ParseValid("0").Root.Output));
        Assert.False(Decimal128.IsNegative(zero.Value));

        // Literals are unsigned: `-0` is prefix minus over the ordinary zero literal, and IEEE
        // negation gives the value its sign.
        var negated = Assert.IsType<Expr.Unary>(Assert.Single(SourceProvenance.ParseValid("-0").Root.Output));
        Assert.Equal(UnaryOp.Minus, negated.Op);
        Assert.False(Decimal128.IsNegative(Assert.IsType<Expr.Num>(negated.Operand).Value));

        Assert.False(Decimal128.IsNegative(SingleAtom("0")));
        Assert.True(Decimal128.IsNegative(SingleAtom("-0")));
    }

    [Theory]
    [InlineData("+0", 1)]
    [InlineData("1 + +0", 5)]
    [InlineData("max((+0, -0))", 6)]
    public void UnaryPlus_IsNotKatLangSyntax_SoPlusZeroIsNoSpelling(string source, int plusColumn)
    {
        var error = Assert.Single(
            SourceProvenance.ExpectFrontEndError(source),
            diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.UnexpectedToken, error.Code);
        Assert.Equal("Unexpected '+'.", error.Message);
        Assert.Equal(new SourceSpan(1, plusColumn, 1, plusColumn + 1), error.Span);
    }

    // ── Equality and ordering: one value ─────────────────────────────────────────────────

    [Theory]
    [InlineData("-0 == 0", true)]
    [InlineData("-0 != 0", false)]
    [InlineData("-0 < 0", false)]
    [InlineData("-0 <= 0", true)]
    [InlineData("-0 > 0", false)]
    [InlineData("-0 >= 0", true)]
    [InlineData("0 < -0", false)]
    [InlineData("0 <= -0", true)]
    [InlineData("0 > -0", false)]
    [InlineData("0 >= -0", true)]
    public void EqualityAndOrdering_TreatTheTwoZerosAsOneValue(string source, bool expected)
    {
        var result = Evaluator.RunCountedObserved(Program(source), enableOptimizations: false).Result;
        Assert.False(result.IsError, source);
        Assert.Equal(expected, Assert.IsType<Result.Bool>(result.Value.Value).Value);
    }

    // ── The extremum rule over every arrangement ─────────────────────────────────────────

    /// <summary>
    /// Element spellings: both signs of zero at two quanta, plus a nonzero neighbor on each
    /// side, so every sequence tests the rule where zero is and is not the extremum.
    /// </summary>
    private static readonly string[] Alphabet = ["-1", "-0", "0", "1", "-0.0", "0.0"];

    /// <summary>
    /// Every sequence of one to four elements over <see cref="Alphabet"/> — every ARRANGEMENT
    /// of every multiset, so agreement with the order-free oracle below IS permutation
    /// invariance — through the synchronous dispatch and the async twin's dispatch.
    /// </summary>
    [Fact]
    public async Task EveryArrangement_FollowsTheOrderFreeSignedZeroRule()
    {
        var failures = new List<string>();
        var programs = 0;
        foreach (var elements in Arrangements(Alphabet, maxLength: 4))
        {
            foreach (var builtin in (string[])["min", "max"])
            {
                programs++;
                var source = $"{builtin}(({string.Join(", ", elements)}))";
                var ast = Program(source);
                var sync = Neutral(Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result);
                var twin = Neutral(await AsyncEvaluationHarness.Complete(
                    Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache())));
                var expected = ExpectedExtremum(builtin, elements);

                if (sync != twin)
                    failures.Add($"{source}: sync {sync} but async twin {twin}");
                else if (!elements.Contains(sync))
                    failures.Add($"{source}: {sync} is not one of the input elements (a manufactured representation)");
                else if ((NumericValue(sync), sync.StartsWith('-')) != expected)
                    failures.Add($"{source}: {sync}, expected value {expected.Value} with negative sign {expected.Negative}");
            }
        }

        Assert.Equal(2 * (6 + 36 + 216 + 1296), programs);
        Assert.True(failures.Count == 0, $"{failures.Count} violation(s):\n" + string.Join("\n", failures.Take(25)));
    }

    /// <summary>
    /// The ORDER-FREE oracle, independent of <see cref="Decimal128.Min"/>/<see cref="Decimal128.Max"/>:
    /// the numeric extremum decides; only a ZERO extremum consults signs, and then only the
    /// signs of the zero elements that are present.
    /// </summary>
    private static (int Value, bool Negative) ExpectedExtremum(string builtin, IReadOnlyList<string> elements)
    {
        var values = elements.Select(NumericValue).ToList();
        var extremum = builtin == "min" ? values.Min() : values.Max();
        if (extremum != 0)
            return (extremum, extremum < 0);

        var zeros = elements.Where(element => NumericValue(element) == 0).ToList();
        return builtin == "min"
            ? (0, zeros.Any(zero => zero.StartsWith('-')))  // -0 whenever a negative zero takes part
            : (0, zeros.All(zero => zero.StartsWith('-'))); // 0 whenever an ordinary zero takes part
    }

    private static int NumericValue(string element) => element switch
    {
        "-1" => -1,
        "1" => 1,
        "-0" or "0" or "-0.0" or "0.0" => 0,
        _ => throw new ArgumentException($"not an alphabet element: {element}", nameof(element)),
    };

    private static IEnumerable<string[]> Arrangements(string[] alphabet, int maxLength)
    {
        IEnumerable<string[]> layer = [[]];
        for (var length = 1; length <= maxLength; length++)
        {
            layer = layer.SelectMany(prefix => alphabet.Select(element => (string[])[.. prefix, element])).ToList();
            foreach (var arrangement in layer)
                yield return arrangement;
        }
    }

    // ── Supply routes and execution strategies ───────────────────────────────────────────

    public static TheoryData<string, string> SupplyRoutes() => new()
    {
        // Direct sequence (singletons: a redundant group is the scalar itself).
        { "min((-0))", "-0" },
        { "max((-0))", "-0" },
        { "min((0))", "0" },
        // List literal and dot-call receiver.
        { "min([0, -0])", "-0" },
        { "max([-0, 0])", "0" },
        { "(0, -0).min", "-0" },
        { "(-0, 0).max", "0" },
        // A property-produced sequence, directly and as a receiver.
        { "A = 0, -0\nmin(A)", "-0" },
        { "A = -0, 0\nA.max", "0" },
        // Explicit spread supply.
        { "A = 0, -0\nB = -0, 0\nmin((A*, B*))", "-0" },
        { "A = -0\nmax((A*, 0))", "0" },
        // Selection, first/last, and an index result are value boundaries that keep the sign.
        { "A = (0, -0), (-0, 0)\nmin(A:0)", "-0" },
        { "A = (0, -0), (-0, 0)\n(A:1).max", "0" },
        { "max((first((-0, 1)), -0))", "-0" },
        { "min((0, last((1, -0))))", "-0" },
        { "A = -0, 5\nmin((0, A:0))", "-0" },
        // Callback-produced zeros: the maximum of negative zeros alone stays negative.
        { "Neg(x) = -x\nmax(map((0, 0), Neg))", "-0" },
        { "Neg(x) = -x\nmax((map((0, 0), Neg)*, 0))", "0" },
        { "Lo(x, acc) = min((x, acc))\nreduce((0, -0, 0), Lo, 0)", "-0" },
        { "M(p) = max(p)\nmap([(-0, 0), (0, -0), (-0, -0)], M)", "L[0, 0, -0]" },
        // Collecting parameters and forwarding.
        { "F(*xs) = min(xs)\nF(0, -0)", "-0" },
        { "F(*xs) = max(xs)\nG(*ys) = F(ys*)\nG(-0, 0)", "0" },
        // Builtin results as the collection.
        { "min(filter((0, -0, 3), {x < 1}))", "-0" },
        { "max(orderDesc((0, -0)))", "0" },
        // Computed zeros take their IEEE signs and then obey the same rule.
        { "min((0, -7 div 8))", "-0" },
        { "max((0 * -1, 0))", "0" },
    };

    [Theory]
    [MemberData(nameof(SupplyRoutes))]
    public async Task SupplyRoutes_KeepTheExtremumSign_OnEveryStrategy(string source, string expected)
    {
        var ast = Program(source);
        Assert.Equal(expected, Neutral(Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result));
        Assert.Equal(expected, Neutral(Evaluator.RunCountedObserved(ast, enableOptimizations: true).Result));

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        Assert.Equal(expected, Neutral(await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, cache))));
        Assert.Equal(0, cache.SyncAccesses);
    }

    /// <summary>
    /// A genuinely suspended async twin: every zero there is read through a property, so the
    /// twin awaits the cache seam (and yields to the thread pool) before the extremum runs.
    /// </summary>
    [Theory]
    [InlineData("Z = -0\nO = 0\nmin((O, Z))", "-0")]
    [InlineData("Z = -0\nO = 0\nmax((Z, O))", "0")]
    [InlineData("Z = -0\nmax((Z, Z))", "-0")]
    [InlineData("A = (0, -0), (-0, 0)\n(A:1).min", "-0")]
    public async Task AsyncTwin_AfterGenuineSuspension_KeepsTheExtremumSign(string source, string expected)
    {
        var ast = Program(source);
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var twin = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, cache));

        Assert.Equal(expected, Neutral(twin));
        Assert.Equal(Neutral(Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result), Neutral(twin));
        Assert.True(cache.AsyncAccesses > 0, "the zeros must be read through the async cache seam");
        Assert.NotEmpty(cache.ThreadHops);
        Assert.Equal(0, cache.SyncAccesses);
    }

    /// <summary>
    /// The planned loop evaluates <c>min</c>/<c>max</c> through its generic fallback, but it
    /// keeps its state in its own unboxed numeric representation and applies planned
    /// arithmetic to it (a unary over an unplannable call falls back as ONE expression, so
    /// the planned negation here is always over a state slot). A zero sign must survive both
    /// directions: an extremum result entering the planned state, and a planned <c>-0</c>
    /// entering an extremum.
    /// </summary>
    [Theory]
    [InlineData("S(x) = min((x, -0))\nrepeat(S, 3, 0)", "-0")]
    [InlineData("S(x) = max((x, 0))\nrepeat(S, 3, -0)", "0")]
    [InlineData("S(x) = max((-0, x))\nrepeat(S, 3, -0)", "-0")]
    [InlineData("S(x) = -x\nrepeat(S, 1, max((0, -0)))", "-0")]
    [InlineData("S(x, y) = min((x, y)), -y\nrepeat(S, 2, 0, 0)", "S[-0, 0]")]
    [InlineData("S(x, y) = max((x, y)), -y\nrepeat(S, 2, -0, -0)", "S[0, -0]")]
    [InlineData("S(x, y) = min((y, x)), max((x, y))\nrepeat(S, 3, 0, -0)", "S[-0, 0]")]
    [InlineData("S(x, n) = max((x, 0)), n - 1, n > 1\nwhile(S, -0, 3)", "S[0, 1]")]
    public void PlannedLoops_CarryTheExtremumSignLikeTheGenericPath(string source, string expected)
    {
        var ast = Program(source);

        var plannedDiagnostics = new LoopOptimizationDiagnostics();
        var planned = Evaluator.RunCountedObserved(ast, enableOptimizations: true, loopDiagnostics: plannedDiagnostics).Result;
        var genericDiagnostics = new LoopOptimizationDiagnostics();
        var generic = Evaluator.RunCountedObserved(ast, enableOptimizations: false, loopDiagnostics: genericDiagnostics).Result;

        Assert.True(plannedDiagnostics.OptimizedLoopHits > 0, "the loop must actually run planned");
        Assert.Equal(0, genericDiagnostics.OptimizedLoopHits);
        Assert.Equal(expected, Neutral(generic));
        Assert.Equal(expected, Neutral(planned));
    }

    // ── Presentation: `0` and `-0`, never `+0` ───────────────────────────────────────────

    [Theory]
    [InlineData("min((0, -0))", "-0")]
    [InlineData("min((-0, 0))", "-0")]
    [InlineData("max((0, -0))", "0")]
    [InlineData("max((-0, 0))", "0")]
    [InlineData("max((-0, -0))", "-0")]
    [InlineData("min((0, 0))", "0")]
    public void Presentation_SpellsTheResultZeroOrMinusZero_AndTheTextReadsBack(string source, string text)
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(text, success.ToDisplayString());
        var atom = Assert.Single(success.Atoms);
        Assert.Equal(text.StartsWith('-'), Decimal128.IsNegative(atom));
        Assert.Equal(text, ValueTextRenderer.FormatNumberInvariant(atom));

        var flat = Evaluator.RunFlat(Program(source));
        Assert.False(flat.IsError);
        Assert.Equal(Decimal128.IsNegative(atom), Decimal128.IsNegative(Assert.Single(flat.Value)));

        var converted = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"{source}.string"));
        Assert.Equal(text, Assert.IsType<Result.Str>(converted.Value).Value);

        // The displayed text is itself KatLang source for the same zero; `+0` never is.
        var reread = Assert.Single(Assert.IsType<RunResult.Success>(KatLangEngine.Run(text)).Atoms);
        Assert.True(reread == atom);
        Assert.Equal(Decimal128.IsNegative(atom), Decimal128.IsNegative(reread));
    }

    [Theory]
    [InlineData("DisplayDecimals = 2\nmax((-0, 0))", "0")]
    [InlineData("DisplayDecimals = 2\nmin((0, -0))", "-0")]
    [InlineData("DisplayDecimals = 2\nmax((-0.0, 0.0))", "0.00")]
    [InlineData("DisplayDecimals = 2\nmin((0.0, -0.0))", "-0.00")]
    public void DisplayDecimals_KeepsTheExtremumSign_WithoutAPlusSign(string source, string display)
        => Assert.Equal(display, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());

    // ── Non-finite neighbors keep their IEEE extremum behavior ───────────────────────────

    [Theory]
    [InlineData("min((0, -0, Math.Sqrt(-1)))", "NaN")]
    [InlineData("max((Math.Sqrt(-1), 0, -0))", "NaN")]
    [InlineData("min((-0, 0, 9e6144 * 10))", "-0")]
    [InlineData("max((-0, 0, 0 - 9e6144 * 10))", "0")]
    [InlineData("min((0 - 9e6144 * 10, -0, 0))", "-Infinity")]
    [InlineData("max((0, -0, 9e6144 * 10))", "Infinity")]
    public void NonFiniteNeighbors_KeepTheirIeeeExtremumBehavior(string source, string expected)
        => Assert.Equal(expected, Neutral(Evaluator.RunCountedObserved(Program(source), enableOptimizations: false).Result));

    // ── Helpers ──────────────────────────────────────────────────────────────────────────

    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static Decimal128 SingleAtom(string source)
    {
        var result = Evaluator.RunCountedObserved(Program(source), enableOptimizations: false).Result;
        Assert.False(result.IsError, source);
        return Assert.IsType<Result.Atom>(result.Value.Value).Value;
    }

    /// <summary>The sign- and quantum-faithful neutral text of a successful result.</summary>
    private static string Neutral(EvalResult<Evaluator.CountedResult> result)
    {
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        return SemanticExplorerHarness.Neutral(result.Value.Value);
    }
}
