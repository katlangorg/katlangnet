namespace KatLang.Tests;

/// <summary>
/// THE BARE ROOT CALLABLE ROW is one static decision shared by the signature analysis and the rewrite
/// (<c>ImplicitArgumentResolver.BareRootRowCallable</c>). The analysis keeps every bare root row that names a static
/// callable out of the root's lifting equations. The rewrite preserves only the subset whose callee requires supplied
/// arguments or is an unnameable family (THE ROOT CLAUSE, <c>ShouldPreserveBareRootRow</c>). The rows in between, a bare
/// root reference to a static callable that ACCEPTS zero supplied arguments, are where the two predicates disagree. The
/// rewrite walks and rewrites them as ordinary rows, so they must lift nothing there. The selection invariant
/// (<c>RequireSelectedComposition</c>) fails loudly on any run where they do, so every row below is also a check of the
/// invariant. Each row covers one callee category, and each runs on the six evaluation routes, on a host-built AST and
/// beside a root formula that does lift.
/// </summary>
public class BareRootRowPredicateTests
{
    private const string Inc = "Inc(x) = x + 1\n";

    /// <summary>
    /// The disagreement set: (id, the root's declarations, the bare root row, the pinned outcome). Each row names a static
    /// callable that accepts zero supplied arguments, which the analysis excludes and the rewrite does not preserve.
    /// </summary>
    public static TheoryData<string, string, string, string> ZeroArgumentRows => new()
    {
        { "property", "K = 5\n", "K", "ok 5" },
        { "collecting-only", "Roll(*xs) = 7\n", "Roll", "ok 7" },
        { "alias", "L = 5\nK = L\n", "K", "ok 5" },
        // An inferring body whose SELECTED signature accepts zero arguments: only the final signature tells.
        { "selected-formula", "M = 5\nK = M + 1\n", "K", "ok 6" },
        { "dotted", "Lib = { public K = 5 }\n", "Lib.K", "ok 5" },
        { "dotted-two-edges", "Lib = { public S = { public K = 5 }\n 0 }\n", "Lib.S.K", "ok 5" },
        { "dotted-selected-formula", "Lib = { M = 5\n public K = M + 1 }\n", "Lib.K", "ok 6" },
        { "opened", "open Lib\nLib = { public K = 5 }\n", "K", "ok 5" },
        { "block-head", "", "{ public K = 5\n 0 }.K", "ok 5" },
        { "math-constant", "", "Math.Pi", "ok 3.141592653589793238462643383279503" },
    };

    /// <summary>
    /// The agreement set: the same categories with a callee that REQUIRES supplied arguments, which both phases keep out
    /// of the root's lifting. The row stays the callee's own zero-argument demand.
    /// </summary>
    public static TheoryData<string, string, string, string> PreservedRows => new()
    {
        { "property", Inc, "Inc", "eval ArityMismatch" },
        { "alias", Inc + "A = Inc\n", "A", "eval ArityMismatch" },
        { "selected-formula", Inc + "K = Inc + 0\n", "K", "eval ArityMismatch" },
        { "dotted", "Lib = { public Inc(x) = x + 1 }\n", "Lib.Inc", "eval ArityMismatch" },
        { "opened", "open Lib\nLib = { public Inc(x) = x + 1 }\n", "Inc", "eval ArityMismatch" },
        { "builtin", "", "count", "eval ArityMismatch" },
        { "math-member", "", "Math.Abs", "eval ArityMismatch" },
        { "family", "F(0) = 0\nF(n) = n + 1\n", "F", "eval NoMatchingBranch" },
        { "unnameable-family", "S(1) = 1\nS(-1) = -1\n", "S", "eval NoMatchingBranch" },
    };

    // ── The observer ──────────────────────────────────────────────────────────────────────────

    /// <summary>A program's outcome: <c>front &lt;sorted codes&gt;</c>, or the six-route observation (every route agreeing).</summary>
    private static async Task<string> Outcome(string source)
    {
        if (KatLangEngine.Run(source) is RunResult.ParseFailure failure)
            return "front " + string.Join(",", failure.Errors.Select(static error => error.Code.ToString()).Distinct().Order(StringComparer.Ordinal));
        return RepeatedNameConstraintTests.Rendered(await RepeatedNameConstraintTests.OnEveryRouteAsync(source));
    }

    /// <summary>An evaluation failure's kind (<c>eval &lt;code&gt;</c>); every other outcome as rendered.</summary>
    private static string Class(string outcome)
        => outcome.StartsWith("err ", StringComparison.Ordinal) ? "eval " + outcome[4..outcome.IndexOf(':', StringComparison.Ordinal)]
            : outcome;

    /// <summary>The elaborated root and the diagnostics of a parser-built program.</summary>
    private static (Algorithm.User Root, IReadOnlyList<Diagnostic> Diagnostics) Elaborate(string source)
    {
        var parsed = Parser.Parse(source);
        return (Assert.IsType<Algorithm.User>(parsed.Root), parsed.Diagnostics);
    }

    /// <summary>The root's lifted parameter names, in signature order.</summary>
    private static string[] RootParameters(Algorithm.User root)
        => root.ParameterPatterns.Select(static pattern => pattern.DisplayName).ToArray();

    // ── The disagreement set ──────────────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(ZeroArgumentRows))]
    public async Task AZeroArgumentBareRootRow_IsItsCachedValue_OnEveryRoute(string id, string declarations, string row, string expected)
    {
        var outcome = await Outcome(declarations + row);
        Assert.True(expected == outcome, $"{id}\nexpected: {expected}\nactual:   {outcome}");
    }

    /// <summary>
    /// The rewrite rewrites the row as an ordinary row and lifts nothing from it: the root gains no parameter, the row is
    /// no synthesized call, and no diagnostic is reported.
    /// </summary>
    [Theory]
    [MemberData(nameof(ZeroArgumentRows))]
    public void AZeroArgumentBareRootRow_LiftsNothing(string id, string declarations, string row, string expected)
    {
        _ = expected;
        var (root, diagnostics) = Elaborate(declarations + row);
        Assert.True(diagnostics.Count == 0, $"{id}: {string.Join("; ", diagnostics)}");
        Assert.True(RootParameters(root).Length == 0, $"{id}: root gained ({string.Join(", ", RootParameters(root))})");
        Assert.IsNotType<Expr.Call>(Assert.Single(root.Output));
    }

    /// <summary>
    /// Beside a root formula that lifts, the excluded row adds nothing to the root's dependencies: the root lifts exactly
    /// the formula's <c>x</c>, before and after the row, which is the dependency list the selection composed (a row
    /// that added a callee would fail the selection invariant instead).
    /// </summary>
    [Theory]
    [MemberData(nameof(ZeroArgumentRows))]
    public void AZeroArgumentBareRootRow_BesideALiftingFormula_AddsNoDependency(string id, string declarations, string row, string expected)
    {
        _ = expected;
        foreach (var rows in new[] { $"{row}, Inc + 0", $"Inc + 0, {row}" })
        {
            var (root, diagnostics) = Elaborate(Inc + declarations + rows);
            Assert.True(new[] { "x" }.SequenceEqual(RootParameters(root)), $"{id} / {rows}: root lifted ({string.Join(", ", RootParameters(root))})");
            Assert.DoesNotContain(diagnostics, static diagnostic => diagnostic.Message.Contains("analysis and the rewrite", StringComparison.Ordinal));
        }
    }

    // ── The agreement set ─────────────────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(PreservedRows))]
    public async Task ABareRootRowThatRequiresArguments_IsItsOwnDemand_OnEveryRoute(string id, string declarations, string row, string expected)
    {
        var outcome = Class(await Outcome(declarations + row));
        Assert.True(expected == outcome, $"{id}\nexpected: {expected}\nactual:   {outcome}");
    }

    [Theory]
    [MemberData(nameof(PreservedRows))]
    public void ABareRootRowThatRequiresArguments_IsPreserved(string id, string declarations, string row, string expected)
    {
        _ = expected;
        var (root, diagnostics) = Elaborate(declarations + row);
        Assert.True(diagnostics.Count == 0, $"{id}: {string.Join("; ", diagnostics)}");
        Assert.True(RootParameters(root).Length == 0, $"{id}: root gained ({string.Join(", ", RootParameters(root))})");
        Assert.IsNotType<Expr.Call>(Assert.Single(root.Output));
    }

    /// <summary>A preserved row beside a lifting formula: the root lifts the formula's <c>x</c> and nothing from the row.</summary>
    [Theory]
    [MemberData(nameof(PreservedRows))]
    public void ABareRootRowThatRequiresArguments_BesideALiftingFormula_AddsNoDependency(string id, string declarations, string row, string expected)
    {
        _ = expected;
        var formula = declarations.StartsWith(Inc, StringComparison.Ordinal) ? "" : Inc;
        foreach (var rows in new[] { $"{row}, Inc + 0", $"Inc + 0, {row}" })
        {
            var (root, _) = Elaborate(formula + declarations + rows);
            Assert.True(new[] { "x" }.SequenceEqual(RootParameters(root)), $"{id} / {rows}: root lifted ({string.Join(", ", RootParameters(root))})");
            Assert.IsNotType<Expr.Call>(root.Output[rows.StartsWith(row, StringComparison.Ordinal) ? 0 : 1]);
        }
    }

    // ── A host-built AST ──────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The same decisions on an AST no parser built, through parameter detection and the resolver directly: a bare root
    /// <c>K</c> (zero arguments) and <c>Lib.K</c> stay as written, and a bare root <c>F</c> (requires <c>x</c>) is
    /// preserved — each row unchanged, the root unlifted, no diagnostic.
    /// </summary>
    [Fact]
    public void AHostBuiltRoot_MakesTheSameDecisions()
    {
        var zero = new Algorithm.User(null, [], [], [], [new Expr.Num(5)]);
        var requires = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Resolve("x")]) { HasExplicitParameterList = true };
        var library = new Algorithm.User(null, [], [], [new Property("K", zero, IsPublic: true)], [new Expr.Num(0)]);
        Expr[] rows = [new Expr.Resolve("K"), new Expr.DotCall(new Expr.Resolve("Lib"), "K", null), new Expr.Resolve("F")];
        foreach (var row in rows)
        {
            var root = new Algorithm.User(
                null, [], [], [new Property("K", zero), new Property("F", requires), new Property("Lib", library)], [row]);
            var detected = ParameterDetector.Detect(root);
            Assert.Empty(detected.Diagnostics);
            var diagnostics = new DiagnosticBag();
            var resolved = Assert.IsType<Algorithm.User>(ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics));
            Assert.Empty(diagnostics);
            Assert.Empty(resolved.ParameterPatterns);
            var output = Assert.Single(resolved.Output);
            Assert.IsNotType<Expr.Call>(output);
            Assert.Equal(row.GetType(), output.GetType());
        }
    }
}
