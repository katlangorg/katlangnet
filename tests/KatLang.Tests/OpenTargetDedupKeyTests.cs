namespace KatLang.Tests;

/// <summary>
/// The dedup identity of a written <c>open</c> target has ONE owner,
/// <see cref="Evaluator.OpenTargetDedupKey"/>, consumed by runtime open
/// resolution (<c>Evaluator.ResolveAllOpens</c>) and by elaborated-scope lookup
/// (<c>ElaboratedPropertyScope.GetResolvedOpenProviders</c>, the front end's and
/// the editor's provider source). These tests pin the relation itself — named
/// targets keyed by their open spelling independent of position, inline targets
/// keyed by position independent of spelling, every other form total through its
/// rendered spelling — and the observable consequences both consumers must share:
/// first-occurrence-wins dedup of repeated named targets (including their order),
/// never-deduplicated inline targets, ordinal (case-sensitive) comparison, and
/// per-scope positional identity. A structural pin keeps a second local spelling
/// of the key from regrowing in either consumer.
/// </summary>
public class OpenTargetDedupKeyTests
{
    // ── the key relation ───────────────────────────────────────────────────────

    [Fact]
    public void NamedTargets_AreKeyedBySpelling_IndependentOfPosition()
    {
        var resolve = new Expr.Resolve("Lib");
        Assert.Equal("Lib", Evaluator.OpenTargetDedupKey(resolve, 0));
        Assert.Equal("Lib", Evaluator.OpenTargetDedupKey(resolve, 7));

        // A real elaborated dotted open target renders as its dotted path.
        var root = SourceProvenance.ParseValid(
            "Lib = {\n    public S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S\n    X\n}\nA").Root;
        var dotted = Assert.IsType<Expr.DotCall>(Assert.Single(PropertyAlgorithm(root, "A").Opens));
        Assert.Equal("Lib.S", Evaluator.OpenTargetDedupKey(dotted, 0));
        Assert.Equal("Lib.S", Evaluator.OpenTargetDedupKey(dotted, 4));
        Assert.Equal(Evaluator.OpenExprName(dotted), Evaluator.OpenTargetDedupKey(dotted, 4));
    }

    [Fact]
    public void InlineTargets_AreKeyedByPosition_IndependentOfSpelling()
    {
        var block = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], []));
        Assert.Equal("(inline#0)", Evaluator.OpenTargetDedupKey(block, 0));
        // The SAME node at another position is another provider.
        Assert.Equal("(inline#1)", Evaluator.OpenTargetDedupKey(block, 1));

        var capture = new Expr.Capture(OutputBundle.Empty);
        Assert.Equal("(inline#2)", Evaluator.OpenTargetDedupKey(capture, 2));
    }

    [Fact]
    public void EveryOtherForm_IsKeyedByItsRenderedOpenSpelling()
    {
        // The generic arm is deliberately total: ResolveAllOpens spells an illegal
        // target's BadOpenForm diagnostic with this key, so no open form may throw.
        var number = new Expr.Num(42);
        Assert.Equal(Evaluator.OpenExprName(number), Evaluator.OpenTargetDedupKey(number, 0));

        var spread = new Expr.SequenceSpread(new Expr.Resolve("Lib"));
        Assert.Equal(Evaluator.OpenExprName(spread), Evaluator.OpenTargetDedupKey(spread, 0));
        Assert.Equal(Evaluator.OpenTargetDedupKey(spread, 0), Evaluator.OpenTargetDedupKey(spread, 5));
    }

    // ── both consumers, one relation ───────────────────────────────────────────

    [Fact]
    public void RepeatedNamedTarget_IsOneProviderForBothConsumers()
    {
        const string source = "Lib = {\n    public X = 101\n}\nA = {\n    open Lib, Lib, Lib\n    X\n}\nA";
        Assert.Equal("ok raw=101 n=1", SemanticExplorerHarness.Observe("dedup.named", source).Neutral);

        var root = SourceProvenance.ParseValid(source).Root;
        var providers = ProvidersOf(root, "A");
        Assert.Single(providers);
        Assert.Same(PropertyAlgorithm(root, "Lib"), providers[0].Target);
    }

    [Fact]
    public void RepeatedDottedTarget_IsOneProviderForBothConsumers()
    {
        const string source = "Lib = {\n    public S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S, Lib.S\n    X\n}\nA";
        Assert.Equal("ok raw=101 n=1", SemanticExplorerHarness.Observe("dedup.dotted", source).Neutral);

        var root = SourceProvenance.ParseValid(source).Root;
        var providers = ProvidersOf(root, "A");
        Assert.Single(providers);
        Assert.Same(PropertyAlgorithm(PropertyAlgorithm(root, "Lib"), "S"), providers[0].Target);
    }

    [Fact]
    public void RepeatedNamedTarget_KeepsItsFirstPosition()
    {
        // `open Lib, Other, Lib`: the second Lib is dropped, so the provider order is
        // [Lib, Other] — a last-occurrence-wins dedup would yield [Other, Lib].
        const string source = "Lib = {\n    public X = 101\n}\nOther = {\n    public Y = 202\n}\nA = {\n    open Lib, Other, Lib\n    X + Y\n}\nA";
        Assert.Equal("ok raw=303 n=1", SemanticExplorerHarness.Observe("dedup.order", source).Neutral);

        var root = SourceProvenance.ParseValid(source).Root;
        var providers = ProvidersOf(root, "A");
        Assert.Equal(2, providers.Count);
        Assert.Same(PropertyAlgorithm(root, "Lib"), providers[0].Target);
        Assert.Same(PropertyAlgorithm(root, "Other"), providers[1].Target);
    }

    [Fact]
    public void Runtime_ResolvesDedupedTargetsInFirstOccurrenceOrder()
    {
        // Two illegal builtin targets bracket a valid one: `open count, Lib, sum, count`
        // dedups to [count, Lib, sum], so the FIRST failure the runtime reports names
        // `count`. Keeping the last occurrence instead would order [Lib, sum, count]
        // and report `sum` first.
        const string source = "Lib = {\n    public X = 101\n}\nA = {\n    open count, Lib, sum, count\n    X\n}\nA";
        Assert.Equal("err illegalInOpen", SemanticExplorerHarness.Observe("dedup.runtimeOrder", source).Neutral);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var message = Assert.Single(failure.Errors).Message;
        Assert.Contains("count", message, StringComparison.Ordinal);
        Assert.DoesNotContain("sum", message, StringComparison.Ordinal);
    }

    [Fact]
    public void InlineTargets_AreNeverDeduplicated_ForBothConsumers()
    {
        // Two structurally identical inline blocks are two providers: the runtime
        // reports the ambiguity by their positional keys, and the elaborated scope
        // resolves two distinct provider targets.
        const string source = "A = {\n    open { public X = 101 }, { public X = 101 }\n    X\n}\nA";
        Assert.Equal("err ambiguousOpen", SemanticExplorerHarness.Observe("dedup.inline", source).Neutral);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var ambiguity = Assert.Single(failure.Errors.Select(static error => error.Source).OfType<EvalError.AmbiguousOpen>());
        Assert.Equal("X", ambiguity.Name);
        Assert.Equal(["(inline#0)", "(inline#1)"], ambiguity.Providers);

        var root = SourceProvenance.ParseValid(source).Root;
        var providers = ProvidersOf(root, "A");
        Assert.Equal(2, providers.Count);
        Assert.NotSame(providers[0].Target, providers[1].Target);
    }

    [Fact]
    public void NamedAndInlineTargets_MixWithoutCrossDedup()
    {
        const string source = "Lib = {\n    public X = 101\n}\nA = {\n    open Lib, { public Y = 202 }, Lib\n    X + Y\n}\nA";
        Assert.Equal("ok raw=303 n=1", SemanticExplorerHarness.Observe("dedup.mixed", source).Neutral);

        var root = SourceProvenance.ParseValid(source).Root;
        var providers = ProvidersOf(root, "A");
        Assert.Equal(2, providers.Count);
        Assert.Same(PropertyAlgorithm(root, "Lib"), providers[0].Target);
        Assert.Single(providers[1].Target.Properties, static property => property.Name == "Y");
    }

    [Fact]
    public void Keys_CompareOrdinally_SoCaseDistinctTargetsAreDistinctProviders()
    {
        const string source = "Lib = {\n    public X = 101\n}\nlib = {\n    public X = 202\n}\nA = {\n    open Lib, lib\n    X\n}\nA";
        Assert.Equal("err ambiguousOpen", SemanticExplorerHarness.Observe("dedup.case", source).Neutral);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var ambiguity = Assert.Single(failure.Errors.Select(static error => error.Source).OfType<EvalError.AmbiguousOpen>());
        Assert.Equal(["Lib", "lib"], ambiguity.Providers);

        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(2, ProvidersOf(root, "A").Count);
    }

    [Fact]
    public void InlineTargets_HavePerScopePositionalIdentity()
    {
        // Position 0 in A and position 0 in B are different scopes' providers.
        const string source = "A = {\n    open { public X = 101 }\n    X\n}\nB = {\n    open { public X = 202 }\n    X\n}\nA, B";
        Assert.Equal("ok raw=S[101, 202] n=2", SemanticExplorerHarness.Observe("dedup.scopes", source).Neutral);

        var root = SourceProvenance.ParseValid(source).Root;
        var a = Assert.Single(ProvidersOf(root, "A"));
        var b = Assert.Single(ProvidersOf(root, "B"));
        Assert.NotSame(a.Target, b.Target);
    }

    // ── structural closure: one owner, two callers ─────────────────────────────

    [Fact]
    public void ProductionSource_SpellsTheDedupKeyExactlyOnce()
    {
        var sources = ReadProductionSources();

        // The positional inline key literal exists in exactly one production file.
        var filesWithInlineKey = sources
            .Where(static file => file.Text.Contains("inline#", StringComparison.Ordinal))
            .Select(static file => file.Name)
            .ToList();
        Assert.Equal(["Evaluator.cs"], filesWithInlineKey);

        var evaluator = sources.Single(static file => file.Name == "Evaluator.cs").Text;
        Assert.Equal(1, CountOccurrences(evaluator, "inline#"));
        Assert.Equal(1, CountOccurrences(evaluator, "internal static string OpenTargetDedupKey("));

        // Runtime open resolution consumes the helper rather than respelling it.
        var resolveStart = evaluator.IndexOf("ResolveAllOpens(", StringComparison.Ordinal);
        var resolveEnd = evaluator.IndexOf("LookupOpens(", resolveStart, StringComparison.Ordinal);
        Assert.True(resolveStart >= 0 && resolveEnd > resolveStart, "Expected the ResolveAllOpens .. LookupOpens region in Evaluator.cs.");
        Assert.Contains("OpenTargetDedupKey(openExpr, i)", evaluator[resolveStart..resolveEnd], StringComparison.Ordinal);

        // Elaborated lookup consumes the same helper and defines none of its own.
        var lookup = sources.Single(static file => file.Name == "ElaboratedScopeLookup.cs").Text;
        Assert.Contains("Evaluator.OpenTargetDedupKey(", lookup, StringComparison.Ordinal);
        Assert.DoesNotContain("static string OpenTargetDedupKey", lookup, StringComparison.Ordinal);
    }

    // ── helpers ────────────────────────────────────────────────────────────────

    private static Algorithm PropertyAlgorithm(Algorithm owner, string name)
        => owner.Properties.Single(property => property.Name == name).Value;

    /// <summary>
    /// The resolved open providers of root property <paramref name="name"/>'s
    /// body, through the same chain construction the front end uses (the body's
    /// level over the root level).
    /// </summary>
    private static IReadOnlyList<ResolvedOpenProvider> ProvidersOf(Algorithm root, string name)
    {
        var rootScope = ElaboratedScopeLookup.CreateScope(root);
        var bodyScope = ElaboratedScopeLookup.CreateScope(PropertyAlgorithm(root, name), rootScope);
        return bodyScope.GetResolvedOpenProviders();
    }

    private static int CountOccurrences(string text, string needle)
    {
        var count = 0;
        for (var index = text.IndexOf(needle, StringComparison.Ordinal);
            index >= 0;
            index = text.IndexOf(needle, index + needle.Length, StringComparison.Ordinal))
        {
            count++;
        }

        return count;
    }

    private static IReadOnlyList<(string Name, string Text)> ReadProductionSources()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory); current is not null; current = current.Parent)
        {
            var candidate = Path.Combine(current.FullName, "src", "KatLang");
            if (!File.Exists(Path.Combine(candidate, "Evaluator.cs")))
                continue;

            return Directory
                .EnumerateFiles(candidate, "*.cs", SearchOption.AllDirectories)
                .Where(static path => !path.Contains($"{Path.DirectorySeparatorChar}obj{Path.DirectorySeparatorChar}", StringComparison.Ordinal)
                    && !path.Contains($"{Path.DirectorySeparatorChar}bin{Path.DirectorySeparatorChar}", StringComparison.Ordinal))
                .Select(static path => (Path.GetFileName(path), File.ReadAllText(path)))
                .ToList();
        }

        throw new InvalidOperationException("src/KatLang was not found above the test output directory.");
    }
}
