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
        // Since the final audit (September 2026) the front end refuses every builtin
        // target eagerly (one IllegalInOpen per written target), so the runtime's
        // first-occurrence order is pinned over the RECOVERY tree it elaborates anyway.
        const string source = "Lib = {\n    public X = 101\n}\nA = {\n    open count, Lib, sum, count\n    X\n}\nA";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.Equal(3, parsed.Diagnostics.Count(d => d.Code == DiagnosticCode.IllegalInOpen));

        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsError);
        var innermost = result.Error;
        while (innermost is EvalError.WithContext context) innermost = context.Inner;
        var illegal = Assert.IsType<EvalError.IllegalInOpen>(innermost);
        Assert.Contains("count", illegal.Reason, StringComparison.Ordinal);
        Assert.DoesNotContain("sum", illegal.Reason, StringComparison.Ordinal);
    }

    /// <summary>The innermost evaluator error, with context frames unwrapped (a fallback's ambiguity is reported inside its call).</summary>
    private static EvalError? InnermostError(EvalError? error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    [Fact]
    public void InlineTargets_AreNeverDeduplicated_ForBothConsumers()
    {
        // Two structurally identical inline blocks are two declarations, so two providers
        // (Q-19 D-I): a WRITTEN X both provide is the front end's ambiguity (Q-29 A-U); a
        // lookup only evaluation decides (a fallback on a parameter receiver) is the
        // runtime's, reported by the blocks' positional names; and the elaborated scope
        // resolves two distinct provider targets.
        const string written = "A = {\n    open { public X = 101 }, { public X = 101 }\n    X\n}\nA";
        Assert.Equal("parseError", SemanticExplorerHarness.Observe("dedup.inline", written).Neutral);
        Assert.Equal(DiagnosticCode.AmbiguousOpen, Assert.Single(SourceProvenance.ExpectFrontEndError(written)).Code);

        const string source = "A = {\n    open { public X(v) = 101 }, { public X(v) = 101 }\n    K(q) = q.X\n    K(10)\n}\nA";
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var ambiguity = Assert.Single(failure.Errors.Select(static error => InnermostError(error.Source)).OfType<EvalError.AmbiguousOpen>());
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
        // `Lib` and `lib` are two declarations: a WRITTEN X both provide is the front end's
        // ambiguity (Q-29 A-U), and a lookup only evaluation decides is the runtime's.
        const string written = "Lib = {\n    public X = 101\n}\nlib = {\n    public X = 202\n}\nA = {\n    open Lib, lib\n    X\n}\nA";
        Assert.Equal("parseError", SemanticExplorerHarness.Observe("dedup.case", written).Neutral);
        Assert.Equal(DiagnosticCode.AmbiguousOpen, Assert.Single(SourceProvenance.ExpectFrontEndError(written)).Code);

        const string source = "Lib = {\n    public X(v) = 101\n}\nlib = {\n    public X(v) = 202\n}\nA = {\n    open Lib, lib\n    K(q) = q.X\n    K(10)\n}\nA";
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var ambiguity = Assert.Single(failure.Errors.Select(static error => InnermostError(error.Source)).OfType<EvalError.AmbiguousOpen>());
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
        // Keep the historical acceptance identity while replacing its retired source-text pin.
        // Q2 must deduplicate language providers and repeated reads must reuse solved work.
        const string source = "Lib={public X=7\n0}\nAlias=Lib\nF={open Lib,Lib,Alias\nX}\n0";
        var raw = SourceProvenance.ParseSyntaxValidRoot(source);
        var operation = StaticStructureAdmission.Create(raw).Operation;
        var observations = new FrontEndTraversalObservations();
        operation.Queries.Observations = observations;
        var f = operation.ContextOf(operation.Root, PropertyAlgorithm(raw, "F"));
        var query = StaticQueryKey.OpenProviders(f, StaticCycleCheck.Formation);
        var providers = Assert.IsType<StaticScopeKey[]>(operation.Read(query).Data);
        var provider = Assert.Single(providers);
        Assert.Same(PropertyAlgorithm(raw, "Lib"), operation.SourceOf(provider));
        Assert.Equal(StaticFactKind.Declaration, operation.Binding(f, "X").Kind);
        Assert.Equal(1, observations.StaticOpenIndexBuilds);
        Assert.Equal(1, observations.StaticOpenIndexMemberVisits);
        var evaluations = operation.Queries.Statistics.Evaluations;
        var targets = observations.StaticOpenTargetComputations;
        for (var repeat = 0; repeat < 100; repeat++)
        {
            Assert.Same(providers, operation.Read(query).Data);
            Assert.Equal(StaticFactKind.Declaration, operation.Binding(f, "X").Kind);
        }
        Assert.Equal(evaluations, operation.Queries.Statistics.Evaluations);
        Assert.Equal(targets, observations.StaticOpenTargetComputations);
        Assert.Equal(1, observations.StaticOpenIndexBuilds);
        Assert.Equal(1, observations.StaticOpenIndexMemberVisits);
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

}
