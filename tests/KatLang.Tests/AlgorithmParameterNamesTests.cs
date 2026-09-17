namespace KatLang.Tests;

/// <summary>
/// <see cref="Algorithm.Params"/> is the LIVE name projection of <see cref="Algorithm.Parameters"/>
/// (Lean: <c>Algorithm.params</c>): computed from the current parameter list on every read and
/// never stored on the record, because a host-built algorithm keeps its caller-owned
/// <c>Parameters</c> list and the public AST reads through to it (the established
/// collection-ownership behavior <c>LoopStrategyPreparationTests</c> pins). The September 2026
/// <c>Params</c> investigation measured the projection at 1–4 reads per evaluator operation and
/// removed its cost instead of caching it: a zero-parameter algorithm's projection allocates
/// nothing, a parameterized one allocates exactly one array, and every count-only consumer reads
/// <c>Parameters.Count</c> — the same number by construction, which the corpus walk below pins.
/// </summary>
public class AlgorithmParameterNamesTests
{
    [Fact]
    public void Params_IsTheOrderedNameProjection_OnEveryVariant()
    {
        // Order and duplicates are the list's own: the projection neither sorts nor deduplicates.
        var user = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("b"), new ParameterDeclaration("a"), new ParameterDeclaration("b")],
            Opens: [],
            Properties: [],
            Output: [new Expr.Num(1)]);
        Assert.Equal(["b", "a", "b"], user.Params);
        Assert.Equal(user.Parameters.Count, user.Params.Count);

        var collecting = new Algorithm.User(null, [], [], [], [new Expr.Num(1)])
            .WithParameterPatterns([new CaptureParameterPattern("head"), new CaptureParameterPattern("rest", Kind: ParameterKind.Collecting)]);
        Assert.Equal(["head", "rest"], collecting.Params);

        var family = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.Bind("x"), new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))]);
        Assert.Empty(family.Params);
        Assert.Empty(new Algorithm.Builtin(BuiltinId.count).Params);
    }

    [Fact]
    public void Params_ReadsThroughToTheCallerOwnedParameterList()
    {
        // The public AST retains the host's list instance. Every read reflects the list as it
        // is NOW — a same-count rename, growth, and emptying alike — and a copy wired earlier
        // (the evaluator's `with { Parent = ... }` view) sees the same live list. Any
        // representation that stored the names on the record, at construction or on first
        // read, would report a stale projection on at least one of these assertions.
        var parameters = new List<ParameterDeclaration> { new("x") };
        var algorithm = new Algorithm.User(null, parameters, [], [], [new Expr.Num(1)]);
        var wiredCopy = algorithm with { Parent = new ScopeCtx(null, [], []) };
        Assert.Equal(["x"], algorithm.Params);
        Assert.Equal(["x"], wiredCopy.Params);

        parameters[0] = new ParameterDeclaration("y");
        Assert.Equal(["y"], algorithm.Params);
        Assert.Equal(["y"], wiredCopy.Params);

        parameters.Add(new ParameterDeclaration("z"));
        Assert.Equal(["y", "z"], algorithm.Params);
        Assert.Equal(["y", "z"], wiredCopy.Params);
        Assert.Equal(2, algorithm.Parameters.Count);

        parameters.Clear();
        Assert.Empty(algorithm.Params);
        Assert.Empty(wiredCopy.Params);

        parameters.Add(new ParameterDeclaration("back"));
        Assert.Equal(["back"], algorithm.Params);
    }

    [Fact]
    public void ReplacingParameters_ReplacesTheProjection_AndUnrelatedCopiesKeepIt()
    {
        var algorithm = new Algorithm.User(null, [new ParameterDeclaration("x")], [], [], [new Expr.Param("x")]);
        Assert.Equal(["x"], algorithm.Params);

        // Every parameter-replacing route (the public With* family and a direct `with`) gives
        // the copy the new names — same count with different names, empty to non-empty, and
        // non-empty to empty — and never touches the source.
        Assert.Equal(["p", "q"], algorithm.WithParameters([new ParameterDeclaration("p"), new ParameterDeclaration("q")]).Params);
        Assert.Equal(["y"], algorithm.WithParams(["y"]).Params);
        Assert.Empty(algorithm.WithParams([]).Params);
        Assert.Equal(["x", "n"], algorithm.WithParams(["x", "n"]).Params);
        Assert.Equal(["only"], (algorithm with { Parameters = [new ParameterDeclaration("only")] }).Params);
        Assert.Equal(["x"], algorithm.Params);

        var emptied = algorithm.WithParams([]);
        Assert.Empty(emptied.Params);
        Assert.Equal(["again"], emptied.WithParams(["again"]).Params);

        // Copies that change something else keep the projection of the shared list.
        Assert.Equal(["x"], (algorithm with { Parent = new ScopeCtx(null, [], []) }).Params);
        Assert.Equal(["x"], (algorithm with { Output = [new Expr.Num(2)] }).Params);
        Assert.Equal(["x"], (algorithm with { }).Params);
    }

    [Fact]
    public void Params_OfAZeroParameterAlgorithm_AllocatesNothing()
    {
        // The dominant read: every evaluator-synthesized wrapper and most written properties
        // have no parameters, and the evaluator projects their names on every property read,
        // scope wiring, and body entry. Thread-local allocation is exact, so the assertion is
        // exactly zero bytes, on every variant, after the first read has JIT-compiled the path.
        var user = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var family = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.Bind("x"), user)]);
        var builtin = new Algorithm.Builtin(BuiltinId.count);
        Algorithm[] algorithms = [user, family, builtin, user with { Parent = new ScopeCtx(null, [], []) }];
        var total = 0;
        foreach (var algorithm in algorithms)
            total += algorithm.Params.Count;

        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < 1000; i++)
        {
            foreach (var algorithm in algorithms)
                total += algorithm.Params.Count;
        }

        Assert.Equal(0L, GC.GetAllocatedBytesForCurrentThread() - before);
        Assert.Equal(0, total);
    }

    [Fact]
    public void Params_OfAParameterizedAlgorithm_IsOneFreshListPerRead()
    {
        // A parameterized projection is a fresh list per read — not a shared cached instance
        // that one consumer could corrupt for another — and costs exactly one small object.
        var algorithm = new Algorithm.User(
            null,
            [new ParameterDeclaration("a"), new ParameterDeclaration("b"), new ParameterDeclaration("c")],
            [],
            [],
            [new Expr.Num(1)]);
        var first = algorithm.Params;
        var second = algorithm.Params;
        Assert.NotSame(first, second);
        Assert.Equal(first, second);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var read = algorithm.Params;
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(3, read.Count);
        Assert.InRange(allocated, 1, 64);
    }

    [Theory]
    [InlineData("Inc(v) = v + 1\nInc(0)")]
    [InlineData("F = a + b * c\nF(1, 2, 3)")]
    [InlineData("Outer(n) = {\n  Inner(k) = n + k\n  Inner(1)\n}\nOuter(5)")]
    [InlineData("F(0) = 100\nF(x) = x + 1\nF(1)")]
    [InlineData("Collect(*items) = items\nCollect(1, 2, 3)")]
    [InlineData("PairSum((x, y)) = x + y\nPairSum((1, 2))")]
    [InlineData("x, *rest, z = (1, 2, 3, 4)\nx + z")]
    [InlineData("Square = x * x\nAdd(x, acc) = acc + x\nrange(1, 5).map(Square).reduce(Add, 0)")]
    [InlineData("Step = k + 1\nStep.repeat(3, 2):0")]
    [InlineData("Outer(n) = {\n  public Twice = n * 2\n  Twice\n}\nOuter(3)")]
    public void EveryElaboratedAlgorithm_HasAsManyNamesAsParameters(string source)
    {
        // The invariant every count-only consumer relies on when it reads Parameters.Count
        // instead of materializing Params: over explicit, implicitly lifted, collecting,
        // sequence-value-patterned, deconstruction, callback, loop-step, and nested
        // algorithms alike, the projection has exactly one name per parameter, in order.
        var root = SourceProvenance.ParseValid(source).Root;
        var collector = new AlgorithmCollector();
        collector.VisitAlgorithm(root);

        Assert.NotEmpty(collector.Algorithms);
        foreach (var algorithm in collector.Algorithms)
        {
            Assert.Equal(algorithm.Parameters.Select(static parameter => parameter.Name), algorithm.Params);
            Assert.Equal(algorithm.Parameters.Count, algorithm.Params.Count);
        }
    }

    [Fact]
    public void ZeroArgumentValueDemand_CountsParameters_NotPatterns()
    {
        // The one law site a count-only rewrite could quietly change the meaning of: the
        // zero-argument value demand asks for the PARAMETER count (Lean:
        // `(Algorithm.params a).length = 0`), never the pattern count. A parameter list may
        // have a pattern with zero captures — host-constructible only, the parser rejects
        // `F(()) = 5` — and such a property is still a zero-argument value: reading `F`
        // proceeds to its output instead of reporting an arity mismatch.
        var patternedButParameterless = new Algorithm.User(null, [], [], [], [new Expr.Num(5)])
        {
            ParameterPatterns = [new SequenceValueParameterPattern([])],
        };
        Assert.Single(patternedButParameterless.ParameterPatterns);
        Assert.Empty(patternedButParameterless.Params);

        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("F", patternedButParameterless)],
            Output: [new Expr.Resolve("F")]);

        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([5m], result.Value.ToAtoms());
    }

    private sealed class AlgorithmCollector : AstWalker
    {
        public List<Algorithm> Algorithms { get; } = [];

        protected override bool VisitsExplicitParameterDeclarations => false;

        protected override void VisitUserAlgorithm(Algorithm.User algorithm)
        {
            Algorithms.Add(algorithm);
            base.VisitUserAlgorithm(algorithm);
        }

        protected override void VisitConditionalAlgorithm(Algorithm.Conditional algorithm)
        {
            Algorithms.Add(algorithm);
            base.VisitConditionalAlgorithm(algorithm);
        }
    }
}
