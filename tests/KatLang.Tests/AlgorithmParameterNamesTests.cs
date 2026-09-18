namespace KatLang.Tests;

/// <summary>
/// <see cref="Algorithm.User.ParameterPatterns"/> is a user algorithm's ONE stored parameter
/// channel (Lean: the <c>parameterPatterns</c> field of <c>Algorithm.mk</c>);
/// <see cref="Algorithm.User.Parameters"/> (Lean <c>Algorithm.parameters</c>) and
/// <see cref="Algorithm.User.Params"/> (Lean <c>Algorithm.params</c>) are LIVE projections of
/// it: computed from the current pattern list on every read and never stored on the record,
/// because a host-built algorithm keeps its caller-owned pattern list and the public AST reads
/// through to it (the established collection-ownership behavior
/// <c>LoopStrategyPreparationTests</c> pins). The September 2026 <c>Params</c> investigation
/// measured the name projection at 1–4 reads per evaluator operation and removed its cost
/// instead of caching it: a zero-parameter algorithm's projections allocate nothing, a flat
/// parameterized one allocates exactly one array per projection (a nested sequence-value
/// pattern takes the iterative flatten instead), and every count-only
/// consumer inside the implementation reads the projection-free <c>ParameterCount</c> —
/// allocation-free for a flat pattern list, an explicit stack for nested groups — the same
/// number by construction, which the corpus walk below pins.
/// </summary>
public class AlgorithmParameterNamesTests
{
    [Fact]
    public void Params_IsTheOrderedNameProjection_OfTheStoredPatterns()
    {
        // Order and duplicates are the pattern list's own: the projection neither sorts nor
        // deduplicates, and Parameters holds the very declarations the capture leaves hold.
        var user = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [new CaptureParameterPattern("b"), new CaptureParameterPattern("a"), new CaptureParameterPattern("b")],
            Opens: [],
            Properties: [],
            Output: [new Expr.Num(1)]);
        Assert.Equal(["b", "a", "b"], user.Params);
        Assert.Equal(user.Parameters.Count, user.Params.Count);
        Assert.Equal(3, user.ParameterCount);
        Assert.Same(((CaptureParameterPattern)user.ParameterPatterns[1]).Parameter, user.Parameters[1]);

        var collecting = new Algorithm.User(null, [], [], [], [new Expr.Num(1)])
            .WithParameterPatterns([new CaptureParameterPattern("head"), new CaptureParameterPattern("rest", Kind: ParameterKind.Collecting)]);
        Assert.Equal(["head", "rest"], collecting.Params);
        Assert.Equal(ParameterKind.Collecting, collecting.Parameters[1].Kind);

        // Nested sequence-value patterns flatten left to right, depth first — Lean's
        // `(parameterPatterns a).flatMap captures`.
        var nested = new Algorithm.User(
            null,
            [
                new SequenceValueParameterPattern([new CaptureParameterPattern("x"), new SequenceValueParameterPattern([new CaptureParameterPattern("y")])]),
                new CaptureParameterPattern("z"),
            ],
            [],
            [],
            [new Expr.Num(1)]);
        Assert.Equal(["x", "y", "z"], nested.Params);
        Assert.Equal(["x", "y", "z"], nested.Parameters.Select(static parameter => parameter.Name));
        Assert.Equal(3, nested.ParameterCount);

        // A builtin and a clause family have no parameter list at all: the total internal
        // accessors (Lean `Algorithm.params`) answer [] and 0 for them.
        var family = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.Bind("x"), new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))]);
        Algorithm familyAsAlgorithm = family;
        Algorithm builtin = new Algorithm.Builtin(BuiltinId.count);
        Assert.Empty(familyAsAlgorithm.Params);
        Assert.Empty(builtin.Params);
        Assert.Empty(familyAsAlgorithm.Parameters);
        Assert.Equal(0, builtin.ParameterCount);
    }

    [Fact]
    public void Projections_ReadThroughToTheCallerOwnedPatternList()
    {
        // The public AST retains the host's list instance. Every read reflects the list as it
        // is NOW — a same-count rename, growth, a nested-shape change, and emptying alike —
        // and a copy wired earlier (the evaluator's `with { Parent = ... }` view) sees the
        // same live list. Any representation that stored the names or declarations on the
        // record, at construction or on first read, would report a stale projection on at
        // least one of these assertions.
        var patterns = new List<ParameterPattern> { new CaptureParameterPattern("x") };
        var algorithm = new Algorithm.User(null, patterns, [], [], [new Expr.Num(1)]);
        var wiredCopy = algorithm with { Parent = new ScopeCtx(null, [], []) };
        Assert.Equal(["x"], algorithm.Params);
        Assert.Equal(["x"], wiredCopy.Params);

        patterns[0] = new CaptureParameterPattern("y");
        Assert.Equal(["y"], algorithm.Params);
        Assert.Equal(["y"], wiredCopy.Params);
        Assert.Equal("y", Assert.Single(algorithm.Parameters).Name);

        patterns.Add(new CaptureParameterPattern("z"));
        Assert.Equal(["y", "z"], algorithm.Params);
        Assert.Equal(["y", "z"], wiredCopy.Params);
        Assert.Equal(2, algorithm.Parameters.Count);
        Assert.Equal(2, algorithm.ParameterCount);

        // A nested pattern's own item list is caller-owned too.
        var items = new List<ParameterPattern> { new CaptureParameterPattern("p") };
        patterns.Add(new SequenceValueParameterPattern(items));
        Assert.Equal(["y", "z", "p"], algorithm.Params);
        items.Add(new CaptureParameterPattern("q"));
        Assert.Equal(["y", "z", "p", "q"], algorithm.Params);
        Assert.Equal(4, algorithm.ParameterCount);

        patterns.Clear();
        Assert.Empty(algorithm.Params);
        Assert.Empty(wiredCopy.Params);
        Assert.Empty(algorithm.Parameters);
        Assert.Equal(0, algorithm.ParameterCount);

        patterns.Add(new CaptureParameterPattern("back"));
        Assert.Equal(["back"], algorithm.Params);
    }

    [Fact]
    public void ReplacingThePatterns_ReplacesTheProjections_AndUnrelatedCopiesKeepThem()
    {
        var algorithm = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);
        Assert.Equal(["x"], algorithm.Params);

        // Every parameter-replacing route (the public With* family and a direct `with` on the
        // stored channel) gives the copy the new names — same count with different names,
        // empty to non-empty, and non-empty to empty — and never touches the source.
        Assert.Equal(["p", "q"], algorithm.WithParameters([new ParameterDeclaration("p"), new ParameterDeclaration("q")]).Params);
        Assert.Equal(["y"], algorithm.WithParams(["y"]).Params);
        Assert.Empty(algorithm.WithParams([]).Params);
        Assert.Equal(["x", "n"], algorithm.WithParams(["x", "n"]).Params);
        Assert.Equal(["only"], (algorithm with { ParameterPatterns = [new CaptureParameterPattern("only")] }).Params);
        Assert.Equal(["x"], algorithm.Params);

        var emptied = algorithm.WithParams([]);
        Assert.Empty(emptied.Params);
        Assert.Equal(["again"], emptied.WithParams(["again"]).Params);

        // Copies that change something else keep the projection of the shared list.
        Assert.Equal(["x"], (algorithm with { Parent = new ScopeCtx(null, [], []) }).Params);
        Assert.Equal(["x"], (algorithm with { Output = [new Expr.Num(2)] }).Params);
        Assert.Equal(["x"], (algorithm with { }).Params);

        // The total updates are the identity on the variants that have no parameter list.
        var family = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.Bind("x"), algorithm)]);
        Assert.Same(family, family.WithParams(["a"]));
        Assert.Same(family, family.WithParameterPatterns([new CaptureParameterPattern("a")]));
        var builtin = new Algorithm.Builtin(BuiltinId.count);
        Assert.Same(builtin, builtin.WithParameters([new ParameterDeclaration("a")]));
    }

    [Fact]
    public void Projections_OfAZeroParameterAlgorithm_AllocateNothing()
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
            total += algorithm.Params.Count + algorithm.Parameters.Count + algorithm.ParameterCount;

        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < 1000; i++)
        {
            foreach (var algorithm in algorithms)
                total += algorithm.Params.Count + algorithm.Parameters.Count + algorithm.ParameterCount;
        }

        Assert.Equal(0L, GC.GetAllocatedBytesForCurrentThread() - before);
        Assert.Equal(0, total);
    }

    [Fact]
    public void Projections_OfAParameterizedAlgorithm_AreOneFreshArrayPerRead_AndTheCountIsFree()
    {
        // A parameterized projection is a fresh array per read — not a shared cached instance
        // that one consumer could corrupt for another — and costs exactly one small object;
        // the count-only accessor allocates nothing for this flat list.
        var algorithm = new Algorithm.User(
            null,
            [new CaptureParameterPattern("a"), new CaptureParameterPattern("b"), new CaptureParameterPattern("c")],
            [],
            [],
            [new Expr.Num(1)]);
        var first = algorithm.Params;
        var second = algorithm.Params;
        Assert.NotSame(first, second);
        Assert.Equal(first, second);
        Assert.NotSame(algorithm.Parameters, algorithm.Parameters);
        var count = algorithm.ParameterCount;

        var before = GC.GetAllocatedBytesForCurrentThread();
        var names = algorithm.Params;
        var namesAllocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(3, names.Count);
        Assert.InRange(namesAllocated, 1, 64);

        before = GC.GetAllocatedBytesForCurrentThread();
        var declarations = algorithm.Parameters;
        var declarationsAllocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(3, declarations.Count);
        Assert.InRange(declarationsAllocated, 1, 64);

        before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < 1000; i++)
            count += algorithm.ParameterCount;
        Assert.Equal(0L, GC.GetAllocatedBytesForCurrentThread() - before);
        Assert.Equal(3 * 1001, count);
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
    public void EveryElaboratedAlgorithm_DerivesItsParametersFromItsPatterns(string source)
    {
        // The invariant every count-only consumer relies on when it reads ParameterCount
        // instead of materializing a projection: over explicit, implicitly lifted, collecting,
        // sequence-value-patterned, deconstruction, callback, loop-step, and nested algorithms
        // alike, Parameters is exactly the flattened capture list of the stored patterns,
        // Params has exactly one name per parameter in order, and the count agrees.
        var root = SourceProvenance.ParseValid(source).Root;
        var collector = new AlgorithmCollector();
        collector.VisitAlgorithm(root);

        Assert.NotEmpty(collector.Algorithms);
        foreach (var algorithm in collector.Algorithms)
        {
            Assert.Equal(ParameterPattern.FlattenCaptures(algorithm.ParameterPatterns), algorithm.Parameters);
            Assert.Equal(algorithm.Parameters.Select(static parameter => parameter.Name), algorithm.Params);
            Assert.Equal(algorithm.Parameters.Count, algorithm.Params.Count);
            Assert.Equal(algorithm.Parameters.Count, algorithm.ParameterCount);
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
        var patternedButParameterless = new Algorithm.User(null, [new SequenceValueParameterPattern([])], [], [], [new Expr.Num(5)]);
        Assert.Single(patternedButParameterless.ParameterPatterns);
        Assert.Empty(patternedButParameterless.Params);
        Assert.Equal(0, patternedButParameterless.ParameterCount);

        var root = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
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
