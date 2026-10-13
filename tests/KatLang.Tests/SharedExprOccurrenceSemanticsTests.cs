using KatLang.Evaluation.Caching;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// The AST occurrence invariant that makes shared <see cref="Expr"/> subgraphs — built by a host,
/// or shared by the front end (a spliced module, a shared implicit-argument bundle) — a safe
/// representation: an expression OCCURRENCE is semantic work, whatever the host object topology.
/// If one immutable <see cref="Expr"/> reference appears in N positions, evaluation happens N
/// times, each under its own occurrence's lexical context, charging the same steps, items, and
/// dynamic depth as N structurally identical clones; the structural preflight judges the same
/// weighted paths; and no evaluator cache keys on <see cref="Expr"/> reference identity, so
/// occurrences never alias.
///
/// <para>Every experiment here compares ONE root holding the SAME child reference twice against
/// a root holding two independently constructed clones — or, for the doubling literal DAG, a
/// graph whose every level holds the same child twice against its fully expanded tree — through
/// the public prebuilt-AST entry points (shared host subtrees are an explicitly supported AST
/// shape — the pre-evaluation walker and <c>AstStructuralPreflight</c> are reference-memoized for
/// exactly this).</para>
/// </summary>
public class SharedExprOccurrenceSemanticsTests
{
    private static Expr.AlgorithmExpr Program(Algorithm.User root) => new(root);

    private static Algorithm.User Root(
        IReadOnlyList<Property>? properties = null,
        params Expr[] output)
        => new(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: properties ?? [],
            Output: OutputBundle.TakeOwnership(output));

    private static Algorithm.User Body(params Expr[] output)
        => new(Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: OutputBundle.TakeOwnership(output));

    private static Algorithm.User Function(string param, Expr body)
        => new(
            Parent: null,
            ParameterPatterns: Algorithm.NormalParameters([param]),
            Opens: [],
            Properties: [],
            Output: [body]);

    /// <summary>`F(x) = x + 1` and `G = F(2)`: a call-bearing subtree, so occurrences charge
    /// real steps and dynamic depth.</summary>
    private static IReadOnlyList<Property> CallProperties() =>
    [
        new Property("F", Function("x", new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1)))),
        new Property("G", Body(new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(2)]))),
    ];

    private static Expr CallSubtree() => new Expr.Call(new Expr.Resolve("G"), OutputBundle.Empty);

    private static void AssertFlat(Expr program, params Decimal128[] expected)
    {
        var result = Evaluator.RunFlat(program);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
    }

    // ── Per-occurrence evaluation and charge parity ──────────────────────────────────────────

    [Fact]
    public void SharedCallSubtree_EvaluatesOncePerOccurrence_ChargingExactlyWhatClonesCharge()
    {
        var shared = CallSubtree();
        var sharedProgram = Program(Root(CallProperties(), shared, shared));
        var clonedProgram = Program(Root(CallProperties(), CallSubtree(), CallSubtree()));

        var (sharedResult, sharedBudget) = Evaluator.RunCountedObserved(sharedProgram);
        var (clonedResult, clonedBudget) = Evaluator.RunCountedObserved(clonedProgram);

        Assert.False(sharedResult.IsError);
        Assert.False(clonedResult.IsError);
        Assert.Equal(clonedResult.Value.Value, sharedResult.Value.Value, Result.ValueComparer);
        Assert.Equal(clonedResult.Value.EmittedCount, sharedResult.Value.EmittedCount);

        // The load-bearing equalities: identical steps, materialization, and peak dynamic depth.
        // A visited-reference shortcut anywhere in evaluation would make the shared run cheaper.
        Assert.Equal(clonedBudget.ConsumedSteps, sharedBudget.ConsumedSteps);
        Assert.Equal(clonedBudget.MaterializedItems, sharedBudget.MaterializedItems);
        Assert.Equal(clonedBudget.MaterializedStringChars, sharedBudget.MaterializedStringChars);
        Assert.Equal(clonedBudget.PeakDepth, sharedBudget.PeakDepth);

        // And the shared run costs strictly more than a single occurrence: work scales with
        // occurrences, not with unique references.
        var (_, singleBudget) = Evaluator.RunCountedObserved(Program(Root(CallProperties(), CallSubtree())));
        Assert.True(sharedBudget.ConsumedSteps > singleBudget.ConsumedSteps);
    }

    [Fact]
    public void SharedCallSubtree_CrossesTheStepBoundaryExactlyWhereClonesDo()
    {
        var shared = CallSubtree();
        var sharedProgram = Program(Root(CallProperties(), shared, shared));
        var clonedProgram = Program(Root(CallProperties(), CallSubtree(), CallSubtree()));

        var failed = false;
        var succeeded = false;
        for (long limit = 1; limit <= 24; limit++)
        {
            var limits = new EvaluationLimits { MaxSteps = limit };
            var sharedR = Evaluator.Run(sharedProgram, limits);
            var clonedR = Evaluator.Run(clonedProgram, limits);

            Assert.Equal(clonedR.IsError, sharedR.IsError);
            if (sharedR.IsError)
            {
                Assert.Equal(clonedR.Error.GetType(), sharedR.Error.GetType());
                failed = true;
            }
            else
            {
                succeeded = true;
            }
        }

        // The sweep must include both sides of the boundary, or the parity above is vacuous.
        Assert.True(failed && succeeded, "The step sweep did not cross the success/failure boundary.");
    }

    [Fact]
    public void SharedCallSubtree_CrossesTheDepthBoundaryExactlyWhereClonesDo()
    {
        var shared = CallSubtree();
        var sharedProgram = Program(Root(CallProperties(), shared, shared));
        var clonedProgram = Program(Root(CallProperties(), CallSubtree(), CallSubtree()));

        var failed = false;
        var succeeded = false;
        for (var limit = 1; limit <= 12; limit++)
        {
            var limits = new EvaluationLimits { MaxDepth = limit };
            var sharedR = Evaluator.Run(sharedProgram, limits);
            var clonedR = Evaluator.Run(clonedProgram, limits);

            Assert.Equal(clonedR.IsError, sharedR.IsError);
            if (sharedR.IsError)
            {
                Assert.Equal(clonedR.Error.GetType(), sharedR.Error.GetType());
                failed = true;
            }
            else
            {
                succeeded = true;
            }
        }

        Assert.True(failed && succeeded, "The depth sweep did not cross the success/failure boundary.");
    }

    // ── A deeply shared value-literal DAG evaluates exactly like its expanded tree ────────────

    /// <summary>
    /// The doubling literal DAG: <c>L0 = [1, 2]</c>, <c>Lk = [L(k-1), L(k-1)]</c>. Shared, it is ONE
    /// list-literal object per level holding the SAME child reference twice, so depth n spells
    /// 2^(n+1) - 1 list-literal occurrences with n+1 objects; expanded, every occurrence is its own
    /// object (the structurally identical tree).
    /// </summary>
    private static Expr LiteralDag(int depth, bool shared)
    {
        if (depth == 0)
            return new Expr.ListLiteral([new Expr.Num(1), new Expr.Num(2)]);
        if (!shared)
            return new Expr.ListLiteral([LiteralDag(depth - 1, shared: false), LiteralDag(depth - 1, shared: false)]);

        var child = LiteralDag(depth - 1, shared: true);
        return new Expr.ListLiteral([child, child]);
    }

    [Fact]
    public void SharedLiteralChild_MaterializesOncePerOccurrence()
    {
        var child = new Expr.ListLiteral([new Expr.Num(1), new Expr.Num(2)]);
        var twice = new Expr.ListLiteral([child, child]);
        var once = new Expr.ListLiteral([child]);

        var (twiceResult, twiceBudget) = Evaluator.RunCountedObserved(twice);
        var (onceResult, onceBudget) = Evaluator.RunCountedObserved(once);
        Assert.False(twiceResult.IsError);
        Assert.False(onceResult.IsError);
        Assert.True(twiceBudget.MaterializedItems > onceBudget.MaterializedItems);
    }

    [Fact]
    public void SharedLiteralDag_EvaluatesWithExactlyTheExpandedTreesWork()
    {
        // Evaluation is per VISIT, and a shared reference visited twice pays twice: the doubling
        // DAG and its expanded tree describe the same expression, so they charge identical work.
        var shared = LiteralDag(6, shared: true);
        var expanded = LiteralDag(6, shared: false);

        var (sharedResult, sharedBudget) = Evaluator.RunCountedObserved(shared);
        var (expandedResult, expandedBudget) = Evaluator.RunCountedObserved(expanded);

        Assert.False(sharedResult.IsError);
        Assert.False(expandedResult.IsError);
        Assert.Equal(expandedResult.Value.Value, sharedResult.Value.Value, Result.ValueComparer);
        Assert.Equal(expandedResult.Value.EmittedCount, sharedResult.Value.EmittedCount);
        Assert.Equal(expandedBudget.ConsumedSteps, sharedBudget.ConsumedSteps);
        Assert.True(sharedBudget.ConsumedExpressionCheckpoints > 0);
        Assert.Equal(expandedBudget.ConsumedExpressionCheckpoints, sharedBudget.ConsumedExpressionCheckpoints);
        Assert.Equal(expandedBudget.MaterializedItems, sharedBudget.MaterializedItems);
        Assert.Equal(expandedBudget.MaterializedStringChars, sharedBudget.MaterializedStringChars);
        Assert.Equal(expandedBudget.PeakDepth, sharedBudget.PeakDepth);
    }

    [Fact]
    public void SharedLiteralDag_CrossesTheMaterializationBoundaryExactlyWhereTheExpandedTreeDoes()
    {
        var shared = LiteralDag(4, shared: true);
        var expanded = LiteralDag(4, shared: false);

        var failed = false;
        var succeeded = false;
        for (long limit = 1; limit <= 96; limit++)
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = limit };
            var sharedR = Evaluator.Run(shared, limits);
            var expandedR = Evaluator.Run(expanded, limits);

            Assert.Equal(expandedR.IsError, sharedR.IsError);
            if (sharedR.IsError)
            {
                Assert.Equal(expandedR.Error.GetType(), sharedR.Error.GetType());
                failed = true;
            }
            else
            {
                succeeded = true;
            }
        }

        Assert.True(failed && succeeded, "The materialization sweep did not cross the success/failure boundary.");
    }

    [Fact]
    public void SharedLiteralDag_CalledAsACallee_ReportsTheExpandedTreesDiagnostic()
    {
        // A literal has no callable identity; the diagnostic that names the shared callee must be
        // the expanded tree's, and both are spanless (host-built nodes carry no source spans).
        var shared = Evaluator.Run(new Expr.Call(LiteralDag(4, shared: true), OutputBundle.Empty));
        var expanded = Evaluator.Run(new Expr.Call(LiteralDag(4, shared: false), OutputBundle.Empty));

        Assert.True(shared.IsError);
        Assert.True(expanded.IsError);
        Assert.Equal(expanded.Error, shared.Error);
        Assert.Equal(expanded.Error.ToString(), shared.Error.ToString());
        Assert.Null(shared.Error.Span);
    }

    // ── Environment sensitivity: each occurrence resolves in ITS context ─────────────────────

    [Fact]
    public void SharedNameReference_ResolvesPerOccurrenceContext()
    {
        // ONE `Resolve("V")` reference placed inside two sibling scopes that bind V differently.
        // The same immutable Expr object must yield 1 under the first owner and 2 under the
        // second: context comes from the occurrence, never from the node.
        var sharedResolve = new Expr.Resolve("V");
        var blockOne = Body(sharedResolve) with
        {
            Properties = [new Property("V", Body(new Expr.Num(1)))],
        };
        var blockTwo = Body(sharedResolve) with
        {
            Properties = [new Property("V", Body(new Expr.Num(2)))],
        };

        var program = Program(Root(
            properties: null,
            new Expr.AlgorithmExpr(blockOne),
            new Expr.AlgorithmExpr(blockTwo)));

        AssertFlat(program, 1m, 2m);

        var counted = Evaluator.RunCounted(program);
        Assert.False(counted.IsError);
        Assert.Equal(2, counted.Value.EmittedCount);
    }

    [Fact]
    public void SharedNameReference_ResolvesPerOccurrence_UnderEveryCacheConfiguration()
    {
        // The zero-argument property cache keys on (owner scope, property binding, environments,
        // run) — never on Expr identity — so a shared Resolve under two owners must not alias,
        // and cached/uncached runs must agree. The doubled occurrence inside each block also
        // exercises a repeat access whose cached reuse must stay owner-correct.
        var sharedResolve = new Expr.Resolve("V");
        var blockOne = Body(sharedResolve, sharedResolve) with
        {
            Properties = [new Property("V", Body(new Expr.Num(1)))],
        };
        var blockTwo = Body(sharedResolve, sharedResolve) with
        {
            Properties = [new Property("V", Body(new Expr.Num(2)))],
        };

        var program = Program(Root(
            properties: null,
            new Expr.AlgorithmExpr(blockOne),
            new Expr.AlgorithmExpr(blockTwo)));

        // Default entry point: fresh run-scoped cache.
        AssertFlat(program, 1m, 1m, 2m, 2m);

        // Explicit pass-through (uncached) configuration.
        var uncached = Evaluator.Run(program, UncachedZeroArgPropertyResultCache.Instance);
        Assert.False(uncached.IsError);
        Assert.Equal([1m, 1m, 2m, 2m], uncached.Value.ToHostAtoms());

        // A reused run-scoped cache instance across BOTH occurrences within one run.
        var cached = Evaluator.Run(program, new RunScopedZeroArgPropertyResultCache());
        Assert.False(cached.IsError);
        Assert.Equal([1m, 1m, 2m, 2m], cached.Value.ToHostAtoms());
    }

    [Fact]
    public void SharedNameReference_RemainsOwnerCorrectWhenOneExplicitCacheIsReusedAcrossRuns()
    {
        var sharedResolve = new Expr.Resolve("V");
        var blockOne = Body(sharedResolve) with
        {
            Properties = [new Property("V", Body(new Expr.Num(1)))],
        };
        var blockTwo = Body(sharedResolve) with
        {
            Properties = [new Property("V", Body(new Expr.Num(2)))],
        };
        var program = Program(Root(
            properties: null,
            new Expr.AlgorithmExpr(blockOne),
            new Expr.AlgorithmExpr(blockTwo)));
        var cache = new RunScopedZeroArgPropertyResultCache();

        var first = Evaluator.Run(program, cache);
        var second = Evaluator.Run(program, cache);

        Assert.False(first.IsError);
        Assert.False(second.IsError);
        Assert.Equal([1m, 2m], first.Value.ToHostAtoms());
        Assert.Equal(first.Value, second.Value, Result.ValueComparer);
    }

    // ── Structural preflight: shared topology judges the same weighted paths ────────────────

    [Fact]
    public void SharedDeepSubtree_GetsTheSamePreflightVerdictAsClones_AtEveryLimit()
    {
        static Expr DeepChain(int depth)
        {
            Expr node = new Expr.Num(1);
            for (var i = 0; i < depth; i++)
                node = new Expr.Capture([node]);
            return node;
        }

        // A Capture node weighs TWO structural units (it absorbed the former Block +
        // transparent wrapper pair), so a 16-level chain weighs ~32 plus root overhead —
        // the sweep below covers both sides of that boundary with margin.
        const int chainDepth = 16;
        var shared = DeepChain(chainDepth);
        var sharedProgram = Program(Root(null, shared, shared));
        var clonedProgram = Program(Root(null, DeepChain(chainDepth), DeepChain(chainDepth)));

        var rejected = false;
        var accepted = false;
        for (var limit = 1; limit <= 64; limit++)
        {
            var limits = new EvaluationLimits { MaxAstDepth = limit };
            var sharedR = Evaluator.Run(sharedProgram, limits);
            var clonedR = Evaluator.Run(clonedProgram, limits);

            Assert.Equal(clonedR.IsError, sharedR.IsError);
            if (sharedR.IsError)
            {
                Assert.Equal(clonedR.Error.GetType(), sharedR.Error.GetType());
                Assert.IsType<EvalError.AstDepthLimitExceeded>(sharedR.Error);
                rejected = true;
            }
            else
            {
                accepted = true;
            }
        }

        Assert.True(rejected && accepted, "The preflight sweep did not cross the verdict boundary.");
    }

    [Fact]
    public void SharedSubtree_PreservesDifferentIncomingEdgeTransitionCosts()
    {
        // The shared fragment Capture -> ListLiteral -> Capture -> ListLiteral -> 1. The first
        // occurrence is reached through Capture -> Capture (no evaluator transition surcharge);
        // the second through ListLiteral -> Capture (a spine-to-recursive re-entry). Preflight may
        // memoize the child's height, but it must still add each incoming edge's own cost.
        static Expr Fragment()
            => new Expr.Capture([new Expr.ListLiteral([new Expr.Capture([new Expr.ListLiteral([new Expr.Num(1)])])])]);

        var shared = Fragment();
        var sharedProgram = Program(Root(
            null,
            new Expr.Capture([shared]),
            new Expr.ListLiteral([shared])));
        var clonedProgram = Program(Root(
            null,
            new Expr.Capture([Fragment()]),
            new Expr.ListLiteral([Fragment()])));

        var rejected = false;
        var accepted = false;
        for (var limit = 1; limit <= 32; limit++)
        {
            var limits = new EvaluationLimits { MaxAstDepth = limit };
            var sharedR = Evaluator.Run(sharedProgram, limits);
            var clonedR = Evaluator.Run(clonedProgram, limits);
            Assert.Equal(clonedR.IsError, sharedR.IsError);
            if (sharedR.IsError)
            {
                Assert.IsType<EvalError.AstDepthLimitExceeded>(sharedR.Error);
                rejected = true;
            }
            else
            {
                accepted = true;
            }
        }

        Assert.True(rejected && accepted, "The transition-cost sweep did not cross its boundary.");
    }

    // ── No state on Expr: repeated and re-entrant use of one shared graph ────────────────────

    [Fact]
    public void SharedGraph_EvaluatesIdenticallyOnRepeatedRuns()
    {
        var shared = CallSubtree();
        var program = Program(Root(CallProperties(), shared, shared));

        var (first, firstBudget) = Evaluator.RunCountedObserved(program);
        var (second, secondBudget) = Evaluator.RunCountedObserved(program);
        var (third, thirdBudget) = Evaluator.RunCountedObserved(program);

        Assert.False(first.IsError);
        Assert.Equal(first.Value.Value, second.Value.Value, Result.ValueComparer);
        Assert.Equal(first.Value.Value, third.Value.Value, Result.ValueComparer);

        // Nothing is retained on the Expr nodes between runs: every run pays the same work.
        Assert.Equal(firstBudget.ConsumedSteps, secondBudget.ConsumedSteps);
        Assert.Equal(firstBudget.ConsumedSteps, thirdBudget.ConsumedSteps);
        Assert.Equal(firstBudget.PeakDepth, thirdBudget.PeakDepth);
    }
}
