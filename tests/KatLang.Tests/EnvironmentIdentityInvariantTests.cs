using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;
using AlgEnv = System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Algorithm Value, KatLang.EvalError? ValueError)>;
using CountedParamEnv = System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Evaluator.CountedResult Value)>;
using ValEnv = System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Result Value)>;

namespace KatLang.Tests;

/// <summary>
/// The evaluator's environment tiers are plain lists whose REFERENCE IDENTITY is the
/// binding-context identity of the run-scoped caches: a LOCAL-ONLY zero-argument property
/// entry is keyed by the identities of the three tiers at the access
/// (<see cref="ZeroArgPropertyCacheKey"/>), and a deconstruction group's shared bind by
/// the caller's three environment identities (<see cref="DeconstructionBindingExecution"/>).
/// <c>Evaluator.Concat</c> — the ONE helper that builds a new binding context's tier by
/// prepending the binding's own entries — must therefore return a FRESH list on every
/// call, never one of its operands, even when the other operand is empty. The obvious
/// short-circuit <c>if (a.Count == 0) return b;</c> would make two activations that bind
/// nothing new share one binding context, and a local-only property would be served the
/// other activation's entry. The identity-PRESERVING shadow helpers
/// (<c>ShadowValEnv</c> and its tiers) are different: a shadowed inherited tier is a view
/// of the caller's context, and the callee's fresh identity is minted by the
/// <c>Concat</c> that follows.
/// </summary>
public class EnvironmentIdentityInvariantTests
{
    private static readonly ValEnv Empty = [];

    private static ValEnv Bindings(params (string Name, Result Value)[] bindings) => bindings;

    [Fact]
    public void Concat_AlwaysMintsAFreshList_EvenWhenAnOperandIsEmpty()
    {
        ValEnv environment = Bindings(("x", new Result.Atom(1)));

        var emptyPrepended = Evaluator.Concat(Empty, environment);
        var emptyAppended = Evaluator.Concat(environment, Empty);
        var bothEmpty = Evaluator.Concat(Empty, Empty);
        var ordinary = Evaluator.Concat(Bindings(("y", new Result.Atom(2))), environment);

        Assert.NotSame(environment, emptyPrepended);
        Assert.NotSame(environment, emptyAppended);
        Assert.NotSame(Empty, bothEmpty);
        Assert.NotSame(bothEmpty, Evaluator.Concat(Empty, Empty));
        Assert.NotSame(emptyPrepended, Evaluator.Concat(Empty, environment));
        Assert.NotSame(environment, ordinary);
        Assert.NotSame(emptyPrepended, emptyAppended);
        // Content is the ordinary concatenation; only the identity is new.
        Assert.Equal(environment, emptyPrepended);
        Assert.Equal(environment, emptyAppended);
        Assert.Empty(bothEmpty);
        Assert.Equal(["y", "x"], ordinary.Select(binding => binding.Name));
    }

    [Fact]
    public void Concat_IsNotAnIdentityFunctionOnEitherOperand_ForEveryTierType()
    {
        // The three tiers are distinct list element types; the helper is generic and the
        // law holds for each instantiation.
        AlgEnv algorithms = [("f", new Algorithm.Builtin(BuiltinId.@count), null)];
        CountedParamEnv counted = [("n", new Evaluator.CountedResult(new Result.Atom(1), 1))];

        Assert.NotSame(algorithms, Evaluator.Concat([], algorithms));
        Assert.NotSame(counted, Evaluator.Concat([], counted));
    }

    /// <summary>
    /// Run-scoped cache that records ACTUAL EVALUATIONS per property name.
    /// </summary>
    private sealed class CountingCache : IZeroArgPropertyResultCache
    {
        private readonly RunScopedZeroArgPropertyResultCache _inner = new();

        public Dictionary<string, int> Requests { get; } = new(StringComparer.Ordinal);

        public Dictionary<string, int> Evaluations { get; } = new(StringComparer.Ordinal);

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Requests[execution.Binding.Name] = Requests.GetValueOrDefault(execution.Binding.Name) + 1;
            return _inner.GetOrEvaluate(execution, () =>
            {
                Evaluations[execution.Binding.Name] = Evaluations.GetValueOrDefault(execution.Binding.Name) + 1;
                return evaluate();
            });
        }
    }

    private static IReadOnlyList<Decimal128> Atoms(EvalResult<Result> result)
    {
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        return result.Value.ToAtoms();
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void TwoActivationsThatBindNothing_AreTwoBindingContexts_ForALocalOnlyProperty(bool optimize)
    {
        // `Inner` declares no parameters, so each `Inner()` call prepends NOTHING to the
        // inherited tiers — Concat(empty, inherited) — yet each call is its own activation:
        // the local-only `P` (it reads Outer's parameter) is evaluated once per activation
        // and reused within it. An identity-preserving Concat would key both activations
        // by Outer's own tiers and evaluate `P` once.
        const string source = "Outer(x) = {\n    Inner = {\n        P = x * 10\n        P + P\n    }\n    Inner(), Inner()\n}\nOuter(2)";
        var root = SourceProvenance.ParseValid(source).Root;
        var inner = Assert.Single(Assert.Single(root.Properties, p => p.Name == "Outer").Value.Properties, p => p.Name == "Inner");
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(inner.Value.Properties, p => p.Name == "P").Exposure);

        var cache = new CountingCache();
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root), cache, enableLoopOptimization: optimize);

        Assert.Equal([40m, 40m], Atoms(result));
        Assert.Equal(4, cache.Requests["P"]);
        Assert.Equal(2, cache.Evaluations["P"]);
    }

    [Theory]
    [InlineData(0)] // synchronous generic
    [InlineData(1)] // synchronous optimized
    [InlineData(2)] // genuinely suspending async twin
    public async Task TwoActivationsOfADeconstructingCaller_NeverShareOneGroupBind(int path)
    {
        // Inner binds NO new parameters. Reusing Concat's inherited operand would alias
        // both activations' three tiers and incorrectly reuse the first full group bind.
        const string source = "Outer(x) = {\n    Inner = {\n        a, b = (x, x + 1)\n        a + b\n    }\n    Inner(), Inner()\n}\nOuter(1)";
        var observations = new EvaluationObservations();
        var ast = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var (result, _) = path == 2
            ? await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                ast, zeroArgPropertyResultCache: cache, observations: observations))
            : Evaluator.RunCountedObserved(ast, enableOptimizations: path == 1, observations: observations);

        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([3m, 3m], result.Value.Value.ToAtoms());
        Assert.Equal(2, observations.DeconstructionFullBindCount);
        if (path == 2)
        {
            Assert.True(cache.AsyncAccesses > 0);
            Assert.Equal(0, cache.SyncAccesses);
        }
    }
}
