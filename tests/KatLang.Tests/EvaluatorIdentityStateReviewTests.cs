using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

public class EvaluatorIdentityStateReviewTests
{
    [Fact]
    public void BinderlessClauseMatches_StillHaveDistinctFamilyActivations()
    {
        var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var family = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), body)]);
        var wire = typeof(Evaluator).GetMethod("ChildOfConditionalCall", BindingFlags.Static | BindingFlags.NonPublic)!;
        Algorithm Invoke() => (Algorithm)wire.Invoke(null,
            [family, body, Array.Empty<string>(), Evaluator.EvalCtx.Empty, Array.Empty<(string, Result)>()])!;
        var first = Invoke().Parent!;
        var second = Invoke().Parent!;
        Assert.Same(family, first.Owner);
        Assert.Empty(first.Parameters);
        Assert.NotNull(first.Activation);
        Assert.NotNull(second.Activation);
        Assert.NotSame(first.Activation, second.Activation);
    }

    [Theory]
    [InlineData(2)]
    [InlineData(12)]
    [InlineData(4096)]
    public void ActivationCapture_PreservesEnvironmentOrderAndFirstBindingOnAllChannels(int width)
    {
        var names = Enumerable.Range(0, width).Select(i => $"p{i}").ToArray();
        var expectedNames = names.Reverse().ToArray();
        var function = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var other = new Algorithm.Builtin(BuiltinId.count);
        var values = expectedNames.Select(n => (Name: n, Value: (Result)new Result.Atom(1)))
            .Concat(names.Select(n => (n, (Result)new Result.Atom(2)))).Append(("unowned", new Result.Atom(3))).ToArray();
        var algorithms = expectedNames.Select(n => (Name: n, Algorithm: (Algorithm)function, Error: (EvalError?)null))
            .Concat(names.Select(n => (n, (Algorithm)other, (EvalError?)new EvalError.BadArity()))).ToArray();
        var counted = expectedNames.Select(n => (Name: n, Value: new Evaluator.CountedResult(new Result.Atom(7), 3)))
            .Concat(names.Select(n => (n, new Evaluator.CountedResult(new Result.Atom(8), 4)))).ToArray();
        var ctx = Evaluator.EvalCtx.Empty.WithAlgEnv(algorithms).WithCountedParamEnv(counted);

        // Duplicate owned names do not allocate multiple bindings. All tiers independently
        // preserve environment order, not signature order, including the wide set path.
        var captured = ParameterActivation.Capture([.. names, names[0]], ctx, values);
        Assert.Equal(expectedNames, captured.Values.Select(b => b.Name));
        Assert.All(captured.Values, b => Assert.Equal(new Result.Atom(1), b.Value));
        Assert.Equal(expectedNames, captured.Algorithms.Select(b => b.Name));
        Assert.All(captured.Algorithms, b => { Assert.Same(function, b.Value); Assert.Null(b.ValueError); });
        Assert.Equal(expectedNames, captured.Counted.Select(b => b.Name));
        Assert.All(captured.Counted, b => Assert.Equal(new Evaluator.CountedResult(new Result.Atom(7), 3), b.Value));
        Assert.NotSame(captured, ParameterActivation.Capture(names, ctx, values));
    }

    [Fact]
    public void RuntimeOnlyOwnerCycle_IsIgnoredByPreflightEqualityHashAndPrinting()
    {
        var scope = new ScopeCtx(null, [], [], []);
        var owner = new Algorithm.User(scope, [], [], [], [new Expr.Num(1)]);
        // Construct an actual back-reference cycle, exclusively through runtime state.
        // Public immutable construction cannot close this graph; reflection is test-only.
        typeof(ScopeCtx).GetProperty("Owner", BindingFlags.Instance | BindingFlags.NonPublic)!.SetValue(scope, owner);
        Assert.Same(scope, scope.Owner!.Parent);
        var unowned = scope with { Owner = null };
        Assert.Equal(scope, unowned);
        Assert.Equal(scope.GetHashCode(), unowned.GetHashCode());
        Assert.Equal(scope.ToString(), unowned.ToString());
        Assert.DoesNotContain("Owner", owner.ToString());
        Assert.False(AstStructuralPreflight.TryGetChild(scope, 0, out _));
        Assert.Null(AstStructuralPreflight.Check(owner, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines));
    }

    [Fact]
    public void FlatBinderViews_KeepBodyDeclarationAndSeparateInvocations()
    {
        var body = new Algorithm.User(null, [], [],
            [new Property("P", new Algorithm.User(null, [], [], [], [new Expr.Param("x")]),
                Exposure: PropertyExposure.LocalOnlyCapturedAncestorParameters) { RequiredAncestorParameters = ["x"] }],
            [new Expr.Binary(BinaryOp.Add, new Expr.Resolve("P"), new Expr.Param("y"))]);
        var family = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]), body)]);
        var method = typeof(Evaluator).GetMethod("TryGetFlatBinderUserEquivalent", BindingFlags.NonPublic | BindingFlags.Static)!;
        var first = Assert.IsType<Algorithm.User>(method.Invoke(null, [family]));
        var second = Assert.IsType<Algorithm.User>(method.Invoke(null, [family]));
        Assert.NotSame(first, second);
        Assert.Same(body.Declaration, first.Declaration);
        Assert.Same(body.Declaration, second.Declaration);
        Assert.Same(family.Declaration, first.Parent!.Declaration);
        Assert.NotSame(first.Declaration, family.Declaration);
        var root = new Algorithm.User(null, [], [], [new Property("F", family)],
            [new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(5), new Expr.Num(1)]),
             new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(7), new Expr.Num(2)])]);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root), new RunScopedZeroArgPropertyResultCache());
        Assert.False(result.IsError);
        Assert.Equal([6m, 9m], result.Value.ToAtoms());
    }

    [Fact]
    public async Task DeferredMaterialization_RetainsDeclarationAcrossSuspensionAndRepeatedRuns()
    {
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["identity.test"],
            DownloadCode = async (_, _) => { downloads++; await Task.Yield(); return "public One = 1"; },
        };
        const string source = "F(0) = 0\nF(n) = {\n open 'https://identity.test/lib'\n Inner = { public X = n + One }\n Inner.X\n}\nF(5), F(7)";
        var parsed = await SourceProvenance.ParseValidAsync(source, options);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        var placeholder = family.Branches[1].Body;
        Assert.True(DeferredModuleRegions.TryGet(placeholder, out var region));
        Assert.Equal(0, downloads);
        for (var run = 0; run < 2; run++)
        {
            var result = await Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root));
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal([6m, 8m], result.Value.ToAtoms());
            Assert.True(region.TryGetMaterialized(out var materialized));
            Assert.Same(placeholder.Declaration, materialized.Declaration);
            Assert.Same(region.RawBody.Declaration, materialized.Declaration);
        }
        Assert.Equal(1, downloads);
        Assert.Equal(1, region.MaterializationAttempts);
    }

    [Fact]
    public void CompletedRuns_ReleaseActualObservedScopesActivationsAndEnvironments()
    {
        var references = RunAndObserve();
        Assert.Contains(references, r => r.Kind == "scope");
        Assert.Contains(references, r => r.Kind == "activation");
        Assert.Contains(references, r => r.Kind == "values");
        Assert.Contains(references, r => r.Kind == "algorithms");
        Assert.Contains(references, r => r.Kind == "counted");
        for (var attempt = 0; attempt < 5 && references.Any(r => r.Reference.IsAlive); attempt++)
        {
            GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true, compacting: true);
            GC.WaitForPendingFinalizers();
            GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true, compacting: true);
        }
        Assert.All(references, r => Assert.False(r.Reference.IsAlive, $"retained {r.Kind}"));
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static List<(string Kind, WeakReference Reference)> RunAndObserve()
    {
        var cache = new WeakObservationCache();
        var root = SourceProvenance.ParseValid("F(n) = {\n Inner = { public X = n }\n Inner.X\n}\n"
            + "Apply(f, n) = {\n Inner = { public X = f(n) }\n Inner.X\n}\nInc(v) = v + 1\n"
            + "F(5), Apply(Inc, 5), [6, 7].map(F).sum").Root;
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root), cache);
        Assert.False(result.IsError);
        Assert.Equal([5m, 6m, 13m], result.Value.ToAtoms());
        cache.References.Add(("root", new WeakReference(root)));
        return cache.References;
    }

    private sealed class WeakObservationCache : IZeroArgPropertyResultCache
    {
        internal List<(string Kind, WeakReference Reference)> References { get; } = [];
        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            References.Add(("owner", new WeakReference(execution.Owner)));
            for (var scope = execution.Owner.Parent; scope is not null; scope = scope.Parent)
            {
                if (scope.Activation is not { } activation) continue;
                References.Add(("scope", new WeakReference(scope)));
                References.Add(("activation", new WeakReference(activation)));
                if (activation.Values.Count > 0) References.Add(("values", new WeakReference(activation.Values)));
                if (activation.Algorithms.Count > 0) References.Add(("algorithms", new WeakReference(activation.Algorithms)));
                if (activation.Counted.Count > 0) References.Add(("counted", new WeakReference(activation.Counted)));
            }
            return evaluate();
        }
    }
}
