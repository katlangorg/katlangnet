using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text.Json;
using KatLang.Semantics;

namespace KatLang.Tests;

public class OpenMemberIndexHostileReviewTests
{
    private static Algorithm.User Owner(IReadOnlyList<Property> properties)
        => new(null, [], [], properties, OutputBundle.Empty);

    private static Property Member(string name, int value, bool isPublic = true)
        => new(name, new Algorithm.User(null, [], [], [], [new Expr.Num(value)]), IsPublic: isPublic);

    private static string Siblings(int width)
        => "Lib = {\n" + string.Concat(Enumerable.Range(0, width).Select(i => $"public m{i} = {i}\n"))
            + "1\n}\n" + string.Concat(Enumerable.Range(0, width).Select(i => $"B{i} = {{ open Lib\n m0\n}}\n")) + "B0";

    [Fact]
    public void GeneratedIndexes_MatchIndependentOrderedLinearOracle()
    {
        var random = new Random(817239);
        string?[] names = [null, "", "x", "X", "é", "e\u0301", "İ", "i", "m", "missing"];
        var observations = new FrontEndTraversalObservations();
        var cache = new OpenMemberIndexCache(observations);
        for (var trial = 0; trial < 200; trial++)
        {
            var properties = Enumerable.Range(0, 80).Select(i => Member(
                i % 3 == 0 ? $"unrelated{i}" : names[random.Next(names.Length - 1)]!, i, random.Next(3) != 0)
                with { Exposure = i % 2 == 0 ? PropertyExposure.Exported : PropertyExposure.LocalOnlyCapturedAncestorParameters }).ToArray();
            var target = Owner(properties);
            var equalTarget = target with { };
            Assert.Equal(target, equalTarget);
            var shared = cache.IndexOf(target);
            var distinct = cache.IndexOf(equalTarget);
            Assert.NotSame(shared, distinct);
            foreach (var name in names.Concat(properties.Select(p => p.Name)))
            {
                Property? expected = null;
                foreach (var property in properties)
                {
                    if (property.IsPublic && string.Equals(property.Name, name, StringComparison.Ordinal))
                    {
                        expected = property;
                        break;
                    }
                }
                foreach (var (owner, index) in new[] { (target, shared), (equalTarget, distinct) })
                {
                    var actual = index.Lookup(name);
                    Assert.Same(expected, actual?.Property);
                    if (actual is { } hit) Assert.Same(owner, hit.Owner);
                }
            }
            Assert.Same(shared, cache.IndexOf(target));
        }
        Assert.Equal(400, observations.LookupOpenMemberIndexBuilds);
    }

    [Fact]
    public void ProviderOrder_AmbiguityAndOwnedShadowingStayWithEachScope()
    {
        var lib = Owner([Member("x", 1), Member("y", 2)]);
        var x = Owner([Member("x", 3)]);
        var y = Owner([Member("y", 4)]);
        var direct = Member("x", 5);
        var cache = new OpenMemberIndexCache();
        ElaboratedPropertyScope Scope(Algorithm a, Algorithm b, ElaboratedPropertyScope? parent = null)
            => new(parent, [new Expr.AlgorithmExpr(a), new Expr.AlgorithmExpr(b)], [], memberIndexes: cache);
        var a = Scope(lib, x);
        var b = Scope(lib, y);
        var reversed = Scope(y, lib);
        var outer = ElaboratedScopeLookup.CreateScope(Owner([direct]), memberIndexes: cache);
        var shadowed = Scope(lib, x, outer);
        Assert.Equal(new[] { lib.Properties[0], x.Properties[0] }, ElaboratedScopeLookup.LookupOpenPropertyMatches(a, "x").Select(hit => hit.Property));
        Assert.Same(lib.Properties[0], Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(b, "x")).Property);
        Assert.Equal(new[] { lib.Properties[1], y.Properties[0] }, ElaboratedScopeLookup.LookupOpenPropertyMatches(b, "y").Select(hit => hit.Property));
        Assert.Equal(new[] { y.Properties[0], lib.Properties[1] }, ElaboratedScopeLookup.LookupOpenPropertyMatches(reversed, "y").Select(hit => hit.Property));
        Assert.Same(direct, Assert.Single(ElaboratedScopeLookup.LookupLexicalPropertyMatches(shadowed, "x")).Property);
        Assert.Equal(3, cache.Count);
        Assert.Same(a.GetResolvedOpenProviders()[0].Target, b.GetResolvedOpenProviders()[0].Target);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedTargetIndex_DoesNotDeduplicateDistinctProviders(bool namedAliases)
    {
        var lib = Owner([Member("x", 1)]);
        var cache = new OpenMemberIndexCache();
        var parent = ElaboratedScopeLookup.CreateScope(Owner([
            new Property("A", lib), new Property("B", lib)]), memberIndexes: cache);
        Expr[] opens = namedAliases ? [new Expr.Resolve("A"), new Expr.Resolve("B")]
            : [new Expr.AlgorithmExpr(lib), new Expr.AlgorithmExpr(lib)];
        var scope = new ElaboratedPropertyScope(parent, opens, []);
        var hits = ElaboratedScopeLookup.LookupOpenPropertyMatches(scope, "x");
        Assert.Equal(2, hits.Count);
        Assert.All(hits, hit => Assert.Same(lib, hit.Owner));
        Assert.Equal(1, cache.Count);
        Assert.Equal(2, scope.GetResolvedOpenProviders().Count);
    }

    [Fact]
    public void HostMutationBetweenOperations_IsObservedByFreshIndex()
    {
        var properties = new List<Property> { Member("x", 1), Member("y", 2) };
        var target = Owner(properties);
        var first = new OpenMemberIndexCache();
        Assert.Same(properties[0], first.IndexOf(target).Lookup("x")!.Value.Property);
        // Caller-owned lists may change BETWEEN operations; concurrent mutation is unsupported.
        properties[0] = Member("z", 3);
        properties[1] = properties[1] with { IsPublic = false };
        var second = new OpenMemberIndexCache();
        Assert.Null(second.IndexOf(target).Lookup("x"));
        Assert.Null(second.IndexOf(target).Lookup("y"));
        Assert.Same(properties[0], second.IndexOf(target).Lookup("z")!.Value.Property);
        Assert.NotSame(first.IndexOf(target), second.IndexOf(target));
    }

    [Fact]
    public void EqualTargetObjects_AreDistinctInDetectionAndModelConstruction()
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot("L1 = { public x = 1\n1 }\nL2 = { public x = 1\n1 }\nA = { open L1\nx }\nB = { open L2\nx }\nA + B");
        var properties = syntax.Properties.ToArray();
        var first = Assert.IsType<Algorithm.User>(properties[0].Value);
        properties[1] = properties[1] with { Value = first with { } };
        var root = syntax with { Properties = properties };
        Assert.Equal(properties[0].Value, properties[1].Value);
        Assert.NotSame(properties[0].Value, properties[1].Value);
        var detection = new FrontEndTraversalObservations();
        var (_, diagnostics) = ParameterDetector.DetectPrevalidated(root, null, detection);
        Assert.DoesNotContain(diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(2, detection.LookupOpenMemberIndexBuilds);
        var model = new FrontEndTraversalObservations();
        _ = SemanticModelBuilder.Build(root, model);
        Assert.Equal(2, model.LookupOpenMemberIndexBuilds);
    }

    [Fact]
    public async Task ConcurrentParsesAndModels_KeepIndependentIndexesAndIdenticalResults()
    {
        var source = Siblings(24);
        var shared = SourceProvenance.ParseValid(source).Parsed;
        var results = await Task.WhenAll(Enumerable.Range(0, 16).Select(_ => Task.Run(() =>
        {
            var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
            var detection = new FrontEndTraversalObservations();
            var (_, diagnostics) = ParameterDetector.DetectPrevalidated(syntax, null, detection);
            Assert.DoesNotContain(diagnostics, d => d.Severity == DiagnosticSeverity.Error);
            Assert.Equal(1, detection.LookupOpenMemberIndexBuilds);
            var parsed = SourceProvenance.ParseValid(source).Parsed;
            var observations = new FrontEndTraversalObservations();
            var model = SemanticModelBuilder.Build(shared, observations);
            Assert.Equal(1, observations.LookupOpenMemberIndexBuilds);
            Assert.Equal(new Result.Atom(0), Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root)).Value);
            return JsonSerializer.Serialize(new { model.IdentifierResolutions, model.Declarations, model.ScopeVisibilities });
        })));
        Assert.All(results, result => Assert.Equal(results[0], result));
    }

    [Fact]
    public void HostPreludeBuilds_UseFreshOperationCaches()
    {
        var operations = HostOperations.Create(HostOperation.Create("Observe", (_, _) => new Result.Atom(1)));
        var parsed = Parser.Parse(Siblings(24), new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        for (var run = 0; run < 3; run++)
        {
            var observations = new FrontEndTraversalObservations();
            var model = SemanticModelBuilder.Build(parsed, observations);
            Assert.Equal(1, observations.LookupOpenMemberIndexBuilds);
            Assert.Contains(model.GetVisibleSymbolsAt(new SourcePosition(1, 1)), symbol => symbol.Name == "Observe");
        }
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (Algorithm Target, WeakReference Cache, WeakReference Index) FinishedLookup()
    {
        var target = Owner([Member("x", 1)]);
        var cache = new OpenMemberIndexCache();
        var index = cache.IndexOf(target);
        return (target, new WeakReference(cache), new WeakReference(index));
    }

    [Fact]
    public void LiveTarget_DoesNotRetainFinishedOperationCacheOrIndex()
    {
        var finished = FinishedLookup();
        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
        Assert.False(finished.Cache.IsAlive);
        Assert.False(finished.Index.IsAlive);
        GC.KeepAlive(finished.Target);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (ParseResult Parse, SemanticModel Model, WeakReference Cache, WeakReference Index) FinishedModelBuild()
    {
        var parsed = SourceProvenance.ParseValid(Siblings(24)).Parsed;
        var type = typeof(SemanticModelBuilder).GetNestedType("Builder", BindingFlags.NonPublic)!;
        var builder = Activator.CreateInstance(type, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance,
            binder: null, args: [null, null, null], culture: null)!;
        var model = (SemanticModel)type.GetMethod("Build", [typeof(Algorithm)])!.Invoke(builder, [parsed.Root])!;
        var cache = (OpenMemberIndexCache)type.GetField("_openMemberIndexes", BindingFlags.Instance | BindingFlags.NonPublic)!.GetValue(builder)!;
        Assert.Equal(1, cache.Count);
        var index = cache.IndexOf(parsed.Root.Properties[0].Value);
        Assert.Equal(1, cache.Count);
        return (parsed, model, new WeakReference(cache), new WeakReference(index));
    }

    [Fact]
    public void LiveParseAndModel_DoNotKeepBuildCacheAlive()
    {
        var finished = FinishedModelBuild();
        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
        Assert.False(finished.Cache.IsAlive);
        Assert.False(finished.Index.IsAlive);
        GC.KeepAlive(finished.Parse);
        GC.KeepAlive(finished.Model);
    }

    [Fact]
    public void IndexHasNoMutationSurface_AndNoStaticTargetMap()
    {
        Assert.All(typeof(OpenTargetMemberIndex).GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic), field => Assert.True(field.IsInitOnly, field.Name));
        Assert.DoesNotContain(typeof(OpenTargetMemberIndex).GetMethods(BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly), method => method.Name != "Lookup");
        static bool ContainsIndex(Type type) => type == typeof(OpenMemberIndexCache) || type == typeof(OpenTargetMemberIndex)
            || type.IsGenericType && type.GetGenericArguments().Any(ContainsIndex);
        foreach (var type in typeof(Parser).Assembly.GetTypes())
            Assert.DoesNotContain(type.GetFields(BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic), field => ContainsIndex(field.FieldType));
    }

    [Theory]
    [InlineData(1, 5, 1)]
    [InlineData(0, 12, 3)]
    public async Task NestedDeferredOpens_FetchOnlySelectedRegions(int argument, int expected, int downloads)
    {
        var requested = new List<string>();
        var options = new RunOptions
        {
            AllowedHosts = ["katlang.org"],
            DownloadCode = async (url, _) =>
            {
                await Task.Yield();
                requested.Add(url);
                return url.EndsWith("eager.kat", StringComparison.Ordinal) ? "public Total = 5"
                    : url.EndsWith("outer.kat", StringComparison.Ordinal) ? "public Later = 3" : "public Deep = 4";
            },
        };
        var source = "open 'https://katlang.org/eager.kat'\nF(0) = {\nopen 'https://katlang.org/outer.kat'\nG(0) = {\nopen 'https://katlang.org/nested.kat'\nTotal + Later + Deep\n}\nG(n) = Total\nG(0)\n}\nF(n) = Total\nF(" + argument + ")";
        var parsed = (await SourceProvenance.ParseValidAsync(source, options)).Parsed;
        Assert.Single(requested);
        _ = SemanticModelBuilder.Build(parsed);
        Assert.Single(requested);
        var result = await Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.False(result.IsError);
        Assert.Equal(new Result.Atom(expected), result.Value);
        Assert.Equal(downloads, requested.Count);
        var repeated = await Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.Equal(new Result.Atom(expected), repeated.Value);
        Assert.Equal(downloads, requested.Count);
    }
}
