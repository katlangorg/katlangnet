using System.Collections.Immutable;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// F5: the lazy body index of shared static lookup facts is one snapshot, published atomically
/// once per view version. Readers are released together by a barrier before any index exists.
/// </summary>
public sealed class StaticLookupFactsConcurrencyTests
{
    private const int Readers = 8;

    private static Algorithm.User Empty(int tag) => new(null, [], [new Expr.Num(tag)], [], []);
    private static CompletedStaticStructures.BodyFacts Body(Algorithm body, StaticScopeKey? receiver)
        => new(body, receiver is null ? CompletedStaticStructures.Selection.Unavailable : new(StaticFactKind.Structure, receiver),
            CompletedStaticStructures.Selection.Unavailable, new Dictionary<string, StaticScopeKey>(), new HashSet<string>(),
            ImmutableArray<CompletedStaticStructures.Selection>.Empty);
    private static StaticScopeKey Key(StaticScopeKey parent, Algorithm body, object? region = null)
        => new(parent, OpenProviderIdentity.DeclarationOf(body), region as Pattern);

    private sealed record Catalog(CompletedStaticStructures Facts, StaticScopeKey Root, Algorithm Lone, Algorithm Shared,
        Algorithm X, StaticScopeKey LoneKey, StaticScopeKey SharedDirect, StaticScopeKey SharedNested, StaticScopeKey YKey);

    // `shared` is published directly under the root (receiver X) and nested under Y (receiver Y):
    // two contexts that disagree on the receiver. `lone` has one context and receiver X.
    private static Catalog Build()
    {
        var root = new StaticKeyTable().Root;
        var facts = new CompletedStaticStructures(root);
        Algorithm x = Empty(1), y = Empty(2), lone = Empty(3), shared = Empty(4);
        var xKey = Key(root, x);
        var yKey = Key(root, y);
        var loneKey = Key(root, lone);
        var direct = Key(root, shared);
        var nested = Key(yKey, shared);
        facts.Add(xKey, Body(x, null));
        facts.Add(yKey, Body(y, null));
        facts.Add(loneKey, Body(lone, xKey));
        facts.Add(direct, Body(shared, xKey));
        facts.Add(nested, Body(shared, yKey));
        return new(facts, root, lone, shared, x, loneKey, direct, nested, yKey);
    }

    private static void RunTogether(int count, Action<int> read)
    {
        using var barrier = new Barrier(count);
        var errors = new Exception?[count];
        var threads = Enumerable.Range(0, count).Select(i => new Thread(() =>
        {
            try
            {
                barrier.SignalAndWait();
                read(i);
            }
            catch (Exception error) { errors[i] = error; }
        })).ToArray();
        foreach (var thread in threads) thread.Start();
        foreach (var thread in threads) Assert.True(thread.Join(TimeSpan.FromSeconds(30)));
        Assert.All(errors, Assert.Null);
    }

    private static void AssertCatalog(Catalog c)
    {
        Assert.Same(c.LoneKey, c.Facts.ExactContext(c.Lone)!.Key);
        Assert.Same(c.X, c.Facts.AgreedReceiver(c.Lone));
        Assert.Throws<ArgumentException>(() => c.Facts.ExactContext(c.Shared));
        Assert.Throws<ArgumentException>(() => c.Facts.AgreedReceiver(c.Shared));
        Assert.Same(c.SharedDirect, c.Facts.ContextualBody(c.Root, c.Shared, null));
        Assert.Same(c.SharedNested, c.Facts.ContextualBody(c.YKey, c.Shared, null));
        Assert.Null(c.Facts.ContextualBody(c.Root, c.Shared, new Pattern.Bind("p")));
        Assert.Null(c.Facts.ContextualBody(c.LoneKey, c.Shared, null));
        Assert.Null(c.Facts.ExactContext(Empty(5)));
    }

    [Fact]
    public void ConcurrentFirstAccess_PublishesOneConsistentSnapshot()
    {
        var c = Build();
        c.Facts.Seal();
        Assert.Equal(0, c.Facts.BodyIndexBuilds);
        RunTogether(Readers, i =>
        {
            // Each reader starts with a different query so all three entry points race the first build.
            for (var round = 0; round < 3; round++)
                switch ((i + round) % 3)
                {
                    case 0: Assert.Same(c.LoneKey, c.Facts.ExactContext(c.Lone)!.Key); break;
                    case 1: Assert.Same(c.X, c.Facts.AgreedReceiver(c.Lone)); break;
                    default: Assert.Same(c.SharedNested, c.Facts.ContextualBody(c.YKey, c.Shared, null)); break;
                }
            AssertCatalog(c);
        });
        Assert.Equal(1, c.Facts.BodyIndexBuilds);
        Assert.Equal(c.Facts.Count, c.Facts.BodyIndexScopeVisits);
    }

    [Fact]
    public void ConcurrentSharedBodyLookups_KeepAmbiguityAndReceiverDisagreement()
    {
        var c = Build();
        c.Facts.Seal();
        RunTogether(Readers, i =>
        {
            if (i % 2 == 0) Assert.Throws<ArgumentException>(() => c.Facts.AgreedReceiver(c.Shared));
            else Assert.Throws<ArgumentException>(() => c.Facts.ExactContext(c.Shared));
            Assert.Same(i % 2 == 0 ? c.SharedDirect : c.SharedNested,
                c.Facts.ContextualBody(i % 2 == 0 ? c.Root : c.YKey, c.Shared, null));
        });
        Assert.Equal(1, c.Facts.BodyIndexBuilds);
    }

    [Fact]
    public void Retargeting_PublishesAFreshSnapshotAndNeverReusesTheStaleOne()
    {
        var c = Build();
        AssertCatalog(c);
        Assert.Equal(1, c.Facts.BodyIndexBuilds);
        var replacement = ((Algorithm.User)c.Lone) with { Output = [new Expr.Num(30)] };
        c.Facts.Retarget(c.LoneKey, replacement);
        Assert.Same(c.LoneKey, c.Facts.ExactContext(replacement)!.Key);
        Assert.Null(c.Facts.ExactContext(c.Lone));
        Assert.Same(c.X, c.Facts.AgreedReceiver(replacement));
        Assert.Null(c.Facts.AgreedReceiver(c.Lone));
        Assert.Same(c.SharedNested, c.Facts.ContextualBody(c.YKey, c.Shared, null));
        Assert.Equal(2, c.Facts.BodyIndexBuilds);
        c.Facts.Seal();
        Assert.Same(c.LoneKey, c.Facts.ExactContext(replacement)!.Key);
        Assert.Equal(2, c.Facts.BodyIndexBuilds); // Sealing preserves the version: no rebuild.
        var extension = new CompletedStaticStructures(c.Root, previous: c.Facts);
        Assert.Same(c.LoneKey, extension.ExactContext(replacement)!.Key);
        Assert.Null(extension.ExactContext(c.Lone));
        Assert.Equal(1, extension.BodyIndexBuilds);
    }

    // Delegates to real facts but faults while the first index is being built.
    private sealed class FaultingFacts(StaticLookupFacts source) : StaticLookupFacts
    {
        internal int Faults = 1;
        internal override StaticScopeKey PreludeKey => source.PreludeKey;
        internal override IEnumerable<StaticScopeKey> Scopes => source.Scopes;
        internal override void EnsureUsable() => source.EnsureUsable();
        internal override StaticScopeKey? Child(StaticScopeKey parent, Algorithm body, Pattern? pattern = null) => source.Child(parent, body, pattern);
        internal override CompletedStaticStructures.BodyFacts? Facts(StaticScopeKey key)
            => Interlocked.Decrement(ref Faults) == 0 ? throw new InvalidOperationException("injected") : source.Facts(key);
    }

    [Fact]
    public void FailedConstruction_PublishesNothing()
    {
        var c = Build();
        c.Facts.Seal();
        var faulting = new FaultingFacts(c.Facts);
        Assert.Equal("injected", Assert.Throws<InvalidOperationException>(() => faulting.ExactContext(c.Lone)).Message);
        Assert.Equal(0, faulting.BodyIndexBuilds);
        Assert.Equal(0, faulting.BodyIndexScopeVisits);
        Assert.Same(c.LoneKey, faulting.ExactContext(c.Lone)!.Key);
        Assert.Throws<ArgumentException>(() => faulting.AgreedReceiver(c.Shared));
        Assert.Equal(1, faulting.BodyIndexBuilds);
    }

    [Fact]
    public void FailedPublication_HidesAnAlreadyBuiltSnapshot()
    {
        var root = new StaticKeyTable().Root;
        var facts = new CompletedStaticStructures(root,
            resources: new StaticQueryResourceBudget(new(1000, 8, MaxStorageUnits: 1)));
        var body = Empty(1);
        var key = Key(root, body);
        facts.Add(key, Body(body, null));
        Assert.Same(key, facts.ExactContext(body)!.Key);
        // Retargeting charges metadata the budget refuses; the publication fails terminally.
        Assert.Throws<StaticQueryLimitExceededException>(() => facts.Retarget(key, body with { Output = [new Expr.Num(2)] }));
        Assert.True(facts.IsFailed);
        Assert.Throws<InvalidOperationException>(() => facts.ExactContext(body));
        Assert.Throws<InvalidOperationException>(() => facts.AgreedReceiver(body));
        Assert.Throws<InvalidOperationException>(() => facts.ContextualBody(root, body, null));
        Assert.Equal(1, facts.BodyIndexBuilds);
    }

    private static string Fingerprint(SemanticModel model)
        => string.Join('\n', model.IdentifierResolutions.Select(r =>
                $"{r.Occurrence.Name}@{r.Occurrence.Span.Start}:{r.Classification}->{r.ResolvedDeclaration?.Span.Start}/{r.ResolvedProperty?.Name}")
            .Concat(model.PropertyInfos.Select(p => $"P:{p.Name}")));

    [Fact]
    public void ParallelSemanticModels_ShareCompletedFactsConsistently()
    {
        const string source = "Lib={public K=9\npublic F(a)=a+K\n0}\nAlias=Lib\nUse={open Alias\nF(K)}\nAlias.K+Lib.F(1)+Use";
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(';', parsed.Diagnostics));
        var facts = parsed.Root.CompletedStructure!.Facts;
        Assert.True(facts.IsSealed);
        var builds = facts.BodyIndexBuilds;
        var fingerprints = new string[Readers];
        RunTogether(Readers, i => fingerprints[i] = Fingerprint(SemanticModelBuilder.Build(parsed)));
        var expected = Fingerprint(SemanticModelBuilder.Build(parsed));
        Assert.Contains("Alias", expected, StringComparison.Ordinal);
        Assert.All(fingerprints, fingerprint => Assert.Equal(expected, fingerprint));
        Assert.InRange(facts.BodyIndexBuilds, builds, builds + 1);
    }
}
