namespace KatLang.Tests;

public sealed class SuggestionScopeAdmissionTests
{
    private static Algorithm.User User(IReadOnlyList<Property>? properties = null, IReadOnlyList<Expr>? opens = null)
        => new(null, [], opens ?? [], properties ?? [], [new Expr.Num(0)]);

    private static ElaboratedPropertyScope Admitted(Algorithm root, FrontEndTraversalObservations? work = null)
    {
        var context = AnalyzedStaticStructures.ForBoundAst(root);
        var cache = new OpenMemberIndexCache(work);
        var prelude = ElaboratedScopeLookup.CreateScope(context.Facts.Prelude, observations: work, memberIndexes: cache,
            completedContext: context.Facts.Context(context.Facts.PreludeKey));
        return ElaboratedScopeLookup.CreateScope(root, prelude, completedContext: context);
    }

    [Fact]
    public void EqualNamesUnderDistinctOwners_KeepContextsAndShareOnlyTheImmutableIndex()
    {
        var hidden = new Property("X", User());
        var first = new Property("X", User(), IsPublic: true);
        var later = new Property("X", User(), IsPublic: true);
        var library = User([hidden, first, later]);
        var left = User([new Property("Lib", library)], [new Expr.Resolve("Lib")]);
        var right = User([new Property("Lib", library)], [new Expr.Resolve("Lib")]);
        var root = User([new Property("Left", left), new Property("Right", right)]);
        var work = new FrontEndTraversalObservations();
        var owner = Admitted(root, work);
        var a = ElaboratedScopeLookup.CreateScope(left, owner);
        var b = ElaboratedScopeLookup.CreateScope(right, owner);
        Assert.Same(owner.BoundLookupContext().Facts, a.BoundLookupContext().Facts);
        Assert.Same(a.BoundLookupContext().Facts, b.BoundLookupContext().Facts);
        Assert.NotSame(a.BoundLookupContext().Key, b.BoundLookupContext().Key);
        var ap = Assert.Single(a.GetResolvedOpenProviders());
        var bp = Assert.Single(b.GetResolvedOpenProviders());
        Assert.NotEqual(ap.Identity, bp.Identity);
        Assert.Same(library, ap.Target);
        Assert.Same(library, bp.Target);
        Assert.Same(first, ap.TryLookupPublicMember("X")!.Value.Property);
        Assert.Same(first, bp.TryLookupPublicMember("X")!.Value.Property);
        Assert.Equal(1, work.LookupOpenMemberIndexBuilds);
        Assert.Null(root.CompletedStructure); // Analysis is not successful program publication.
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DirectInlineMissingAndAmbiguousProviders_PreserveOrderingAndOwnedShadowing(bool shadow)
    {
        var first = User([new Property("Shared", User(), IsPublic: true), new Property("OnlyA", User(), IsPublic: true)]);
        var second = User([new Property("Shared", User(), IsPublic: true), new Property("OnlyB", User(), IsPublic: true)]);
        var own = new Property("Shared", User());
        var root = User(shadow ? [new Property("A", first), own] : [new Property("A", first)],
            [new Expr.Resolve("A"), new Expr.AlgorithmExpr(second), new Expr.Resolve("MissingProvider")]);
        var scope = Admitted(root);
        var providers = scope.GetResolvedOpenProviders();
        Assert.Equal(2, providers.Count);
        Assert.Same(first, providers[0].Target);
        Assert.Same(second, providers[1].Target);
        Assert.NotEqual(providers[0].Identity, providers[1].Identity);
        var hits = ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, "Shared");
        if (shadow) Assert.Same(own, Assert.Single(hits).Property);
        else
        {
            Assert.Equal(2, hits.Count); // Multiple matches expose ambiguity; none is selected.
            Assert.Same(first.Properties[0], hits[0].Property);
            Assert.Same(second.Properties[0], hits[1].Property);
        }
        Assert.Empty(ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, "MissingProvider"));
        var query = Assert.IsType<LexicalSuggestionQuery>(new SuggestionContexts().Capture("zz", scope, ParameterOwnership.Empty, null));
        Assert.Contains("OnlyA", query.Candidates.Names);
        Assert.Contains("OnlyB", query.Candidates.Names);
        Assert.Equal(shadow, query.Candidates.Names.Contains("Shared"));
        Assert.DoesNotContain("MissingProvider", query.Candidates.Names);
    }

    [Fact]
    public void SharedBranchBodies_KeepTheActualPatternRegions()
    {
        var body = new Algorithm.User(null, [], [], [], [new Expr.Param("n")]);
        var first = new Pattern.Bind("n");
        var second = new Pattern.Bind("n");
        var family = new Algorithm.Conditional(null, [], [new CondBranch(first, body), new CondBranch(second, body)]);
        var root = Admitted(User([new Property("F", family)]));
        var level = ElaboratedScopeLookup.CreateScope(family, root);
        var a = ElaboratedScopeLookup.CreateScope(body, level, branchPattern: first).BoundLookupContext();
        var b = ElaboratedScopeLookup.CreateScope(body, level, branchPattern: second).BoundLookupContext();
        Assert.Same(a.Facts, b.Facts);
        Assert.NotSame(a.Key, b.Key);
        Assert.Same(first, a.Key.BindingRegion);
        Assert.Same(second, b.Key.BindingRegion);
        Assert.Same(body, a.Facts.Facts(a.Key)!.Body);
        Assert.Same(body, b.Facts.Facts(b.Key)!.Body);
    }

    [Fact]
    public void RawAndResolvedReferences_KeepDifferentNamespaceMeanings()
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot("Lib={public K=7\n0}\nA=Lib\n0");
        var library = syntax.Properties.Single(p => p.Name == "Lib").Value;
        var writtenUser = syntax.Properties.Single(p => p.Name == "A").Value;
        var raw = ElaboratedScopeLookup.CreateScope(syntax, sourcePhase: StaticAstPhase.RawSource);
        var resolved = Admitted(syntax); // Supplied as a final User, never silently converted into an Alias.
        Assert.Same(library, ElaboratedScopeLookup.CompletedReceiver(new Expr.Resolve("A"), raw).Algorithm);
        Assert.Same(writtenUser, ElaboratedScopeLookup.CompletedReceiver(new Expr.Resolve("A"), resolved).Algorithm);
        Assert.IsType<Algorithm.User>(writtenUser);
        Assert.IsType<Expr.Resolve>(Assert.Single(writtenUser.Output));
        Assert.Null(syntax.CompletedStructure);
    }

    [Fact]
    public void DetachedDefinitionsRequireCoherentReadmissionOfTheActualGraph()
    {
        var root = SourceProvenance.ParseValid("Lib={public K=7\n0}\nReader={open Lib\n0}\n0").Root;
        var scope = Admitted(root);
        Assert.Same(root.CompletedStructure!.Facts, scope.BoundLookupContext().Facts);
        var library = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "Lib").Value);
        var replacement = User();
        var changedLibrary = library with { Properties = [library.Properties.Single().WithValue(replacement)] };
        var detached = ElaboratedScopeLookup.CreateScope(changedLibrary, scope);
        Assert.Throws<InvalidOperationException>(() => detached.BoundLookupContext());
        var changed = root with { Properties = root.Properties.Select(p => p.Name == "Lib" ? p.WithValue(changedLibrary) : p).ToArray() };
        var admitted = Admitted(changed);
        var reader = ElaboratedScopeLookup.CreateScope(changed.Properties.Single(p => p.Name == "Reader").Value, admitted);
        Assert.Same(replacement, Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(reader, "K")).Property.Value);
        Assert.NotSame(scope.BoundLookupContext().Facts, admitted.BoundLookupContext().Facts);
    }

    [Fact]
    public void CancelledAndMismatchedAdmission_RemainsAnExplicitRefusal()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var root = SourceProvenance.ParseValid("X=1\nX").Root;
        var error = Assert.Throws<OperationCanceledException>(() => AnalyzedStaticStructures.ForBoundAst(root, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Throws<ArgumentException>(() => ElaboratedScopeLookup.CreateScope(root, sourcePhase: StaticAstPhase.RawSource));
    }

    [Theory]
    [InlineData(8)]
    [InlineData(32)]
    public void RelatedConsumers_ReuseOneProviderIndex(int consumers)
    {
        var library = User(Enumerable.Range(0, 32).Select(i => new Property($"m{i}", User(), IsPublic: true)).ToArray());
        var children = Enumerable.Range(0, consumers).Select(_ => User(opens: [new Expr.Resolve("Lib")])).ToArray();
        var properties = new[] { new Property("Lib", library) }.Concat(children.Select((body, i) => new Property($"C{i}", body))).ToArray();
        var work = new FrontEndTraversalObservations();
        var root = Admitted(User(properties), work);
        foreach (var child in children)
        {
            var level = ElaboratedScopeLookup.CreateScope(child, root);
            Assert.Same(root.BoundLookupContext().Facts, level.BoundLookupContext().Facts);
            var provider = Assert.Single(level.GetResolvedOpenProviders());
            Assert.Same(library, provider.Target);
            Assert.Same(library.Properties[0], provider.TryLookupPublicMember("m0")!.Value.Property);
        }
        Assert.Equal(1, work.LookupOpenMemberIndexBuilds);
    }
}
