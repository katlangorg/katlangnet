namespace KatLang.Tests;

/// <summary>
/// AST-U1-A1: the variant-preserving own-scope updates (<c>Algorithm.WithOwnScope</c> and
/// <c>Algorithm.WithOwnScopeBody</c>) shared by the exposure pass's scope-body rewrite and the
/// resolver's lone-row completion. They replace a user algorithm's or a callable alias's OWN opens,
/// declarations and rows — never a target's — and keep the variant, declaration identity and every
/// carried fact.
/// </summary>
public class OwnScopeBodyUpdateTests
{
    private static readonly Expr.Resolve TargetRow = new("F");

    private static Algorithm.User ModuleUser() => new(
        new ScopeCtx(null, [], []),
        [new CaptureParameterPattern("x")],
        [new Expr.Resolve("Lib")],
        [new Property("P", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))],
        [new Expr.Num(1), new Expr.Num(2)])
    {
        HasExplicitParameterList = true,
        IsModuleElaborated = true,
    };

    [Fact]
    public void User_ReplacesOnlyItsOwnScopeAndRows_KeepingIdentityAndParameters()
    {
        var user = ModuleUser();
        List<Expr> opens = [new Expr.Resolve("Other")];
        List<Property> properties = [];
        var first = new Expr.Num(3);
        var empty = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], []));

        var updated = Assert.IsType<Algorithm.User>(user.WithOwnScopeBody(opens, properties, [first, empty, first]));

        Assert.Same(user.Declaration, updated.Declaration);
        Assert.Same(user.Parent, updated.Parent);
        Assert.Same(user.ParameterPatterns, updated.ParameterPatterns);
        Assert.True(updated.HasExplicitParameterList);
        Assert.True(updated.IsModuleElaborated);
        Assert.Same(opens, updated.Opens);
        Assert.Same(properties, updated.Properties);
        // Order, multiplicity, a visible empty value and expression identity are the rows given.
        Assert.Equal(3, updated.Output.Count);
        Assert.Same(first, updated.Output[0]);
        Assert.Same(empty, updated.Output[1]);
        Assert.Same(first, updated.Output[2]);

        Assert.Same(OutputBundle.Empty, Assert.IsType<Algorithm.User>(user.WithOwnScopeBody(opens, properties, [])).Output);

        // The own-scope update leaves the output bundle itself in place.
        var scoped = Assert.IsType<Algorithm.User>(user.WithOwnScope(opens, properties));
        Assert.Same(user.Output, scoped.Output);
        Assert.Same(user.Declaration, scoped.Declaration);

        // Passing the stored bundle back must keep its storage, including an unchanged body.
        var unchanged = Assert.IsType<Algorithm.User>(user.WithOwnScopeBody(user.Opens, user.Properties, user.Output));
        Assert.Same(user.Declaration, unchanged.Declaration);
        Assert.Same(user.Parent, unchanged.Parent);
        Assert.Same(user.ParameterPatterns, unchanged.ParameterPatterns);
        Assert.Same(user.Opens, unchanged.Opens);
        Assert.Same(user.Properties, unchanged.Properties);
        Assert.Same(user.Output, unchanged.Output);
    }

    [Fact]
    public void Alias_KeepsItsOneTargetRowAndTargetFacts_AndNeverBecomesAUser()
    {
        var body = ModuleUser() with { ParameterPatterns = [], HasExplicitParameterList = false };
        var alias = new Algorithm.Alias(body, TargetRow) { HasRuntimeTarget = true };
        List<Expr> opens = [];
        List<Property> properties = [new Property("Own", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]))];
        var rewrittenRow = new Expr.Resolve("F");

        var updated = Assert.IsType<Algorithm.Alias>(alias.WithOwnScopeBody(opens, properties, [rewrittenRow]));

        Assert.Same(body.Declaration, updated.Declaration);
        Assert.Same(alias.Parent, updated.Parent);
        Assert.True(updated.IsModuleElaborated);
        Assert.True(updated.HasRuntimeTarget);
        Assert.Same(rewrittenRow, updated.Target);
        Assert.Same(opens, updated.Opens);
        Assert.Same(properties, updated.Properties);
        // An alias still declares no parameter list of its own.
        Assert.Empty(((Algorithm)updated).ParameterPatterns);

        var scoped = Assert.IsType<Algorithm.Alias>(alias.WithOwnScope(opens, properties));
        Assert.Same(TargetRow, scoped.Target);
        Assert.Same(body.Declaration, scoped.Declaration);
        Assert.True(scoped.HasRuntimeTarget);
    }

    [Fact]
    public void Alias_RowCountOtherThanOne_FailsInsteadOfTruncatingOrInventingATarget()
    {
        var alias = new Algorithm.Alias(null, [], [], TargetRow);

        Assert.Throws<InvalidOperationException>(() => alias.WithOwnScopeBody([], [], []));
        Assert.Throws<InvalidOperationException>(() => alias.WithOwnScopeBody([], [], [TargetRow, new Expr.Num(1)]));
    }

    [Fact]
    public void BuiltinAndFamily_HaveNoScopeBodyToReplace()
    {
        Algorithm[] others =
        [
            new Algorithm.Builtin(BuiltinId.count),
            new Algorithm.Conditional(null, [new Expr.Resolve("Lib")], []),
        ];
        foreach (var other in others)
        {
            Assert.Throws<InvalidOperationException>(() => other.WithOwnScope([], []));
            Assert.Throws<InvalidOperationException>(() => other.WithOwnScopeBody([], [], [TargetRow]));
        }
    }

    [Fact]
    public void StoredListsAreBorrowed_SoLaterHostMutationsAndWithCopiesReadThrough()
    {
        List<ParameterPattern> patternItems = [new CaptureParameterPattern("a"), new CaptureParameterPattern("b")];
        var user = new Algorithm.User(null, [new SequenceValueParameterPattern(patternItems)], [], [], [new Expr.Num(1)]);
        List<Expr> opens = [];
        List<Property> properties = [];
        var scoped = Assert.IsType<Algorithm.User>(user.WithOwnScope(opens, properties));
        var storedRow = new Expr.Num(2);
        List<Expr> rows = [storedRow];
        var rewritten = Assert.IsType<Algorithm.User>(user.WithOwnScopeBody(opens, properties, rows));
        var alias = new Algorithm.Alias(null, [], [], TargetRow);
        var scopedAlias = Assert.IsType<Algorithm.Alias>(alias.WithOwnScope(opens, properties));
        var rewrittenAlias = Assert.IsType<Algorithm.Alias>(alias.WithOwnScopeBody(opens, properties, [TargetRow]));

        Algorithm[] views =
        [
            scoped, scoped with { }, rewritten, rewritten with { },
            scopedAlias, scopedAlias with { }, rewrittenAlias, rewrittenAlias with { },
        ];

        properties.Add(new Property("Late", new Algorithm.User(null, [], [], [], [new Expr.Num(2)])));
        var lateOpen = new Expr.Resolve("LateLib");
        opens.Add(lateOpen);
        patternItems.Add(new CaptureParameterPattern("c"));
        rows.Add(new Expr.Num(3));

        foreach (var view in views)
        {
            Assert.Equal("Late", Assert.Single(view.Properties).Name);
            Assert.Same(lateOpen, Assert.Single(view.Opens));
        }
        foreach (var view in views.OfType<Algorithm.User>())
            Assert.Equal(["a", "b", "c"], view.Params);

        // OutputBundle has its own snapshot contract; later list membership changes stay outside it.
        Assert.Same(storedRow, Assert.Single(rewritten.Output));
    }

    [Fact]
    public void StaticAlias_KeepsResolvedTargetFactsAndItsOwnNamespace_ThroughBothUpdates()
    {
        const string source = "F(x) = {\n    TargetMember = 99\n    x\n}\nA = {\n    Own = 7\n    F\n}\nA(3)";
        var root = SourceProvenance.ParseValid(source).Root;
        var alias = Assert.IsType<Algorithm.Alias>(root.Properties.Single(p => p.Name == "A").Value);
        var targetFacts = Assert.IsType<ImplicitArgumentResolver.AliasTarget>(alias.ResolvedTarget);
        Assert.False(alias.HasRuntimeTarget);
        Assert.Equal("Own", Assert.Single(alias.Properties).Name);
        Assert.Equal("TargetMember", Assert.Single(targetFacts.Algorithm.Properties).Name);

        var scoped = Assert.IsType<Algorithm.Alias>(alias.WithOwnScope(alias.Opens, alias.Properties));
        var rewrittenRow = new Expr.Resolve("F");
        var rewritten = Assert.IsType<Algorithm.Alias>(alias.WithOwnScopeBody(alias.Opens, alias.Properties, [rewrittenRow]));
        foreach (var view in new[] { scoped, rewritten })
        {
            Assert.Same(alias.Declaration, view.Declaration);
            Assert.Same(targetFacts, view.ResolvedTarget);
            Assert.False(view.HasRuntimeTarget);
            Assert.Same(alias.Properties, view.Properties);
            Assert.Equal("Own", Assert.Single(view.Properties).Name);
            Assert.Empty(((Algorithm)view).ParameterPatterns);
        }
        Assert.Same(alias.Target, scoped.Target);
        Assert.Same(rewrittenRow, rewritten.Target);
    }

    [Fact]
    public void ElaboratedRuntimeAlias_KeepsVariantFactsAndOwnMembers_ThroughBothConsumers()
    {
        // The resolver's lone-row completion and the exposure pass both rewrite this alias's own scope:
        // its own member K is classified against the enclosing parameter n, while the alias keeps its
        // runtime-target classification and its own row — the parameter f, never f's target body.
        const string source = "Apply(f, n) = {\n    A = {\n        K = n * 2\n        f\n    }\n    A\n}\nInc(x) = x + 1\nApply(Inc, 3)";
        var root = SourceProvenance.ParseValid(source).Root;
        var apply = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "Apply").Value);
        var alias = Assert.IsType<Algorithm.Alias>(apply.Properties.Single(p => p.Name == "A").Value);

        Assert.True(alias.HasRuntimeTarget);
        Assert.Null(alias.ResolvedTarget);
        Assert.Equal("f", Assert.IsType<Expr.Param>(alias.Target).Name);
        var own = Assert.Single(alias.Properties);
        Assert.Equal("K", own.Name);
        Assert.Equal(["n"], own.RequiredAncestorParameters);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, own.Exposure);
    }
}
