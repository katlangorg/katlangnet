namespace KatLang.Tests;

public sealed class StaticStructureQueryTests
{
    [Fact]
    public void RuntimeRecipeIdentityIsTransported_WithoutPublishingAStaticNamespace()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot("Mk(n)=n+1\nF(x)=x\nA=Mk(F+0).Algorithm\nB=A\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var a = operation.ContextOf(operation.Root, root.Properties.Single(p => p.Name == "A").Value);
        var b = operation.ContextOf(operation.Root, root.Properties.Single(p => p.Name == "B").Value);
        var fact = operation.Read(StaticQueryKey.TargetWalk(b, StaticCycleCheck.Formation));
        Assert.Equal(StaticFactKind.Runtime, fact.Kind);
        Assert.Same(a, fact.Scope);
        Assert.Null(operation.StructureCell(b));
    }
    private static readonly StaticQueryLimits Limits = new(1_000_000, 4, 200_000, 4_000_000);
    private static (Algorithm Root, StaticStructureQueries Queries) Model(string source)
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        return (root, new(root, Limits));
    }
    private static StaticScopeKey Child(StaticStructureQueries queries, StaticScopeKey parent, string name)
        => queries.BodyIn(parent, queries.BodyOf(parent).Properties.Single(p => p.Name == name).Value);
    private static string[] Inputs(StaticStructureQueries queries, StaticScopeKey scope)
        => Assert.IsType<string[]>(queries.Get(StaticQueryKey.Inputs(scope)).Data);

    [Fact]
    public void OrdinaryFreeNames_DoNotAcquireArtificialSelfDependencies()
    {
        var (_, q) = Model("P = x + y + x\n0");
        var p = Child(q, q.Root, "P");
        Assert.Equal(new[] { "x", "y" }, Inputs(q, p));
        Assert.Equal(StaticFactKind.Yes, q.Get(StaticQueryKey.IsInput(p, "x")).Kind);
        var binding = q.Get(StaticQueryKey.Binding(p, "x", StaticCycleCheck.Formation));
        Assert.Equal(StaticFactKind.Parameter, binding.Kind);
        Assert.Same(p, binding.Scope);
    }

    [Fact]
    public void ExplicitAncestorParameter_PrecedesNestedOpens()
    {
        var (_, q) = Model("Lib = { public x = 9\n0 }\nP(x) = { N = { open Lib\nx + 1 }\nN }\n0");
        var p = Child(q, q.Root, "P");
        var n = Child(q, p, "N");
        Assert.Empty(Inputs(q, n));
        var binding = q.Get(StaticQueryKey.Binding(n, "x", StaticCycleCheck.Formation));
        Assert.Equal(StaticFactKind.Parameter, binding.Kind);
        Assert.Same(p, binding.Scope);
    }

    [Fact]
    public void MembersAreWrittenIdentity_AndIncludePrivateDeclarations()
    {
        var (_, q) = Model("Lib = { V = 1\npublic W = 2\n0 }\n0");
        var lib = Child(q, q.Root, "Lib");
        var members = Assert.IsType<StaticMembers>(q.Get(StaticQueryKey.Members(lib)).Data);
        Assert.Same(q.BodyOf(lib).Properties[0], members.Declared("V"));
        Assert.Null(members.Public("V"));
        Assert.Same(q.BodyOf(lib).Properties[1], members.Public("W"));
    }

    [Fact]
    public void TransparentReferencesTransportIdentity_AndBracesKeepTheirOwnStructure()
    {
        var (_, q) = Model("Lib = { public V = 42\n0 }\nA = Lib\nC = { Lib }\n0");
        var lib = Child(q, q.Root, "Lib");
        var a = Child(q, q.Root, "A");
        var c = Child(q, q.Root, "C");
        Assert.Same(lib, q.Get(StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation)).Scope);
        Assert.Same(c, q.Get(StaticQueryKey.TargetWalk(c, StaticCycleCheck.Formation)).Scope);
    }

    [Fact]
    public void ODDTargetCyclesPassThroughCarriers_WithoutErasingTheirStructure()
    {
        var (_, q) = Model("A = B\nB = { public X = 1\nA }\n0");
        var a = Child(q, q.Root, "A");
        var b = Child(q, q.Root, "B");
        Assert.Same(a, q.Get(StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation)).Scope);
        Assert.Same(b, q.Get(StaticQueryKey.TargetWalk(b, StaticCycleCheck.Formation)).Scope);
        Assert.Equal(StaticFactKind.Refused, q.Get(StaticQueryKey.Project(StaticQueryKind.TargetWalk, a,
            StaticQueryProjection.TargetCycle, stratum: StaticCycleCheck.None)).Kind);
    }

    [Fact]
    public void OD_B_ParameterRootedMemberReferences_InferNoMemberNames()
    {
        var (_, q) = Model("P(b) = { A = b.C.D\nA }\n0");
        var p = Child(q, q.Root, "P");
        var a = Child(q, p, "A");
        Assert.Empty(Inputs(q, a));
        Assert.Equal(StaticFactKind.Runtime, q.Get(StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation)).Kind);
    }

    [Fact]
    public void OpensDeduplicateTheTransportedProvider_AndPreserveAmbiguity()
    {
        var (_, q) = Model("Lib = { public V = 42\n0 }\nA = Lib\nOther = { public V = 9\n0 }\nP = { open A, Lib\nV + 0 }\nQ = { open A, Other\nV + 0 }\n0");
        var p = Child(q, q.Root, "P");
        var other = Child(q, q.Root, "Q");
        Assert.Empty(Inputs(q, p));
        var providers = Assert.IsType<StaticScopeKey[]>(q.Get(StaticQueryKey.OpenProviders(p, StaticCycleCheck.Formation)).Data);
        Assert.Single(providers);
        Assert.Same(Child(q, q.Root, "Lib"), providers[0]);
        Assert.Equal(StaticFactKind.Ambiguous, q.Get(StaticQueryKey.Binding(other, "V", StaticCycleCheck.Formation)).Kind);
        Assert.Empty(Inputs(q, other));
    }

    [Fact]
    public void RuntimeMay_IsDefiniteInformation_DistinctFromUnresolvedStaticKnowledge()
    {
        var (_, q) = Model("P(b) = b.M\n0");
        var p = Child(q, q.Root, "P");
        var edge = Assert.IsType<Expr.DotCall>(((Algorithm.User)q.BodyOf(p)).Output[0]);
        Assert.Equal(StaticFactKind.May, q.Get(StaticQueryKey.MissSelection(p, edge)).Kind);
        Assert.Empty(Inputs(q, p));
    }

    [Fact]
    public void OpenReferenceRowsNeverResolveTheirHeadsThroughAnotherOpen()
    {
        var (_, q) = Model("Lib = { public Target = { public V = 42\n0 }\n0 }\nP = { open Lib\nA = Target\nH = { open A\nV + 0 }\n0 }\n0");
        var p = Child(q, q.Root, "P");
        var a = Child(q, p, "A");
        var h = Child(q, p, "H");
        Assert.Equal(StaticFactKind.Structure, q.Get(StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation)).Kind);
        Assert.Empty(Assert.IsType<StaticScopeKey[]>(q.Get(StaticQueryKey.OpenProviders(h, StaticCycleCheck.Formation)).Data));
        Assert.Equal(new[] { "V" }, Inputs(q, h));
    }

    [Fact]
    public void InlineOpenBlocksAreRootedAtThePrelude_AndCannotCaptureTheHolder()
    {
        var (_, q) = Model("P(x) = { open { public V = x\n0 }\nV }\n0");
        var p = Child(q, q.Root, "P");
        var providers = Assert.IsType<StaticScopeKey[]>(q.Get(StaticQueryKey.OpenProviders(p, StaticCycleCheck.Formation)).Data);
        var provider = Assert.Single(providers);
        var v = Child(q, provider, "V");
        Assert.Equal(new[] { "x" }, Inputs(q, v));
        Assert.NotSame(p, q.Get(StaticQueryKey.Binding(v, "x", StaticCycleCheck.Formation)).Scope);
    }

    [Fact]
    public void GraceUsesSemanticOccurrenceOrder_AndExactSharedDagMultiplicity()
    {
        var (_, q) = Model("P = a~~ + b~\n0");
        Assert.Equal(new[] { "b", "a" }, Inputs(q, Child(q, q.Root, "P")));
        var shared = new Expr.Grace(new Expr.Resolve("a"), 1);
        var body = new Algorithm.User(null, [], [], [], [new Expr.Binary(BinaryOp.Add, shared, new Expr.Binary(BinaryOp.Add, new Expr.Resolve("b"), shared))]);
        var root = new Algorithm.User(null, [], [], [new Property("P", body)], []);
        var host = new StaticStructureQueries(root, Limits);
        Assert.Equal(new[] { "b", "a" }, Inputs(host, Child(host, host.Root, "P")));
    }

    [Fact]
    public void ScopeAndQueryDemandPermutations_PreserveBindingAndStructure()
    {
        foreach (var order in new[] { new[] { 0, 1, 2, 3 }, new[] { 3, 2, 1, 0 }, new[] { 1, 3, 0, 2 } })
        {
            var (_, q) = Model("Lib = { public V = 42\n0 }\nA = Lib\nP = A.V + x\n0");
            var a = Child(q, q.Root, "A");
            var p = Child(q, q.Root, "P");
            var keys = new[] { StaticQueryKey.Inputs(p), StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation),
                StaticQueryKey.Binding(p, "A", StaticCycleCheck.Formation), StaticQueryKey.IsInput(p, "x") };
            foreach (var index in order) q.Get(keys[index]);
            Assert.Equal(new[] { "x" }, Inputs(q, p));
            Assert.Same(Child(q, q.Root, "Lib"), q.Get(keys[1]).Scope);
        }
    }

    [Fact]
    public void HostSharedBranchBodies_DistinguishTheirPatternBindingRegions()
    {
        var (_, q) = Model("Template = { N = x\n0 }\n0");
        var body = q.BodyOf(q.Root).Properties.Single().Value;
        var xPattern = new Pattern.Bind("x");
        var yPattern = new Pattern.Bind("y");
        var xBody = q.BranchBodyIn(q.Root, body, xPattern);
        var yBody = q.BranchBodyIn(q.Root, body, yPattern);
        Assert.NotSame(xBody, yBody);
        Assert.Same(body.Declaration, xBody.Declaration);
        Assert.Same(xBody, q.BranchBodyIn(q.Root, body, xPattern));
        Assert.Empty(Inputs(q, xBody));
        Assert.Empty(Inputs(q, yBody));
        Assert.Equal(StaticFactKind.Parameter, q.Get(StaticQueryKey.Binding(xBody, "x", StaticCycleCheck.Formation)).Kind);
        Assert.Equal(StaticFactKind.Missing, q.Get(StaticQueryKey.Binding(yBody, "x", StaticCycleCheck.Formation)).Kind);
        Assert.Empty(Inputs(q, Child(q, xBody, "N")));
        Assert.Equal(new[] { "x" }, Inputs(q, Child(q, yBody, "N")));
    }

    [Fact]
    public void AlgorithmLinksThroughCallResults_RetainTheRuntimeStructureBoundary()
    {
        var (_, q) = Model("C(meta op) = op\nF(x) = x\nA = C(F(1)).Algorithm\nP = A.Q + 0\n0");
        var a = Child(q, q.Root, "A");
        var p = Child(q, q.Root, "P");
        Assert.Empty(Inputs(q, a));
        Assert.Equal(StaticFactKind.Runtime, q.Get(StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation)).Kind);
        var edge = Assert.IsType<Expr.DotCall>(((Expr.Binary)((Algorithm.User)q.BodyOf(p)).Output[0]).Left);
        Assert.Equal(StaticFactKind.May, q.Get(StaticQueryKey.MissSelection(p, edge)).Kind);
    }

    [Fact]
    public void ModuleExpansionMarksDoNotFreezeInference_AndModuleScopesAreHygienicAndShared()
    {
        var (_, q) = Model("x = 9\nHolder(a) = 0\nOther(b) = 0\n0");
        var holder = Child(q, q.Root, "Holder");
        var other = Child(q, q.Root, "Other");
        var module = ((Algorithm.User)SourceProvenance.ParseSyntaxValidRoot("x")) with { IsModuleElaborated = true };
        var first = q.BodyIn(holder, module);
        Assert.Same(first, q.BodyIn(other, module));
        Assert.Same(q.Keys.Root, first.Parent);
        Assert.Equal(new[] { "x" }, Inputs(q, first));
        var namespaceModule = ((Algorithm.User)SourceProvenance.ParseSyntaxValidRoot("count")) with { IsModuleElaborated = true };
        var scope = q.BodyIn(holder, namespaceModule);
        Assert.Same(scope, q.Get(StaticQueryKey.TargetWalk(scope, StaticCycleCheck.Formation)).Scope);
    }
}
