using KatLang.Semantics;
using System.Numerics;
using Xunit.Abstractions;
using System.Runtime.CompilerServices;

namespace KatLang.Tests;

public sealed class StandaloneScopeRecoveryTests(ITestOutputHelper output)
{
    private static Algorithm.User Value(int value) => new(null, [], [], [], [new Expr.Num(value)]);
    private static Algorithm.User Syntax(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.False(parsed.HasErrors);
        return parsed.Root;
    }

    [Fact]
    public void MissingPhaseFailsExplicitlyInsteadOfInventingAResolvedNamespace()
    {
        var root = Syntax("Lib={public K=7\n0}\nA=Lib\nP={open A\nK}\n0");
        var scope = ElaboratedScopeLookup.CreateScope(root);
        var body = root.Properties.Single(p => p.Name == "P").Value;
        var child = ElaboratedScopeLookup.CreateScope(body, scope);
        Assert.Contains("provenance", Assert.Throws<InvalidOperationException>(() => child.GetResolvedOpenProviders()).Message);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    public void ExplicitPhasePreservesDirectNestedAndOpenedReferenceStructure(int phaseValue)
    {
        var phase=(StaticAstPhase)phaseValue;
        var root = Syntax("Lib={public K=7\n0}\nA=Lib\nBox={public C=Lib\n0}\nB=Box.C\nP={open A,B\nK}\n0");
        var scope = ElaboratedScopeLookup.CreateScope(root, sourcePhase: phase);
        var p = ElaboratedScopeLookup.CreateScope(root.Properties.Single(p => p.Name == "P").Value, scope);
        Assert.Single(p.GetResolvedOpenProviders());
        var member = Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(p, "K"));
        Assert.Equal((Decimal128)7, Assert.IsType<Expr.Num>(member.Property.Value.Output.Single()).Value);
        Assert.Same(scope.StandaloneAnalysis().Source, p.StandaloneAnalysis().Source);
    }

    [Fact]
    public void ResolvedUserAndActualAliasRemainDifferentAfterHostModification()
    {
        var library = new Algorithm.User(null, [], [], [new Property("K", Value(7)) { IsPublic=true }], [new Expr.Num(0)]);
        var user = new Algorithm.User(null, [], [], [], [new Expr.Resolve("Lib")]);
        var alias = new Algorithm.Alias(user, user.Output[0]);
        var root = new Algorithm.User(null, [], [new Expr.Resolve("A")], [new Property("Lib",library),new Property("User",user),new Property("A",alias)], []);
        var scope = ElaboratedScopeLookup.CreateScope(root,sourcePhase: StaticAstPhase.Resolved);
        Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(scope,"K"));
        Assert.Same(user,ElaboratedScopeLookup.CompletedReceiver(new Expr.Resolve("User"),scope).Algorithm);
        var original = SourceProvenance.ParseValid("open Lib\nLib={public K=7\n0}\nK").Root;
        var lib = original.Properties.Single().Value;
        var changed = original with { Properties=[original.Properties.Single().WithValue(Assert.IsType<Algorithm.User>(lib) with { Properties=[lib.Properties.Single().WithValue(Value(9))] })] };
        var modified = ElaboratedScopeLookup.CreateScope(changed);
        Assert.Equal((Decimal128)9,Assert.IsType<Expr.Num>(Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(modified,"K")).Property.Value.Output.Single()).Value);
    }

    [Fact]
    public void ModuleScopesDoNotReadTheirHolderAndOwnerlessAncestorsKeepIdentity()
    {
        var lib = new Algorithm.User(null, [], [], [new Property("K", Value(7)) { IsPublic=true }], [new Expr.Num(0)]);
        var parentA = new ScopeCtx(null, [], [new Property("Lib",lib)]);
        var parentB = new ScopeCtx(null, [], [new Property("Lib",lib)]);
        var body = new Algorithm.User(parentA, [], [new Expr.Resolve("Lib")], [], []);
        var a = ElaboratedScopeLookup.CreateScope(body, sourcePhase: StaticAstPhase.NameResolved);
        var b = ElaboratedScopeLookup.CreateScope(body with { Parent=parentB }, sourcePhase: StaticAstPhase.NameResolved);
        Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(a,"K"));
        Assert.NotEqual(a.GetResolvedOpenProviders().Single().Identity,b.GetResolvedOpenProviders().Single().Identity);
        var same=ElaboratedScopeLookup.CreateScope(body,sourcePhase:StaticAstPhase.NameResolved);
        Assert.Equal(a.GetResolvedOpenProviders().Single().Identity,same.GetResolvedOpenProviders().Single().Identity);
        var module = new Algorithm.User(null, [], [new Expr.Resolve("Lib")], [], []) { IsModuleElaborated=true };
        var hygienic = ElaboratedScopeLookup.CreateScope(module,a);
        Assert.Empty(hygienic.GetResolvedOpenProviders());
    }

    [Fact]
    public void ADetachedHostCopyCannotSilentlyReuseAnotherPublishedView()
    {
        var original=SourceProvenance.ParseValid("Lib={public K=7\n0}\n0").Root;
        var lib=Assert.IsType<Algorithm.User>(original.Properties.Single().Value);
        var changed=lib with { Properties=[lib.Properties.Single().WithValue(Value(9))] };
        var parent=ElaboratedScopeLookup.CreateScope(original);
        var detached=ElaboratedScopeLookup.CreateScope(changed,parent);
        Assert.Throws<InvalidOperationException>(()=>detached.BoundLookupContext());
        var supplied=original with { Properties=[original.Properties.Single().WithValue(changed)] };
        var facts=AnalyzedStaticStructures.ForBoundAst(supplied);
        var root=ElaboratedScopeLookup.CreateScope(supplied,completedContext:facts);
        var actual=ElaboratedScopeLookup.CreateScope(changed,root);
        Assert.Equal((Decimal128)9,Assert.IsType<Expr.Num>(actual.BoundLookupContext().Facts.Facts(actual.BoundLookupContext().Key)!.Body!.Properties.Single().Value.Output.Single()).Value);
    }

    [Fact]
    public void RawFactsProjectKnownQ1InputOwnershipWithoutRunningDetection()
    {
        var raw=Syntax("F=x+1\nF(1)");
        var root=ElaboratedScopeLookup.CreateScope(raw,sourcePhase:StaticAstPhase.RawSource);
        var body=raw.Properties.Single().Value;
        var scope=ElaboratedScopeLookup.CreateScope(body,root);
        Assert.Empty(body.Params);
        Assert.True(ElaboratedScopeLookup.SelectOwnedDeclaration(scope,"x",ElaboratedScopeLookup.OwnParameterBindings.Instance).TryGetParameter(out _));
    }

    [Fact]
    public void PendingCarrierAndOwnerlessParameterFactsKeepTheirBoundaries()
    {
        var library=new Algorithm.User(null,[],[],[new Property("K",Value(7)) { IsPublic=true }],[new Expr.Num(0)]);
        var source=new Algorithm.User(null,[],[],[new Property("M",Value(9)) { IsPublic=true }],[new Expr.Resolve("Lib")]);
        var carrier=new Algorithm.Alias(source,source.Output[0]);
        var pending=new Algorithm.Alias(new Algorithm.User(null,[],[],[],[new Expr.Resolve("Lib")]),new Expr.Resolve("Lib"))
            { ResolvedStructureCell=AliasStructureCell.PendingOn(library) };
        var owner=new Algorithm.User(null,[],[],[new Property("Lib",library),new Property("C",carrier),new Property("P",pending)],[]);
        var scope=ElaboratedScopeLookup.CreateScope(owner,sourcePhase:StaticAstPhase.Resolved);
        Assert.NotNull(ElaboratedScopeLookup.ResolveOpenTarget(scope,new Expr.Resolve("C")));
        Assert.Equal("M",Assert.Single(ElaboratedScopeLookup.ResolveOpenTarget(scope,new Expr.Resolve("C"))!.Properties).Name);
        Assert.Null(ElaboratedScopeLookup.ResolveOpenTarget(scope,new Expr.Resolve("P")));
        var host=new ScopeCtx(null,[],[new Property("Lib",library)],["Lib"]);
        var body=new Algorithm.User(host,[],[new Expr.Resolve("Lib")],[],[]);
        Assert.Empty(ElaboratedScopeLookup.CreateScope(body,sourcePhase:StaticAstPhase.NameResolved).GetResolvedOpenProviders());
        var ownedHost=host with { Owner=Value(0) };
        Assert.Empty(ElaboratedScopeLookup.CreateScope(body with { Parent=ownedHost },sourcePhase:StaticAstPhase.NameResolved).GetResolvedOpenProviders());
    }

    [Fact]
    public void CancelledExtensionDoesNotPoisonItsImmutableParentOrRetainTheProducerToken()
    {
        var (state,token)=RetainedSource();
        for(var i=0;i<4;i++) { GC.Collect();GC.WaitForPendingFinalizers();GC.Collect(); }
        Assert.False(token.IsAlive);
        using var cancelled=new CancellationTokenSource();cancelled.Cancel();
        Assert.Throws<OperationCanceledException>(()=>state.Inside(Value(1),null,StaticAstPhase.Resolved,null,cancelled.Token));
        Assert.NotNull(state.Inside(Value(2),null,StaticAstPhase.Resolved,null).Context.Facts);
        Assert.NotNull(state.Context.Facts.Facts(state.Context.Key));
        GC.KeepAlive(state);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (StandaloneScopeAnalysis State,WeakReference Token) RetainedSource()
    {
        var token=new CancellationTokenSource();
        var state=StandaloneScopeAnalysis.Start(Value(0),StaticAstPhase.Resolved,cancellationToken:token.Token);
        return (state,new(token));
    }

    [Theory]
    [InlineData(0,false)]
    [InlineData(1,false)]
    [InlineData(0,true)]
    [InlineData(1,true)]
    public void SiblingsReuseAncestorsAndPreserveDistinctBranchRegions(int phaseValue,bool wiredParent)
    {
        var phase=(StaticAstPhase)phaseValue;
        long previousWork=0,previousAllocation=0;
        foreach (var width in new[] {8,16,32,64,128})
        {
            var library = new Algorithm.User(null, [], [], [new Property("K",Value(7)) { IsPublic=true }], [new Expr.Num(0)]);
            var owner = new Algorithm.User(null, [], [], new[] {new Property("Lib",library)}.Concat(Enumerable.Range(0,width).Select(i=>new Property("P"+i,Value(i)))).ToArray(), [new Expr.Num(0)]);
            var frame=new ScopeCtx(null,owner.Opens,owner.Properties) { Owner=owner };
            var allocationStart=GC.GetAllocatedBytesForCurrentThread();
            var parent = ElaboratedScopeLookup.CreateScope(owner,sourcePhase: phase);
            var initial = parent.StandaloneAnalysis();
            long work=initial.Statistics.AdapterWork,entries=initial.Statistics.Entries,localStorage=initial.Source.RetainedStorageUnits;
            var bodies = new List<Property>();
            for(var i=0;i<width;i++)
            {
                var child = new Algorithm.User(wiredParent?frame:null, [], [new Expr.Resolve("Lib")], [], [new Expr.Resolve("K")]);
                bodies.Add(new Property("C"+i,child));
                var before=initial.Source;
                var scope = ElaboratedScopeLookup.CreateScope(child,parent);
                Assert.Single(scope.GetResolvedOpenProviders());
                var state=scope.StandaloneAnalysis();
                Assert.Same(initial.Source.Contexts[initial.Context.Key],state.Source.Contexts[initial.Context.Key]);
                Assert.Equal(before.Contexts.Count+1,state.Source.Contexts.Count);
                Assert.Equal(before.Syntax.Count+1,state.Source.Syntax.Count);
                work+=state.Statistics.AdapterWork;entries+=state.Statistics.Entries;
                localStorage+=state.Source.RetainedStorageUnits-state.InheritedStorageUnits;
            }
            var allocated=GC.GetAllocatedBytesForCurrentThread()-allocationStart;
            var commonStart=GC.GetAllocatedBytesForCurrentThread();
            var input=ParameterDetector.Detect(owner with { Properties=owner.Properties.Concat(bodies).ToArray() });
            Assert.Empty(input.Diagnostics);
            _=PropertyExposureResolver.Resolve(ImplicitArgumentResolver.Resolve(input));
            var common=input.Operation!.Queries.Statistics;
            var commonAllocated=GC.GetAllocatedBytesForCurrentThread()-commonStart;
            output.WriteLine(System.Text.Json.JsonSerializer.Serialize(new {phase=phase.ToString(),wiredParent,width,standalone=new {work,entries,localStorage,allocated},common,commonAllocated}));
            // One constant-size supplied body per sibling, one wide ancestor graph admitted once.
            Assert.InRange(work,1,common.AdapterWork);
            if(previousWork>0) Assert.True(work<previousWork*3);
            if(previousAllocation>0) Assert.True(allocated<previousAllocation*3);
            previousWork=work;previousAllocation=allocated;
        }
        var root=ElaboratedScopeLookup.CreateScope(Value(0),sourcePhase: StaticAstPhase.NameResolved);
        var shared=new Algorithm.User(null,[],[],[],[new Expr.Resolve("x")]);
        var x=ElaboratedScopeLookup.CreateScope(shared,root,branchPattern:new Pattern.Bind("x"));
        var y=ElaboratedScopeLookup.CreateScope(shared,root,branchPattern:new Pattern.Bind("y"));
        Assert.NotSame(x.StandaloneAnalysis().Context.Key,y.StandaloneAnalysis().Context.Key);
        Assert.Same(x.StandaloneAnalysis().Source.Syntax[shared],y.StandaloneAnalysis().Source.Syntax[shared]);
        Assert.Contains("x",x.BoundLookupContext().Facts.Facts(x.BoundLookupContext().Key)!.Parameters);
        Assert.DoesNotContain("x",y.BoundLookupContext().Facts.Facts(y.BoundLookupContext().Key)!.Parameters);
        Assert.True(ElaboratedScopeLookup.SelectOwnedDeclaration(x,"x",ElaboratedScopeLookup.OwnParameterBindings.Instance).TryGetParameter(out _));
        Assert.False(ElaboratedScopeLookup.SelectOwnedDeclaration(y,"x",ElaboratedScopeLookup.OwnParameterBindings.Instance).TryGetParameter(out _));
    }
}
