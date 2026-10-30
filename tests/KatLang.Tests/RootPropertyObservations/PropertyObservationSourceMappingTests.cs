using KatLang.Evaluation.Caching;
using KatLang.Semantics;
using static KatLang.Tests.RootPropertyObservations.PropertyObservationTestSupport;

namespace KatLang.Tests.RootPropertyObservations;

/// <summary>
/// IV-2: an observation identifies its root property by name and canonical declaration anchor
/// (<see cref="Property.FirstDeclarationSpan"/> of the final elaborated root's own
/// <see cref="Property"/> instance). The anchor round-trips through the public
/// <see cref="SemanticModel"/> of the same document, a root declaration maps to its OWN anchor —
/// never a dependency's, an alias target's, or a shadowing nested declaration's — and synthetic,
/// imported, nested, and source-less bindings never appear. Sections 1–2 are legal source through
/// the engine; section 3 pins the sink's defensive filters from host-built ASTs, which no written
/// program reaches.
/// </summary>
public class PropertyObservationSourceMappingTests
{
    private const string Meta = "Square(x) = x * x\nCapture(meta operation) = operation\n";

    // ── 1. Source anchors and the semantic-model round trip ─────────────────────────────────

    public static TheoryData<string> MappingSources => new()
    {
        "Price = 200\nVAT = Price * 0.21\nTotal = Price + VAT\nUnused = 6 * 7\nTotal",
        "A = 1\nF = {\n    A = 2\n    A\n}\nF + A",
        "x, y = 1, 2\nx + y",
        "A = 5\nB = A\nB",
        "X = 1 / 3\nDisplayDecimals = 2\nX",
        "Describe(0) = 'zero'\nDescribe(n) = 'other'\nD = Describe(0)\nD",
        "Only(*xs) = 7\nLong = Only +\n    1\nLong",
        Meta + "R = Capture(Square(5))\nL = [R, 1]\nR.Invoke() + count(L)",
    };

    [Theory]
    [MemberData(nameof(MappingSources))]
    public void EveryObservation_ResolvesToItsOwnRootDeclaration_InTheSemanticModel(string source)
    {
        var result = Run(source);
        var observations = result.PropertyObservations!;
        Assert.NotEmpty(observations);
        var root = result switch
        {
            RunResult.Success s => s.Root,
            RunResult.EvalFailure f => f.Root,
            _ => throw new InvalidOperationException(result.ToString()),
        };

        foreach (var model in new[] { SemanticModelBuilder.Build(Parser.Parse(source)), SemanticModelBuilder.Build(root) })
        {
            foreach (var observation in observations)
            {
                var resolution = model.FindResolutionAt(observation.DeclarationSpan.Start);
                Assert.NotNull(resolution);
                Assert.Equal(IdentifierClassification.PropertyDefinition, resolution.Classification);
                Assert.Equal(observation.Name, resolution.Occurrence.Name);
                Assert.Equal(observation.DeclarationSpan, resolution.Occurrence.Span);

                // Identity through the model's OWN canonical occurrence, never a value-equal copy.
                var declaration = resolution.ResolvedDeclaration;
                Assert.NotNull(declaration);
                var property = model.FindPropertyByDeclaration(declaration);
                Assert.NotNull(property);
                Assert.Equal(observation.Name, property.Name);
                Assert.Same(declaration, property.Declaration);
                Assert.Contains(model.FindDeclarations(observation.Name), d => ReferenceEquals(d, declaration));
            }
        }

        // The anchor is the root binding's own canonical anchor.
        foreach (var observation in observations)
        {
            var binding = Assert.Single(root.Properties, p => p.Name == observation.Name);
            Assert.Equal(binding.FirstDeclarationSpan, observation.DeclarationSpan);
        }
    }

    [Fact]
    public void ShadowingNestedDeclaration_IsNotObserved_TheRootNameMapsToTheRootDeclaration()
    {
        // F's row is a calculation: a lone `A` row would make F a forwarding carrier of its own A, which
        // owns no entry (M4★ OD-E).
        var result = Run("A = 1\nF = {\n    A = 2\n    A + 0\n}\nF + A");

        Assert.Equal("F=2#1; A=1#1", Describe(result));
        Assert.Equal(new SourceSpan(1, 1, 1, 2), Single(result, "A").DeclarationSpan);
        Assert.Equal(new SourceSpan(2, 1, 2, 2), Single(result, "F").DeclarationSpan);
    }

    [Fact]
    public void DeconstructionTargets_MapToTheirOwnNames_AndTheSyntheticSourceIsNeverObserved()
    {
        var result = Run("x, y = 1, 2\nx + y");

        Assert.Equal("x=1#1; y=2#1", Describe(result));
        Assert.Equal(new SourceSpan(1, 1, 1, 2), Single(result, "x").DeclarationSpan);
        Assert.Equal(new SourceSpan(1, 4, 1, 5), Single(result, "y").DeclarationSpan);

        // The elaborated root really holds a spanless hoisted source, and it really published:
        // the sink filtered it.
        var root = ((RunResult.Success)result).Root;
        Assert.Contains(root.Properties, p => p.Name.StartsWith('$') && p.DeclarationSpans.Count == 0);
        Assert.DoesNotContain(result.PropertyObservations!, o => o.Name.StartsWith('$'));
    }

    [Fact]
    public void StaticAlias_IsNotObserved_ItsTargetMapsToItsOwnDeclaration()
    {
        // M4★ OD-E: the alias owns no entry, so only the target is observed, at its own declaration.
        var result = Run("Target = 5\nAlias = Target\nAlias");
        Assert.DoesNotContain(result.PropertyObservations!, static observation => observation.Name == "Alias");
        Assert.Equal(new SourceSpan(1, 1, 1, 7), Single(result, "Target").DeclarationSpan);
    }

    [Fact]
    public void RuntimeTargetAlias_ReadAsAProperty_IsNotObserved_ItsTargetIs()
    {
        // M4★ OD-E: A = R.Algorithm is a runtime reference to the captured callee Z, which owns no entry:
        // reading it is Z's own bare read, so Z is observed at its own declaration and A is not (formerly
        // A was published under its own declaration). R holds a call reference and is withheld.
        var result = Run("Capture(meta operation) = operation\nZ = 7\nR = Capture(Z())\nA = R.Algorithm\nA + 1");

        Assert.Equal("8", result.ToDisplayString());
        Assert.Equal(PropertyValueStatus.Withheld, Single(result, "R").Status);
        Assert.DoesNotContain(result.PropertyObservations!, static observation => observation.Name == "A");
        var target = Single(result, "Z");
        Assert.Equal(PropertyValueStatus.Available, target.Status);
        Assert.Equal("7", result.RenderPropertyValue(target).Text);
        Assert.Equal(new SourceSpan(2, 1, 2, 2), target.DeclarationSpan);
    }

    [Fact]
    public void ExplicitlyCalledRuntimeAlias_IsNotObserved()
    {
        var result = Run(Meta + "R = Capture(Square(5))\nA = R.Algorithm\nA(9)");

        Assert.Equal("81", result.ToDisplayString());
        Assert.Equal("R=<withheld>#1", Describe(result));
    }

    [Fact]
    public void SourceClauseFamily_IsCalledNotPublished_AndItsCallerMapsToItsOwnAnchor()
    {
        // A written clause family takes parameters, so it is never a zero-supply property read;
        // its model keeps one canonical occurrence per clause head.
        const string source = "Describe(0) = 'zero'\nDescribe(n) = 'other'\nD = Describe(0)\nD";
        var result = Run(source);

        Assert.Equal("D=zero#1", Describe(result));
        Assert.Equal(new SourceSpan(3, 1, 3, 2), Single(result, "D").DeclarationSpan);
        var family = Assert.Single(((RunResult.Success)result).Root.Properties, p => p.Name == "Describe");
        Assert.Equal(2, family.DeclarationSpans.Count);
    }

    [Fact]
    public async Task ModuleProvidedBindings_AreNotObserved()
    {
        var options = new RunOptions
        {
            ObservePropertyValues = true,
            AllowedHosts = ["mods.test"],
            DownloadCode = (_, _) => ValueTask.FromResult("public X = 5\npublic Y = X + 1"),
        };

        // K computes with the member (a lone `M.Y` row would make K a member reference, which owns no
        // entry, M4★ OD-E).
        var loaded = await KatLangEngine.RunAsync("M = load('https://mods.test/x.kat')\nK = M.Y + 0\nK", options);
        Assert.Equal("K=6#1", Describe(loaded));

        var opened = await KatLangEngine.RunAsync("open 'https://mods.test/x.kat'\nK = Y + 0\nK + X", options);
        Assert.Equal("11", opened.ToDisplayString());
        Assert.Equal("K=6#1", Describe(opened));
    }

    [Fact]
    public void SameSourceTwice_MapsToTheSameAnchors_InIndependentSnapshots()
    {
        const string source = "Price = 200\nVAT = Price * 0.21\nVAT";
        var first = Run(source);
        var second = Run(source);

        Assert.NotSame(first.PropertyObservations, second.PropertyObservations);
        Assert.Equal(
            first.PropertyObservations!.Select(o => (o.Name, o.DeclarationSpan)),
            second.PropertyObservations!.Select(o => (o.Name, o.DeclarationSpan)));
    }

    // ── 2. Host-built defensive filters (not source-reachable) ──────────────────────────────

    private static readonly SourceSpan SpanA = new(1, 1, 1, 2);
    private static readonly SourceSpan SpanB = new(2, 1, 2, 2);

    private static Algorithm.User Body(params Expr[] output) => new(null, [], [], [], output);

    private static Algorithm.User Root(IReadOnlyList<Property> properties, params Expr[] output)
        => new(null, [], [], properties, output);

    /// <summary>Runs a host-built root on the generic route with a sink, and returns the completed snapshot.</summary>
    private static (EvalResult<Evaluator.CountedResult> Result, PropertyObservations Snapshot, int Duplicates) RunHostBuilt(Algorithm.User root)
    {
        var sink = new RootPropertyObservationSink(root);
        var (result, _) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(root),
            zeroArgPropertyResultCache: new RunScopedZeroArgPropertyResultCache(sink));
        return (result, sink.Complete(), sink.DuplicateBindingPublications);
    }

    [Fact]
    public void HostBuilt_SpanlessAndInvalidAnchorProperties_AreNotObserved()
    {
        var spanned = new Property("A", Body(new Expr.Num(1))) { DeclarationSpans = [SpanA] };
        var spanless = new Property("B", Body(new Expr.Num(2)));
        var defaultSpan = new Property("C", Body(new Expr.Num(3))) { DeclarationSpans = [default] };
        var root = Root([spanned, spanless, defaultSpan],
            new Expr.Resolve("A"), new Expr.Resolve("B"), new Expr.Resolve("C"));

        var (result, snapshot, duplicates) = RunHostBuilt(root);

        Assert.False(result.IsError, result.ToString());
        var observation = Assert.Single(snapshot);
        Assert.Equal("A", observation.Name);
        Assert.Equal(SpanA, observation.DeclarationSpan);
        Assert.Equal(0, duplicates);
    }

    [Fact]
    public void HostBuilt_LocalOnlyRootMetadata_IsNotObserved()
    {
        var localOnly = new Property("A", Body(new Expr.Num(1)), Exposure: PropertyExposure.LocalOnlyConditionalAlgorithm)
        {
            DeclarationSpans = [SpanA],
        };
        var exported = new Property("B", Body(new Expr.Resolve("A"))) { DeclarationSpans = [SpanB] };
        var (result, snapshot, _) = RunHostBuilt(Root([localOnly, exported], new Expr.Resolve("B")));

        Assert.False(result.IsError, result.ToString());
        Assert.Equal(["B"], snapshot.Select(o => o.Name));
    }

    [Fact]
    public void HostBuilt_SharedPropertyUnderAnotherOwner_IsObservedOnlyForTheRootOwner()
    {
        // One Property object placed in the root's list AND in a nested owner's own list: the
        // nested owner's read publishes under the nested owner's key (a different owner
        // identity), which the sink must not mistake for the root binding.
        var shared = new Property("A", Body(new Expr.Num(1))) { DeclarationSpans = [SpanA] };
        var nested = new Property("N", new Algorithm.User(null, [], [], [shared], [new Expr.Resolve("A")]))
        {
            DeclarationSpans = [SpanB],
        };

        var nestedOnly = RunHostBuilt(Root([shared, nested], new Expr.Resolve("N")));
        Assert.False(nestedOnly.Result.IsError, nestedOnly.Result.ToString());
        Assert.Equal(["N"], nestedOnly.Snapshot.Select(o => o.Name));

        var both = RunHostBuilt(Root([shared, nested], new Expr.Resolve("N"), new Expr.Resolve("A")));
        Assert.False(both.Result.IsError, both.Result.ToString());
        Assert.Equal(["N", "A"], both.Snapshot.Select(o => o.Name));
        Assert.Equal(0, both.Duplicates);
    }

    [Fact]
    public void HostBuilt_ZeroAcceptingClauseFamily_IsObservedAtItsFirstClauseAnchor()
    {
        // The zero-supply conditional funnel is reachable only from a host-built AST
        // (ZeroArgumentDemandArityTests.ClauseFamilyWithAZeroArityBranch_IsDemandable).
        var family = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.SequenceValue([]), Body(new Expr.Num(7)))]);
        var property = new Property("F", family) { DeclarationSpans = [SpanB, SpanA] };

        var (result, snapshot, _) = RunHostBuilt(Root([property], new Expr.Resolve("F")));

        Assert.False(result.IsError, result.ToString());
        var observation = Assert.Single(snapshot);
        Assert.Equal(SpanB, observation.DeclarationSpan);
        Assert.Equal(7m, observation.Value!.AsNum());
    }
}
