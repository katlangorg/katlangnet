using KatLang.Optimizations.Loops;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// The ownership-first OWNER WALK over owned declarations
/// (<see cref="ElaboratedScopeLookup.SelectOwnedDeclaration"/>) and its two
/// front-end consumers: parameter classification
/// (<c>ParameterDetector.ShouldRewriteAsParam</c>) and receiver classification
/// (<c>ParameterDetector.ResolveReceiverNameProvider</c>).
///
/// <para>Search outward by owning scope: the first scope that DECLARES the name
/// wins. Invalid same-owner collisions select the parameter for recovery.
/// Evaluation results alone cannot distinguish "the right binding
/// was selected" from "an unrelated runtime path happened to produce the same
/// number", so these tests assert the ELABORATED BINDING KIND at the reference
/// site (<see cref="Expr.Param"/> vs <see cref="Expr.Resolve"/>) and the
/// SELECTED DECLARATION the editor reports, alongside the value. The
/// declaration-identity relation across the runtime, editor and detector views
/// is pinned by <c>LookupCoherenceTests</c>; the canonical behavior is pinned by
/// the <c>ownership-*</c> language-spec cases.</para>
/// </summary>
public class ParameterOwnershipTests
{
    // ── the walk itself, over an explicitly constructed owner chain ──────────

    private static Algorithm.User Owner(params Property[] properties)
        => new(Parent: null, Parameters: [], Opens: [], Properties: [.. properties], Output: OutputBundle.Empty);

    private static Property Value(string name, int sentinel)
        => new(name, new Algorithm.User(null, [], [], [], [new Expr.Num(sentinel)]));

    /// <summary>
    /// A test-local <see cref="IOwnedParameterBindings"/>: the level that owns
    /// each name, stated directly rather than derived, so the walk is exercised
    /// independently of how the detector builds its map.
    /// </summary>
    private sealed class Bindings(params (ElaboratedPropertyScope Level, string Name)[] entries)
        : IOwnedParameterBindings
    {
        public bool DeclaresParameter(ElaboratedPropertyScope level, string name)
            => entries.Any(entry => ReferenceEquals(entry.Level, level) && entry.Name == name);
    }

    private static (ElaboratedPropertyScope Root, ElaboratedPropertyScope Middle, ElaboratedPropertyScope Inner)
        BuildChain(bool rootDeclaresV, bool middleDeclaresV)
    {
        var root = ElaboratedScopeLookup.CreateScope(
            rootDeclaresV ? Owner(Value("v", 303)) : Owner());
        var middle = ElaboratedScopeLookup.CreateScope(
            middleDeclaresV ? Owner(Value("v", 101)) : Owner(), root);
        var inner = ElaboratedScopeLookup.CreateScope(Owner(), middle);
        return (root, middle, inner);
    }

    [Fact]
    public void OwnerWalk_ParameterOfAFartherOwner_BeatsAPropertyOfAnEvenFartherOwner()
    {
        var (root, middle, inner) = BuildChain(rootDeclaresV: true, middleDeclaresV: false);

        var selected = ElaboratedScopeLookup.SelectOwnedDeclaration(inner, "v", new Bindings((middle, "v")));

        Assert.Equal(OwnedDeclarationKind.Parameter, selected.Kind);
        Assert.Same(middle, selected.OwnerScope);
        Assert.Null(selected.PropertyHit);
        // The root's property is still there — it simply belongs to a farther owner.
        var farther = ElaboratedScopeLookup.TryLookupDirectLexicalProperty(inner, "v");
        Assert.Same(root.Properties.Single().Property, farther!.Value.Property);
        Assert.Same(root.Properties.Single().Owner, farther.Value.Owner);
    }

    [Fact]
    public void OwnerWalk_NearerProperty_BeatsAFartherParameter()
    {
        var (_, middle, inner) = BuildChain(rootDeclaresV: false, middleDeclaresV: true);
        var outerMost = middle.Parent!;

        var selected = ElaboratedScopeLookup.SelectOwnedDeclaration(inner, "v", new Bindings((outerMost, "v")));

        Assert.Equal(OwnedDeclarationKind.Property, selected.Kind);
        Assert.Same(middle, selected.OwnerScope);
        Assert.Equal(101, (int)((Expr.Num)selected.PropertyHit!.Value.Property.Value.Output[0]).Value);
    }

    [Fact]
    public void OwnerWalk_SameOwnerDeclaresBoth_SelectsTheParameter()
    {
        var (_, middle, inner) = BuildChain(rootDeclaresV: false, middleDeclaresV: true);

        var selected = ElaboratedScopeLookup.SelectOwnedDeclaration(inner, "v", new Bindings((middle, "v")));

        Assert.Equal(OwnedDeclarationKind.Parameter, selected.Kind);
        Assert.Same(middle, selected.OwnerScope);
    }

    [Fact]
    public void OwnerWalk_NoOwnerDeclaresTheName_LeavesItToTheOpenAndPreludeFallback()
    {
        var (_, _, inner) = BuildChain(rootDeclaresV: false, middleDeclaresV: false);

        var selected = ElaboratedScopeLookup.SelectOwnedDeclaration(inner, "v", new Bindings());

        Assert.Equal(OwnedDeclarationKind.None, selected.Kind);
        Assert.Null(selected.OwnerScope);
        Assert.Null(selected.PropertyHit);
    }

    /// <summary>
    /// The property arm must select exactly what
    /// <see cref="ElaboratedScopeLookup.TryLookupDirectLexicalProperty"/>
    /// selects: same level order, same per-level first-declaration rule. Only
    /// the parameter dimension is new.
    /// </summary>
    [Fact]
    public void OwnerWalk_PropertyArm_AgreesWithDirectLexicalLookup()
    {
        var (_, middle, inner) = BuildChain(rootDeclaresV: true, middleDeclaresV: true);

        var selected = ElaboratedScopeLookup.SelectOwnedDeclaration(inner, "v", new Bindings());
        var direct = ElaboratedScopeLookup.TryLookupDirectLexicalProperty(inner, "v");

        Assert.Equal(OwnedDeclarationKind.Property, selected.Kind);
        Assert.Same(middle, selected.OwnerScope);
        Assert.Same(direct!.Value.Property, selected.PropertyHit!.Value.Property);
    }

    // ── ParameterOwnership: nearest binding wins by construction ─────────────

    [Fact]
    public void ParameterOwnership_InnerExtensionShadowsTheSameNameFromAnOuterOwner()
    {
        var (_, middle, inner) = BuildChain(rootDeclaresV: false, middleDeclaresV: false);
        var outerMost = middle.Parent!;

        var parameters = ParameterOwnership.Empty
            .Extend(outerMost, ["v"])
            .Extend(middle, ["v"]);

        Assert.True(parameters.Contains("v"));
        Assert.True(parameters.DeclaresParameter(middle, "v"));
        Assert.False(parameters.DeclaresParameter(outerMost, "v"));
        Assert.Equal(["v"], parameters.Names);

        var selected = ElaboratedScopeLookup.SelectOwnedDeclaration(inner, "v", parameters);
        Assert.Same(middle, selected.OwnerScope);
    }

    [Fact]
    public void ParameterOwnership_ExtendingWithNothingKeepsTheSameInstance()
    {
        var (_, middle, _) = BuildChain(rootDeclaresV: false, middleDeclaresV: false);
        var parameters = ParameterOwnership.Empty.Extend(middle, ["v"]);

        Assert.Same(parameters, parameters.Extend(middle, []));
        Assert.Same(ParameterOwnership.Empty, ParameterOwnership.Empty.Extend(middle, []));
        Assert.Empty(ParameterOwnership.Empty.Names);
        Assert.False(ParameterOwnership.Empty.Contains("v"));
    }

    [Fact]
    public void SharedBody_KeepsOwnershipRegionsAndIndependentDetectionsIsolated()
    {
        var shared = new Algorithm.User(null, [], [], [], [new Expr.Resolve("v")]);
        var nearer = Owner(Value("v", 5), new Property("Read", shared)) with
        {
            Output = new OutputBundle([new Expr.Resolve("Read")]),
        };

        // Reuse the exact input objects in several owner contexts and in three
        // independent detections. Only the binding at Outer changes between runs.
        foreach (var parameter in new[] { "v", "q", "v" })
        {
            var outer = new Algorithm.User(null, [new ParameterDeclaration(parameter)], [],
                [new Property("Left", shared), new Property("Right", shared), new Property("Nearer", nearer)],
                [new Expr.Resolve("Left"), new Expr.Resolve("Right"), new Expr.Resolve("Nearer")]);
            var root = Owner(Value("v", 99), new Property("Outer", outer), new Property("Other", shared)) with
            {
                Output = new OutputBundle([
                    new Expr.Call(new Expr.Resolve("Outer"), new OutputBundle([new Expr.Num(7)])),
                    new Expr.Resolve("Other"),
                ]),
            };
            var (detected, diagnostics) = ParameterDetector.Detect(root);
            Assert.Empty(diagnostics);
            var detectedOuter = detected.Properties.Single(p => p.Name == "Outer").Value;
            var left = detectedOuter.Properties.Single(p => p.Name == "Left").Value;
            Assert.Same(left, detectedOuter.Properties.Single(p => p.Name == "Right").Value);
            Assert.Empty(left.Params);
            Assert.Equal(parameter == "v" ? typeof(Expr.Param) : typeof(Expr.Resolve), left.Output.Single().GetType());
            Assert.IsType<Expr.Resolve>(detectedOuter.Properties.Single(p => p.Name == "Nearer").Value
                .Properties.Single(p => p.Name == "Read").Value.Output.Single());
            Assert.IsType<Expr.Resolve>(detected.Properties.Single(p => p.Name == "Other").Value.Output.Single());
            var result = Evaluator.Run(new Expr.AlgorithmExpr(detected));
            Assert.False(result.IsError);
            Assert.Equal<System.Numerics.Decimal128>(parameter == "v" ? [7, 7, 5, 99] : [99, 99, 5, 99], result.Value.ToAtoms());
        }
        Assert.IsType<Expr.Resolve>(shared.Output.Single());
    }

    // ── elaborated binding kind at the reference site ────────────────────────

    /// <summary>
    /// How the reference in the innermost body elaborated: a runtime parameter
    /// read, or a lexical property reference. Reading it off the elaborated AST
    /// is what keeps an accidental runtime fallback from masking an incorrect
    /// classification.
    /// </summary>
    private static Expr ReferenceNode(string source, bool expectCollision, params string[] path)
    {
        var parsed = Parser.Parse(source);
        if (expectCollision)
            Assert.Equal(DiagnosticCode.ParameterPropertyCollision, Assert.Single(parsed.Diagnostics).Code);
        else
            Assert.Empty(parsed.Diagnostics);

        var algorithm = parsed.Root;
        foreach (var step in path)
            algorithm = algorithm.Properties.Single(property => property.Name == step).Value;

        var row = algorithm.Output.Single();
        return row is Expr.Binary(_, var left, _) ? left : row;
    }

    [Theory]
    // A captured ancestor parameter beats a property of a farther owner...
    [InlineData("v = 99\nOuter(v) = {\n    Inner = v + 1\n    Inner\n}\nOuter(7)", true)]
    // ...at any nesting distance, and regardless of where the property is written.
    [InlineData("Wrapper = {\n    v = 99\n    Outer(v) = {\n        Inner = v + 1\n        Inner\n    }\n    Outer(7)\n}\nWrapper", true)]
    [InlineData("Outer(v) = {\n    Inner = v + 1\n    Inner\n}\nv = 99\nOuter(7)", true)]
    // Invalid same-owner recovery still selects the parameter.
    [InlineData("Outer(v) = {\n    v = 5\n    Inner = v + 1\n    Inner\n}\nOuter(7)", true, true)]
    [InlineData("Outer(v) = {\n    Inner = v + 1\n    v = 5\n    Inner\n}\nOuter(7)", true, true)]
    // The prelude is the outermost owner, so a parameter beats an alias or builtin.
    [InlineData("Outer(pi) = {\n    Inner = pi + 1\n    Inner\n}\nOuter(7)", true)]
    // `open` is consulted only after the whole owner walk.
    [InlineData("Lib = {\n    public v = 99\n}\nOuter(v) = {\n    open Lib\n    Inner = v + 1\n    Inner\n}\nOuter(7)", true)]
    // A name no owner binds stays an ordinary lexical reference.
    [InlineData("v = 99\nOuter(q) = {\n    Inner = v + 1\n    Inner\n}\nOuter(7)", false)]
    public void ReferenceInsideANestedBody_ElaboratesToTheSelectedBindingKind(string source, bool expectParameter, bool expectCollision = false)
    {
        var node = ReferenceNode(source, expectCollision, PathOf(source));

        if (expectParameter)
            Assert.IsType<Expr.Param>(node);
        else
            Assert.IsType<Expr.Resolve>(node);

        static string[] PathOf(string source)
            => source.Contains("Wrapper", StringComparison.Ordinal)
                ? ["Wrapper", "Outer", "Inner"]
                : ["Outer", "Inner"];
    }

    /// <summary>
    /// The invalid nearer-property case, asserted the same way: the nested reference
    /// must stay a lexical reference so it reaches the intervening declaration.
    /// Dropping the shadowing guard entirely would turn this into a parameter.
    /// </summary>
    [Fact]
    public void ReferenceShadowedByANearerProperty_StaysALexicalReference()
    {
        const string source = "v = 99\nOuter(v) = {\n    Mid = {\n        v = 5\n        Inner = v + 1\n        Inner\n    }\n    Mid\n}\nOuter(7)";

        Assert.IsType<Expr.Resolve>(ReferenceNode(source, true, "Outer", "Mid", "Inner"));
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    /// <summary>
    /// A captured parameter never becomes a parameter OF the nested body: the
    /// binding stays the enclosing algorithm's, read through the inherited
    /// environment. Promotion policy is unchanged by the ownership fix.
    /// </summary>
    [Fact]
    public void CapturedParameter_DoesNotBecomeAParameterOfTheNestedBody()
    {
        var parsed = Parser.Parse("v = 99\nOuter(v) = {\n    Inner = v + 1\n    Inner\n}\nOuter(7)");
        Assert.False(parsed.HasErrors);

        var outer = parsed.Root.Properties.Single(property => property.Name == "Outer").Value;
        var inner = outer.Properties.Single(property => property.Name == "Inner").Value;

        Assert.Equal(["v"], outer.Params);
        Assert.Empty(inner.Params);
    }

    // ── the editor view reports the selected binding ─────────────────────────

    /// <summary>
    /// Go-to-definition and hover must land on the binding the program actually
    /// reads, not on the shadowed property. The editor consumes the front end's
    /// one decision, so this is the same rule observed through the query API.
    /// </summary>
    [Theory]
    [InlineData(
        "v = 99\nOuter(v) = {\n    Inner = v + 1\n    Inner\n}\nOuter(7)",
        IdentifierClassification.ExplicitParameterReference, 2, 7)]
    [InlineData(
        "Outer(v) = {\n    v = 5\n    Inner = v + 1\n    Inner\n}\nOuter(7)",
        IdentifierClassification.ExplicitParameterReference, 1, 7, true)]
    [InlineData(
        "v = 99\nOuter(v) = {\n    Mid = {\n        v = 5\n        Inner = v + 1\n        Inner\n    }\n    Mid\n}\nOuter(7)",
        IdentifierClassification.PropertyReference, 4, 9, true)]
    [InlineData(
        "v = 99\nOuter(q) = {\n    Inner = v + 1\n    Inner\n}\nOuter(7)",
        IdentifierClassification.PropertyReference, 1, 1)]
    public void EditorResolution_NamesTheSelectedDeclaration(
        string source,
        IdentifierClassification expectedClassification,
        int expectedDeclarationLine,
        int expectedDeclarationColumn,
        bool expectCollision = false)
    {
        var parsed = Parser.Parse(source);
        if (expectCollision)
            Assert.Equal(DiagnosticCode.ParameterPropertyCollision, Assert.Single(parsed.Diagnostics).Code);
        else
            Assert.Empty(parsed.Diagnostics);
        var model = SemanticModelBuilder.Build(parsed);

        var (line, column) = LastOccurrence(source, "v");
        var resolution = model.FindResolutionAt(line, column);

        Assert.NotNull(resolution);
        Assert.Equal(expectedClassification, resolution.Classification);
        Assert.NotNull(resolution.ResolvedDeclaration);
        Assert.Equal(expectedDeclarationLine, resolution.ResolvedDeclaration.Span.StartLineNumber);
        Assert.Equal(expectedDeclarationColumn, resolution.ResolvedDeclaration.Span.StartColumn);
    }

    /// <summary>
    /// Completion enumerates what resolution selects: the scope containing the
    /// nested reference must offer <c>v</c> as the parameter, never as the
    /// shadowed outer property.
    /// </summary>
    [Fact]
    public void VisibleSymbols_OfferTheSelectedBinding()
    {
        const string source = "v = 99\nOuter(v) = {\n    Inner = v + 1\n    Inner\n}\nOuter(7)";
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);

        var (line, column) = LastOccurrence(source, "v");
        var symbol = Assert.Single(
            model.GetVisibleSymbolsAt(line, column), candidate => candidate.Name == "v");

        Assert.Equal(IdentifierClassification.ExplicitParameterReference, symbol.Classification);
    }

    // ── execution paths that could have masked the classification ────────────

    /// <summary>
    /// The PLANNED loop executor runs an ownership-sensitive step and agrees with
    /// the generic one. The corpus equivalence sweep compares the two strategies
    /// over every case and probe, but it cannot say the planned executor was the
    /// one that ran — <see cref="LoopOptimizationDiagnostics.OptimizedLoopHits"/>
    /// establishes that here, so the claim rests on the harness rather than on
    /// the entry point.
    /// </summary>
    [Fact]
    public void PlannedLoopStep_ReadsTheSelectedBinding_AndAgreesWithTheGenericStrategy()
    {
        const string source = "v = 99\nOuter(v) = repeat({x + v}, 3, 0)\nOuter(7)";
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var diagnostics = new LoopOptimizationDiagnostics();
        var (optimized, _) = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics);
        var (generic, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false);

        Assert.True(diagnostics.OptimizedLoopHits > 0, "the planned loop executor did not run this loop");
        var plan = Assert.Single(diagnostics.GetSnapshot().LoopPlans);
        var output = Assert.Single(plan.Expressions);
        Assert.Equal("Add(StateSlot(x), CapturedSlot(v))", output.PlanSummary);
        Assert.True(output.Planned);
        Assert.Equal(1, plan.ExecutionCount);
        Assert.Equal(3, diagnostics.LoopIterations);
        Assert.Equal(0, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.False(optimized.IsError);
        Assert.Equal([21m], optimized.Value.Value.ToAtoms());
        Assert.Equal(
            optimized.Value.Value.ToAtoms(),
            Assert.IsType<Evaluator.CountedResult>(generic.Value).Value.ToAtoms());
    }

    private static (int Line, int Column) LastOccurrence(string source, string name)
    {
        var (tokens, _) = Lexer.Tokenize(source);
        var token = tokens.Last(t => t.Kind == TokenKind.Identifier && t.StringValue == name);
        return (token.Line, token.Column);
    }
}
