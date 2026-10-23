using KatLang.ParserFuzz;
using KatLang.Tests.StructuralFuzz;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2B generator contracts: deterministic, versioned case identities; direct reconstruction of
/// any one case; binding-preserving transformations; clean front ends for every valid source and the
/// named diagnostic/phase for every invalid one; and an unchanged legacy structural corpus.
/// Generation only — nothing here evaluates a program.
/// </summary>
public class SemanticGrammarGeneratorTests
{
    private static readonly HostOperations HostNames = MetamorphicHostFixture.Synchronous().Operations;

    [Fact]
    public void Corpus_IsDeterministic_InSourceProfilesAndDescriptor()
    {
        var first = SemanticCorpus.All();
        var second = SemanticCorpus.All();
        Assert.Equal(first.Count, second.Count);
        foreach (var (a, b) in first.Zip(second))
        {
            Assert.Equal(a.CaseId, b.CaseId);
            Assert.Equal(a.Members.Select(m => m.Source), b.Members.Select(m => m.Source));
            Assert.Equal(a.Profiles.ToArray(), b.Profiles.ToArray());
            Assert.Equal(SemanticDescriptor.Write(a), SemanticDescriptor.Write(b));
        }

        Assert.Equal(first.Count, first.Select(c => c.CaseId).Distinct(StringComparer.Ordinal).Count());
    }

    [Fact]
    public void EveryCase_ReconstructsFromItsIdAlone_WithoutGeneratingTheCorpus()
    {
        foreach (var semanticCase in SemanticCorpus.All())
        {
            Assert.True(SemanticCorpus.TryReconstruct(semanticCase.CaseId, SemanticRecipe.RecipeVersion, out var rebuilt, out var problem), problem);
            Assert.Equal(SemanticDescriptor.Write(semanticCase), SemanticDescriptor.Write(rebuilt));
        }

        // A seeded case is its own stream: index 7 needs no earlier case.
        var direct = SemanticCorpus.SeededCase(SemanticCorpus.Seeds[2], 7);
        var enumerated = SemanticCorpus.Seeded().Single(c => c.CaseId == direct.CaseId);
        Assert.Equal(SemanticDescriptor.Write(enumerated), SemanticDescriptor.Write(direct));
    }

    [Fact]
    public void CaseIds_AreVersioned_AndOtherVersionsOrMalformedIdsAreRefused()
    {
        Assert.All(SemanticCorpus.All(), c => Assert.StartsWith("sem2b/v1/", c.CaseId, StringComparison.Ordinal));
        var id = SemanticCorpus.Seeded()[0].CaseId;

        Assert.False(SemanticCorpus.TryReconstruct(id, SemanticRecipe.RecipeVersion + 1, out _, out var otherVersion));
        Assert.Contains("is not built by this generator", otherVersion, StringComparison.Ordinal);
        Assert.False(SemanticCorpus.TryReconstruct("sem2b/v1/seed/zz/1", SemanticRecipe.RecipeVersion, out _, out var malformed));
        Assert.Contains("malformed", malformed, StringComparison.Ordinal);
        Assert.False(SemanticCorpus.TryReconstruct("sem2b/v1/sys/meta/999", SemanticRecipe.RecipeVersion, out _, out var unknown));
        Assert.Contains("no systematic case", unknown, StringComparison.Ordinal);
        Assert.False(SemanticCorpus.TryReconstruct("other/v1/sys/meta/0", SemanticRecipe.RecipeVersion, out _, out var prefix));
        Assert.Contains("recipe prefix", prefix, StringComparison.Ordinal);
    }

    /// <summary>
    /// The systematic chooser visits every value of a dimension across consecutive case indices and
    /// advances within a case; the seeded chooser depends only on (seed, index).
    /// </summary>
    [Fact]
    public void Choosers_CoverEveryValue_AndSeededStreamsAreIndependent()
    {
        var seen = Enumerable.Range(0, 5).Select(j => SemanticChooser.Systematic(j).Pick("meta.op", 5)).ToHashSet();
        Assert.Equal(5, seen.Count);
        var within = SemanticChooser.Systematic(0);
        Assert.NotEqual(within.Pick("meta.op", 6), within.Pick("meta.op", 6));

        var a = SemanticChooser.Seeded(42, 3);
        var b = SemanticChooser.Seeded(42, 3);
        var c = SemanticChooser.Seeded(42, 4);
        var streamA = Enumerable.Range(0, 16).Select(_ => a.Pick("x", 1000)).ToList();
        Assert.Equal(streamA, Enumerable.Range(0, 16).Select(_ => b.Pick("x", 1000)).ToList());
        Assert.NotEqual(streamA, Enumerable.Range(0, 16).Select(_ => c.Pick("x", 1000)).ToList());
    }

    /// <summary>Every valid member parses and elaborates with no diagnostic (host operations in scope).</summary>
    [Fact]
    public void EveryValidMember_PassesTheFrontEndCleanly()
    {
        var members = 0;
        foreach (var semanticCase in SemanticCorpus.All().Where(c => c.Kind != SemanticCaseKind.InvalidFrontEnd))
        {
            foreach (var member in semanticCase.Members)
            {
                var parsed = Parser.Parse(member.Source, new RunOptions { HostOperations = HostNames });
                Assert.False(parsed.HasErrors,
                    $"{semanticCase.CaseId}/{member.Role}: {string.Join("; ", parsed.Diagnostics.Select(d => d.Code + " " + d.Message.Split('\n')[0]))}\n{member.Source}");
                members++;
            }
        }

        Assert.True(members > 400, $"only {members} valid members were generated");
    }

    /// <summary>Each invalid production is rejected with its NAMED diagnostic in its NAMED phase.</summary>
    [Fact]
    public void EveryInvalidCase_HasItsNamedDiagnosticInItsNamedPhase()
    {
        var invalid = SemanticCorpus.All().Where(c => c.Kind == SemanticCaseKind.InvalidFrontEnd).ToList();
        Assert.True(invalid.Count >= SemanticGrammar.InvalidProductions.Length);
        foreach (var production in SemanticGrammar.InvalidProductions)
            Assert.Contains(invalid, c => c.Features.Contains("invalid-" + production.Name));

        foreach (var semanticCase in invalid)
        {
            var expected = semanticCase.Expected;
            var syntax = Parser.ParseSyntax(semanticCase.Source);
            var parsed = Parser.Parse(semanticCase.Source, new RunOptions { HostOperations = HostNames });
            Assert.True(parsed.HasErrors, semanticCase.CaseId);
            if (expected.DiagnosticPhase == SemanticExpectation.SyntaxPhase)
            {
                Assert.Contains(syntax.Diagnostics, d => d.Severity == DiagnosticSeverity.Error && d.Code == expected.Diagnostic);
            }
            else
            {
                Assert.Equal(SemanticExpectation.ElaborationPhase, expected.DiagnosticPhase);
                Assert.False(syntax.HasErrors, $"{semanticCase.CaseId} must pass the raw parser");
                Assert.Contains(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error && d.Code == expected.Diagnostic);
            }

            Assert.True(expected.Events.IsEmpty);
            Assert.Single(semanticCase.Members);
        }
    }

    /// <summary>
    /// Alpha-renaming renames BY NAME, so deliberate shadow pairs keep sharing one name, and the
    /// binding graph is re-validated: references keep their declarations. A renaming that would
    /// merge two declarations of one scope is refused.
    /// </summary>
    [Fact]
    public void AlphaRename_PreservesSymbolsAndShadowing_AndRefusesCapture()
    {
        var shadowing = SemanticCorpus.All().First(c => c.Features.Contains("shadowing") && c.Kind == SemanticCaseKind.ValidSuccess);
        var renamed = shadowing.Members.Single(m => m.Role == SemanticMember.AlphaRenameRole).Source;
        Assert.DoesNotContain("v1", renamed, StringComparison.Ordinal);
        Assert.NotEqual(shadowing.Source, renamed);

        // A hand-built shadow pair: the renamed program still declares the inner function under
        // the outer one's name, and both references resolve as before.
        var g = new SemanticGrammar.Gen(SemanticChooser.Systematic(0));
        var outer = g.Fresh();
        var x = g.Fresh();
        var inner = g.ShadowOf(outer);
        var other = g.Fresh();
        MExpr Shadowed(params MExpr[] rows) => new MExpr.Brace(new MScope([new MDecl.Value(inner, [SemanticGrammar.Atom(5)])], rows));

        // A call to `outer` from inside the shadowing scope would bind to the shadow: refused.
        var captured = g.Finish(new MScope(
            [new MDecl.Func(outer, [new MParam(x, false)], new MExpr.Ref(x))],
            [Shadowed(new MExpr.Ref(inner), new MExpr.Call(outer, [SemanticGrammar.Atom(1)]))]));
        Assert.Throws<InvalidOperationException>(captured.ValidateNaming);

        var program = captured with
        {
            Root = new MScope(
                [.. captured.Root.Decls, new MDecl.Value(other, [SemanticGrammar.Atom(2)])],
                [Shadowed(new MExpr.Ref(inner)), new MExpr.Call(outer, [SemanticGrammar.Atom(1)]), new MExpr.Ref(other), captured.Root.Rows[^1]]),
        };
        program.ValidateNaming();
        var alpha = SemanticCorpus.AlphaRename(program);
        Assert.Equal(alpha.Names[outer], alpha.Names[inner]);
        Assert.NotEqual(program.Names[outer], alpha.Names[outer]);

        // Two declarations of one scope may never share a rendered name.
        var graph = ScopeGraph.Build(program.Root);
        Assert.False(graph.RenameKeepsBindings(other, program.Names[outer], program.Names));
        Assert.True(graph.RenameKeepsBindings(other, "fresh", program.Names));
    }

    /// <summary>The new model nodes render the current surface forms (and META parameters render).</summary>
    [Fact]
    public void ExtendedModelNodes_RenderTheCurrentSurfaceForms()
    {
        var g = new SemanticGrammar.Gen(SemanticChooser.Systematic(0));
        var cap = g.Fresh();
        var op = g.Fresh();
        var r = g.Fresh();
        var program = g.Finish(new MScope(
            [
                new MDecl.Func(cap, [new MParam(op, false, Meta: true)], new MExpr.Ref(op)),
                new MDecl.Value(r, [new MExpr.Call(cap, [new MExpr.Prim("trace", [SemanticGrammar.Atom(1)])])]),
            ],
            [
                new MExpr.Select(new MExpr.Dot(new MExpr.Ref(r), "Arguments", null), [SemanticGrammar.Atom(0), new MExpr.Spread(new MExpr.Binary("/", SemanticGrammar.Atom(1), SemanticGrammar.Atom(0)))]),
                new MExpr.ListLit([new MExpr.Dot(new MExpr.Ref(r), "Invoke", []), new MExpr.Binary("*", new MExpr.Add(SemanticGrammar.Atom(1), SemanticGrammar.Atom(2)), SemanticGrammar.Atom(3))]),
            ]));
        Assert.Equal(
            "v1(meta v2) = v2\nv3 = v1(trace(1))\nv3.Arguments[0, (1 / 0)*]\n[v3.Invoke(), (1 + 2) * 3]\n997",
            program.Render());
    }

    /// <summary>
    /// The SEM-2B model extension leaves the ORIGINAL structural corpus byte-identical: its rendered
    /// sources (and therefore every existing case identity and seed meaning) are pinned by digest.
    /// The digest was recorded from the pre-extension revision afcdc715.
    /// </summary>
    [Fact]
    public void LegacyStructuralCorpus_RendersByteIdentically()
    {
        var text = string.Join("\n\u0000\n", StructuralCorpus.All().Select(c => c.CaseId + "\n" + c.Program.Render()));
        var digest = SemanticFingerprint.Of(text);
        Assert.True(digest == LegacyStructuralCorpusDigest, $"legacy structural corpus digest changed: {digest}");
    }

    internal const string LegacyStructuralCorpusDigest =
        "sha256:19a30c09b324433395ec9d8cee8a8bf2d8d7d46d9d2bf81df3489a4677d5cccc";

    [Fact]
    public void NestedPatterns_KeepBinderIdentityThroughRenderingRenamingAndVisitors()
    {
        var g = new SemanticGrammar.Gen(SemanticChooser.Systematic(0));
        var fragment = SemanticGrammar.NestedPattern(g, outerList: false, failing: false);
        var program = g.Finish(new MScope(fragment.Decls, [fragment.Row]));
        program.ValidateNaming();
        Assert.Contains("(([", program.Render(), StringComparison.Ordinal);
        Assert.Contains("*v", program.Render(), StringComparison.Ordinal);
        var alpha = SemanticCorpus.AlphaRename(program);
        Assert.Contains("*w", alpha.Render(), StringComparison.Ordinal);
        var atom = ModelRewriter.CollectExprs<MExpr.Atom>(program.Root).First();
        var rewritten = program with { Root = ModelRewriter.ReplaceExpr(program.Root, atom, atom) };
        rewritten.ValidateNaming();
        Assert.Equal(program.Render(), rewritten.Render());
        Assert.Equal(StructuralShrinker.Size(program), StructuralShrinker.Size(rewritten));
        Assert.DoesNotContain(StructuralTransforms.Enumerate(program), c => c.Rule == StructuralRule.ForceKnownNonMatchingClause);
    }
}
