using KatLang.Semantics;
using Xunit;

namespace KatLang.Tests;

public class PublicationRecoveryTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task DeferredPresence_PreservesKnownAmbiguityAndDirectOwnership(bool shadow, bool malformed)
    {
        var downloads = 0;
        var source = (shadow ? "X=5\n" : "")
            + "F(0)={\nopen {public X=1}, {public X=2}, 'https://example.test/module'\nX\n}\nF(1)=0\nF(0)"
            + (malformed ? "\n@" : "");
        var parsed = await Parser.ParseAsync(source, new RunOptions {
            AllowedHosts=["example.test"], DownloadCode=(_,_)=>{downloads++;return ValueTask.FromResult("0");} });
        Assert.Equal(malformed, parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);
        var site = Assert.Single(model.FindResolutions("X"), resolution => resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
        Assert.Equal(shadow ? IdentifierClassification.PropertyReference : IdentifierClassification.Unresolved, site.Classification);
        var symbols = model.GetVisibleSymbolsAt(site.Occurrence.Span.Start).Where(symbol => symbol.Name == "X").ToArray();
        if (shadow) Assert.NotNull(Assert.Single(symbols).Declaration);
        else Assert.Empty(symbols);
        Assert.Equal(0, downloads);
    }

    [Theory]
    [InlineData(8)]
    [InlineData(16)]
    [InlineData(32)]
    [InlineData(64)]
    public void EquivalentOpenConsumers_ShareActualQ2IndexWork(int width)
    {
        var source = "Lib={\n" + string.Concat(Enumerable.Range(0, width).Select(i => $"public A{i}={i}\n")) + "0\n}\n"
            + string.Concat(Enumerable.Range(0, width).Select(i => $"P{i}={{open Lib\nA0}}\n")) + "0";
        var syntax = Parser.ParseSyntax(source);
        Assert.False(syntax.HasErrors);
        var observations = new FrontEndTraversalObservations();
        var program = ParameterDetector.DetectPrevalidated(syntax.Root, observations: observations);
        Assert.Equal(0, program.Diagnostics.ReportedErrorCount);
        Assert.Equal(width, observations.StaticOpenTargetComputations);
        Assert.Equal(1, observations.StaticOpenIndexBuilds);
        Assert.Equal(width, observations.StaticOpenIndexMemberVisits);
    }

    [Fact]
    public void SharedLibrarySyntax_InDifferentOwners_KeepsDistinctProviderIndexes()
    {
        var value = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var library = new Algorithm.User(null, [], [], [new Property("K", value, IsPublic: true)], [new Expr.Num(0)]);
        var use = new Algorithm.User(null, [], [new Expr.Resolve("Lib")], [], [new Expr.Resolve("K")]);
        Algorithm Owner() => new Algorithm.User(null, [], [], [new Property("Lib", library), new Property("Use", use)], [new Expr.Num(0)]);
        var root = new Algorithm.User(null, [], [], [new Property("Left", Owner()), new Property("Right", Owner())], [new Expr.Num(0)]);
        var observations = new FrontEndTraversalObservations();
        var program = ParameterDetector.DetectPrevalidated(root, observations: observations);
        Assert.Equal(0, program.Diagnostics.ReportedErrorCount);
        Assert.Equal(2, observations.StaticOpenIndexBuilds);
        Assert.Equal(2, observations.StaticOpenIndexMemberVisits);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void SharedFamily_PublishesCanonicalViews_AndKeepsBindingDiagnostics(bool raw, bool ownOpens)
    {
        foreach (var reversedDeclarations in new[] { false, true })
        foreach (var reversedUses in new[] { false, true })
        {
            var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
            var library = new Algorithm.User(null, [], [], [new Property("K", body, IsPublic: true)], [new Expr.Num(0)]);
            var family = new Algorithm.Conditional(null, ownOpens ? [new Expr.AlgorithmExpr(library)] : [],
                [new CondBranch(new Pattern.LitInt(1), body)]);
            string[] declarations = reversedDeclarations ? ["Second", "First"] : ["First", "Second"];
            string[] uses = reversedUses ? ["Second", "First"] : ["First", "Second"];
            var spans = new SourceSpan[] {
                new(new SourcePosition(10, 3), new SourcePosition(10, 9)),
                new(new SourcePosition(11, 3), new SourcePosition(11, 9)) };
            var root = new Algorithm.User(null, [], [],
                declarations.Select(name => new Property(name, family)).ToArray(),
                uses.Select((name, index) => (Expr)new Expr.Binary(BinaryOp.Add,
                    new Expr.Resolve(name) { Span = spans[index] }, new Expr.Num(0))).ToArray());
            var diagnostics = new DiagnosticBag();
            var observations = new FrontEndTraversalObservations();
            Algorithm resolved;
            if (raw)
            {
                var detected = ParameterDetector.DetectPrevalidated(root, observations: observations, diagnostics: diagnostics);
                Assert.Same(detected.Root.Properties[0].Value, detected.Root.Properties[1].Value);
                resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations: observations);
            }
            else resolved = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root, observations: observations, diagnostics: diagnostics);
            Assert.Same(resolved.Properties[0].Value, resolved.Properties[1].Value);
            Assert.Same(family.Declaration, Assert.IsType<Algorithm.Conditional>(resolved.Properties[0].Value).Declaration);
            var errors = diagnostics.Where(diagnostic => diagnostic.Code == DiagnosticCode.UnliftableClauseFamily).ToArray();
            Assert.Equal(2, errors.Length);
            for (var index = 0; index < errors.Length; index++)
            {
                Assert.StartsWith($"'{uses[index]}' is used as a value here, but clause family '{uses[index]}'", errors[index].Message);
                Assert.Equal(spans[index], errors[index].Span);
            }
            Assert.Equal(1, observations.ResolverBranchBodyRegionExpansions);
        }
    }

    [Theory]
    [InlineData("", false, false)]
    [InlineData("X = 5\n", true, false)]
    [InlineData("", false, true)]
    [InlineData("X = 5\n", true, true)]
    public async Task DeferredPresence_IsVisibleWithoutAProviderPublication(string prefix, bool direct, bool malformed)
    {
        var downloads = 0;
        var source = prefix + "F(0) = {\n open { public X = 1 }, 'https://example.test/module'\n X\n}\nF(1) = 0\nF(0)"
            + (malformed ? "\n@" : "");
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            AllowedHosts = ["example.test"],
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult("public X = 2\n0"); },
        });
        Assert.Equal(malformed, parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);
        var site = Assert.Single(model.FindResolutions("X"), resolution => resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
        var visible = Assert.Single(model.GetVisibleSymbolsAt(site.Occurrence.Span.Start), symbol => symbol.Name == "X");
        Assert.Equal(direct ? IdentifierClassification.PropertyReference : IdentifierClassification.DeferredModuleReference, visible.Classification);
        Assert.Equal(direct, visible.Declaration is not null);
        if (!direct)
        {
            Assert.Null(visible.Property);
            Assert.Empty(visible.Members);
            Assert.Null(site.ResolvedDeclaration);
        }
        Assert.Equal(0, downloads);
    }
}
