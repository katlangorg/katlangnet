using System.Reflection;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// The semantic-model builder registers every property DECLARATION eagerly when
/// it opens a scope (<c>CreateScope</c>'s per-property loop): the declaration
/// occurrence, its definition resolution, its <see cref="PropertyInfo"/>, and the
/// declaration→property link — independent of whether anything references the
/// property and whether the scope's completion region is ever emitted. That
/// loop used to also fill a per-frame property table nothing read; the table is
/// gone, the side effects are the reason the loop exists, and these tests fail if
/// the loop (or any one of its effects) goes with it. Load-elaborated module
/// subtrees are the discriminating case: their scope regions are suppressed, so
/// no completion enumeration ever touches their properties and the eager loop is
/// the ONLY registration path for an unreferenced module property.
/// </summary>
public class SemanticModelDeclarationRegistrationTests
{
    private const string ModuleUrl = "https://katlang.org/lib.kat";

    private static RunOptions InMemoryModule(string module) => new()
    {
        DownloadCode = (url, _) => url.TrimEnd('/') == ModuleUrl
            ? ValueTask.FromResult(module)
            : throw new InvalidOperationException($"unexpected download: {url}"),
    };

    [Fact]
    public async Task ModuleProperties_AreRegisteredEvenWhenUnreferencedAndUnenumerated()
    {
        const string module = """
            public Tax = 0.21
            Helper = 9
            public Spare = 7
            """;
        var provenance = await SourceProvenance.ParseValidAsync(
            $"open '{ModuleUrl}'\nTax + 1",
            InMemoryModule(module));
        var model = SemanticModelBuilder.Build(provenance.Parsed);

        // The module emits no completion region (its spans are module-local) ...
        Assert.Single(model.ScopeVisibilities);

        // ... yet its unreferenced properties — private and public alike — are fully
        // registered with module-local coordinates.
        AssertDeclarationRegistered(model, "Helper", line: 2, column: 1);
        AssertDeclarationRegistered(model, "Spare", line: 3, column: 8);
    }

    [Fact]
    public void UnreferencedNestedProperty_IsRegisteredWithItsDefinitionResolution()
    {
        var model = SemanticModelBuilder.Build(
            SourceProvenance.ParseValid("A = {\n    Unused = 5\n    1\n}\nA").Parsed);

        AssertDeclarationRegistered(model, "Unused", line: 2, column: 5);
    }

    [Fact]
    public async Task UnreferencedPrivateModuleClauseFamily_RegistersEveryDeclarationSpan()
    {
        const string module = """
            Hidden(0) = 1
            Hidden(x) = x
            public Visible = 7
            """;
        var provenance = await SourceProvenance.ParseValidAsync(
            $"open '{ModuleUrl}'\nVisible",
            InMemoryModule(module));
        var model = SemanticModelBuilder.Build(provenance.Parsed);

        // Hidden is private, unreferenced, and belongs to a suppressed module
        // region, so eager CreateScope registration is its only semantic-model
        // registration path. Both clause heads must map to the ONE family info.
        var declarations = model.FindDeclarations("Hidden").ToList();
        Assert.Equal([1, 2], declarations.Select(static declaration => declaration.Span.StartLineNumber).ToList());

        var property = Assert.Single(model.FindProperties("Hidden"));
        Assert.Same(declarations[0], property.Declaration);
        foreach (var declaration in declarations)
        {
            Assert.Same(property, model.FindPropertyByDeclaration(declaration));
            var resolution = Assert.Single(
                model.IdentifierResolutions,
                candidate => ReferenceEquals(candidate.Occurrence, declaration));
            Assert.Equal(IdentifierClassification.PropertyDefinition, resolution.Classification);
            Assert.Same(declaration, resolution.ResolvedDeclaration);
            Assert.Same(property, resolution.ResolvedProperty);
        }
    }

    /// <summary>
    /// Every effect of the eager loop, in execution order: the declaration
    /// occurrence exists, it is linked to the property's info, its definition
    /// resolution exists and carries that info, and the info is reported.
    /// </summary>
    private static void AssertDeclarationRegistered(SemanticModel model, string name, int line, int column)
    {
        var declaration = Assert.Single(model.FindDeclarations(name));
        Assert.Equal(OccurrenceKind.PropertyDefinition, declaration.Kind);
        Assert.Equal(line, declaration.Span.StartLineNumber);
        Assert.Equal(column, declaration.Span.StartColumn);

        var property = Assert.Single(model.FindProperties(name));
        Assert.Same(declaration, property.Declaration);
        Assert.Same(property, model.FindPropertyByDeclaration(declaration));

        var resolution = Assert.Single(
            model.IdentifierResolutions,
            candidate => ReferenceEquals(candidate.Occurrence, declaration));
        Assert.Equal(IdentifierClassification.PropertyDefinition, resolution.Classification);
        Assert.Same(declaration, resolution.ResolvedDeclaration);
        Assert.Same(property, resolution.ResolvedProperty);
    }

    /// <summary>
    /// Architecture audit: a builder scope frame binds parameters and points at the
    /// authoritative property scope level — it never carries a property table of
    /// its own. Property lookup has one owner, <c>ElaboratedScopeLookup</c>.
    /// </summary>
    [Fact]
    public void ScopeFrame_CarriesNoPropertyTable()
    {
        var frame = typeof(SemanticModelBuilder).GetNestedType("ScopeFrame", BindingFlags.NonPublic);
        Assert.NotNull(frame);

        var members = frame!
            .GetProperties(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
            .Select(static property => property.Name)
            .OrderBy(static name => name, StringComparer.Ordinal)
            .ToList();
        Assert.Equal(["Parameters", "Parent", "PropertyScope"], members);
    }
}
