using System.Reflection;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// The semantic-model builder registers every DOCUMENT-OWNED property declaration eagerly
/// when it opens a scope (<c>CreateScope</c>'s per-property loop): the declaration
/// occurrence, its definition resolution, its <see cref="PropertyInfo"/>, and the
/// declaration→property link — independent of whether anything references the
/// property and whether the scope's completion region is ever emitted. That loop used to
/// also fill a per-frame property table nothing read; the table is gone and the side
/// effects are the reason the loop exists. The same loop runs for a load-elaborated
/// module subtree, where it builds the module's LOCATIONLESS property symbols (the
/// binding surface document lookups resolve to) and registers nothing: a module property
/// is never a declaration site of the importing document, referenced or not, public or
/// not (K7-SEM-R1). These tests fail if either half of that contract goes.
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
    public async Task ModuleProperties_RegisterNoDocumentSites_ReferencedOrNot()
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

        // ... and none of its declarations — private, public, referenced, or unreferenced —
        // is a declaration site of this document.
        Assert.Empty(model.Declarations);
        AssertNotRegistered(model, "Helper");
        AssertNotRegistered(model, "Spare");

        // The referenced Tax enters the model only through the document's reference, as a
        // locationless module-provided target.
        Assert.Empty(model.FindDeclarations("Tax"));
        var reference = Assert.Single(model.FindResolutions("Tax"));
        Assert.Equal(OccurrenceKind.ResolveReference, reference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
        Assert.Null(reference.ResolvedDeclaration);
        var property = Assert.Single(model.FindProperties("Tax"));
        Assert.Same(property, reference.ResolvedProperty);
        Assert.Null(property.Declaration);
        Assert.True(property.IsPublic);
    }

    [Fact]
    public void UnreferencedNestedProperty_IsRegisteredWithItsDefinitionResolution()
    {
        var model = SemanticModelBuilder.Build(
            SourceProvenance.ParseValid("A = {\n    Unused = 5\n    1\n}\nA").Parsed);

        AssertDeclarationRegistered(model, "Unused", line: 2, column: 5);
    }

    [Fact]
    public void UnreferencedPrivateClauseFamily_RegistersEveryDeclarationSpan()
    {
        var model = SemanticModelBuilder.Build(
            SourceProvenance.ParseValid("Hidden(0) = 1\nHidden(x) = x\npublic Visible = 7\nVisible").Parsed);

        // Hidden is private and unreferenced, so eager CreateScope registration is its only
        // semantic-model registration path. Both clause heads must map to the ONE family info.
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

    [Fact]
    public async Task UnreferencedPrivateModuleClauseFamily_RegistersNothing()
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

        // Neither clause head, nor the binder x, nor the family's property info is a
        // document-owned object; Visible reaches the model only through its reference.
        AssertNotRegistered(model, "Hidden");
        AssertNotRegistered(model, "x");
        Assert.Empty(model.Declarations);
        var visible = Assert.Single(model.FindResolutions("Visible"));
        Assert.Null(visible.ResolvedDeclaration);
        Assert.Same(Assert.Single(model.FindProperties("Visible")), visible.ResolvedProperty);
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
    /// No effect of the eager loop for a module-provided declaration: no declaration
    /// occurrence, no resolution site, no identifier occurrence, and no reported property.
    /// </summary>
    private static void AssertNotRegistered(SemanticModel model, string name)
    {
        Assert.Empty(model.FindDeclarations(name));
        Assert.Empty(model.FindResolutions(name));
        Assert.DoesNotContain(model.IdentifierOccurrences, occurrence => occurrence.Name == name);
        Assert.Empty(model.FindProperties(name));
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
        // HasDeferredModuleOpen is a per-frame flag (B2c editor uncertainty), not a name table.
        Assert.Equal(["HasDeferredModuleOpen", "Parameters", "Parent", "PropertyScope"], members);
    }
}
