using System.Text.RegularExpressions;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Batch 3 / L5 — the Math metadata relations have ONE owner each.
/// <list type="bullet">
/// <item>The registry descriptor owns the canonical qualified name
/// (<see cref="MathMemberDescriptor.CanonicalQualifiedName"/>), derived once at
/// descriptor construction from <see cref="BuiltinRegistry.MathModuleName"/> and the
/// member name; the editor's alias-target metadata carries that very string instance.</item>
/// <item>No consumer classifies a written Math reference by its spelling or shape: the
/// resolver classifies the member a reference resolves to by identity
/// (<c>ImplicitArgumentResolver.PreludeContext.IsStrictValue</c>, read through the
/// formula-lifting roles). The registry keeps no callable-facts table to consult, and a
/// source scan pins that no consumer re-joins the qualified name or re-spells the module.</item>
/// </list>
/// Every check iterates the registry, so a future descriptor participates automatically.
/// </summary>
public class MathMetadataOwnershipTests
{
    // ── Canonical qualified name ────────────────────────────────────────────

    [Fact]
    public void CanonicalQualifiedName_IsModuleDotMember_ForEveryDescriptor()
    {
        // The relation restated BY HAND — the reviewed pin — for constants and
        // functions alike.
        Assert.Equal("Math", BuiltinRegistry.MathModuleName);
        Assert.NotEmpty(BuiltinRegistry.MathMembers);
        foreach (var member in BuiltinRegistry.MathMembers)
            Assert.Equal("Math." + member.Name, member.CanonicalQualifiedName);
    }

    [Fact]
    public void CanonicalQualifiedName_IsDerivedOnce()
    {
        foreach (var member in BuiltinRegistry.MathMembers)
        {
            // Derived once at descriptor construction: repeated reads return the
            // same string instance (a per-read interpolation would not).
            Assert.Same(member.CanonicalQualifiedName, member.CanonicalQualifiedName);
        }
    }

    [Fact]
    public void EditorAliasTarget_CarriesTheDescriptorQualifiedNameInstance()
    {
        foreach (var member in BuiltinRegistry.MathMembers)
        {
            var aliasSymbol = Assert.Single(PreludeCatalog.Symbols, symbol => symbol.Name == member.PreludeAlias);
            var target = aliasSymbol.Property!.AliasTarget;
            Assert.NotNull(target);
            Assert.Same(member.CanonicalQualifiedName, target!.QualifiedName);
        }
    }

    // ── Ownership: consumers do not re-implement the relations ──────────────

    /// <summary>A re-joined canonical name: the module prefix spelled together with a member name.</summary>
    private static readonly Regex ReJoinedQualifiedName = new(
        @"\$""Math\.\{|""Math\.""\s*\+|MathModuleName\s*\+\s*""\.""|""Math""\s*\+\s*""\.""",
        RegexOptions.Compiled | RegexOptions.CultureInvariant);

    /// <summary>
    /// A bare module literal used in a semantic-name operation. Deliberately does
    /// not ban every <c>"Math"</c> string in production: user-facing prose and
    /// unrelated text are legitimate. These are the code shapes that would
    /// re-own prelude membership, receiver identity, or canonical name lookup.
    /// </summary>
    private static readonly Regex ReSpelledSemanticModuleName = new(
        @"(?:\bName\s*:\s*|\b(?:ownerName|moduleName|name)\s*(?:==|!=)\s*|\bnew\s+(?:Property|Expr\.Resolve)\s*\(\s*)""Math""|""Math""\s*(?:==|!=)\s*\b(?:ownerName|moduleName|name)",
        RegexOptions.Compiled | RegexOptions.CultureInvariant);

    private static readonly Regex MathModuleDefinition = new(
        @"\bconst\s+string\s+MathModuleName\s*=\s*""Math""\s*;",
        RegexOptions.Compiled | RegexOptions.CultureInvariant);

    [Fact]
    public void NoConsumerReJoinsTheQualifiedName_OrReSpellsTheModuleName()
    {
        var sourceRoot = Path.Combine(FindRepoRoot(), "src", "KatLang");
        var offenders = new List<string>();

        foreach (var path in ProductionSources(sourceRoot))
        {
            var fileName = Path.GetFileName(path);
            if (fileName == "BuiltinRegistry.cs")
                continue;

            var text = File.ReadAllText(path);
            if (ReJoinedQualifiedName.IsMatch(text))
                offenders.Add($"{fileName}: re-joins the canonical qualified Math name instead of reading MathMemberDescriptor.CanonicalQualifiedName.");
            if (ReSpelledSemanticModuleName.IsMatch(text))
                offenders.Add($"{fileName}: re-spells the Math module name in a semantic-name operation instead of using BuiltinRegistry.MathModuleName.");
        }

        Assert.True(offenders.Count == 0, string.Join(Environment.NewLine, offenders));

        // The scan is live: the owner itself does contain each raw relation.
        var registry = File.ReadAllText(Path.Combine(sourceRoot, "BuiltinRegistry.cs"));
        Assert.Matches(ReJoinedQualifiedName, registry);
        Assert.Matches(MathModuleDefinition, registry);
    }

    [Fact]
    public void SemanticModuleLiteralScan_DoesNotBanUserFacingText()
    {
        Assert.DoesNotMatch(ReSpelledSemanticModuleName, "throw new InvalidOperationException(\"Math\");");
        Assert.DoesNotMatch(ReSpelledSemanticModuleName, "var helpText = \"Math\";");
        Assert.Matches(ReSpelledSemanticModuleName, "target is Expr.Resolve { Name: \"Math\" }");
        Assert.Matches(ReSpelledSemanticModuleName, "ownerName == \"Math\"");
        Assert.Matches(ReSpelledSemanticModuleName, "new Property(\"Math\", algorithm)");
    }

    private static IEnumerable<string> ProductionSources(string sourceRoot)
        => Directory
            .EnumerateFiles(sourceRoot, "*.cs", SearchOption.AllDirectories)
            .Where(static path =>
                !path.Contains($"{Path.DirectorySeparatorChar}obj{Path.DirectorySeparatorChar}", StringComparison.Ordinal)
                && !path.Contains($"{Path.DirectorySeparatorChar}bin{Path.DirectorySeparatorChar}", StringComparison.Ordinal)
                && !path.Contains($"{Path.DirectorySeparatorChar}artifacts{Path.DirectorySeparatorChar}", StringComparison.Ordinal));

    private static string FindRepoRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "KatLang.slnx")))
            directory = directory.Parent;

        Assert.True(directory is not null, "Could not locate the repository root (KatLang.slnx).");
        return directory!.FullName;
    }
}
