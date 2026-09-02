using System.Text.RegularExpressions;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Batch 3 / L5 — the Math metadata relations have ONE owner each.
/// <list type="bullet">
/// <item>The registry descriptor owns the canonical qualified name
/// (<see cref="MathMemberDescriptor.CanonicalQualifiedName"/>), derived once at
/// descriptor construction from <see cref="BuiltinRegistry.MathModuleName"/> and the
/// member name; the callable facts of BOTH spellings and the editor's alias-target
/// metadata carry that very string instance.</item>
/// <item><see cref="AstHelpers"/> owns the two shape classifications — the canonical
/// dot edge <c>Math.X</c> and the prelude alias <c>x</c> — and their strict-value
/// twins. Consumers (implicit-argument resolution, dependency ordering, the
/// evaluator's qualified-native gate) call these instead of re-implementing the
/// shape or re-joining the names; a source scan pins that ownership.</item>
/// </list>
/// Every check iterates the registry, so a future descriptor participates automatically.
/// </summary>
public class MathMetadataOwnershipTests
{
    private static Expr.DotCall MathDot(string memberName, OutputBundle? args)
        => new(new Expr.Resolve(BuiltinRegistry.MathModuleName), memberName, args);

    private static IEnumerable<MathMemberDescriptor> FunctionMembers()
        => BuiltinRegistry.MathMembers.Where(static member => member.Kind != MathMemberKind.Constant);

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
    public void CanonicalQualifiedName_IsDerivedOnce_AndBothSpellingsFactsCarryThatInstance()
    {
        foreach (var member in BuiltinRegistry.MathMembers)
        {
            // Derived once at descriptor construction: repeated reads return the
            // same string instance (a per-read interpolation would not).
            Assert.Same(member.CanonicalQualifiedName, member.CanonicalQualifiedName);

            if (member.Kind == MathMemberKind.Constant)
            {
                // Constants have a qualified name but no callable facts.
                Assert.False(BuiltinRegistry.TryGetMathMemberFacts(member.Name, out _));
                Assert.False(BuiltinRegistry.TryGetMathAliasFacts(member.PreludeAlias, out _));
                continue;
            }

            Assert.True(BuiltinRegistry.TryGetMathMemberFacts(member.Name, out var canonicalFacts));
            Assert.True(BuiltinRegistry.TryGetMathAliasFacts(member.PreludeAlias, out var aliasFacts));

            // Reference identity, not merely equal text: the facts take the
            // descriptor's instance instead of re-joining "Math" + "." + Name.
            Assert.Same(member.CanonicalQualifiedName, canonicalFacts!.CanonicalKey);
            Assert.Same(member.CanonicalQualifiedName, aliasFacts!.CanonicalKey);
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

    // ── Canonical dot shape: `Math.X` ───────────────────────────────────────

    [Fact]
    public void CanonicalDotShape_ClassifiesEveryFunctionMember_AndNoConstant()
    {
        foreach (var member in BuiltinRegistry.MathMembers)
        {
            var bareEdge = MathDot(member.Name, args: null);
            var callEdge = MathDot(member.Name, args: [new Expr.Num(1)]);

            if (member.Kind == MathMemberKind.Constant)
            {
                Assert.False(bareEdge.TryGetRegistryProvenCanonicalMathFacts(isPreludeNameShadowed: null, out _));
                Assert.False(callEdge.HasRegistryProvenStrictValueArguments());
                continue;
            }

            Assert.True(bareEdge.TryGetRegistryProvenCanonicalMathFacts(isPreludeNameShadowed: null, out var facts));
            Assert.Same(member.CanonicalQualifiedName, facts!.CanonicalKey);
            Assert.Equal(member.Name, facts.SpelledName);
            Assert.True(bareEdge.HasRegistryProvenStrictValueArguments());
            Assert.True(callEdge.HasRegistryProvenStrictValueArguments());

            // A shadowed `Math` (a user-defined structural container) never
            // acquires builtin facts from its spelling; shadowing an unrelated
            // name changes nothing.
            Assert.False(bareEdge.TryGetRegistryProvenCanonicalMathFacts(static name => name == "Math", out _));
            Assert.False(callEdge.HasRegistryProvenStrictValueArguments(static name => name == "Math"));
            Assert.True(callEdge.HasRegistryProvenStrictValueArguments(name => name == member.Name));
        }
    }

    [Fact]
    public void CanonicalDotShape_RejectsLookalikes()
    {
        OutputBundle args = [new Expr.Num(1)];
        foreach (var member in FunctionMembers())
        {
            // Same-looking syntax on a non-Math receiver.
            Assert.False(new Expr.DotCall(new Expr.Resolve("Obj"), member.Name, args).HasRegistryProvenStrictValueArguments());
            // Case-distinct and near-miss receiver spellings.
            Assert.False(new Expr.DotCall(new Expr.Resolve("math"), member.Name, args).HasRegistryProvenStrictValueArguments());
            Assert.False(new Expr.DotCall(new Expr.Resolve("MathX"), member.Name, args).HasRegistryProvenStrictValueArguments());
            // The alias or a case-distinct member spelled after the dot.
            Assert.False(MathDot(member.PreludeAlias, args).HasRegistryProvenStrictValueArguments());
            Assert.False(MathDot(member.Name.ToUpperInvariant(), args).HasRegistryProvenStrictValueArguments());
            // A parameter or nested receiver is not the bare module reference.
            Assert.False(new Expr.DotCall(new Expr.Param("Math"), member.Name, args).HasRegistryProvenStrictValueArguments());
            Assert.False(new Expr.DotCall(MathDot(member.Name, null), member.Name, args).HasRegistryProvenStrictValueArguments());
        }

        Assert.False(MathDot("NotAMember", args).HasRegistryProvenStrictValueArguments());
        Assert.False(MathDot("NotAMember", args).TryGetRegistryProvenCanonicalMathFacts(isPreludeNameShadowed: null, out _));
    }

    // ── Alias shape: the bare prelude alias `x` ─────────────────────────────

    [Fact]
    public void AliasShape_ClassifiesEveryFunctionAlias_AndNoConstant()
    {
        foreach (var member in BuiltinRegistry.MathMembers)
        {
            Expr alias = new Expr.Resolve(member.PreludeAlias);
            var aliasCall = new Expr.Call(alias, [new Expr.Num(1)]);

            if (member.Kind == MathMemberKind.Constant)
            {
                Assert.False(alias.TryGetRegistryProvenMathAliasFacts(isPreludeNameShadowed: null, out _));
                Assert.False(aliasCall.HasRegistryProvenStrictValueArguments());
                continue;
            }

            Assert.True(alias.TryGetRegistryProvenMathAliasFacts(isPreludeNameShadowed: null, out var facts));
            Assert.Same(member.CanonicalQualifiedName, facts!.CanonicalKey);
            Assert.Equal(member.PreludeAlias, facts.SpelledName);
            Assert.True(aliasCall.HasRegistryProvenStrictValueArguments());

            // The two shapes project ONE descriptor: identical canonical key and
            // parameter names for the alias and the canonical dot spelling.
            Assert.True(MathDot(member.Name, null).TryGetRegistryProvenCanonicalMathFacts(isPreludeNameShadowed: null, out var canonicalFacts));
            Assert.Same(canonicalFacts!.CanonicalKey, facts.CanonicalKey);
            Assert.Equal(canonicalFacts.Signature.ParameterNames, facts.Signature.ParameterNames);

            // A shadowed alias (any visible user property of that name) is an
            // ordinary neutral callable; shadowing an unrelated name changes nothing.
            Assert.False(alias.TryGetRegistryProvenMathAliasFacts(name => name == member.PreludeAlias, out _));
            Assert.False(aliasCall.HasRegistryProvenStrictValueArguments(name => name == member.PreludeAlias));
            Assert.True(aliasCall.HasRegistryProvenStrictValueArguments(static name => name == "Math"));
        }
    }

    [Fact]
    public void AliasShape_RejectsLookalikes()
    {
        foreach (var member in FunctionMembers())
        {
            // The canonical member name spelled bare is NOT the alias (`Sin` is a free name).
            Assert.False(new Expr.Resolve(member.Name).TryGetRegistryProvenMathAliasFacts(isPreludeNameShadowed: null, out _));
            // Case-distinct spellings are different names under ordinal rules.
            Assert.False(new Expr.Resolve(member.PreludeAlias.ToUpperInvariant()).TryGetRegistryProvenMathAliasFacts(isPreludeNameShadowed: null, out _));
            // A parameter reference is never an alias (a detected parameter is an Expr.Param).
            Assert.False(new Expr.Param(member.PreludeAlias).TryGetRegistryProvenMathAliasFacts(isPreludeNameShadowed: null, out _));
            // A dotted spelling of the alias is not the bare alias shape.
            Assert.False(new Expr.DotCall(new Expr.Resolve("Obj"), member.PreludeAlias).TryGetRegistryProvenMathAliasFacts(isPreludeNameShadowed: null, out _));
            // A call whose callee is not a bare name carries no alias facts.
            Assert.False(new Expr.Call(new Expr.Call(new Expr.Resolve(member.PreludeAlias), []), [new Expr.Num(1)]).HasRegistryProvenStrictValueArguments());
        }

        // A user-looking name that is no alias.
        Assert.False(new Expr.Resolve("sine").TryGetRegistryProvenMathAliasFacts(isPreludeNameShadowed: null, out _));
        Assert.False(new Expr.Call(new Expr.Resolve("sine"), [new Expr.Num(1)]).HasRegistryProvenStrictValueArguments());
    }

    // ── Ownership: consumers do not re-implement the relations ──────────────

    /// <summary>The raw registry relation; only the two owners may consult it directly.</summary>
    private static readonly Regex RawMathFactLookup = new(
        @"\bTryGetMath(?:Member|Alias)Facts\s*\(",
        RegexOptions.Compiled | RegexOptions.CultureInvariant);

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
    public void OnlyTheOwnersConsultRawMathFacts_AndNoConsumerReJoinsTheQualifiedName()
    {
        var sourceRoot = Path.Combine(FindRepoRoot(), "src", "KatLang");
        var factOwners = new HashSet<string>(StringComparer.Ordinal) { "AstHelpers.cs", "BuiltinRegistry.cs" };
        var offenders = new List<string>();

        foreach (var path in ProductionSources(sourceRoot))
        {
            var fileName = Path.GetFileName(path);
            var text = File.ReadAllText(path);

            if (!factOwners.Contains(fileName) && RawMathFactLookup.IsMatch(text))
                offenders.Add($"{fileName}: consults the raw registry fact lookup instead of the AstHelpers shape classifiers.");
            if (fileName != "BuiltinRegistry.cs" && ReJoinedQualifiedName.IsMatch(text))
                offenders.Add($"{fileName}: re-joins the canonical qualified Math name instead of reading MathMemberDescriptor.CanonicalQualifiedName.");
            if (fileName != "BuiltinRegistry.cs" && ReSpelledSemanticModuleName.IsMatch(text))
                offenders.Add($"{fileName}: re-spells the Math module name in a semantic-name operation instead of using BuiltinRegistry.MathModuleName or an AstHelpers classifier.");
        }

        Assert.True(offenders.Count == 0, string.Join(Environment.NewLine, offenders));

        // The scan is live: the owners themselves do contain each raw relation.
        Assert.Matches(RawMathFactLookup, File.ReadAllText(Path.Combine(sourceRoot, "AstHelpers.cs")));
        var registry = File.ReadAllText(Path.Combine(sourceRoot, "BuiltinRegistry.cs"));
        Assert.Matches(RawMathFactLookup, registry);
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
