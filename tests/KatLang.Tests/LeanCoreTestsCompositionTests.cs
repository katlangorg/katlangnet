using System.Text.RegularExpressions;

namespace KatLang.Tests;

/// <summary>
/// Keeps the split hand-written Lean suite compositionally closed. Lean only
/// elaborates imported modules, so a missing root import can otherwise make a
/// whole domain disappear while <c>lake build CoreTests</c> remains green.
/// </summary>
public class LeanCoreTestsCompositionTests
{
    private static readonly string[] ExpectedModules =
    [
        "Common",
        "CallableSignatures",
        "OutputSemantics",
        "DotCallSemantics",
        "HigherOrderCalls",
        "Conditionals",
        "Strings",
        "SequenceCallbackBuiltins",
        "CollectionBuiltins",
        "SequenceBuiltinRegressions",
        "CollectingParameters",
        "Numerics",
        "DotReceiverSegments",
        "ParityGuards",
        "ValueBoundary",
        "ListValues",
        "CollectingBindings",
        "OutputBundle",
        "NameOwnership",
        "ValueDemand",
        "ComparisonChains",
        "SelectionValueBoundary",
        "ExplicitValueOpening",
        "PropertyCacheConsumers",
        "ArgumentValueOutcome",
        "ForwardingBindings",
        "RepeatedNameConstraints",
        "BuiltinArgumentRoles",
        "StructuralPatterns",
        "AliasForwarding",
        "ModelC",
        "LoopCardinality",
        "LoopSteps",
        "ErrorTaxonomy",
        "DotIdentity",
        "OpenProviderIdentity",
        "ModuleUnits",
        "GraceMovement",
        "FamilyCallbackCardinality",
        "CollectingCallableForwarding",
        "EmptyStructuralPatterns",
        "CallbackResultBoundary",
        "PropertyCachePublication",
        "VariadicSelection",
        "ParentScopeValidation",
        "RepeatedSpread",
    ];

    [Fact]
    public void RootImportsEveryExpectedModuleExactlyOnce()
    {
        var leanDirectory = FindLeanDirectory();
        var actualFiles = Directory
            .EnumerateFiles(Path.Combine(leanDirectory, "CoreTests"), "*.lean", SearchOption.TopDirectoryOnly)
            .Select(Path.GetFileNameWithoutExtension)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var expectedFiles = ExpectedModules.Order(StringComparer.Ordinal).ToArray();

        Assert.Equal(expectedFiles, actualFiles);
        Assert.Equal(
            ExpectedModules.Select(static module => $"CoreTests.{module}"),
            ReadImports(Path.Combine(leanDirectory, "CoreTests.lean")));
    }

    [Fact]
    public void DomainImportsStaySiblingBasedWithOnlyApprovedFixtureEdges()
    {
        var leanDirectory = FindLeanDirectory();
        foreach (var module in ExpectedModules)
        {
            var expected = module switch
            {
                "Common" => new[] { "KatLang" },
                "CollectionBuiltins" =>
                [
                    "KatLang",
                    "CoreTests.Common",
                    "CoreTests.SequenceCallbackBuiltins",
                ],
                "ParityGuards" =>
                [
                    "KatLang",
                    "CoreTests.Common",
                    "CoreTests.DotReceiverSegments",
                ],
                // A standalone model of the C#-only Grace movement law (PAR-06, X-49): it imports
                // nothing, so it can never reach into the evaluator model.
                "GraceMovement" => [],
                _ => new[] { "KatLang", "CoreTests.Common" },
            };

            Assert.Equal(
                expected,
                ReadImports(Path.Combine(leanDirectory, "CoreTests", $"{module}.lean")));
        }
    }

    /// <summary>
    /// Every library the Lean package declares is the authoritative model or one of the seven
    /// canonical validation targets (<c>scripts/validate-all.ps1</c>), so no proof library can sit
    /// outside validation. The historical Ready-binding fixture and its laws were retired on
    /// 2026-10-12 (owner decision; git history keeps them): the laws file imports only the model
    /// and the paper algebra.
    /// </summary>
    [Fact]
    public void LeanPackageDeclaresOnlyTheModelAndTheValidatedTargets()
    {
        var lean = FindLeanDirectory();
        var declarations = File.ReadLines(Path.Combine(lean, "lakefile.lean"))
            .Where(static line => !line.TrimStart().StartsWith("--", StringComparison.Ordinal))
            .Where(static line => Regex.IsMatch(line, @"\b(?:lean_lib|lean_exe|extern_lib|target)\b"))
            .ToArray();
        // Every declaration is a guillemet-quoted library at the start of its line, so the
        // extraction below cannot miss a library written in another Lake form.
        Assert.All(declarations, static line => Assert.Matches(@"^lean_lib «[^»]+» where$", line));
        var libraries = declarations
            .Select(static line => Regex.Match(line, @"^lean_lib «([^»]+)»").Groups[1].Value)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(
            new[]
            {
                "AstDemo",
                "CoreArityAlgebra",
                "CoreArityAlgebraProofs",
                "CoreTests",
                "KatLang",
                "KatLangArityLaws",
                "LanguageSpecCases",
                "SemanticExplorerCases",
            },
            libraries);
        Assert.Equal(["CoreArityAlgebra", "KatLang"], ReadImports(Path.Combine(lean, "KatLangArityLaws.lean")));
        Assert.Equal(["KatLang", "CoreTests.Common"], ReadImports(Path.Combine(lean, "CoreTests", "ModelC.lean")));
    }

    private static string[] ReadImports(string path)
        => File.ReadLines(path)
            .Where(static line => line.StartsWith("import ", StringComparison.Ordinal))
            .Select(static line => line["import ".Length..])
            .ToArray();

    private static string FindLeanDirectory()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory); current is not null; current = current.Parent)
        {
            var candidate = Path.Combine(current.FullName, "lean");
            if (File.Exists(Path.Combine(candidate, "CoreTests.lean")))
                return candidate;
        }

        throw new InvalidOperationException("lean/CoreTests.lean was not found above the test output directory.");
    }
}
