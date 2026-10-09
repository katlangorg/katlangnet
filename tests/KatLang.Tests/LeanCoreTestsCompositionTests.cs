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
                // These completed-input proof checks retain explicit historical algebra.
                // The production model and current Model-C laws never import that fixture.
                "ExplicitValueOpening" or "HigherOrderCalls" or "RepeatedNameConstraints" or "ValueDemand" =>
                [
                    "HistoricalReadyBinding",
                    "KatLang",
                    "CoreTests.Common",
                ],
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

    [Fact]
    public void HistoricalReadyFixtureNeverEntersTheProductionModel()
    {
        var lean = FindLeanDirectory();
        Assert.DoesNotContain("HistoricalReadyBinding", ReadImports(Path.Combine(lean, "KatLang.lean")));
        Assert.Equal(["KatLang"], ReadImports(Path.Combine(lean, "HistoricalReadyBinding.lean")));
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
