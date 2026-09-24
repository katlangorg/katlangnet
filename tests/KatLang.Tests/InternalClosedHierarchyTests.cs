using System.Reflection;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// The INTERNAL finite variant hierarchies are C# <c>closed</c> like the eight public roots
/// (<c>ClosedHierarchyContractTests</c> in the public-API test project pins those; this
/// assembly is a friend, so it can see these). Closing them lets the compiler prove the
/// expression-shaped dispatches over them exhaustive with no catch-all arm
/// (<c>LoopOptimizer.EvalLoopExprPlan</c> and its diagnostic renderer,
/// <c>SequencePipelineOptimizer.ExecuteFilterCount</c> / <c>SourceKind</c>,
/// <c>Evaluator.PreEvaluationValidationError</c>): the fake-variant experiment — a sealed
/// probe variant added to each root — fails the build at exactly those sites and nowhere
/// else. The two roots whose consumers are switch STATEMENTS or kind predicates
/// (<c>OpenCandidate</c>, <c>PreparedSequenceBuiltinSuffixArg</c>) gain the closed
/// contract itself. The former is a class; the latter is a record whose synthesized
/// copy constructor can no longer admit foreign derivations. <c>CallableBindingNode</c>, the
/// evaluator's binding-plan node, was a public root until the September 2026 public API audit
/// made the signature and binding-plan planners internal; it keeps its closed contract here.
/// </summary>
public class InternalClosedHierarchyTests
{
    private static readonly Assembly KatLangAssembly = typeof(KatLangEngine).Assembly;

    /// <summary>One row per internal closed root and the variant names it declares.</summary>
    private static readonly IReadOnlyList<(Type Root, string[] Variants)> ClosedHierarchies =
    [
        (typeof(LoopExprPlan),
            ["Constant", "StringConstant", "StateSlot", "CapturedSlot", "CountedParamSlot", "TempSlot", "TempCall", "Unary", "Binary", "Comparison", "If", "Fallback"]),
        (typeof(FilterCountSourcePlan), ["Generic", "DirectRange"]),
        (typeof(PreEvaluationAstViolation),
            ["ExplicitParametersWithoutOutput", "ConditionalBranchArityMismatch", "ConditionalBranchOutputArityMismatch"]),
        (PreparedSequenceBuiltinSuffixArgType, ["AlgorithmArg", "ValueArg", "WholeNumberArg"]),
        (typeof(OpenCandidate), ["ResolvedOpenCandidate", "UnresolvedOpenCandidate"]),
        (typeof(CallableBindingNode), ["CaptureBindingNode", "CollectingCaptureBindingNode", "SequenceValueBindingNode"]),
    ];

    public static TheoryData<Type, string[]> ClosedRoots
    {
        get
        {
            var data = new TheoryData<Type, string[]>();
            foreach (var (root, variants) in ClosedHierarchies)
                data.Add(root, variants);
            return data;
        }
    }

    private static Type PreparedSequenceBuiltinSuffixArgType
        => typeof(Evaluator).GetNestedType("PreparedSequenceBuiltinSuffixArg", BindingFlags.NonPublic)
            ?? throw new InvalidOperationException("Evaluator.PreparedSequenceBuiltinSuffixArg was not found.");

    [Theory]
    [MemberData(nameof(ClosedRoots))]
    public void InternalRoot_IsClosed_AndDeclaresExactlyItsSealedVariants(Type root, string[] variants)
    {
        Assert.True(IsClosedType(root), $"{root.Name} must carry the closed-type metadata (`closed`).");
        Assert.True(root.IsAbstract, $"{root.Name} is implicitly abstract: only its declared variants are instantiable.");
        Assert.False(root.IsSealed);
        Assert.False(root.IsPublic || root.IsNestedPublic, $"{root.Name} is an internal hierarchy; a public one belongs in the public-API contract table.");

        var declared = DirectVariants(root).OrderBy(type => type.Name, StringComparer.Ordinal).ToList();
        Assert.Equal(variants.OrderBy(name => name, StringComparer.Ordinal), declared.Select(type => type.Name));
        Assert.All(declared, variant => Assert.True(
            variant.IsSealed,
            $"{variant.FullName} must be sealed: every closed root's variants are the leaves of the hierarchy."));
    }

    [Fact]
    public void ThisTableAndThePublicOne_CoverEveryClosedTypeOfTheAssembly()
    {
        // A newly closed internal type joins ClosedRoots (so its variant set is pinned); a
        // public one is pinned by ClosedHierarchyContractTests instead.
        var closedInternal = KatLangAssembly.GetTypes()
            .Where(type => IsClosedType(type) && !(type.IsPublic || type.IsNestedPublic))
            .Select(type => type.FullName!)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();
        var tabled = ClosedHierarchies
            .Select(hierarchy => hierarchy.Root.FullName!)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();

        Assert.Equal(tabled, closedInternal);
    }

    private static bool IsClosedType(Type type)
        => type.CustomAttributes.Any(attribute =>
            attribute.AttributeType.FullName == "System.Runtime.CompilerServices.IsClosedTypeAttribute");

    private static IReadOnlyList<Type> DirectVariants(Type root)
        => KatLangAssembly.GetTypes()
            .Where(type => type.BaseType == root)
            .ToList();
}
