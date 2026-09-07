using System.Reflection;

namespace KatLang.Tests;

/// <summary>
/// Library-wide policy pin for the shared <see cref="AstWalker"/>'s per-declaration loop.
///
/// <para>The base walker visits every explicit parameter declaration of every algorithm it
/// expands, which is O(N²) on a wide assignment deconstruction: its N synthetic helpers share ONE
/// N-declaration list, so a walker that examines declarations it never uses rescans that list once
/// per helper. The in-family opt-out (<c>VisitsExplicitParameterDeclarations => false</c>) exists
/// for walkers that override neither declaration hook; forgetting it re-creates the quadratic
/// (K2-R2: the load-elaboration guard walked 40k targets in ~10 s, the whole rest of the front end
/// in ~1.5 s). This test makes the policy mechanical for every walker the library ships: a walker
/// that overrides no declaration hook must not inherit the base loop unchanged. Hook overrides
/// and traversal policies may both be inherited. A hook-bearing walker may deliberately disable
/// this loop (e.g. collect markers only in conditional binders), or re-enable an inherited opt-out.
/// The value of a custom policy belongs in that walker's behavioral tests.</para>
/// </summary>
public class AstWalkerDeclarationVisitPolicyTests
{
    private const BindingFlags InstanceMembers =
        BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;

    private static IReadOnlyList<Type> LibraryWalkerTypes()
        => typeof(AstWalker).Assembly.GetTypes()
            .Where(static type => !type.IsAbstract && typeof(AstWalker).IsAssignableFrom(type))
            .OrderBy(static type => type.FullName, StringComparer.Ordinal)
            .ToList();

    private static bool OverridesMethod(Type type, string name)
    {
        var method = type.GetMethod(name, InstanceMembers);
        Assert.NotNull(method);
        return method.DeclaringType != typeof(AstWalker);
    }

    private static bool InheritsUnusedDeclarationLoop(Type type)
    {
        if (OverridesMethod(type, "VisitExplicitParameterDeclaration")
            || OverridesMethod(type, "VisitCollectMarker"))
            return false;

        var property = type.GetProperty("VisitsExplicitParameterDeclarations", InstanceMembers);
        Assert.NotNull(property);
        var getter = property.GetGetMethod(nonPublic: true);
        Assert.NotNull(getter);
        return getter.DeclaringType == typeof(AstWalker);
    }

    [Fact]
    public void LibraryWalkers_AreEnumerated()
    {
        // The policy below must actually cover the shipped walkers; an empty enumeration would
        // make it vacuous. The guard, the pre-evaluation validation walker, the exposure marker,
        // and the module loader's pre-scan are the known members.
        var names = LibraryWalkerTypes().Select(static type => type.Name).ToList();
        Assert.Contains("LoadWalker", names);
        Assert.Contains("PreEvaluationValidationWalker", names);
        Assert.Contains("FinalExposureMarker", names);
        Assert.Contains("LoadBearingMarker", names);
    }

    [Fact]
    public void EveryLibraryWalker_OptsOutOfDeclarationVisits_UnlessItOverridesADeclarationHook()
    {
        var violations = new List<string>();

        foreach (var type in LibraryWalkerTypes())
        {
            if (InheritsUnusedDeclarationLoop(type))
            {
                violations.Add(
                    $"{type.FullName}: overrides neither VisitExplicitParameterDeclaration nor VisitCollectMarker "
                    + "but keeps the base per-declaration loop enabled. Override "
                    + "VisitsExplicitParameterDeclarations => false, or the walk is O(N^2) on a wide "
                    + "assignment deconstruction (N helpers sharing one N-declaration list).");
            }
        }

        Assert.True(
            violations.Count == 0,
            "AstWalker declaration-visit policy violations:" + Environment.NewLine
            + string.Join(Environment.NewLine, violations));
    }

    [Fact]
    public void Policy_RespectsInheritedHooksAndPolicies()
    {
        Assert.True(InheritsUnusedDeclarationLoop(typeof(UnusedWalker)));
        Assert.True(InheritsUnusedDeclarationLoop(typeof(InheritedUnusedWalker)));
        Assert.False(InheritsUnusedDeclarationLoop(typeof(InheritedOptOutWalker)));
        Assert.False(InheritsUnusedDeclarationLoop(typeof(InheritedDeclarationWalker)));
        Assert.False(InheritsUnusedDeclarationLoop(typeof(ReenabledDeclarationWalker)));
        Assert.False(InheritsUnusedDeclarationLoop(typeof(ConditionalMarkerWalker)));
    }

    [Fact]
    public void Observations_CountDeclarationIterations_EvenWithNoOpHooks()
    {
        // A small positive calibration for the counter: the production guard correctly records
        // zero, but deleting the recording point must still fail a permanent regression test.
        var root = SourceProvenance.ParseSyntaxValidRoot("a, b, c = range(1, 4)\na");
        var observations = new FrontEndTraversalObservations();
        new UnusedWalker { TraversalObservations = observations }.VisitAlgorithm(root);
        Assert.Equal(9, observations.WalkerParameterDeclarationVisits); // Three lists of three.
        Assert.Equal(25, observations.WalkerAlgorithmExpansions + observations.WalkerExpressionExpansions);
        Assert.Equal(34, observations.WalkerSteps);
    }

    private class UnusedWalker : AstWalker;
    private sealed class InheritedUnusedWalker : UnusedWalker;
    private class OptOutWalker : AstWalker
    {
        protected override bool VisitsExplicitParameterDeclarations => false;
    }
    private sealed class InheritedOptOutWalker : OptOutWalker;
    private class DeclarationWalker : AstWalker
    {
        protected override void VisitExplicitParameterDeclaration(Algorithm algorithm, ParameterDeclaration declaration) { }
    }
    private sealed class InheritedDeclarationWalker : DeclarationWalker;
    private sealed class ReenabledDeclarationWalker : OptOutWalker
    {
        protected override bool VisitsExplicitParameterDeclarations => true;
        protected override void VisitExplicitParameterDeclaration(Algorithm algorithm, ParameterDeclaration declaration) { }
    }
    private sealed class ConditionalMarkerWalker : OptOutWalker
    {
        protected override void VisitCollectMarker(SourceSpan span) { }
    }
}
