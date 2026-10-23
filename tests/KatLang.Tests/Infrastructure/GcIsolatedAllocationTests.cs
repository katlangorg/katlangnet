namespace KatLang.Tests.Infrastructure;

/// <summary>
/// Runs this assembly's strict allocation measurements in a child test host without background GC
/// (<see cref="GcIsolatedAllocation"/>). The inventory is pinned so that a measurement cannot be
/// dropped or renamed out of the child run silently; coarse allocation bounds stay in-process.
/// </summary>
public class GcIsolatedAllocationTests
{
    [Fact]
    public void Inventory_IsPinned()
        => Assert.Equal(
            [
                "KatLang.Tests.AlgorithmParameterNamesTests.Projections_OfAParameterizedAlgorithm_CostOneSmallArray_AndTheCountIsFree_GcIsolatedChild",
                "KatLang.Tests.AlgorithmParameterNamesTests.Projections_OfAZeroParameterAlgorithm_AllocateNothing_GcIsolatedChild",
                "KatLang.Tests.AlgorithmPayloadReviewTests.WithParameters_NonUserIdentity_DoesNotAllocateDiscardedPatterns_GcIsolatedChild",
                "KatLang.Tests.MetaCallBindingContextTests.AnEmptyMintedNeedTier_CostsNoExtraAllocation_GcIsolatedChild",
                "KatLang.Tests.NeedCellProjectionFlightTests.IdentityOnlyProjection_RereadsAllocateNothing_GcIsolatedChild",
                "KatLang.Tests.OrdinaryCallLookupTests.Lookups_AllocateNothing_AtAnyTier_GcIsolatedChild",
                "KatLang.Tests.ScopeVisibilityRepresentationTests.Queries_AllocateIndependentlyOfTheScopeWidth_GcIsolatedChild",
                "KatLang.Tests.SharedValueGraphComplexityTests.ScalarFastPath_AllocatesNothing_GcIsolatedChild",
                "KatLang.Tests.WideDeconstructionScalabilityTests.TargetMetadata_DoesNotAllocateBeyondTheHelperRecord_GcIsolatedChild",
            ],
            GcIsolatedAllocation.ChildTests(typeof(GcIsolatedAllocationTests).Assembly));

    [Fact]
    public Task StrictAllocationMeasurements_PassInAHostWithoutBackgroundGc()
        => GcIsolatedAllocation.RunChildrenAsync(typeof(GcIsolatedAllocationTests).Assembly);
}
