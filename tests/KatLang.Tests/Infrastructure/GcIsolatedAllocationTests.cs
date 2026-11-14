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
                "KatLang.Tests.FamilyLiteralHeadBindingTests.FlatLiteralHead_AllocatesOnlyItsEnvironment_GcIsolatedChild",
                "KatLang.Tests.FlatCaptureHeadBindingTests.BoundBodyEntry_ProjectsTheParameterNamesOncePerCall_GcIsolatedChild",
                "KatLang.Tests.FlatCaptureHeadBindingTests.FindDuplicatePropName_OfAShortPropertyList_AllocatesNothing_GcIsolatedChild",
                "KatLang.Tests.FlatCaptureHeadBindingTests.FlatCaptureHead_AllocatesExactlyItsEnvironment_AndARefusalNothing_GcIsolatedChild",
                "KatLang.Tests.MetaCallBindingContextTests.AnEmptyMintedNeedTier_CostsNoExtraAllocation_GcIsolatedChild",
                "KatLang.Tests.NeedCellProjectionFlightTests.IdentityOnlyProjection_RereadsAllocateNothing_GcIsolatedChild",
                "KatLang.Tests.OrdinaryCallBindingAllocationTests.BuiltinArgumentSupply_AllocatesNoIteratorOrDelegate_GcIsolatedChild",
                "KatLang.Tests.OrdinaryCallBindingAllocationTests.BuiltinCallback_AllocatesOnlyItsSupplyArrays_GcIsolatedChild",
                "KatLang.Tests.OrdinaryCallBindingAllocationTests.FlatUniqueLevel_BindingAllocatesExactlyTheResultArray_GcIsolatedChild",
                "KatLang.Tests.OrdinaryCallLookupTests.Lookups_AllocateNothing_AtAnyTier_GcIsolatedChild",
                "KatLang.Tests.ScopeVisibilityRepresentationTests.Queries_AllocateIndependentlyOfTheScopeWidth_GcIsolatedChild",
                "KatLang.Tests.SharedValueGraphComplexityTests.ReferenceClasses_OneComparison_OfTheDifferentlySharedPair_AllocatesUnderEightMegabytes_GcIsolatedChild",
                "KatLang.Tests.SharedValueGraphComplexityTests.ScalarFastPath_AllocatesNothing_GcIsolatedChild",
                "KatLang.Tests.WideDeconstructionScalabilityTests.TargetMetadata_DoesNotAllocateBeyondTheHelperRecord_GcIsolatedChild",
            ],
            GcIsolatedAllocation.ChildTests(typeof(GcIsolatedAllocationTests).Assembly));

    [Fact]
    public Task StrictAllocationMeasurements_PassInAHostWithoutBackgroundGc()
        => GcIsolatedAllocation.RunChildrenAsync(typeof(GcIsolatedAllocationTests).Assembly);
}
