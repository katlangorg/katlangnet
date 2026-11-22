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
                "KatLang.Tests.CollectionBuiltinDispatchTests.CallItems_AllocateExactlyTheirItemArray_GcIsolatedChild",
                "KatLang.Tests.CollectionBuiltinDispatchTests.ControlReadingDispatch_AllocatesNoClosureOrDelegate_GcIsolatedChild",
                "KatLang.Tests.CollectionBuiltinDispatchTests.ZeroControlDispatch_AllocatesOnlyItsCallItems_GcIsolatedChild",
                "KatLang.Tests.CollectionResultHandoverAllocationTests.Atoms_OfAFlatList_AllocatesTheNumbersAndOneExactArray_GcIsolatedChild",
                "KatLang.Tests.CollectionResultHandoverAllocationTests.CollectorMaterialization_AllocatesOneExactArray_GcIsolatedChild",
                "KatLang.Tests.CollectionResultHandoverAllocationTests.Distinct_AllocatesItsSetOneBitSetAndOneExactArray_GcIsolatedChild",
                "KatLang.Tests.CollectionResultHandoverAllocationTests.Distinct_LargeInput_AllocatesWithTheNumberOfFirstOccurrences_GcIsolatedChild",
                "KatLang.Tests.CollectionResultHandoverAllocationTests.FusedDotReceiverItems_AllocateNothingPerItem_GcIsolatedChild",
                "KatLang.Tests.CollectionResultHandoverAllocationTests.NumericReducers_AllocateNothingPerItem_GcIsolatedChild",
                "KatLang.Tests.CollectionResultHandoverAllocationTests.OrderResults_AllocateThePositionsTheNumbersAndOneExactArray_GcIsolatedChild",
                "KatLang.Tests.CollectionResultHandoverAllocationTests.OrderResults_OfDenseWholeNumbers_AllocateTheBucketsTheNumbersAndOneExactArray_GcIsolatedChild",
                "KatLang.Tests.CollectionResultHandoverAllocationTests.RetainedTake_AllocatesOneExactArray_GcIsolatedChild",
                "KatLang.Tests.CollectionResultHandoverAllocationTests.SliceResults_AllocateOneExactArray_GcIsolatedChild",
                "KatLang.Tests.FamilyLiteralHeadBindingTests.FlatLiteralHead_AllocatesOnlyItsEnvironment_GcIsolatedChild",
                "KatLang.Tests.FlatCaptureHeadBindingTests.BoundBodyEntry_ProjectsTheParameterNamesOncePerCall_GcIsolatedChild",
                "KatLang.Tests.FlatCaptureHeadBindingTests.FindDuplicatePropName_OfAShortPropertyList_AllocatesNothing_GcIsolatedChild",
                "KatLang.Tests.FlatCaptureHeadBindingTests.FlatCaptureHead_AllocatesExactlyItsEnvironment_AndARefusalNothing_GcIsolatedChild",
                "KatLang.Tests.LiteralClauseRunTests.ASelection_AllocatesNothing_GcIsolatedChild",
                "KatLang.Tests.MetaCallBindingContextTests.AnEmptyMintedNeedTier_CostsNoExtraAllocation_GcIsolatedChild",
                "KatLang.Tests.NeedCellContextAndRecordTests.ARecordsFirstPair_AllocatesNoTable_GcIsolatedChild",
                "KatLang.Tests.NeedCellDemandScaffoldingTests.AMathNativeCall_AllocatesExactlyItsReadsAndItsResult_GcIsolatedChild",
                "KatLang.Tests.NeedCellDemandScaffoldingTests.AnUnjoinedAsynchronousDemand_AllocatesOnlyItsContextAndStateMachines_GcIsolatedChild",
                "KatLang.Tests.NeedCellDemandScaffoldingTests.AnUnjoinedSynchronousDemand_AllocatesOnlyItsContext_GcIsolatedChild",
                "KatLang.Tests.NeedCellDemandScaffoldingTests.DemandAndMathWorkloads_StayBelowTheirMeasuredBounds_GcIsolatedChild",
                "KatLang.Tests.NeedCellEdgesAndGateTests.ACellTheGraphTablesKeyed_StillLocksWithoutAllocating_GcIsolatedChild",
                "KatLang.Tests.NeedCellEdgesAndGateTests.ACell_IsItsOwnGate_AndAllocatesNothingBesideItself_GcIsolatedChild",
                "KatLang.Tests.NeedCellEdgesAndGateTests.AnUnjoinedRuntimeProjection_AllocatesNoCompletion_GcIsolatedChild",
                "KatLang.Tests.NeedCellProjectionFlightTests.IdentityOnlyProjection_RereadsAllocateNothing_GcIsolatedChild",
                "KatLang.Tests.OrdinaryCallBindingAllocationTests.BuiltinArgumentSupply_AllocatesNoIteratorOrDelegate_GcIsolatedChild",
                "KatLang.Tests.OrdinaryCallBindingAllocationTests.BuiltinCallback_AllocatesOnlyItsSupplyArrays_GcIsolatedChild",
                "KatLang.Tests.OrdinaryCallBindingAllocationTests.FlatUniqueLevel_BindingAllocatesExactlyTheResultArray_GcIsolatedChild",
                "KatLang.Tests.OrdinaryCallLookupTests.Lookups_AllocateNothing_AtAnyTier_GcIsolatedChild",
                "KatLang.Tests.ReadOnlyViewAllocationTests.TakeOwnership_AllocatesTheValueAndOneViewOverTheGivenArray_GcIsolatedChild",
                "KatLang.Tests.ScopeVisibilityRepresentationTests.Queries_AllocateIndependentlyOfTheScopeWidth_GcIsolatedChild",
                "KatLang.Tests.SemanticModelNameLookupTests.NameQueries_AllocateOnlyTheirResultLists_GcIsolatedChild",
                "KatLang.Tests.SemanticModelPositionLookupTests.PositionQueries_AllocateNothing_GcIsolatedChild",
                "KatLang.Tests.SharedValueGraphComplexityTests.HostComparer_OneComparison_OfTheDifferentlySharedPair_AllocatesUnderEightMegabytes_GcIsolatedChild",
                "KatLang.Tests.SharedValueGraphComplexityTests.ReferenceClassEntries_TheIsomorphicControlAndUnsharedTrees_StayUnderTheOneEntryBounds_GcIsolatedChild",
                "KatLang.Tests.SharedValueGraphComplexityTests.ReferenceClasses_OneComparison_OfTheDifferentlySharedPair_AllocatesUnderEightMegabytes_GcIsolatedChild",
                "KatLang.Tests.SharedValueGraphComplexityTests.ScalarFastPath_AllocatesNothing_GcIsolatedChild",
                "KatLang.Tests.WideBodyDuplicatePropertyCheckTests.AWideVerdict_IsReusedWithoutAllocating_GcIsolatedChild",
                "KatLang.Tests.WideDeconstructionScalabilityTests.TargetMetadata_DoesNotAllocateBeyondTheHelperRecord_GcIsolatedChild",
                "KatLang.Tests.WideParameterFrameTests.WideFrameReads_AllocateNothing_OwnAndCaptured_GcIsolatedChild",
            ],
            GcIsolatedAllocation.ChildTests(typeof(GcIsolatedAllocationTests).Assembly));

    [Fact]
    public Task StrictAllocationMeasurements_PassInAHostWithoutBackgroundGc()
        => GcIsolatedAllocation.RunChildrenAsync(typeof(GcIsolatedAllocationTests).Assembly);
}
