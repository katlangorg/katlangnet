namespace KatLang;

/// <summary>A deferred occurrence keeps identities and completed program publications, never an eager query operation.</summary>
internal sealed record StaticStructureDeferredContext(
    ModuleUnitRegistry Registry,
    StaticScopeKey Declaring,
    Pattern Pattern,
    string BranchName,
    ParameterOwnership CapturedParameters)
{
    internal ImplicitArgumentResolver.ForwardableParameters? Forwardable { get; init; }

    /// <summary>
    /// Set, beside <see cref="Forwardable"/>, when implicit-argument resolution LEFT THE BRANCH'S PROVISIONAL BODY
    /// UNRESOLVED: its own signature selection was refused (<c>ImplicitArgumentResolver.ResolveProvisionalBranch</c>), so
    /// the body in the tree is the detected one and none of its forwardings was charged to the family. The value is the
    /// names of the bodies the selection was refused at (<c>SelectedSignatures.Refusals</c>), distinct, in
    /// first-occurrence order; never empty. Null for a provisional body that was resolved, and before resolution.
    /// <para>Read only to WORD a refused materialization (<c>DeferredModuleRegion.ReportUnchargedEnclosingParameters</c>):
    /// a requirement such a branch's family never charged may be a forwarding to the program's own callable, so the report
    /// must not say a module provides the reference. It decides nothing. The list is compared by reference: nothing reads
    /// this record's equality.</para>
    /// </summary>
    internal IReadOnlyList<string>? UnresolvedProvisionalBodies { get; init; }
}
