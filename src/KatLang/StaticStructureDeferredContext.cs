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
}
