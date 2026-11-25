namespace KatLang;

/// <summary>Explicit handoff of one admitted source operation from name resolution to signature processing.</summary>
internal sealed class DetectedProgram(
    Algorithm root, DiagnosticBag diagnostics, StaticStructureOperation? operation,
    ModuleUnits modules, HostOperations? hostOperations)
{
    internal Algorithm Root { get; } = root;
    internal DiagnosticBag Diagnostics { get; } = diagnostics;
    internal StaticStructureOperation? Operation { get; } = operation;
    internal ModuleUnits Modules { get; } = modules;
    internal HostOperations? HostOperations { get; } = hostOperations;

    public void Deconstruct(out Algorithm root, out DiagnosticBag diagnostics)
        => (root, diagnostics) = (Root, Diagnostics);
}
