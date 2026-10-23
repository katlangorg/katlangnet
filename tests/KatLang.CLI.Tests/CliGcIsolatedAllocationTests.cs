using KatLang.TestInfrastructure;

namespace KatLang.CLI.Tests;

/// <summary>
/// Runs this assembly's strict allocation measurements in a child test host without background GC
/// (<see cref="GcIsolatedAllocation"/>). The inventory is pinned so that a measurement cannot be
/// dropped or renamed out of the child run silently.
/// </summary>
public class CliGcIsolatedAllocationTests
{
    [Fact]
    public void Inventory_IsPinned()
        => Assert.Equal(
            ["KatLang.CLI.Tests.TerminalSafeDiagnosticsTests.Escaping_SafeText_AllocatesNothing_GcIsolatedChild"],
            GcIsolatedAllocation.ChildTests(typeof(CliGcIsolatedAllocationTests).Assembly));

    [Fact]
    public Task StrictAllocationMeasurements_PassInAHostWithoutBackgroundGc()
        => GcIsolatedAllocation.RunChildrenAsync(typeof(CliGcIsolatedAllocationTests).Assembly);
}
