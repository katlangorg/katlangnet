using System.Runtime.CompilerServices;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// WHOLE-SUITE PLAN RUN. With the environment variable <c>KATLANG_FORCE_INVOCATION_PLANS=1</c>, every
/// evaluator run of this test process captures an <see cref="InvocationPlanTestSeam"/>
/// (<see cref="InvocationPlanTestSeam.ProcessDefault"/>), so the entire suite executes with every call-shaped
/// supplied argument routed through its retained plan — the agreement check between the J7 gate's ordinary
/// route and the plan route. It is an explicit investigation mode, never part of ordinary validation:
/// without the variable nothing changes. Tests that compare a plan run against an ordinary run read
/// <see cref="Forced"/>.
/// </summary>
internal static class ForcedInvocationPlansHook
{
    internal const string Variable = "KATLANG_FORCE_INVOCATION_PLANS";

#pragma warning disable CA2255 // A test-process switch: it must apply before any test creates a budget.
    [ModuleInitializer]
    internal static void Initialize()
    {
        if (Environment.GetEnvironmentVariable(Variable) == "1")
            InvocationPlanTestSeam.ProcessDefault = new InvocationPlanTestSeam();
    }
#pragma warning restore CA2255

    /// <summary>Whether this test process runs every evaluation with plans (the forced investigation mode).</summary>
    internal static bool Forced => InvocationPlanTestSeam.ProcessDefault is not null;
}
