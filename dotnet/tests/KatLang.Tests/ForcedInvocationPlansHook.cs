using System.Runtime.CompilerServices;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// WHOLE-SUITE PLAN RUN. With the environment variable <c>KATLANG_FORCE_INVOCATION_PLANS=1</c>, every
/// evaluator run of this test process captures an <see cref="InvocationPlanTestSeam"/>
/// (<see cref="InvocationPlanTestSeam.ProcessDefault"/>), so the entire suite executes with every call-shaped
/// supplied argument routed through its retained plan — the agreement check between the J7 gate's ordinary
/// route and the plan route. This is a legacy, explicitly requested diagnostic mode, never a second
/// normal validation pass. The validation script removes the variable:
/// without the variable nothing changes. The variable is read once, when the test assembly loads, so it
/// is set or removed in the test host's environment before the host starts — never toggled by a test.
/// A test whose expectation legitimately depends on the route — plan and supply-formation counts,
/// <see cref="EvaluationBudget.RetainsInvocationPlans"/>, plan-disabled fusion hits — selects between its
/// two independently justified expectations with <see cref="Forced"/>; values, effects, charges and
/// diagnostics never depend on it.
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
