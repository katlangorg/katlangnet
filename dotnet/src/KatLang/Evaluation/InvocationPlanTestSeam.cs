namespace KatLang.Evaluation;

/// <summary>
/// <b>INVOCATION-PLAN TEST SEAM</b> (internal; never set by production code). A production run retains
/// invocation plans only under its J7 program gate (<see cref="EvaluationBudget.RetainsInvocationPlans"/>):
/// a META-free program without deferred module regions never allocates one. Tests use this seam to
/// observe the plan machinery directly:
/// <list type="bullet">
/// <item>a run whose budget captures a seam RETAINS plans whatever its program (so a META-free program's
/// plan route can be compared with its ordinary route), and</item>
/// <item>a host operation registered in <see cref="MetaReceivers"/> becomes an internal META receiver:
/// when its wrapper body runs, the receiver gets the wrapper's supplied cells unforced (instead of the
/// ordinary host-argument collection) and may reify their plans, demand them or invoke them — reaching
/// states no surface program can, such as a reference used after its run ended or from a foreign run.</item>
/// </list>
/// <para>A budget captures the seam when it is created, from the ambient activation (<see cref="Activate"/>)
/// or else from <see cref="ProcessDefault"/>; a run created outside both never sees one.</para>
/// </summary>
internal sealed class InvocationPlanTestSeam
{
    private static readonly AsyncLocal<InvocationPlanTestSeam?> Ambient = new();

    internal InvocationPlanTestSeam(IReadOnlyDictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>? metaReceivers = null)
        => MetaReceivers = metaReceivers ?? new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>();

    /// <summary>Host-operation names whose wrapper body is an internal META receiver in a seam run.</summary>
    internal IReadOnlyDictionary<string, Func<IReadOnlyList<NeedCell?>, Result>> MetaReceivers { get; }

    /// <summary>
    /// The seam a budget captures when no activation is ambient. The test assembly sets it only for an
    /// explicit whole-suite plan run (<c>KATLANG_FORCE_INVOCATION_PLANS=1</c>), so every run of that test
    /// process retains plans.
    /// </summary>
    internal static InvocationPlanTestSeam? ProcessDefault { get; set; }

    /// <summary>The seam a budget created in the current flow captures, if any.</summary>
    internal static InvocationPlanTestSeam? Current => Ambient.Value ?? ProcessDefault;

    /// <summary>Activates <paramref name="seam"/> for budgets created in this flow until disposed.</summary>
    internal static IDisposable Activate(InvocationPlanTestSeam seam)
    {
        var previous = Ambient.Value;
        Ambient.Value = seam;
        return new Restore(previous);
    }

    private sealed class Restore(InvocationPlanTestSeam? previous) : IDisposable
    {
        public void Dispose() => Ambient.Value = previous;
    }
}
