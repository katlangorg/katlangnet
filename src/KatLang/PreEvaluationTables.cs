namespace KatLang;

/// <summary>
/// The OWNED HAND-OVER of reference-identity table storage between one run's pre-evaluation passes.
/// Before evaluation a run walks its program up to three times, and each walk builds a table keyed by
/// node identity over the whole graph: the synchronous entry guard for deferred module regions (a node
/// set, <see cref="DeferredModuleRegion.RequiresAsyncEvaluationCounting"/>), the structural preflight (a
/// node-to-height table, <see cref="AstStructuralPreflight.CheckAdmittedProgram"/>) and the
/// pre-evaluation validation walk (a visited set, and an alias-reach table when the graph holds an alias;
/// <see cref="AlgorithmValidation.FindFirstPreEvaluationViolation(Expr, FrontEndTraversalObservations?, int, PreEvaluationTables?, bool, CancellationToken)"/>).
/// A pass that has finished with its table hands it over here, and a later pass that needs a table of
/// the same shape takes it instead of allocating its own. Implementation-only: an allocation saving.
///
/// <para><b>One owner at a time.</b> Each shape has one slot. A pass hands its table over as its LAST
/// act on it and never reads or writes it again; <c>Take…</c> MOVES the table out of the slot, so two
/// passes can never hold the same table. A hand-over into an occupied slot is a wiring error and fails
/// loud instead of silently dropping one of the tables.</para>
///
/// <para><b>Storage, never contents.</b> The passes give the same storage different meanings: a visited
/// mark in the guard's set and in the validation walk's, a weighted height or the on-path marker in the
/// preflight's table, an alias-reach answer in the validation walk's. So <c>Take…</c> CLEARS the table
/// before returning it: the taker starts from an empty table that only reuses the giver's storage, and
/// can never observe an entry a previous pass left behind, whatever it meant there. Only
/// reference-identity tables are accepted — a structural comparer would recurse over the very graph the
/// preflight guards.</para>
///
/// <para><b>Per run.</b> One instance per run preparation (<c>Evaluator.PrepareSynchronousRun</c>,
/// <c>Evaluator.PrepareAsyncTwinRun</c>), held in a local and dropped when the preparation returns; it is
/// never stored on the budget, a cache, the tree or any static field. Which tables are handed over, and
/// their sizes, decide nothing: every pass still makes its own complete walk, in the same order, with
/// the same refusals and diagnostics.</para>
/// </summary>
internal sealed class PreEvaluationTables
{
    private HashSet<object>? _nodeSet;
    private Dictionary<object, int>? _nodeTable;

    /// <summary>
    /// Hands a finished pass's node set over to the run's next pass. The caller gives up the set: it must
    /// not read or write it afterwards.
    /// </summary>
    internal void HandOver(HashSet<object> nodeSet)
    {
        RequireReferenceIdentity(nodeSet.Comparer);
        if (_nodeSet is not null)
            throw new InvalidOperationException("The run's pre-evaluation tables already hold a handed-over node set.");
        _nodeSet = nodeSet;
    }

    /// <summary>
    /// Hands a finished pass's node table over to the run's next pass. The caller gives up the table: it
    /// must not read or write it afterwards.
    /// </summary>
    internal void HandOver(Dictionary<object, int> nodeTable)
    {
        RequireReferenceIdentity(nodeTable.Comparer);
        if (_nodeTable is not null)
            throw new InvalidOperationException("The run's pre-evaluation tables already hold a handed-over node table.");
        _nodeTable = nodeTable;
    }

    /// <summary>
    /// Moves the handed-over node set out, EMPTY and with room for <paramref name="capacityHint"/> entries
    /// (capacity only), or returns <c>null</c> when none was handed over.
    /// </summary>
    internal HashSet<object>? TakeNodeSet(int capacityHint)
    {
        var nodeSet = _nodeSet;
        if (nodeSet is null)
            return null;

        _nodeSet = null;
        nodeSet.Clear();
        nodeSet.EnsureCapacity(capacityHint);
        return nodeSet;
    }

    /// <summary>
    /// Moves the handed-over node table out, EMPTY and with room for <paramref name="capacityHint"/>
    /// entries (capacity only), or returns <c>null</c> when none was handed over. The taker gives the
    /// entries its own meaning: none of the giver's survives.
    /// </summary>
    internal Dictionary<object, int>? TakeNodeTable(int capacityHint)
    {
        var nodeTable = _nodeTable;
        if (nodeTable is null)
            return null;

        _nodeTable = null;
        nodeTable.Clear();
        nodeTable.EnsureCapacity(capacityHint);
        return nodeTable;
    }

    private static void RequireReferenceIdentity(IEqualityComparer<object> comparer)
    {
        if (!ReferenceEquals(comparer, ReferenceEqualityComparer.Instance))
            throw new InvalidOperationException("A pre-evaluation table must be keyed by reference identity.");
    }
}
