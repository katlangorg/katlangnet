namespace KatLang;

internal sealed partial class StaticStructureQueries
{
    /// <summary>
    /// Q3's invocation projection follows a carrier's row as well as a transparent reference. Namespace selection
    /// deliberately stops at a carrier. The endpoint and last written hop are immutable structural facts; processing
    /// that endpoint's signature remains Q8's responsibility.
    /// </summary>
    private StaticFact InvocationTarget(BodyContext context, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        var own = new StaticFact(StaticFactKind.Structure, context.Key);
        if (context.Body is not Algorithm.User { IsSyntheticDeconstructionPlumbing: false, Output.Count: 1 }
            || WrittenReferenceRow(context) is not { } row)
            return own;

        // OD-D is the same formation gate used by the other Q3 projections, not a recursion/ancestry test.
        var lower = reader.Read(Project(StaticQueryKind.TargetWalk, context.Key, StaticQueryProjection.TargetCycle,
            stratum: StaticCycleCheck.None));
        var final = reader.Read(Project(StaticQueryKind.TargetWalk, context.Key, StaticQueryProjection.TargetCycle,
            stratum: StaticCycleCheck.Lower));
        if (lower.Kind == StaticFactKind.Refused || final.Kind == StaticFactKind.Refused) return own;
        if (lower.IsUnknown || final.IsUnknown) return StaticFact.Unknown;

        var target = reader.Read(Project(StaticQueryKind.TargetWalk, context.Key, StaticQueryProjection.RowTarget,
            stratum: StaticCycleCheck.Formation));
        if (target.IsUnknown) return target;
        if (target.Kind != StaticFactKind.Structure) return own;
        var end = reader.Read(Project(StaticQueryKind.TargetWalk, target.Scope!, StaticQueryProjection.InvocationTarget));
        if (end.IsUnknown) return end;
        // This is an ordinary Read equation: transporting the last-hop spelling is not a Follow equation. Each
        // node observes one terminal dependency, so a shared tail is retained once by the operation's engine.
        return new(StaticFactKind.Structure, end.Scope, Data: end.Data ?? row);
    }
}
