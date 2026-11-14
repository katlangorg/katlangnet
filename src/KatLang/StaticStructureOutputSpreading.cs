namespace KatLang;

/// <summary>
/// DECLARATION-LEVEL OUTPUT SPREADING, the receiver arm (owner decision D1, November 2026): an extension-call edge
/// <c>R.F(args)</c> whose receiver is a written call to a marked declaration IS the call <c>F(R*, args)</c> from
/// parameter detection on — the order of inferred names included — exactly as the parser lowers the written
/// <c>R*.F(args)</c>. This is the ONE decision: Q7 (<see cref="Inputs"/>) orders the edge's names by it, and the
/// detector's collection walk and rewrite read it through <see cref="StaticStructureOperation.LoweredReceiverMarker"/>
/// and build the call, so implicit-argument resolution never sees the edge and never decides again. It composes
/// existing readings only: the edge's miss verdict (Q5) and the receiver call's callee through Q1's binding and Q3's
/// target walk (the <see cref="StaticQueryProjection.Receiver"/> projection: through transparent references, a carrier
/// itself, no static identity for a runtime reference).
/// </summary>
internal sealed partial class StaticStructureQueries
{
    /// <summary>
    /// Whether the admission of this operation met a declaration carrying the output-spreading marker
    /// (<see cref="StaticStructureOperation.AdmittedWithOutputSpreadMarkers"/>): only then is any edge examined, so a
    /// program without markers is read exactly as before, query for query.
    /// </summary>
    internal bool AdmittedWithOutputSpreadMarkers { get; set; }

    /// <summary>
    /// What <see cref="LoweredReceiver"/> found: the marker of the declaration the receiver call invokes (the edge is
    /// lowered), nothing (the edge stays an edge), or <see cref="IsUnknown"/> while a fact it reads is still undecided.
    /// </summary>
    internal readonly record struct LoweredReceiverVerdict(OutputSpreadMarker? Marker, bool IsUnknown);

    /// <summary>
    /// Whether <paramref name="edge"/> is a MARKED EXTENSION EDGE in <paramref name="scope"/>: its miss is certain and
    /// selects the lexical fallback (no <c>string</c>/<c>Invoke</c>/<c>Arguments</c>/<c>Algorithm</c> intrinsic), and its
    /// receiver is a written call whose callee resolves statically to a marked declaration (<see cref="ReceiverCallee"/>).
    /// Inside an equation it reads through <paramref name="reader"/> and reports an undecided fact as unknown; at the
    /// consumer boundary (<paramref name="reader"/> null) every fact is final.
    /// </summary>
    internal LoweredReceiverVerdict LoweredReceiver(StaticScopeKey scope, Expr.DotCall edge,
        StaticQueryReader<StaticQueryKey, StaticFact>? reader = null)
    {
        if (!AdmittedWithOutputSpreadMarkers || edge.UsesDotMissIntrinsic()
            || edge.Target.UnwrapGraceOperand() is not (Expr.Call or Expr.DotCall))
            return default;
        var selection = ReadFact(StaticQueryKey.MissSelection(scope, edge), reader);
        if (selection.IsUnknown) return new(null, IsUnknown: true);
        if (selection.Kind != StaticFactKind.Always) return default;
        var callee = ReceiverCallee(scope, edge.Target.UnwrapGraceOperand(), reader);
        if (callee.IsUnknown) return new(null, IsUnknown: true);
        return callee.Kind == StaticFactKind.Structure && callee.Scope is { } declaration
            ? new(ContextOf(declaration).Body.OutputSpread, IsUnknown: false)
            : default;
    }

    /// <summary>
    /// The STRUCTURAL identity of the declaration the written call <paramref name="call"/> invokes (R1), as a Q3 fact:
    /// <c>N(args)</c> and <c>(Path.N)(args)</c> by their callee; a structural member call <c>Path.N(args)</c> by its
    /// member; an extension call <c>x.N(args)</c> / <c>x.N</c> (the call <c>N(x, args)</c>, DOT-03) by its lexical
    /// fallback. Every other expression — an argumentless structural member (a READ), an intrinsic edge, an edge a
    /// runtime receiver decides, a callee that is no name or path — invokes no static declaration.
    /// </summary>
    private StaticFact ReceiverCallee(StaticScopeKey scope, Expr call, StaticQueryReader<StaticQueryKey, StaticFact>? reader)
    {
        switch (call)
        {
            case Expr.Call { Function: var function }:
                return function.UnwrapGraceOperand() is Expr.Resolve or Expr.DotCall { Args: null }
                    ? ReadFact(Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.Receiver, node: function.UnwrapGraceOperand()), reader)
                    : StaticFact.Missing;

            case Expr.DotCall inner:
            {
                var selection = ReadFact(StaticQueryKey.MissSelection(scope, inner), reader);
                if (selection.IsUnknown) return selection;
                if (selection.Kind == StaticFactKind.Always)
                {
                    return !inner.UsesDotMissIntrinsic() && inner.EffectiveLexicalFallback.UnwrapGraceOperand() is Expr.Resolve fallback
                        ? ReadFact(Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.Receiver, node: fallback), reader)
                        : StaticFact.Missing;
                }

                if (selection.Kind != StaticFactKind.Never || inner.Args is null) return StaticFact.Missing;
                // The member step of the Receiver projection, for an edge that carries arguments (the projection reads
                // argumentless paths only): the receiver's structure, its declared member, that member's target walk.
                var receiver = ReadFact(Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.Receiver, node: inner.Target), reader);
                if (receiver.IsUnknown) return receiver;
                if (receiver.Kind != StaticFactKind.Structure) return StaticFact.Missing;
                var members = ReadFact(StaticQueryKey.Members(receiver.Scope!), reader);
                if (members.IsUnknown) return members;
                if (((StaticMembers)members.Data!).Declared(inner.Name) is not { } member) return StaticFact.Missing;
                var target = BodyIn(receiver.Scope!, member.Value);
                var reached = ReadFact(StaticQueryKey.TargetWalk(target, StaticCycleCheck.Formation), reader);
                return reached.Kind == StaticFactKind.Refused ? new(StaticFactKind.Structure, target) : reached;
            }

            default:
                return StaticFact.Missing;
        }
    }

    private StaticFact ReadFact(StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact>? reader)
        => reader is null ? Get(key) : reader.Read(key);
}
