namespace KatLang;

internal static partial class ImplicitArgumentResolver
{
    /// <summary>Rebuilds Q8's physical views over final eager publications; no eager loop, map or operation is retained.</summary>
    internal static Algorithm ElaborateStructuralDeferredBranch(Algorithm detectedBody, StaticStructureDeferredContext context,
        StaticStructureOperation operation, DiagnosticBag diagnostics, FrontEndTraversalObservations? observations,
        SourceSpan? importSite, ModuleUnits modules)
    {
        var run = new ResolutionRun(operation, importSite)
        {
            Observations = observations,
            Prelude = PreludeContext.For(null, (Algorithm.User)operation.SourceOf(operation.Queries.Keys.Root)),
            Owners = operation.OwnersOf(context.Declaring),
            Level = operation.ResolverLevel(context.Declaring),
            Diagnostics = diagnostics,
            Modules = modules,
        };
        var map = CompletedSignatureMap(context.Declaring, run);
        var forwardable = (context.Forwardable ?? throw new InvalidOperationException("Deferred structure has no Q8 binding context."))
            .Rebase(run.ReferenceNameSets);
        var branch = new ConditionalBranchContext(context.BranchName, context.Pattern);

        // B3-5★: the branch's own bodies are selected before any of them is rewritten (every eager signature it reads is
        // final already). A refusal publishes nothing; the caller takes A1's recovery route over the detected body.
        run.Selected = SelectSignatures(detectedBody, map, forwardable, isRoot: false, branch, run);
        if (!run.Selected.Succeeded)
        {
            ReportRefusedSelection(run.Selected, run);
            run.ReleaseLevels();
            return detectedBody;
        }

        var resolved = ProcessAlgorithm(detectedBody, map, forwardable, isRoot: false, observations, diagnostics, branch, run);
        run.CompletePendingTargets();
        run.CommitDeferredChecks();
        RequireEveryAnalyzedBodyRewritten(run);
        run.ReleaseLevels();
        // A branch this unit defers again was resolved provisionally (ResolveProvisionalBranch): no completed fact.
        operation.RetractProvisionalResolutions();
        operation.CompleteLookups(resolved);
        return resolved;
    }

    private static SignatureMap CompletedSignatureMap(StaticScopeKey declaring, ResolutionRun run)
    {
        var operation = run.StructuralOperation;
        var chain = new Stack<StaticScopeKey>();
        for (var at = declaring; !ReferenceEquals(at, operation.Queries.Keys.Root); at = at.Parent!) chain.Push(at);
        // These are views of completed Q8 publications, not structural decisions. Canonicalize only the names
        // actually read so repeated signatures retain their identity without copying W outer entries per fork.
        var selected = new Dictionary<string, VisibleProperty?>(StringComparer.Ordinal);
        var map = SignatureMap.CompletedExternal(name =>
        {
            if (selected.TryGetValue(name, out var entry)) return entry;
            var binding = operation.Binding(declaring, name, StaticQueryProjection.OwnedBinding);
            if (binding.Kind == StaticFactKind.Declaration && !ReferenceEquals(binding.Scope, operation.Queries.Keys.Root))
            {
                var key = operation.ContextOf(binding.Scope!, binding.Property!.Value);
                var value = operation.Published(key, StaticPublicationStage.Resolved)
                    ?? operation.DetectedView(key) ?? operation.SourceOf(key);
                entry = new(CallableSignature.FromAlgorithm(name, value), value, operation.OwnersOf(binding.Scope!))
                    { Level = operation.ResolverLevel(binding.Scope!) };
            }
            selected[name] = entry;
            return entry;
        }, run.Observations);
        while (chain.TryPop(out var key))
        {
            var body = operation.DetectedView(key) ?? operation.SourceOf(key);
            if (body.Opens.Count != 0)
                map.AttachOpens();
        }
        return map;
    }

    /// <summary>
    /// THE PROVISIONAL RESOLUTION OF A DEFERRED BRANCH (owner decision 2026-11-16: resolve the provisional body, classify
    /// from it, refuse exactly the uncharged). A branch that loads a module on demand is elaborated eagerly only
    /// PROVISIONALLY (B2c): detection already made its binder and ancestor-parameter references parameter reads, with its
    /// diagnostics withheld. This is the same step for implicit arguments: the provisional body is analyzed, selected and
    /// rewritten exactly as any other branch body, AS IF THE MODULES IT LOADS ON DEMAND WERE EMPTY. Nothing here decides
    /// what such a module would supply: its load directives are the opaque source constructs they are in every unelaborated
    /// tree (MOD-07; the whole-document form of this state is a missing module, FrontEndPipeline.FinalizeElaboration), so
    /// a name only the module could bind stays exactly as detection left it, and every reference the owner walk, the
    /// prelude or an open of a known provider at any level decides is lifted and forwarded as in an eager branch. The
    /// enclosing declarations' exposure is then classified from a body that holds those forwardings
    /// (<c>PropertyExposureResolver.ProvisionalFamilyContribution</c>), so a materialized body can require an enclosing
    /// binding the classification did not charge only where the module changed what a reference denotes or needs.
    /// <para>ITS OWN SELECTION (B3-5★). The body is selected on its own, after the selection of the resolution around it
    /// (<see cref="SelectedSignatures.Enclosing"/>): a branch body is closed, so no signature outside it depends on a
    /// body inside it, and a group the selector refuses here is the provisional body's alone. Such a refusal is not a
    /// program's error (the module may supply what the group lacks): nothing is reported, the body stays the detected one
    /// (A1's recovery route), and its forwardings are then not charged, which can only refuse its materialization, never
    /// admit a wrong one. The region placed in the tree RECORDS that its provisional body was left unresolved, with the
    /// names of the refused bodies (<see cref="LeftUnresolved"/>), so that such a refusal is not worded as a module's
    /// doing. THE REACH INVARIANT and THE SELECTION INVARIANT hold of this selection as of any other.</para>
    /// <para>NOTHING IS REPORTED. The rewrite runs with no diagnostics sink, as provisional detection does: every
    /// diagnostic of the body is the materialization's, made against the real module members. The region memo keys
    /// the provisional mode (<see cref="AlgorithmRegionKey"/>), so no body processed here is ever served to a reach
    /// outside a provisional resolution, and no branch report is replayed from here.</para>
    /// <para>PUBLICATION. PROVISIONAL FACTS ARE NOT COMPLETED FACTS (B3-2★). The resolved body lives in the TREE: it is
    /// the placeholder's body, carrying <paramref name="region"/>, this pass's fork of the region, and it is what the
    /// exposure summary channel and the editor read. In the operation its resolved views exist only while the run that
    /// made them needs them (the reach check, alias targets, structure cells): the whole resolution runs inside
    /// <see cref="StaticStructureOperation.EnterProvisionalResolution"/>, and the run retracts them before the completed
    /// lookup facts are built (<see cref="StaticStructureOperation.RetractProvisionalResolutions"/>). WHAT IS RETRACTED
    /// is exactly what could hand a provisional view to a later reader: the resolved publications first made inside
    /// the resolution (with their source-to-resolved-view entries) and the region aliases recorded inside it. WHAT
    /// STAYS in the operation is the view-to-source entries of the provisional bodies (keyed by the view, so they serve
    /// only a caller that already holds one, as the tree does), the structure cells created or completed from a
    /// provisional view (read after the run only for contexts that still hold a resolved view), and the ledger
    /// charges, which are cumulative by policy. So the completed lookup facts are built from the placeholder's
    /// DETECTED view, the frozen continuation holds no provisional publication, view, alias or cell, and no
    /// materialization can observe one (the field comment in <c>StaticStructureOperation</c> gives the reader-by-reader
    /// argument). A materialization admits its unit under a fresh region key
    /// (<c>StaticStructureQueries.MaterializedBranchIn</c>) and elaborates it from the loaded source; a block written
    /// as an open target is keyed at the root level in the placeholder and in the materialized body alike, which is
    /// why the provisional views must not survive into the continuation.</para>
    /// </summary>
    private static Algorithm ResolveProvisionalBranch(
        Algorithm.Conditional family,
        StaticScopeKey familyKey,
        int index,
        DeferredModuleRegion region,
        string propertyName,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        FrontEndTraversalObservations? observations,
        ResolutionRun run)
    {
        var operation = run.StructuralOperation;
        var branch = family.Branches[index];
        // This pass's view of the placeholder: the detected provisional body carrying this pass's fork of its region. The
        // tree's detected placeholder is a copy of detection's published view (it carries detection's fork), so the view is
        // registered against the admitted source placeholder: the same branch of the family as the operation admitted it.
        var body = branch.Body with { DeferredRegion = region };
        if (operation.SourceOf(familyKey) is not Algorithm.Conditional admitted || admitted.Branches.Count != family.Branches.Count)
            throw new InvalidOperationException("Internal error: a deferred branch's family has no admitted source of the same shape.");
        var declaring = run.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root;
        var placeholder = operation.ContextOf(declaring, admitted.Branches[index].Body, branch.Pattern);
        operation.RegisterView(placeholder, body);

        var context = new ConditionalBranchContext(propertyName, branch.Pattern);
        var enclosing = run.Selected ?? throw new InvalidOperationException(
            "Internal error: a deferred branch was reached before its resolution selected the signatures.");
        using var provisional = operation.EnterProvisionalResolution();
        var selected = SelectSignatures(body, parentParamMap, forwardable, isRoot: false, context, run);
        if (!selected.Succeeded)
            return LeftUnresolved(body, region, selected, placeholder, run);

        run.Selected = selected;
        run.ProvisionalResolutions++;
        try
        {
            var resolved = ProcessAlgorithm(body, parentParamMap, forwardable, isRoot: false, observations, diagnostics: null, context, run);
            RequireEveryAnalyzedBodyRewritten(run);
            if (!ReferenceEquals(resolved.DeferredRegion, region))
                throw new InvalidOperationException("Internal error: a deferred branch's resolved provisional body lost its region.");
            return resolved;
        }
        finally
        {
            run.ProvisionalResolutions--;
            run.Selected = enclosing;
        }
    }

    /// <summary>
    /// The placeholder body of a deferred branch whose PROVISIONAL SELECTION WAS REFUSED: the detected body, unrewritten
    /// (A1's recovery route), carrying a fork of <paramref name="region"/> that RECORDS the fact where it is decided
    /// (<see cref="StaticStructureDeferredContext.UnresolvedProvisionalBodies"/>: the names of the refused bodies, distinct,
    /// in first-occurrence order). None of the body's forwardings is charged to its family, so its materialization can be
    /// refused for a forwarding to the program's OWN callable, and the refusal then must not blame a module for it
    /// (<c>DeferredModuleRegion.ReportUnchargedEnclosingParameters</c> words it from this record). The record decides
    /// nothing, and nothing is reported here: the refused group is not a program's error.
    /// <para>The fact rides the region the TREE holds, like every other context of the occurrence: every later fork copies
    /// it (<see cref="DeferredModuleRegion.WithExposure"/>), and a placeholder met inside a materialization's run gets its
    /// own from that run. No side table, and no region already placed in a tree is changed: the body returned is a new
    /// view of the admitted placeholder, registered like the one the selection analyzed
    /// (<see cref="StaticStructureOperation.RegisterView"/>), which stays a view of the same source.</para>
    /// </summary>
    private static Algorithm LeftUnresolved(
        Algorithm body, DeferredModuleRegion region, SelectedSignatures selected, StaticScopeKey placeholder, ResolutionRun run)
    {
        var structural = region.Structure
            ?? throw new InvalidOperationException("Internal error: a deferred branch's region lost its structural context.");
        var names = new List<string>();
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var bodies = 0L;
        foreach (var (refused, _, _) in selected.Refusals)
        {
            bodies += refused.Count;
            foreach (var refusedBody in refused)
            {
                if (seen.Add(refusedBody.Name))
                    names.Add(refusedBody.Name);
            }
        }

        if (names.Count == 0)
            throw new InvalidOperationException("Internal error: a refused signature selection names no body.");
        var operation = run.StructuralOperation;
        // Retained with the tree: one reference per distinct name (eight to a 64-byte ledger slot) and the array header.
        operation.Queries.Resources.Metadata(1 + (names.Count + 7L) / 8, work: bodies, cancellationToken: run.CancellationToken);
        var unresolved = body with
        {
            DeferredRegion = region.WithStructure(structural with { UnresolvedProvisionalBodies = names.ToArray() }),
        };
        operation.RegisterView(placeholder, unresolved);
        return unresolved;
    }

    /// <summary>
    /// One reference of a materialized deferred branch whose synthesized call passes an ENCLOSING parameter binding: the
    /// callee as written (<c>X</c>, <c>M.X</c>, an in-branch alias <c>P</c>; null when it has no spelling as a name
    /// path, a block-headed path <c>{ … }.K</c>), the explicit call that passes the same arguments (<c>X(y)</c>; null
    /// without a callee spelling or when an argument has no simple spelling), and the reference's span (null inside
    /// imported content, which carries no location).
    /// </summary>
    internal readonly record struct EnclosingForward(string? Callee, string? ExplicitCall, SourceSpan? Span);

    /// <summary>
    /// WHERE A REFUSED MATERIALIZATION IS REPORTED (<see cref="DiagnosticCode.DeferredBranchForwardsEnclosingParameter"/>):
    /// for each name of <paramref name="parameters"/>, the first reference of <paramref name="resolvedBody"/> in source
    /// order whose call passes a binding of that name from OUTSIDE the branch's family, whatever the callee. A POSITION
    /// ONLY: the refusal is decided before this is asked, by the comparison of the body's contribution with its family's
    /// (<c>PropertyExposureResolver.UnchargedByFamily</c>), and a name this finds no reference for is reported at the
    /// region's site instead. It re-encodes no lookup: it reads the calls this pass just synthesized, with no table kept
    /// on the tree or by the run. Every such call keeps its reference's own call node and span
    /// (<see cref="RewriteBareReference"/>, the structural-member arm of <see cref="RewriteDotCall"/>, bare forwarding in
    /// <see cref="TryCompleteLoneCalleeRow"/>), and its synthesized arguments are plain reads of the bindings it forwards.
    /// <para>A name is OUTSIDE the family where no owner between the reference and the body's root rebinds it: the
    /// branch's pattern binders (<paramref name="branchPattern"/>), and the parameters and declared properties of every
    /// body on the way, bind the nearer declaration (Q-04, ownership first). The caller asks only for names the family's
    /// eager classification never charged, so no WRITTEN read of such a binding exists in the body (the provisional body
    /// would have charged it): every free argument read found is a forwarded one.</para>
    /// <para>Called only for a refused materialization, so every other program pays nothing. Iterative and
    /// reference-deduplicated: work is linear in the body's distinct nodes. A loaded module's root is not entered (it is
    /// hygienic, Q-31: no site binding reaches it), nor a nested branch that still waits for its own modules (its body
    /// is provisional and is judged when it loads).</para>
    /// </summary>
    internal static Dictionary<string, EnclosingForward> FindEnclosingForwards(
        Algorithm resolvedBody, Pattern branchPattern, IReadOnlySet<string> parameters)
    {
        var found = new Dictionary<string, EnclosingForward>(StringComparer.Ordinal);
        var visited = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<(object Node, BodyLevel? Level)>();
        var binders = branchPattern.BoundNames();
        pending.Push((resolvedBody, binders.Count == 0 ? null : new BodyLevel(new HashSet<string>(binders, StringComparer.Ordinal), null)));
        while (pending.TryPop(out var item))
        {
            var (node, level) = item;
            if (!visited.Add(node))
                continue;

            switch (node)
            {
                case Algorithm { IsModuleRoot: true } or Algorithm.Builtin:
                    continue;

                // A nested branch that waits for its own modules; the materialized body itself is the unit judged here.
                case Algorithm { DeferredRegion: not null } when !ReferenceEquals(node, resolvedBody):
                    continue;

                case Algorithm.Conditional family:
                    foreach (var branch in family.Branches)
                    {
                        var bound = branch.Pattern.BoundNames();
                        pending.Push((branch.Body, bound.Count == 0 ? level : new BodyLevel(new HashSet<string>(bound, StringComparer.Ordinal), level)));
                    }

                    continue;

                case Algorithm body:
                {
                    var own = new HashSet<string>(StringComparer.Ordinal);
                    foreach (var capture in ParameterPattern.CapturesExpandingSharedNodesOnce(body.ParameterPatterns))
                        own.Add(capture.Name);
                    foreach (var property in body.Properties)
                        own.Add(property.Name);
                    var inside = own.Count == 0 ? level : new BodyLevel(own, level);
                    foreach (var property in body.Properties)
                        pending.Push((property.Value, inside));
                    foreach (var row in body.Output)
                        pending.Push((row, inside));
                    continue;
                }

                case Expr.Call call:
                    NoteForwards(call, call.Function, call.Args, level, parameters, found);
                    break;

                case Expr.DotCall { Args: { } arguments } edge:
                    NoteForwards(edge, edge, arguments, level, parameters, found);
                    break;
            }

            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push((child, level));
        }

        return found;
    }

    /// <summary>
    /// The names one owner between a reference and the materialized body's root binds, innermost first: a body of the
    /// branch (its parameters and its declared properties), or a clause pattern's binders.
    /// </summary>
    private sealed class BodyLevel(IReadOnlySet<string> names, BodyLevel? outer)
    {
        /// <summary>Whether one of the branch's own owners, from this level outward, binds <paramref name="name"/>.</summary>
        public bool Binds(string name)
        {
            for (var at = this; at is not null; at = at.Outer)
                if (at.Names.Contains(name))
                    return true;
            return false;
        }

        private BodyLevel? Outer => outer;

        private IReadOnlySet<string> Names => names;
    }

    // Records the call as the first forward of every wanted name one of its arguments reads free: an argument that is
    // the binding itself, its re-spread, or a structure rebuilt around it (FWD-02: BuildPatternArgument). A callee with
    // no spelling as a name path still positions the report; only its wording names no reference.
    private static void NoteForwards(Expr call, Expr callee, OutputBundle arguments, BodyLevel? level,
        IReadOnlySet<string> parameters, Dictionary<string, EnclosingForward> found)
    {
        EnclosingForward? forward = null;
        var slots = new Stack<Expr>();
        for (var index = arguments.Count - 1; index >= 0; index--)
            slots.Push(arguments[index]);
        while (slots.TryPop(out var slot))
        {
            switch (slot)
            {
                case Expr.Param(var name) when parameters.Contains(name) && level?.Binds(name) != true:
                    if (forward is null)
                    {
                        var written = WrittenCallee(callee);
                        forward = new EnclosingForward(written, written is null ? null : ExplicitCall(written, arguments), call.Span);
                    }

                    if (!found.TryGetValue(name, out var earlier) || Precedes(forward.Value.Span, earlier.Span))
                        found[name] = forward.Value;
                    break;
                case Expr.SequenceSpread(var operand):
                    slots.Push(operand);
                    break;
                case Expr.ListLiteral(var items):
                    foreach (var element in items)
                        slots.Push(element);
                    break;
                case Expr.Capture(var rows):
                    foreach (var row in rows)
                        slots.Push(row);
                    break;
            }
        }
    }

    // Source order: a located reference before an unlocated one, then by start position.
    private static bool Precedes(SourceSpan? candidate, SourceSpan? earlier)
        => candidate is { } span && (earlier is not { } known || span.Start.CompareTo(known.Start) < 0);

    // A callee as it is written: a name, or a member path over one (the lifted edge itself for a dotted callee).
    private static string? WrittenCallee(Expr callee)
    {
        var steps = new Stack<string>();
        for (var at = callee.UnwrapGraceOperand(); ; )
        {
            switch (at)
            {
                case Expr.Resolve(var name):
                    steps.Push(name);
                    return string.Join(".", steps);
                case Expr.DotCall edge:
                    steps.Push(edge.Name);
                    at = edge.Target.UnwrapGraceOperand();
                    continue;
                default:
                    return null;
            }
        }
    }

    // The written call that passes the same arguments, when every argument has a simple spelling.
    private static string? ExplicitCall(string callee, OutputBundle arguments)
    {
        var slots = new List<string>(arguments.Count);
        foreach (var argument in arguments)
        {
            if (ArgumentSpelling(argument) is not { } spelling)
                return null;
            slots.Add(spelling);
        }

        return $"{callee}({string.Join(", ", slots)})";
    }

    private static string? ArgumentSpelling(Expr argument) => argument switch
    {
        Expr.Param(var name) => name,
        Expr.SequenceSpread(Expr.Param(var name)) => name + "*",
        _ => null,
    };
}
