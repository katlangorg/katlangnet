namespace KatLang;

internal static partial class ImplicitArgumentResolver
{
    /// <summary>Rebuilds Q8's physical views over final eager publications; no eager loop, map or operation is retained.</summary>
    internal static Algorithm ElaborateStructuralDeferredBranch(Algorithm detectedBody, StaticStructureDeferredContext context,
        StaticStructureOperation operation, DiagnosticBag diagnostics, FrontEndTraversalObservations? observations,
        SourceSpan? importSite, ModuleUnits modules)
    {
        var run = new ResolutionRun(importSite, structuralOperation: operation)
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
        run.ReleaseLevels();
        operation.CompleteLookups(resolved);
        return resolved;
    }

    private static SignatureMap CompletedSignatureMap(StaticScopeKey declaring, ResolutionRun run)
    {
        var operation = run.StructuralOperation!;
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
                    ?? operation.Published(key, StaticPublicationStage.Detected) ?? operation.SourceOf(key);
                entry = new(CallableSignature.FromAlgorithm(name, value), value, operation.OwnersOf(binding.Scope!))
                    { Level = operation.ResolverLevel(binding.Scope!) };
            }
            selected[name] = entry;
            return entry;
        }, run.Observations);
        while (chain.TryPop(out var key))
        {
            var body = operation.Published(key, StaticPublicationStage.Detected) ?? operation.SourceOf(key);
            if (body.Opens.Count != 0)
                map.AttachOpens();
        }
        return map;
    }
}
