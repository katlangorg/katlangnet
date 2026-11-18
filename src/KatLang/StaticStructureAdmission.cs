namespace KatLang;

/// <summary>Operation admission policy. A resource refusal is terminal and never an inference answer.</summary>
internal static class StaticStructureAdmission
{
    internal readonly record struct Measurement(long Nodes, long Edges, long GraphBytes, StaticQueryLimits Limits, bool HasOpens = true,
        bool HasOutputSpreadMarkers = false);

    internal static (StaticStructureOperation Operation, Measurement Measurement) Create(Algorithm root, HostOperations? hostOperations = null,
        SourceProcessingLimits? sourceProcessingLimits = null, StaticAstPhase phase = StaticAstPhase.RawSource, IReadOnlyList<Algorithm>? sourceAncestors = null, CancellationToken cancellationToken = default)
    {
        var prelude = hostOperations?.SemanticPreludeAlgorithm ?? BuiltinRegistry.SharedSemanticPreludeAlgorithm;
        var measurement = Measure(root, prelude, sourceProcessingLimits, sourceAncestors, out var sharedNodes, cancellationToken);
        return (new(root, measurement.Limits, prelude, phase, cancellationToken)
        {
            SharedBodies = SharedBodyCensus.FromSharedNodes(sharedNodes),
            AdmittedWithoutOpens = !measurement.HasOpens,
            AdmittedWithOutputSpreadMarkers = measurement.HasOutputSpreadMarkers,
        }, measurement);
    }

    internal static Measurement Measure(Algorithm root, Algorithm prelude, SourceProcessingLimits? sourceProcessingLimits = null,
        IReadOnlyList<Algorithm>? sourceAncestors = null, CancellationToken cancellationToken = default)
        => Measure(root, prelude, sourceProcessingLimits, sourceAncestors, out _, cancellationToken);

    private static Measurement Measure(Algorithm root, Algorithm prelude, SourceProcessingLimits? sourceProcessingLimits,
        IReadOnlyList<Algorithm>? sourceAncestors, out HashSet<object>? sharedNodes, CancellationToken cancellationToken)
    {
        sharedNodes = null;
        cancellationToken.ThrowIfCancellationRequested();
        // Immutable explicit policy, never inferred from GC or machine memory. Preserve the
        // conservative 1 KiB/entry and 64-byte ledger slots as well as operation-scaled work.
        // These are accounting bounds, not a promise about total process memory.
        var graphBytes = (sourceProcessingLimits ?? SourceProcessingLimits.Default).EffectiveMaxStaticStructureBytes;
        var maxSourceFacts = graphBytes / 32;
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        seen.Add(root); pending.Push(root);
        if (seen.Add(prelude)) pending.Push(prelude);
        if (sourceAncestors is not null) foreach (var ancestor in sourceAncestors)
        {
            cancellationToken.ThrowIfCancellationRequested();
            if (seen.Contains(ancestor)) continue;
            if (seen.Count >= maxSourceFacts) throw new StaticQueryLimitExceededException("Static source admission exceeded its node-storage envelope.");
            seen.Add(ancestor); pending.Push(ancestor);
        }
        if (seen.Count > maxSourceFacts) throw new StaticQueryLimitExceededException("Static source admission exceeded its node-storage envelope.");
        long edges = 0;
        var hasOpens = false;
        var hasOutputSpreadMarkers = false;
        while (pending.TryPop(out var node))
        {
            cancellationToken.ThrowIfCancellationRequested();
            hasOpens |= node is Algorithm { Opens.Count: > 0 };
            hasOutputSpreadMarkers |= node is Algorithm { OutputSpread: not null };
            for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++)
            {
                cancellationToken.ThrowIfCancellationRequested();
                if (edges >= graphBytes / 8) throw new StaticQueryLimitExceededException("Static source admission exceeded its edge-work envelope.");
                edges++;
                if (seen.Contains(child))
                {
                    (sharedNodes ??= new(ReferenceEqualityComparer.Instance)).Add(child);
                    continue;
                }
                if (seen.Count >= maxSourceFacts) throw new StaticQueryLimitExceededException("Static source admission exceeded its memory envelope.");
                seen.Add(child); pending.Push(child);
            }
        }
        var facts = seen.Count + edges;
        var entries = (int)Math.Min(int.MaxValue, Math.Min(graphBytes / 1024, 4096 + 128 * Math.Min(facts, (long.MaxValue - 4096) / 128)));
        var limits = new StaticQueryLimits(16_384 + 1024 * Math.Min(facts, (long.MaxValue - 16_384) / 1024), 4, entries, 65_536 + 4096 * Math.Min(facts, (long.MaxValue - 65_536) / 4096), graphBytes / 64);
        return new(seen.Count, edges, graphBytes, limits, hasOpens, hasOutputSpreadMarkers);
    }

    /// <summary>
    /// The refusal names the exhausted counter (the exception's own sentence) and then says what a host can do. For an
    /// envelope bound (<see cref="EnvelopeSentence"/>): the envelope never exceeds
    /// <see cref="SourceProcessingLimits.MaxSupportedStaticStructureBytes"/>, and configuration may only lower it, so the
    /// remedy is a smaller program. For the operation's WORK bound (<see cref="WorkBoundSentence"/>): the bound is
    /// 16,384 + 1,024 per admitted node and edge (<see cref="Measurement.Limits"/>)
    /// and does not move with <see cref="SourceProcessingLimits.MaxStaticStructureBytes"/>, so lowering the envelope
    /// never lowers it and the envelope sentence would misstate the remedy. Text only; the kind stays
    /// <see cref="DiagnosticCode.StaticStructureLimitExceeded"/>.
    /// </summary>
    internal static Diagnostic Rejection(StaticQueryLimitExceededException error)
        => new($"Static structure analysis exceeded its resource bound. {error.Message} {(error.IsWorkBound ? WorkBoundSentence : EnvelopeSentence)}",
            DiagnosticSeverity.Error, null)
        { Code = DiagnosticCode.StaticStructureLimitExceeded };

    internal const string EnvelopeSentence =
        "The program exceeds the host's static-structure envelope (at most 1 GiB; a host may only lower it).";

    internal const string WorkBoundSentence =
        "This bound scales with the size of the analyzed program (16,384 + 1,024 per node and edge) rather than with the host's static-structure envelope, so no envelope setting raises or lowers it.";
}
