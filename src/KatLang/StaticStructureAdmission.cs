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
        var measurement = Measure(root, prelude, sourceProcessingLimits, sourceAncestors, out var sharedNodes, observations: null, cancellationToken);
        return (new(root, measurement.Limits, prelude, phase, cancellationToken)
        {
            SharedBodies = SharedBodyCensus.FromSharedNodes(sharedNodes),
            AdmittedWithoutOpens = !measurement.HasOpens,
            AdmittedWithOutputSpreadMarkers = measurement.HasOutputSpreadMarkers,
        }, measurement);
    }

    internal static Measurement Measure(Algorithm root, Algorithm prelude, SourceProcessingLimits? sourceProcessingLimits = null,
        IReadOnlyList<Algorithm>? sourceAncestors = null, CancellationToken cancellationToken = default)
        => Measure(root, prelude, sourceProcessingLimits, sourceAncestors, out _, observations: null, cancellationToken);

    // `observations` records the walk's edges for a deferred materialization's reference measure (MeasureLoadedBody); null
    // everywhere else, so no other measure is observed.
    private static Measurement Measure(Algorithm root, Algorithm prelude, SourceProcessingLimits? sourceProcessingLimits,
        IReadOnlyList<Algorithm>? sourceAncestors, out HashSet<object>? sharedNodes, FrontEndTraversalObservations? observations,
        CancellationToken cancellationToken)
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
                observations?.RecordDeferredAdmissionEdge();
                if (seen.Contains(child))
                {
                    (sharedNodes ??= new(ReferenceEqualityComparer.Instance)).Add(child);
                    continue;
                }
                if (seen.Count >= maxSourceFacts) throw new StaticQueryLimitExceededException("Static source admission exceeded its memory envelope.");
                seen.Add(child); pending.Push(child);
            }
        }
        return MeasurementOf(seen.Count, edges, graphBytes, hasOpens, hasOutputSpreadMarkers);
    }

    /// <summary>The measurement of an admitted graph of <paramref name="nodes"/> distinct nodes and <paramref name="edges"/> enumerated edges.</summary>
    private static Measurement MeasurementOf(long nodes, long edges, long graphBytes, bool hasOpens, bool hasOutputSpreadMarkers)
    {
        var facts = nodes + edges;
        // The entry bound has two parts, one entry per KiB of the envelope and 4,096 + 128 per admitted node and edge, and
        // is the smaller. Which part that is (the program's only when strictly smaller) selects the refusal's explanation
        // (ProgramScaledEntries); the bound itself is the same either way.
        var envelopeEntries = graphBytes / 1024;
        var programEntries = 4096 + 128 * Math.Min(facts, (long.MaxValue - 4096) / 128);
        var entries = (int)Math.Min(int.MaxValue, Math.Min(envelopeEntries, programEntries));
        var limits = new StaticQueryLimits(16_384 + 1024 * Math.Min(facts, (long.MaxValue - 16_384) / 1024), 4, entries,
            65_536 + 4096 * Math.Min(facts, (long.MaxValue - 65_536) / 4096), graphBytes / 64, ProgramScaledEntries: programEntries < envelopeEntries);
        return new(nodes, edges, graphBytes, limits, hasOpens, hasOutputSpreadMarkers);
    }

    /// <summary>
    /// THE ADMISSION MEASURE OF A DEFERRED MATERIALIZATION'S LOADED BODY: <see cref="Measure(Algorithm, Algorithm, SourceProcessingLimits?, IReadOnlyList{Algorithm}?, CancellationToken)"/>
    /// over <paramref name="root"/> and <paramref name="prelude"/>, with every module view the body splices counted as
    /// one UNIT (<see cref="CompletedModuleViews.AdmissionUnit"/>) instead of walked: the edge that reaches a view is the
    /// body's, the view and everything the measure's walk reaches from it without entering another module view are the
    /// unit's, and a view a unit reaches is a unit of its own, counted once however many views or body nodes reach it. A
    /// view's own nodes are disjoint from every other part (each view is its own parse's import view, spliced by
    /// reference), so the totals — distinct nodes, enumerated edges, the open and output-spreading flags — and therefore
    /// the limits are exactly the ordinary walk's. A unit an earlier materialization published is taken as published;
    /// any other is computed from its view and staged in <paramref name="moduleViews"/>. Whenever the totals reach an
    /// envelope bound, the ordinary walk is replayed, so a refusal is exactly the established one (which bound, which
    /// sentence). The reference mode measures the ordinary way.
    /// </summary>
    internal static Measurement MeasureLoadedBody(Algorithm root, Algorithm prelude, SourceProcessingLimits? sourceProcessingLimits,
        CompletedModuleViews.Attempt? moduleViews, CancellationToken cancellationToken = default)
    {
        // The reference mode walks the ordinary way, its edges observed like the unit walk's.
        if (moduleViews is not { Shares: true })
            return Measure(root, prelude, sourceProcessingLimits, sourceAncestors: null, out _, moduleViews?.Observations, cancellationToken);

        var measurement = MeasureByUnits(root, prelude, sourceProcessingLimits, moduleViews, cancellationToken)
            // A total reached an envelope bound: the ordinary walk refuses exactly as before.
            ?? Measure(root, prelude, sourceProcessingLimits, cancellationToken: cancellationToken);
        if (moduleViews.Verifies)
        {
            var ordinary = Measure(root, prelude, sourceProcessingLimits, cancellationToken: cancellationToken);
            if (ordinary != measurement)
                throw new InvalidOperationException($"The admission measure by module-view units ({measurement}) differs from the ordinary walk ({ordinary}).");
        }

        return measurement;
    }

    /// <summary>The unit-counting measure of <see cref="MeasureLoadedBody"/>; null when a total reaches an envelope bound.</summary>
    private static Measurement? MeasureByUnits(Algorithm root, Algorithm prelude, SourceProcessingLimits? sourceProcessingLimits,
        CompletedModuleViews.Attempt moduleViews, CancellationToken cancellationToken)
    {
        cancellationToken.ThrowIfCancellationRequested();
        var graphBytes = (sourceProcessingLimits ?? SourceProcessingLimits.Default).EffectiveMaxStaticStructureBytes;
        // The ordinary walk admits at most this many distinct nodes and enumerated edges (it refuses the next one).
        var maxNodes = graphBytes / 32;
        var maxEdges = graphBytes / 8;
        var observations = moduleViews.Observations;
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        var units = new Queue<Algorithm.User>();
        seen.Add(root);
        pending.Push(root);
        if (seen.Add(prelude))
            pending.Push(prelude);
        if (seen.Count > maxNodes)
            return null;
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
                if (++edges > maxEdges)
                    return null;
                observations?.RecordDeferredAdmissionEdge();
                if (seen.Contains(child))
                    continue;
                if (seen.Count >= maxNodes)
                    return null;
                seen.Add(child);
                if (CompletedModuleViews.IsModuleView(child, out var view))
                    units.Enqueue(view);
                else
                    pending.Push(child);
            }
        }

        long nodes = seen.Count;
        while (units.TryDequeue(out var view))
        {
            cancellationToken.ThrowIfCancellationRequested();
            if (moduleViews.TryGetUnit(view, out var unit, out var published))
            {
                if (published)
                {
                    observations?.RecordCompletedModuleViewReuse();
                    if (moduleViews.Verifies
                        && ComputeAdmissionUnit(view, long.MaxValue, long.MaxValue, observations: null, cancellationToken) is var walked
                        && (walked is null || !walked.SameAs(unit)))
                        throw new InvalidOperationException("A completed module view's published admission unit differs from the one its view gives.");
                }
            }
            else
            {
                // The unit includes its root, already counted when it was queued.
                unit = ComputeAdmissionUnit(view, maxNodes - nodes + 1, maxEdges - edges, observations, cancellationToken);
                if (unit is null)
                    return null;
                moduleViews.StageUnit(view, unit);
            }

            nodes += unit.Nodes - 1;
            edges += unit.Edges;
            if (nodes > maxNodes || edges > maxEdges)
                return null;
            hasOpens |= unit.HasOpens;
            hasOutputSpreadMarkers |= unit.HasOutputSpreadMarkers;
            foreach (var nested in unit.Nested)
            {
                cancellationToken.ThrowIfCancellationRequested();
                if (!seen.Add(nested))
                    continue;
                if (++nodes > maxNodes)
                    return null;
                units.Enqueue(nested);
            }
        }

        return MeasurementOf(nodes, edges, graphBytes, hasOpens, hasOutputSpreadMarkers);
    }

    /// <summary>
    /// The admission unit of <paramref name="view"/>: the measure's walk from the view, stopping at every other module
    /// view (recorded as nested, never entered), with the walk's own cancellation checks; null as soon as its nodes or
    /// edges exceed what is left of the envelope (<paramref name="nodeAllowance"/>, <paramref name="edgeAllowance"/>).
    /// </summary>
    private static CompletedModuleViews.AdmissionUnit? ComputeAdmissionUnit(Algorithm.User view, long nodeAllowance, long edgeAllowance,
        FrontEndTraversalObservations? observations, CancellationToken cancellationToken)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance) { view };
        var pending = new Stack<object>();
        pending.Push(view);
        if (seen.Count > nodeAllowance)
            return null;
        List<Algorithm.User>? nested = null;
        HashSet<Algorithm.User>? nestedSet = null;
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
                if (++edges > edgeAllowance)
                    return null;
                observations?.RecordDeferredAdmissionEdge();
                if (seen.Contains(child))
                    continue;
                if (CompletedModuleViews.IsModuleView(child, out var inner))
                {
                    if ((nestedSet ??= new(ReferenceEqualityComparer.Instance)).Add(inner))
                        (nested ??= []).Add(inner);
                    continue;
                }

                seen.Add(child);
                if (seen.Count > nodeAllowance)
                    return null;
                pending.Push(child);
            }
        }

        return new(seen.Count, edges, hasOpens, hasOutputSpreadMarkers, nested is null ? [] : nested.ToArray());
    }

    /// <summary>
    /// The refusal names the exhausted counter (the exception's own sentence) and then says what a host can do
    /// (<see cref="StaticQueryLimitExceededException.Bound"/>). For an envelope bound (<see cref="EnvelopeSentence"/>):
    /// the envelope never exceeds <see cref="SourceProcessingLimits.MaxSupportedStaticStructureBytes"/>, and configuration
    /// may only lower it, so the remedy is a smaller program. Source admission's node and edge caps and the ledger's
    /// storage bound are such bounds. The ENTRY bound (<see cref="StaticQueryLimits.MaxEntries"/>) is mixed: the smaller
    /// of an envelope part, one entry per KiB, and a program-scaled part, 4,096 + 128 per admitted node and edge, and its
    /// refusal explains the part that set it. While the envelope part is the smaller, or the two are equal, that is the
    /// envelope sentence. Otherwise (<see cref="StaticQueryLimits.ProgramScaledEntries"/>; under the default envelope,
    /// every program of fewer than 8,160 admitted nodes and edges) the program did not reach the envelope, and
    /// <see cref="ProgramScaledEntryBoundSentence"/> says that no envelope setting raises the bound. It does not say that
    /// none lowers it: a host that lowers the envelope far enough makes the envelope part the smaller. The operation's
    /// WORK bound (<see cref="WorkBoundSentence"/>: 16,384 + 1,024 per admitted node and edge) and READ bound
    /// (<see cref="ReadBoundSentence"/>: 65,536 + 4,096 per admitted node and edge), both <see cref="Measurement.Limits"/>,
    /// do not move with <see cref="SourceProcessingLimits.MaxStaticStructureBytes"/>, so lowering the envelope never
    /// lowers them and the envelope sentence would misstate the remedy. Three limits are constants that neither the
    /// program's size nor any host setting moves: signature selection's enumeration limit
    /// (<see cref="SignatureEnumerationSentence"/>, 2^62 classifications), the per-query REFINEMENT limit
    /// (<see cref="RefinementLimitSentence"/>, four strict changes of one answer; the production fact order,
    /// <see cref="StaticStructureQueries.IsRefinement"/>, changes a fact at most twice, so only a definition of greater
    /// height reaches it), and a namespace certificate's 32-bit record count (<see cref="CertificateStorageSentence"/>,
    /// never reached: <see cref="StaticStructureQueries.NamespaceCertificateTotal"/>). Text only; the kind stays
    /// <see cref="DiagnosticCode.StaticStructureLimitExceeded"/>, the refusal stays unpositioned, and no threshold depends
    /// on which sentence explains it.
    /// </summary>
    internal static Diagnostic Rejection(StaticQueryLimitExceededException error)
        => new($"Static structure analysis exceeded its resource bound. {error.Message} {RemedySentence(error.Bound)}",
            DiagnosticSeverity.Error, null)
        { Code = DiagnosticCode.StaticStructureLimitExceeded };

    private static string RemedySentence(StaticQueryBoundKind bound) => bound switch
    {
        StaticQueryBoundKind.Envelope => EnvelopeSentence,
        StaticQueryBoundKind.Work => WorkBoundSentence,
        StaticQueryBoundKind.Reads => ReadBoundSentence,
        StaticQueryBoundKind.SignatureEnumeration => SignatureEnumerationSentence,
        StaticQueryBoundKind.ProgramScaledEntries => ProgramScaledEntryBoundSentence,
        StaticQueryBoundKind.Refinements => RefinementLimitSentence,
        StaticQueryBoundKind.CertificateStorage => CertificateStorageSentence,
        _ => throw new System.Diagnostics.UnreachableException($"Unknown static query bound kind {bound}."),
    };

    internal const string EnvelopeSentence =
        "The program exceeds the host's static-structure envelope (at most 1 GiB; a host may only lower it).";

    internal const string WorkBoundSentence =
        "This bound scales with the size of the analyzed program (16,384 + 1,024 per node and edge) rather than with the host's static-structure envelope, so no envelope setting raises or lowers it.";

    internal const string ReadBoundSentence =
        "This bound scales with the size of the analyzed program (65,536 + 4,096 per node and edge) rather than with the host's static-structure envelope, so no envelope setting raises or lowers it.";

    internal const string SignatureEnumerationSentence =
        "This limit is fixed: the count doubles with each .Algorithm link classified together, and 2^62 or more is refused whatever the size of the program or the host's static-structure envelope, so no host setting raises or lowers it.";

    internal const string ProgramScaledEntryBoundSentence =
        "This bound scales with the size of the analyzed program (4,096 + 128 per node and edge) and is below what the host's static-structure envelope allows (one entry per KiB), so no envelope setting raises it.";

    internal const string RefinementLimitSentence =
        "This limit is fixed: no static query may refine its answer more often, whatever the size of the program or the host's static-structure envelope, so no host setting raises or lowers it.";

    internal const string CertificateStorageSentence =
        "This limit is fixed: a namespace certificate counts at most 2,147,483,647 records, whatever the size of the program or the host's static-structure envelope, so no host setting raises or lowers it.";
}
