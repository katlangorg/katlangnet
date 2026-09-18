namespace KatLang;

/// <summary>
/// Diagnostic-only origin of one implicit parameter inferred from an
/// unresolved identifier. This is deliberately internal: public AST and
/// structured-error consumers need the ordinary parameter/error payloads,
/// while only KatLang's diagnostic renderer consumes this implementation
/// metadata.
///
/// <para><b>Identity and sharing.</b> ONE note is ONE promotion: the moment a
/// detection run over one body first promotes an unresolved name
/// (<c>ParameterDetector.ImplicitParameterOccurrenceRecorder</c>), in one
/// front-end context. Every record that stands for that promotion references
/// the SAME note object: the inferred capture, the declarations flattened from
/// it, every caller signature implicit argument resolution lifts that very
/// capture into, the dot edge whose fallback occurrence caused the promotion
/// (<see cref="Expr.DotCall.InferredFallbackProvenance"/>), and the error
/// snapshots the evaluator takes from a callee's parameters. Each carrier holds
/// the reference in an equality-transparent <c>RuntimeStateSlot</c>, so a
/// <c>with</c> copy is one more view of the same note and record equality never
/// sees it. Nothing ever forks a note: a body elaborated again in another
/// context (a module spliced under a second owner, a deferred branch
/// materialized, a re-detected host tree) is a new promotion with a new note,
/// which is why an independent context can reach an independent verdict.</para>
///
/// <para><b>Mutation.</b> <see cref="Name"/> and <see cref="Span"/> are fixed
/// at promotion. The receiver-aware half — <see cref="DotMemberOrigin"/> and the
/// suggestion — is finalized IN PLACE
/// by <see cref="DotMemberProvenanceFinalizer"/>, the one walk that runs after
/// exposure completion (once per pipeline run; a deferred materialization is
/// its own run over the notes it minted), through the two named operations
/// below and nothing else; because the note is shared, the verdict reaches every view
/// (every lifted caller included) without rewriting any executable node. The
/// finalizer runs before its tree is published — inside the synchronous front
/// end, or inside a deferred region's gated materialization over notes that
/// materialization itself minted — and evaluation only reads, so no note is
/// ever mutated concurrently.</para>
/// </summary>
internal sealed class ImplicitParameterProvenance
{
    internal ImplicitParameterProvenance(
        string name,
        SourceSpan? span,
        NameSuggestion? suggestion,
        DotMemberFallbackOrigin? dotMemberOrigin = null)
    {
        Name = name;
        Span = span;
        Suggestion = suggestion;
        DotMemberOrigin = dotMemberOrigin;
    }

    internal string Name { get; }

    /// <summary>
    /// The first semantic source occurrence of the promoted name, or null when that
    /// occurrence lies in imported module content — an import view carries no source
    /// locations (see <see cref="ImportSite"/>) — so a report about the promotion is
    /// positioned and worded from the current document alone.
    /// </summary>
    internal SourceSpan? Span { get; }

    /// <summary>
    /// The conservative suggestion after any source-defined property involved
    /// in it has received its final exposure classification. Before that
    /// classification, an exposure-dependent suggestion is suppressed. A
    /// receiver-member suggestion is already spelled with its receiver
    /// (<c>Math.Ceil</c>); a lexical suggestion is the bare name.
    /// </summary>
    internal string? SuggestedName => Suggestion?.EligibleName;

    /// <summary>
    /// Present when the promoted name was the member of a dot edge whose
    /// receiver is statically known and provably lacks that member, so the
    /// edge's lexical fallback was the selected resolution and its unresolved
    /// callable name became this parameter. Diagnostic-only provenance: it
    /// records what resolution already decided and never alters it —
    /// <c>Math.Ceiling(2.1)</c> keeps falling back exactly like a receiver the
    /// front end cannot inspect. <c>null</c> for bare-name occurrences and for
    /// runtime-valued or unresolved receivers, where the member may exist.
    /// </summary>
    internal DotMemberFallbackOrigin? DotMemberOrigin { get; private set; }

    private NameSuggestion? Suggestion { get; set; }

    /// <summary>
    /// Ownership completion can replace an opened receiver with a captured
    /// parameter. Drop the now-unproven report on this shared note, including
    /// copies lifted into callers; no executable node or signature changes.
    /// </summary>
    internal void ForgetDotMemberOrigin()
    {
        DotMemberOrigin = null;
        Suggestion = null;
    }

    internal void ConfirmDotMemberReceiver(Algorithm receiver)
        => Suggestion = Suggestion?.RestrictToReceiver(receiver);

    internal static IReadOnlyList<ImplicitParameterProvenance>? CollectFrom(
        IReadOnlyList<ParameterDeclaration> parameters)
    {
        List<ImplicitParameterProvenance>? notes = null;
        foreach (var parameter in parameters)
        {
            if (parameter.InferredProvenance is { } provenance)
                (notes ??= []).Add(provenance);
        }

        return notes;
    }
}

/// <summary>
/// The receiver-aware half of an implicit parameter's provenance: the dot
/// edge's statically known receiver, as the same diagnostic spelling the
/// evaluator's dot-call context renders (<c>Math</c>, <c>Lib.Sub</c>,
/// <c>(inline library)</c>). The member name is the provenance's own
/// <see cref="ImplicitParameterProvenance.Name"/> and the member token its
/// <see cref="ImplicitParameterProvenance.Span"/>.
/// </summary>
internal sealed record DotMemberFallbackOrigin(string ReceiverDescription);

/// <summary>
/// A ranked suggestion. Eligibility never depends on exposure: an opened or
/// structural name is selected by visibility alone, and a local-only member the
/// site may not use is reported at the access, never hidden from suggestions.
/// A receiver-member suggestion carries the receiver spelling it is written
/// after (<c>Math</c> for <c>Math.Ceil</c>) when that spelling is a dotted
/// name path the user can write; a lexical suggestion carries none.
/// </summary>
internal sealed class NameSuggestion
{
    internal NameSuggestion(string name, string? receiverQualifier = null, bool isReceiverMember = false)
    {
        Name = name;
        ReceiverQualifier = receiverQualifier;
        IsReceiverMember = isReceiverMember;
    }

    private string Name { get; }

    private string? ReceiverQualifier { get; }

    private bool IsReceiverMember { get; }

    // A completed owner may select a different receiver than the one the note
    // was recorded against. A spelling from that former receiver must also be a
    // declared member of the finally selected one (declared, not exported: the
    // structural surface selects by declaration).
    internal NameSuggestion? RestrictToReceiver(Algorithm receiver)
    {
        if (!IsReceiverMember)
            return receiver.Properties.Count == 0 ? this : null;

        return ElaboratedScopeLookup.TryLookupProperty(receiver, Name) is not null
            ? new NameSuggestion(Name, ReceiverQualifier, isReceiverMember: true)
            : null;
    }

    internal string EligibleName
        => ReceiverQualifier is null ? Name : $"{ReceiverQualifier}.{Name}";
}

/// <summary>
/// Revalidates only diagnostic metadata against the completed tree. A final
/// owner may bind a former opened receiver as a parameter, or exposure may
/// reveal a different opened provider. First-occurrence notes are shared with
/// lifted captures, so invalidation reaches every caller without changing any
/// executable node. Reads each dot edge's own carried note
/// (<see cref="Expr.DotCall.InferredFallbackProvenance"/>) — the ONE place a
/// note is mutated — and rewrites nothing. Scope/node identity bounds
/// shared-DAG traversal.
/// </summary>
internal sealed class DotMemberProvenanceFinalizer(ElaboratedPropertyScope parentScope) : AstWalker
{
    private ElaboratedPropertyScope _scope = parentScope;
    private readonly Dictionary<ElaboratedPropertyScope, HashSet<object>> _visited = new(ReferenceEqualityComparer.Instance);

    protected override bool VisitsExplicitParameterDeclarations => false;

    private bool Enter(object node)
    {
        if (!_visited.TryGetValue(_scope, out var nodes))
            _visited[_scope] = nodes = new(ReferenceEqualityComparer.Instance);
        return nodes.Add(node);
    }

    public override void VisitAlgorithm(Algorithm algorithm)
    {
        var previousScope = _scope;
        if (algorithm.DeferredRegion is not null || !Enter(algorithm))
            return;
        // Parameters already have Param identity. A level with no declarations
        // cannot change receiver lookup and need not split the diagnostic region.
        if (algorithm.Properties.Count != 0 || algorithm.Opens.Count != 0)
            _scope = ElaboratedScopeLookup.CreateScope(algorithm, _scope);
        base.VisitAlgorithm(algorithm);
        _scope = previousScope;
    }

    public override void VisitPattern(Pattern pattern) { }

    protected override void VisitProperty(Property property) => VisitAlgorithm(property.Value);

    protected override void VisitOpenExpression(Expr expression)
    {
        var previous = _scope;
        _scope = _scope.Root;
        base.VisitOpenExpression(expression);
        _scope = previous;
    }

    public override void VisitExpr(Expr expr)
    {
        if (!Enter(expr))
            return;
        if (expr is Expr.DotCall { InferredFallbackProvenance: { DotMemberOrigin: not null } note } edge)
        {
            var receiver = edge.Target.UnwrapGraceOperand().ResolveStaticStructuralMemberProvider(name =>
            {
                var hits = ElaboratedScopeLookup.LookupLexicalPropertyMatches(_scope, name);
                return hits.Count == 1
                    ? new(StaticStructuralMemberProviderKind.KnownAlgorithm, hits[0].Property.Value)
                    : new StaticStructuralMemberProvider(StaticStructuralMemberProviderKind.LexicalReference);
            });
            if (receiver.Kind != StaticStructuralMemberProviderKind.KnownAlgorithm
                || edge.GetLexicalFallbackSelection(receiver) != LexicalFallbackSelection.Always)
                note.ForgetDotMemberOrigin();
            else
                note.ConfirmDotMemberReceiver(receiver.Algorithm!);
        }
        base.VisitExpr(expr);
    }
}
