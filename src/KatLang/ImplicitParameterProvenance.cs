using System.Collections.Frozen;

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
///
/// <para><b>Generated cycle notes (R1).</b> A capture of a recursive completion with no single derivable origin carries a
/// GENERATED note (<see cref="ForCycle"/>) instead of a promotion note: it holds no span and no suggestion, and its
/// <see cref="CycleOrigin"/> names the cycle and the source declarations that supply the name. It is no source
/// declaration, so nothing that asks for one origin can read a root out of it.</para>
///
/// <para><b>Deferred suggestion (FE-1).</b> A promotion captures only the
/// suggestion's candidate context (<see cref="SuggestionQuery"/>, immutable and
/// free of scope chains); the suggestion itself is computed on the first read of
/// <see cref="SuggestedName"/> — when a diagnostic renders it — as the captured
/// query's result with the finalizer's receiver confirmations applied in the
/// order they were made, exactly the value eager computation followed by those
/// in-place operations produced. The first read publishes that pure result
/// atomically, so concurrent first readers compute the same value and the note
/// stays observationally immutable after publication.</para>
/// </summary>
internal sealed class ImplicitParameterProvenance
{
    // The sentinel published when evaluation yields no suggestion.
    private static readonly object NoSuggestion = new();

    private readonly SuggestionQuery? _suggestionQuery;
    private List<FrozenSet<string>>? _confirmedReceivers;
    private bool _suggestionDropped;
    private object? _suggestion;

    internal ImplicitParameterProvenance(
        string name,
        SourceSpan? span,
        SuggestionQuery? suggestion,
        DotMemberFallbackOrigin? dotMemberOrigin = null)
    {
        Name = name;
        Span = span;
        _suggestionQuery = suggestion;
        DotMemberOrigin = dotMemberOrigin;
    }

    /// <summary>The generated note of a capture whose name a recursive cycle shares (see the class documentation).</summary>
    internal static ImplicitParameterProvenance ForCycle(string name, ParameterCycleOrigin origin)
        => new(name, span: null, suggestion: null) { CycleOrigin = origin };

    internal string Name { get; }

    /// <summary>The cycle and its sources, for a generated note; null for a promotion note.</summary>
    internal ParameterCycleOrigin? CycleOrigin { get; private init; }

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
    /// Whether the suggestion has been computed — false until its first read (see the class
    /// documentation), so a front end that renders no diagnostic compares no candidate.
    /// </summary>
    internal bool IsSuggestionEvaluated => Volatile.Read(ref _suggestion) is not null;

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

    private NameSuggestion? Suggestion
    {
        get
        {
            if (Volatile.Read(ref _suggestion) is { } published)
                return published as NameSuggestion;

            NameSuggestion? suggestion = null;
            if (!_suggestionDropped)
            {
                suggestion = _suggestionQuery?.Evaluate();
                if (_confirmedReceivers is not null)
                {
                    foreach (var receiver in _confirmedReceivers)
                        suggestion = suggestion?.RestrictToReceiver(receiver);
                }
            }

            return Interlocked.CompareExchange(ref _suggestion, (object?)suggestion ?? NoSuggestion, null) is { } raced
                ? raced as NameSuggestion
                : suggestion;
        }
    }

    /// <summary>
    /// The finalizer found that the recorded receiver is no longer the statically known
    /// member provider of the completed tree (exposure revealed another provider, or the
    /// fallback is no longer certain). Drop the now-unproven report on this shared note,
    /// including copies lifted into callers; no executable node or signature changes.
    /// </summary>
    internal void ForgetDotMemberOrigin()
    {
        DotMemberOrigin = null;
        _suggestionDropped = true;
        _suggestion = null;
    }

    internal void ConfirmDotMemberReceiver(FrozenSet<string> receiverMembers)
    {
        (_confirmedReceivers ??= []).Add(receiverMembers);
        _suggestion = null;
    }

    /// <summary>
    /// <c>CollectFrom(FlattenCaptures(patterns))</c> — the same notes in the same order — reading
    /// only the captures that carry a provenance: <see cref="CollectFrom(IReadOnlyList{ParameterDeclaration})"/>
    /// skips every other one, so the result is unchanged, while a host-built signature that
    /// shares structural nodes without a provenance-bearing capture is read once per distinct
    /// node instead of once per path (<see cref="ParameterPattern.SelectCapturesSkippingBarrenNodes"/>).
    /// </summary>
    internal static IReadOnlyList<ImplicitParameterProvenance>? CollectFromPatterns(
        IReadOnlyList<ParameterPattern> patterns)
        => CollectFrom(ParameterPattern.SelectCapturesSkippingBarrenNodes(
            patterns, static parameter => parameter.InferredProvenance is not null));

    internal static IReadOnlyList<ImplicitParameterProvenance>? CollectFrom(
        IReadOnlyList<ParameterDeclaration> parameters)
    {
        List<ImplicitParameterProvenance>? notes = null;
        foreach (var parameter in parameters)
        {
            if (parameter.InferredProvenance is not { } provenance)
                continue;
            (notes ??= []).Add(provenance);
            if (provenance.CycleOrigin is not { } cycle)
                continue;
            // A cycle reports every source's promotion: each stays what it is, none stands for the cycle.
            foreach (var root in cycle.Roots)
            {
                if (root.Declaration.InferredProvenance is { } source && !notes.Contains(source))
                    notes.Add(source);
            }
        }

        return notes;
    }
}

/// <summary>
/// The shared origin of a capture in a first-provider cycle of a recursive completion (R1): the cycle's members and the
/// source declarations reachable from it through every active, lifted, non-inert provider. A SET in meaning: the arrays
/// are in canonical order only so that rendering is stable, and <see cref="SameContent"/> ignores order. Immutable.
/// Generated metadata, never a declaration. No root means no source declaration supplies the name to the settled cycle.
/// </summary>
internal sealed class ParameterCycleOrigin(IReadOnlyList<ParameterCycleMember> members, IReadOnlyList<ParameterCycleRoot> roots)
{
    internal IReadOnlyList<ParameterCycleMember> Members { get; } = members;

    internal IReadOnlyList<ParameterCycleRoot> Roots { get; } = roots;

    internal bool SameContent(ParameterCycleOrigin other)
    {
        if (ReferenceEquals(this, other))
            return true;
        if (Members.Count != other.Members.Count || Roots.Count != other.Roots.Count)
            return false;
        var keys = new HashSet<ParameterOriginKey>(Roots.Count);
        foreach (var root in Roots)
            keys.Add(ParameterOriginKey.Of(root.Declaration));
        foreach (var root in other.Roots)
        {
            if (!keys.Contains(ParameterOriginKey.Of(root.Declaration)))
                return false;
        }

        var paths = new HashSet<ParameterCycleMember>(Members);
        return other.Members.All(paths.Contains);
    }
}

/// <summary>One member of a cycle: the names of its declaring bodies and its definition's span.</summary>
internal readonly record struct ParameterCycleMember(string Path, SourceSpan? Span)
{
    internal static readonly Comparison<ParameterCycleMember> RenderOrder = (left, right) =>
    {
        var byPath = string.CompareOrdinal(left.Path, right.Path);
        return byPath != 0 ? byPath : ParameterCycleRoot.ComparePositions(left.Span, right.Span);
    };
}

/// <summary>One source of a cycle: the declaration record, and the callee or body name a report shows it under.</summary>
internal readonly record struct ParameterCycleRoot(ParameterDeclaration Declaration, string Provider)
{
    /// <summary>Where the source is written, or null for locationless module content.</summary>
    internal SourceSpan? Span => Declaration.OriginSpan;

    internal static readonly Comparison<ParameterCycleRoot> RenderOrder = (left, right) =>
    {
        var byPosition = ComparePositions(left.Span, right.Span);
        return byPosition != 0 ? byPosition : string.CompareOrdinal(left.Provider, right.Provider);
    };

    internal static int ComparePositions(SourceSpan? left, SourceSpan? right)
    {
        if (left is not { } a)
            return right is null ? 0 : 1;
        if (right is not { } b)
            return -1;
        var byLine = a.Start.Line.CompareTo(b.Start.Line);
        return byLine != 0 ? byLine : a.Start.Column.CompareTo(b.Start.Column);
    }
}

/// <summary>
/// The IDENTITY of a source origin: the source position of a name when it has one, else the promotion note or original
/// record of locationless content. Copies (a META lift, X-02 recovery, a re-elaboration of the same text) are one origin.
/// A kind is no part of an origin. Never used for a generated cycle record: <see cref="SameOrigin"/> compares those by content.
/// </summary>
internal readonly struct ParameterOriginKey : IEquatable<ParameterOriginKey>
{
    private readonly string _name;
    private readonly SourceSpan? _span;
    private readonly object? _record;

    private ParameterOriginKey(string name, SourceSpan? span, object? record)
    {
        _name = name;
        _span = span;
        _record = record;
    }

    internal static ParameterOriginKey Of(ParameterDeclaration declaration)
    {
        var original = declaration.OriginalDeclaration ?? declaration;
        if (original.Span is { } span)
            return new(original.Name, span, null);
        return original.InferredProvenance is { } note
            ? note.Span is { } occurrence ? new(original.Name, occurrence, null) : new(original.Name, null, note)
            : new(original.Name, null, original);
    }

    internal static bool SameOrigin(ParameterDeclaration left, ParameterDeclaration right)
    {
        var (cycle, otherCycle) = (left.InferredProvenance?.CycleOrigin, right.InferredProvenance?.CycleOrigin);
        return cycle is null || otherCycle is null
            ? cycle is null && otherCycle is null && Of(left).Equals(Of(right))
            : cycle.SameContent(otherCycle);
    }

    public bool Equals(ParameterOriginKey other)
        => string.Equals(_name, other._name, StringComparison.Ordinal) && _span == other._span && ReferenceEquals(_record, other._record);

    public override bool Equals(object? obj) => obj is ParameterOriginKey other && Equals(other);

    public override int GetHashCode()
        => HashCode.Combine(_name, _span, _record is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(_record));
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

    // The completed tree may name a different receiver than the one the note
    // was recorded against. A spelling from that former receiver must also be a
    // declared member of the finally selected one (declared, not exported: the
    // structural surface selects by declaration).
    internal NameSuggestion? RestrictToReceiver(FrozenSet<string> receiverMembers)
    {
        if (!IsReceiverMember)
            return receiverMembers.Count == 0 ? this : null;

        return receiverMembers.Contains(Name)
            ? new NameSuggestion(Name, ReceiverQualifier, isReceiverMember: true)
            : null;
    }

    internal string EligibleName
        => ReceiverQualifier is null ? Name : $"{ReceiverQualifier}.{Name}";
}

/// <summary>
/// Revalidates only diagnostic metadata against the completed tree: exposure may
/// reveal a different opened provider. (Automatic parameter forwarding never
/// re-selects a written receiver, Q-04, so a receiver name keeps the binding
/// name resolution recorded.) First-occurrence notes are shared with
/// lifted captures, so invalidation reaches every caller without changing any
/// executable node. Reads each dot edge's own carried note
/// (<see cref="Expr.DotCall.InferredFallbackProvenance"/>) — the ONE place a
/// note is mutated — and rewrites nothing. Scope/node identity bounds
/// shared-DAG traversal.
/// </summary>
internal sealed class DotMemberProvenanceFinalizer(ElaboratedPropertyScope parentScope) : AstWalker
{
    private ElaboratedPropertyScope _scope = parentScope;
    private Pattern? _branchPattern;
    private readonly Dictionary<StaticScopeKey, HashSet<object>> _completedVisited = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<ElaboratedPropertyScope, HashSet<object>> _visited = new(ReferenceEqualityComparer.Instance);
    private RegionFreeNames? _regionNames;
    private HashSet<CompletedBodyRegion>? _regions;

    /// <summary>The bodies of the finalized tree several paths reach; null when none is.</summary>
    internal SharedBodyCensus? SharedBodies { get; init; }

    // A note outlives this walk. Keep only immutable member spellings, never a receiver AST or
    // its caller-owned lists; share the snapshot across all confirmations of one receiver.
    private readonly Dictionary<Algorithm, FrozenSet<string>> _receiverMembers = new(ReferenceEqualityComparer.Instance);

    internal FrozenSet<string> ReceiverMembers(Algorithm receiver)
    {
        if (!_receiverMembers.TryGetValue(receiver, out var members))
        {
            members = receiver.Properties.Select(static property => property.Name).ToFrozenSet(StringComparer.Ordinal);
            _receiverMembers.Add(receiver, members);
        }
        return members;
    }

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
        var pattern = _branchPattern;
        _branchPattern = null;
        var completed = CompletedStructureContext.For(algorithm, _scope, pattern);
        // A loaded module (Q-31 H-P) is rooted at the prelude: its receivers resolve under the
        // prelude level whatever holds it, so it is walked in that region once.
        if (algorithm.IsModuleRoot)
            _scope = _scope.Root;
        var visited = false;
        if (completed is not null)
        {
            if (!_completedVisited.TryGetValue(completed.Key, out var nodes))
                _completedVisited[completed.Key] = nodes = new(ReferenceEqualityComparer.Instance);
            visited = !nodes.Add(algorithm);
        }
        else visited = !Enter(algorithm);
        // Contexts whose free names select the same declarations give every edge below one verdict: a shared note is settled
        // by the first of them, never once per path of a shared graph.
        if (!visited && completed is not null && !algorithm.IsModuleRoot && SharedBodies?.Holds(algorithm) == true
            && CompletedBodyRegion.Of(completed.Facts, completed.Key, algorithm, _regionNames ??= new(new NameSetInterner())) is { } region)
            visited = !(_regions ??= []).Add(region);
        if (algorithm.DeferredRegion is not null || visited)
        {
            _scope = previousScope;
            return;
        }
        // Parameters already have Param identity. A level with no declarations
        // cannot change receiver lookup and need not split the diagnostic region.
        if (completed is not null || algorithm.Properties.Count != 0 || algorithm.Opens.Count != 0)
            _scope = ElaboratedScopeLookup.CreateScope(algorithm, _scope, completedContext: completed);
        base.VisitAlgorithm(algorithm);
        _scope = previousScope;
    }

    public override void VisitPattern(Pattern pattern) { }

    protected override void VisitConditionalBranch(CondBranch branch)
    {
        var saved = _branchPattern;
        _branchPattern = branch.Pattern;
        try { base.VisitConditionalBranch(branch); }
        finally { _branchPattern = saved; }
    }

    protected override void VisitProperty(Property property)
    {
        if (property.Value is Algorithm.User { IsAssignmentDeconstructionSource: true } source)
            foreach (var row in source.Output) VisitExpr(row);
        else VisitAlgorithm(property.Value);
    }

    protected override void VisitOpenExpression(Expr expression)
    {
        var previous = _scope;
        _scope = _scope.Root;
        base.VisitOpenExpression(expression);
        _scope = previous;
    }

    // A call argument bundle shared by several call nodes (FE-2) is walked once per scope, like a
    // shared node.
    private protected override void VisitCallArguments(OutputBundle arguments)
    {
        if (_claims.Reaches(arguments) && Enter(arguments))
            base.VisitCallArguments(arguments);
    }

    // Only a claimed dot edge (or a nested algorithm, below which one may be) is acted on: a
    // subtree that reaches neither is not walked in any scope (FE-3: a synthesized argument bundle
    // shared by the owners of K scopes is not re-walked per scope).
    private readonly NestedReachIndex _claims = new(static expr =>
        expr is Expr.DotCall { InferredFallbackProvenance.DotMemberOrigin: not null });

    public override void VisitExpr(Expr expr)
    {
        if (!_claims.Reaches(expr) || !Enter(expr))
            return;
        if (expr is Expr.DotCall { InferredFallbackProvenance: { DotMemberOrigin: not null } note } edge)
        {
            var receiver = ElaboratedScopeLookup.CompletedReceiver(edge.Target.UnwrapGraceOperand(), _scope);
            if (receiver.Kind != StaticStructuralMemberProviderKind.KnownAlgorithm
                || edge.GetLexicalFallbackSelection(receiver) != LexicalFallbackSelection.Always)
                note.ForgetDotMemberOrigin();
            else
                note.ConfirmDotMemberReceiver(ReceiverMembers(receiver.Algorithm!));
        }
        base.VisitExpr(expr);
    }
}
