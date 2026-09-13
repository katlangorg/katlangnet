using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// Diagnostic-only origin of one implicit parameter inferred from an
/// unresolved identifier. This is deliberately internal: public AST and
/// structured-error consumers need the ordinary parameter/error payloads,
/// while only KatLang's diagnostic renderer consumes this implementation
/// metadata.
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

    internal bool CanPositionAtOrigin { get; set; } = true;

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
/// A ranked suggestion and, for structural/open candidates, the exact
/// property whose final Exported classification makes the corrected spelling
/// eligible. Direct lexical properties and bound names need no exposure gate.
/// A receiver-member suggestion carries the receiver spelling it is written
/// after (<c>Math</c> for <c>Math.Ceil</c>) when that spelling is a dotted
/// name path the user can write; a lexical suggestion carries none.
/// </summary>
internal sealed class NameSuggestion
{
    internal NameSuggestion(string name, Property? requiredExportedProperty, string? receiverQualifier = null, bool isReceiverMember = false)
    {
        Name = name;
        RequiredExportedProperty = requiredExportedProperty;
        ReceiverQualifier = receiverQualifier;
        IsReceiverMember = isReceiverMember;
        if (requiredExportedProperty is not null)
            FinalPropertyExposure.Track(requiredExportedProperty);
    }

    private string Name { get; }

    private Property? RequiredExportedProperty { get; }

    private string? ReceiverQualifier { get; }

    private bool IsReceiverMember { get; }

    // An opened provider can disappear during exposure completion. A spelling
    // from that former receiver must also exist on the finally selected one.
    internal NameSuggestion? RestrictToReceiver(Algorithm receiver)
    {
        if (!IsReceiverMember)
            return receiver.Properties.Count == 0 ? this : null;

        return ElaboratedScopeLookup.TryLookupProperty(receiver, Name) is { Property.Exposure: PropertyExposure.Exported } hit
            // This receiver belongs to the completed exposure tree. Its stored
            // classification is final, including prelude trees from other passes.
            ? new NameSuggestion(Name, null, ReceiverQualifier, isReceiverMember: true)
            : null;
    }

    internal string? EligibleName
        => RequiredExportedProperty is null
            || FinalPropertyExposure.IsConfirmedExported(RequiredExportedProperty)
                ? ReceiverQualifier is null ? Name : $"{ReceiverQualifier}.{Name}"
                : null;
}

/// <summary>
/// Revalidates only diagnostic metadata against the completed tree. A final
/// owner may bind a former opened receiver as a parameter, or exposure may
/// reveal a different opened provider. First-occurrence notes are shared with
/// lifted captures, so invalidation reaches every caller without changing any
/// executable node. Scope/node identity bounds shared-DAG traversal.
/// </summary>
internal sealed class DotMemberProvenanceFinalizer(ElaboratedPropertyScope parentScope) : AstWalker
{
    private ElaboratedPropertyScope _scope = parentScope;
    private bool _inModule;
    private readonly Dictionary<ElaboratedPropertyScope, HashSet<object>> _visited = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<ElaboratedPropertyScope, HashSet<object>> _visitedInModules = new(ReferenceEqualityComparer.Instance);

    protected override bool VisitsExplicitParameterDeclarations => false;

    private bool Enter(object node)
    {
        var visited = _inModule ? _visitedInModules : _visited;
        if (!visited.TryGetValue(_scope, out var nodes))
            visited[_scope] = nodes = new(ReferenceEqualityComparer.Instance);
        return nodes.Add(node);
    }

    public override void VisitAlgorithm(Algorithm algorithm)
    {
        var previousScope = _scope;
        var previousModule = _inModule;
        _inModule |= algorithm is Algorithm.User { IsModuleElaborated: true };
        if (DeferredModuleRegions.IsDeferred(algorithm) || !Enter(algorithm))
        {
            _inModule = previousModule;
            return;
        }
        // Parameters already have Param identity. A level with no declarations
        // cannot change receiver lookup and need not split the diagnostic region.
        if (algorithm.Properties.Count != 0 || algorithm.Opens.Count != 0)
            _scope = ElaboratedScopeLookup.CreateScope(algorithm, _scope);
        base.VisitAlgorithm(algorithm);
        _scope = previousScope;
        _inModule = previousModule;
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
        if (expr is Expr.DotCall edge
            && DiagnosticRecordMetadata<ImplicitParameterProvenance>.Get(edge) is { DotMemberOrigin: not null } note)
        {
            if (_inModule)
                note.CanPositionAtOrigin = false;
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

/// <summary>
/// Weak, diagnostic-only bridge between suggestion collection (which runs
/// during parameter detection) and the later authoritative property-exposure
/// pass. Keys are the exact property records seen by lookup; retaining an AST
/// cannot retain unrelated prior ASTs through this table.
/// </summary>
internal static class FinalPropertyExposure
{
    private sealed class Holder
    {
        internal PropertyExposure? Exposure { get; set; }
    }

    private static readonly ConditionalWeakTable<Property, Holder> ExposureByProperty = new();

    internal static void Track(Property property)
        => _ = ExposureByProperty.GetValue(property, static _ => new Holder());

    private static void Record(Property property, PropertyExposure exposure)
    {
        ExposureByProperty.GetValue(property, static _ => new Holder()).Exposure = exposure;
    }

    internal static void RecordIfTracked(Property property, PropertyExposure exposure)
    {
        if (ExposureByProperty.TryGetValue(property, out var holder))
            holder.Exposure = exposure;
    }

    /// <summary>
    /// Keeps the exposure identity of a property across front-end record
    /// rebuilding before the final exposure pass. Suggestions may hold the
    /// earlier record while the resolver necessarily sees the later one.
    /// </summary>
    internal static void Link(Property source, Property destination)
    {
        var holder = ExposureByProperty.GetValue(source, static _ => new Holder());
        ExposureByProperty.Remove(destination);
        ExposureByProperty.Add(destination, holder);
    }

    internal static bool IsConfirmedExported(Property property)
        => ExposureByProperty.TryGetValue(property, out var holder)
            && holder.Exposure == PropertyExposure.Exported;

    /// <summary>
    /// Prelude/host-operation signature trees are already final and do not run
    /// through PropertyExposureResolver with the source tree. Mark them once so
    /// Math and configured host/prelude candidates remain suggestible.
    /// </summary>
    internal static void MarkTreeFinal(Algorithm algorithm)
        => new FinalExposureMarker().VisitAlgorithm(algorithm);

    /// <summary>
    /// Uses the shared exhaustive AST traversal so algorithms embedded in
    /// output/open/call expressions are finalized too, not only algorithms
    /// reachable through named properties and conditional branches.
    /// Reference-identity memoized: marked trees legally contain shared (acyclic)
    /// subtrees — detection preserves input sharing — and recording a property's
    /// stored exposure is idempotent, so revisiting a shared node is pure waste
    /// (path-exponential on diamond-shaped DAGs without the memo).
    /// </summary>
    private sealed class FinalExposureMarker : AstWalker
    {
        private readonly HashSet<object> _visited = new(ReferenceEqualityComparer.Instance);

        protected override bool VisitsExplicitParameterDeclarations => false;

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (!_visited.Add(algorithm))
                return;

            base.VisitAlgorithm(algorithm);
        }

        public override void VisitExpr(Expr expr)
        {
            if (!_visited.Add(expr))
                return;

            base.VisitExpr(expr);
        }

        protected override void VisitProperty(Property property)
        {
            Record(property, property.Exposure);
            base.VisitProperty(property);
        }
    }
}

/// <summary>
/// Stores diagnostic metadata beside records without adding an instance field.
/// Record equality/hash/printing therefore remain exactly the pre-feature
/// semantic identity. Explicit copy constructors call <see cref="Copy"/> so a
/// user or evaluator <c>with</c> clone retains the diagnostic payload.
/// </summary>
internal static class DiagnosticRecordMetadata<T> where T : class
{
    private sealed class Holder(T value)
    {
        internal T Value { get; } = value;
    }

    private static readonly ConditionalWeakTable<object, Holder> Values = new();

    internal static T? Get(object owner)
        => Values.TryGetValue(owner, out var holder) ? holder.Value : null;

    internal static void Set(object owner, T? value)
    {
        Values.Remove(owner);
        if (value is not null)
            Values.Add(owner, new Holder(value));
    }

    internal static void Copy(object source, object destination)
        => Set(destination, Get(source));
}
