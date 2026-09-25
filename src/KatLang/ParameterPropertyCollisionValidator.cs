using System.Collections.Immutable;

namespace KatLang;

/// <summary>
/// Declaration validity over COMPLETED signatures: a property cannot reuse a parameter
/// name from its own or an enclosing lexical algorithm. Lookup in invalid recovery trees
/// is unchanged. Lean: conflictingOwnedNames / validOwnedDeclarations.
/// Callers have already performed the front-end structural preflight.
/// <para><paramref name="programRoot"/> names the ROOT program algorithm when the caller
/// validates a whole program. The root is never called, so its completed signature
/// binds nothing: every root parameter is a name the root itself could not resolve (or
/// a name forwarding lifted into it), and evaluation reports exactly that
/// (<see cref="EvalError.UnresolvedImplicitParams"/>, with the reference and its
/// suggestion). Those phantom inputs are therefore checked only against the root's OWN
/// declarations — where a lifted name meets the property it would have been forwarded
/// from — and never blamed on a declaration nested in a deeper owner: a nested property
/// cannot hide an input no call establishes, and reporting it as the collision would
/// point the user at the wrong declaration (<c>Lib = { public Q = 1 }</c> followed by the
/// root row <c>Q + 1</c> is a missing <c>open Lib</c> / <c>Lib.Q</c>, not a conflict in
/// <c>Lib</c>). A nested owner's completed signature keeps the full rule: its parameters
/// are bound by its calls, so a deeper property of the same name really would hide them.</para>
/// </summary>
internal sealed class ParameterPropertyCollisionValidator(
    DiagnosticBag diagnostics,
    ParameterPropertyCollisionValidator.ParameterBindings? enclosingParameters = null,
    Algorithm? programRoot = null,
    SourceSpan? importSite = null) : AstWalker
{
    // Validity depends on the names in scope, not the route through a shared DAG. The
    // first conflicting source reach supplies diagnostic metadata for a shared declaration,
    // which is reported once by its declaration NODE (never by span identity: an imported
    // declaration has no span, and a value-type span could not carry identity).
    // A node's visited contexts are CONTEXT IDS: the canonical id of the visible parameter NAME
    // SET (ContextId, a NameSetInterner set), so a visit compares an int — hashing a content key
    // of every name in scope at each node made a P-parameter body O(P²) — and an extension
    // derives its id from the enclosing context's by the names it adds (FE-1), never re-sorting
    // every name in scope. Equal name sets share one id whatever bindings built them, so the
    // memo's equivalence is exactly name-set content, as before.
    private readonly Dictionary<object, HashSet<int>> _visited = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<ParameterBindings, CanonicalNameSet> _contextNames = new(ReferenceEqualityComparer.Instance);
    private NameSetInterner? _nameSets;
    private readonly HashSet<Property> _reported = new(ReferenceEqualityComparer.Instance);
    // The import site of the module content the walk is inside (see ImportSite): where a
    // conflicting imported declaration — which has no span of its own — is reported. Starts
    // at the site a deferred region recorded for its body.
    private SourceSpan? _importSite = importSite;
    private readonly Dictionary<object, Dictionary<ParameterBindings, ParameterBindings>> _extensions
        = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Pattern, IReadOnlyList<ParameterDeclaration>> _binders = new(ReferenceEqualityComparer.Instance);
    private ParameterBindings _parameters = enclosingParameters ?? ParameterBindings.Empty;

    /// <summary>
    /// Immutable completed bindings retained across deferred materialization: each visible
    /// parameter name with its first declaration's span, nearest signature winning. PERSISTENT
    /// (FE-1): an extension shares the enclosing entries and writes only its own names.
    /// </summary>
    internal sealed class ParameterBindings
    {
        internal static readonly ParameterBindings Empty = new(ImmutableDictionary.Create<string, SourceSpan?>(StringComparer.Ordinal));

        internal ParameterBindings(ImmutableDictionary<string, SourceSpan?> declarations) => Entries = declarations;

        internal ImmutableDictionary<string, SourceSpan?> Entries { get; }

        internal IReadOnlyDictionary<string, SourceSpan?> Declarations => Entries;
    }

    protected override bool VisitsExplicitParameterDeclarations => false;

    private NameSetInterner NameSets => _nameSets ??= new NameSetInterner(TraversalObservations);

    private bool FirstVisit(object node)
    {
        if (!_visited.TryGetValue(node, out var contexts))
            _visited.Add(node, contexts = []);
        return contexts.Add(ContextId(_parameters));
    }

    // Equal name sets share one id, so the memo's equivalence is exactly name-set equality.
    private int ContextId(ParameterBindings bindings) => ContextNames(bindings).Id;

    // A context this validator extended already has its set (see Extend); one it did not build —
    // the empty context or a deferred region's recorded enclosing bindings — is canonicalized once.
    private CanonicalNameSet ContextNames(ParameterBindings bindings)
    {
        if (_contextNames.TryGetValue(bindings, out var names))
            return names;
        TraversalObservations?.RecordCollisionContextIntern();
        names = NameSets.With(NameSetInterner.Empty, bindings.Entries.Keys);
        _contextNames.Add(bindings, names);
        return names;
    }

    public override void VisitAlgorithm(Algorithm algorithm)
    {
        if (!FirstVisit(algorithm))
            return;
        // Provisional deferred signatures are not declarations of the loaded program.
        // Record completed ancestors and branch binders on the region the placeholder
        // carries; validate after materialization. (This walk rewrites nothing, so the
        // recording is the one in-place update a region ever receives from the front end.)
        if (algorithm.DeferredRegion is { } region)
            region.RecordValidation(_parameters);
        else
            base.VisitAlgorithm(algorithm);
    }

    public override void VisitExpr(Expr expr)
    {
        if (!FirstVisit(expr))
            return;
        var saved = _importSite;
        if (expr is Expr.AlgorithmExpr block && ImportSite.OfBlock(block) is { } site)
            _importSite = site;
        try { base.VisitExpr(expr); }
        finally { _importSite = saved; }
    }

    protected override void VisitProperty(Property property)
    {
        var saved = _importSite;
        if (ImportSite.OfProperty(property) is { } site)
            _importSite = site;
        try { VisitAlgorithm(property.Value); }
        finally { _importSite = saved; }
    }

    protected override void VisitOpenExpression(Expr expr)
    {
        // Match ParameterDetector.ProcessOpenExprs: an inline open target starts a
        // separate owner region at the prelude, without the importing owner's inputs.
        var saved = _parameters;
        _parameters = ParameterBindings.Empty;
        try { base.VisitOpenExpression(expr); }
        finally { _parameters = saved; }
    }

    protected override void VisitUserAlgorithm(Algorithm.User algorithm)
    {
        var saved = _parameters;
        _parameters = Extend(algorithm.ParameterPatterns);
        try
        {
            if (_parameters.Declarations.Count > 0)
                ReportOwner(algorithm);
            // The root program's phantom signature is checked against its own declarations
            // only (see the class documentation): nested owners descend without it.
            if (ReferenceEquals(algorithm, programRoot))
                _parameters = saved;
            base.VisitUserAlgorithm(algorithm);
        }
        finally { _parameters = saved; }
    }

    protected override void VisitConditionalBranch(CondBranch branch)
    {
        if (!_binders.TryGetValue(branch.Pattern, out var parameters))
        {
            var declarations = new List<ParameterDeclaration>();
            var pending = new Stack<Pattern>();
            pending.Push(branch.Pattern);
            while (pending.TryPop(out var current))
            {
                switch (current)
                {
                    case Pattern.Bind binder:
                        declarations.Add(new(binder.Name, binder.NameSpan));
                        break;
                    case Pattern.SequenceValue group:
                        for (var i = group.Items.Count - 1; i >= 0; i--)
                            pending.Push(group.Items[i]);
                        break;
                    case Pattern.LitInt or Pattern.LitString or Pattern.LitBool:
                        break;
                    default:
                        throw new InvalidOperationException($"Unhandled pattern: {current.GetType().Name}");
                }
            }
            _binders.Add(branch.Pattern, parameters = declarations);
        }
        var saved = _parameters;
        _parameters = Extend(parameters);
        try { VisitAlgorithm(branch.Body); }
        finally { _parameters = saved; }
    }

    private ParameterBindings Extend(IReadOnlyList<ParameterPattern> parameterPatterns)
        => parameterPatterns.Count == 0
            ? _parameters
            : Extend(parameterPatterns, static patterns => ParameterPattern.FlattenCaptures(patterns));

    private ParameterBindings Extend(IReadOnlyList<ParameterDeclaration> parameters)
        => parameters.Count == 0 ? _parameters : Extend(parameters, static declarations => declarations);

    // Keyed by the STORED list instance: a user algorithm's pattern list (the one parameter
    // channel; its flat Parameters view is a fresh projection per read, so it can never be the
    // memo key) or a branch pattern's binder list. Deconstruction helpers can share one wide
    // pattern list. Extend it once per enclosing context, rather than flatten and scan N
    // declarations for each of N helpers.
    private ParameterBindings Extend<TList>(TList signature, Func<TList, IReadOnlyList<ParameterDeclaration>> declarationsOf)
        where TList : class
    {
        if (!_extensions.TryGetValue(signature, out var contexts))
            _extensions.Add(signature, contexts = new(ReferenceEqualityComparer.Instance));
        if (contexts.TryGetValue(_parameters, out var extended))
            return extended;
        // PERSISTENT extension (FE-1): the enclosing declarations are shared, never copied, and
        // the context's name set is the enclosing one's extended by this signature's names.
        // First declaration wins within one signature; a nearer signature wins over
        // ancestors. Repeated pattern names therefore retain their first source anchor.
        var declarations = _parameters.Entries.ToBuilder();
        var parameters = declarationsOf(signature);
        for (var i = parameters.Count - 1; i >= 0; i--)
        {
            declarations[parameters[i].Name] = parameters[i].Span;
            TraversalObservations?.RecordContextEntryWritten();
        }
        extended = new(declarations.ToImmutable());
        var enclosingNames = ContextNames(_parameters);
        TraversalObservations?.RecordCollisionContextIntern();
        _contextNames.Add(extended, NameSets.With(enclosingNames, parameters.Select(static parameter => parameter.Name)));
        contexts.Add(_parameters, extended);
        return extended;
    }

    private void ReportOwner(Algorithm owner)
    {
        foreach (var property in owner.Properties)
        {
            if (!_parameters.Declarations.TryGetValue(property.Name, out var parameterSpan))
                continue;
            if (!_reported.Add(property))
                continue;
            // The parameter's position is stated only when the document wrote it (an imported
            // parameter has none, and a module-relative coordinate is never rendered).
            var location = parameterSpan is { } declared
                ? $" The parameter is declared at line {declared.Start.Line}, column {declared.Start.Column}."
                : "";
            var message =
                $"Property '{property.Name}' conflicts with parameter '{property.Name}' in the same or an enclosing algorithm. Rename one of the declarations.{location}";
            // A written declaration is reported at each of its name occurrences (a clause
            // family contributes several); an imported one — no occurrence spans — once, at
            // the import site. A document-owned synthetic declaration (no spans, no site)
            // cannot conflict: its name is not an identifier a parameter can carry.
            if (property.DeclarationSpans.Count > 0)
            {
                foreach (var span in property.DeclarationSpans)
                    diagnostics.Add(CreateCollisionDiagnostic(message, span));
            }
            else if (_importSite is { } site)
            {
                diagnostics.Add(CreateCollisionDiagnostic(message, site));
            }
        }
    }

    private static Diagnostic CreateCollisionDiagnostic(string message, SourceSpan span)
        => new(message, DiagnosticSeverity.Error, span) { Code = DiagnosticCode.ParameterPropertyCollision };
}
