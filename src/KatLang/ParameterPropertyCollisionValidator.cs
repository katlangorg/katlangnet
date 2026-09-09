namespace KatLang;

/// <summary>
/// Declaration validity over COMPLETED signatures: a property cannot reuse a parameter
/// name from its own or an enclosing lexical algorithm. Lookup in invalid recovery trees
/// is unchanged. Lean: conflictingOwnedNames / validOwnedDeclarations.
/// Callers have already performed the front-end structural preflight.
/// </summary>
internal sealed class ParameterPropertyCollisionValidator(
    List<Diagnostic> diagnostics,
    ParameterPropertyCollisionValidator.ParameterBindings? enclosingParameters = null) : AstWalker
{
    // Validity depends on the names in scope, not the route through a shared DAG. The
    // first conflicting source reach supplies diagnostic metadata for a shared declaration.
    private readonly Dictionary<object, HashSet<string>> _visited = new(ReferenceEqualityComparer.Instance);
    private readonly HashSet<SourceSpan> _reported = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<IReadOnlyList<ParameterDeclaration>, Dictionary<ParameterBindings, ParameterBindings>> _extensions
        = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Pattern, IReadOnlyList<ParameterDeclaration>> _binders = new(ReferenceEqualityComparer.Instance);
    private ParameterBindings _parameters = enclosingParameters ?? ParameterBindings.Empty;

    /// <summary>Immutable completed bindings retained across deferred materialization.</summary>
    internal sealed class ParameterBindings
    {
        internal static readonly ParameterBindings Empty = new(new(StringComparer.Ordinal));
        internal readonly IReadOnlyDictionary<string, SourceSpan?> Declarations;
        internal readonly string Key;

        internal ParameterBindings(Dictionary<string, SourceSpan?> declarations)
        {
            Declarations = declarations;
            Key = FrontEndRegionKeys.NameSet(declarations.Keys);
        }
    }

    protected override bool VisitsExplicitParameterDeclarations => false;

    private bool FirstVisit(object node)
    {
        if (!_visited.TryGetValue(node, out var contexts))
            _visited.Add(node, contexts = new(StringComparer.Ordinal));
        return contexts.Add(_parameters.Key);
    }

    public override void VisitAlgorithm(Algorithm algorithm)
    {
        if (!FirstVisit(algorithm))
            return;
        // Provisional deferred signatures are not declarations of the loaded program.
        // Record completed ancestors and branch binders; validate after materialization.
        if (DeferredModuleRegions.TryGet(algorithm, out var region))
            DeferredModuleRegions.Register(algorithm, region.WithValidation(_parameters));
        else
            base.VisitAlgorithm(algorithm);
    }

    public override void VisitExpr(Expr expr)
    {
        if (FirstVisit(expr))
            base.VisitExpr(expr);
    }

    protected override void VisitProperty(Property property) => VisitAlgorithm(property.Value);

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
        _parameters = Extend(algorithm.Parameters);
        try
        {
            if (_parameters.Declarations.Count > 0)
                ReportOwner(algorithm);
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
                    case Pattern.LitInt or Pattern.LitString:
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

    private ParameterBindings Extend(IReadOnlyList<ParameterDeclaration> parameters)
    {
        if (parameters.Count == 0)
            return _parameters;
        // Deconstruction helpers can share one wide signature. Extend it once per
        // enclosing context, rather than scan N declarations for each of N helpers.
        if (!_extensions.TryGetValue(parameters, out var contexts))
            _extensions.Add(parameters, contexts = new(ReferenceEqualityComparer.Instance));
        if (contexts.TryGetValue(_parameters, out var extended))
            return extended;
        var declarations = new Dictionary<string, SourceSpan?>(_parameters.Declarations, StringComparer.Ordinal);
        // First declaration wins within one signature; a nearer signature wins over
        // ancestors. Repeated pattern names therefore retain their first source anchor.
        for (var i = parameters.Count - 1; i >= 0; i--)
            declarations[parameters[i].Name] = parameters[i].Span;
        extended = new(declarations);
        contexts.Add(_parameters, extended);
        return extended;
    }

    private void ReportOwner(Algorithm owner)
    {
        foreach (var property in owner.Properties)
        {
            if (!_parameters.Declarations.TryGetValue(property.Name, out var parameterSpan))
                continue;
            // Source identity survives rewrites; equal module coordinates are distinct.
            foreach (var span in property.DeclarationSpans)
            {
                if (!_reported.Add(span))
                    continue;
                var location = parameterSpan is null ? ""
                    : $" The parameter is declared at line {parameterSpan.StartLineNumber}, column {parameterSpan.StartColumn}.";
                diagnostics.Add(new Diagnostic(
                    $"Property '{property.Name}' conflicts with parameter '{property.Name}' in the same or an enclosing algorithm. Rename one of the declarations.{location}",
                    DiagnosticSeverity.Error, span)
                {
                    Code = DiagnosticCode.ParameterPropertyCollision,
                });
            }
        }
    }
}
