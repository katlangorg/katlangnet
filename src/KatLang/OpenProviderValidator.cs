namespace KatLang;

/// <summary>
/// The front-end half of the <c>open</c> PROVIDER rule: every <c>open</c> target must resolve
/// to an algorithm that needs no call. Runs after parameter-signature completion — the only
/// point at which an INFERRED parameter list is final, so an implicitly parameterized
/// provider (<c>Lib = { public X = 1  p + 1 }</c>, whose output row makes <c>p</c> Lib's
/// own parameter) is refused exactly like an explicit <c>Lib(p)</c> — and before exposure
/// resolution, which it does not depend on. Targets resolve through the shared static
/// resolution (<see cref="ElaboratedScopeLookup.ResolveOpenTarget"/>): the head by the
/// direct lexical chain, dotted steps through public members, an inline block by itself; a
/// target that resolves to nothing is left to the existing unresolved-name/open diagnostics.
/// Only the RESOLVED provider is judged — a parameterized head of a dotted target is
/// navigated by identity, and a member of it that captures the head's parameter is the
/// separate accessibility question decided at each access. The evaluator applies the same
/// rule at open resolution (<c>Evaluator.ResolveOpen</c>, Lean <c>resolveOpen</c>), so a tree
/// this pass rejects is never evaluated for a restatement.
/// Scope regions mirror parameter detection: a user algorithm's body is one level, a clause
/// family's own open list (host trees) one level above its branch bodies, and an inline
/// open-target block a separate region starting at the prelude.
/// </summary>
internal sealed class OpenProviderValidator : AstWalker
{
    private readonly List<Diagnostic> _diagnostics;
    private readonly Dictionary<ElaboratedPropertyScope, HashSet<object>> _visited = new();
    private readonly HashSet<SourceSpan> _reported = new(ReferenceEqualityComparer.Instance);
    private readonly OpenPresence _openPresence = new();
    private ElaboratedPropertyScope _scope;

    private OpenProviderValidator(List<Diagnostic> diagnostics, ElaboratedPropertyScope parentScope)
    {
        _diagnostics = diagnostics;
        _scope = parentScope;
    }

    protected override bool VisitsExplicitParameterDeclarations => false;

    private bool FirstVisit(object node)
    {
        if (!_visited.TryGetValue(_scope, out var nodes))
            _visited[_scope] = nodes = new(ReferenceEqualityComparer.Instance);
        return nodes.Add(node);
    }

    /// <summary>Validates every open target of a completed program tree against the prelude-rooted chain.</summary>
    internal static void Validate(Algorithm root, List<Diagnostic> diagnostics, HostOperations? hostOperations)
    {
        var prelude = hostOperations?.SemanticPreludeAlgorithm ?? BuiltinRegistry.CreateSemanticPreludeAlgorithm();
        Validate(root, diagnostics, ElaboratedScopeLookup.CreateScope(prelude));
    }

    /// <summary>Validates a materialized deferred branch body under the chain recorded at its branch.</summary>
    internal static void Validate(Algorithm root, List<Diagnostic> diagnostics, ElaboratedPropertyScope parentScope)
        => new OpenProviderValidator(diagnostics, parentScope).VisitAlgorithm(root);

    public override void VisitAlgorithm(Algorithm algorithm)
    {
        // A deferred region's provisional body is validated when it materializes, under the
        // chain recorded at its branch.
        if (DeferredModuleRegions.IsDeferred(algorithm) || !_openPresence.Contains(algorithm) || !FirstVisit(algorithm))
            return;

        base.VisitAlgorithm(algorithm);
    }

    protected override void VisitUserAlgorithm(Algorithm.User algorithm)
    {
        var saved = _scope;
        _scope = ElaboratedScopeLookup.CreateScope(algorithm, saved);
        try
        {
            ValidateOpens(algorithm.Opens);
            base.VisitUserAlgorithm(algorithm);
        }
        finally
        {
            _scope = saved;
        }
    }

    protected override void VisitConditionalAlgorithm(Algorithm.Conditional algorithm)
    {
        var saved = _scope;
        if (algorithm.Opens.Count > 0)
        {
            _scope = ElaboratedScopeLookup.CreateScope(algorithm, saved);
            ValidateOpens(algorithm.Opens);
        }

        try
        {
            base.VisitConditionalAlgorithm(algorithm);
        }
        finally
        {
            _scope = saved;
        }
    }

    protected override void VisitProperty(Property property) => VisitAlgorithm(property.Value);

    // Context matters only where there is an open to validate. A graph-bounded scan
    // prevents the context walk from expanding paths through unrelated shared DAGs.
    private sealed class OpenPresence : AstWalker
    {
        private readonly Dictionary<object, bool> _memo = new(ReferenceEqualityComparer.Instance);
        private bool _found;
        protected override bool VisitsExplicitParameterDeclarations => false;

        public bool Contains(Algorithm algorithm)
        {
            VisitAlgorithm(algorithm);
            return _memo[algorithm];
        }

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (_memo.TryGetValue(algorithm, out var known)) { _found |= known; return; }
            var outer = _found;
            _found = algorithm.Opens.Count > 0;
            base.VisitAlgorithm(algorithm);
            _memo[algorithm] = _found;
            _found |= outer;
        }

        public override void VisitExpr(Expr expression)
        {
            if (_memo.TryGetValue(expression, out var known)) { _found |= known; return; }
            var outer = _found;
            _found = false;
            base.VisitExpr(expression);
            _memo[expression] = _found;
            _found |= outer;
        }
    }

    protected override void VisitOpenExpression(Expr expression)
    {
        // An inline open target starts a separate region at the prelude, without the
        // importing owner's declarations (ParameterDetector.ProcessOpenExprs).
        var saved = _scope;
        _scope = _scope.Root;
        try { base.VisitOpenExpression(expression); }
        finally { _scope = saved; }
    }

    public override void VisitExpr(Expr expr)
    {
        if (!FirstVisit(expr))
            return;

        base.VisitExpr(expr);
    }

    private void ValidateOpens(IReadOnlyList<Expr> opens)
    {
        foreach (var target in opens)
        {
            if (ElaboratedScopeLookup.ResolveOpenTarget(_scope, target) is not { } provider
                || !Evaluator.RequiresArguments(provider)
                || target.Span is not { } span
                || !_reported.Add(span))
            {
                continue;
            }

            _diagnostics.Add(new Diagnostic(
                Evaluator.FormatOpenTargetRequiresArguments(Evaluator.OpenExprName(target), provider),
                DiagnosticSeverity.Error,
                span)
            {
                Code = DiagnosticCode.IllegalInOpen,
            });
        }
    }

}
