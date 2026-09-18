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
    // Each open TARGET node is reported once, however many regions reach it (by node
    // identity, never by span identity: an imported target has no span).
    private readonly HashSet<Expr> _reported = new(ReferenceEqualityComparer.Instance);
    private readonly OpenPresence _openPresence = new();
    private ElaboratedPropertyScope _scope;
    // The import site of the module content the walk is inside (see ImportSite): where a
    // refused imported open target — which has no span of its own — is reported. Starts at
    // the site a deferred region recorded for its body.
    private SourceSpan? _importSite;

    private OpenProviderValidator(List<Diagnostic> diagnostics, ElaboratedPropertyScope parentScope, SourceSpan? importSite)
    {
        _diagnostics = diagnostics;
        _scope = parentScope;
        _importSite = importSite;
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
        Validate(root, diagnostics, ElaboratedScopeLookup.CreateScope(prelude), importSite: null);
    }

    /// <summary>
    /// Validates a materialized deferred branch body under the chain recorded at its branch,
    /// starting from the import site the region recorded for the body.
    /// </summary>
    internal static void Validate(Algorithm root, List<Diagnostic> diagnostics, ElaboratedPropertyScope parentScope, SourceSpan? importSite = null)
        => new OpenProviderValidator(diagnostics, parentScope, importSite).VisitAlgorithm(root);

    public override void VisitAlgorithm(Algorithm algorithm)
    {
        // A deferred region's provisional body is validated when it materializes, under the
        // chain recorded at its branch.
        if (algorithm.DeferredRegion is not null || !_openPresence.Contains(algorithm) || !FirstVisit(algorithm))
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

    protected override void VisitProperty(Property property)
    {
        var saved = _importSite;
        if (ImportSite.OfProperty(property) is { } site)
            _importSite = site;
        try { VisitAlgorithm(property.Value); }
        finally { _importSite = saved; }
    }

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

        var saved = _importSite;
        if (expr is Expr.AlgorithmExpr block && ImportSite.OfBlock(block) is { } site)
            _importSite = site;
        try { base.VisitExpr(expr); }
        finally { _importSite = saved; }
    }

    private void ValidateOpens(IReadOnlyList<Expr> opens)
    {
        foreach (var target in opens)
        {
            // A target the document wrote is reported at its own span; an imported one at
            // the import site of the module content it lies in. A spanless target with no
            // site (a host-built tree) is left to the evaluator's own open resolution.
            if ((target.Span ?? _importSite) is not { } span)
                continue;

            // The HEAD of a dotted target is checked first: a prelude builtin has no members,
            // so `open count.X` can never provide anything and is refused exactly like the
            // bare `open count` — never left to become an implicit parameter of the opener
            // (the evaluators refuse the same head by kind at open resolution).
            if (DottedHead(target) is { } head
                && ElaboratedScopeLookup.ResolveOpenTarget(_scope, head) is Algorithm.Builtin
                && _reported.Add(target))
            {
                _diagnostics.Add(new Diagnostic(
                    Evaluator.FormatOpenTargetIsBuiltin(Evaluator.OpenExprName(head)),
                    DiagnosticSeverity.Error,
                    span)
                {
                    Code = DiagnosticCode.IllegalInOpen,
                });
                continue;
            }

            if (ElaboratedScopeLookup.ResolveOpenTarget(_scope, target) is not { } provider)
                continue;

            // A prelude builtin (`open count`, `open if`) is a callable, never a namespace: the
            // evaluator refuses it by KIND at open resolution (Lean `resolveAlgForOpen`), so the
            // front end refuses it eagerly too — exactly like a parameterized provider, whose
            // arity lives in `Params` where a builtin's lives in registry metadata.
            var message = provider is Algorithm.Builtin
                ? Evaluator.FormatOpenTargetIsBuiltin(Evaluator.OpenExprName(target))
                : Evaluator.RequiresArguments(provider)
                    ? Evaluator.FormatOpenTargetRequiresArguments(Evaluator.OpenExprName(target), provider, sourceBacked: true)
                    : null;
            if (message is null || !_reported.Add(target))
                continue;

            _diagnostics.Add(new Diagnostic(message, DiagnosticSeverity.Error, span)
            {
                Code = DiagnosticCode.IllegalInOpen,
            });
        }
    }

    /// <summary>The bare head of a dotted core open form (`open A.B.C` → `A`), or null for any other target.</summary>
    private static Expr? DottedHead(Expr target)
    {
        if (target is not Expr.DotCall { } dotted || !dotted.IsCoreOpenForm())
            return null;

        Expr head = dotted;
        while (head is Expr.DotCall inner)
            head = inner.Target;
        return head is Expr.Resolve ? head : null;
    }

}
