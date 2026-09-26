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
/// written name path that resolves to nothing is <see cref="DiagnosticCode.UnresolvedOpenTarget"/>
/// here (a parameter-owned head is parameter detection's <see cref="DiagnosticCode.OpenTargetIsParameter"/>,
/// an illegal target shape the parser's <see cref="DiagnosticCode.BadOpenForm"/>), so open validity
/// never depends on whether a lookup happens to consult the target.
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
    private readonly DiagnosticBag _diagnostics;
    private readonly Dictionary<ElaboratedPropertyScope, HashSet<object>> _visited = new();
    // Each open TARGET node is reported once, however many regions reach it (by node
    // identity, never by span identity: an imported target has no span).
    private readonly HashSet<Expr> _reported = new(ReferenceEqualityComparer.Instance);
    private readonly OpenPresence _openPresence;
    private ElaboratedPropertyScope _scope;
    // The import site of the module content the walk is inside (see ImportSite): where a
    // refused imported open target — which has no span of its own — is reported. Starts at
    // the site a deferred region recorded for its body.
    private SourceSpan? _importSite;

    private OpenProviderValidator(
        DiagnosticBag diagnostics,
        ElaboratedPropertyScope parentScope,
        SourceSpan? importSite,
        FrontEndTraversalObservations? observations)
    {
        _diagnostics = diagnostics;
        _scope = parentScope;
        _importSite = importSite;
        _openPresence = new() { TraversalObservations = observations };
        TraversalObservations = observations;
    }

    protected override bool VisitsExplicitParameterDeclarations => false;

    private bool FirstVisit(object node)
    {
        if (!_visited.TryGetValue(_scope, out var nodes))
            _visited[_scope] = nodes = new(ReferenceEqualityComparer.Instance);
        return nodes.Add(node);
    }

    /// <summary>Validates every open target of a completed program tree against the prelude-rooted chain.</summary>
    internal static void Validate(
        Algorithm root,
        DiagnosticBag diagnostics,
        HostOperations? hostOperations,
        FrontEndTraversalObservations? observations = null)
    {
        var prelude = hostOperations?.SemanticPreludeAlgorithm ?? BuiltinRegistry.CreateSemanticPreludeAlgorithm();
        Validate(root, diagnostics, ElaboratedScopeLookup.CreateScope(prelude), importSite: null, observations);
    }

    /// <summary>
    /// Validates a materialized deferred branch body under the chain recorded at its branch,
    /// starting from the import site the region recorded for the body.
    /// </summary>
    internal static void Validate(
        Algorithm root,
        DiagnosticBag diagnostics,
        ElaboratedPropertyScope parentScope,
        SourceSpan? importSite = null,
        FrontEndTraversalObservations? observations = null)
        => new OpenProviderValidator(diagnostics, parentScope, importSite, observations).VisitAlgorithm(root);

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

        // A call argument bundle shared by several call nodes (FE-2) is scanned once, like a shared node.
        private protected override void VisitCallArguments(OutputBundle arguments)
        {
            if (_memo.TryGetValue(arguments, out var known)) { _found |= known; return; }
            var outer = _found;
            _found = false;
            base.VisitCallArguments(arguments);
            _memo[arguments] = _found;
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
        // Opens are validated at algorithms only: a subtree that reaches none has nothing to
        // validate in ANY scope region, so it is not walked (FE-3: one argument bundle shared by the
        // owners of K scope regions is not re-walked per region).
        if (!_nestedAlgorithms.Reaches(expr) || !FirstVisit(expr))
            return;

        var saved = _importSite;
        if (expr is Expr.AlgorithmExpr block && ImportSite.OfBlock(block) is { } site)
            _importSite = site;
        try { base.VisitExpr(expr); }
        finally { _importSite = saved; }
    }

    // A call argument bundle shared by several call nodes (FE-2) is visited once per scope region,
    // like a shared node — and not at all when it reaches no algorithm (FE-3).
    private protected override void VisitCallArguments(OutputBundle arguments)
    {
        if (_nestedAlgorithms.Reaches(arguments) && FirstVisit(arguments))
            base.VisitCallArguments(arguments);
    }

    private readonly NestedReachIndex _nestedAlgorithms = new();

    private void ValidateOpens(IReadOnlyList<Expr> opens)
    {
        foreach (var target in opens)
        {
            // Each WRITTEN target is a site the author fixes, so each is reported (a repeated
            // spelling is one provider to lookup, but two places in the source).
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
            {
                // `open` is static: a target naming nothing is invalid whether or not any
                // lookup ever consults this level's opens. Left alone, the front end dropped
                // it (its names became implicit parameters) while the evaluator failed as
                // soon as a lookup reached the level (Lean `resolveAllOpens`).
                if (DescribeUnresolvedTarget(target) is { } reason && _reported.Add(target))
                {
                    _diagnostics.Add(new Diagnostic(reason, DiagnosticSeverity.Error, span)
                    {
                        Code = DiagnosticCode.UnresolvedOpenTarget,
                    });
                }

                continue;
            }

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

    /// <summary>
    /// Why a written name path provides no algorithm — the step at which the static
    /// resolution (<see cref="ElaboratedScopeLookup.ResolveOpenTarget"/>) fails, named the way
    /// the evaluator's open resolution fails there: a head no enclosing declaration or prelude
    /// member provides (an open head never resolves through another open), a member its
    /// receiver lacks, declares privately (open paths select public members), or declares only
    /// inside a conditional branch (a family exposes no members). Null for every target this
    /// rule does not own: a parameter-owned head (parameter detection reported
    /// <see cref="DiagnosticCode.OpenTargetIsParameter"/>), an inline block, and the shapes the
    /// parser rejects as <see cref="DiagnosticCode.BadOpenForm"/>.
    /// </summary>
    private string? DescribeUnresolvedTarget(Expr target)
    {
        if (!PropertyDependencyGraphBuilder.TryGetOpenTargetPath(target, out var head, out var steps))
            return null;

        var description = Evaluator.OpenExprName(target);
        if (ElaboratedScopeLookup.TryLookupDirectLexicalProperty(_scope, head) is not { } headHit)
        {
            return $"'{description}' cannot be opened because no property named '{head}' is visible here; " +
                "the first name of an open target resolves through the enclosing declarations and the prelude, never through another open.";
        }

        var receiver = headHit.Property.Value;
        var receiverDescription = head;
        foreach (var step in steps)
        {
            if (ElaboratedScopeLookup.TryLookupPublicProperty(receiver, step) is { } member)
            {
                receiver = member.Property.Value;
                receiverDescription += "." + step;
                continue;
            }

            if (ElaboratedScopeLookup.TryLookupProperty(receiver, step) is not null)
                return $"'{description}' cannot be opened because property '{step}' of '{receiverDescription}' is not public; an open path selects public members only.";

            return receiver.DefinesConditionalBranchProperty(step)
                ? $"'{description}' cannot be opened because '{step}' is declared only inside a conditional branch of '{receiverDescription}', and a clause family exposes no members."
                : $"'{description}' cannot be opened because '{receiverDescription}' has no property named '{step}'.";
        }

        return null;
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
