namespace KatLang;

internal static class LoadElaborationGuard
{
    internal const string ModuleElaborationUnavailableDiagnostic =
        "This program uses load, but module elaboration is unavailable in the current parser/run configuration. Provide a downloader/module loader, or remove load usage.";

    private const string PostElaborationInvariantDiagnostic =
        "Internal error: module elaboration left an unresolved load directive in the AST.";

    internal static IReadOnlyList<Diagnostic> CreateUnavailableDiagnostics(Algorithm root)
        => CreateUnavailableDiagnostics(root, observations: null);

    /// <summary>
    /// Observation overload: <paramref name="observations"/> passively records the base-walker
    /// steps of the guard's walk (scaling regressions only). The pipeline passes no observer;
    /// the diagnostics are identical either way.
    /// </summary>
    internal static IReadOnlyList<Diagnostic> CreateUnavailableDiagnostics(
        Algorithm root,
        FrontEndTraversalObservations? observations)
    {
        var diagnostics = new DiagnosticBag();
        ReportUnavailable(root, diagnostics, observations);
        return diagnostics;
    }

    /// <summary>
    /// Reports one <see cref="DiagnosticCode.LoadElaborationUnavailable"/> diagnostic per load
    /// directive into the operation's bag (so a program writing thousands of them costs one
    /// bounded list) and returns whether there was any.
    /// </summary>
    internal static bool ReportUnavailable(
        Algorithm root,
        DiagnosticBag diagnostics,
        FrontEndTraversalObservations? observations = null)
    {
        var found = false;
        VisitLoads(root, observations, span =>
        {
            found = true;
            diagnostics.Report(DiagnosticCode.LoadElaborationUnavailable, ModuleElaborationUnavailableDiagnostic, span);
        });

        return found;
    }

    /// <summary>
    /// The invariant-violation diagnostic, positioned at the offending load call when it has
    /// a span of its own, otherwise at <paramref name="importSite"/> — the site, in the
    /// current document, of the module content the call lies in (module content carries no
    /// locations) — and otherwise unpositioned.
    /// </summary>
    internal static Diagnostic CreatePostElaborationInvariantDiagnostic(Algorithm root, SourceSpan? importSite = null)
    {
        TryFindFirstUnresolvedLoad(root, out var span);
        return new Diagnostic(
            PostElaborationInvariantDiagnostic,
            DiagnosticSeverity.Error,
            span ?? importSite)
        {
            Code = DiagnosticCode.InternalError,
        };
    }

    internal static void ThrowIfUnresolvedLoad(Algorithm root, string phaseName)
    {
        if (!TryFindFirstUnresolvedLoad(root, out _))
            return;

        throw new InvalidOperationException(
            $"{phaseName} requires module-elaborated AST. Unresolved load syntax should not reach this phase after a successful public parse.");
    }

    internal static bool TryFindFirstUnresolvedLoad(Algorithm root, out SourceSpan? span)
    {
        var found = false;
        SourceSpan? firstSpan = null;

        VisitLoads(root, candidateSpan =>
        {
            if (found)
                return;

            found = true;
            firstSpan = candidateSpan;
        });

        span = firstSpan;
        return found;
    }

    private static void VisitLoads(Algorithm root, Action<SourceSpan?> onLoad)
        => VisitLoads(root, observations: null, onLoad);

    private static void VisitLoads(
        Algorithm root,
        FrontEndTraversalObservations? observations,
        Action<SourceSpan?> onLoad)
    {
        new LoadWalker(onLoad) { TraversalObservations = observations }.VisitAlgorithm(root);
    }

    private sealed class LoadWalker(Action<SourceSpan?> onLoad) : AstWalker
    {
        // A load directive is an EXPRESSION (a `load('url')` call, or the `open 'url'` sugar
        // that lowers to one), so this walk inspects expression nodes only: a parameter
        // declaration carries a name and spans, never an expression, and neither declaration
        // hook is overridden here. Skipping the base walker's per-declaration loop is therefore
        // behavior-preserving — and it is what keeps the guard LINEAR on a wide assignment
        // deconstruction: the N synthetic helpers share ONE N-declaration list, so iterating it
        // once per helper was N² no-op visits. The same walker serves the sync/no-downloader
        // pipeline, the async post-elaboration invariant, deferred-branch materialization,
        // and semantic-model building. Pinned by the walker-step
        // observations in `WideDeconstructionScalabilityTests` and, for every library walker,
        // by `AstWalkerDeclarationVisitPolicyTests`.
        protected override bool VisitsExplicitParameterDeclarations => false;

        // Reference-identity memo over visited algorithms and expressions. Elaborated
        // trees legally contain shared (acyclic) subtrees — module elaboration splices one
        // cached module at several load sites, and host-built trees may share freely — and
        // this walk's observation is node-local (a load either is or is not at a node), so
        // revisits are pure waste: without the memo a compact diamond-shaped DAG makes the
        // guard walk take time exponential in its depth. One shared load node reports once
        // (per node, not per path). Walker instances are per-call, so the memo is run-scoped.
        private readonly HashSet<object> _visited = new(ReferenceEqualityComparer.Instance);

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (!_visited.Add(algorithm))
                return;

            base.VisitAlgorithm(algorithm);
        }

        /// <summary>
        /// B2c: a branch body that is a deferred module region's placeholder carries its load
        /// directives INTENTIONALLY — they are materialized when the branch is selected — so
        /// it is not an unresolved load the pipeline forgot. The guard distinguishes the two
        /// by the region the body carries (<see cref="Algorithm.DeferredRegion"/>), never by
        /// shape.
        /// </summary>
        protected override void VisitConditionalBranch(CondBranch branch)
        {
            if (branch.Body.DeferredRegion is not null)
                return;

            base.VisitConditionalBranch(branch);
        }

        public override void VisitExpr(Expr expr)
        {
            if (!_visited.Add(expr))
                return;

            if (expr.TryGetUnresolvedLoadArguments(out var args))
            {
                onLoad(expr.Span);
                foreach (var argExpr in args)
                    VisitExpr(argExpr);
                return;
            }

            base.VisitExpr(expr);
        }
    }
}
