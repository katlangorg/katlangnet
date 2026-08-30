namespace KatLang;

internal static class LoadElaborationGuard
{
    internal const string ModuleElaborationUnavailableDiagnostic =
        "This program uses load, but module elaboration is unavailable in the current parser/run configuration. Provide a downloader/module loader, or remove load usage.";

    private const string PostElaborationInvariantDiagnostic =
        "Internal error: module elaboration left an unresolved load directive in the AST.";

    internal static IReadOnlyList<Diagnostic> CreateUnavailableDiagnostics(Algorithm root)
    {
        var diagnostics = new List<Diagnostic>();

        VisitLoads(root, span =>
        {
            diagnostics.Add(new Diagnostic(
                ModuleElaborationUnavailableDiagnostic,
                DiagnosticSeverity.Error,
                span ?? new SourceSpan(1, 1, 1, 1))
            {
                Code = DiagnosticCode.LoadElaborationUnavailable,
            });
        });

        return diagnostics;
    }

    internal static Diagnostic CreatePostElaborationInvariantDiagnostic(Algorithm root)
    {
        TryFindFirstUnresolvedLoad(root, out var span);
        return new Diagnostic(
            PostElaborationInvariantDiagnostic,
            DiagnosticSeverity.Error,
            span ?? new SourceSpan(1, 1, 1, 1))
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
    {
        new LoadWalker(onLoad).VisitAlgorithm(root);
    }

    private sealed class LoadWalker(Action<SourceSpan?> onLoad) : AstWalker
    {
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
