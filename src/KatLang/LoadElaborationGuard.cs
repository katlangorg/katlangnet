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
                span ?? new SourceSpan(1, 1, 1, 1)));
        });

        return diagnostics;
    }

    internal static Diagnostic CreatePostElaborationInvariantDiagnostic(Algorithm root)
    {
        TryFindFirstUnresolvedLoad(root, out var span);
        return new Diagnostic(
            PostElaborationInvariantDiagnostic,
            DiagnosticSeverity.Error,
            span ?? new SourceSpan(1, 1, 1, 1));
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
        public override void VisitExpr(Expr expr)
        {
            if (expr.TryGetUnresolvedLoadArguments(out var args))
            {
                onLoad(expr.Span);
                VisitAlgorithm(args);
                return;
            }

            base.VisitExpr(expr);
        }
    }
}
