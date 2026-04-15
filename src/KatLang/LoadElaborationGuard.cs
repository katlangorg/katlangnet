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

        VisitAlgorithm(root, span =>
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

        VisitAlgorithm(root, candidateSpan =>
        {
            if (found)
                return;

            found = true;
            firstSpan = candidateSpan;
        });

        span = firstSpan;
        return found;
    }

    private static void VisitAlgorithm(Algorithm algorithm, Action<SourceSpan?> onLoad)
    {
        switch (algorithm)
        {
            case Algorithm.User user:
                foreach (var open in user.Opens)
                    VisitExpr(open, onLoad);

                foreach (var property in user.Properties)
                    VisitAlgorithm(property.Value, onLoad);

                foreach (var expr in user.Output)
                    VisitExpr(expr, onLoad);
                break;

            case Algorithm.Conditional conditional:
                foreach (var open in conditional.Opens)
                    VisitExpr(open, onLoad);

                foreach (var branch in conditional.Branches)
                    VisitAlgorithm(branch.Body, onLoad);
                break;

            case Algorithm.Builtin:
                break;
        }
    }

    private static void VisitExpr(Expr expr, Action<SourceSpan?> onLoad)
    {
        switch (expr)
        {
            case Expr.Call(Expr.Resolve("load"), var args):
                onLoad(expr.Span);
                VisitAlgorithm(args, onLoad);
                break;

            case Expr.Call(var function, var args):
                VisitExpr(function, onLoad);
                VisitAlgorithm(args, onLoad);
                break;

            case Expr.Block(var algorithm):
                VisitAlgorithm(algorithm, onLoad);
                break;

            case Expr.DotCall(var target, _, var args):
                VisitExpr(target, onLoad);
                if (args is not null)
                    VisitAlgorithm(args, onLoad);
                break;

            case Expr.Unary(_, var operand):
                VisitExpr(operand, onLoad);
                break;

            case Expr.Binary(_, var left, var right):
                VisitExpr(left, onLoad);
                VisitExpr(right, onLoad);
                break;

            case Expr.Index(var target, var selector):
                VisitExpr(target, onLoad);
                VisitExpr(selector, onLoad);
                break;

            case Expr.Combine(var left, var right):
                VisitExpr(left, onLoad);
                VisitExpr(right, onLoad);
                break;

            case Expr.Grace(var inner, _):
                VisitExpr(inner, onLoad);
                break;

            case Expr.Resolve:
            case Expr.Param:
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.NativeCall:
                break;
        }
    }
}