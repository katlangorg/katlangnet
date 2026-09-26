namespace KatLang;

/// <summary>
/// FE-3: whether an expression subtree REACHES a node a walker acts on — always a nested
/// algorithm (<see cref="Expr.AlgorithmExpr"/>, below which a walker may find anything), plus the
/// walker's own extra targets — along exactly the children <see cref="AstWalker.VisitExpr"/> walks
/// (a dot-call's target, stored lexical fallback, and arguments included). Memoized per node
/// reference for one pass, so the answer costs each distinct node once.
///
/// <para>A walker whose memo is keyed by a CONTEXT (a scope, a visible-parameter set) re-walks a
/// shared subtree once per context. A walker that descends expressions ONLY to reach such target
/// nodes skips a subtree that reaches none, in every context — which is what keeps one synthesized
/// argument bundle shared by K owners (each its own context) from being walked K times.</para>
/// </summary>
internal sealed class NestedReachIndex(Func<Expr, bool>? isExtraTarget = null)
{
    private readonly Dictionary<object, bool> _memo = new(ReferenceEqualityComparer.Instance);

    public bool Reaches(OutputBundle bundle)
    {
        if (bundle.Count == 0)
            return false;
        if (_memo.TryGetValue(bundle, out var reaches))
            return reaches;
        reaches = false;
        foreach (var slot in bundle.Head)
        {
            if (Reaches(slot))
            {
                reaches = true;
                break;
            }
        }

        reaches |= bundle.Tail is { } tail && Reaches(tail);

        _memo[bundle] = reaches;
        return reaches;
    }

    public bool Reaches(Expr expr)
    {
        if (isExtraTarget?.Invoke(expr) == true)
            return true;
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return expr is Expr.AlgorithmExpr;
        if (_memo.TryGetValue(expr, out var reaches))
            return reaches;
        // Compiler-exhaustive over the closed Expr hierarchy: a new variant is a build error here
        // until its children are named, exactly as AstWalker.VisitExpr walks them.
        reaches = expr switch
        {
            Expr.AlgorithmExpr => true,
            Expr.Unary unary => Reaches(unary.Operand),
            Expr.Binary binary => Reaches(binary.Left) || Reaches(binary.Right),
            Expr.Comparison comparison => Reaches(comparison.First) || comparison.Links.Any(link => Reaches(link.Operand)),
            Expr.Index index => Reaches(index.Target) || Reaches(index.Selector),
            Expr.SequenceConstruct construct => Reaches(construct.Left) || Reaches(construct.Right),
            Expr.SequenceSpread spread => Reaches(spread.Operand),
            Expr.ListLiteral list => Reaches(list.Items),
            Expr.DotCall dotCall => Reaches(dotCall.Target)
                || (dotCall.LexicalFallback is { } fallback && Reaches(fallback))
                || (dotCall.Args is { } args && Reaches(args)),
            Expr.Grace grace => Reaches(grace.Inner),
            Expr.Capture capture => Reaches(capture.Body),
            Expr.Call call => Reaches(call.Function) || Reaches(call.Args),
            Expr.Resolve or Expr.Param or Expr.NativeCall or Expr.Num or Expr.StringLiteral
                or Expr.BoolLiteral or Expr.EmptySequence => false,
        };
        _memo[expr] = reaches;
        return reaches;
    }
}
