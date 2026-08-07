namespace KatLang;

/// <summary>
/// Shared recursive KatLang AST walker.
/// Override the visit hooks you care about; the default implementation walks
/// all nested algorithms, expressions, patterns, declaration metadata, and
/// nested scopes without using reflection.
///
/// <para><b>Recursion contract:</b> traversal is RECURSIVE on the CLR stack by
/// design (the virtual visit hooks fire in depth-first order), and it is
/// host-controlled: subclass walks over caller-supplied trees are NOT protected by
/// the structural safety preflight that guards the library's own entry points
/// (evaluator <c>Run*</c>, parsing, front-end elaboration, semantic modeling).
/// A subclass walking an arbitrarily deep or cyclic host-built tree recurses on
/// its caller's stack; keep host-built inputs within the depths those library
/// gates document (see <see cref="EvaluationLimits.MaxSupportedAstDepth"/> and its
/// 1 MiB minimum thread-stack envelope), or bound them before walking.</para>
/// </summary>
public abstract class AstWalker
{
    /// <summary>
    /// Visits an algorithm node.
    /// </summary>
    public virtual void VisitAlgorithm(Algorithm algorithm)
    {
        switch (algorithm)
        {
            case Algorithm.User user:
                VisitUserAlgorithm(user);
                break;
            case Algorithm.Conditional conditional:
                VisitConditionalAlgorithm(conditional);
                break;
            case Algorithm.Builtin builtin:
                VisitBuiltinAlgorithm(builtin);
                break;
        }
    }

    /// <summary>
    /// Whether <see cref="VisitUserAlgorithm"/> iterates each algorithm's explicit parameter
    /// declarations and calls <see cref="VisitExplicitParameterDeclaration"/>. Defaults to
    /// <c>true</c>. Walkers that never override <see cref="VisitExplicitParameterDeclaration"/>
    /// may return <c>false</c> to skip that loop (see the note in <see cref="VisitUserAlgorithm"/>).
    /// </summary>
    protected virtual bool VisitsExplicitParameterDeclarations => true;

    /// <summary>
    /// Visits a user-defined algorithm and recurses into its contents.
    /// </summary>
    protected virtual void VisitUserAlgorithm(Algorithm.User algorithm)
    {
        // Walkers that do not override VisitExplicitParameterDeclaration can opt out of this
        // per-parameter loop. It matters for wide assignment deconstructions: those elaborate to
        // N synthetic helpers that each carry the full N-capture parameter list, so a walker that
        // visits every declaration is O(N^2) even when the visit is a no-op.
        if (VisitsExplicitParameterDeclarations)
        {
            foreach (var parameter in algorithm.ExplicitParameters)
            {
                VisitExplicitParameterDeclaration(algorithm, parameter);
                if (parameter.CollectMarkerSpan is { } collectMarkerSpan)
                    VisitCollectMarker(collectMarkerSpan);
            }
        }

        foreach (var open in algorithm.Opens)
            VisitOpenExpression(open);

        foreach (var property in algorithm.Properties)
            VisitProperty(property);

        foreach (var expr in algorithm.Output)
            VisitExpr(expr);
    }

    /// <summary>
    /// Visits a conditional algorithm and recurses into its contents.
    /// </summary>
    protected virtual void VisitConditionalAlgorithm(Algorithm.Conditional algorithm)
    {
        foreach (var open in algorithm.Opens)
            VisitOpenExpression(open);

        foreach (var branch in algorithm.Branches)
            VisitConditionalBranch(branch);
    }

    /// <summary>
    /// Visits a builtin algorithm.
    /// </summary>
    protected virtual void VisitBuiltinAlgorithm(Algorithm.Builtin algorithm)
    {
    }

    /// <summary>
    /// Visits a property declaration and then its value algorithm.
    /// </summary>
    protected virtual void VisitProperty(Property property)
    {
        foreach (var span in property.DeclarationSpans)
            VisitPropertyDeclaration(property, span);

        VisitAlgorithm(property.Value);
    }

    /// <summary>
    /// Visits one conditional branch.
    /// </summary>
    protected virtual void VisitConditionalBranch(CondBranch branch)
    {
        VisitPattern(branch.Pattern);
        VisitAlgorithm(branch.Body);
    }

    /// <summary>
    /// Visits a pattern node.
    /// </summary>
    public virtual void VisitPattern(Pattern pattern)
    {
        switch (pattern)
        {
            case Pattern.Bind bind:
                VisitBindPattern(bind);
                break;
            case Pattern.SequenceValue group:
                foreach (var item in group.Items)
                    VisitPattern(item);
                break;
            case Pattern.LitInt:
            case Pattern.LitString:
                break;
        }
    }

    /// <summary>
    /// Visits an expression node.
    /// </summary>
    public virtual void VisitExpr(Expr expr)
    {
        switch (expr)
        {
            case Expr.Resolve resolve:
                VisitResolveIdentifier(resolve);
                break;
            case Expr.Param parameter:
                VisitParameterIdentifier(parameter);
                break;
            case Expr.Unary(_, var operand):
                VisitExpr(operand);
                break;
            case Expr.Binary(_, var left, var right):
                VisitExpr(left);
                VisitExpr(right);
                break;
            case Expr.Index(var target, var selector):
                VisitExpr(target);
                VisitExpr(selector);
                break;
            case Expr.SequenceConstruct(var left, var right):
                VisitExpr(left);
                VisitExpr(right);
                break;
            case Expr.SequenceSpread(var operand):
                VisitExpr(operand);
                break;
            case Expr.ListLiteral(var items):
                foreach (var item in items)
                    VisitExpr(item);
                break;
            case Expr.DotCall(var target, _, var args):
                VisitExpr(target);
                if (expr is Expr.DotCall dotCall && dotCall.MemberSpan is { } memberSpan)
                    VisitDotMemberIdentifier(dotCall, memberSpan);
                if (args is not null)
                    VisitAlgorithm(args);
                break;
            case Expr.Grace(var inner, _):
                VisitExpr(inner);
                break;
            case Expr.Block(var algorithm):
                VisitAlgorithm(algorithm);
                break;
            case Expr.Call(var function, var args):
                VisitExpr(function);
                VisitAlgorithm(args);
                break;
            case Expr.NativeCall:
            case Expr.Num:
            case Expr.StringLiteral:
                break;
        }
    }

    /// <summary>
    /// Visits an expression that appears in open-target position.
    /// </summary>
    protected virtual void VisitOpenExpression(Expr expr) => VisitExpr(expr);

    /// <summary>
    /// Visits one property declaration span.
    /// </summary>
    protected virtual void VisitPropertyDeclaration(Property property, SourceSpan span)
    {
    }

    /// <summary>
    /// Visits one explicit ordinary parameter declaration.
    /// </summary>
    protected virtual void VisitExplicitParameterDeclaration(Algorithm algorithm, ParameterDeclaration declaration)
    {
    }

    /// <summary>
    /// Visits one conditional binder declaration.
    /// </summary>
    protected virtual void VisitBindPattern(Pattern.Bind pattern)
    {
        if (pattern.NameSpan is { } span)
            VisitConditionalBinderDeclaration(pattern, span);
        if (pattern.CollectMarkerSpan is { } collectMarkerSpan)
            VisitCollectMarker(collectMarkerSpan);
    }

    /// <summary>
    /// Visits one conditional binder declaration span.
    /// </summary>
    protected virtual void VisitConditionalBinderDeclaration(Pattern.Bind pattern, SourceSpan span)
    {
    }

    /// <summary>
    /// Visits a source-backed prefix <c>*</c> collect marker of a collecting binding.
    /// </summary>
    protected virtual void VisitCollectMarker(SourceSpan span)
    {
    }

    /// <summary>
    /// Visits a resolve identifier occurrence.
    /// </summary>
    protected virtual void VisitResolveIdentifier(Expr.Resolve expr)
    {
    }

    /// <summary>
    /// Visits a parameter identifier occurrence.
    /// </summary>
    protected virtual void VisitParameterIdentifier(Expr.Param expr)
    {
    }

    /// <summary>
    /// Visits a dot-call member identifier occurrence.
    /// </summary>
    protected virtual void VisitDotMemberIdentifier(Expr.DotCall expr, SourceSpan span)
    {
    }
}
