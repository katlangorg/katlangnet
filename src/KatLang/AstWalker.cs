namespace KatLang;

/// <summary>
/// Shared recursive KatLang AST walker.
/// Override the visit hooks you care about; the default implementation walks
/// all nested algorithms, expressions, patterns, declaration metadata, and
/// nested scopes without using reflection.
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
    /// Visits a user-defined algorithm and recurses into its contents.
    /// </summary>
    protected virtual void VisitUserAlgorithm(Algorithm.User algorithm)
    {
        foreach (var parameter in algorithm.ExplicitParameters)
            VisitExplicitParameterDeclaration(algorithm, parameter);

        if (algorithm.ExplicitOutputSpan is { } outputSpan)
            VisitReservedOutputDeclaration(algorithm, outputSpan);

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
            case Pattern.Group group:
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
            case Expr.Combine(var left, var right):
                VisitExpr(left);
                VisitExpr(right);
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
    /// Visits the reserved <c>Output</c> declaration name when explicit output syntax was used.
    /// </summary>
    protected virtual void VisitReservedOutputDeclaration(Algorithm algorithm, SourceSpan span)
    {
    }

    /// <summary>
    /// Visits one conditional binder declaration.
    /// </summary>
    protected virtual void VisitBindPattern(Pattern.Bind pattern)
    {
        if (pattern.NameSpan is { } span)
            VisitConditionalBinderDeclaration(pattern, span);
    }

    /// <summary>
    /// Visits one conditional binder declaration span.
    /// </summary>
    protected virtual void VisitConditionalBinderDeclaration(Pattern.Bind pattern, SourceSpan span)
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
