namespace KatLang;

/// <summary>
/// Walks a parsed AST and classifies identifiers as parameters vs. algorithm references.
/// For each parametrized algorithm, identifiers not matching any local property name
/// or any property name visible from a parent scope or any opened algorithm are converted from
/// <see cref="Expr.Resolve"/> to <see cref="Expr.Param"/>, and added to the algorithm's
/// <see cref="Algorithm.Params"/> list.
///
/// Lean spec anchor: <c>shouldTreatAsImplicitParam</c> — uses the full ownership-first
/// lookup order (local → parent chain → opens) to determine if a name is an implicit parameter.
/// No casing restriction: any unknown identifier becomes an implicit parameter, regardless of case.
/// </summary>
public static class ParameterDetector
{
    /// <summary>
    /// Names provided by the prelude algorithm (builtins + Math).
    /// These are always in scope and should never be treated as implicit parameters.
    /// Lean: preludeAlg properties are on the initial call stack.
    /// </summary>
    private static readonly HashSet<string> PreludeNames =
        ["if", "while", "repeat", "atoms", "load", "Math"];

    /// <summary>
    /// Property names provided by the Math builtin algorithm.
    /// Used during open resolution: when <c>open = Math</c> is encountered,
    /// these names are added to the visible set so they are not mistakenly
    /// treated as implicit parameters.
    /// Lean: mathAlg properties.
    /// </summary>
    private static readonly HashSet<string> MathPropertyNames =
        ["Pi", "E", "Abs", "Ceil", "Floor", "Round", "Sign", "Sqrt",
         "Ln", "Lg", "Sin", "Asin", "Cos", "Acos", "Tan", "Atan",
         "Pow", "Log"];

    /// <summary>
    /// Processes a root algorithm, detecting and classifying parameters throughout the tree.
    /// Returns a new AST with correct <see cref="Expr.Param"/> nodes and populated
    /// <see cref="Algorithm.Params"/> lists.
    /// </summary>
    public static Algorithm Detect(Algorithm root)
    {
        return ProcessAlgorithm(root, parentPropertyNames: new(PreludeNames), propertyAlgs: new());
    }

    private static Algorithm ProcessAlgorithm(Algorithm alg, HashSet<string> parentPropertyNames, Dictionary<string, Algorithm> propertyAlgs)
    {
        // Collect local property names and build property algorithm map
        var localNames = new HashSet<string>();
        var allPropertyAlgs = new Dictionary<string, Algorithm>(propertyAlgs);
        foreach (var prop in alg.Properties)
        {
            localNames.Add(prop.Name);
            allPropertyAlgs[prop.Name] = prop.Value;
        }

        // Build the full set of names visible from this algorithm (local + parent)
        var visibleNames = new HashSet<string>(parentPropertyNames);
        foreach (var name in localNames)
            visibleNames.Add(name);

        // Add names visible through opens (public properties of opened algorithms)
        // Lean: shouldTreatAsImplicitParam uses lookupLexical which includes opens.
        CollectOpenVisibleNames(alg.Opens, allPropertyAlgs, visibleNames);

        // Process properties recursively (each property body is a parametrized algorithm)
        var newProperties = new List<Property>(alg.Properties.Count);
        foreach (var prop in alg.Properties)
        {
            var processedBody = ProcessAlgorithm(prop.Value, visibleNames, allPropertyAlgs);
            newProperties.Add(new Property(prop.Name, processedBody, prop.IsPublic));
        }

        if (!alg.IsParametrized)
        {
            // Non-parametrized: just process nested blocks, no param detection
            var newOutput = new List<Expr>(alg.Output.Count);
            foreach (var expr in alg.Output)
                newOutput.Add(ProcessExpr(expr, visibleNames, allPropertyAlgs));

            return alg with
            {
                Properties = newProperties,
                Output = newOutput,
            };
        }

        // Parametrized: find free lowercase identifiers → params (in order of first appearance)
        var paramNames = new HashSet<string>();
        var paramOrder = new List<string>();
        var graceWeights = new Dictionary<string, int>();
        CollectFreeParams(alg.Output, visibleNames, paramNames, paramOrder, graceWeights);

        // Apply grace reordering
        if (graceWeights.Count > 0)
            ApplyGraceReordering(paramOrder, graceWeights);

        // Rewrite Resolve → Param for detected parameters
        var rewrittenOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
            rewrittenOutput.Add(RewriteParams(expr, paramNames, visibleNames, allPropertyAlgs));

        return alg with
        {
            Params = paramOrder,
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    /// <summary>
    /// Collects identifiers that are free (not defined as properties in any visible scope).
    /// Preserves order of first appearance.
    /// </summary>
    private static void CollectFreeParams(
        IReadOnlyList<Expr> exprs,
        HashSet<string> visibleNames,
        HashSet<string> paramNames,
        List<string> paramOrder,
        Dictionary<string, int> graceWeights)
    {
        foreach (var expr in exprs)
            CollectFreeParams(expr, visibleNames, paramNames, paramOrder, graceWeights);
    }

    private static void CollectFreeParams(
        Expr expr,
        HashSet<string> visibleNames,
        HashSet<string> paramNames,
        List<string> paramOrder,
        Dictionary<string, int> graceWeights)
    {
        switch (expr)
        {
            case Expr.Grace(Expr.Resolve(var name), var weight):
                if (!visibleNames.Contains(name) && name.Length > 0)
                {
                    if (paramNames.Add(name))
                        paramOrder.Add(name);
                    // Accumulate weight (multiple references sum up)
                    if (!graceWeights.TryAdd(name, weight))
                        graceWeights[name] += weight;
                }
                break;

            case Expr.Grace(var inner, _):
                // Grace wrapping non-Resolve (shouldn't happen, but handle gracefully)
                CollectFreeParams(inner, visibleNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Resolve(var name):
                if (!visibleNames.Contains(name) && name.Length > 0)
                {
                    if (paramNames.Add(name))
                        paramOrder.Add(name);
                }
                break;

            case Expr.Binary(_, var left, var right):
                CollectFreeParams(left, visibleNames, paramNames, paramOrder, graceWeights);
                CollectFreeParams(right, visibleNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Unary(_, var operand):
                CollectFreeParams(operand, visibleNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Index(var target, var selector):
                CollectFreeParams(target, visibleNames, paramNames, paramOrder, graceWeights);
                CollectFreeParams(selector, visibleNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Combine(var left, var right):
                CollectFreeParams(left, visibleNames, paramNames, paramOrder, graceWeights);
                CollectFreeParams(right, visibleNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.DotCall(var target, _, null):
                CollectFreeParams(target, visibleNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.DotCall(var target, _, var dotArgs):
                CollectFreeParams(target, visibleNames, paramNames, paramOrder, graceWeights);
                if (dotArgs is not null && !dotArgs.IsParametrized)
                    CollectFreeParams(dotArgs.Output, visibleNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Block(var alg):
                // Non-parametrized blocks (e.g. double-parens grouping) are transparent:
                // free identifiers bubble up to the enclosing param scope.
                // Parametrized blocks have their own scope — don't collect.
                if (!alg.IsParametrized)
                    CollectFreeParams(alg.Output, visibleNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Call(var func, var args):
                CollectFreeParams(func, visibleNames, paramNames, paramOrder, graceWeights);
                // Non-parametrized args (parenthesized call): free identifiers belong to the
                // enclosing algorithm. Parametrized args ({} block call): own param scope.
                if (!args.IsParametrized)
                    CollectFreeParams(args.Output, visibleNames, paramNames, paramOrder, graceWeights);
                break;

            // Num, Param — no free names
            default:
                break;
        }
    }

    /// <summary>
    /// Reorders parameters based on accumulated grace weights.
    /// Positive weight moves rightward, negative weight moves leftward.
    /// Each swap consumes one unit of weight. Movement stops at list boundaries
    /// or when blocked by a neighbor with equal or more extreme weight.
    /// </summary>
    private static void ApplyGraceReordering(
        List<string> paramOrder,
        Dictionary<string, int> graceWeights)
    {
        var weights = paramOrder.Select(n =>
            graceWeights.TryGetValue(n, out var w) ? w : 0).ToArray();

        for (var i = 0; i < paramOrder.Count; i++)
        {
            var idx = i;
            while (true)
            {
                if (weights[idx] == 0) break;

                if (weights[idx] > 0) // postfix: move right
                {
                    if (idx < paramOrder.Count - 1 && weights[idx + 1] < weights[idx])
                    {
                        weights[idx]--;
                        (paramOrder[idx], paramOrder[idx + 1]) = (paramOrder[idx + 1], paramOrder[idx]);
                        (weights[idx], weights[idx + 1]) = (weights[idx + 1], weights[idx]);
                        idx++;
                        continue;
                    }
                    break;
                }

                if (weights[idx] < 0) // prefix: move left
                {
                    if (idx > 0 && weights[idx - 1] > weights[idx])
                    {
                        weights[idx]++;
                        (paramOrder[idx], paramOrder[idx - 1]) = (paramOrder[idx - 1], paramOrder[idx]);
                        (weights[idx], weights[idx - 1]) = (weights[idx - 1], weights[idx]);
                        idx--;
                        continue;
                    }
                    break;
                }
            }
        }
    }

    /// <summary>
    /// Rewrites <see cref="Expr.Resolve"/> to <see cref="Expr.Param"/> for detected parameter names.
    /// Also recursively processes nested algorithms.
    /// </summary>
    private static Expr RewriteParams(
        Expr expr,
        HashSet<string> paramNames,
        HashSet<string> visibleNames,
        Dictionary<string, Algorithm> propertyAlgs)
    {
        switch (expr)
        {
            case Expr.Grace(var inner, _):
                // Strip Grace wrapper — weight has been consumed during collection
                return RewriteParams(inner, paramNames, visibleNames, propertyAlgs);

            case Expr.Resolve(var name) when paramNames.Contains(name):
                return new Expr.Param(name) { Span = expr.Span };

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    RewriteParams(left, paramNames, visibleNames, propertyAlgs),
                    RewriteParams(right, paramNames, visibleNames, propertyAlgs)) { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, RewriteParams(operand, paramNames, visibleNames, propertyAlgs)) { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    RewriteParams(target, paramNames, visibleNames, propertyAlgs),
                    RewriteParams(selector, paramNames, visibleNames, propertyAlgs)) { Span = expr.Span };

            case Expr.Combine(var left, var right):
                return new Expr.Combine(
                    RewriteParams(left, paramNames, visibleNames, propertyAlgs),
                    RewriteParams(right, paramNames, visibleNames, propertyAlgs)) { Span = expr.Span };

            case Expr.DotCall(var target, var name, null):
                return new Expr.DotCall(
                    RewriteParams(target, paramNames, visibleNames, propertyAlgs),
                    name) { Span = expr.Span };

            case Expr.DotCall(var target, var name, var dotArgs):
            {
                var rewrittenTarget = RewriteParams(target, paramNames, visibleNames, propertyAlgs);
                if (dotArgs is null)
                    return new Expr.DotCall(rewrittenTarget, name) { Span = expr.Span };
                if (dotArgs.IsParametrized)
                    return new Expr.DotCall(rewrittenTarget, name, ProcessAlgorithm(dotArgs, visibleNames, propertyAlgs)) { Span = expr.Span };
                var rewrittenOutput = new List<Expr>(dotArgs.Output.Count);
                foreach (var argExpr in dotArgs.Output)
                    rewrittenOutput.Add(RewriteParams(argExpr, paramNames, visibleNames, propertyAlgs));
                var processedProps = new List<Property>(dotArgs.Properties.Count);
                foreach (var prop in dotArgs.Properties)
                    processedProps.Add(new Property(prop.Name, ProcessAlgorithm(prop.Value, visibleNames, propertyAlgs), prop.IsPublic));
                return new Expr.DotCall(rewrittenTarget, name,
                    dotArgs with { Output = rewrittenOutput, Properties = processedProps }) { Span = expr.Span };
            }

            case Expr.Block(var alg):
                if (alg.IsParametrized)
                {
                    return new Expr.Block(ProcessAlgorithm(alg, visibleNames, propertyAlgs)) { Span = expr.Span };
                }
                else
                {
                    // Non-parametrized block (double-parens grouping): rewrite in enclosing param scope
                    var rewrittenOutput = new List<Expr>(alg.Output.Count);
                    foreach (var argExpr in alg.Output)
                        rewrittenOutput.Add(RewriteParams(argExpr, paramNames, visibleNames, propertyAlgs));
                    var processedProps = new List<Property>(alg.Properties.Count);
                    foreach (var prop in alg.Properties)
                        processedProps.Add(new Property(prop.Name, ProcessAlgorithm(prop.Value, visibleNames, propertyAlgs), prop.IsPublic));
                    return new Expr.Block(alg with { Output = rewrittenOutput, Properties = processedProps }) { Span = expr.Span };
                }

            case Expr.Call(var func, var args):
                if (args.IsParametrized)
                {
                    // Parametrized args ({} block): process as independent algorithm
                    return new Expr.Call(
                        RewriteParams(func, paramNames, visibleNames, propertyAlgs),
                        ProcessAlgorithm(args, visibleNames, propertyAlgs)) { Span = expr.Span };
                }
                else
                {
                    // Non-parametrized args (parenthesized call): rewrite output in enclosing
                    // param context, then process any nested properties/blocks within args.
                    var rewrittenOutput = new List<Expr>(args.Output.Count);
                    foreach (var argExpr in args.Output)
                        rewrittenOutput.Add(RewriteParams(argExpr, paramNames, visibleNames, propertyAlgs));
                    var processedProps = new List<Property>(args.Properties.Count);
                    foreach (var prop in args.Properties)
                        processedProps.Add(new Property(prop.Name, ProcessAlgorithm(prop.Value, visibleNames, propertyAlgs), prop.IsPublic));
                    return new Expr.Call(
                        RewriteParams(func, paramNames, visibleNames, propertyAlgs),
                        args with { Output = rewrittenOutput, Properties = processedProps }) { Span = expr.Span };
                }

            default:
                return expr;
        }
    }

    /// <summary>
    /// Processes an expression in a non-parametrized context: just recurse into nested algorithms.
    /// </summary>
    private static Expr ProcessExpr(Expr expr, HashSet<string> visibleNames, Dictionary<string, Algorithm> propertyAlgs)
    {
        return expr switch
        {
            Expr.Grace(var inner, _) => ProcessExpr(inner, visibleNames, propertyAlgs),
            Expr.Block(var alg) => new Expr.Block(
                ProcessAlgorithm(alg, visibleNames, propertyAlgs)) { Span = expr.Span },
            Expr.Call(var func, var args) => new Expr.Call(
                ProcessExpr(func, visibleNames, propertyAlgs),
                ProcessAlgorithm(args, visibleNames, propertyAlgs)) { Span = expr.Span },
            Expr.Binary(var op, var l, var r) => new Expr.Binary(op,
                ProcessExpr(l, visibleNames, propertyAlgs),
                ProcessExpr(r, visibleNames, propertyAlgs)) { Span = expr.Span },
            Expr.Unary(var op, var operand) => new Expr.Unary(op,
                ProcessExpr(operand, visibleNames, propertyAlgs)) { Span = expr.Span },
            Expr.Index(var t, var s) => new Expr.Index(
                ProcessExpr(t, visibleNames, propertyAlgs),
                ProcessExpr(s, visibleNames, propertyAlgs)) { Span = expr.Span },
            Expr.Combine(var l, var r) => new Expr.Combine(
                ProcessExpr(l, visibleNames, propertyAlgs),
                ProcessExpr(r, visibleNames, propertyAlgs)) { Span = expr.Span },
            Expr.DotCall(var t, var n, var da) => new Expr.DotCall(
                ProcessExpr(t, visibleNames, propertyAlgs),
                n,
                da is not null ? ProcessAlgorithm(da, visibleNames, propertyAlgs) : null) { Span = expr.Span },
            _ => expr,
        };
    }

    /// <summary>
    /// Attempts to statically resolve an open expression to an Algorithm
    /// using known properties. Used for determining which names are visible
    /// through opens during parameter detection.
    /// </summary>
    private static Algorithm? ResolveOpenExprStatic(Expr expr, Dictionary<string, Algorithm> knownProps)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                return knownProps.TryGetValue(name, out var alg) ? alg : null;

            case Expr.DotCall(var target, var name, null):
            {
                var targetAlg = ResolveOpenExprStatic(target, knownProps);
                if (targetAlg is null) return null;
                // Open path: intermediate must be public (Lean: lookupPublicProp)
                foreach (var prop in targetAlg.Properties)
                    if (prop.Name == name && prop.IsPublic)
                        return prop.Value;
                return null;
            }

            case Expr.Block(var blockAlg):
                return blockAlg;

            default:
                return null;
        }
    }

    /// <summary>
    /// Collects property names visible through opens by statically resolving
    /// open expressions and collecting their public property names.
    /// Lean: shouldTreatAsImplicitParam uses lookupLexical which includes opens.
    /// </summary>
    private static void CollectOpenVisibleNames(
        IReadOnlyList<Expr> opens,
        Dictionary<string, Algorithm> knownProps,
        HashSet<string> visibleNames)
    {
        foreach (var openExpr in opens)
            CollectOpenNamesFromExpr(openExpr, knownProps, visibleNames);
    }

    private static void CollectOpenNamesFromExpr(
        Expr expr,
        Dictionary<string, Algorithm> knownProps,
        HashSet<string> visibleNames)
    {
        if (expr is Expr.Combine(var left, var right))
        {
            CollectOpenNamesFromExpr(left, knownProps, visibleNames);
            CollectOpenNamesFromExpr(right, knownProps, visibleNames);
            return;
        }

        var alg = ResolveOpenExprStatic(expr, knownProps);
        if (alg is null)
        {
            // If we can't resolve statically, check if this is a prelude name with known sub-properties.
            // Math is a builtin algorithm whose properties aren't in the parsed AST.
            if (expr is Expr.Resolve(var preName) && preName == "Math")
            {
                foreach (var mathName in MathPropertyNames)
                    visibleNames.Add(mathName);
            }
            return;
        }

        foreach (var prop in alg.Properties)
            if (prop.IsPublic)
                visibleNames.Add(prop.Name);
    }
}
