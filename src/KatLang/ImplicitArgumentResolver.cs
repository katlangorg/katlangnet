namespace KatLang;

/// <summary>
/// Rewrites bare references to parametrized algorithms into explicit <see cref="Expr.Call"/> nodes,
/// lifting their parameters into the enclosing algorithm's <see cref="Algorithm.Params"/> list.
/// Must run after <see cref="ParameterDetector"/>.
/// </summary>
public static class ImplicitArgumentResolver
{
    /// <summary>
    /// Processes a root algorithm, resolving all implicit arguments throughout the tree.
    /// Returns a new AST where every bare reference to a parametrized algorithm
    /// has been rewritten into an explicit call with lifted parameters.
    /// </summary>
    public static Algorithm Resolve(Algorithm root)
    {
        return ProcessAlgorithm(root, parentParamMap: new Dictionary<string, IReadOnlyList<string>>(), isRoot: true);
    }

    /// <summary>
    /// Builds a map from property name to its parameter list for one level of properties.
    /// </summary>
    private static Dictionary<string, IReadOnlyList<string>> BuildPropertyParamMap(
        IReadOnlyList<Property> properties)
    {
        var map = new Dictionary<string, IReadOnlyList<string>>();
        foreach (var prop in properties)
            map[prop.Name] = prop.Value.Params;
        return map;
    }

    /// <summary>
    /// Processes an algorithm: topologically sorts its properties, recursively processes each,
    /// then collects implicit deps and rewrites the algorithm's own output if parametrized.
    /// </summary>
    private static Algorithm ProcessAlgorithm(
        Algorithm alg,
        Dictionary<string, IReadOnlyList<string>> parentParamMap,
        bool isRoot = false)
    {
        // Build local param map
        var localParamMap = BuildPropertyParamMap(alg.Properties);
        var dependencyGraph = alg is Algorithm.User userAlgorithm
            ? PropertyDependencyGraphBuilder.Build(userAlgorithm)
            : PropertyDependencyGraph.Empty;

        // Visible map = parent + local (local overrides)
        var visibleParamMap = new Dictionary<string, IReadOnlyList<string>>(parentParamMap);
        foreach (var (k, v) in localParamMap)
            visibleParamMap[k] = v;

        // Topological sort of properties
        var topoOrder = dependencyGraph.TopologicalOrder;

        // Process properties in topological order
        var processedProperties = new Property[alg.Properties.Count];
        foreach (var idx in topoOrder)
        {
            var prop = alg.Properties[idx];

            if (prop.Value is Algorithm.Conditional condAlg)
            {
                // Process each conditional branch body
                var processedBranches = new List<CondBranch>(condAlg.Branches.Count);
                foreach (var branch in condAlg.Branches)
                {
                    var processedBody = ProcessAlgorithm(branch.Body, visibleParamMap);
                    processedBranches.Add(new CondBranch(branch.Pattern, processedBody));
                }
                var processedCond = new Algorithm.Conditional(
                    condAlg.Parent, condAlg.Opens, processedBranches);
                processedProperties[idx] = prop.WithValue(processedCond);
            }
            else
            {
                var processedBody = ProcessAlgorithm(prop.Value, visibleParamMap);

                // Update param maps with (potentially augmented) params
                localParamMap[prop.Name] = processedBody.Params;
                visibleParamMap[prop.Name] = processedBody.Params;

                processedProperties[idx] = prop.WithValue(processedBody);
            }
        }

        var newProperties = processedProperties.ToList();

        if (!alg.IsParametrized)
        {
            // Non-parametrized: recurse into nested structures but don't lift
            var newOutput = new List<Expr>(alg.Output.Count);
            foreach (var expr in alg.Output)
                newOutput.Add(ProcessExprNested(expr, visibleParamMap));

            return alg with
            {
                Properties = newProperties,
                Output = newOutput,
            };
        }

        // Parametrized: collect implicit deps and lift params
        var deps = new List<(string Name, IReadOnlyList<string> Params)>();
        var seen = new HashSet<string>();
        foreach (var expr in alg.Output)
        {
            if (ShouldPreserveBareRootResolve(expr, visibleParamMap, isRoot))
                continue;

            CollectImplicitDeps(expr, visibleParamMap, seen, deps, inCallPosition: false);
        }

        // Compute lifted params: existing first, then new ones from deps
        var existingParams = new HashSet<string>(alg.Params);
        var newParams = new List<string>(alg.Params);
        foreach (var (_, refParams) in deps)
        {
            foreach (var p in refParams)
            {
                if (existingParams.Add(p))
                    newParams.Add(p);
            }
        }

        // Rewrite output expressions
        var rewrittenOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
        {
            rewrittenOutput.Add(
                ShouldPreserveBareRootResolve(expr, visibleParamMap, isRoot)
                    ? expr
                    : RewriteImplicitCalls(expr, visibleParamMap, inCallPosition: false));
        }

        return alg with
        {
            Params = newParams,
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    private static bool ShouldPreserveBareRootResolve(
        Expr expr,
        Dictionary<string, IReadOnlyList<string>> paramMap,
        bool isRoot)
        => isRoot
            && expr is Expr.Resolve(var name)
            && paramMap.TryGetValue(name, out var ps)
            && ps.Count > 0;

    /// <summary>
    /// Collects implicit dependencies from an expression: bare <see cref="Expr.Resolve"/> nodes
    /// pointing to parametrized algorithms in the visible scope.
    /// </summary>
    private static void CollectImplicitDeps(
        Expr expr,
        Dictionary<string, IReadOnlyList<string>> paramMap,
        HashSet<string> seen,
        List<(string Name, IReadOnlyList<string> Params)> deps,
        bool inCallPosition)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (!inCallPosition
                    && paramMap.TryGetValue(name, out var ps)
                    && ps.Count > 0)
                {
                    if (seen.Add(name))
                        deps.Add((name, ps));
                }
                break;

            case Expr.Call(var func, _):
                // func: if it's a direct Resolve, it's explicitly called — mark as call position
                // Otherwise recurse normally (e.g. Prop target is not in call position)
                if (func is Expr.Resolve)
                    CollectImplicitDeps(func, paramMap, seen, deps, inCallPosition: true);
                else
                    CollectImplicitDeps(func, paramMap, seen, deps, inCallPosition: false);
                break;

            case Expr.Binary(_, var left, var right):
                CollectImplicitDeps(left, paramMap, seen, deps, false);
                CollectImplicitDeps(right, paramMap, seen, deps, false);
                break;

            case Expr.Unary(_, var operand):
                CollectImplicitDeps(operand, paramMap, seen, deps, false);
                break;

            case Expr.Index(var target, var selector):
                CollectImplicitDeps(target, paramMap, seen, deps, false);
                CollectImplicitDeps(selector, paramMap, seen, deps, false);
                break;

            case Expr.ResultJoin(var left, var right):
                CollectImplicitDeps(left, paramMap, seen, deps, false);
                CollectImplicitDeps(right, paramMap, seen, deps, false);
                break;

            case Expr.DotCall(var target, var name, var dotArgs):
                // DotCall target is in algorithm position (resolveAlg, not eval)
                CollectImplicitDeps(target, paramMap, seen, deps, inCallPosition: true);
                if (dotArgs is not null && IsMathValueDotCall(target, name))
                    CollectArgumentImplicitDeps(dotArgs, paramMap, seen, deps);
                break;

            case Expr.Grace(var inner, _):
                CollectImplicitDeps(inner, paramMap, seen, deps, inCallPosition);
                break;

            case Expr.Block:
                // Nested block — own scope, do not collect
                break;

            default:
                break;
        }
    }

    private static void CollectArgumentImplicitDeps(
        Algorithm args,
        Dictionary<string, IReadOnlyList<string>> paramMap,
        HashSet<string> seen,
        List<(string Name, IReadOnlyList<string> Params)> deps)
    {
        if (args.IsParametrized)
            return;

        foreach (var argExpr in args.Output)
            CollectImplicitDeps(argExpr, paramMap, seen, deps, inCallPosition: false);
    }

    /// <summary>
    /// Rewrites bare <see cref="Expr.Resolve"/> nodes into <see cref="Expr.Call"/> nodes
    /// with lifted parameters. Also recursively processes nested algorithms.
    /// </summary>
    private static Expr RewriteImplicitCalls(
        Expr expr,
        Dictionary<string, IReadOnlyList<string>> paramMap,
        bool inCallPosition)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (!inCallPosition
                    && paramMap.TryGetValue(name, out var ps)
                    && ps.Count > 0)
                {
                    // Rewrite: Resolve(name) → Call(Resolve(name), argsAlg)
                    var argExprs = new List<Expr>(ps.Count);
                    foreach (var p in ps)
                        argExprs.Add(new Expr.Param(p));

                    var argsAlg = new Algorithm.User(
                        Parent: null,
                        Params: [],
                        Opens: [],
                        Properties: [],
                        Output: argExprs);

                    return new Expr.Call(new Expr.Resolve(name) { Span = expr.Span }, argsAlg) { Span = expr.Span };
                }
                return expr;

            case Expr.Call(var func, var args):
                // If func is a direct Resolve, leave it (explicitly called)
                // Otherwise recurse into func normally
                var newFunc = func is Expr.Resolve
                    ? func
                    : RewriteImplicitCalls(func, paramMap, inCallPosition: false);

                var newArgs = ProcessAlgorithm(args, paramMap);
                return new Expr.Call(newFunc, newArgs) { Span = expr.Span };

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    RewriteImplicitCalls(left, paramMap, false),
                    RewriteImplicitCalls(right, paramMap, false)) { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, RewriteImplicitCalls(operand, paramMap, false)) { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    RewriteImplicitCalls(target, paramMap, false),
                    RewriteImplicitCalls(selector, paramMap, false)) { Span = expr.Span };

            case Expr.ResultJoin(var left, var right):
                return new Expr.ResultJoin(
                    RewriteImplicitCalls(left, paramMap, false),
                    RewriteImplicitCalls(right, paramMap, false)) { Span = expr.Span };

            case Expr.DotCall(var target, var name, var dotArgs):
                // DotCall target is in algorithm position (resolveAlg, not eval)
                return new Expr.DotCall(
                    RewriteImplicitCalls(target, paramMap, inCallPosition: true),
                    name,
                    dotArgs is not null
                        ? IsMathValueDotCall(target, name)
                            ? ProcessArgumentAlgorithm(dotArgs, paramMap)
                            : ProcessAlgorithm(dotArgs, paramMap)
                        : null)
                {
                    Span = expr.Span,
                    MemberSpan = ((Expr.DotCall)expr).MemberSpan
                };

            case Expr.Grace(var inner, _):
                return RewriteImplicitCalls(inner, paramMap, inCallPosition);

            case Expr.Block(var alg):
                return new Expr.Block(ProcessAlgorithm(alg, paramMap)) { Span = expr.Span };

            default:
                return expr;
        }
    }

    private static Algorithm ProcessArgumentAlgorithm(
        Algorithm args,
        Dictionary<string, IReadOnlyList<string>> paramMap)
    {
        if (args.IsParametrized)
            return ProcessAlgorithm(args, paramMap);

        var newOutput = new List<Expr>(args.Output.Count);
        foreach (var expr in args.Output)
            newOutput.Add(RewriteImplicitCalls(expr, paramMap, inCallPosition: false));

        var newProperties = new List<Property>(args.Properties.Count);
        foreach (var prop in args.Properties)
            newProperties.Add(prop.WithValue(ProcessAlgorithm(prop.Value, paramMap)));

        return args with
        {
            Properties = newProperties,
            Output = newOutput,
        };
    }

    private static bool IsMathValueDotCall(Expr target, string name)
        => target is Expr.Resolve { Name: "Math" }
            && BuiltinRegistry.IsMathFunctionMember(name);

    /// <summary>
    /// Processes an expression in a non-parametrized context:
    /// recurse into nested algorithms only (no lifting at this level).
    /// </summary>
    private static Expr ProcessExprNested(
        Expr expr,
        Dictionary<string, IReadOnlyList<string>> paramMap)
    {
        return expr switch
        {
            Expr.Block(var alg) => new Expr.Block(
                ProcessAlgorithm(alg, paramMap)) { Span = expr.Span },
            Expr.Call(var func, var args) => new Expr.Call(
                ProcessExprNested(func, paramMap),
                ProcessAlgorithm(args, paramMap)) { Span = expr.Span },
            Expr.Binary(var op, var l, var r) => new Expr.Binary(op,
                ProcessExprNested(l, paramMap),
                ProcessExprNested(r, paramMap)) { Span = expr.Span },
            Expr.Unary(var op, var operand) => new Expr.Unary(op,
                ProcessExprNested(operand, paramMap)) { Span = expr.Span },
            Expr.Index(var t, var s) => new Expr.Index(
                ProcessExprNested(t, paramMap),
                ProcessExprNested(s, paramMap)) { Span = expr.Span },
            Expr.ResultJoin(var l, var r) => new Expr.ResultJoin(
                ProcessExprNested(l, paramMap),
                ProcessExprNested(r, paramMap)) { Span = expr.Span },
            Expr.DotCall(var t, var n, var da) => new Expr.DotCall(
                ProcessExprNested(t, paramMap),
                n,
                da is not null ? ProcessAlgorithm(da, paramMap) : null)
            {
                Span = expr.Span,
                MemberSpan = ((Expr.DotCall)expr).MemberSpan
            },
            Expr.Grace(var inner, _) => ProcessExprNested(inner, paramMap),
            _ => expr,
        };
    }
}
