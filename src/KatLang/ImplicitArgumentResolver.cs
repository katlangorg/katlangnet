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
    /// Finds bare <see cref="Expr.Resolve"/> references to local parametrized properties
    /// within an expression list. Used for building the dependency graph.
    /// </summary>
    private static HashSet<string> FindBareParametrizedRefs(
        IReadOnlyList<Expr> exprs,
        Dictionary<string, IReadOnlyList<string>> localParamMap)
    {
        var refs = new HashSet<string>();
        foreach (var expr in exprs)
            FindBareParametrizedRefs(expr, localParamMap, refs, inCallPosition: false);
        return refs;
    }

    private static void FindBareParametrizedRefs(
        Expr expr,
        Dictionary<string, IReadOnlyList<string>> localParamMap,
        HashSet<string> refs,
        bool inCallPosition)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (!inCallPosition
                    && localParamMap.TryGetValue(name, out var ps)
                    && ps.Count > 0)
                {
                    refs.Add(name);
                }
                break;

            case Expr.Call(var func, _):
                // func in call position: if it's a Resolve, suppress lifting
                FindBareParametrizedRefs(func, localParamMap, refs, inCallPosition: true);
                // Do NOT recurse into call args — separate scope
                break;

            case Expr.Binary(_, var left, var right):
                FindBareParametrizedRefs(left, localParamMap, refs, false);
                FindBareParametrizedRefs(right, localParamMap, refs, false);
                break;

            case Expr.Unary(_, var operand):
                FindBareParametrizedRefs(operand, localParamMap, refs, false);
                break;

            case Expr.Index(var target, var selector):
                FindBareParametrizedRefs(target, localParamMap, refs, false);
                FindBareParametrizedRefs(selector, localParamMap, refs, false);
                break;

            case Expr.Combine(var left, var right):
                FindBareParametrizedRefs(left, localParamMap, refs, false);
                FindBareParametrizedRefs(right, localParamMap, refs, false);
                break;

            case Expr.DotCall(var target, _, _):
                // DotCall target is in algorithm position (resolveAlg, not eval)
                FindBareParametrizedRefs(target, localParamMap, refs, inCallPosition: true);
                break;

            case Expr.Grace(var inner, _):
                FindBareParametrizedRefs(inner, localParamMap, refs, inCallPosition);
                break;

            case Expr.Block:
                // Nested block — own scope, do not collect
                break;

            default:
                break;
        }
    }

    /// <summary>
    /// Finds all bare (non-call-position) <see cref="Expr.Resolve"/> references to sibling
    /// properties within an expression list. Unlike <see cref="FindBareParametrizedRefs"/>,
    /// includes references to ALL siblings regardless of their current parameter count.
    /// Used by <see cref="TopologicalSort"/> to ensure correct processing order for
    /// transitive implicit argument propagation.
    /// Lean spec: "Transitive ordering invariant" in implicit argument resolution.
    /// </summary>
    private static HashSet<string> FindBareSiblingRefs(
        IReadOnlyList<Expr> exprs,
        HashSet<string> siblingNames)
    {
        var refs = new HashSet<string>();
        foreach (var expr in exprs)
            FindBareSiblingRefs(expr, siblingNames, refs, inCallPosition: false);
        return refs;
    }

    private static void FindBareSiblingRefs(
        Expr expr,
        HashSet<string> siblingNames,
        HashSet<string> refs,
        bool inCallPosition)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (!inCallPosition && siblingNames.Contains(name))
                    refs.Add(name);
                break;

            case Expr.Call(var func, _):
                FindBareSiblingRefs(func, siblingNames, refs, inCallPosition: true);
                break;

            case Expr.Binary(_, var left, var right):
                FindBareSiblingRefs(left, siblingNames, refs, false);
                FindBareSiblingRefs(right, siblingNames, refs, false);
                break;

            case Expr.Unary(_, var operand):
                FindBareSiblingRefs(operand, siblingNames, refs, false);
                break;

            case Expr.Index(var target, var selector):
                FindBareSiblingRefs(target, siblingNames, refs, false);
                FindBareSiblingRefs(selector, siblingNames, refs, false);
                break;

            case Expr.Combine(var left, var right):
                FindBareSiblingRefs(left, siblingNames, refs, false);
                FindBareSiblingRefs(right, siblingNames, refs, false);
                break;

            case Expr.DotCall(var target, _, null):
                FindBareSiblingRefs(target, siblingNames, refs, false);
                break;

            case Expr.DotCall(var target, _, _):
                FindBareSiblingRefs(target, siblingNames, refs, inCallPosition: true);
                break;

            case Expr.Grace(var inner, _):
                FindBareSiblingRefs(inner, siblingNames, refs, inCallPosition);
                break;

            case Expr.Block:
                break;

            default:
                break;
        }
    }

    /// <summary>
    /// Topologically sorts property indices based on sibling references.
    /// Uses ALL bare sibling references (not just parametrized ones) to ensure
    /// correct transitive ordering: a property with initially zero parameters
    /// may acquire parameters through its own dependencies during resolution.
    /// Returns indices in processing order (dependencies first).
    /// Properties involved in cycles are appended at the end (unmodified).
    /// </summary>
    private static List<int> TopologicalSort(
        IReadOnlyList<Property> properties,
        Dictionary<string, IReadOnlyList<string>> localParamMap)
    {
        var nameToIndex = new Dictionary<string, int>();
        for (var i = 0; i < properties.Count; i++)
            nameToIndex[properties[i].Name] = i;

        // Collect all sibling property names for broad dependency tracking
        var siblingNames = new HashSet<string>(nameToIndex.Keys);

        // Build adjacency: edge from i → j means property i depends on property j
        var inDegree = new int[properties.Count];
        var dependents = new List<int>[properties.Count];
        for (var i = 0; i < properties.Count; i++)
            dependents[i] = [];

        for (var i = 0; i < properties.Count; i++)
        {
            // Use ALL sibling refs (not just parametrized) for correct transitive ordering
            var refs = FindBareSiblingRefs(properties[i].Value.Output, siblingNames);
            foreach (var refName in refs)
            {
                if (nameToIndex.TryGetValue(refName, out var j) && j != i)
                {
                    dependents[j].Add(i); // j must be processed before i
                    inDegree[i]++;
                }
            }
        }

        // Kahn's algorithm
        var queue = new Queue<int>();
        for (var i = 0; i < properties.Count; i++)
        {
            if (inDegree[i] == 0)
                queue.Enqueue(i);
        }

        var result = new List<int>(properties.Count);
        while (queue.Count > 0)
        {
            var node = queue.Dequeue();
            result.Add(node);
            foreach (var dep in dependents[node])
            {
                inDegree[dep]--;
                if (inDegree[dep] == 0)
                    queue.Enqueue(dep);
            }
        }

        // Any remaining nodes are in cycles — append them as-is
        if (result.Count < properties.Count)
        {
            for (var i = 0; i < properties.Count; i++)
            {
                if (inDegree[i] > 0)
                    result.Add(i);
            }
        }

        return result;
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

        // Visible map = parent + local (local overrides)
        var visibleParamMap = new Dictionary<string, IReadOnlyList<string>>(parentParamMap);
        foreach (var (k, v) in localParamMap)
            visibleParamMap[k] = v;

        // Topological sort of properties
        var topoOrder = TopologicalSort(alg.Properties, localParamMap);

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
                processedProperties[idx] = new Property(prop.Name, processedCond, prop.IsPublic);
            }
            else
            {
                var processedBody = ProcessAlgorithm(prop.Value, visibleParamMap);

                // Update param maps with (potentially augmented) params
                localParamMap[prop.Name] = processedBody.Params;
                visibleParamMap[prop.Name] = processedBody.Params;

                processedProperties[idx] = new Property(prop.Name, processedBody, prop.IsPublic);
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
                // Do NOT recurse into call args — separate scope
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

            case Expr.Combine(var left, var right):
                CollectImplicitDeps(left, paramMap, seen, deps, false);
                CollectImplicitDeps(right, paramMap, seen, deps, false);
                break;

            case Expr.DotCall(var target, _, _):
                // DotCall target is in algorithm position (resolveAlg, not eval)
                CollectImplicitDeps(target, paramMap, seen, deps, inCallPosition: true);
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

                // Process args algorithm recursively (it's a separate scope)
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

            case Expr.Combine(var left, var right):
                return new Expr.Combine(
                    RewriteImplicitCalls(left, paramMap, false),
                    RewriteImplicitCalls(right, paramMap, false)) { Span = expr.Span };

            case Expr.DotCall(var target, var name, var dotArgs):
                // DotCall target is in algorithm position (resolveAlg, not eval)
                return new Expr.DotCall(
                    RewriteImplicitCalls(target, paramMap, inCallPosition: true),
                    name,
                    dotArgs is not null ? ProcessAlgorithm(dotArgs, paramMap) : null) { Span = expr.Span };

            case Expr.Grace(var inner, _):
                return RewriteImplicitCalls(inner, paramMap, inCallPosition);

            case Expr.Block(var alg):
                return new Expr.Block(ProcessAlgorithm(alg, paramMap)) { Span = expr.Span };

            default:
                return expr;
        }
    }

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
            Expr.Combine(var l, var r) => new Expr.Combine(
                ProcessExprNested(l, paramMap),
                ProcessExprNested(r, paramMap)) { Span = expr.Span },
            Expr.DotCall(var t, var n, var da) => new Expr.DotCall(
                ProcessExprNested(t, paramMap),
                n,
                da is not null ? ProcessAlgorithm(da, paramMap) : null) { Span = expr.Span },
            Expr.Grace(var inner, _) => ProcessExprNested(inner, paramMap),
            _ => expr,
        };
    }
}
