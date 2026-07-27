namespace KatLang;

/// <summary>
/// Rewrites bare references to parametrized algorithms into explicit <see cref="Expr.Call"/> nodes,
/// lifting their parameters into the enclosing algorithm's <see cref="Algorithm.Parameters"/> list.
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
        return ProcessAlgorithm(root, parentParamMap: new Dictionary<string, CallableSignature>(), isRoot: true);
    }

    /// <summary>
    /// Builds a map from property name to its parameter-pattern signature for one level of properties.
    /// </summary>
    private static Dictionary<string, CallableSignature> BuildPropertyParamMap(
        IReadOnlyList<Property> properties)
    {
        var map = new Dictionary<string, CallableSignature>();
        foreach (var prop in properties)
            map[prop.Name] = CallableSignature.FromAlgorithm(prop.Name, prop.Value);
        return map;
    }

    /// <summary>
    /// Processes an algorithm: topologically sorts its properties, recursively processes each,
    /// then collects implicit deps and rewrites the algorithm's own output if parametrized.
    /// </summary>
    private static Algorithm ProcessAlgorithm(
        Algorithm alg,
        Dictionary<string, CallableSignature> parentParamMap,
        bool isRoot = false)
    {
        if (alg is Algorithm.Builtin)
            return alg;

        // A synthetic assignment-deconstruction helper (`x, ...y, z = RHS`) is a fully-elaborated
        // leaf: its output is a single bound Param (rewritten by ParameterDetector), it has no
        // properties or opens, and its explicit N-capture pattern lifts nothing. The general path
        // would still build an O(N) existing-parameter set and source-binding-kind map per helper —
        // O(N^2) across a wide deconstruction's N helpers — only to rewrite an output that has no
        // implicit calls. Returning it unchanged is O(1) and identical.
        if (alg is Algorithm.User { IsAssignmentDeconstructionHelper: true })
            return alg;

        var newOpens = ProcessOpenExprs(alg.Opens);

        // Build local param map
        var localParamMap = BuildPropertyParamMap(alg.Properties);
        var dependencyGraph = alg is Algorithm.User userAlgorithm
            ? PropertyDependencyGraphBuilder.Build(userAlgorithm)
            : PropertyDependencyGraph.Empty;

        // Visible map = parent + local (local overrides). When there are no local properties —
        // the common leaf case, e.g. every simple property value `A = expr` — nothing overrides
        // the parent map and the per-property loop below (the only writer of visibleParamMap) is
        // empty, so the parent map is shared instead of copied. Cloning this O(P) parent map once
        // per leaf property is what made this pass O(P^2) in the property count.
        Dictionary<string, CallableSignature> visibleParamMap;
        if (localParamMap.Count == 0)
        {
            visibleParamMap = parentParamMap;
        }
        else
        {
            visibleParamMap = new Dictionary<string, CallableSignature>(parentParamMap);
            foreach (var (k, v) in localParamMap)
                visibleParamMap[k] = v;
        }

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

                // Update param maps with the processed, potentially augmented signature.
                var processedSignature = CallableSignature.FromAlgorithm(prop.Name, processedBody);
                localParamMap[prop.Name] = processedSignature;
                visibleParamMap[prop.Name] = processedSignature;

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
                Opens = newOpens,
                Properties = newProperties,
                Output = newOutput,
            };
        }

        if (alg.ExplicitParameterPatterns.Count > 0)
        {
            var explicitExistingParams = new HashSet<string>(alg.Params);
            var explicitBindingKinds = BuildSourceBindingKinds(alg.ParameterPatterns);
            var newOutput = new List<Expr>(alg.Output.Count);
            foreach (var expr in alg.Output)
            {
                newOutput.Add(
                    RewriteImplicitCalls(
                        expr,
                        visibleParamMap,
                        alg.ParameterPatterns,
                        explicitBindingKinds,
                        inCallPosition: false,
                        requireExistingParameters: true,
                        explicitExistingParams));
            }

            return alg with
            {
                Opens = newOpens,
                Properties = newProperties,
                Output = newOutput,
            };
        }

        // Parametrized: collect implicit deps and lift params
        var deps = new List<(string Name, CallableSignature Signature)>();
        var seen = new HashSet<string>();
        foreach (var expr in alg.Output)
        {
            if (ShouldPreserveBareRootResolve(expr, visibleParamMap, isRoot))
                continue;

            CollectImplicitDeps(expr, visibleParamMap, seen, deps, inCallPosition: false);
        }

        // Compute lifted parameter patterns: existing patterns first, then new
        // dependency captures with their recursive shape preserved.
        var existingParams = new HashSet<string>(alg.Params);
        var newPatterns = new List<ParameterPattern>(alg.ParameterPatterns);
        foreach (var (_, signature) in deps)
        {
            if (CanForwardSingleVariadicStream(alg.ParameterPatterns, signature.ParameterPatterns))
                continue;

            foreach (var pattern in signature.ParameterPatterns)
            {
                var missingPattern = MissingCapturePattern(pattern, existingParams);
                if (missingPattern is null)
                    continue;

                newPatterns.Add(missingPattern);
                foreach (var capture in missingPattern.Captures)
                    existingParams.Add(capture.Name);
            }
        }

        // Rewrite output expressions. Source binding kinds come from the
        // LIFTED pattern list: a callee name missing from the original caller
        // parameters binds through the capture lifted above (possibly by an
        // earlier dependency with a different kind), and that lifted capture
        // is the forwarding source.
        var liftedBindingKinds = BuildSourceBindingKinds(newPatterns);
        var rewrittenOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
        {
            rewrittenOutput.Add(
                ShouldPreserveBareRootResolve(expr, visibleParamMap, isRoot)
                    ? expr
                    : RewriteImplicitCalls(
                        expr,
                        visibleParamMap,
                        alg.ParameterPatterns,
                        liftedBindingKinds,
                        inCallPosition: false));
        }

        return alg.WithParameterPatterns(newPatterns) with
        {
            Opens = newOpens,
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    private static IReadOnlyList<Expr> ProcessOpenExprs(IReadOnlyList<Expr> opens)
    {
        if (opens.Count == 0)
            return opens;

        var processed = new List<Expr>(opens.Count);
        foreach (var open in opens)
            processed.Add(ProcessOpenExpr(open));
        return processed;
    }

    private static Expr ProcessOpenExpr(Expr expr)
    {
        switch (expr)
        {
            case Expr.Block(var algorithm):
                return new Expr.Block(ProcessAlgorithm(algorithm, new Dictionary<string, CallableSignature>()))
                {
                    Span = expr.Span,
                };

            case Expr.DotCall(var target, var name, var args):
                return new Expr.DotCall(
                    ProcessOpenExpr(target),
                    name,
                    args is not null ? ProcessAlgorithm(args, new Dictionary<string, CallableSignature>()) : null)
                {
                    Span = expr.Span,
                    MemberSpan = ((Expr.DotCall)expr).MemberSpan,
                };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    ProcessOpenExpr(operand)) { Span = expr.Span };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    ProcessOpenExpr(left),
                    ProcessOpenExpr(right)) { Span = expr.Span };

            case Expr.ListLiteral(var items):
                return new Expr.ListLiteral(
                    items.Select(ProcessOpenExpr).ToList()) { Span = expr.Span };

            case Expr.Call(var function, var args):
                return new Expr.Call(
                    ProcessOpenExpr(function),
                    ProcessAlgorithm(args, new Dictionary<string, CallableSignature>())) { Span = expr.Span };

            default:
                return expr;
        }
    }

    private static bool ShouldPreserveBareRootResolve(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        bool isRoot)
        => isRoot
            && expr is Expr.Resolve(var name)
            && paramMap.TryGetValue(name, out var ps)
            && ps.Parameters.Count > 0;

    private static ParameterPattern? MissingCapturePattern(
        ParameterPattern pattern,
        IReadOnlySet<string> existingParams)
    {
        switch (pattern)
        {
            case CaptureParameterPattern capture:
                return existingParams.Contains(capture.Name) ? null : capture;

            case SequenceValueParameterPattern group:
            {
                var missingItems = new List<ParameterPattern>(group.Items.Count);
                foreach (var item in group.Items)
                {
                    var missingItem = MissingCapturePattern(item, existingParams);
                    if (missingItem is not null)
                        missingItems.Add(missingItem);
                }

                return missingItems.Count == 0
                    ? null
                    : new SequenceValueParameterPattern(missingItems);
            }

            default:
                return null;
        }
    }

    private static bool TryGetSingleTopLevelVariadicCapture(
        IReadOnlyList<ParameterPattern> patterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CaptureParameterPattern? capture)
    {
        if (patterns.Count == 1
            && patterns[0] is CaptureParameterPattern { Kind: ParameterKind.Variadic } variadic)
        {
            capture = variadic;
            return true;
        }

        capture = null;
        return false;
    }

    private static bool TryGetSingleForwardableCalleeStream(
        IReadOnlyList<ParameterPattern> patterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CaptureParameterPattern? capture)
    {
        if (TryGetSingleTopLevelVariadicCapture(patterns, out capture))
            return true;

        if (patterns.Count == 1
            && patterns[0] is SequenceValueParameterPattern { Items.Count: 1 } group
            && group.Items[0] is CaptureParameterPattern { Kind: ParameterKind.Variadic } groupedVariadic)
        {
            capture = groupedVariadic;
            return true;
        }

        capture = null;
        return false;
    }

    private static bool TryGetSingleVariadicForwarding(
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlyList<ParameterPattern> calleePatterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? calleeName,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? callerName)
    {
        if (TryGetSingleTopLevelVariadicCapture(callerPatterns, out var callerCapture)
            && TryGetSingleForwardableCalleeStream(calleePatterns, out var calleeCapture))
        {
            calleeName = calleeCapture.Name;
            callerName = callerCapture.Name;
            return true;
        }

        calleeName = null;
        callerName = null;
        return false;
    }

    private static bool CanForwardSingleVariadicStream(
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlyList<ParameterPattern> calleePatterns)
        => TryGetSingleVariadicForwarding(callerPatterns, calleePatterns, out _, out _);

    private static bool CanBuildImplicitCallArgumentsFromExistingParameters(
        IReadOnlyList<ParameterPattern> calleePatterns,
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlySet<string> existingParameterNames)
    {
        if (CanForwardSingleVariadicStream(callerPatterns, calleePatterns))
            return true;

        foreach (var capture in ParameterPattern.FlattenCaptures(calleePatterns))
        {
            if (!existingParameterNames.Contains(capture.Name))
                return false;
        }

        return true;
    }

    /// <summary>
    /// Maps every caller-side capture name (top-level and nested) to its
    /// binding kind. Implicit forwarding consults this map so the decision to
    /// re-spread a forwarded value is made from the SOURCE binding, never from
    /// the destination parameter kind alone.
    /// </summary>
    private static Dictionary<string, ParameterKind> BuildSourceBindingKinds(
        IEnumerable<ParameterPattern> callerPatterns)
    {
        var kinds = new Dictionary<string, ParameterKind>(StringComparer.Ordinal);
        foreach (var capture in ParameterPattern.FlattenCaptures(callerPatterns))
            kinds.TryAdd(capture.Name, capture.Kind);
        return kinds;
    }

    private static IReadOnlyList<Expr> BuildImplicitCallArguments(
        IReadOnlyList<ParameterPattern> calleePatterns,
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlyDictionary<string, ParameterKind> sourceBindingKinds)
    {
        TryGetSingleVariadicForwarding(
            callerPatterns,
            calleePatterns,
            out var forwardedCalleeName,
            out var forwardedCallerName);

        string MapCaptureName(CaptureParameterPattern capture)
            => forwardedCalleeName is not null
                && capture.Name == forwardedCalleeName
                ? forwardedCallerName!
                : capture.Name;

        // A variadic DESTINATION re-spreads the forwarded value only when the
        // SOURCE binding is itself a collecting binding's exact list: then
        // `callee(rest...)` re-supplies exactly the collected items
        // (spread(collect(xs)) = xs). An ordinary source binding always
        // forwards as ONE argument, even into a variadic destination. A name
        // absent from the caller's bindings is about to be lifted as a copy
        // of the callee's own pattern, so its source kind IS the callee kind.
        bool ForwardAsSpread(CaptureParameterPattern calleeCapture)
            => sourceBindingKinds.TryGetValue(MapCaptureName(calleeCapture), out var sourceKind)
                ? sourceKind == ParameterKind.Variadic
                : calleeCapture.Kind == ParameterKind.Variadic;

        return calleePatterns
            .Select(pattern => BuildPatternArgument(pattern, MapCaptureName, ForwardAsSpread))
            .ToList();
    }

    private static Expr BuildPatternArgument(
        ParameterPattern pattern,
        Func<CaptureParameterPattern, string> mapCaptureName,
        Func<CaptureParameterPattern, bool> forwardAsSpread)
    {
        return pattern switch
        {
            // A variadic destination whose source binding is a collecting binding's
            // exact list forwards through explicit spread so the callee's variadic
            // parameter re-collects exactly the caller's items; every other
            // capture forwards as one argument slot.
            CaptureParameterPattern { Kind: ParameterKind.Variadic } variadic
                when forwardAsSpread(variadic) =>
                new Expr.SequenceSpread(new Expr.Param(mapCaptureName(variadic))),
            CaptureParameterPattern capture => new Expr.Param(mapCaptureName(capture)),
            SequenceValueParameterPattern group => new Expr.Block(new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: BuildPatternArgumentOutput(group.Items, mapCaptureName, forwardAsSpread))),
            _ => throw new InvalidOperationException("Unknown parameter pattern."),
        };
    }

    private static IReadOnlyList<Expr> BuildPatternArgumentOutput(
        IReadOnlyList<ParameterPattern> patterns,
        Func<CaptureParameterPattern, string> mapCaptureName,
        Func<CaptureParameterPattern, bool> forwardAsSpread)
        => patterns
            .Select(pattern => BuildPatternArgument(pattern, mapCaptureName, forwardAsSpread))
            .ToList();

    /// <summary>
    /// Collects implicit dependencies from an expression: bare <see cref="Expr.Resolve"/> nodes
    /// pointing to parametrized algorithms in the visible scope.
    /// </summary>
    private static void CollectImplicitDeps(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        HashSet<string> seen,
        List<(string Name, CallableSignature Signature)> deps,
        bool inCallPosition)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (!inCallPosition
                    && paramMap.TryGetValue(name, out var ps)
                    && ps.Parameters.Count > 0)
                {
                    if (seen.Add(name))
                        deps.Add((name, ps));
                }
                break;

            case Expr.Call(var func, _):
                // func: if it's a direct Resolve, it's explicitly called - mark as call position.
                // Otherwise recurse normally (e.g. Prop target is not in call position).
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

            case Expr.SequenceSpread(var operand):
                CollectImplicitDeps(operand, paramMap, seen, deps, false);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectImplicitDeps(left, paramMap, seen, deps, false);
                CollectImplicitDeps(right, paramMap, seen, deps, false);
                break;

            case Expr.ListLiteral(var listItems):
                foreach (var item in listItems)
                    CollectImplicitDeps(item, paramMap, seen, deps, false);
                break;

            case Expr.DotCall(var target, var name, var dotArgs):
                if (!inCallPosition
                    && TryGetBareBuiltinCallableSignature(expr, paramMap, out var callableKey, out var signature))
                {
                    if (seen.Add(callableKey))
                        deps.Add((callableKey, signature));
                }

                // DotCall target is in algorithm position (resolveAlg, not eval).
                CollectImplicitDeps(target, paramMap, seen, deps, inCallPosition: true);
                if (dotArgs is not null && IsMathValueDotCall(target, name))
                    CollectArgumentImplicitDeps(dotArgs, paramMap, seen, deps);
                break;

            case Expr.Grace(var inner, _):
                CollectImplicitDeps(inner, paramMap, seen, deps, inCallPosition);
                break;

            case Expr.Block:
                // Nested block has its own scope, so do not collect here.
                break;

            default:
                break;
        }
    }

    private static void CollectArgumentImplicitDeps(
        Algorithm args,
        Dictionary<string, CallableSignature> paramMap,
        HashSet<string> seen,
        List<(string Name, CallableSignature Signature)> deps)
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
        Dictionary<string, CallableSignature> paramMap,
        IReadOnlyList<ParameterPattern> callerParameterPatterns,
        IReadOnlyDictionary<string, ParameterKind> sourceBindingKinds,
        bool inCallPosition,
        bool requireExistingParameters = false,
        IReadOnlySet<string>? existingParameterNames = null)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (!inCallPosition
                    && paramMap.TryGetValue(name, out var ps)
                    && ps.Parameters.Count > 0)
                {
                    if (requireExistingParameters
                        && (existingParameterNames is null
                            || !CanBuildImplicitCallArgumentsFromExistingParameters(
                                ps.ParameterPatterns,
                                callerParameterPatterns,
                                existingParameterNames)))
                    {
                        return expr;
                    }

                    var argsAlg = new Algorithm.User(
                        Parent: null,
                        Parameters: [],
                        Opens: [],
                        Properties: [],
                        Output: BuildImplicitCallArguments(ps.ParameterPatterns, callerParameterPatterns, sourceBindingKinds));

                    return new Expr.Call(new Expr.Resolve(name) { Span = expr.Span }, argsAlg) { Span = expr.Span };
                }
                return expr;

            case Expr.Call(var func, var args):
                // If func is a direct Resolve, leave it (explicitly called).
                // Otherwise recurse into func normally.
                var newFunc = func is Expr.Resolve
                    ? func
                    : RewriteImplicitCalls(
                        func,
                        paramMap,
                        callerParameterPatterns,
                        sourceBindingKinds,
                        inCallPosition: false,
                        requireExistingParameters,
                        existingParameterNames);

                var newArgs = ProcessAlgorithm(args, paramMap);
                return new Expr.Call(newFunc, newArgs) { Span = expr.Span };

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    RewriteImplicitCalls(left, paramMap, callerParameterPatterns, sourceBindingKinds, false, requireExistingParameters, existingParameterNames),
                    RewriteImplicitCalls(right, paramMap, callerParameterPatterns, sourceBindingKinds, false, requireExistingParameters, existingParameterNames)) { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, RewriteImplicitCalls(operand, paramMap, callerParameterPatterns, sourceBindingKinds, false, requireExistingParameters, existingParameterNames)) { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    RewriteImplicitCalls(target, paramMap, callerParameterPatterns, sourceBindingKinds, false, requireExistingParameters, existingParameterNames),
                    RewriteImplicitCalls(selector, paramMap, callerParameterPatterns, sourceBindingKinds, false, requireExistingParameters, existingParameterNames)) { Span = expr.Span };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    RewriteImplicitCalls(operand, paramMap, callerParameterPatterns, sourceBindingKinds, false, requireExistingParameters, existingParameterNames)) { Span = expr.Span };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    RewriteImplicitCalls(left, paramMap, callerParameterPatterns, sourceBindingKinds, false, requireExistingParameters, existingParameterNames),
                    RewriteImplicitCalls(right, paramMap, callerParameterPatterns, sourceBindingKinds, false, requireExistingParameters, existingParameterNames)) { Span = expr.Span };

            case Expr.ListLiteral(var listItems):
                return new Expr.ListLiteral(
                    listItems.Select(item => RewriteImplicitCalls(item, paramMap, callerParameterPatterns, sourceBindingKinds, false, requireExistingParameters, existingParameterNames)).ToList())
                { Span = expr.Span };

            case Expr.DotCall(var target, var name, null)
                when !inCallPosition
                    && TryGetBareBuiltinCallableSignature(expr, paramMap, out _, out var builtinSignature):
                if (requireExistingParameters
                    && (existingParameterNames is null
                        || !CanBuildImplicitCallArgumentsFromExistingParameters(
                            builtinSignature.ParameterPatterns,
                            callerParameterPatterns,
                            existingParameterNames)))
                {
                    return expr;
                }

                var dotArgsAlg = new Algorithm.User(
                    Parent: null,
                    Parameters: [],
                    Opens: [],
                    Properties: [],
                    Output: BuildImplicitCallArguments(builtinSignature.ParameterPatterns, callerParameterPatterns, sourceBindingKinds));

                return new Expr.DotCall(
                    RewriteImplicitCalls(target, paramMap, callerParameterPatterns, sourceBindingKinds, inCallPosition: true, requireExistingParameters, existingParameterNames),
                    name,
                    dotArgsAlg)
                {
                    Span = expr.Span,
                    MemberSpan = ((Expr.DotCall)expr).MemberSpan
                };

            case Expr.DotCall(var target, var name, var dotArgs):
                // DotCall target is in algorithm position (resolveAlg, not eval).
                return new Expr.DotCall(
                    RewriteImplicitCalls(target, paramMap, callerParameterPatterns, sourceBindingKinds, inCallPosition: true, requireExistingParameters, existingParameterNames),
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
                return RewriteImplicitCalls(inner, paramMap, callerParameterPatterns, sourceBindingKinds, inCallPosition, requireExistingParameters, existingParameterNames);

            case Expr.Block(var alg):
                return new Expr.Block(ProcessAlgorithm(alg, paramMap)) { Span = expr.Span };

            default:
                return expr;
        }
    }

    private static Algorithm ProcessArgumentAlgorithm(
        Algorithm args,
        Dictionary<string, CallableSignature> paramMap)
    {
        if (args.IsParametrized)
            return ProcessAlgorithm(args, paramMap);

        var newOutput = new List<Expr>(args.Output.Count);
        var argBindingKinds = BuildSourceBindingKinds(args.ParameterPatterns);
        foreach (var expr in args.Output)
            newOutput.Add(RewriteImplicitCalls(expr, paramMap, args.ParameterPatterns, argBindingKinds, inCallPosition: false));

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

    private static bool TryGetBareBuiltinCallableSignature(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? callableKey,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CallableSignature? signature)
    {
        if (expr is Expr.DotCall(Expr.Resolve { Name: var ownerName }, var memberName, null)
            && !paramMap.ContainsKey(ownerName)
            && BuiltinRegistry.TryGetBuiltinCallableSignature(ownerName, memberName, out signature)
            && signature.Parameters.Count > 0)
        {
            callableKey = $"{ownerName}.{memberName}";
            return true;
        }

        callableKey = null;
        signature = null;
        return false;
    }

    /// <summary>
    /// Processes an expression in a non-parametrized context:
    /// recurse into nested algorithms only (no lifting at this level).
    /// </summary>
    private static Expr ProcessExprNested(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap)
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
            Expr.SequenceSpread(var operand) => new Expr.SequenceSpread(
                ProcessExprNested(operand, paramMap)) { Span = expr.Span },
            Expr.SequenceConstruct(var l, var r) => new Expr.SequenceConstruct(
                ProcessExprNested(l, paramMap),
                ProcessExprNested(r, paramMap)) { Span = expr.Span },
            Expr.ListLiteral(var items) => new Expr.ListLiteral(
                items.Select(item => ProcessExprNested(item, paramMap)).ToList())
            { Span = expr.Span },
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
