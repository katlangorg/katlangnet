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
    /// Processes a root algorithm, detecting and classifying parameters throughout the tree.
    /// Returns a new AST with correct <see cref="Expr.Param"/> nodes and populated
    /// <see cref="Algorithm.Params"/> lists, along with any diagnostics (e.g. free
    /// identifiers in conditional branch bodies that violate the full-input-specification rule).
    /// </summary>
    public static (Algorithm Root, IReadOnlyList<Diagnostic> Diagnostics) Detect(Algorithm root)
    {
        var diagnostics = new List<Diagnostic>();
        var preludeScope = ElaboratedScopeLookup.CreateScope(BuiltinRegistry.CreateSemanticPreludeAlgorithm());
        var processed = ProcessAlgorithm(
            root,
            preludeScope,
            capturedParamNames: [],
            diagnostics);
        return (processed, diagnostics);
    }

    private static Algorithm ProcessAlgorithm(
        Algorithm alg,
        ElaboratedPropertyScope parentScope,
        HashSet<string> capturedParamNames,
        List<Diagnostic>? diagnostics = null)
    {
        var scope = ElaboratedScopeLookup.CreateScope(alg, parentScope);

        var paramNames = new HashSet<string>(alg.Params);
        var paramOrder = new List<string>(alg.Params);
        var graceWeights = new Dictionary<string, int>();

        if (alg.IsParametrized)
        {
            // Ordinary nested algorithms close over already-known outer params.
            // These should rewrite to Expr.Param but must not become new local params.
            var boundNames = UnionNames(capturedParamNames, alg.Params);

            CollectFreeParams(alg.Output, scope, boundNames, paramNames, paramOrder, graceWeights);

            if (graceWeights.Count > 0)
                ApplyGraceReordering(paramOrder, graceWeights);
        }

        var nestedCapturedParamNames = alg.IsParametrized
            ? UnionNames(capturedParamNames, paramOrder)
            : new HashSet<string>(capturedParamNames);

        // Process properties recursively (each property body is a parametrized algorithm)
        var newProperties = new List<Property>(alg.Properties.Count);
        foreach (var prop in alg.Properties)
        {
            if (prop.Value is Algorithm.Conditional condAlg)
            {
                // Process each conditional branch body with the full-input-specification rule:
                // - Pattern binder names are rewritten to Expr.Param (resolved via valEnv at runtime)
                // - NO other free identifiers become implicit parameters
                // - The branch body's Params list is empty (bindings come from pattern matching)
                var processedBranches = new List<CondBranch>(condAlg.Branches.Count);
                foreach (var branch in condAlg.Branches)
                {
                    var binderNames = new HashSet<string>(branch.Pattern.BoundNames());
                    var processedBody = ProcessConditionalBranchBody(
                        branch.Body,
                        scope,
                        binderNames,
                        prop.Name,
                        nestedCapturedParamNames,
                        diagnostics);
                    processedBranches.Add(new CondBranch(branch.Pattern, processedBody));
                }
                var processedCond = new Algorithm.Conditional(
                    condAlg.Parent, condAlg.Opens, processedBranches);
                newProperties.Add(new Property(prop.Name, processedCond, prop.IsPublic, prop.Exposure)
                {
                    DeclarationSpans = prop.DeclarationSpans
                });
            }
            else
            {
                var processedBody = ProcessAlgorithm(
                    prop.Value,
                    scope,
                    nestedCapturedParamNames,
                    diagnostics);
                newProperties.Add(new Property(prop.Name, processedBody, prop.IsPublic, prop.Exposure)
                {
                    DeclarationSpans = prop.DeclarationSpans
                });
            }
        }

        if (!alg.IsParametrized)
        {
            // Non-parametrized: just process nested blocks, no param detection
            var newOutput = new List<Expr>(alg.Output.Count);
            foreach (var expr in alg.Output)
                newOutput.Add(ProcessExpr(expr, scope, nestedCapturedParamNames));

            return alg with
            {
                Properties = newProperties,
                Output = newOutput,
            };
        }

        // Rewrite Resolve → Param for detected parameters
        var rewrittenOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
            rewrittenOutput.Add(RewriteParams(expr, paramNames, scope, capturedParamNames));

        return alg with
        {
            Params = paramOrder,
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    /// <summary>
    /// Processes a conditional branch body under the full-input-specification rule:
    /// - Pattern binder names are rewritten to <see cref="Expr.Param"/> (resolved via valEnv at runtime).
    /// - No other free identifiers become implicit parameters.
    /// - The branch body's <see cref="Algorithm.Params"/> list is empty.
    /// - Nested algorithms within the body are processed normally.
    ///
    /// This enforces the invariant that conditional branch inputs come ONLY from the
    /// branch pattern. Free identifiers in the body that are not pattern-bound must
    /// resolve through ordinary lexical / property / open / builtin lookup.
    /// Any free identifier that would be an implicit parameter (not visible in any scope)
    /// is reported as a compile-time error.
    /// </summary>
    private static Algorithm ProcessConditionalBranchBody(
        Algorithm body,
        ElaboratedPropertyScope parentScope,
        HashSet<string> binderNames,
        string branchName,
        HashSet<string> capturedParamNames,
        List<Diagnostic>? diagnostics)
    {
        var bodyScope = ElaboratedScopeLookup.CreateScope(body, parentScope);

        var bodyCapturedParamNames = UnionNames(capturedParamNames, binderNames);

        // Detect free identifiers that would be implicit parameters — these are
        // forbidden in conditional branch bodies (full-input-specification rule).
        if (diagnostics is not null)
        {
            var freeNames = new HashSet<string>();
            var freeOrder = new List<string>();
            var dummyWeights = new Dictionary<string, int>();
            CollectFreeParams(
                body.Output,
                bodyScope,
                bodyCapturedParamNames,
                freeNames,
                freeOrder,
                dummyWeights);
            foreach (var freeName in freeOrder)
            {
                // Find the span for the first occurrence of this free identifier
                var span = FindResolveSpan(body.Output, freeName);
                diagnostics.Add(new Diagnostic(
                    FormatConditionalBranchUndeclaredIdentifier(freeName, branchName),
                    DiagnosticSeverity.Error,
                    span ?? new SourceSpan(0, 0, 0, 0)));
            }
        }

        // Process nested properties normally
        var newProperties = new List<Property>(body.Properties.Count);
        foreach (var prop in body.Properties)
        {
            var processedProp = ProcessAlgorithm(
                prop.Value,
                bodyScope,
                bodyCapturedParamNames,
                diagnostics);
            newProperties.Add(new Property(prop.Name, processedProp, prop.IsPublic, prop.Exposure)
            {
                DeclarationSpans = prop.DeclarationSpans
            });
        }

        // Rewrite only binder names Resolve → Param; leave all others as-is.
        // Process nested blocks/calls normally for their own parameter detection.
        var rewrittenOutput = new List<Expr>(body.Output.Count);
        foreach (var expr in body.Output)
            rewrittenOutput.Add(RewriteBinderRefs(expr, binderNames, bodyScope, capturedParamNames));

        return body with
        {
            Params = [],  // No implicit params — bindings come from pattern matching
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    private static string FormatConditionalBranchUndeclaredIdentifier(string identifierName, string branchName)
        => string.Join(
            Environment.NewLine,
            $"Identifier '{identifierName}' is used in conditional branch '{branchName}', but it is not declared in the branch pattern.",
            "If you want to use a parameter, declare it in the pattern, for example: `A(y) = y`.");

    /// <summary>
    /// Rewrites <see cref="Expr.Resolve"/> → <see cref="Expr.Param"/> ONLY for pattern binder names.
    /// Other identifiers remain as <see cref="Expr.Resolve"/> (lexical lookup at runtime).
    /// Grace wrappers are stripped (they should not appear in conditional bodies, but handle gracefully).
    /// Nested algorithms are processed via <see cref="ProcessAlgorithm"/> for their own scope.
    /// </summary>
    private static Expr RewriteBinderRefs(
        Expr expr,
        HashSet<string> binderNames,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames)
    {
        switch (expr)
        {
            case Expr.Grace(var inner, _):
                // Grace in conditional branch body is a parse error (already reported).
                // Strip it here for error recovery so downstream processing doesn't crash.
                return RewriteBinderRefs(inner, binderNames, scope, capturedParamNames);

            case Expr.Resolve(var name) when ShouldRewriteAsParam(name, binderNames, scope, capturedParamNames):
                return new Expr.Param(name) { Span = expr.Span };

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    RewriteBinderRefs(left, binderNames, scope, capturedParamNames),
                    RewriteBinderRefs(right, binderNames, scope, capturedParamNames)) { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, RewriteBinderRefs(operand, binderNames, scope, capturedParamNames)) { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    RewriteBinderRefs(target, binderNames, scope, capturedParamNames),
                    RewriteBinderRefs(selector, binderNames, scope, capturedParamNames)) { Span = expr.Span };

            case Expr.ResultJoin(var left, var right):
                return new Expr.ResultJoin(
                    RewriteBinderRefs(left, binderNames, scope, capturedParamNames),
                    RewriteBinderRefs(right, binderNames, scope, capturedParamNames)) { Span = expr.Span };

            case Expr.DotCall(var target, var name, null):
                return new Expr.DotCall(
                    RewriteBinderRefs(target, binderNames, scope, capturedParamNames),
                    name) { Span = expr.Span, MemberSpan = ((Expr.DotCall)expr).MemberSpan };

            case Expr.DotCall(var target, var name, var dotArgs):
            {
                var rewrittenTarget = RewriteBinderRefs(target, binderNames, scope, capturedParamNames);
                var nestedCapturedParamNames = UnionNames(capturedParamNames, binderNames);
                if (dotArgs.IsParametrized)
                    return new Expr.DotCall(rewrittenTarget, name, ProcessAlgorithm(dotArgs, scope, nestedCapturedParamNames))
                    {
                        Span = expr.Span,
                        MemberSpan = ((Expr.DotCall)expr).MemberSpan
                    };
                var rewrittenOutput = new List<Expr>(dotArgs.Output.Count);
                foreach (var argExpr in dotArgs.Output)
                    rewrittenOutput.Add(RewriteBinderRefs(argExpr, binderNames, scope, capturedParamNames));
                var processedProps = new List<Property>(dotArgs.Properties.Count);
                foreach (var prop in dotArgs.Properties)
                    processedProps.Add(new Property(prop.Name, ProcessAlgorithm(prop.Value, scope, nestedCapturedParamNames), prop.IsPublic, prop.Exposure)
                    {
                        DeclarationSpans = prop.DeclarationSpans
                    });
                return new Expr.DotCall(rewrittenTarget, name,
                    dotArgs with { Output = rewrittenOutput, Properties = processedProps })
                {
                    Span = expr.Span,
                    MemberSpan = ((Expr.DotCall)expr).MemberSpan
                };
            }

            case Expr.Block(var alg):
                if (alg.IsParametrized)
                {
                    return new Expr.Block(ProcessAlgorithm(alg, scope, UnionNames(capturedParamNames, binderNames))) { Span = expr.Span };
                }
                else
                {
                    var rewrittenOutput = new List<Expr>(alg.Output.Count);
                    foreach (var argExpr in alg.Output)
                        rewrittenOutput.Add(RewriteBinderRefs(argExpr, binderNames, scope, capturedParamNames));
                    var processedProps = new List<Property>(alg.Properties.Count);
                    foreach (var prop in alg.Properties)
                        processedProps.Add(new Property(prop.Name, ProcessAlgorithm(prop.Value, scope, UnionNames(capturedParamNames, binderNames)), prop.IsPublic, prop.Exposure)
                        {
                            DeclarationSpans = prop.DeclarationSpans
                        });
                    return new Expr.Block(alg with { Output = rewrittenOutput, Properties = processedProps }) { Span = expr.Span };
                }

            case Expr.Call(var func, var args):
                if (args.IsParametrized)
                {
                    return new Expr.Call(
                        RewriteBinderRefs(func, binderNames, scope, capturedParamNames),
                        ProcessAlgorithm(args, scope, UnionNames(capturedParamNames, binderNames))) { Span = expr.Span };
                }
                else
                {
                    var rewrittenOutput = new List<Expr>(args.Output.Count);
                    foreach (var argExpr in args.Output)
                        rewrittenOutput.Add(RewriteBinderRefs(argExpr, binderNames, scope, capturedParamNames));
                    var processedProps = new List<Property>(args.Properties.Count);
                    foreach (var prop in args.Properties)
                        processedProps.Add(new Property(prop.Name, ProcessAlgorithm(prop.Value, scope, UnionNames(capturedParamNames, binderNames)), prop.IsPublic, prop.Exposure)
                        {
                            DeclarationSpans = prop.DeclarationSpans
                        });
                    return new Expr.Call(
                        RewriteBinderRefs(func, binderNames, scope, capturedParamNames),
                        args with { Output = rewrittenOutput, Properties = processedProps }) { Span = expr.Span };
                }

            default:
                return expr;
        }
    }

    /// <summary>
    /// Collects identifiers that are free (not defined as properties in any visible scope).
    /// Preserves order of first appearance.
    /// </summary>
    private static void CollectFreeParams(
        IReadOnlyList<Expr> exprs,
        ElaboratedPropertyScope scope,
        HashSet<string> extraBoundNames,
        HashSet<string> paramNames,
        List<string> paramOrder,
        Dictionary<string, int> graceWeights)
    {
        foreach (var expr in exprs)
            CollectFreeParams(expr, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
    }

    private static void CollectFreeParams(
        Expr expr,
        ElaboratedPropertyScope scope,
        HashSet<string> extraBoundNames,
        HashSet<string> paramNames,
        List<string> paramOrder,
        Dictionary<string, int> graceWeights)
    {
        switch (expr)
        {
            case Expr.Grace(Expr.Resolve(var name), var weight):
                if (!IsBoundName(name, scope, extraBoundNames) && name.Length > 0)
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
                CollectFreeParams(inner, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Resolve(var name):
                if (!IsBoundName(name, scope, extraBoundNames) && name.Length > 0)
                {
                    if (paramNames.Add(name))
                        paramOrder.Add(name);
                }
                break;

            case Expr.Binary(_, var left, var right):
                CollectFreeParams(left, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                CollectFreeParams(right, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Unary(_, var operand):
                CollectFreeParams(operand, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Index(var target, var selector):
                CollectFreeParams(target, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                CollectFreeParams(selector, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.ResultJoin(var left, var right):
                CollectFreeParams(left, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                CollectFreeParams(right, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.DotCall(var target, _, null):
                CollectFreeParams(target, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.DotCall(var target, _, var dotArgs):
                CollectFreeParams(target, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                if (dotArgs is not null && !dotArgs.IsParametrized)
                    CollectFreeParams(dotArgs.Output, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Block(var alg):
                // Non-parametrized blocks (e.g. double-parens grouping) are transparent:
                // free identifiers bubble up to the enclosing param scope.
                // Parametrized blocks have their own scope — don't collect.
                if (!alg.IsParametrized)
                    CollectFreeParams(alg.Output, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Call(var func, var args):
                CollectFreeParams(func, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                // Non-parametrized args (parenthesized call): free identifiers belong to the
                // enclosing algorithm. Parametrized args ({} block call): own param scope.
                if (!args.IsParametrized)
                    CollectFreeParams(args.Output, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
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

    private static HashSet<string> UnionNames(HashSet<string> baseNames, IEnumerable<string> extraNames)
    {
        var names = new HashSet<string>(baseNames);
        foreach (var extraName in extraNames)
            names.Add(extraName);
        return names;
    }

    private static bool ShouldRewriteAsParam(
        string name,
        HashSet<string> localParamNames,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames)
        => localParamNames.Contains(name)
            || (capturedParamNames.Contains(name) && !HasVisiblePropertyName(scope, name));

    /// <summary>
    /// Rewrites <see cref="Expr.Resolve"/> to <see cref="Expr.Param"/> for detected parameter names.
    /// Also recursively processes nested algorithms.
    /// </summary>
    private static Expr RewriteParams(
        Expr expr,
        HashSet<string> paramNames,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames)
    {
        switch (expr)
        {
            case Expr.Grace(var inner, _):
                // Strip Grace wrapper — weight has been consumed during collection
                return RewriteParams(inner, paramNames, scope, capturedParamNames);

            case Expr.Resolve(var name) when ShouldRewriteAsParam(name, paramNames, scope, capturedParamNames):
                return new Expr.Param(name) { Span = expr.Span };

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    RewriteParams(left, paramNames, scope, capturedParamNames),
                    RewriteParams(right, paramNames, scope, capturedParamNames)) { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, RewriteParams(operand, paramNames, scope, capturedParamNames)) { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    RewriteParams(target, paramNames, scope, capturedParamNames),
                    RewriteParams(selector, paramNames, scope, capturedParamNames)) { Span = expr.Span };

            case Expr.ResultJoin(var left, var right):
                return new Expr.ResultJoin(
                    RewriteParams(left, paramNames, scope, capturedParamNames),
                    RewriteParams(right, paramNames, scope, capturedParamNames)) { Span = expr.Span };

            case Expr.DotCall(var target, var name, null):
                return new Expr.DotCall(
                    RewriteParams(target, paramNames, scope, capturedParamNames),
                    name) { Span = expr.Span, MemberSpan = ((Expr.DotCall)expr).MemberSpan };

            case Expr.DotCall(var target, var name, var dotArgs):
            {
                var rewrittenTarget = RewriteParams(target, paramNames, scope, capturedParamNames);
                var nestedCapturedParamNames = UnionNames(capturedParamNames, paramNames);
                if (dotArgs.IsParametrized)
                    return new Expr.DotCall(rewrittenTarget, name, ProcessAlgorithm(dotArgs, scope, nestedCapturedParamNames))
                    {
                        Span = expr.Span,
                        MemberSpan = ((Expr.DotCall)expr).MemberSpan
                    };
                var rewrittenOutput = new List<Expr>(dotArgs.Output.Count);
                foreach (var argExpr in dotArgs.Output)
                    rewrittenOutput.Add(RewriteParams(argExpr, paramNames, scope, capturedParamNames));
                var processedProps = new List<Property>(dotArgs.Properties.Count);
                foreach (var prop in dotArgs.Properties)
                    processedProps.Add(new Property(prop.Name, ProcessAlgorithm(prop.Value, scope, nestedCapturedParamNames), prop.IsPublic, prop.Exposure)
                    {
                        DeclarationSpans = prop.DeclarationSpans
                    });
                return new Expr.DotCall(rewrittenTarget, name,
                    dotArgs with { Output = rewrittenOutput, Properties = processedProps })
                {
                    Span = expr.Span,
                    MemberSpan = ((Expr.DotCall)expr).MemberSpan
                };
            }

            case Expr.Block(var alg):
                if (alg.IsParametrized)
                {
                    return new Expr.Block(ProcessAlgorithm(alg, scope, UnionNames(capturedParamNames, paramNames))) { Span = expr.Span };
                }
                else
                {
                    // Non-parametrized block (double-parens grouping): rewrite in enclosing param scope
                    var rewrittenOutput = new List<Expr>(alg.Output.Count);
                    foreach (var argExpr in alg.Output)
                        rewrittenOutput.Add(RewriteParams(argExpr, paramNames, scope, capturedParamNames));
                    var processedProps = new List<Property>(alg.Properties.Count);
                    foreach (var prop in alg.Properties)
                        processedProps.Add(new Property(prop.Name, ProcessAlgorithm(prop.Value, scope, UnionNames(capturedParamNames, paramNames)), prop.IsPublic, prop.Exposure)
                        {
                            DeclarationSpans = prop.DeclarationSpans
                        });
                    return new Expr.Block(alg with { Output = rewrittenOutput, Properties = processedProps }) { Span = expr.Span };
                }

            case Expr.Call(var func, var args):
                if (args.IsParametrized)
                {
                    // Parametrized args ({} block): process as independent algorithm
                    return new Expr.Call(
                        RewriteParams(func, paramNames, scope, capturedParamNames),
                        ProcessAlgorithm(args, scope, UnionNames(capturedParamNames, paramNames))) { Span = expr.Span };
                }
                else
                {
                    // Non-parametrized args (parenthesized call): rewrite output in enclosing
                    // param context, then process any nested properties/blocks within args.
                    var rewrittenOutput = new List<Expr>(args.Output.Count);
                    foreach (var argExpr in args.Output)
                        rewrittenOutput.Add(RewriteParams(argExpr, paramNames, scope, capturedParamNames));
                    var processedProps = new List<Property>(args.Properties.Count);
                    foreach (var prop in args.Properties)
                        processedProps.Add(new Property(prop.Name, ProcessAlgorithm(prop.Value, scope, UnionNames(capturedParamNames, paramNames)), prop.IsPublic, prop.Exposure)
                        {
                            DeclarationSpans = prop.DeclarationSpans
                        });
                    return new Expr.Call(
                        RewriteParams(func, paramNames, scope, capturedParamNames),
                        args with { Output = rewrittenOutput, Properties = processedProps }) { Span = expr.Span };
                }

            default:
                return expr;
        }
    }

    /// <summary>
    /// Processes an expression in a non-parametrized context: just recurse into nested algorithms.
    /// </summary>
    private static Expr ProcessExpr(
        Expr expr,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames)
    {
        return expr switch
        {
            Expr.Grace(var inner, _) => ProcessExpr(inner, scope, capturedParamNames),
            Expr.Block(var alg) => new Expr.Block(
                ProcessAlgorithm(alg, scope, capturedParamNames)) { Span = expr.Span },
            Expr.Call(var func, var args) => new Expr.Call(
                ProcessExpr(func, scope, capturedParamNames),
                ProcessAlgorithm(args, scope, capturedParamNames)) { Span = expr.Span },
            Expr.Binary(var op, var l, var r) => new Expr.Binary(op,
                ProcessExpr(l, scope, capturedParamNames),
                ProcessExpr(r, scope, capturedParamNames)) { Span = expr.Span },
            Expr.Unary(var op, var operand) => new Expr.Unary(op,
                ProcessExpr(operand, scope, capturedParamNames)) { Span = expr.Span },
            Expr.Index(var t, var s) => new Expr.Index(
                ProcessExpr(t, scope, capturedParamNames),
                ProcessExpr(s, scope, capturedParamNames)) { Span = expr.Span },
            Expr.ResultJoin(var l, var r) => new Expr.ResultJoin(
                ProcessExpr(l, scope, capturedParamNames),
                ProcessExpr(r, scope, capturedParamNames)) { Span = expr.Span },
            Expr.DotCall(var t, var n, var da) => new Expr.DotCall(
                ProcessExpr(t, scope, capturedParamNames),
                n,
                da is not null ? ProcessAlgorithm(da, scope, capturedParamNames) : null)
            {
                Span = expr.Span,
                MemberSpan = ((Expr.DotCall)expr).MemberSpan
            },
            _ => expr,
        };
    }

    private static bool IsBoundName(
        string name,
        ElaboratedPropertyScope scope,
        HashSet<string> extraBoundNames)
        => extraBoundNames.Contains(name) || HasVisiblePropertyName(scope, name);

    private static bool HasVisiblePropertyName(ElaboratedPropertyScope scope, string name)
        => ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, name).Count > 0;

    /// <summary>
    /// Finds the <see cref="SourceSpan"/> of the first <see cref="Expr.Resolve"/> with the given name
    /// in a list of expressions. Used for error reporting on free identifiers in conditional branches.
    /// </summary>
    private static SourceSpan? FindResolveSpan(IReadOnlyList<Expr> exprs, string name)
    {
        foreach (var expr in exprs)
        {
            var span = FindResolveSpan(expr, name);
            if (span is not null) return span;
        }
        return null;
    }

    private static SourceSpan? FindResolveSpan(Expr expr, string name)
    {
        return expr switch
        {
            Expr.Resolve(var n) when n == name => expr.Span,
            Expr.Grace(var inner, _) => FindResolveSpan(inner, name),
            Expr.Binary(_, var l, var r) => FindResolveSpan(l, name) ?? FindResolveSpan(r, name),
            Expr.Unary(_, var operand) => FindResolveSpan(operand, name),
            Expr.Index(var t, var s) => FindResolveSpan(t, name) ?? FindResolveSpan(s, name),
            Expr.ResultJoin(var l, var r) => FindResolveSpan(l, name) ?? FindResolveSpan(r, name),
            Expr.DotCall(var t, _, var da) => FindResolveSpan(t, name) ?? (da is not null ? FindResolveSpan(da.Output, name) : null),
            Expr.Block(var alg) => FindResolveSpan(alg.Output, name),
            Expr.Call(var f, var args) => FindResolveSpan(f, name) ?? FindResolveSpan(args.Output, name),
            _ => null,
        };
    }
}
