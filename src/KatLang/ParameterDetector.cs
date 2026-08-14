namespace KatLang;

/// <summary>
/// Walks a parsed AST and classifies identifiers as parameters vs. algorithm references.
/// For each algorithm scope, identifiers not matching any local property name
    /// or any property name visible from a parent scope or any opened algorithm are converted from
    /// <see cref="Expr.Resolve"/> to <see cref="Expr.Param"/>, and added to the algorithm's
    /// <see cref="Algorithm.Parameters"/> list.
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
    /// <see cref="Algorithm.Parameters"/> lists, along with any diagnostics (e.g. free
    /// identifiers in conditional branch bodies that violate the full-input-specification rule).
    ///
    /// <para><b>Host-AST contract:</b> the root may be a preconstructed (host-built) AST.
    /// A non-recursive structural preflight runs BEFORE this pass's recursive rewriting
    /// walk: a tree whose structural depth exceeds
    /// <see cref="EvaluationLimits.MaxSupportedAstDepth"/> — the shared fat-frame
    /// elaboration ceiling, measured with a ≥2x stack margin for this pass on the
    /// documented 1 MiB thread baseline — or a cyclic node graph is rejected with a
    /// placeholder root and one structured diagnostic instead of overflowing the
    /// process stack. Roots reaching this pass through the front-end pipeline are
    /// already gated and pass unchanged.</para>
    /// </summary>
    public static (Algorithm Root, IReadOnlyList<Diagnostic> Diagnostics) Detect(Algorithm root)
    {
        if (AstStructuralPreflight.Check(
                root,
                EvaluationLimits.MaxSupportedAstDepth,
                AstConsumerProfile.FullyRecursive) is { } structuralRejection)
        {
            return (
                new Algorithm.User(null, [], [], [], []),
                [AstStructuralPreflight.ToParseDiagnostic(
                    structuralRejection, EvaluationLimits.MaxSupportedAstDepth)]);
        }

        return DetectPrevalidated(root);
    }

    /// <summary>
    /// The detection core behind <see cref="Detect"/>, without the structural
    /// preflight. Only for callers that ALREADY gated the tree at the shared
    /// elaboration ceiling (the front-end pipeline's common gate); it must never
    /// become reachable with an unvalidated host tree.
    /// </summary>
    internal static (Algorithm Root, IReadOnlyList<Diagnostic> Diagnostics) DetectPrevalidated(Algorithm root)
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
        if (alg is Algorithm.Builtin)
            return alg;

        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is already a
        // fully-formed elaboration leaf: an explicit N-capture sequence-value pattern, no
        // opens, no properties, and an output that is exactly the single bound target name.
        // Its only required elaboration is rewriting that bound Resolve to a Param. Running
        // it through the general path builds an O(N) param-name set, param-order list,
        // captured-name union, and MergeParameterPatterns per helper, so a wide
        // deconstruction is O(N^2) across its N sibling helpers. This leaf path is O(1) in
        // the capture count and produces the identical elaborated helper.
        if (alg is Algorithm.User { IsAssignmentDeconstructionHelper: true } deconstructionHelper)
            return RewriteAssignmentDeconstructionHelperOutput(deconstructionHelper);

        var newOpens = ProcessOpenExprs(alg.Opens, diagnostics);
        var algWithProcessedOpens = alg with { Opens = newOpens };
        var scope = ElaboratedScopeLookup.CreateScope(algWithProcessedOpens, parentScope);

        var paramNames = new HashSet<string>(alg.Params);
        var paramOrder = new List<string>(alg.Params);
        var graceWeights = new Dictionary<string, int>();
        var hasExplicitParameterList = alg.ExplicitParameterPatterns.Count > 0;

        // Ordinary nested algorithms close over already-known outer params.
        // These should rewrite to Expr.Param but must not become new local params.
        var boundNames = UnionNames(capturedParamNames, alg.Params);

        if (hasExplicitParameterList)
        {
            ReportUndeclaredExplicitParameterNames(alg.Output, scope, boundNames, diagnostics);
        }
        else
        {
            CollectFreeParams(alg.Output, scope, boundNames, paramNames, paramOrder, graceWeights);

            if (graceWeights.Count > 0)
                ApplyGraceReordering(paramOrder, graceWeights);
        }

        var nestedCapturedParamNames = UnionNames(capturedParamNames, paramOrder);

        // Process properties recursively (each property body is an algorithm scope)
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

        // Rewrite Resolve → Param for detected parameters
        var rewrittenOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
            rewrittenOutput.Add(RewriteParams(expr, paramNames, scope, capturedParamNames));

        return algWithProcessedOpens.WithParams(paramOrder) with
        {
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    /// <summary>
    /// Cheap elaboration of a synthetic assignment-deconstruction helper. The general
    /// <see cref="ProcessAlgorithm"/> path would rewrite the helper's output <see cref="Expr.Resolve"/>
    /// to an <see cref="Expr.Param"/> (the target is one of the helper's explicit captures), so this
    /// does exactly that and nothing else. The helper carries no free identifiers, no opens, and no
    /// nested algorithms, so no scope, param-name set, or pattern merge is needed — only the output
    /// rewrite. Every output slot of such a helper is a bare reference to a bound capture by
    /// construction (see <c>Parser.AddDeconstructionProperties</c>), so the rewrite is unconditional.
    /// </summary>
    private static Algorithm RewriteAssignmentDeconstructionHelperOutput(Algorithm.User helper)
    {
        var rewrittenOutput = new List<Expr>(helper.Output.Count);
        foreach (var expr in helper.Output)
            rewrittenOutput.Add(expr is Expr.Resolve resolve ? new Expr.Param(resolve.Name) { Span = expr.Span } : expr);
        return helper with { Output = rewrittenOutput };
    }

    private static IReadOnlyList<Expr> ProcessOpenExprs(
        IReadOnlyList<Expr> opens,
        List<Diagnostic>? diagnostics)
    {
        if (opens.Count == 0)
            return opens;

        var openParentScope = ElaboratedScopeLookup.CreateScope(BuiltinRegistry.CreateSemanticPreludeAlgorithm());
        var processed = new List<Expr>(opens.Count);
        foreach (var open in opens)
            processed.Add(ProcessOpenExpr(open, openParentScope, diagnostics));
        return processed;
    }

    private static Expr ProcessOpenExpr(
        Expr expr,
        ElaboratedPropertyScope openParentScope,
        List<Diagnostic>? diagnostics)
    {
        switch (expr)
        {
            case Expr.AlgorithmExpr(var algorithm):
                return new Expr.AlgorithmExpr(ProcessAlgorithm(algorithm, openParentScope, [], diagnostics)) { Span = expr.Span };

            case Expr.Capture(var captureBody):
                // A capture target owns no scope: its rows are processed in the
                // open-target parent scope (the pre-split transparent wrapper
                // added only an empty lookup level here).
                return new Expr.Capture(new OutputBundle(
                    captureBody.Select(row => ProcessExpr(row, openParentScope, [])).ToList()))
                { Span = expr.Span };

            case Expr.DotCall dotCall:
                // `with` keeps the stored dot-edge facts (member span,
                // resolution mode, marker span). Open targets are ordinary
                // structural paths, so the fallback identity is inert here,
                // but the detector is the normalization owner: every DotCall
                // it emits carries an EXPLICIT fallback (null is only a
                // host-construction shorthand for Resolve(Name)).
                return dotCall with
                {
                    Target = ProcessOpenExpr(dotCall.Target, openParentScope, diagnostics),
                    Args = dotCall.Args is { } dotArgs
                        ? new OutputBundle(dotArgs.Select(argExpr => ProcessExpr(argExpr, openParentScope, [])).ToList())
                        : null,
                    LexicalFallback = dotCall.EffectiveLexicalFallback,
                };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    ProcessOpenExpr(operand, openParentScope, diagnostics))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    ProcessOpenExpr(left, openParentScope, diagnostics),
                    ProcessOpenExpr(right, openParentScope, diagnostics)) { Span = expr.Span };

            case Expr.ListLiteral(var items):
                return new Expr.ListLiteral(
                    items.Select(item => ProcessOpenExpr(item, openParentScope, diagnostics)).ToList())
                { Span = expr.Span };

            case Expr.Call(var function, var args):
                return new Expr.Call(
                    ProcessOpenExpr(function, openParentScope, diagnostics),
                    new OutputBundle(args.Select(argExpr => ProcessExpr(argExpr, openParentScope, [])).ToList())) { Span = expr.Span };

            default:
                return expr;
        }
    }

    /// <summary>
    /// Processes a conditional branch body under the full-input-specification rule:
    /// - Pattern binder names are rewritten to <see cref="Expr.Param"/> (resolved via valEnv at runtime).
    /// - No other free identifiers become implicit parameters.
    /// - The branch body's <see cref="Algorithm.Parameters"/> list is empty.
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
            Parameters = [],  // No implicit params — bindings come from pattern matching
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    private static string FormatConditionalBranchUndeclaredIdentifier(string identifierName, string branchName)
        => string.Join(
            Environment.NewLine,
            $"Identifier '{identifierName}' is used in conditional branch '{branchName}', but it is not declared in the branch pattern.",
            "If you want to use a parameter, declare it in the pattern, for example: `A(y) = y`.");

    private static string FormatExplicitParameterUndeclaredIdentifier(string identifierName)
        => string.Join(
            Environment.NewLine,
            $"Identifier '{identifierName}' is used in an explicitly parameterized algorithm, but it is not declared in the parameter list.",
            "Explicit parameter lists are closed. Declare the parameter explicitly or define a visible property/opened name.");

    private static void ReportUndeclaredExplicitParameterNames(
        IReadOnlyList<Expr> output,
        ElaboratedPropertyScope scope,
        HashSet<string> boundNames,
        List<Diagnostic>? diagnostics)
    {
        if (diagnostics is null)
            return;

        var freeNames = new HashSet<string>();
        var freeOrder = new List<string>();
        var dummyWeights = new Dictionary<string, int>();
        CollectFreeParams(output, scope, boundNames, freeNames, freeOrder, dummyWeights);

        foreach (var freeName in freeOrder)
        {
            var span = FindResolveSpan(output, freeName);
            diagnostics.Add(new Diagnostic(
                FormatExplicitParameterUndeclaredIdentifier(freeName),
                DiagnosticSeverity.Error,
                span ?? new SourceSpan(0, 0, 0, 0)));
        }
    }

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

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    RewriteBinderRefs(operand, binderNames, scope, capturedParamNames))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    RewriteBinderRefs(left, binderNames, scope, capturedParamNames),
                    RewriteBinderRefs(right, binderNames, scope, capturedParamNames)) { Span = expr.Span };

            case Expr.ListLiteral(var items):
                return new Expr.ListLiteral(
                    items.Select(item => RewriteBinderRefs(item, binderNames, scope, capturedParamNames)).ToList())
                { Span = expr.Span };

            case Expr.DotCall dotCall:
            {
                // Argument bundles own no scope: slots rewrite in the enclosing
                // binder scope, exactly like capture rows. The stored
                // lexical-fallback identity rewrites by the SAME rule as a bare
                // callee name (Resolve → Param when the member is a known
                // binder), for BOTH resolution modes.
                OutputBundle? rewrittenArgs = null;
                if (dotCall.Args is { } dotArgs)
                {
                    var rewrittenSlots = new List<Expr>(dotArgs.Count);
                    foreach (var argExpr in dotArgs)
                        rewrittenSlots.Add(RewriteBinderRefs(argExpr, binderNames, scope, capturedParamNames));
                    rewrittenArgs = new OutputBundle(rewrittenSlots);
                }

                return dotCall with
                {
                    Target = RewriteBinderRefs(dotCall.Target, binderNames, scope, capturedParamNames),
                    Args = rewrittenArgs,
                    LexicalFallback = RewriteBinderRefs(dotCall.EffectiveLexicalFallback, binderNames, scope, capturedParamNames),
                };
            }

            case Expr.AlgorithmExpr(var alg):
                return new Expr.AlgorithmExpr(ProcessAlgorithm(alg, scope, UnionNames(capturedParamNames, binderNames))) { Span = expr.Span };

            case Expr.Capture(var captureBody):
                {
                    // Captures are transparent: rows rewrite in the enclosing
                    // binder scope (no scope of their own, no properties).
                    var rewrittenRows = new List<Expr>(captureBody.Count);
                    foreach (var row in captureBody)
                        rewrittenRows.Add(RewriteBinderRefs(row, binderNames, scope, capturedParamNames));
                    return new Expr.Capture(new OutputBundle(rewrittenRows)) { Span = expr.Span };
                }

            case Expr.Call(var func, var args):
            {
                // Argument bundles own no scope: slots rewrite in the enclosing
                // binder scope.
                var rewrittenArgs = new List<Expr>(args.Count);
                foreach (var argExpr in args)
                    rewrittenArgs.Add(RewriteBinderRefs(argExpr, binderNames, scope, capturedParamNames));
                return new Expr.Call(
                    RewriteBinderRefs(func, binderNames, scope, capturedParamNames),
                    new OutputBundle(rewrittenArgs)) { Span = expr.Span };
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

            case Expr.SequenceSpread(var operand):
                CollectFreeParams(operand, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectFreeParams(left, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                CollectFreeParams(right, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.ListLiteral(var items):
                // List-literal elements are transparent to the enclosing
                // parameter scope, like spread operands and sequence joins.
                foreach (var item in items)
                    CollectFreeParams(item, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.DotCall dotCall:
                CollectFreeParams(dotCall.Target, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                // EXTENSION dot (`a~.t` / `a.~t`): the member is a
                // callable-name occurrence and participates in ordinary
                // free-name analysis through its stored lexical-fallback
                // identity, so `K = a~.t` infers the same parameters as
                // `K = t(a)`. ORDINARY dot deliberately contributes nothing
                // here: the member may be a structural property of the runtime
                // receiver, so it never becomes an implicit parameter merely
                // because a lexical fallback path exists.
                if (dotCall.ResolutionMode == DotResolutionMode.ExtensionOnly)
                    CollectFreeParams(dotCall.EffectiveLexicalFallback, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                if (dotCall.Args is { } dotArgs)
                    CollectFreeParams(dotArgs, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.Capture(var captureBody):
                // Captures are transparent: free identifiers bubble up to the
                // enclosing param scope.
                CollectFreeParams(captureBody, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                break;

            case Expr.AlgorithmExpr:
                // Scope-owning algorithm expressions own their names — don't collect.
                break;

            case Expr.Call(var func, var args):
                CollectFreeParams(func, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
                // Argument bundles are transparent: free identifiers inside
                // argument slots belong to the enclosing algorithm. (A brace
                // block argument is an AlgorithmExpr slot and owns its names.)
                CollectFreeParams(args, scope, extraBoundNames, paramNames, paramOrder, graceWeights);
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
            || (capturedParamNames.Contains(name) && !HasVisibleNonBuiltinPropertyName(scope, name));

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

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    RewriteParams(operand, paramNames, scope, capturedParamNames))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    RewriteParams(left, paramNames, scope, capturedParamNames),
                    RewriteParams(right, paramNames, scope, capturedParamNames)) { Span = expr.Span };

            case Expr.ListLiteral(var items):
                return new Expr.ListLiteral(
                    items.Select(item => RewriteParams(item, paramNames, scope, capturedParamNames)).ToList())
                { Span = expr.Span };

            case Expr.DotCall dotCall:
            {
                // Argument bundles own no scope: slots rewrite in the enclosing
                // param context. The stored lexical-fallback identity rewrites
                // by the SAME rule as a bare callee name (Resolve → Param when
                // the member is a known local or captured parameter), for BOTH
                // resolution modes: ordinary dot rewrites already-known
                // parameters here without ever collecting new ones.
                OutputBundle? rewrittenArgs = null;
                if (dotCall.Args is { } dotArgs)
                {
                    var rewrittenSlots = new List<Expr>(dotArgs.Count);
                    foreach (var argExpr in dotArgs)
                        rewrittenSlots.Add(RewriteParams(argExpr, paramNames, scope, capturedParamNames));
                    rewrittenArgs = new OutputBundle(rewrittenSlots);
                }

                return dotCall with
                {
                    Target = RewriteParams(dotCall.Target, paramNames, scope, capturedParamNames),
                    Args = rewrittenArgs,
                    LexicalFallback = RewriteParams(dotCall.EffectiveLexicalFallback, paramNames, scope, capturedParamNames),
                };
            }

            case Expr.AlgorithmExpr(var alg):
                return new Expr.AlgorithmExpr(ProcessAlgorithm(alg, scope, UnionNames(capturedParamNames, paramNames))) { Span = expr.Span };

            case Expr.Capture(var captureBody):
                {
                    // Captures are transparent: rewrite rows in the enclosing param scope.
                    var rewrittenRows = new List<Expr>(captureBody.Count);
                    foreach (var row in captureBody)
                        rewrittenRows.Add(RewriteParams(row, paramNames, scope, capturedParamNames));
                    return new Expr.Capture(new OutputBundle(rewrittenRows)) { Span = expr.Span };
                }

            case Expr.Call(var func, var args):
            {
                // Argument bundles own no scope: slots rewrite in the enclosing
                // param context. (A brace block argument is an AlgorithmExpr
                // slot and processes as an independent algorithm.)
                var rewrittenArgs = new List<Expr>(args.Count);
                foreach (var argExpr in args)
                    rewrittenArgs.Add(RewriteParams(argExpr, paramNames, scope, capturedParamNames));
                return new Expr.Call(
                    RewriteParams(func, paramNames, scope, capturedParamNames),
                    new OutputBundle(rewrittenArgs)) { Span = expr.Span };
            }

            default:
                return expr;
        }
    }

    /// <summary>
    /// Processes an expression in a transparent context (capture rows, list elements,
    /// argument slots): just recurse into nested algorithms.
    /// </summary>
    private static Expr ProcessExpr(
        Expr expr,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames)
    {
        return expr switch
        {
            Expr.Grace(var inner, _) => ProcessExpr(inner, scope, capturedParamNames),
            Expr.AlgorithmExpr(var alg) => new Expr.AlgorithmExpr(
                ProcessAlgorithm(alg, scope, capturedParamNames)) { Span = expr.Span },
            Expr.Capture(var captureBody) => new Expr.Capture(new OutputBundle(
                captureBody.Select(row => ProcessExpr(row, scope, capturedParamNames)).ToList()))
            { Span = expr.Span },
            Expr.Call(var func, var args) => new Expr.Call(
                ProcessExpr(func, scope, capturedParamNames),
                new OutputBundle(args.Select(argExpr => ProcessExpr(argExpr, scope, capturedParamNames)).ToList())) { Span = expr.Span },
            Expr.Binary(var op, var l, var r) => new Expr.Binary(op,
                ProcessExpr(l, scope, capturedParamNames),
                ProcessExpr(r, scope, capturedParamNames)) { Span = expr.Span },
            Expr.Unary(var op, var operand) => new Expr.Unary(op,
                ProcessExpr(operand, scope, capturedParamNames)) { Span = expr.Span },
            Expr.Index(var t, var s) => new Expr.Index(
                ProcessExpr(t, scope, capturedParamNames),
                ProcessExpr(s, scope, capturedParamNames)) { Span = expr.Span },
            Expr.SequenceSpread(var operand) => new Expr.SequenceSpread(
                ProcessExpr(operand, scope, capturedParamNames))
            {
                Span = expr.Span,
                SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
            },
            Expr.SequenceConstruct(var l, var r) => new Expr.SequenceConstruct(
                ProcessExpr(l, scope, capturedParamNames),
                ProcessExpr(r, scope, capturedParamNames)) { Span = expr.Span },
            Expr.ListLiteral(var items) => new Expr.ListLiteral(
                items.Select(item => ProcessExpr(item, scope, capturedParamNames)).ToList())
            { Span = expr.Span },
            // The detector is the normalization owner: every DotCall it emits
            // carries an EXPLICIT fallback identity (null is only a
            // host-construction shorthand for Resolve(Name)).
            Expr.DotCall dotCall => dotCall with
            {
                Target = ProcessExpr(dotCall.Target, scope, capturedParamNames),
                Args = dotCall.Args is { } da
                    ? new OutputBundle(da.Select(argExpr => ProcessExpr(argExpr, scope, capturedParamNames)).ToList())
                    : null,
                LexicalFallback = dotCall.EffectiveLexicalFallback,
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

    private static bool HasVisibleNonBuiltinPropertyName(ElaboratedPropertyScope scope, string name)
        => ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, name)
            .Any(static hit => hit.Property.Value is not Algorithm.Builtin);

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
            Expr.SequenceConstruct(var l, var r) => FindResolveSpan(l, name) ?? FindResolveSpan(r, name),
            Expr.SequenceSpread(var operand) => FindResolveSpan(operand, name),
            Expr.ListLiteral(var items) => FindResolveSpan(items, name),
            Expr.DotCall d => FindResolveSpan(d.Target, name)
                ?? (d.ResolutionMode == DotResolutionMode.ExtensionOnly
                    ? FindResolveSpan(d.EffectiveLexicalFallback, name)
                    : null)
                ?? (d.Args is not null ? FindResolveSpan(d.Args, name) : null),
            Expr.AlgorithmExpr(var alg) => FindResolveSpan(alg.Output, name),
            Expr.Capture(var captureBody) => FindResolveSpan(captureBody, name),
            Expr.Call(var f, var args) => FindResolveSpan(f, name) ?? FindResolveSpan(args, name),
            _ => null,
        };
    }
}
