namespace KatLang;

/// <summary>
/// The ONE source-coordinate boundary of module elaboration (Task 3a: one coordinate
/// space per result). A fetched module is parsed as its own document — its parse
/// diagnostics are positioned in ITS text and never leave the loader except as a
/// caller-local <c>load:</c> failure at the load site — and the tree that crosses into
/// the loading document's result is its IMPORT VIEW: the same declarations with every
/// source location removed. Nothing in the loading document's result may then present a
/// module-relative line/column as a position in that document; a location an imported
/// construct is later reported at is one the current document supplies (the evaluator's
/// attach-if-missing rule at the demanding expression, the front end's import-site anchor
/// for a diagnostic raised inside the view, the load site for nested module loads).
/// </summary>
internal sealed partial class ModuleLoader
{
    /// <summary>
    /// Rewrites a freshly parsed module root into its locationless import view. Every
    /// source-position field the parser populates is cleared — <see cref="Expr.Span"/>,
    /// <see cref="Expr.DotCall.MemberSpan"/>, <see cref="Expr.SequenceSpread.SpreadMarkerSpan"/>,
    /// <see cref="Property.DeclarationSpans"/>, parameter declaration and collect-marker
    /// spans, and binder-pattern spans — while everything else is carried through the
    /// record copy: declaration identity (a <c>with</c> copy is a view of the same
    /// declaration), deferred-region and provenance slots, deconstruction metadata,
    /// exposure, and the written parameter-list bit. Reference-identity memoized so a
    /// shared subtree stays shared in the view, and identity-preserving for a subtree
    /// that carries no location at all (returned as the same instance). Applied ONCE per
    /// fetched module, before nested loads are elaborated and before the module enters
    /// the cache, so every splice — first or cached, eager or deferred — shares one
    /// caller-independent view.
    /// </summary>
    /// <remarks>
    /// Recursive like the loader's own walks, on the tree the raw-syntax structural
    /// preflight has just admitted at the nested allowance, with the same stack-reserve
    /// probe (<see cref="ThrowIfInsufficientStack"/>) at every level.
    /// </remarks>
    private static Algorithm.User ToImportView(Algorithm.User parsedModuleRoot)
        => (Algorithm.User)new ImportViewRewriter().Rewrite(parsedModuleRoot);

    private sealed class ImportViewRewriter
    {
        private readonly Dictionary<Algorithm, Algorithm> _algorithms = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Expr, Expr> _expressions = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Property, Property> _properties = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Pattern, Pattern> _patterns = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<ParameterPattern, ParameterPattern> _parameterPatterns = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<object, object> _lists = new(ReferenceEqualityComparer.Instance);

        public Algorithm Rewrite(Algorithm algorithm)
        {
            ThrowIfInsufficientStack();
            if (_algorithms.TryGetValue(algorithm, out var memoized))
                return memoized;

            // Compiler-exhaustive over the closed Algorithm hierarchy: a new variant is a
            // build error here until its location-bearing payload is decided.
            Algorithm rewritten = algorithm switch
            {
                Algorithm.Builtin => algorithm,
                Algorithm.User user => RewriteUser(user),
                Algorithm.Conditional conditional => RewriteConditional(conditional),
            };
            _algorithms[algorithm] = rewritten;
            return rewritten;
        }

        private Algorithm RewriteUser(Algorithm.User user)
        {
            var patterns = RewriteList(user.ParameterPatterns, RewriteParameterPattern);
            var opens = RewriteList(user.Opens, Rewrite);
            var properties = RewriteList(user.Properties, RewriteProperty);
            var output = RewriteBundle(user.Output);
            if (ReferenceEquals(patterns, user.ParameterPatterns)
                && ReferenceEquals(opens, user.Opens)
                && ReferenceEquals(properties, user.Properties)
                && ReferenceEquals(output, user.Output))
            {
                return user;
            }

            return user with
            {
                ParameterPatterns = patterns,
                Opens = opens,
                Properties = properties,
                Output = output,
            };
        }

        private Algorithm RewriteConditional(Algorithm.Conditional conditional)
        {
            var opens = RewriteList(conditional.Opens, Rewrite);
            var branches = RewriteList(conditional.Branches, RewriteBranch);
            return ReferenceEquals(opens, conditional.Opens) && ReferenceEquals(branches, conditional.Branches)
                ? conditional
                : conditional with { Opens = opens, Branches = branches };
        }

        private CondBranch RewriteBranch(CondBranch branch)
        {
            var pattern = RewritePattern(branch.Pattern);
            var body = Rewrite(branch.Body);
            return ReferenceEquals(pattern, branch.Pattern) && ReferenceEquals(body, branch.Body)
                ? branch
                : new CondBranch(pattern, body);
        }

        private Property RewriteProperty(Property property)
        {
            if (_properties.TryGetValue(property, out var memoized))
                return memoized;

            var value = Rewrite(property.Value);
            var rewritten = property.DeclarationSpans.Count == 0 && ReferenceEquals(value, property.Value)
                ? property
                : property with { Value = value, DeclarationSpans = [] };
            _properties[property] = rewritten;
            return rewritten;
        }

        private Pattern RewritePattern(Pattern pattern)
        {
            if (_patterns.TryGetValue(pattern, out var memoized))
                return memoized;

            // Compiler-exhaustive over the closed Pattern hierarchy.
            Pattern rewritten = pattern switch
            {
                Pattern.Bind bind => bind.NameSpan is null && bind.CollectMarkerSpan is null
                    ? bind
                    : bind with { NameSpan = null, CollectMarkerSpan = null },
                Pattern.LitInt or Pattern.LitString or Pattern.LitBool => pattern,
                Pattern.SequenceValue sequence => RewriteList(sequence.Items, RewritePattern) is var items
                    && ReferenceEquals(items, sequence.Items)
                    ? sequence
                    : new Pattern.SequenceValue(items),
            };
            _patterns[pattern] = rewritten;
            return rewritten;
        }

        private ParameterPattern RewriteParameterPattern(ParameterPattern pattern)
        {
            if (_parameterPatterns.TryGetValue(pattern, out var memoized))
                return memoized;

            // Compiler-exhaustive over the closed ParameterPattern hierarchy. The capture
            // leaf keeps its held declaration's identity-carrying provenance slot.
            ParameterPattern rewritten = pattern switch
            {
                CaptureParameterPattern capture => capture.Span is null && capture.CollectMarkerSpan is null
                    ? capture
                    : capture with { Parameter = capture.Parameter with { Span = null, CollectMarkerSpan = null } },
                SequenceValueParameterPattern sequence => RewriteList(sequence.Items, RewriteParameterPattern) is var items
                    && ReferenceEquals(items, sequence.Items)
                    ? sequence
                    : new SequenceValueParameterPattern(items),
            };
            _parameterPatterns[pattern] = rewritten;
            return rewritten;
        }

        public Expr Rewrite(Expr expr)
        {
            ThrowIfInsufficientStack();
            if (_expressions.TryGetValue(expr, out var memoized))
                return memoized;

            var rewritten = RewriteCore(expr);
            _expressions[expr] = rewritten;
            return rewritten;
        }

        // Compiler-exhaustive over the closed Expr hierarchy: a new variant is a build error
        // here until its location-bearing payload and children are decided.
        private Expr RewriteCore(Expr expr) => expr switch
        {
            // Childless leaves: only their own span can carry a location.
            Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence or Expr.Resolve or Expr.NativeCall
                => expr.Span is null ? expr : expr with { Span = null },

            Expr.Unary unary => Rewrite(unary.Operand) is var operand
                && ReferenceEquals(operand, unary.Operand) && unary.Span is null
                ? unary
                : unary with { Operand = operand, Span = null },

            Expr.Binary binary => (Rewrite(binary.Left), Rewrite(binary.Right)) is var (left, right)
                && ReferenceEquals(left, binary.Left) && ReferenceEquals(right, binary.Right) && binary.Span is null
                ? binary
                : binary with { Left = left, Right = right, Span = null },

            Expr.Comparison comparison => RewriteComparison(comparison),

            Expr.Index index => (Rewrite(index.Target), Rewrite(index.Selector)) is var (target, selector)
                && ReferenceEquals(target, index.Target) && ReferenceEquals(selector, index.Selector) && index.Span is null
                ? index
                : index with { Target = target, Selector = selector, Span = null },

            Expr.SequenceConstruct join => (Rewrite(join.Left), Rewrite(join.Right)) is var (left, right)
                && ReferenceEquals(left, join.Left) && ReferenceEquals(right, join.Right) && join.Span is null
                ? join
                : join with { Left = left, Right = right, Span = null },

            Expr.SequenceSpread spread => Rewrite(spread.Operand) is var operand
                && ReferenceEquals(operand, spread.Operand) && spread.Span is null && spread.SpreadMarkerSpan is null
                ? spread
                : spread with { Operand = operand, Span = null, SpreadMarkerSpan = null },

            Expr.ListLiteral list => RewriteBundle(list.Items) is var items
                && ReferenceEquals(items, list.Items) && list.Span is null
                ? list
                : list with { Items = items, Span = null },

            Expr.DotCall dotCall => RewriteDotCall(dotCall),

            Expr.Grace grace => Rewrite(grace.Inner) is var inner
                && ReferenceEquals(inner, grace.Inner) && grace.Span is null
                ? grace
                : grace with { Inner = inner, Span = null },

            Expr.AlgorithmExpr block => Rewrite(block.Algorithm) is var algorithm
                && ReferenceEquals(algorithm, block.Algorithm) && block.Span is null
                ? block
                : block with { Algorithm = algorithm, Span = null },

            Expr.Capture capture => RewriteBundle(capture.Body) is var body
                && ReferenceEquals(body, capture.Body) && capture.Span is null
                ? capture
                : capture with { Body = body, Span = null },

            Expr.Call call => (Rewrite(call.Function), RewriteBundle(call.Args)) is var (function, args)
                && ReferenceEquals(function, call.Function) && ReferenceEquals(args, call.Args) && call.Span is null
                ? call
                : call with { Function = function, Args = args, Span = null },
        };

        private Expr RewriteDotCall(Expr.DotCall dotCall)
        {
            var target = Rewrite(dotCall.Target);
            var args = dotCall.Args is { } writtenArgs ? RewriteBundle(writtenArgs) : null;
            // The stored fallback identity is a real child (a raw tree may hold the member's
            // Resolve, possibly Grace-wrapped); null stays the unelaborated default.
            var fallback = dotCall.LexicalFallback is { } storedFallback ? Rewrite(storedFallback) : null;
            if (ReferenceEquals(target, dotCall.Target)
                && ReferenceEquals(args, dotCall.Args)
                && ReferenceEquals(fallback, dotCall.LexicalFallback)
                && dotCall.Span is null
                && dotCall.MemberSpan is null)
            {
                return dotCall;
            }

            // `with` keeps the stored elaboration facts and the provenance slot.
            return dotCall with
            {
                Target = target,
                Args = args,
                LexicalFallback = fallback,
                Span = null,
                MemberSpan = null,
            };
        }

        private OutputBundle RewriteBundle(OutputBundle bundle)
        {
            if (bundle.Count == 0)
                return bundle;
            if (_lists.TryGetValue(bundle, out var memoized))
                return (OutputBundle)memoized;

            Expr[]? rewrittenItems = null;
            for (var index = 0; index < bundle.Count; index++)
            {
                var item = bundle[index];
                var rewritten = Rewrite(item);
                if (rewrittenItems is null && !ReferenceEquals(rewritten, item))
                {
                    rewrittenItems = new Expr[bundle.Count];
                    for (var copied = 0; copied < index; copied++)
                        rewrittenItems[copied] = bundle[copied];
                }

                if (rewrittenItems is not null)
                    rewrittenItems[index] = rewritten;
            }

            var result = rewrittenItems is null ? bundle : OutputBundle.TakeOwnership(rewrittenItems);
            _lists[bundle] = result;
            return result;
        }

        /// <summary>
        /// Rewrites a caller-owned list element-wise, returning the SAME list instance when
        /// no element changed (a host-visible list stays the host's) and a fresh list
        /// otherwise; memoized per list instance so a list shared by several owners (the
        /// deconstruction helpers' one pattern list) is rewritten once and stays shared.
        /// </summary>
        /// <summary>
        /// A comparison chain keeps its instance when neither its first operand, any link
        /// operand, nor its own span changes; otherwise the links are rewritten through the
        /// ONE link rewriter and the node loses its location like every other expression.
        /// </summary>
        private Expr RewriteComparison(Expr.Comparison comparison)
        {
            var first = Rewrite(comparison.First);
            var links = AstHelpers.RewriteComparisonLinks(comparison.Links, Rewrite);
            return ReferenceEquals(first, comparison.First) && ReferenceEquals(links, comparison.Links) && comparison.Span is null
                ? comparison
                : comparison with { First = first, Links = links, Span = null };
        }

        private IReadOnlyList<T> RewriteList<T>(IReadOnlyList<T> items, Func<T, T> rewrite)
            where T : class
        {
            if (items.Count == 0)
                return items;
            if (_lists.TryGetValue(items, out var memoized))
                return (IReadOnlyList<T>)memoized;

            List<T>? rewrittenItems = null;
            for (var index = 0; index < items.Count; index++)
            {
                var item = items[index];
                var rewritten = rewrite(item);
                if (rewrittenItems is null && !ReferenceEquals(rewritten, item))
                {
                    rewrittenItems = new List<T>(items.Count);
                    for (var copied = 0; copied < index; copied++)
                        rewrittenItems.Add(items[copied]);
                }

                rewrittenItems?.Add(rewritten);
            }

            IReadOnlyList<T> result = rewrittenItems ?? items;
            _lists[items] = result;
            return result;
        }
    }
}
