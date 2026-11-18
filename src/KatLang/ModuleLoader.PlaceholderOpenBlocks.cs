namespace KatLang;

internal sealed partial class ModuleLoader
{
    /// <summary>
    /// A kept branch reports a prelude-rooted block's diagnostics and completes its facts. A placeholder
    /// withholds diagnostics and retracts its resolution. When both hold the same block, give the placeholder
    /// a distinct source view at admission. The region keeps the original raw body for materialization.
    /// </summary>
    private sealed class PlaceholderOpenBlocks
    {
        private enum Reach { Expanded, Kept, Placeholder }

        private readonly Dictionary<object, object> _views = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<object, object> _lists = new(ReferenceEqualityComparer.Instance);

        internal T View<T>(T node) where T : class => _views.TryGetValue(node, out var view) ? (T)view : node;

        internal static PlaceholderOpenBlocks? Find(Algorithm root, HashSet<object> loadBearing, CancellationToken cancellationToken)
        {
            var kept = new HashSet<Algorithm>(ReferenceEqualityComparer.Instance);
            var provisional = new HashSet<Algorithm>(ReferenceEqualityComparer.Instance);
            HashSet<object>[] visited =
            [
                new(ReferenceEqualityComparer.Instance),
                new(ReferenceEqualityComparer.Instance),
                new(ReferenceEqualityComparer.Instance),
            ];
            var postorder = new List<object>();
            var pending = new Stack<(object Node, Reach Mode, bool Finish)>();
            pending.Push((root, Reach.Expanded, false));
            while (pending.TryPop(out var item))
            {
                cancellationToken.ThrowIfCancellationRequested();
                var (node, mode, finish) = item;
                if (finish)
                {
                    postorder.Add(node);
                    continue;
                }
                if (!visited[(int)mode].Add(node) || node is Algorithm { IsModuleRoot: true }) continue;
                if (mode == Reach.Placeholder) pending.Push((node, mode, true));

                // Every other live path goes through the ordinary loader rewrite, which gives the
                // open target a fresh object. Only a kept branch can hold the placeholder's raw head.
                if (mode != Reach.Expanded && node is Algorithm owner)
                    foreach (var open in owner.Opens)
                        if (open.OpenTargetHead() is Expr.AlgorithmExpr { Algorithm.IsModuleRoot: false } head)
                            (mode == Reach.Kept ? kept : provisional).Add(head.Algorithm);

                foreach (var child in Children(node))
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    var reach = mode;
                    if (mode != Reach.Placeholder && node is Algorithm.Conditional && child is Algorithm branch)
                        reach = loadBearing.Contains(branch) ? Reach.Placeholder : Reach.Kept;
                    pending.Push((child, reach, false));
                }
            }

            provisional.IntersectWith(kept);
            if (provisional.Count == 0) return null;

            // Rebuild just the mixed heads and their ancestors in the placeholder, bottom up.
            // A shared expression, argument bundle or body holds one view across all its reaches.
            var result = new PlaceholderOpenBlocks();
            foreach (var node in postorder)
            {
                cancellationToken.ThrowIfCancellationRequested();
                if ((node is Algorithm block && provisional.Contains(block)) || Children(node).Any(result._views.ContainsKey))
                    result._views.Add(node, result.Copy(node));
            }
            result._lists.Clear();
            return result;
        }

        // Only syntax that can lead to an open block. Group every bundle as one node so K holders
        // of the same W slots take O(K + W) work, including in output, capture, list and selector positions.
        private static IEnumerable<object> Children(object node)
        {
            switch (node)
            {
                case Algorithm algorithm:
                    foreach (var open in algorithm.Opens) yield return open;
                    foreach (var property in algorithm.Properties) yield return property.Value;
                    foreach (var branch in algorithm.Branches) yield return branch.Body;
                    if (algorithm is Algorithm.User user) yield return user.Output;
                    if (algorithm is Algorithm.Alias alias) yield return alias.Target;
                    break;
                case Expr.Capture capture: yield return capture.Body; break;
                case Expr.ListLiteral list: yield return list.Items; break;
                case Expr.Index index:
                    yield return index.Target;
                    yield return index.Selectors;
                    break;
                default:
                    for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++) yield return child;
                    break;
            }
        }

        private object Copy(object node) => node switch
        {
            Algorithm.User user => user with
            {
                Opens = Items(user.Opens, View), Properties = Items(user.Properties, PropertyView), Output = View(user.Output),
            },
            Algorithm.Conditional family => family with { Opens = Items(family.Opens, View), Branches = Items(family.Branches, BranchView) },
            Algorithm.Alias alias => alias with
            {
                Opens = Items(alias.Opens, View), Properties = Items(alias.Properties, PropertyView), Target = View(alias.Target),
            },
            Algorithm.Builtin builtin => builtin,
            OutputBundle bundle => bundle.Tail is { } tail ? OutputBundle.Prepend(Items(bundle.Head, View), View(tail))
                : OutputBundle.From(Items(bundle.Head, View)),
            Expr expr => CopyExpr(expr),
            _ => throw new InvalidOperationException("Unexpected node on a placeholder's open-target path."),
        };

        private Expr CopyExpr(Expr expr) => expr switch
        {
            Expr.AlgorithmExpr block => block with { Algorithm = View(block.Algorithm) },
            Expr.Grace grace => grace with { Inner = View(grace.Inner) },
            Expr.Unary unary => unary with { Operand = View(unary.Operand) },
            Expr.Binary binary => binary with { Left = View(binary.Left), Right = View(binary.Right) },
            Expr.Comparison comparison => comparison with { First = View(comparison.First), Links = AstHelpers.RewriteComparisonLinks(comparison.Links, View) },
            Expr.Index index => index with { Target = View(index.Target), Selectors = View(index.Selectors) },
            Expr.SequenceSpread spread => spread with { Operand = View(spread.Operand) },
            Expr.SequenceConstruct join => join with { Left = View(join.Left), Right = View(join.Right) },
            Expr.ListLiteral list => list with { Items = View(list.Items) },
            Expr.Capture capture => capture with { Body = View(capture.Body) },
            Expr.Call call => call with { Function = View(call.Function), Args = View(call.Args) },
            Expr.DotCall dot => dot with
            {
                Target = View(dot.Target), Args = dot.Args is { } args ? View(args) : null,
                LexicalFallback = dot.LexicalFallback is { } fallback ? View(fallback) : null,
            },
            Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence or Expr.Resolve or Expr.NativeCall => expr,
        };

        private Property PropertyView(Property property) => _views.TryGetValue(property.Value, out var body)
            ? property.WithValue((Algorithm)body) : property;

        private CondBranch BranchView(CondBranch branch) => _views.TryGetValue(branch.Body, out var body)
            ? branch with { Body = (Algorithm)body } : branch;

        private IReadOnlyList<T> Items<T>(IReadOnlyList<T> items, Func<T, T> rewrite) where T : class
        {
            if (items.Count == 0) return items;
            if (_lists.TryGetValue(items, out var known)) return (IReadOnlyList<T>)known;
            T[]? copy = null;
            for (var i = 0; i < items.Count; i++)
            {
                var original = items[i];
                var next = rewrite(original);
                if (!ReferenceEquals(original, next))
                {
                    copy ??= items.ToArray();
                    copy[i] = next;
                }
            }
            var result = (IReadOnlyList<T>?)copy ?? items;
            _lists.Add(items, result);
            return result;
        }
    }
}
