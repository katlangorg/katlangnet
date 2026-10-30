namespace KatLang;

internal sealed partial class StaticStructureOperation
{
    /// <summary>Registers externally supplied name classifications, never claiming signature completion.</summary>
    internal void RegisterNameResolvedInput(Algorithm root)
    {
        if (!ReferenceEquals(SourceOf(Root), root)) throw new ArgumentException("The input does not belong to this admission.", nameof(root));
        var pending = new Queue<StaticScopeKey>();
        var seen = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
        Add(Root);
        while (pending.TryDequeue(out var key))
        {
            Queries.EnsureUsable();
            var body = SourceOf(key);
            Publish(key, StaticPublicationStage.Detected, body);
            if (body is Algorithm.Alias) Publish(key, StaticPublicationStage.Resolved, body);
            foreach (var property in body.Properties) Add(ContextOf(key, property.Value));
            if (body is Algorithm.Conditional family)
                foreach (var branch in family.Branches)
                    Add(ContextOf(family.Opens.Count == 0 ? key.Parent ?? Queries.Keys.Root : key, branch.Body, branch.Pattern));
            EnqueueExpressions(body.Opens, Queries.Keys.Root);
            EnqueueExpressions(body.Output, key);
        }

        void Add(StaticScopeKey key)
        {
            if (seen.Contains(key)) return;
            Queries.Resources.Metadata(2);
            seen.Add(key);
            pending.Enqueue(key);
        }

        void EnqueueExpressions(IEnumerable<Expr> expressions, StaticScopeKey declaring)
        {
            var nodes = new Stack<object>();
            var visited = new HashSet<object>(ReferenceEqualityComparer.Instance);
            foreach (var expression in expressions) Push(expression);
            while (nodes.TryPop(out var node))
            {
                Queries.EnsureUsable();
                if (node is Algorithm body) { Add(ContextOf(declaring, body)); continue; }
                for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++) Push(child);
            }
            void Push(object node)
            {
                Queries.Resources.Metadata(0);
                if (visited.Contains(node)) return;
                Queries.Resources.Metadata(2);
                visited.Add(node);
                nodes.Push(node);
            }
        }
    }
}
