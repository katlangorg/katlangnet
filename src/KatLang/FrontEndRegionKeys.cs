namespace KatLang;

/// <summary>
/// One pass's immutable branch-context metadata. Pattern references cache the derivation only;
/// region identity is exact name-set or closed-specification CONTENT. A shared wide pattern is
/// read and canonicalized once, before any of its many branch-body region lookups. No cache is
/// retained by deferred contexts, which keep only the captured binder set.
/// </summary>
internal sealed class BranchContextInterner
{
    internal sealed record NamesContext(IReadOnlySet<string> Names, int Id);
    private readonly NameSetInterner _names = new();
    private readonly Dictionary<Pattern, NamesContext> _patterns = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<IReadOnlySet<string>, int> _sets = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Pattern, int> _patternsToSpecifications = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<string, int> _specifications = new(StringComparer.Ordinal);

    internal NamesContext NamesOf(Pattern pattern)
    {
        if (!_patterns.TryGetValue(pattern, out var context))
        {
            IReadOnlySet<string> names = new HashSet<string>(pattern.BoundNames(), StringComparer.Ordinal);
            context = new(names, NamesId(names));
            _patterns.Add(pattern, context);
        }
        return context;
    }

    internal int NamesId(IReadOnlySet<string> names)
    {
        if (!_sets.TryGetValue(names, out var id))
        {
            id = _names.With(NameSetInterner.Empty, names).Id;
            _sets.Add(names, id);
        }
        return id;
    }

    internal int ClosedSpecificationId(Pattern pattern)
    {
        if (!_patternsToSpecifications.TryGetValue(pattern, out var id))
        {
            var specification = FrontEndRegionKeys.ClosedBranchSpecification(pattern);
            if (!_specifications.TryGetValue(specification, out id))
            {
                id = _specifications.Count + 1;
                _specifications.Add(specification, id);
            }
            _patternsToSpecifications.Add(pattern, id);
        }
        return id;
    }
}

/// <summary>
/// Canonical key fragments for the front-end passes' SEMANTIC-REGION memos (M4). A shared
/// acyclic host AST is processed once per distinct node and semantic region: a node reached
/// again through another path — a second family sharing one branch body, a second parent of
/// one family — is served from a run-local memo whose key is the minimal complete context
/// that can change the node's result. Node and scope identity stay REFERENCE identity in
/// every key (two structurally equal but distinct nodes are distinct regions, exactly like
/// every other front-end memo); the name-set and pattern dimensions below are the only ones
/// compared by CONTENT, because two families that bind the same binder names — or two bodies
/// that captured the same ancestor names — genuinely share the semantic input even though
/// they hold distinct set or pattern objects.
/// </summary>
internal static class FrontEndRegionKeys
{
    /// <summary>
    /// Order-independent identity of a set of names. Empty for the empty set.
    /// </summary>
    internal static string NameSet(IEnumerable<string> names)
    {
        var builder = new System.Text.StringBuilder();
        foreach (var name in names.Order(StringComparer.Ordinal))
            builder.Append(name.Length).Append(':').Append(name);
        return builder.ToString();
    }

    /// <summary>
    /// The CLOSED input specification a conditional branch pattern imposes on its body, as the
    /// resolver derives it (<c>ImplicitArgumentResolver.BranchBinderParameterPatterns</c>): the
    /// binder names with their binding kinds and the sequence-group boundaries around them —
    /// literal items bind nothing and contribute nothing, while a nested group keeps its
    /// boundary even when empty. Two patterns with the same rendering impose the same closed
    /// specification, so a body they share rewrites once.
    /// </summary>
    internal static string ClosedBranchSpecification(Pattern pattern)
    {
        var builder = new System.Text.StringBuilder();
        // A top-level sequence pattern IS the branch's parameter list; any other top-level
        // pattern is one single parameter position.
        var items = pattern is Pattern.SequenceValue(var topLevelItems) ? topLevelItems : [pattern];
        foreach (var item in items)
            Append(item, builder);
        return builder.ToString();

        static void Append(Pattern item, System.Text.StringBuilder builder)
        {
            switch (item)
            {
                case Pattern.Bind binder:
                    builder.Append(binder.Name.Length).Append(':').Append(binder.Name)
                        .Append(':').Append((int)binder.ParameterKind).Append(',');
                    break;

                case Pattern.SequenceValue(var group):
                    builder.Append('(');
                    foreach (var child in group)
                        Append(child, builder);
                    builder.Append(')');
                    break;

                case Pattern.LitInt:
                case Pattern.LitString:
                case Pattern.LitBool:
                    break;

                default:
                    throw new InvalidOperationException(
                        $"Unhandled Pattern variant in {nameof(FrontEndRegionKeys)}.{nameof(ClosedBranchSpecification)}: {item.GetType().Name}.");
            }
        }
    }
}
