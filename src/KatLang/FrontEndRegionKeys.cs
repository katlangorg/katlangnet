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
    private readonly Dictionary<Pattern, int> _patternsToBareForwardingHeads = new(ReferenceEqualityComparer.Instance);
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
        => SpecificationId(pattern, _patternsToSpecifications, FrontEndRegionKeys.ClosedBranchSpecification);

    /// <summary>
    /// The id of the head structure a BARE-FORWARDING branch body reads
    /// (<see cref="FrontEndRegionKeys.BareForwardingBranchHead"/>). Shares the id space of
    /// <see cref="ClosedSpecificationId"/>: a literal-free head renders the same either way and gets
    /// the same id.
    /// </summary>
    internal int BareForwardingHeadId(Pattern pattern)
        => SpecificationId(pattern, _patternsToBareForwardingHeads, FrontEndRegionKeys.BareForwardingBranchHead);

    private int SpecificationId(Pattern pattern, Dictionary<Pattern, int> byPattern, Func<Pattern, string> render)
    {
        if (!byPattern.TryGetValue(pattern, out var id))
        {
            var specification = render(pattern);
            if (!_specifications.TryGetValue(specification, out id))
            {
                id = _specifications.Count + 1;
                _specifications.Add(specification, id);
            }
            byPattern.Add(pattern, id);
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
    /// binder names with their binding kinds and the group boundaries around them — literal items
    /// bind nothing and contribute nothing, while a nested group keeps its boundary and its kind
    /// even when empty. Two patterns with the same rendering impose the same closed specification,
    /// so a body they share rewrites once.
    /// </summary>
    internal static string ClosedBranchSpecification(Pattern pattern) => RenderBranchHead(pattern, includeLiteralPositions: false);

    /// <summary>
    /// The head STRUCTURE a BARE-FORWARDING branch body reads (<c>G(head) = F</c>, FWD-02): the closed
    /// specification plus the POSITION of every literal item, never its value. Bare forwarding
    /// matches a callee parameter pattern only against a head pattern with the same contract, and a
    /// head item that holds a literal (<c>[0, x]</c>) declares no literal-free pattern (<c>[x]</c>),
    /// so literal positions decide what a head can supply while literal values — never forwarded —
    /// decide nothing. The resolver keys a branch body with it only when the body's SHAPE is one bare
    /// written row, whose rewrite is constant work; K literal branches of one shape still share one
    /// region, and a wide shared body keeps the closed specification (FE-1).
    /// </summary>
    internal static string BareForwardingBranchHead(Pattern pattern) => RenderBranchHead(pattern, includeLiteralPositions: true);

    private static string RenderBranchHead(Pattern pattern, bool includeLiteralPositions)
    {
        var builder = new System.Text.StringBuilder();
        // A top-level sequence pattern IS the branch's parameter list; any other top-level
        // pattern is one single parameter position.
        var items = pattern is Pattern.SequenceValue(var topLevelItems) ? topLevelItems : [pattern];
        foreach (var item in items)
            Append(item, builder, includeLiteralPositions);
        return builder.ToString();

        static void Append(Pattern item, System.Text.StringBuilder builder, bool includeLiteralPositions)
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
                        Append(child, builder, includeLiteralPositions);
                    builder.Append(')');
                    break;

                // The structural KIND is part of the specification: a list group forwards as a
                // list, so a body shared by a sequence head and a list head never shares a key.
                case Pattern.ListValue(var list):
                    builder.Append('[');
                    foreach (var child in list)
                        Append(child, builder, includeLiteralPositions);
                    builder.Append(']');
                    break;

                // A literal binds nothing and is never forwarded; only its POSITION shapes what a
                // head can supply, so it renders as one value-blind placeholder ('#' never occurs
                // in a closed specification, so a head with a literal never shares an id with a
                // literal-free one, while heads that differ only in literal values do).
                case Pattern.LitInt or Pattern.LitString or Pattern.LitBool when includeLiteralPositions:
                    builder.Append("#,");
                    break;

                case Pattern.LitInt:
                case Pattern.LitString:
                case Pattern.LitBool:
                    break;

                default:
                    throw new InvalidOperationException(
                        $"Unhandled Pattern variant in {nameof(FrontEndRegionKeys)}.{nameof(RenderBranchHead)}: {item.GetType().Name}.");
            }
        }
    }
}
