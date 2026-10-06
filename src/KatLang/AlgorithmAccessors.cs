namespace KatLang;

/// <summary>
/// The Lean-total read accessors over the closed <see cref="Algorithm"/> hierarchy, for the
/// implementation only: Lean's <c>Algorithm.parent</c>, <c>parameterPatterns</c>,
/// <c>parameters</c>, <c>params</c>, <c>opens</c>, <c>props</c>, <c>output</c>, and
/// <c>branches</c> are TOTAL functions that return the owning variant's field and the empty
/// value (<c>none</c> / <c>[]</c>) for every other constructor. The public type exposes
/// payload only on the variant that owns it (see <see cref="Algorithm"/>), so these C# 14
/// extension properties give the evaluator, the front-end passes, and the semantic model the
/// same total reads under the same names — <c>algorithm.Properties</c> on a base-typed value
/// is <c>Algorithm.props a</c> — without adding a member to the base type.
///
/// <para><b>Read only.</b> An extension property has no <c>init</c> accessor, so no
/// <c>with</c> expression over a base-typed value can name a payload member: a write requires
/// narrowing to the variant that owns the member, which is the whole point. Every accessor is
/// an exhaustive switch expression over the closed hierarchy with no catch-all arm: a new
/// variant fails the build here until its total reads are decided (a base-typed default would
/// silently hand it empty payload).</para>
///
/// <para>When the receiver is statically a variant (<see cref="Algorithm.User"/>,
/// <see cref="Algorithm.Conditional"/>), the variant's own instance member binds instead of
/// the extension, so narrowed code reads the stored field directly.</para>
/// </summary>
internal static class AlgorithmAccessors
{
    extension(Algorithm algorithm)
    {
        /// <summary>Lean: <c>Algorithm.parent</c>; <c>none</c> for a builtin.</summary>
        internal ScopeCtx? Parent => algorithm switch
        {
            Algorithm.User user => user.Parent,
            Algorithm.Conditional family => family.Parent,
            Algorithm.Alias alias => alias.Parent,
            Algorithm.Builtin => null,
        };

        /// <summary>
        /// Lean: <c>Algorithm.parameterPatterns</c>; <c>[]</c> for a builtin, a family, or an alias (an
        /// alias declares no parameter list of its own: its callable's is its target's).
        /// </summary>
        internal IReadOnlyList<ParameterPattern> ParameterPatterns => algorithm switch
        {
            Algorithm.User user => user.ParameterPatterns,
            Algorithm.Builtin or Algorithm.Conditional or Algorithm.Alias => [],
        };

        /// <summary>Lean: <c>Algorithm.parameters</c>; <c>[]</c> for a builtin, a family, or an alias.</summary>
        internal IReadOnlyList<ParameterDeclaration> Parameters => algorithm switch
        {
            Algorithm.User user => user.Parameters,
            Algorithm.Builtin or Algorithm.Conditional or Algorithm.Alias => [],
        };

        /// <summary>Lean: <c>Algorithm.params</c>; <c>[]</c> for a builtin, a family, or an alias.</summary>
        internal IReadOnlyList<string> Params => algorithm switch
        {
            Algorithm.User user => user.Params,
            Algorithm.Builtin or Algorithm.Conditional or Algorithm.Alias => [],
        };

        /// <summary>
        /// Lean: <c>(Algorithm.params a).length</c> — the parameter count without materializing
        /// the projection; <c>0</c> for a builtin, a family, or an alias.
        /// </summary>
        internal int ParameterCount => algorithm switch
        {
            Algorithm.User user => user.ParameterCount,
            Algorithm.Builtin or Algorithm.Conditional or Algorithm.Alias => 0,
        };

        /// <summary>Lean: <c>Algorithm.opens</c>; <c>[]</c> for a builtin.</summary>
        internal IReadOnlyList<Expr> Opens => algorithm switch
        {
            Algorithm.User user => user.Opens,
            Algorithm.Conditional family => family.Opens,
            Algorithm.Alias alias => alias.Opens,
            Algorithm.Builtin => [],
        };

        /// <summary>
        /// Lean: <c>Algorithm.props</c>; <c>[]</c> for a builtin or a family. An alias's are what its own
        /// body declares — never its target's members.
        /// </summary>
        internal IReadOnlyList<Property> Properties => algorithm switch
        {
            Algorithm.User user => user.Properties,
            Algorithm.Alias alias => alias.Properties,
            Algorithm.Builtin or Algorithm.Conditional => [],
        };

        /// <summary>
        /// Lean: <c>Algorithm.output</c>; the empty bundle for a builtin or a family. An alias's is its
        /// ONE written row — the target reference — so the static walks (dependency and exposure
        /// summaries, the structural preflight, the editor) see what the alias reads. The evaluator
        /// never evaluates an alias's output as rows: an alias is normalized to its target first.
        /// </summary>
        internal OutputBundle Output => algorithm switch
        {
            Algorithm.User user => user.Output,
            Algorithm.Alias alias => OutputBundle.From([alias.Target]),
            Algorithm.Builtin or Algorithm.Conditional => OutputBundle.Empty,
        };

        /// <summary>Lean: <c>Algorithm.branches</c>; <c>[]</c> for a builtin, a user algorithm, or an alias.</summary>
        internal IReadOnlyList<CondBranch> Branches => algorithm switch
        {
            Algorithm.Conditional family => family.Branches,
            Algorithm.User or Algorithm.Builtin or Algorithm.Alias => [],
        };

        /// <summary>
        /// <see cref="Algorithm.User.HasExplicitParameterList"/> for a user algorithm; false for
        /// a builtin, a family, or an alias, which have no written parameter list.
        /// </summary>
        internal bool HasExplicitParameterList => algorithm switch
        {
            Algorithm.User user => user.HasExplicitParameterList,
            Algorithm.Builtin or Algorithm.Conditional or Algorithm.Alias => false,
        };

        /// <summary>
        /// Whether this algorithm is the root of a LOADED MODULE (Q-31 H-P / Q-32 I-U, decided
        /// 2026-10-06): the declaration a canonical module URL denotes in this compiled program,
        /// declared at the prelude wherever it is named. Load elaboration marks the root
        /// (<see cref="Algorithm.User.IsModuleElaborated"/>), and a module whose one row is a
        /// callable alias keeps the mark on its alias (<see cref="Algorithm.Alias.IsModuleElaborated"/>).
        /// Lean: a declaration whose identity is <c>PropertyIdentity.module</c>.
        /// </summary>
        internal bool IsModuleRoot => algorithm switch
        {
            Algorithm.User user => user.IsModuleElaborated,
            Algorithm.Alias alias => alias.IsModuleElaborated,
            Algorithm.Builtin or Algorithm.Conditional => false,
        };

        /// <summary>
        /// Lean: <c>Algorithm.findDuplicatePropName</c> — total; <c>none</c> for a builtin or a
        /// family, which declare no properties (<see cref="Algorithm.User.FindDuplicatePropName"/>).
        /// </summary>
        internal string? FindDuplicatePropName() => algorithm switch
        {
            Algorithm.User user => user.FindDuplicatePropName(),
            Algorithm.Alias alias => FirstDuplicatePropertyName(alias.Properties),
            Algorithm.Builtin or Algorithm.Conditional => null,
        };

        /// <summary>
        /// Lean: <c>Algorithm.hasDuplicateBranchPatterns</c> — total; false for a builtin, a user
        /// algorithm, or an alias, which have no branches (<see cref="Algorithm.Conditional.HasDuplicateBranchPatterns"/>).
        /// </summary>
        internal bool HasDuplicateBranchPatterns() => algorithm switch
        {
            Algorithm.Conditional family => family.HasDuplicateBranchPatterns(),
            Algorithm.User or Algorithm.Builtin or Algorithm.Alias => false,
        };
    }

    private static string? FirstDuplicatePropertyName(IReadOnlyList<Property> properties)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var property in properties)
        {
            if (!seen.Add(property.Name))
                return property.Name;
        }

        return null;
    }
}
