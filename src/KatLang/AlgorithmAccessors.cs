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
            Algorithm.Builtin => null,
        };

        /// <summary>Lean: <c>Algorithm.parameterPatterns</c>; <c>[]</c> for a builtin or a family.</summary>
        internal IReadOnlyList<ParameterPattern> ParameterPatterns => algorithm switch
        {
            Algorithm.User user => user.ParameterPatterns,
            Algorithm.Builtin or Algorithm.Conditional => [],
        };

        /// <summary>Lean: <c>Algorithm.parameters</c>; <c>[]</c> for a builtin or a family.</summary>
        internal IReadOnlyList<ParameterDeclaration> Parameters => algorithm switch
        {
            Algorithm.User user => user.Parameters,
            Algorithm.Builtin or Algorithm.Conditional => [],
        };

        /// <summary>Lean: <c>Algorithm.params</c>; <c>[]</c> for a builtin or a family.</summary>
        internal IReadOnlyList<string> Params => algorithm switch
        {
            Algorithm.User user => user.Params,
            Algorithm.Builtin or Algorithm.Conditional => [],
        };

        /// <summary>
        /// Lean: <c>(Algorithm.params a).length</c> — the parameter count without materializing
        /// the projection; <c>0</c> for a builtin or a family.
        /// </summary>
        internal int ParameterCount => algorithm switch
        {
            Algorithm.User user => user.ParameterCount,
            Algorithm.Builtin or Algorithm.Conditional => 0,
        };

        /// <summary>Lean: <c>Algorithm.opens</c>; <c>[]</c> for a builtin.</summary>
        internal IReadOnlyList<Expr> Opens => algorithm switch
        {
            Algorithm.User user => user.Opens,
            Algorithm.Conditional family => family.Opens,
            Algorithm.Builtin => [],
        };

        /// <summary>Lean: <c>Algorithm.props</c>; <c>[]</c> for a builtin or a family.</summary>
        internal IReadOnlyList<Property> Properties => algorithm switch
        {
            Algorithm.User user => user.Properties,
            Algorithm.Builtin or Algorithm.Conditional => [],
        };

        /// <summary>Lean: <c>Algorithm.output</c>; the empty bundle for a builtin or a family.</summary>
        internal OutputBundle Output => algorithm switch
        {
            Algorithm.User user => user.Output,
            Algorithm.Builtin or Algorithm.Conditional => OutputBundle.Empty,
        };

        /// <summary>Lean: <c>Algorithm.branches</c>; <c>[]</c> for a builtin or a user algorithm.</summary>
        internal IReadOnlyList<CondBranch> Branches => algorithm switch
        {
            Algorithm.Conditional family => family.Branches,
            Algorithm.User or Algorithm.Builtin => [],
        };

        /// <summary>
        /// <see cref="Algorithm.User.HasExplicitParameterList"/> for a user algorithm; false for
        /// a builtin or a family, which have no written parameter list.
        /// </summary>
        internal bool HasExplicitParameterList => algorithm switch
        {
            Algorithm.User user => user.HasExplicitParameterList,
            Algorithm.Builtin or Algorithm.Conditional => false,
        };

        /// <summary>
        /// Lean: <c>Algorithm.findDuplicatePropName</c> — total; <c>none</c> for a builtin or a
        /// family, which declare no properties (<see cref="Algorithm.User.FindDuplicatePropName"/>).
        /// </summary>
        internal string? FindDuplicatePropName() => algorithm switch
        {
            Algorithm.User user => user.FindDuplicatePropName(),
            Algorithm.Builtin or Algorithm.Conditional => null,
        };

        /// <summary>
        /// Lean: <c>Algorithm.hasDuplicateBranchPatterns</c> — total; false for a builtin or a
        /// user algorithm, which have no branches (<see cref="Algorithm.Conditional.HasDuplicateBranchPatterns"/>).
        /// </summary>
        internal bool HasDuplicateBranchPatterns() => algorithm switch
        {
            Algorithm.Conditional family => family.HasDuplicateBranchPatterns(),
            Algorithm.User or Algorithm.Builtin => false,
        };
    }
}
