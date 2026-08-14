using System.Diagnostics.CodeAnalysis;

namespace KatLang;

/// <summary>
/// What can be known statically about an expression's ability to provide
/// structural members when it is used in algorithm position.
/// </summary>
internal enum StaticStructuralMemberProviderKind
{
    /// <summary>A lexical reference needs an elaborated scope to identify its algorithm.</summary>
    LexicalReference,

    /// <summary>A parameter may carry an algorithm value only at runtime.</summary>
    RuntimeParameter,

    /// <summary>The expression can never expose structural members.</summary>
    DefinitelyAbsent,

    /// <summary>The expression denotes this statically known algorithm.</summary>
    KnownAlgorithm,
}

/// <summary>
/// Static structural-member capability for one expression. This is deliberately
/// more basic than DotCall dispatch: editor and dependency consumers derive
/// their dot-edge decisions from the same algorithm-position fact.
/// </summary>
internal readonly record struct StaticStructuralMemberProvider(
    StaticStructuralMemberProviderKind Kind,
    Algorithm? Algorithm = null);

internal static class AstHelpers
{
    internal static bool TryGetUnresolvedLoadArguments(
        this Expr expr,
        [NotNullWhen(true)] out OutputBundle? args)
    {
        if (expr is Expr.Call(Expr.Resolve(var name), var loadArgs) && name == "load")
        {
            args = loadArgs;
            return true;
        }

        args = null;
        return false;
    }

    internal static Property WithValue(this Property property, Algorithm value)
        => new(property.Name, value, property.IsPublic, property.Exposure)
        {
            DeclarationSpans = property.DeclarationSpans,
        };

    /// <summary>
    /// The core open-form rule shared by parser and evaluator validation.
    /// Surface-only unresolved <c>load</c> sugar is layered on by the parser.
    /// </summary>
    internal static bool IsCoreOpenForm(this Expr expr)
        => expr is Expr.AlgorithmExpr
            or Expr.Resolve
            or Expr.DotCall { Args: null, ResolutionMode: DotResolutionMode.Ordinary };

    /// <summary>
    /// Whether this edge selects the independently established ordinary-dot
    /// <c>.string</c> value intrinsic. Extension edges treat <c>string</c> as
    /// their stored lexical callable like every other member name.
    /// </summary>
    internal static bool UsesOrdinaryDotStringIntrinsic(this Expr.DotCall dotCall)
        => dotCall.ResolutionMode == DotResolutionMode.Ordinary
            && string.Equals(dotCall.Name, "string", StringComparison.Ordinal);

    /// <summary>
    /// Whether registry facts prove that this dot edge's written arguments are
    /// strict values rather than neutral higher-order argument slots. Only an
    /// ordinary structural Math member has that consumer contract; extension
    /// edges bypass the registry surface.
    /// </summary>
    internal static bool HasRegistryProvenStrictValueArguments(this Expr.DotCall dotCall)
        => dotCall.ResolutionMode == DotResolutionMode.Ordinary
            && dotCall.Target is Expr.Resolve { Name: "Math" }
            && BuiltinRegistry.IsMathFunctionMember(dotCall.Name);

    /// <summary>
    /// Classifies an expression by the GENERAL algorithm-position capability
    /// relevant to structural lookup. The switch is intentionally exhaustive
    /// and fail-loud: adding a new <see cref="Expr"/> form requires deciding
    /// this one fundamental capability, rather than adding DotCall-specific
    /// receiver cases in every static consumer.
    /// </summary>
    internal static StaticStructuralMemberProvider GetStaticStructuralMemberProvider(this Expr expr)
        => expr switch
        {
            Expr.Resolve => new(StaticStructuralMemberProviderKind.LexicalReference),
            Expr.Param => new(StaticStructuralMemberProviderKind.RuntimeParameter),
            Expr.AlgorithmExpr(var algorithm) => new(
                StaticStructuralMemberProviderKind.KnownAlgorithm,
                algorithm),

            // Capture and a lifted dot result resolve through memberless
            // algorithm wrappers. All remaining value/expression forms are
            // rejected by ResolveAlg. Either way, no structural member can
            // pre-empt a dot edge's lexical fallback.
            Expr.Capture
                or Expr.DotCall
                or Expr.Num
                or Expr.StringLiteral
                or Expr.Unary
                or Expr.Binary
                or Expr.Index
                or Expr.SequenceConstruct
                or Expr.EmptySequence
                or Expr.SequenceSpread
                or Expr.ListLiteral
                or Expr.Call
                or Expr.Grace
                or Expr.NativeCall
                => new(StaticStructuralMemberProviderKind.DefinitelyAbsent),

            _ => throw new InvalidOperationException(
                $"Unhandled Expr type in static structural-member classification: {expr.GetType().Name}"),
        };

    /// <summary>
    /// True when a conditional algorithm declares <paramref name="name"/> in
    /// at least one branch body. Such a member is local-only and blocks lexical
    /// fallback even though it is not present in the algorithm's direct
    /// property collection.
    /// </summary>
    internal static bool DefinesConditionalBranchProperty(this Algorithm algorithm, string name)
    {
        if (algorithm is not Algorithm.Conditional conditional)
            return false;

        foreach (var branch in conditional.Branches)
        {
            foreach (var property in branch.Body.Properties)
            {
                if (string.Equals(property.Name, name, StringComparison.Ordinal))
                    return true;
            }
        }

        return false;
    }

    /// <summary>
    /// The ONE static representation of a dot edge's structural-vs-fallback
    /// selection possibility, for static consumers (dependency/exposure
    /// analysis, editor classification). Returns true when the edge's stored
    /// lexical fallback is UNCONDITIONALLY the selected resolution:
    /// <list type="bullet">
    /// <item>every <see cref="DotResolutionMode.ExtensionOnly"/> edge —
    /// extension resolution bypasses structural lookup and the ordinary-dot
    /// <c>string</c> intrinsic by the language rule;</item>
    /// <item>an ORDINARY edge whose receiver's general structural-member
    /// capability is definitely absent, or whose statically known algorithm
    /// neither declares the member nor defines it in a conditional branch.</item>
    /// </list>
    /// Returns false when structural resolution (a member hit, a local-only /
    /// arity / no-branch member error, or the ordinary-dot <c>string</c>
    /// intrinsic) may pre-empt the fallback: parameter and lexical-name
    /// receivers resolve to runtime algorithm values this static view cannot
    /// inspect, and a member-bearing literal receiver selects structurally.
    /// Static consumers must treat a conditional fallback as unselected
    /// rather than guessing — the evaluator remains the only place that
    /// decides the actual dispatch.
    /// </summary>
    internal static bool LexicalFallbackIsUnconditional(this Expr.DotCall dotCall)
    {
        if (dotCall.ResolutionMode == DotResolutionMode.ExtensionOnly)
            return true;

        // The ordinary-dot `string` value intrinsic pre-empts BOTH structural
        // lookup and the lexical fallback on every receiver shape.
        if (dotCall.UsesOrdinaryDotStringIntrinsic())
            return false;

        var provider = dotCall.Target.GetStaticStructuralMemberProvider();
        return provider.Kind switch
        {
            StaticStructuralMemberProviderKind.LexicalReference
                or StaticStructuralMemberProviderKind.RuntimeParameter => false,
            StaticStructuralMemberProviderKind.DefinitelyAbsent => true,
            StaticStructuralMemberProviderKind.KnownAlgorithm =>
                !HasStructuralMemberOrConditionalBranchMember(provider.Algorithm!, dotCall.Name),
            _ => throw new InvalidOperationException(
                $"Unhandled static structural-member provider kind: {provider.Kind}"),
        };
    }

    private static bool HasStructuralMemberOrConditionalBranchMember(Algorithm receiver, string name)
    {
        foreach (var property in receiver.Properties)
        {
            if (string.Equals(property.Name, name, StringComparison.Ordinal))
                return true;
        }

        return receiver.DefinesConditionalBranchProperty(name);
    }

    /// <summary>
    /// Collapses a wrapper algorithm whose single output row is a scope-owning
    /// algorithm expression into that algorithm (module elaboration's
    /// single-block property-body promotion). A <see cref="Expr.Capture"/> body
    /// never collapses — a captured value boundary is not algorithm identity —
    /// the unwrap predicate is the structural node kind.
    /// </summary>
    internal static Algorithm UnwrapSingleBlockPropertyBody(this Algorithm algorithm)
    {
        if (algorithm is Algorithm.User
            {
                Params.Count: 0, Opens.Count: 0, Properties.Count: 0,
                Output: [Expr.AlgorithmExpr(var innerAlgorithm)]
            })
        {
            return innerAlgorithm;
        }

        return algorithm;
    }
}
