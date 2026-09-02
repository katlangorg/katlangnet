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

/// <summary>
/// The ONE static classification of a dot edge's structural-vs-lexical
/// selection: whether the edge's stored lexical fallback can be the selected
/// resolution at runtime. Consumers differ in WHICH states they act on, never
/// in how the states are derived:
/// <list type="bullet">
/// <item>implicit parameter inference includes the fallback callable for
/// <see cref="Conditional"/> and <see cref="Always"/> (a MAY-selection
/// question: if the fallback can be needed, its callable identity must be
/// representable in the inferred signature);</item>
/// <item>dependency/exposure analysis charges the fallback only for
/// <see cref="Always"/> (a MUST-selection question: charging a conditional
/// fallback would revoke working structural/open access).</item>
/// </list>
/// </summary>
internal enum LexicalFallbackSelection
{
    /// <summary>Structural resolution (a member hit, a local-only/no-branch
    /// member error, or the dot-only <c>string</c> intrinsic) always
    /// pre-empts the fallback.</summary>
    Never,

    /// <summary>The receiver resolves to a runtime value this static view
    /// cannot inspect (parameter or unresolved/ambiguous lexical reference):
    /// the fallback may or may not be selected.</summary>
    Conditional,

    /// <summary>Structural resolution is statically impossible: the fallback
    /// is unconditionally the selected resolution.</summary>
    Always,
}

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
    {
        var rewritten = new Property(property.Name, value, property.IsPublic, property.Exposure)
        {
            DeclarationSpans = property.DeclarationSpans,
        };
        FinalPropertyExposure.Link(property, rewritten);
        return rewritten;
    }

    /// <summary>
    /// The core open-form rule shared by parser and evaluator validation.
    /// Surface-only unresolved <c>load</c> sugar is layered on by the parser.
    /// </summary>
    internal static bool IsCoreOpenForm(this Expr expr)
        => expr is Expr.AlgorithmExpr
            or Expr.Resolve
            or Expr.DotCall { Args: null };

    /// <summary>
    /// Whether this edge selects the independently established dot-only
    /// <c>.string</c> value intrinsic. Grace composed with dot syntax shares
    /// it: <c>x~.string</c> and <c>x.~string</c> build the SAME ordinary dot
    /// edge as <c>x.string</c>; Grace only affects inferred name order, so the
    /// intrinsic applies identically.
    /// </summary>
    internal static bool UsesOrdinaryDotStringIntrinsic(this Expr.DotCall dotCall)
        => string.Equals(dotCall.Name, "string", StringComparison.Ordinal);

    /// <summary>
    /// Strips grace ordering wrappers from an expression. Grace annotates
    /// implicit PARAMETER ORDER only — it never changes what the decorated
    /// occurrence resolves to or how a dot edge dispatches — so every
    /// semantic classification of a raw (pre-elaboration) expression looks
    /// through it. Elaborated trees contain no grace; there this is the
    /// identity.
    /// </summary>
    internal static Expr UnwrapGraceOperand(this Expr expr)
    {
        while (expr is Expr.Grace(var inner, _))
            expr = inner;
        return expr;
    }

    // ── Math member shape classification ─────────────────────────────────────
    // The ONE owner of "is this written expression a Math member spelling?" for
    // every static consumer (implicit-argument resolution, dependency ordering,
    // the evaluator's qualified-native gate). Two shapes, one descriptor: the
    // canonical dot edge `Math.X` and the predefined prelude alias `x`. Both
    // helpers are SHAPE classification only — they resolve nothing, read no
    // scope, and dispatch nothing. Callers supply their own ordinary-resolution
    // shadow predicate (or null when they establish binding themselves), so a
    // user-defined `Math` or `sin` never acquires builtin facts from spelling.

    /// <summary>
    /// The canonical Math-member shape of a dot edge: a written <c>Math.X</c>
    /// whose <c>X</c> is a registry Math FUNCTION member, yielding that member's
    /// callable facts. <paramref name="isPreludeNameShadowed"/> is the caller's
    /// shadow knowledge for the module name (a locally defined <c>Math</c> is an
    /// ordinary structural container, never the prelude module); a caller that
    /// establishes binding by resolving the receiver itself passes <c>null</c>.
    /// Constants (<c>Math.Pi</c>) carry no callable facts and never match.
    /// </summary>
    internal static bool TryGetRegistryProvenCanonicalMathFacts(
        this Expr.DotCall dotCall,
        Func<string, bool>? isPreludeNameShadowed,
        [NotNullWhen(true)] out MathCallableFacts? facts)
    {
        if (dotCall.Target is Expr.Resolve { Name: BuiltinRegistry.MathModuleName }
            && !(isPreludeNameShadowed?.Invoke(BuiltinRegistry.MathModuleName) ?? false)
            && BuiltinRegistry.TryGetMathMemberFacts(dotCall.Name, out facts))
        {
            return true;
        }

        facts = null;
        return false;
    }

    /// <summary>
    /// The alias-shape twin of <see cref="TryGetRegistryProvenCanonicalMathFacts"/>:
    /// a written bare name that is a Math FUNCTION member's predefined prelude
    /// alias (<c>sin</c>, <c>pow</c>, ...), yielding the SAME descriptor-projected
    /// facts as the canonical spelling. <paramref name="isPreludeNameShadowed"/> is
    /// the caller's shadow knowledge for the written name — any visible user
    /// property shadows the alias; a parameter reference is an <see cref="Expr.Param"/>
    /// after detection and never matches. The constant alias (<c>pi</c>) carries no
    /// callable facts and never matches.
    /// </summary>
    internal static bool TryGetRegistryProvenMathAliasFacts(
        this Expr callee,
        Func<string, bool>? isPreludeNameShadowed,
        [NotNullWhen(true)] out MathCallableFacts? facts)
    {
        if (callee is Expr.Resolve(var name)
            && !(isPreludeNameShadowed?.Invoke(name) ?? false)
            && BuiltinRegistry.TryGetMathAliasFacts(name, out facts))
        {
            return true;
        }

        facts = null;
        return false;
    }

    /// <summary>
    /// Whether registry facts prove that this dot edge's written arguments are
    /// strict values rather than neutral higher-order argument slots: the edge
    /// has the unshadowed canonical <c>Math.X(...)</c> shape
    /// (<see cref="TryGetRegistryProvenCanonicalMathFacts"/>) and the member's
    /// facts declare strict-value arguments.
    /// </summary>
    internal static bool HasRegistryProvenStrictValueArguments(
        this Expr.DotCall dotCall,
        Func<string, bool>? isPreludeNameShadowed = null)
        => dotCall.TryGetRegistryProvenCanonicalMathFacts(isPreludeNameShadowed, out var facts)
            && facts.HasStrictValueArguments;

    /// <summary>
    /// The alias-call twin of
    /// <see cref="HasRegistryProvenStrictValueArguments(Expr.DotCall, Func{string, bool}?)"/>:
    /// whether registry facts prove that this call's written arguments are strict
    /// values, because its callee is an unshadowed Math prelude alias
    /// (<see cref="TryGetRegistryProvenMathAliasFacts"/>) whose facts declare
    /// strict-value arguments. Both twins read the SAME descriptor facts, so a
    /// consumer classifying calls through this pair cannot drift between
    /// <c>sin(...)</c> and <c>Math.Sin(...)</c>.
    /// </summary>
    internal static bool HasRegistryProvenStrictValueArguments(
        this Expr.Call call,
        Func<string, bool>? isPreludeNameShadowed = null)
        => call.Function.TryGetRegistryProvenMathAliasFacts(isPreludeNameShadowed, out var facts)
            && facts.HasStrictValueArguments;

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
    /// Derives the shared <see cref="LexicalFallbackSelection"/> fact for one
    /// dot edge from the receiver's algorithm-position capability. Callers
    /// supply the provider so each layer can bring its own resolution power
    /// to a <see cref="StaticStructuralMemberProviderKind.LexicalReference"/>
    /// receiver (the detector and the editor resolve it through their
    /// elaborated scope to a <c>KnownAlgorithm</c>; scope-free consumers pass
    /// the raw shape classification and an unresolved reference stays
    /// <see cref="LexicalFallbackSelection.Conditional"/> — the safe state in
    /// both directions). The mapping itself mirrors the evaluator's DotCall
    /// law exactly:
    /// the dot-only <c>string</c> intrinsic pre-empts both channels on every
    /// receiver; a statically known algorithm with the member (declared, or
    /// defined in a conditional branch — which the evaluator turns into a
    /// local-only ERROR, not a fallback) never selects the fallback; a
    /// statically known algorithm without the member, and every
    /// definitely-memberless value shape, always selects it; runtime-valued
    /// receivers may select it.
    /// </summary>
    internal static LexicalFallbackSelection GetLexicalFallbackSelection(
        this Expr.DotCall dotCall,
        StaticStructuralMemberProvider receiverProvider)
    {
        // The dot-only `string` value intrinsic pre-empts BOTH structural
        // lookup and the lexical fallback on every receiver shape.
        if (dotCall.UsesOrdinaryDotStringIntrinsic())
            return LexicalFallbackSelection.Never;

        return receiverProvider.Kind switch
        {
            StaticStructuralMemberProviderKind.LexicalReference
                or StaticStructuralMemberProviderKind.RuntimeParameter
                => LexicalFallbackSelection.Conditional,
            StaticStructuralMemberProviderKind.DefinitelyAbsent
                => LexicalFallbackSelection.Always,
            StaticStructuralMemberProviderKind.KnownAlgorithm =>
                HasStructuralMemberOrConditionalBranchMember(receiverProvider.Algorithm!, dotCall.Name)
                    ? LexicalFallbackSelection.Never
                    : LexicalFallbackSelection.Always,
            _ => throw new InvalidOperationException(
                $"Unhandled static structural-member provider kind: {receiverProvider.Kind}"),
        };
    }

    /// <summary>
    /// The MUST-selection projection of <see cref="GetLexicalFallbackSelection"/>
    /// for scope-free static consumers (dependency/exposure analysis).
    /// Returns true when the edge's stored lexical fallback is
    /// UNCONDITIONALLY the selected resolution. A conditional fallback — a
    /// receiver that may resolve structurally at runtime, including every
    /// lexical reference this scope-free view cannot resolve — must be
    /// treated as unselected rather than guessed: the evaluator remains the
    /// only place that decides the actual dispatch.
    /// </summary>
    internal static bool LexicalFallbackIsUnconditional(this Expr.DotCall dotCall)
        => dotCall.GetLexicalFallbackSelection(
                dotCall.Target.UnwrapGraceOperand().GetStaticStructuralMemberProvider())
            == LexicalFallbackSelection.Always;

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
