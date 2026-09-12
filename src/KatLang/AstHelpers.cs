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

    /// <summary>
    /// The expression is a dot edge that is statically known to FAIL at
    /// runtime before yielding anything: its receiver declares the member
    /// local-only, or defines it only inside conditional branches. The
    /// evaluator reports that structural error before either channel of any
    /// outer edge is consulted, so no member of this expression is ever reached.
    /// </summary>
    KnownFailure,
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
/// <item>dependency/exposure analysis charges the fallback for the same
/// MAY-selected states, read from the ELABORATED scope-aware verdict the
/// detector stamps on the edge (<see cref="Expr.DotCall.ElaboratedFallbackSelection"/>,
/// consumed through <see cref="AstHelpers.LexicalFallbackMayBeSelected"/>): a
/// property whose fallback names an enclosing owner's parameter is local-only
/// exactly when the runtime may read that parameter, while a receiver that
/// declares the member (<see cref="Never"/>) keeps working structural/open
/// access.</item>
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
    /// <summary>
    /// Output rows and hoisted deconstruction RHS rows in written order. Positionless
    /// rows retain declaration order after positioned rows. The optional filter applies
    /// only to output rows, so the resolver's bare-root rule never suppresses an RHS.
    /// </summary>
    internal static IReadOnlyList<Expr> WrittenRows(Algorithm algorithm, Func<Expr, bool>? includeOutputRow = null)
    {
        var output = includeOutputRow is null
            ? algorithm.Output
            : (IReadOnlyList<Expr>)algorithm.Output.Where(includeOutputRow).ToList();
        List<Expr>? merged = null;
        foreach (var property in algorithm.Properties)
        {
            if (property.Value is not Algorithm.User { IsAssignmentDeconstructionSource: true } source)
                continue;

            merged ??= new List<Expr>(output);
            merged.AddRange(source.Output);
        }

        if (merged is null)
            return output;

        return merged
            .OrderBy(static row => row.Span?.StartLineNumber ?? int.MaxValue)
            .ThenBy(static row => row.Span?.StartColumn ?? int.MaxValue)
            .ToList();
    }

    /// <summary>Rewrites each shared hoisted source once in its enclosing row context.</summary>
    internal static void RewriteDeconstructionSourceRows(
        Algorithm algorithm, List<Property> processedProperties, Func<Expr, Expr> rewriteRow)
    {
        Dictionary<Algorithm.User, Algorithm.User>? rewrittenSources = null;
        for (var index = 0; index < algorithm.Properties.Count; index++)
        {
            if (algorithm.Properties[index].Value is not Algorithm.User { IsAssignmentDeconstructionSource: true } source)
                continue;

            rewrittenSources ??= new(ReferenceEqualityComparer.Instance);
            if (!rewrittenSources.TryGetValue(source, out var rewritten))
            {
                rewritten = source with { Output = source.Output.Select(rewriteRow).ToList() };
                rewrittenSources[source] = rewritten;
            }
            processedProperties[index] = algorithm.Properties[index].WithValue(rewritten);
        }
    }

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
    /// relevant to structural lookup, with the scope-free resolution power: a
    /// bare lexical reference stays a
    /// <see cref="StaticStructuralMemberProviderKind.LexicalReference"/>.
    /// See <see cref="ResolveStaticStructuralMemberProvider"/> for the one
    /// classification and the scope-aware entry the detector and the editor use.
    /// </summary>
    internal static StaticStructuralMemberProvider GetStaticStructuralMemberProvider(this Expr expr)
        => expr.ResolveStaticStructuralMemberProvider(resolveLexicalReference: null);

    /// <summary>
    /// The ONE static classification of an expression's algorithm-position
    /// capability relevant to structural lookup. The switch is intentionally
    /// exhaustive and fail-loud: adding a new <see cref="Expr"/> form requires
    /// deciding this one fundamental capability, rather than adding
    /// DotCall-specific receiver cases in every static consumer.
    /// <para><paramref name="resolveLexicalReference"/> is the caller's
    /// resolution power for a bare lexical reference — the detector's owner
    /// walk, the editor's scope lookup — and is consulted for every bare name
    /// the classification meets, including the innermost receiver of a dot
    /// chain; <c>null</c> keeps such names
    /// <see cref="StaticStructuralMemberProviderKind.LexicalReference"/> (the
    /// scope-free dependency/exposure view).</para>
    /// <para>An argumentless dot edge <c>X.M</c> is classified COMPOSITIONALLY,
    /// mirroring the evaluator's receiver resolution (<c>ResolveDotReceiver</c>;
    /// Lean <c>resolveDotReceiver</c>) so the static view agrees with runtime
    /// dispatch at every level of a chain: on a statically known receiver that
    /// declares an exported <c>M</c>, the edge IS that member's algorithm; a
    /// declared local-only or conditional-branch member is a
    /// <see cref="StaticStructuralMemberProviderKind.KnownFailure"/> (the
    /// evaluator errors there, never falls back); a known receiver WITHOUT
    /// the member makes the edge a value — its lexical fallback's result —
    /// which is <see cref="StaticStructuralMemberProviderKind.DefinitelyAbsent"/>;
    /// and a runtime-valued or unresolved receiver propagates its own
    /// indeterminacy outward. The dot-only <c>string</c> intrinsic and every
    /// argument-bearing edge are values, exactly like a written call.</para>
    /// </summary>
    internal static StaticStructuralMemberProvider ResolveStaticStructuralMemberProvider(
        this Expr expr,
        Func<string, StaticStructuralMemberProvider>? resolveLexicalReference)
        => expr switch
        {
            Expr.Resolve(var name) => resolveLexicalReference?.Invoke(name)
                ?? new(StaticStructuralMemberProviderKind.LexicalReference),
            Expr.Param => new(StaticStructuralMemberProviderKind.RuntimeParameter),
            Expr.AlgorithmExpr(var algorithm) => new(
                StaticStructuralMemberProviderKind.KnownAlgorithm,
                algorithm),

            Expr.DotCall { Args: null } edge when !edge.UsesOrdinaryDotStringIntrinsic()
                => ResolveDotEdgeStructuralMemberProvider(edge, resolveLexicalReference),

            // Capture, the `.string` intrinsic, and an argument-bearing dot
            // result resolve through memberless algorithm wrappers. All
            // remaining value/expression forms are rejected by ResolveAlg.
            // Either way, no structural member can pre-empt a dot edge's
            // lexical fallback. (Grace is stripped by callers before
            // classification — see UnwrapGraceOperand — and is classified
            // here only as the raw shape it is.)
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
    /// The dot-edge arm of <see cref="ResolveStaticStructuralMemberProvider"/>:
    /// the static twin of the evaluator's <c>ResolveDotReceiver</c> for ONE
    /// argumentless, non-<c>string</c> edge, classified over its own receiver's
    /// classification. Structural member lookup is the shared
    /// <see cref="ElaboratedScopeLookup.TryLookupProperty"/> (any visibility —
    /// structural access ignores <c>public</c>) plus the exposure check the
    /// evaluator applies, so the front end cannot navigate a member the
    /// evaluator would refuse.
    /// </summary>
    private static StaticStructuralMemberProvider ResolveDotEdgeStructuralMemberProvider(
        Expr.DotCall edge,
        Func<string, StaticStructuralMemberProvider>? resolveLexicalReference)
    {
        var receiver = edge.Target.UnwrapGraceOperand()
            .ResolveStaticStructuralMemberProvider(resolveLexicalReference);
        switch (receiver.Kind)
        {
            case StaticStructuralMemberProviderKind.KnownAlgorithm:
            {
                var algorithm = receiver.Algorithm!;
                if (ElaboratedScopeLookup.TryLookupProperty(algorithm, edge.Name) is { } hit)
                {
                    return hit.Property.Exposure == PropertyExposure.Exported
                        ? new(StaticStructuralMemberProviderKind.KnownAlgorithm, hit.Property.Value)
                        : new(StaticStructuralMemberProviderKind.KnownFailure);
                }

                return algorithm.DefinesConditionalBranchProperty(edge.Name)
                    ? new(StaticStructuralMemberProviderKind.KnownFailure)
                    // The receiver lacks the member: the edge selects its lexical
                    // fallback, whose result is a value.
                    : new(StaticStructuralMemberProviderKind.DefinitelyAbsent);
            }

            // A runtime-valued or unresolved receiver may or may not own the
            // member, so the edge's own capability is equally undecided; a
            // value receiver makes the edge a value; a failing receiver never
            // yields this edge at all.
            case StaticStructuralMemberProviderKind.LexicalReference:
            case StaticStructuralMemberProviderKind.RuntimeParameter:
            case StaticStructuralMemberProviderKind.DefinitelyAbsent:
            case StaticStructuralMemberProviderKind.KnownFailure:
                return receiver;

            default:
                throw new InvalidOperationException(
                    $"Unhandled static structural-member provider kind: {receiver.Kind}");
        }
    }

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
    /// receivers may select it; and a receiver edge that is statically known
    /// to fail (<see cref="StaticStructuralMemberProviderKind.KnownFailure"/>)
    /// never reaches this edge's channels at all, so the fallback is never
    /// selected there either — an error is not a fallback.
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
            StaticStructuralMemberProviderKind.KnownFailure
                => LexicalFallbackSelection.Never,
            _ => throw new InvalidOperationException(
                $"Unhandled static structural-member provider kind: {receiverProvider.Kind}"),
        };
    }

    /// <summary>
    /// The MAY-selection projection of <see cref="GetLexicalFallbackSelection"/>
    /// for the scope-free dependency/exposure walk: true when the edge's stored
    /// lexical fallback can be the selected resolution at runtime. The
    /// ELABORATED scope-aware verdict decides when present
    /// (<see cref="Expr.DotCall.ElaboratedFallbackSelection"/>, stamped by
    /// parameter detection and rechecked by exposure against eligible opens): a receiver
    /// that declares the member never selects the fallback, so a Param
    /// fallback hidden behind a structural winner charges nothing; a receiver
    /// known to lack it — a sibling property whose value is a list, a literal,
    /// a call result — always does; a runtime-valued receiver may. An
    /// unstamped edge (a raw parser or host-built tree) falls back to the
    /// receiver expression's raw shape classification, where an unresolved
    /// lexical reference stays <see cref="LexicalFallbackSelection.Conditional"/>
    /// and is therefore treated as MAY-selected — the safe direction for a
    /// property whose value the runtime may derive from the fallback. The
    /// evaluator remains the only place that decides the actual dispatch.
    /// </summary>
    internal static bool LexicalFallbackMayBeSelected(this Expr.DotCall dotCall)
        => (dotCall.ElaboratedFallbackSelection
                ?? dotCall.GetLexicalFallbackSelection(
                    dotCall.Target.UnwrapGraceOperand().GetStaticStructuralMemberProvider()))
            != LexicalFallbackSelection.Never;

    private static bool HasStructuralMemberOrConditionalBranchMember(Algorithm receiver, string name)
        => ElaboratedScopeLookup.TryLookupProperty(receiver, name) is not null
            || receiver.DefinesConditionalBranchProperty(name);

    /// <summary>
    /// Collapses a wrapper algorithm whose single output row is a scope-owning
    /// algorithm expression into that algorithm (module elaboration's
    /// single-block property-body promotion). A <see cref="Expr.Capture"/> body
    /// never collapses — a captured value boundary is not algorithm identity.
    /// A deconstruction source also keeps its written RHS boundary and provenance.
    /// </summary>
    internal static Algorithm UnwrapSingleBlockPropertyBody(this Algorithm algorithm)
    {
        if (algorithm is Algorithm.User
            {
                IsAssignmentDeconstructionSource: false,
                Params.Count: 0, Opens.Count: 0, Properties.Count: 0,
                Output: [Expr.AlgorithmExpr(var innerAlgorithm)]
            })
        {
            return innerAlgorithm;
        }

        return algorithm;
    }
}
