namespace KatLang;

/// <summary>
/// The role a slot gives the reference that fills it, decided by the slot's IMMEDIATE consumer
/// (THE UNIFIED FORMULA-LIFTING LAW, decided September 30 2026).
/// </summary>
internal enum LiftingRole
{
    /// <summary>
    /// The consumer demands the slot's VALUE — an operand, an index part, a spread operand, a list
    /// or capture element, an output row, the <c>.string</c> receiver, or an argument slot whose
    /// consumer demands its value (a builtin value slot, a Math or host-operation argument, a
    /// clause-family argument). A bare callable reference here is lifted to the call that forwards
    /// its lifting signature. Laziness does not change the role: an <c>if</c> branch is a value
    /// slot whether or not a run selects it, exactly as a free name written there is a parameter.
    /// </summary>
    Value,

    /// <summary>
    /// The consumer keeps the slot's CALLABLE identity — the callee of a call, a builtin callback
    /// slot, a whole argument of a user callable or of a callee known only at run time, a dot
    /// receiver the edge navigates or whose selection is decided at run time. A bare reference
    /// here is never lifted; a compound expression is still examined, its own children taking the
    /// roles of THEIR consumers (<c>Twice(A)</c> keeps <c>A</c>, <c>Twice(A + 0)</c> lifts it).
    /// </summary>
    Callable,
}

/// <summary>
/// What a consumer needs to know about the callable it calls to classify the argument slots: its
/// settled KIND. An unprocessed lone row may become a callable alias, so the resolver settles it
/// before classifying its slots. A callable alias has no kind of its own: it is classified as its
/// normalized TARGET (<see cref="LiftingCallee.OfAlgorithm"/>), so a call through it takes the
/// target's argument roles (X-45).
/// </summary>
internal enum LiftingCalleeKind
{
    /// <summary>A callee known only at run time: a parameter, an unresolved name, a computed value.</summary>
    Dynamic,

    /// <summary>A user algorithm (a property, a block): its binder decides at run time.</summary>
    User,

    /// <summary>A clause family: every argument is a VALUE role for lifting (PAR-07); at run time the family
    /// demands only what its clause patterns inspect (NEED-04, PAT-07).</summary>
    Family,

    /// <summary>A prelude builtin: the registry's slot roles decide.</summary>
    Builtin,

    /// <summary>A Math member (any spelling) or a host operation: every argument is a value.</summary>
    StrictValue,
}

/// <summary>The resolved callee of a call or dot edge, as far as slot roles need it.</summary>
internal readonly record struct LiftingCallee(LiftingCalleeKind Kind, BuiltinId Builtin = default)
{
    public static LiftingCallee Dynamic { get; } = new(LiftingCalleeKind.Dynamic);

    public static LiftingCallee User { get; } = new(LiftingCalleeKind.User);

    public static LiftingCallee Family { get; } = new(LiftingCalleeKind.Family);

    public static LiftingCallee StrictValue { get; } = new(LiftingCalleeKind.StrictValue);

    public static LiftingCallee OfBuiltin(BuiltinId builtin) => new(LiftingCalleeKind.Builtin, builtin);

    /// <summary>
    /// The kind of an algorithm value a name or a member resolves to (a builtin keeps its identity).
    /// A callable ALIAS is its TARGET's kind (binding indirection: an alias's argument roles are its
    /// target's, with no alias-specific role of its own) — the target the front end recorded when it
    /// elaborated the alias; an alias with no recorded target (a host-built tree) is known only at
    /// run time.
    /// </summary>
    public static LiftingCallee OfAlgorithm(Algorithm algorithm, bool isStrictValue)
        => algorithm switch
        {
            Algorithm.Builtin(var builtin) => OfBuiltin(builtin),
            Algorithm.Conditional => Family,
            Algorithm.User => isStrictValue ? StrictValue : User,
            Algorithm.Alias alias => alias.ResolvedTarget is { } target
                ? OfAlgorithm(target.Algorithm, target.IsStrictValue)
                : Dynamic,
        };
}

/// <summary>
/// The name resolution the sibling-order channel classifies with: a callee name's kind by the owner
/// walk over the level's map and the prelude, and the sibling that heads the one provider of the
/// level's own opens that supplies a name (null when none does, or the owner walk decides it).
/// </summary>
internal sealed record SiblingOrderLookup(
    Func<string, LiftingCallee> CalleeKindOf,
    Func<string, int?> OpenedSiblingProvider);

/// <summary>How a dot edge dispatches, as far as the roles of its receiver and arguments need it.</summary>
internal enum DotEdgeKind
{
    /// <summary>The dot-only <c>string</c> intrinsic, the miss route of an edge spelled <c>string</c>
    /// whose statically known receiver declares no member <c>string</c>: it converts the receiver's VALUE.</summary>
    StringIntrinsic,

    /// <summary>A declared member of a statically known receiver (a member named <c>string</c>
    /// included): the receiver is navigated.</summary>
    StructuralMember,

    /// <summary>The lexical fallback is selected: the edge IS the call <c>F(receiver, args)</c>.</summary>
    Fallback,

    /// <summary>A runtime receiver decides between a member and the miss route.</summary>
    Undecided,
}

/// <summary>
/// THE ONE CLASSIFIER OF THE UNIFIED FORMULA-LIFTING LAW (decided September 30 2026): the role each
/// slot of a call or dot edge gives the reference that fills it. Every other consumer's slots are
/// VALUE slots (operators, comparisons, index parts, spread operands, list and capture elements,
/// rows), a block is its own inferring level, and a call's callee is CALLABLE. Implicit-argument
/// resolution's dependency collection and rewrite and the sibling-order channel all read THIS, so
/// what a formula lifts, how it is rewritten, and which sibling it must see processed cannot drift.
/// </summary>
internal static class FormulaLiftingRoles
{
    /// <summary>
    /// The role of the supplied slot at <paramref name="position"/> (receiver included) of a call to
    /// <paramref name="callee"/>; <paramref name="positionKnown"/> is false once a spread slot precedes
    /// it (a spread is supply assembly: its item count is known only at run time).
    /// <list type="bullet">
    ///   <item>a clause family, a Math member and a host operation take every argument as a VALUE role (a
    ///   static classification: at run time a family demands only what its clauses inspect, NEED-04);</item>
    ///   <item>a builtin reads its registry role (a callback is invoked; the collection, every value
    ///   control and a surplus slot are values; <c>if</c> takes three values; a loop's step is
    ///   invoked); a position after a spread is a value only if every declared position is;</item>
    ///   <item>a user callable's argument stays neutral — a plain capture keeps both channels and its
    ///   binder decides at run time — and so does a callee known only at run time.</item>
    /// </list>
    /// </summary>
    public static LiftingRole SlotRole(LiftingCallee callee, int position, bool positionKnown)
        => callee.Kind switch
        {
            LiftingCalleeKind.Family or LiftingCalleeKind.StrictValue => LiftingRole.Value,
            LiftingCalleeKind.Builtin => positionKnown
                ? BuiltinSlotRole(callee.Builtin, position)
                : EveryBuiltinSlotIsAValue(callee.Builtin) ? LiftingRole.Value : LiftingRole.Callable,
            _ => LiftingRole.Callable,
        };

    /// <summary>The roles of a call's written argument slots, in order (after <paramref name="leadingSlots"/> supplied slots).</summary>
    public static LiftingRole[] ArgumentRoles(LiftingCallee callee, OutputBundle args, int leadingSlots = 0, bool leadingPositionsKnown = true)
    {
        var roles = new LiftingRole[args.Count];
        var positionKnown = leadingPositionsKnown;
        for (var index = 0; index < args.Count; index++)
        {
            roles[index] = SlotRole(callee, leadingSlots + index, positionKnown);
            if (args[index] is Expr.SequenceSpread)
                positionKnown = false;
        }

        return roles;
    }

    /// <summary>
    /// How <paramref name="edge"/> dispatches — its ROUTE, decided member-first (DOT-01): a
    /// structural member of a statically known receiver (a member named <c>string</c> included,
    /// Q-17 S-C), the miss route of a statically certain miss — the <c>string</c> intrinsic for an
    /// edge spelled <c>string</c>, the selected lexical fallback otherwise — or undecided (a runtime
    /// receiver). <paramref name="missSelection"/> is the edge's structural-miss verdict (the
    /// detector's stamp, or the caller's own static resolution for an unstamped host tree).
    /// </summary>
    public static DotEdgeKind EdgeKind(Expr.DotCall edge, LexicalFallbackSelection missSelection)
        => missSelection switch
        {
            LexicalFallbackSelection.Never => DotEdgeKind.StructuralMember,
            LexicalFallbackSelection.Always => edge.UsesOrdinaryDotStringIntrinsic()
                ? DotEdgeKind.StringIntrinsic
                : DotEdgeKind.Fallback,
            _ => DotEdgeKind.Undecided,
        };

    /// <summary>
    /// The role of a dot edge's receiver: the <c>string</c> intrinsic converts its value; a
    /// structural member navigates it; a selected fallback makes it slot 0 of the fallback callee
    /// (<c>R.F(args)</c> is <c>F(R, args)</c>, so both spellings classify alike); an undecided edge
    /// keeps it.
    /// </summary>
    public static LiftingRole ReceiverRole(DotEdgeKind kind, LiftingCallee fallbackCallee)
        => kind switch
        {
            DotEdgeKind.StringIntrinsic => LiftingRole.Value,
            DotEdgeKind.Fallback => SlotRole(fallbackCallee, 0, positionKnown: true),
            _ => LiftingRole.Callable,
        };

    /// <summary>
    /// The roles of a dot edge's written arguments: a structural member's own slots, a selected
    /// fallback's slots after the receiver (unknown positions after a spread receiver), and nothing
    /// value-demanded for an undecided edge or the intrinsic.
    /// </summary>
    public static LiftingRole[] DotArgumentRoles(Expr.DotCall edge, DotEdgeKind kind, LiftingCallee callee)
    {
        var args = edge.Args ?? OutputBundle.Empty;
        return kind switch
        {
            DotEdgeKind.StructuralMember => ArgumentRoles(callee, args),
            DotEdgeKind.Fallback => ArgumentRoles(
                callee, args, leadingSlots: 1, leadingPositionsKnown: edge.Target is not Expr.SequenceSpread),
            _ => ArgumentRoles(LiftingCallee.Dynamic, args),
        };
    }

    /// <summary>
    /// A builtin's registry role for supplied position <paramref name="position"/>: only a callback
    /// keeps its callable identity. The collection, every value control, and a SURPLUS position
    /// beyond the signature are values — a surplus slot is value-evaluated like a value slot before
    /// the arity verdict (PV-05), exactly as every argument of a Math member, a host operation and
    /// a clause family is a value whatever the call's arity, so no role depends on how many
    /// arguments a call supplies. The loops invoke their step (position 0) and take values in every
    /// later position; <c>if</c>, <c>atoms</c> and <c>range</c> take values only.
    /// </summary>
    private static LiftingRole BuiltinSlotRole(BuiltinId builtin, int position)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(builtin);
        if (descriptor.SequenceMetadata is { } metadata)
            return metadata.SlotRole(position) == SequenceBuiltinSlotRole.Callback ? LiftingRole.Callable : LiftingRole.Value;

        return IsLoop(builtin) && position == 0 ? LiftingRole.Callable : LiftingRole.Value;
    }

    private static bool EveryBuiltinSlotIsAValue(BuiltinId builtin)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(builtin);
        if (descriptor.SequenceMetadata is { } metadata)
            return metadata.SuffixArgs.All(static suffix => suffix.Kind != SequenceBuiltinSuffixArgKind.Algorithm);

        return !IsLoop(builtin);
    }

    private static bool IsLoop(BuiltinId builtin) => builtin is BuiltinId.@while or BuiltinId.@repeat;
}
