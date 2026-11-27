using KatLang.Evaluation;

namespace KatLang;

/// <summary>
/// The parameter bindings of ONE activation of a lexical owner, captured when a call
/// enters the owner's body (<see cref="Evaluator.EnterAlgorithmBody"/>) or matches one of
/// its clauses (<c>ChildOfConditionalCall</c>): the owner's own parameter names, as bound
/// on the value tier and the need-cell tier at that moment — first binding per name,
/// exactly the tiers a captured-parameter read must see (a cell carries both the VALUE and
/// the CALLABLE channel of its parameter). Keeping the tiers together prevents a
/// shadowing caller from supplying any missing binding.
/// <para>An activation is identified by REFERENCE: two calls of one declaration are two
/// activations even when every captured value is equal (Lean: a fresh index into
/// <c>EvalState.lexicalActivations</c> per <c>recordParameterActivation</c>). It lives on
/// the activated <see cref="ScopeCtx"/> (<see cref="ScopeCtx.Activation"/>) — the head
/// scope of the entered body (<see cref="Evaluator.EvalCtx.HeadScope"/>) or the family
/// scope a selected branch body is wired under — and is runtime-only: it takes no part in
/// record equality. The owning invocation supplies the binding identity for its exported inner properties.</para>
/// </summary>
internal sealed class ParameterActivation
{
    private ParameterActivation(ValEnv values, NeedEnv needs, object valueEnvironmentIdentity, long serial, bool ownsInvocation = false)
    {
        Values = values;
        Needs = needs;
        ValueEnvironmentIdentity = valueEnvironmentIdentity;
        _serialAndInvocation = (serial << 1) | (ownsInvocation ? 1L : 0L);
    }

    // The activation's serial in the upper bits and whether an actual call recorded it in the lowest
    // one. One field, so marking an invocation costs no byte per activation (activations are
    // allocated on every parameterized call, and their size is pinned by the allocation tests).
    private readonly long _serialAndInvocation;

    /// <summary>
    /// The activation's position in the run's recording order (<see cref="EvaluationBudget.NextActivationSerial"/>):
    /// what an exported evaluation's watermark is compared with (<see cref="Evaluator.IsDetached"/>). An
    /// activation recorded before an exported evaluation started is DETACHED inside it: still this
    /// identity for cache keys, alias memos, anchoring and declaring-context inheritance, but no
    /// source of inputs. Runtime-only, like the activation. Lean: the activation's index in
    /// <c>EvalState.lexicalActivations</c>.
    /// </summary>
    internal long Serial => _serialAndInvocation >> 1;

    /// <summary>
    /// Whether an ACTUAL CALL recorded this activation (INNER-PROPERTY LIFETIME, November 2026): a
    /// binding boundary bound a supply for the owner and entered its body
    /// (<see cref="Evaluator.EnterAlgorithmBody"/> with <c>invoked</c>, a selected clause of a family).
    /// Such an activation OWNS the bindings of the properties declared under it, whatever their
    /// exposure: its <see cref="ValueEnvironmentIdentity"/> — the fresh identity its call minted — is
    /// their owning invocation (<see cref="Evaluator.DeclaringInvocationIdentity"/>). An activation
    /// a property-style READ recorded (a parameterless or collecting-only owner with a local-only
    /// member, CACHE-OWNER-D1 / COLLECT-CACHE-1) owns none: a read gives a binding no new lifetime,
    /// so the search continues above it. Lean: <c>ParameterActivation.ownsInvocation</c>.
    /// </summary>
    internal bool OwnsInvocation => (_serialAndInvocation & 1) != 0;

    /// <summary>
    /// THE MARKER OF AN UNAVAILABLE PARAMETER (EXPORTED-DETACHED, November 2026: captured reads are
    /// LEXICAL-ONLY). <see cref="Evaluator.CapturedParameterActivation"/> answers with it when the
    /// level that lexically owns the read name has no activation — a static owner, reached by
    /// navigation from outside its call. The name is lexically OWNED and UNAVAILABLE at the site:
    /// every executed operation on the written occurrence — its VALUE read, its CALLABLE projection
    /// and callee resolution, and its direct transport as a supplied argument, callee, link receiver
    /// or alias row — is refused with <see cref="EvalError.UnknownName"/>
    /// (<see cref="Evaluator.UnboundParameter"/>), and none consults the context's inherited tiers,
    /// which hold whatever a dynamically live caller bound under the same name. It holds no binding
    /// on either tier, so a reader that only LOOKS a cell up (a planner, a retained-slice
    /// classification) finds none. Never a scope's activation: it owns no memo and has no serial
    /// (<see cref="IsUnavailable"/>). Lean: <c>CapturedParameter.unavailable</c>, whose lookup
    /// <c>capturedParameterActivation?</c> is the <c>unknownName</c> refusal.
    /// </summary>
    internal static ParameterActivation Unbound { get; } = new([], [], new object(), serial: 0);

    /// <summary>
    /// <see cref="Unbound"/> for an owner whose activation is DETACHED in the reading context
    /// (<see cref="Evaluator.IsDetached"/>): the same marker, told apart only so the refusal can say
    /// that the name is an input of the enclosing call (<see cref="Evaluator.UnboundParameter"/>).
    /// </summary>
    internal static ParameterActivation UnboundDetached { get; } = new([], [], new object(), serial: 0);

    /// <summary>
    /// Whether this is one of the two markers of an unavailable parameter (<see cref="Unbound"/>,
    /// <see cref="UnboundDetached"/>): the only activations without a serial.
    /// </summary>
    internal bool IsUnavailable => _serialAndInvocation == 0;

    public ValEnv Values { get; }

    internal NeedEnv Needs { get; }

    // The binding context of this activation: the fresh one an explicit call minted, or —
    // when a property-style read entered a parameterless or collecting-only owner — its
    // DECLARING activation's, never the consumer's nor the read's own empty-supply binding's
    // (CACHE-OWNER-D1, COLLECT-CACHE-1, Evaluator.DeclaringBindingIdentity).
    internal object ValueEnvironmentIdentity { get; }

    /// <summary>
    /// The memoized static ends of alias bindings declared under this activation
    /// (<see cref="Evaluator.AliasTargetKey"/>): an alias declared inside a call's body is resolved
    /// once per activation and forgotten with it. Runtime-only memoization, like the activation.
    /// </summary>
    internal Dictionary<Evaluator.AliasTargetKey, Evaluator.AliasStaticEnd> AliasTargets => Memos;

    /// <summary>
    /// The settled <c>.Algorithm</c> ROUTE DECISIONS of runtime-row aliases declared under this activation
    /// (<see cref="Evaluation.EvaluationBudget.AliasRouteDecisions"/>), keyed like
    /// <see cref="AliasTargets"/> by the alias's declaration and forgotten with the activation. (A
    /// runtime alias's BINDING CELL is never held here: it has its property's lifetime and lives in
    /// <see cref="Evaluation.EvaluationBudget.AliasBindingCells"/>, keyed by its binding identity —
    /// several activations share one.)
    /// </summary>
    internal Dictionary<Evaluator.AliasTargetKey, Evaluator.AliasRouteDecision> AliasRouteDecisions => Memos.RouteDecisions;

    /// <summary>
    /// The remembered NAME-RUN ENDS of an <c>open</c> target's stratified structure for references declared under
    /// this activation (<c>Evaluator.FollowOpenNameRun</c>; the run-wide memo is
    /// <see cref="Evaluation.EvaluationBudget.OpenStructureEnds"/>), keyed by the reference view and its callable identity, and forgotten with the activation. Runtime-only memoization,
    /// like the activation.
    /// </summary>
    internal Dictionary<Evaluator.OpenStructureKey, Algorithm> OpenStructureEnds => Memos.OpenStructureEnds;

    /// <summary>
    /// The resolved open providers of this activation's LEVEL — the one scope this activation is the
    /// <see cref="ScopeCtx.Activation"/> of (<see cref="Evaluator.ResolvedOpenLevel"/>) — memoized by the
    /// first lexical lookup that consulted its opens, or null: every later read of the level in this
    /// activation reuses it, and it is forgotten with the activation. A static level keeps its memo on its
    /// scope instead (<see cref="ScopeCtx.StaticOpenLevel"/>).
    /// </summary>
    internal Evaluator.ResolvedOpenLevel? OpenLevel => (Volatile.Read(ref _memos) as ActivationMemo)?.OpenLevel;

    /// <summary>Memoizes <paramref name="level"/> as this activation's resolved open providers (see <see cref="OpenLevel"/>).</summary>
    internal void PublishOpenLevel(Evaluator.ResolvedOpenLevel level) => Memos.OpenLevel = level;

    /// <summary>
    /// The spare plain head level for an unwired alias with <c>open</c>s declared under this
    /// activation (<c>Evaluator.AliasHeadLevel</c>), or null: ONE slot, naming its alias by its
    /// <see cref="ScopeCtx.Owner"/>, forgotten with the activation. A run keeps the slot of aliases declared
    /// outside every activation (<see cref="EvaluationBudget.AliasHeadLevel"/>).
    /// </summary>
    internal ScopeCtx? AliasHeadLevel => (Volatile.Read(ref _memos) as ActivationMemo)?.AliasHeadLevel;

    /// <summary>Keeps <paramref name="level"/> as this activation's alias head level (see <see cref="AliasHeadLevel"/>).</summary>
    internal void PublishAliasHeadLevel(ScopeCtx level) => Memos.AliasHeadLevel = level;

    /// <summary>
    /// The key facts of this activation's LEVEL — the one scope this activation is the
    /// <see cref="ScopeCtx.Activation"/> of (<see cref="Evaluation.Caching.ScopeKeyFacts"/>, which names that
    /// level) — memoized by the first cache key built over it, or null, and forgotten with the activation. A
    /// static level keeps them on its scope instead (<see cref="ScopeCtx.StaticKeyFacts"/>).
    /// </summary>
    internal Evaluation.Caching.ScopeKeyFacts? KeyFacts => Volatile.Read(ref _memos) switch
    {
        Evaluation.Caching.ScopeKeyFacts facts => facts,
        ActivationMemo memo => memo.KeyFacts,
        _ => null,
    };

    /// <summary>
    /// Memoizes <paramref name="facts"/> as this activation's level's key facts (see <see cref="KeyFacts"/>). An
    /// activation without other memos holds them directly, so the key facts alone cost no memo holder; a
    /// racing publication stores equivalent facts.
    /// </summary>
    internal void PublishKeyFacts(Evaluation.Caching.ScopeKeyFacts facts)
    {
        if (_serialAndInvocation == 0)
            throw new InvalidOperationException("An unbound parameter's stand-in activation owns no memo.");

        while (true)
        {
            var current = Volatile.Read(ref _memos);
            if (current is ActivationMemo memo)
            {
                memo.KeyFacts = facts;
                return;
            }

            if (ReferenceEquals(Interlocked.CompareExchange(ref _memos, facts, current), current))
                return;
        }
    }

    // The activation's memos hang off ONE lazily created holder (published first-wins, so racing chases meet
    // in one dictionary): an activation that never meets an alias or consults its level's opens pays one null
    // field, and one whose level only memoized its key facts holds those alone until a holder is needed (the
    // holder then carries them).
    // The two unbound stand-ins (serial 0) are process-wide and must never own a memo.
    private ActivationMemo Memos
    {
        get
        {
            if (_serialAndInvocation == 0)
                throw new InvalidOperationException("An unbound parameter's stand-in activation owns no memo.");

            while (true)
            {
                var current = Volatile.Read(ref _memos);
                if (current is ActivationMemo memo)
                    return memo;

                var created = new ActivationMemo { KeyFacts = current as Evaluation.Caching.ScopeKeyFacts };
                if (ReferenceEquals(Interlocked.CompareExchange(ref _memos, created, current), current))
                    return created;
            }
        }
    }

    // Null, the level's key facts alone, or the ActivationMemo holder.
    private object? _memos;

    // The alias-target memo itself, carrying the route-decision and open name-run memos created on first use,
    // the level's resolved open providers, the alias head level and the level's key facts.
    private sealed class ActivationMemo : Dictionary<Evaluator.AliasTargetKey, Evaluator.AliasStaticEnd>
    {
        private Dictionary<Evaluator.AliasTargetKey, Evaluator.AliasRouteDecision>? _routeDecisions;
        private Dictionary<Evaluator.OpenStructureKey, Algorithm>? _openStructureEnds;
        private Evaluator.ResolvedOpenLevel? _openLevel;
        private ScopeCtx? _aliasHeadLevel;
        private Evaluation.Caching.ScopeKeyFacts? _keyFacts;

        // A pure function of the activation's level, so a racing publication stores equivalent facts.
        public Evaluation.Caching.ScopeKeyFacts? KeyFacts
        {
            get => Volatile.Read(ref _keyFacts);
            set => Volatile.Write(ref _keyFacts, value);
        }

        public Dictionary<Evaluator.AliasTargetKey, Evaluator.AliasRouteDecision> RouteDecisions
            => Volatile.Read(ref _routeDecisions)
               ?? Interlocked.CompareExchange(ref _routeDecisions, [], null)
               ?? _routeDecisions!;

        public Dictionary<Evaluator.OpenStructureKey, Algorithm> OpenStructureEnds
            => Volatile.Read(ref _openStructureEnds)
               ?? Interlocked.CompareExchange(ref _openStructureEnds, [], null)
               ?? _openStructureEnds!;

        // A pure function of the level and the run (Evaluator.ResolvedOpenLevel), so a racing publication
        // stores an equivalent memo and the last one wins.
        public Evaluator.ResolvedOpenLevel? OpenLevel
        {
            get => Volatile.Read(ref _openLevel);
            set => Volatile.Write(ref _openLevel, value);
        }

        // A competing publication can replace the slot. Each reader uses its own alias's scope.
        public ScopeCtx? AliasHeadLevel
        {
            get => Volatile.Read(ref _aliasHeadLevel);
            set => Volatile.Write(ref _aliasHeadLevel, value);
        }
    }

    /// <summary>
    /// Captures the bindings of <paramref name="names"/> from the two tiers of a binding
    /// context: the value environment <paramref name="values"/> and the need-cell tier of
    /// <paramref name="ctx"/>, keeping the first binding of each owned name in environment
    /// order (Lean: <c>recordParameterActivation</c>'s two <c>filter</c>s), together with the
    /// entering context's binding identity (Lean: <c>bindingContext := ctx.bindingContext</c>):
    /// the fresh tier of the call boundary that entered the body, even when that call bound
    /// nothing (<see cref="Evaluator.BindingContextIdentity"/>) — unless a property-style read
    /// supplies the identity its owner inherits from the declaring activation
    /// (<paramref name="inheritedBindingIdentity"/>, CACHE-OWNER-D1; Lean
    /// <c>enterPropertyOwnerBody</c>). <paramref name="invoked"/> marks the activation of an
    /// actual call (<see cref="OwnsInvocation"/>; Lean: <c>ownsInvocation := ctx.enteringInvocation</c>);
    /// a read never passes it.
    /// <para>A WIDE owned-name list (at least <see cref="Evaluator.MinimumIndexedParameterCount"/> names)
    /// is filtered through ONE ordinal index of the names (<see cref="OwnedParameterNames"/>), built in place of
    /// the name set the filter used before, and the need tier keeps it (<see cref="OwnedNeedBindings"/>): the
    /// activation's later reads — whether the head binds a name, a captured read of one of its parameters —
    /// are then one hash lookup instead of a scan of the head's names and bindings. The kept bindings, their
    /// order and the first binding per name are the filter's own, on both tiers (implementation-only,
    /// 2026-11-22, finding <c>evaluator-runtime-quadratic-parameter-width</c>).</para>
    /// <para>A narrow body entered over a LAYERED need tier (<see cref="Evaluator.LayeredBoundNeedEnv"/>: a narrow
    /// boundary over a wide tier) filters only the layer's prefix when every owned name is one the layer hides from
    /// its base — always so for the names its own boundary bound — because the flat list's bindings of those names
    /// all lie in the prefix (<see cref="Evaluator.LayeredBoundNeedEnv.OwnedPart"/>). So entering the body reads none of
    /// the caller's wide tier (implementation-only, 2026-11-24).</para>
    /// </summary>
    internal static ParameterActivation Capture(
        IReadOnlyList<string> names,
        Evaluator.EvalCtx ctx,
        ValEnv values,
        object? inheritedBindingIdentity = null,
        bool invoked = false)
    {
        if (names.Count >= Evaluator.MinimumIndexedParameterCount)
            return CaptureIndexed(new OwnedParameterNames(names), ctx, values, inheritedBindingIdentity, invoked);

        // A layered tier holds the first binding of each name its boundary shadowed in its narrow prefix
        // (Evaluator.LayeredBoundNeedEnv.OwnedPart), so the filter reads only that part: the same bindings.
        return new(
            FilterOwned(values, names, static binding => binding.Name),
            FilterOwned(ctx.NeedEnv is Evaluator.LayeredBoundNeedEnv layered ? layered.OwnedPart(names) : ctx.NeedEnv, names, static binding => binding.Name),
            inheritedBindingIdentity ?? Evaluator.BindingContextIdentity(ctx, values),
            ctx.Budget.NextActivationSerial(),
            invoked);
    }

    // The wide arm of Capture, out of line: the same two filters, in the same order, over the owned-name index.
    private static ParameterActivation CaptureIndexed(
        OwnedParameterNames owned,
        Evaluator.EvalCtx ctx,
        ValEnv values,
        object? inheritedBindingIdentity,
        bool invoked)
        => new(
            owned.FilterValues(values),
            OwnedNeedBindings.Filter(ctx.NeedEnv, owned),
            inheritedBindingIdentity ?? Evaluator.BindingContextIdentity(ctx, values),
            ctx.Budget.NextActivationSerial(),
            invoked);

    /// <summary>
    /// The bindings of <paramref name="env"/> whose names are owned, first binding per name.
    /// Parameter lists are short in every ordinary program, so a linear membership scan
    /// avoids allocating a set; a wider signature crosses over to one, and a wide one is
    /// filtered through its owned-name index instead (<see cref="Capture"/>).
    /// </summary>
    private static TBinding[] FilterOwned<TBinding>(
        IReadOnlyList<TBinding> env,
        IReadOnlyList<string> names,
        Func<TBinding, string> nameOf)
    {
        if (env.Count == 0 || names.Count == 0)
            return [];

        HashSet<string>? ownedSet = names.Count > Evaluator.LinearShadowNameScanLimit
            ? new HashSet<string>(names, StringComparer.Ordinal)
            : null;

        List<TBinding>? kept = null;
        for (var index = 0; index < env.Count; index++)
        {
            var binding = env[index];
            var name = nameOf(binding);
            // Removing a wide signature's name records its first binding in the same
            // hash lookup that establishes ownership. Scanning `kept` here would make
            // capturing a wide invocation quadratic even though ownership uses a set.
            var firstOwned = ownedSet is not null
                ? ownedSet.Remove(name)
                : Evaluator.ContainsOrdinal(names, name) && !AlreadyKept(kept, name, nameOf);
            if (!firstOwned)
                continue;

            (kept ??= new List<TBinding>(names.Count)).Add(binding);
        }

        return kept is null ? [] : kept.ToArray();
    }

    private static bool AlreadyKept<TBinding>(List<TBinding>? kept, string name, Func<TBinding, string> nameOf)
    {
        if (kept is null)
            return false;

        for (var index = 0; index < kept.Count; index++)
        {
            if (string.Equals(nameOf(kept[index]), name, StringComparison.Ordinal))
                return true;
        }

        return false;
    }
}

/// <summary>
/// The owned parameter names of ONE wide activation (<see cref="ParameterActivation.Capture"/>, at least
/// <see cref="Evaluator.MinimumIndexedParameterCount"/> names): <see cref="Names"/> is the very list the
/// activation was captured for — the head scope's <see cref="ScopeCtx.Parameters"/> — and each distinct name's
/// SLOT is its first position in it, found by one ordinal hash lookup. Membership is exactly the ordinal scan's
/// (<see cref="Evaluator.ContainsOrdinal"/>), a null name included (a host-built pattern can carry one). Built
/// once, at the activation's capture, and never changed: an evaluator-made projection, not an AST list.
/// </summary>
internal sealed class OwnedParameterNames
{
    private readonly Dictionary<string, int> _slots;
    private readonly int _nullSlot = -1;

    internal OwnedParameterNames(IReadOnlyList<string> names)
    {
        Names = names;
        _slots = new Dictionary<string, int>(names.Count, StringComparer.Ordinal);
        for (var index = 0; index < names.Count; index++)
        {
            var name = names[index];
            if (name is null)
            {
                if (_nullSlot < 0)
                    _nullSlot = index;
            }
            else
            {
                _slots.TryAdd(name, index);
            }
        }
    }

    /// <summary>The owned names, in their written order, duplicates included.</summary>
    internal IReadOnlyList<string> Names { get; }

    /// <summary>The first position of <paramref name="name"/> in <see cref="Names"/>, or -1 when it is not owned.</summary>
    internal int SlotOf(string name)
        => name is null ? _nullSlot : _slots.TryGetValue(name, out var slot) ? slot : -1;

    /// <summary>Whether <see cref="Names"/> contains <paramref name="name"/> (ordinal).</summary>
    internal bool Owns(string name) => SlotOf(name) >= 0;

    /// <summary>
    /// The value tier's filter (<see cref="ParameterActivation.Capture"/>): the bindings of <paramref name="env"/>
    /// whose names are owned, first binding per name, in environment order — the narrow filter's result.
    /// </summary>
    internal (string Name, Result Value)[] FilterValues(ValEnv env)
    {
        if (env.Count == 0)
            return [];

        var seen = new bool[Names.Count];
        List<(string Name, Result Value)>? kept = null;
        for (var index = 0; index < env.Count; index++)
        {
            var binding = env[index];
            var slot = SlotOf(binding.Name);
            if (slot < 0 || seen[slot])
                continue;
            seen[slot] = true;
            (kept ??= new List<(string Name, Result Value)>(Names.Count)).Add(binding);
        }

        return kept is null ? [] : kept.ToArray();
    }
}

/// <summary>
/// The need tier of ONE wide activation (<see cref="ParameterActivation.Needs"/>, captured over at least
/// <see cref="Evaluator.MinimumIndexedParameterCount"/> owned names): the first binding of each owned name, in
/// environment order — exactly the narrow filter's list — together with the owned-name index it was filtered
/// through (<see cref="Owned"/>) and, per slot, where that name's binding is. So a lookup in it
/// (<see cref="Find"/>, <c>Evaluator.LookupNeed</c>) is one hash lookup and agrees with the ordered scan, and
/// <see cref="Owned"/> answers whether the activated head binds a name without scanning its parameter list
/// (<c>Evaluator.ScopeBindsParameter</c>). Immutable once filtered, so concurrent readers need no lock.
/// </summary>
internal sealed class OwnedNeedBindings : List<(string Name, NeedCell Cell)>
{
    // Per slot of Owned: 1 + the position of that name's binding in this list, or 0 when the name has none.
    private readonly int[] _positions;

    private OwnedNeedBindings(OwnedParameterNames owned, int capacity)
        : base(capacity)
    {
        Owned = owned;
        _positions = new int[owned.Names.Count];
    }

    /// <summary>The owned-name index this tier was filtered through.</summary>
    internal OwnedParameterNames Owned { get; }

    /// <summary>
    /// The bindings of <paramref name="env"/> whose names <paramref name="owned"/> owns, first binding per name, in
    /// environment order. A minted wide tier (<see cref="Evaluator.WideBoundNeedEnv"/>) borrows the result for its
    /// lookups of those names: they are exactly the first bindings of those names in it.
    /// </summary>
    internal static OwnedNeedBindings Filter(NeedEnv env, OwnedParameterNames owned)
    {
        var bindings = new OwnedNeedBindings(owned, Math.Min(env.Count, owned.Names.Count));
        for (var index = 0; index < env.Count; index++)
        {
            var binding = env[index];
            var slot = owned.SlotOf(binding.Name);
            if (slot < 0 || bindings._positions[slot] != 0)
                continue;
            bindings.Add(binding);
            bindings._positions[slot] = bindings.Count;
        }

        if (env is Evaluator.WideBoundNeedEnv minted)
            minted.Lend(bindings);
        return bindings;
    }

    /// <summary>The cell of the first binding named <paramref name="name"/>, or null: the ordered scan's answer.</summary>
    internal NeedCell? Find(string name)
    {
        var slot = Owned.SlotOf(name);
        return slot < 0 ? null : CellAt(slot);
    }

    /// <summary>The cell bound to the owned name of <paramref name="slot"/> (<see cref="OwnedParameterNames.SlotOf"/>), or null when it has none.</summary>
    internal NeedCell? CellAt(int slot)
    {
        var position = _positions[slot];
        return position == 0 ? null : this[position - 1].Cell;
    }
}

public static partial class Evaluator
{
    /// <summary>
    /// Enters an algorithm body. EVERY ACTUAL CALL RECORDS AN ACTIVATION (INNER-PROPERTY LIFETIME,
    /// November 2026): with <paramref name="invoked"/> — a binding boundary bound a supply for the
    /// callee and enters its body here (a user call, a callback, a loop round) — the entry always
    /// captures an activation, marked as owning its invocation
    /// (<see cref="ParameterActivation.OwnsInvocation"/>), because that activation is the identity
    /// that owns the bindings of the properties declared under it, self-contained ones included: two
    /// calls of one owner never share an inner binding. Every other entry is NOT a call and keeps
    /// the former rule below — a property-style read, a block in value position, the zero-argument
    /// demand funnel, a row supply, an alias cell's row. Lean: the invocation mark
    /// <c>EvalCtx.enteringInvocation</c> read by <c>enterAlgorithmBody</c>.
    /// <para>A parameterized body gets a fresh
    /// <see cref="ParameterActivation"/> and the entered context carries the activated head
    /// scope (<see cref="EvalCtx.HeadScope"/>): the scope the body's own declaring level
    /// resolves to, the level captured-parameter reads and the accessibility law find its
    /// activation on, and the parent of every scope wired under the head. A parameterless owner with
    /// local-only properties also gets an activation, whose binding identity keys those properties:
    /// the entering context's, or — for a property-style read — the
    /// <paramref name="inheritedBindingIdentity"/> of its declaring activation (CACHE-OWNER-D1,
    /// <see cref="EvalPropertyOwnerBodyCounted"/>; a collecting-only owner's read passes the same
    /// identity after binding its empty supply, COLLECT-CACHE-1). Other parameterless bodies need no activated head
    /// scope. Lean: <c>enterAlgorithmBody</c> (<c>headScope := some (a.asScopeCtx.withActivation id)</c>)
    /// and, with an inherited identity, <c>enterPropertyOwnerBody</c>.</para>
    /// <para>THE STATIC HEAD LEVEL (implementation-only, November 2026): a body that needs no activation but
    /// declares <c>open</c>s — and has no parameter pattern at all — is entered with its plain declaring scope
    /// (<see cref="AsScopeCtx"/>, no activation) as its head scope, built ONCE for this entry. That is exactly
    /// the scope every consumer would otherwise rebuild per use (<see cref="SiteScope"/> and
    /// <see cref="ScopeInContext"/> fall back to it, and with no pattern its parameter list and the head's
    /// <c>Params</c> are both empty, which <see cref="CapturedParameterActivation"/> reads),
    /// so the entry means what it meant. Being one object, it is the level's runtime state for the entry: the
    /// level's resolved open providers are memoized there (<see cref="ScopeCtx.StaticOpenLevel"/>) and shared
    /// by every read of the entry, its own rows' and those of the bodies wired under it alike.</para>
    /// </summary>
    internal static EvalCtx EnterAlgorithmBody(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv values,
        IReadOnlyList<string>? parameterNames = null,
        object? inheritedBindingIdentity = null,
        bool invoked = false)
    {
        var names = parameterNames ?? algorithm.Params;
        if (!invoked && names.Count == 0 && !HasLocalOnlyProperty(algorithm))
        {
            return algorithm.Opens.Count > 0 && algorithm.ParameterPatterns.Count == 0
                ? ctx.Push(algorithm, AsScopeCtx(algorithm))
                : ctx.Push(algorithm);
        }

        var headScope = new ScopeCtx(algorithm.Parent, algorithm.Opens, algorithm.Properties, names)
        {
            Owner = algorithm,
            Activation = ParameterActivation.Capture(names, ctx, values, inheritedBindingIdentity, invoked),
        };
        return ctx.Push(algorithm, headScope);
    }

    /// <summary>
    /// THE OWNING INVOCATION of a declaring chain (INNER-PROPERTY LIFETIME, November 2026; owner
    /// decision): the binding identity of the nearest level of <paramref name="declaringScope"/>'s
    /// chain that an ACTUAL CALL activated (<see cref="ParameterActivation.OwnsInvocation"/>) — the
    /// fresh identity that call minted — or null when no call owns the chain: the root, a module, a
    /// host scope, a static owner reached by navigation from outside its call. It is the storage
    /// component of every EXPORTED property-style key declared under the chain
    /// (<c>ZeroArgPropertyCacheKey.EnvironmentIdentity</c>): each call of an owner has its own
    /// bindings for the owner's inner properties and runtime-alias cells, reads in the same call
    /// share them — the lexical spelling and a qualified one alike, since a static level is anchored
    /// to its activation on the reader's chain (<see cref="AnchorParents"/>) — and, the chain being
    /// the DECLARING one, no callback, helper, open or referring caller can give a binding another
    /// lifetime. An activation a property-style read recorded is skipped: a read inherits
    /// (CACHE-OWNER-D1), it owns nothing. Null selects the RUN-SCOPED binding, independent of every
    /// activation of the owner before or after. Lean: <c>propertyOwnerInvocation</c>.
    /// <para>The search above the declaring level reads its parent's memoized key facts
    /// (<see cref="Evaluation.Caching.ScopeKeyFacts"/>; implementation-only, 2026-11-22), so a read costs the same at
    /// any depth: the nearest such activation of a chain is a pure function of the chain. The declaring level
    /// itself is read directly — it is often a scope a single read wired, which needs no memo.</para>
    /// </summary>
    internal static object? DeclaringInvocationIdentity(ScopeCtx? declaringScope)
    {
        if (declaringScope is null)
            return null;
        if (declaringScope.Activation is { OwnsInvocation: true } activation)
            return activation.ValueEnvironmentIdentity;
        return Evaluation.Caching.ScopeKeyFacts.ForActivationLookup(declaringScope.Parent).InvocationActivation?.ValueEnvironmentIdentity;
    }

    /// <summary>
    /// Whether <paramref name="algorithm"/> declares a property that is not exported: the
    /// properties whose cache identity a parameterless owner's activation retains
    /// (<see cref="EnterAlgorithmBody"/>). Indexed, so no boxed enumerator per entry.
    /// </summary>
    private static bool HasLocalOnlyProperty(Algorithm algorithm)
    {
        var properties = algorithm.Properties;
        for (var index = 0; index < properties.Count; index++)
        {
            if (properties[index].Exposure != PropertyExposure.Exported)
                return true;
        }

        return false;
    }

    /// <summary>
    /// The binding identity of the nearest ACTIVATED level of <paramref name="declaringScope"/>'s
    /// chain — the context that level's owner was entered in, independent of any consumer — or
    /// null when no level is activated (the root, an unactivated host scope). It keys a local-only
    /// property's cache entry (<c>ZeroArgPropertyCacheKey.FromExecution</c>) and is what a
    /// parameterless owner entered by a property-style read inherits (CACHE-OWNER-D1). Lean:
    /// <c>propertyOwnerBindingContext</c>. Read like <see cref="DeclaringInvocationIdentity"/>
    /// (<see cref="DeclaringActivation"/>).
    /// </summary>
    internal static object? DeclaringBindingIdentity(ScopeCtx? declaringScope)
        => DeclaringActivation(declaringScope)?.ValueEnvironmentIdentity;

    /// <summary>
    /// The activation of the nearest ACTIVATED level of <paramref name="declaringScope"/>'s chain, or null: the
    /// level itself, then its parent's memoized key facts (<see cref="Evaluation.Caching.ScopeKeyFacts"/>).
    /// </summary>
    internal static ParameterActivation? DeclaringActivation(ScopeCtx? declaringScope)
        => declaringScope is null
            ? null
            : declaringScope.Activation ?? Evaluation.Caching.ScopeKeyFacts.ForActivationLookup(declaringScope.Parent).BindingActivation;

    /// <summary>
    /// The scope of the context's head as the site sees it: the activated head scope when the
    /// head was entered with parameters, otherwise the head's plain declaring scope. Null
    /// only for an empty call stack. Lean: <c>siteScope?</c>.
    /// </summary>
    private static ScopeCtx? SiteScope(EvalCtx ctx)
        => ctx.HeadScope ?? (ctx.Head is { } head ? AsScopeCtx(head) : null);

    /// <summary>
    /// The declaring scope of <paramref name="algorithm"/> IN the current context: static
    /// navigation may name the declaration of a currently active lexical ancestor, and then
    /// the active level — same declaration, compatible captured activations — is that scope,
    /// never a dynamically live unrelated caller. The head's own declaring scope in context is
    /// its head scope. Otherwise the algorithm's own level over its ANCHORED parent chain
    /// (<see cref="AnchorParents"/>). Lean: <c>scopeInContext</c>.
    /// </summary>
    private static ScopeCtx ScopeInContext(Algorithm algorithm, EvalCtx ctx)
    {
        if (ctx.Head is not { } site)
            return AsScopeCtx(algorithm);

        if (ReferenceEquals(algorithm, site))
            return ctx.HeadScope ?? AsScopeCtx(algorithm);

        var scope = AsScopeCtx(algorithm);
        var siteScope = SiteScope(ctx);
        var siteLength = 0;
        var siteHasActivation = false;
        for (var level = siteScope; level is not null; level = level.Parent)
        {
            if (IsSameDeclaringScope(scope, level) && CompatibleActivations(scope, level))
                return level;
            siteLength++;
            siteHasActivation |= level.Activation is not null && level.Declaration is not null;
        }

        // Without an activated declaration on the site chain no level can be anchored.
        return siteHasActivation ? AnchorParents(scope, siteScope!, siteLength) : scope;
    }

    /// <summary>
    /// THE ANCHORED CHAIN (E-18; owner decision 2026-11-13): <paramref name="scope"/> over its
    /// parent chain read in the site's context. Walking up, an ACTIVATED level and a level with no
    /// declaration (a host-constructed scope, whose identity is the object itself, or a builtin's)
    /// are kept with everything above them; a static level whose declaration is activated on the
    /// site chain, under compatible captured activations, is that activated site level, and the
    /// levels below it are re-parented onto it. So a member selected from a container obtained
    /// outside its owner's call reads the owner activation its reader is inside, never a same-named
    /// binding of the reader. An activation's own context is never changed — its binding identity keys
    /// property caches and alias cells — so a static owner above an activated level stays static
    /// and <see cref="IsAccessibleFrom"/> refuses its members. Lean: <c>anchorChain</c> with
    /// <c>activatedDeclaration?</c>.
    /// <para>IMPLEMENTATION-ONLY OPTIMIZATION of Lean's search, which tries every site level for
    /// every static level. Two scopes can be the same declaring scope only when their chains are
    /// equally long (<see cref="IsSameDeclaringScope"/> walks both to their ends together), so each
    /// level is compared with the one site level at its own height. A declaration comparison that
    /// fails above its level rules out every level up to that point. Every level of the walk is
    /// static, so a captured-activation disagreement lies above the walk, on every remaining chain
    /// alike, and ends it. Each level is therefore compared once and the walk is linear in the two
    /// chains. It is iterative, because a chain is as deep as lexical nesting, and allocates
    /// nothing unless a level is anchored.</para>
    /// </summary>
    private static ScopeCtx AnchorParents(ScopeCtx scope, ScopeCtx siteScope, int siteLength)
    {
        var length = 0;
        for (var level = scope.Parent; level is not null; level = level.Parent)
            length++;

        // `twin` is the site level at the height of `level`; `deeper` counts the levels of the
        // chain that lie below the whole site chain and so have none.
        ScopeCtx? twin = siteScope;
        for (var drop = siteLength - length; drop > 0; drop--)
            twin = twin!.Parent;
        var deeper = Math.Max(0, length - siteLength);

        var count = 0;
        ScopeCtx? ruledOutThrough = null;
        for (var level = scope.Parent; level is not null; level = level.Parent)
        {
            count++;
            if (level.Activation is not null || level.Declaration is null)
                return scope;
            if (deeper > 0)
            {
                deeper--;
                continue;
            }

            var candidate = twin!;
            twin = candidate.Parent;
            if (ruledOutThrough is not null)
            {
                // A comparison below failed at `ruledOutThrough`, which lies on this level's chain.
                if (ReferenceEquals(level, ruledOutThrough))
                    ruledOutThrough = null;
                continue;
            }

            if (candidate.Activation is null
                || candidate.Declaration is null
                || !IsSameDeclaringLevel(level, candidate))
                continue;
            if (FirstDeclaringMismatch(level.Parent, candidate.Parent) is { } mismatch)
            {
                ruledOutThrough = mismatch;
                continue;
            }

            return CompatibleActivations(level, candidate) ? Reparent(scope, count, candidate) : scope;
        }

        return scope;
    }

    /// <summary>
    /// <paramref name="scope"/> with the <paramref name="count"/>-th level of its parent chain
    /// replaced by <paramref name="anchor"/>: <paramref name="scope"/> and the levels between are
    /// re-parented, keeping their owners and activations.
    /// </summary>
    private static ScopeCtx Reparent(ScopeCtx scope, int count, ScopeCtx anchor)
    {
        var below = new ScopeCtx[count];
        var current = scope;
        for (var i = 0; i < count; i++)
        {
            below[i] = current;
            current = current.Parent!;
        }

        var parent = anchor;
        for (var i = count - 1; i >= 0; i--)
            parent = below[i] with { Parent = parent };
        return parent;
    }

    /// <summary>
    /// The first level of <paramref name="left"/>'s chain at which it and <paramref name="right"/>'s
    /// chain, walked in step, stop being the same declaring scope, or null when they are the same
    /// declaring scope: <see cref="IsSameDeclaringScope"/> of two chains of equal length, which is
    /// how the one caller (<see cref="AnchorParents"/>) aligns them.
    /// </summary>
    private static ScopeCtx? FirstDeclaringMismatch(ScopeCtx? left, ScopeCtx? right)
    {
        while (left is not null && right is not null)
        {
            if (!IsSameDeclaringLevel(left, right))
                return left;
            left = left.Parent;
            right = right.Parent;
        }

        System.Diagnostics.Debug.Assert(left is null && right is null, "AnchorParents compares chains of equal length.");
        return left;
    }

    /// <summary>
    /// Whether every activation <paramref name="required"/> names along its chain is the one
    /// <paramref name="actual"/> carries at the same level; a level that requires no
    /// activation accepts any. Lean: <c>compatibleActivations</c>.
    /// </summary>
    private static bool CompatibleActivations(ScopeCtx? required, ScopeCtx? actual)
    {
        while (required is not null && actual is not null)
        {
            if (required.Activation is { } expected && !ReferenceEquals(expected, actual.Activation))
                return false;
            required = required.Parent;
            actual = actual.Parent;
        }
        return required is null && actual is null;
    }

    private static Algorithm ChildOfInContext(Algorithm parent, Algorithm child, EvalCtx ctx)
        => WithParent(child, ScopeInContext(parent, ctx));

    /// <summary>
    /// HOW A PARAMETER READ FINDS ITS BINDING (EXPORTED-DETACHED, November 2026: captured reads are
    /// LEXICAL-ONLY). Three outcomes, decided by the context alone:
    /// <list type="bullet">
    ///   <item><c>null</c> — the head binds <paramref name="name"/> itself, or NO level of its
    ///   lexical chain binds it (a builtin wrapper's argument, a host-built free parameter): the
    ///   read uses the context's own tiers;</item>
    ///   <item>an activation — the nearest enclosing level binding the name is activated and not
    ///   detached: the read uses that activation's snapshot;</item>
    ///   <item><see cref="ParameterActivation.Unbound"/> / <see cref="ParameterActivation.UnboundDetached"/>
    ///   (<see cref="ParameterActivation.IsUnavailable"/>) — that level is found, but it has no
    ///   activation (a static owner, reached by navigation from outside its call) or its activation
    ///   is DETACHED (<see cref="IsDetached"/>): the name is lexically OWNED and UNAVAILABLE at this
    ///   site. Every executed operation on the written occurrence is REFUSED with
    ///   <see cref="EvalError.UnknownName"/> (<see cref="UnboundParameter"/>): the VALUE read
    ///   (<c>EvalParamCounted</c> and its twin), the CALLABLE projection and callee resolution
    ///   (<c>ResolveNeedParameterAlgorithm</c>) and the direct TRANSPORT of the parameter as a
    ///   supplied argument, callee, link receiver or alias row (<see cref="SupplyCell"/>, whose
    ///   refusal <c>FormNeedSupply</c> reports while the supply is formed, whether or not the
    ///   receiving parameter is ever demanded). None of them consults the context's inherited
    ///   tiers, which hold whatever a dynamically live caller bound under the same name (formerly
    ///   they did: <c>H(y) = G.F(1)</c> read <c>H</c>'s <c>y</c> from inside <c>G</c>). The markers
    ///   hold no binding, so a reader that only looks a cell up — the loop planner, a
    ///   retained-slice classification, a publication origin — finds none and leaves the report to
    ///   the operation that executes.</item>
    /// </list>
    /// Lean: <c>capturedParameter</c> / <c>capturedParameterActivation?</c>.
    /// </summary>
    private static ParameterActivation? CapturedParameterActivation(string name, EvalCtx ctx)
    {
        if (ctx.Head is not { } site)
            return null;

        // The head scope publishes the head's own parameter names (computed once at entry);
        // a head pushed without one reads them from the algorithm (HeadDeclaresParameter).
        if (ctx.HeadScope is { } headScope ? ScopeBindsParameter(headScope, name) : HeadDeclaresParameter(site, name))
            return null;

        if (site.Parent is not { } parent || RequiredParameterOwner(parent, name) is not { } owner)
            return null;
        if (owner.Activation is not { } activation)
            return ParameterActivation.Unbound;
        if (ctx.CallStack is AnnotatedReadOnlyList<Algorithm> annotated)
        {
            if (annotated.DetachedBefore != 0 && activation.Serial < annotated.DetachedBefore)
                return ParameterActivation.UnboundDetached;
            // Inside a retained cell's computation the read is the cell's INPUT READ (ledger R-1; Lean:
            // the `noteCellInput` of `capturedParameterActivation?`) — REFUSED instead when it lands below a
            // reader admitted to the cell while a detached evaluation that detaches the owner is served.
            if (annotated.InputRecord is { } record && record.Note(activation.Serial))
                return ParameterActivation.UnboundDetached;
        }
        return activation;
    }

    /// <summary>
    /// Whether a head pushed WITHOUT a head scope declares <paramref name="name"/>: ordinal membership in its
    /// <c>Params</c> (Lean: <c>x ∈ site.params</c>), read from its stored patterns without projecting them. Only a
    /// user algorithm has names here — a clause family, a builtin or an alias has none — and the head that
    /// actually has them is a loop step the planner pushes to classify its body's references
    /// (<c>LoopOptimizer.TryBuildLoopPlanTemplate</c>) or a fully planned round runs under
    /// (<c>LoopRunFrame.IterationCtx</c>). Until 2026-11-23 every such read projected the head's whole
    /// <c>Params</c> list: one array of N names per captured reference the planner classified, O(N²) bytes for a
    /// wide step whose rows read a captured parameter. Same answer, nothing allocated for a flat head
    /// (<see cref="ParameterPattern.HasCaptureNamed"/>).
    /// </summary>
    private static bool HeadDeclaresParameter(Algorithm site, string name)
        => site is Algorithm.User user && ParameterPattern.HasCaptureNamed(user.ParameterPatterns, name);

    /// <summary>
    /// Whether <paramref name="scope"/>'s parameter list binds <paramref name="name"/>: ordinal membership in
    /// <see cref="ScopeCtx.Parameters"/> (Lean: <c>x ∈ scope.params</c>), the test behind the head's own names
    /// (<see cref="CapturedParameterActivation"/>) and the nearest-owner walk
    /// (<see cref="RequiredParameterOwner"/>). A wide ACTIVATED level answers through the owned-name index its
    /// activation was captured with (<see cref="OwnedNeedBindings.Owned"/>), when that index was built for this
    /// very list; every other level is scanned. Both give the scan's answer.
    /// </summary>
    internal static bool ScopeBindsParameter(ScopeCtx scope, string name)
    {
        var parameters = scope.Parameters;
        return parameters.Count >= MinimumIndexedParameterCount
            && scope.Activation?.Needs is OwnedNeedBindings { Owned: var owned }
            && ReferenceEquals(owned.Names, parameters)
                ? owned.Owns(name)
                : ContainsOrdinal(parameters, name);
    }

    /// <summary>
    /// The failure of an operation on a parameter that no tier binds, or that is UNAVAILABLE at the
    /// site: <see cref="EvalError.UnknownName"/> at the written occurrence. When the name is
    /// unavailable because its lexical owner's activation is DETACHED
    /// (<see cref="ParameterActivation.UnboundDetached"/>), the report says so: the reading property is
    /// classified self-contained, and the name is an input of the call around it. Decided again here,
    /// on the failure path only, from the same context the operation used (only its need tier was
    /// replaced, which the lookup does not read). Never inlined: the operation's frame carries no
    /// error construction (frame-size discipline).
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    internal static EvalError UnboundParameter(string name, SourceSpan? span, EvalCtx ctx)
    {
        var unknown = new EvalError.UnknownName(name) { Span = span };
        return ReferenceEquals(CapturedParameterActivation(name, ctx), ParameterActivation.UnboundDetached)
            ? new EvalError.WithContext(new TextErrorContext(DetachedParameterMessage(name)), unknown) { Span = span }
            : unknown;
    }

    /// <summary>The context of a parameter read refused because its owner's activation is detached.</summary>
    internal static string DetachedParameterMessage(string name)
        => $"parameter '{name}' is an input of the enclosing call, not of an exported (self-contained) property";

    /// <summary>
    /// THE REFUSAL of an executed operation on the written parameter occurrence <paramref name="name"/>
    /// when the name is UNAVAILABLE in <paramref name="ctx"/> (<see cref="CapturedParameterActivation"/>),
    /// or <c>null</c> when the operation may proceed: the head's own name, a name no lexical level
    /// binds (the context's own tiers answer, as before), or an owner whose activation is usable.
    /// Lean: the <c>.unavailable</c> arm of <c>capturedParameterActivation?</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    internal static EvalError? UnavailableParameterRefusal(string name, SourceSpan? span, EvalCtx ctx)
        => CapturedParameterActivation(name, ctx) is { IsUnavailable: true } ? UnboundParameter(name, span, ctx) : null;

    private static EvalCtx ParameterContext(string name, EvalCtx ctx, ref ValEnv values)
    {
        if (CapturedParameterActivation(name, ctx) is not { } activation)
            return ctx;

        values = activation.Values;
        return ctx.WithNeedEnv(activation.Needs);
    }

    internal static bool CapturedParameterNeedsOwnerLookup(string name, EvalCtx ctx, ValEnv values)
    {
        if (CapturedParameterActivation(name, ctx) is not { } activation)
            return false;
        return !ReferenceEquals(LookupVal(activation.Values, name), LookupVal(values, name));
    }
}
