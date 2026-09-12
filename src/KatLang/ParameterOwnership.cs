namespace KatLang;

/// <summary>
/// The parameter bindings visible to a front-end walk, each mapped to the scope
/// LEVEL that owns it: an algorithm's own explicit and inferred parameters at
/// its own level, a conditional branch body's pattern binders at the branch
/// body's level, and every such binding inherited from an enclosing owner at
/// the level that declared it.
///
/// <para>Owner identity is what a plain name set cannot express, and it is the
/// whole point of this type: "is this name a parameter?" was never the question
/// — "which owner declares it, and is that owner nearer than the nearest owner
/// declaring a property of the same name?" is. The map is consumed by
/// <see cref="ElaboratedScopeLookup.SelectOwnedDeclaration"/>, which walks the
/// ordered level chain and asks each level in turn; the chain, not a counted
/// depth, is what establishes which owner is nearer.</para>
///
/// <para>NEAREST WINS BY CONSTRUCTION: <see cref="Extend"/> overwrites an
/// inherited entry, so an inner algorithm's parameter shadows a same-named outer
/// one before any walk begins and exactly one level ever answers
/// <see cref="DeclaresParameter"/> for a name. Instances are immutable and
/// shared freely down a descent; extending allocates a new map only when there
/// is something to add.</para>
///
/// <para>THE NEVER-CALLED OWNER: the program root is never called, so its
/// completed signature binds nothing — every root parameter is a name the root
/// could not resolve (or a name forwarding lifted into it), and evaluation
/// reports exactly that (<see cref="EvalError.UnresolvedImplicitParams"/>).
/// Those phantom inputs still take part in reference classification (a nested
/// reference to one elaborates to the <see cref="Expr.Param"/> the root's error
/// then explains), but they are not CALLABLE bindings: the collision validator
/// checks them against the root's own declarations only, and static
/// <c>open</c>-target classification (<see cref="CallableBindings"/>) never
/// treats one as the owner of an open target's head name — a nested
/// <c>open Q</c> beside an unresolved root row <c>Q.X</c> stays the static
/// lookup it always was, never a "parameter cannot be opened" report. The root
/// level records itself through <see cref="Extend"/>'s
/// <c>ownerIsNeverCalled</c> argument and every map derived from it inherits
/// the mark, so deferred branch contexts carry the same exemption.</para>
/// </summary>
internal sealed class ParameterOwnership : IOwnedParameterBindings
{
    /// <summary>No parameter binding is in scope (the root body and open-target regions).</summary>
    public static readonly ParameterOwnership Empty = new(owners: null, neverCalledOwner: null);

    private static readonly string[] NoNames = [];

    private readonly Dictionary<string, ElaboratedPropertyScope>? _owners;
    private readonly ElaboratedPropertyScope? _neverCalledOwner;

    private ParameterOwnership(
        Dictionary<string, ElaboratedPropertyScope>? owners,
        ElaboratedPropertyScope? neverCalledOwner)
    {
        _owners = owners;
        _neverCalledOwner = neverCalledOwner;
    }

    /// <summary>
    /// Every parameter name currently in scope, innermost binding per name.
    /// Order-independent: callers use it for bound-name membership, region keys,
    /// and diagnostic candidate enumeration, never for signature order.
    /// </summary>
    public IReadOnlyCollection<string> Names => (IReadOnlyCollection<string>?)_owners?.Keys ?? NoNames;

    public bool Contains(string name) => _owners is not null && _owners.ContainsKey(name);

    public bool DeclaresParameter(ElaboratedPropertyScope level, string name)
        => _owners is not null
            && _owners.TryGetValue(name, out var owner)
            && ReferenceEquals(owner, level);

    /// <summary>
    /// The bindings a CALL establishes: this map without the never-called
    /// program root's phantom signature. This is the owner-walk input for
    /// decisions that ask "does a callable parameter own this name?" — today
    /// the static <c>open</c>-target head classification
    /// (<c>ParameterDetector.ClassifyOpenTargetHeads</c>) — while reference
    /// and receiver classification keep reading the full map. Returns this
    /// instance itself when no never-called owner was recorded, so the common
    /// nested-owner case allocates nothing.
    /// </summary>
    public IOwnedParameterBindings CallableBindings
        => _neverCalledOwner is null ? this : new CallableParameterBindings(this);

    /// <summary>
    /// The bindings in scope inside <paramref name="owner"/>'s body: these
    /// bindings owned by that level, over everything inherited. A same-named
    /// inherited binding is REPLACED, which is exactly the shadowing the level
    /// chain would otherwise have to re-derive. <paramref name="ownerIsNeverCalled"/>
    /// marks <paramref name="owner"/> as the program root level whose
    /// signature no call binds (see the class documentation); the mark is
    /// inherited by every map derived from the result.
    /// </summary>
    public ParameterOwnership Extend(
        ElaboratedPropertyScope owner,
        IEnumerable<string> names,
        bool ownerIsNeverCalled = false)
    {
        Dictionary<string, ElaboratedPropertyScope>? extended = null;
        foreach (var name in names)
        {
            extended ??= _owners is null
                ? new Dictionary<string, ElaboratedPropertyScope>(StringComparer.Ordinal)
                : new Dictionary<string, ElaboratedPropertyScope>(_owners, StringComparer.Ordinal);
            extended[name] = owner;
        }

        if (extended is null)
            return this;

        return new ParameterOwnership(extended, ownerIsNeverCalled ? owner : _neverCalledOwner);
    }

    /// <summary>
    /// The callable-bindings view of one map: identical to the map at every
    /// level except the never-called program root, whose entries answer
    /// <c>false</c> so the owner walk continues to the root's own properties
    /// and beyond exactly as if the phantom signature were absent.
    /// </summary>
    private sealed class CallableParameterBindings(ParameterOwnership inner) : IOwnedParameterBindings
    {
        public bool DeclaresParameter(ElaboratedPropertyScope level, string name)
            => !ReferenceEquals(level, inner._neverCalledOwner)
                && inner.DeclaresParameter(level, name);
    }
}
