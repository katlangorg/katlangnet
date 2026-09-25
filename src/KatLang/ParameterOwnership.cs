using System.Collections.Immutable;

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
/// shared freely down a descent; extending creates a new map only when there
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
///
/// <para>PERSISTENT (FE-1): the map is an immutable dictionary, so extending a scope that
/// already sees W bindings by a nested algorithm's few parameters shares the W inherited
/// entries and writes only the new ones — K sibling blocks under a wide owner cost O(K) small
/// extensions, never K copies of the owner's map. Each map also records the map it extended
/// and the names that extension added (<see cref="Parent"/>, <see cref="AddedNames"/>): a map's
/// name set is its parent's plus those, which is what lets a semantic-region key canonicalize
/// the captured names incrementally instead of re-sorting every name in scope.</para>
/// </summary>
internal sealed class ParameterOwnership : IOwnedParameterBindings
{
    /// <summary>No parameter binding is in scope (the root body and open-target regions).</summary>
    public static readonly ParameterOwnership Empty = new(
        ImmutableDictionary.Create<string, ElaboratedPropertyScope>(StringComparer.Ordinal),
        neverCalledOwner: null,
        parent: null,
        addedNames: []);

    private readonly ImmutableDictionary<string, ElaboratedPropertyScope> _owners;
    private readonly ElaboratedPropertyScope? _neverCalledOwner;

    private ParameterOwnership(
        ImmutableDictionary<string, ElaboratedPropertyScope> owners,
        ElaboratedPropertyScope? neverCalledOwner,
        ParameterOwnership? parent,
        IReadOnlyList<string> addedNames)
    {
        _owners = owners;
        _neverCalledOwner = neverCalledOwner;
        Parent = parent;
        AddedNames = addedNames;
    }

    /// <summary>The map this one extended; null only for <see cref="Empty"/>.</summary>
    internal ParameterOwnership? Parent { get; }

    /// <summary>The names the extension that built this map added (its name set is its <see cref="Parent"/>'s plus these).</summary>
    internal IReadOnlyList<string> AddedNames { get; }

    /// <summary>
    /// Every parameter name currently in scope, innermost binding per name, in no
    /// particular order (never a signature order). Front-end passes do not enumerate
    /// it per nested scope: a name set is derived incrementally from
    /// <see cref="Parent"/> and <see cref="AddedNames"/> (FE-1).
    /// </summary>
    public IEnumerable<string> Names => _owners.Keys;

    public bool Contains(string name) => _owners.ContainsKey(name);

    public bool DeclaresParameter(ElaboratedPropertyScope level, string name)
        => _owners.TryGetValue(name, out var owner)
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
        bool ownerIsNeverCalled = false,
        FrontEndTraversalObservations? observations = null)
    {
        ImmutableDictionary<string, ElaboratedPropertyScope>.Builder? extended = null;
        List<string>? added = null;
        foreach (var name in names)
        {
            extended ??= _owners.ToBuilder();
            extended[name] = owner;
            (added ??= []).Add(name);
            observations?.RecordContextEntryWritten();
        }

        if (extended is null)
            return this;

        return new ParameterOwnership(
            extended.ToImmutable(),
            ownerIsNeverCalled ? owner : _neverCalledOwner,
            this,
            added!);
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
