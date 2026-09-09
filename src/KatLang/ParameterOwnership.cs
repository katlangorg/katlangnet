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
/// </summary>
internal sealed class ParameterOwnership : IOwnedParameterBindings
{
    /// <summary>No parameter binding is in scope (the root body and open-target regions).</summary>
    public static readonly ParameterOwnership Empty = new(owners: null);

    private static readonly string[] NoNames = [];

    private readonly Dictionary<string, ElaboratedPropertyScope>? _owners;

    private ParameterOwnership(Dictionary<string, ElaboratedPropertyScope>? owners) => _owners = owners;

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
    /// The bindings in scope inside <paramref name="owner"/>'s body: these
    /// bindings owned by that level, over everything inherited. A same-named
    /// inherited binding is REPLACED, which is exactly the shadowing the level
    /// chain would otherwise have to re-derive.
    /// </summary>
    public ParameterOwnership Extend(ElaboratedPropertyScope owner, IEnumerable<string> names)
    {
        Dictionary<string, ElaboratedPropertyScope>? extended = null;
        foreach (var name in names)
        {
            extended ??= _owners is null
                ? new Dictionary<string, ElaboratedPropertyScope>(StringComparer.Ordinal)
                : new Dictionary<string, ElaboratedPropertyScope>(_owners, StringComparer.Ordinal);
            extended[name] = owner;
        }

        return extended is null ? this : new ParameterOwnership(extended);
    }
}
