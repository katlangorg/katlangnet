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
/// <para>NEAREST WINS BY CONSTRUCTION: an extension overwrites (or, for a template
/// layer, shadows) an inherited entry, so an inner algorithm's parameter shadows a
/// same-named outer one before any walk begins and exactly one level ever answers
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
/// level records itself through an extension's <c>ownerIsNeverCalled</c> argument
/// and every map derived from it inherits the mark, so deferred branch contexts
/// carry the same exemption.</para>
///
/// <para>PERSISTENT (FE-1): the map is an immutable dictionary, so extending a scope that
/// already sees W bindings by a nested algorithm's few parameters shares the W inherited
/// entries and writes only the new ones — K sibling blocks under a wide owner cost O(K) small
/// extensions, never K copies of the owner's map. Each map also records the map it extended
/// and what that extension added (<see cref="Parent"/>, <see cref="AddedNames"/>,
/// <see cref="AddedTemplate"/>): a map's name set is its parent's plus those, which is what lets a
/// semantic-region key canonicalize the captured names incrementally instead of re-sorting every
/// name in scope.</para>
///
/// <para>TEMPLATE LAYERS (FE-3): an owner whose completed signature is a wide shared
/// implicit-signature template (<see cref="ImplicitSignatureTemplate"/>) extends the map by ONE
/// layer — "every name of this template belongs to this level" — instead of writing one entry per
/// name, so K owners that each lift the same L-wide signature cost K layers, never K × L entries.
/// The layer's owner is its own level (owner identity is never shared through the template). A
/// lookup consults the entries written since the nearest layer, then each layer outward (the
/// entries beneath a layer are shadowed by it), so its cost is the number of template layers on the
/// lexical chain, which the front end's structural depth ceiling bounds.</para>
/// </summary>
internal sealed class ParameterOwnership : IOwnedParameterBindings
{
    /// <summary>
    /// The smallest template that extends by a LAYER; a narrower one is written as entries (a few
    /// writes are cheaper than a layer every later lookup must consult).
    /// </summary>
    internal const int TemplateLayerMinimum = 8;

    /// <summary>No parameter binding is in scope (the root body and open-target regions).</summary>
    public static readonly ParameterOwnership Empty = new(
        ImmutableDictionary.Create<string, ElaboratedPropertyScope>(StringComparer.Ordinal),
        neverCalledOwner: null,
        parent: null,
        addedNames: [],
        below: null,
        template: null,
        templateOwner: null);

    // The entries written since the nearest template layer beneath this map (a persistent
    // dictionary, FE-1); for a template layer, empty.
    private readonly ImmutableDictionary<string, ElaboratedPropertyScope> _owners;
    private readonly ElaboratedPropertyScope? _neverCalledOwner;

    // The nearest template layer beneath this map's entries (for a layer: the map it extended).
    private readonly ParameterOwnership? _below;
    private readonly ImplicitSignatureTemplate? _template;
    private readonly ElaboratedPropertyScope? _templateOwner;

    private ParameterOwnership(
        ImmutableDictionary<string, ElaboratedPropertyScope> owners,
        ElaboratedPropertyScope? neverCalledOwner,
        ParameterOwnership? parent,
        IReadOnlyList<string> addedNames,
        ParameterOwnership? below,
        ImplicitSignatureTemplate? template,
        ElaboratedPropertyScope? templateOwner)
    {
        _owners = owners;
        _neverCalledOwner = neverCalledOwner;
        Parent = parent;
        AddedNames = addedNames;
        _below = below;
        _template = template;
        _templateOwner = templateOwner;
    }

    /// <summary>The map this one extended; null only for <see cref="Empty"/>.</summary>
    internal ParameterOwnership? Parent { get; }

    /// <summary>The names the extension that built this map wrote as entries (its name set is its <see cref="Parent"/>'s plus these and <see cref="AddedTemplate"/>'s).</summary>
    internal IReadOnlyList<string> AddedNames { get; }

    /// <summary>The template whose names the extension that built this map added as ONE layer (FE-3), or null.</summary>
    internal ImplicitSignatureTemplate? AddedTemplate => _template;

    /// <summary>
    /// Every parameter name currently in scope, innermost binding per name, in no
    /// particular order (never a signature order). Front-end passes do not enumerate
    /// it per nested scope: a name set is derived incrementally from
    /// <see cref="Parent"/>, <see cref="AddedNames"/>, and <see cref="AddedTemplate"/> (FE-1).
    /// </summary>
    public IEnumerable<string> Names
    {
        get
        {
            var seen = new HashSet<string>(StringComparer.Ordinal);
            for (var node = this; node is not null; node = node._below)
            {
                IEnumerable<string> names = node._template is { } template ? template.Facts.NameSet : node._owners.Keys;
                foreach (var name in names)
                {
                    if (seen.Add(name))
                        yield return name;
                }
            }
        }
    }

    public bool Contains(string name) => OwnerOf(name) is not null;

    public bool DeclaresParameter(ElaboratedPropertyScope level, string name)
        => OwnerOf(name) is { } owner && ReferenceEquals(owner, level);

    // The nearest binding of a name: the entries written since the nearest layer, then each
    // layer outward (every entry beneath a layer is shadowed by it for the layer's names).
    private ElaboratedPropertyScope? OwnerOf(string name)
    {
        for (var node = this; node is not null; node = node._below)
        {
            if (node._template is { } template)
            {
                if (template.Facts.NameSet.Contains(name))
                    return node._templateOwner;
            }
            else if (node._owners.TryGetValue(name, out var owner))
            {
                return owner;
            }
        }

        return null;
    }

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
            // Entries written over a layer start a new entry segment above it.
            extended ??= _template is null ? _owners.ToBuilder() : Empty._owners.ToBuilder();
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
            added!,
            below: _template is null ? _below : this,
            template: null,
            templateOwner: null);
    }

    /// <summary>
    /// The bindings in scope inside <paramref name="owner"/>'s body when its completed signature is
    /// <paramref name="signature"/>: every one of its names owned by that level. A wide shared
    /// template (or a composed signature's shared tail) is added as ONE layer, its owner-local head
    /// as ordinary entries above it; anything else is written name by name exactly like
    /// <see cref="Extend"/> (FE-3).
    /// </summary>
    public ParameterOwnership ExtendSignature(
        ElaboratedPropertyScope owner,
        IReadOnlyList<ParameterPattern> signature,
        bool ownerIsNeverCalled = false,
        FrontEndTraversalObservations? observations = null)
    {
        if (signature is not ImplicitSignatureTemplate template)
            return Extend(owner, ParameterPattern.EnumerateCaptures(signature).Select(static capture => capture.Name), ownerIsNeverCalled, observations);

        var tail = template.Tail ?? template;
        if (tail.Facts.CaptureCount < TemplateLayerMinimum)
            return Extend(owner, template.Facts.Names, ownerIsNeverCalled, observations);

        observations?.RecordContextTemplateLayer();
        var layered = new ParameterOwnership(
            Empty._owners,
            ownerIsNeverCalled ? owner : _neverCalledOwner,
            this,
            addedNames: [],
            below: this,
            tail,
            owner);
        return template.IsComposed
            ? layered.Extend(owner, ParameterPattern.EnumerateCaptures(template.Head).Select(static capture => capture.Name), ownerIsNeverCalled, observations)
            : layered;
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
