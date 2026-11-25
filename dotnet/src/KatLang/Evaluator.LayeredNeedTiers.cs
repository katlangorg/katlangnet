using System.Collections;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;

namespace KatLang;

public static partial class Evaluator
{
    /// <summary>
    /// The need tier a binding boundary mints for its callee (Lean <c>needBindingContext</c>): the callee's own
    /// cells <paramref name="bindings"/> before the inherited tier with the callee's names shadowed out of it
    /// (<c>bindings ++ ctx.needEnv.filter (fun entry =&gt; !names.contains entry.fst)</c>,
    /// <c>EvalCtx.bindParameters</c>). A NARROW boundary over a WIDE tier the evaluator made keeps that tier as its base
    /// instead of copying it (<see cref="LayeredBoundNeedEnv"/>); every other boundary copies both parts into a fresh list
    /// (<see cref="Concat(NeedEnv, NeedEnv)"/> over <see cref="UnshadowedBindings"/>), as before. Either way the
    /// tier is a fresh object, which is the callee's binding-context identity
    /// (<see cref="BindingContextIdentity"/>). Out of line, so the binding sites' frames do not hold the decision.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static NeedEnv MintNeedBindingContext(NeedEnv bindings, NeedEnv inherited, IReadOnlyList<string> names)
        => LayeredBoundNeedEnv.TryMint(bindings, inherited, names) ?? Concat(bindings, UnshadowedBindings(inherited, names));

    /// <summary>
    /// A WIDE shadowed tier the evaluator made once and never changes: the loop planner's step context
    /// (<see cref="ShadowInheritedParameterEnvironments"/>, at least <see cref="MinimumIndexedParameterCount"/> kept
    /// bindings) — the loop context's tier with the step's state names shadowed out, in order: the shadow filter's own
    /// fresh array, wrapped, not copied. It is no binding boundary (its identity is the one a nonempty tier always had,
    /// <see cref="BindingContextIdentity"/>); being recognizably the evaluator's and immutable, it can be the base of the
    /// tier a planned round's boundary mints (<see cref="LayeredBoundNeedEnv"/>), which then layers over it instead of
    /// copying it every round.
    /// </summary>
    internal sealed class ShadowedNeedEnv : IReadOnlyList<(string Name, NeedCell Cell)>
    {
        private readonly NeedEnv _bindings;

        // `bindings` is the shadow filter's fresh array (UnshadowedBindings), which nothing else holds.
        internal ShadowedNeedEnv(NeedEnv bindings)
            => _bindings = bindings;

        /// <summary>The number of bindings.</summary>
        public int Count => _bindings.Count;

        /// <summary>The binding at <paramref name="index"/>.</summary>
        public (string Name, NeedCell Cell) this[int index] => _bindings[index];

        /// <summary>The bindings, in order.</summary>
        public IEnumerator<(string Name, NeedCell Cell)> GetEnumerator() => _bindings.GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }

    /// <summary>
    /// The tier a NARROW binding boundary mints over a WIDE inherited tier (implementation-only, 2026-11-24,
    /// follow-up of the wide parameter frame audit): the same ordered association list Lean's
    /// <c>needBindingContext</c> builds — the boundary's own cells, then the inherited tier with the boundary's names
    /// shadowed out — held as three parts instead of a copy:
    /// <list type="bullet">
    /// <item>a narrow PREFIX: the boundary's own cells, then the cells of the layer it was composed over that its names
    /// do not shadow (fewer than <see cref="MinimumIndexedParameterCount"/> bindings);</item>
    /// <item>a BASE: a flat tier the evaluator made and never changes — one a binding boundary minted
    /// (<see cref="BoundNeedEnv"/>) or a planned loop's shadowed step tier (<see cref="ShadowedNeedEnv"/>) — of at least
    /// <see cref="MinimumIndexedParameterCount"/> bindings, never a layered one, shared, never copied;</item>
    /// <item>the SHADOWED names: every name hidden from the base — this boundary's and those of the layers it was
    /// composed over (fewer than <see cref="MinimumIndexedParameterCount"/>).</item>
    /// </list>
    /// So the tier is <c>prefix ++ base.filter (name ∉ shadowed)</c>. A layer minted over a layer composes, by
    /// <c>filter (p ++ q) = filter p ++ filter q</c> and <c>filter a (filter b q) = filter (a ∧ b) q</c>: its prefix is
    /// its own cells and the parent's prefix minus its names, its base the parent's base, its shadowed names the
    /// union. A boundary under a layer therefore never reads through more than one layer, and a layer retains one
    /// base and no other layer, whatever the depth of a recursion or the number of loop rounds above it. A composition
    /// whose prefix or names would reach <see cref="MinimumIndexedParameterCount"/> is minted as the flat copy
    /// instead, and calls below it layer over that copy.
    /// <para>Before, every such boundary copied the inherited tier twice (the shadow filter, then the prepend) and its
    /// body's activation scanned the copy: a narrow call under a tier of N cells allocated about 32·N bytes and read
    /// 3·N inherited bindings, so a wide loop step whose N rows each make one narrow call (the <c>loopreads</c> shape of
    /// the wide-binding report) allocated about 35 MB per round at N = 1,024.</para>
    /// <para>EQUIVALENCE with the flat list: <see cref="Find"/> gives its ordered first match (a name of the prefix is
    /// found there first; a shadowed name has no binding in the filtered base; any other name's first binding in the
    /// filtered base is its first binding in the base, which keeps its order), and <see cref="Count"/>, the indexer and
    /// the enumerator are that very list, built once on first use (<see cref="IsMaterialized"/>). The cells are the
    /// inherited cells themselves, so VALUE and CALLABLE channels, memoized outcomes and flights are shared exactly as
    /// the copy shared them. A host-built inherited list is never a base: only the evaluator's own tiers
    /// (<see cref="BoundNeedEnv"/>, <see cref="ShadowedNeedEnv"/>), which nothing changes after they are made, are
    /// shared, so a later edit of a host list cannot reach a tier minted over it.
    /// Each boundary mints a fresh layer, which is its binding-context identity
    /// (<see cref="BindingContextIdentity"/>) like the fresh list it replaces. Lean: <c>needBindingContext</c>,
    /// unchanged.</para>
    /// </summary>
    internal sealed class LayeredBoundNeedEnv : IReadOnlyList<(string Name, NeedCell Cell)>
    {
        private readonly NeedEnv _prefix;
        // A BoundNeedEnv or a ShadowedNeedEnv (TryMint).
        private readonly NeedEnv _base;
        private readonly IReadOnlyList<string> _shadowed;
        // The boundary's own names (the callee's names read at the boundary): what the activation entered over this tier
        // is captured for, every one of them shadowed out of the base.
        private readonly IReadOnlyList<string> _names;
        private (string Name, NeedCell Cell)[]? _flat;

        private LayeredBoundNeedEnv(NeedEnv prefix, NeedEnv @base, IReadOnlyList<string> shadowed, IReadOnlyList<string> names)
        {
            _prefix = prefix;
            _base = @base;
            _shadowed = shadowed;
            _names = names;
        }

        /// <summary>
        /// The layered tier of a boundary binding <paramref name="own"/> for <paramref name="names"/> under
        /// <paramref name="inherited"/>, or null when the boundary copies: a boundary of at least
        /// <see cref="MinimumIndexedParameterCount"/> cells or names, an inherited tier that is neither a layer nor an
        /// evaluator-made flat tier (<see cref="BoundNeedEnv"/>, <see cref="ShadowedNeedEnv"/>) of at least
        /// <see cref="MinimumIndexedParameterCount"/> bindings (a narrow tier is cheaper to copy; a host-built one is not
        /// shared), or a composition that would reach the limit. The binding sites supply evaluator-owned cells and
        /// names in lists that stay unchanged. Loop rounds may reuse their prepared step's names.
        /// </summary>
        internal static LayeredBoundNeedEnv? TryMint(NeedEnv own, NeedEnv inherited, IReadOnlyList<string> names)
        {
            if (own.Count >= MinimumIndexedParameterCount || names.Count >= MinimumIndexedParameterCount)
                return null;
            if (inherited is LayeredBoundNeedEnv layered)
                return layered.Compose(own, names);
            return inherited is BoundNeedEnv or ShadowedNeedEnv && inherited.Count >= MinimumIndexedParameterCount
                ? new LayeredBoundNeedEnv(own, inherited, names, names)
                : null;
        }

        // The layer of a boundary minted over this one: `own ++ filter(prefix, names)` over the same base, shadowing the
        // union of the names; null when either part would reach the limit.
        private LayeredBoundNeedEnv? Compose(NeedEnv own, IReadOnlyList<string> names)
        {
            var prefix = _prefix;
            var kept = 0;
            for (var i = 0; i < prefix.Count; i++)
                if (!ContainsOrdinal(names, prefix[i].Name)) kept++;
            if (own.Count + kept >= MinimumIndexedParameterCount)
                return null;
            if (UnionOfNames(_shadowed, names) is not { } shadowed)
                return null;
            if (kept == 0)
                return new LayeredBoundNeedEnv(own, _base, shadowed, names);

            var composed = new (string Name, NeedCell Cell)[own.Count + kept];
            var next = 0;
            for (var i = 0; i < own.Count; i++)
                composed[next++] = own[i];
            for (var i = 0; i < prefix.Count && next < composed.Length; i++)
                if (!ContainsOrdinal(names, prefix[i].Name))
                    composed[next++] = prefix[i];
            return new LayeredBoundNeedEnv(composed, _base, shadowed, names);
        }

        // `shadowed` itself when it already holds every name of `names` (a recursion re-binding its own names), else a
        // fresh list of `shadowed` followed by the other names once each, in their order; null when that would reach
        // the limit. Membership is ordinal, a null name included, as in ContainsOrdinal.
        private static IReadOnlyList<string>? UnionOfNames(IReadOnlyList<string> shadowed, IReadOnlyList<string> names)
        {
            var added = 0;
            for (var i = 0; i < names.Count; i++)
                if (IsNewName(shadowed, names, i)) added++;
            if (added == 0)
                return shadowed;
            if (shadowed.Count + added >= MinimumIndexedParameterCount)
                return null;

            var union = new string[shadowed.Count + added];
            var next = 0;
            for (var i = 0; i < shadowed.Count; i++)
                union[next++] = shadowed[i];
            for (var i = 0; i < names.Count; i++)
                if (IsNewName(shadowed, names, i))
                    union[next++] = names[i];
            return union;
        }

        // Whether names[index] is in neither `shadowed` nor an earlier position of `names`.
        private static bool IsNewName(IReadOnlyList<string> shadowed, IReadOnlyList<string> names, int index)
        {
            var name = names[index];
            if (ContainsOrdinal(shadowed, name))
                return false;
            for (var i = 0; i < index; i++)
                if (string.Equals(names[i], name, StringComparison.Ordinal))
                    return false;
            return true;
        }

        /// <summary>The cell of the first binding named <paramref name="name"/>, or null: the ordered scan's answer.</summary>
        internal NeedCell? Find(string name)
        {
            var prefix = _prefix;
            for (var i = 0; i < prefix.Count; i++)
            {
                var binding = prefix[i];
                if (binding.Name == name) return binding.Cell;
            }

            return ContainsOrdinal(_shadowed, name) ? null : LookupNeed(_base, name);
        }

        /// <summary>
        /// Where the first binding of each of <paramref name="names"/> lies (<see cref="ParameterActivation.Capture"/>):
        /// the prefix when every name is shadowed out of the base — the boundary's own names always are — since no
        /// binding of such a name is left in the filtered base; this whole tier otherwise.
        /// </summary>
        internal NeedEnv OwnedPart(IReadOnlyList<string> names)
        {
            if (ReferenceEquals(names, _names))
                return _prefix;
            if (names.Count >= MinimumIndexedParameterCount)
                return this;
            for (var i = 0; i < names.Count; i++)
                if (!ContainsOrdinal(_shadowed, names[i]))
                    return this;
            return _prefix;
        }

        /// <summary>
        /// This tier with <paramref name="names"/> shadowed out of it (<see cref="UnshadowedBindings"/>): the bindings
        /// the flat list keeps, in its order, as a fresh array or the shared empty one — the flat filter's own result —
        /// read from the prefix and the base without building the flat list.
        /// </summary>
        internal NeedEnv Unshadowed(IReadOnlyList<string> names)
        {
            // A wide name list is tested through one ordinal set (null included), as UnshadowedWideBindings does.
            var set = names.Count >= MinimumIndexedParameterCount ? new HashSet<string>(names, StringComparer.Ordinal) : null;
            var prefix = _prefix;
            var kept = 0;
            for (var i = 0; i < prefix.Count; i++)
                if (!IsIn(set, names, prefix[i].Name)) kept++;
            for (var i = 0; i < _base.Count; i++)
            {
                var name = _base[i].Name;
                if (!ContainsOrdinal(_shadowed, name) && !IsIn(set, names, name)) kept++;
            }
            if (kept == 0)
                return Array.Empty<(string Name, NeedCell Cell)>();

            var bindings = new (string Name, NeedCell Cell)[kept];
            var next = 0;
            for (var i = 0; i < prefix.Count; i++)
                if (!IsIn(set, names, prefix[i].Name))
                    bindings[next++] = prefix[i];
            for (var i = 0; i < _base.Count && next < kept; i++)
            {
                var binding = _base[i];
                if (!ContainsOrdinal(_shadowed, binding.Name) && !IsIn(set, names, binding.Name))
                    bindings[next++] = binding;
            }
            return bindings;
        }

        private static bool IsIn(HashSet<string>? set, IReadOnlyList<string> names, string name)
            => set?.Contains(name) ?? ContainsOrdinal(names, name);

        /// <summary>The number of bindings of the flat list (built on first use).</summary>
        public int Count => Flat.Length;

        /// <summary>The binding at <paramref name="index"/> of the flat list (built on first use).</summary>
        public (string Name, NeedCell Cell) this[int index] => Flat[index];

        /// <summary>The bindings of the flat list, in order (built on first use).</summary>
        public IEnumerator<(string Name, NeedCell Cell)> GetEnumerator()
            => ((IEnumerable<(string Name, NeedCell Cell)>)Flat).GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

        // The flat list `prefix ++ base.filter (name ∉ shadowed)`, built once; concurrent first readers may each build it,
        // and every reader uses the published one (equal in content either way).
        private (string Name, NeedCell Cell)[] Flat => Volatile.Read(ref _flat) ?? Materialize();

        private (string Name, NeedCell Cell)[] Materialize()
        {
            var prefix = _prefix;
            var kept = 0;
            for (var i = 0; i < _base.Count; i++)
                if (!ContainsOrdinal(_shadowed, _base[i].Name)) kept++;
            var flat = new (string Name, NeedCell Cell)[prefix.Count + kept];
            var next = 0;
            for (var i = 0; i < prefix.Count; i++)
                flat[next++] = prefix[i];
            for (var i = 0; i < _base.Count && next < flat.Length; i++)
            {
                var binding = _base[i];
                if (!ContainsOrdinal(_shadowed, binding.Name))
                    flat[next++] = binding;
            }

            return Interlocked.CompareExchange(ref _flat, flat, null) ?? flat;
        }

        /// <summary>Whether the flat list has been built (a test observation: a narrow call's own reads never build it).</summary>
        internal bool IsMaterialized => Volatile.Read(ref _flat) is not null;

        /// <summary>The shared base tier (a test observation).</summary>
        internal NeedEnv Base => _base;

        /// <summary>The prefix: the boundary's own cells, then the kept cells of the layer it was composed over (a test observation).</summary>
        internal NeedEnv Prefix => _prefix;

        /// <summary>The names shadowed out of the base (a test observation).</summary>
        internal IReadOnlyList<string> ShadowedNames => _shadowed;
    }
}
