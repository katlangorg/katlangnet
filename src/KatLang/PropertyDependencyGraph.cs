using System.Runtime.CompilerServices;

namespace KatLang;

internal readonly record struct OwnerQualifiedParameter(string Name, Algorithm? Owner)
{
    private sealed record Identity(long Value);
    private static long _nextIdentity;
    private static readonly ConditionalWeakTable<Algorithm, Identity> Identities = new();
    internal static long OwnerKey(Algorithm owner) => Identities.GetValue(owner, static _ => new(Interlocked.Increment(ref _nextIdentity))).Value;
    internal string ContentKey => $"{(Owner is null ? 0 : OwnerKey(Owner))}:{Name.Length}:{Name}";

    /// <summary>
    /// <see cref="ContentKey"/> with the process-wide owner id written as the one character <c>#</c>. Observation
    /// only (<see cref="FrontEndTraversalObservations.SummaryKeyCharacters"/>): it is no identity, since owners share it.
    /// </summary>
    internal string IdFreeContentKey => $"{(Owner is null ? "0" : "#")}:{Name.Length}:{Name}";

    public bool Equals(OwnerQualifiedParameter other) => Name == other.Name && ReferenceEquals(Owner, other.Owner);
    public override int GetHashCode() => HashCode.Combine(Name, Owner is null ? 0 : RuntimeHelpers.GetHashCode(Owner));
}

internal sealed record PropertyDependencySummaryNode(
    int PropertyIndex,
    IReadOnlyList<int> SummarySiblingDependencyIndices,
    IReadOnlyList<string> SummaryVisiblePropertyDependencyNames,
    IReadOnlyList<string> RequiredAncestorOwnedParameterNames,
    IReadOnlyList<PendingReference> PendingReferences,
    IReadOnlyList<OwnerQualifiedParameter> OwnerQualifiedParameters);

/// <summary>
/// A reference the scope-free summary walk could not reduce to a bare visible name: a
/// static member PATH (<c>Inner.X</c> — <see cref="Head"/> <c>Inner</c>, <see cref="Members"/>
/// <c>[X]</c>), a name or path anchored at the completed context it was written in
/// (<see cref="Origin"/>), or the open-target walks of a level (<see cref="Selection"/>). It names
/// WHAT is read and from where, never which declaration provides it: the owning level's resolver
/// settles it from the completed structure of the origin's chain with the ownership-first rule —
/// the head as a PROPERTY of the chain first, then the <c>open</c> providers of the levels the
/// lookup consults, one level at a time (Lean/evaluator: <c>lookupLexicalProperty</c> then
/// <c>lookupOpenPropertiesInChain</c>). Navigated members charge THEIR requirement summaries —
/// that is what makes a container that reads a captured member through <c>Inner.X</c> or
/// <c>open Inner</c> itself local-only. Immutable; equality is by content so a summary fixed
/// point can compare seeds.
/// </summary>
internal sealed class PendingReference : IEquatable<PendingReference>
{
    public PendingReference(string head, IReadOnlyList<string> members,
        IReadOnlyList<Algorithm>? boundOwners = null, CompletedStructureContext? origin = null, bool openPath = false,
        PendingSelection selection = PendingSelection.Lexical)
    {
        Origin = origin;
        OpenPath = openPath;
        Selection = selection;
        Head = head;
        Members = members;
        BoundOwners = boundOwners ?? [];
        var originKey = origin is null ? "" : selection == PendingSelection.Lexical
            ? $"completed:{origin.Identity}:{openPath}" : $"completed:{origin.Identity}:{openPath}:{selection}";
        ResolutionKey = KeyParts([originKey, head, KeyParts(members), NoProviderKeys]);
        var boundKey = string.Join(",", BoundOwners.Select(OwnerQualifiedParameter.OwnerKey).Order());
        ContentKey = KeyParts([ResolutionKey, boundKey]);
    }

    /// <summary>
    /// The fourth part of every reference key, always empty. Reference keys once serialized the open providers a
    /// reference carried there; no reference carries one (the settlement selects providers), and the part stays so
    /// that every key keeps its exact text: key lengths are observed work
    /// (<see cref="FrontEndTraversalObservations.SummaryKeyCharacters"/>) and weigh the settlement share's entries.
    /// </summary>
    private const string NoProviderKeys = "";

    internal CompletedStructureContext? Origin { get; }
    internal bool OpenPath { get; }

    /// <summary>
    /// What the head denotes (see <see cref="PendingSelection"/>): a name looked up lexically from <see cref="Origin"/>
    /// (the default), the first member SELECTED from <see cref="Origin"/>'s own body (an inline-block head), or the
    /// open-target walks of the level <see cref="Origin"/> is.
    /// </summary>
    internal PendingSelection Selection { get; }

    internal PendingReference At(CompletedStructureContext origin) => Origin is not null ? this
        : new(Head, Members, BoundOwners, origin, OpenPath, Selection);

    public string Head { get; }

    /// <summary>Member steps navigated structurally after the head (any visibility).</summary>
    public IReadOnlyList<string> Members { get; }

    public IReadOnlyList<Algorithm> BoundOwners { get; }

    internal string ContentKey { get; }

    /// <summary>The reference without its bound owners: origin, selection, head and member steps (see <see cref="PendingReferenceSet"/>).</summary>
    internal string ResolutionKey { get; }

    /// <summary>
    /// <see cref="ContentKey"/> with each PROCESS-WIDE id — the completed origin's requirement identity and every
    /// bound owner's <see cref="OwnerQualifiedParameter.OwnerKey"/> — written as the one character <c>#</c>, so its
    /// length is the same in every process and run. Observation only
    /// (<see cref="FrontEndTraversalObservations.SummaryKeyCharacters"/>), never cached and never an identity.
    /// </summary>
    internal string IdFreeContentKey
        => KeyParts([
            KeyParts([Origin is null ? "" : Selection == PendingSelection.Lexical ? $"completed:#:{OpenPath}" : $"completed:#:{OpenPath}:{Selection}", Head, KeyParts(Members), NoProviderKeys]),
            string.Join(",", BoundOwners.Select(static _ => "#"))]);

    internal static string KeyParts(IEnumerable<string> parts)
        => string.Concat(parts.Select(static part => $"{part.Length}:{part}"));

    public PendingReference BoundBy(Algorithm owner, bool ownerHasParameters)
        => !ownerHasParameters || BoundOwners.Any(a => ReferenceEquals(a, owner))
            ? this : new(Head, Members, [.. BoundOwners, owner], Origin, OpenPath, Selection);

    public bool Equals(PendingReference? other) => other is not null && ContentKey == other.ContentKey;

    public override bool Equals(object? obj) => Equals(obj as PendingReference);

    public override int GetHashCode() => ContentKey.GetHashCode(StringComparison.Ordinal);
}

/// <summary>
/// What a <see cref="PendingReference"/>'s head denotes. Each kind is one evaluator selection route the exposure
/// pass charges exactly (owner decision 2026-11-13: a reader is charged the access checks and value reads the
/// evaluator performs on static selections, and nothing else).
/// </summary>
internal enum PendingSelection
{
    /// <summary>A name looked up from the origin: the owner walk, then the opens of the levels it consults.</summary>
    Lexical,

    /// <summary>
    /// The head is the first member SELECTED from the origin's own body, an inline block written as a path head
    /// (<c>{ … }.Sub.Q</c>): the evaluator access-checks every member of the path and never reads the block's VALUE
    /// unless the first step selects nothing (the fallback or intrinsic reads it).
    /// </summary>
    BlockHead,

    /// <summary>
    /// The walks of every open target of the level the origin is: a lookup that reaches that level resolves all of
    /// its opens (<c>resolveAllOpens</c>) before it looks for the name, so each target's selections are checked.
    /// </summary>
    OpenWalks,
}

/// <summary>
/// Union of pending requirements, kept in a form that only GROWS as the requirements it is built
/// from grow. Repeated references with the same resolution context discharge an owner only when
/// EVERY occurrence binds it. Intersecting those bound sets implements (requirements - bound1)
/// union (requirements - bound2), without enumerating the exponentially many call paths of a
/// shared algorithm DAG.
///
/// <para>EXPOSURE-OPEN-1: the set holds ONE entry per reference
/// (<see cref="PendingReference.ResolutionKey"/>), and a reference's own content never changes: it
/// carries no provider and nothing a provider charges, so nothing in it is derived from summaries
/// that grow during a fixed point. An entry changes only by losing bound owners, a summary
/// therefore only grows with the summaries it reads, and the member fixed point terminates around
/// a cycle of mutually opening libraries.</para>
/// </summary>
internal sealed class PendingReferenceSet : IReadOnlyCollection<PendingReference>
{
    private readonly Dictionary<string, PendingReference> _references = new(StringComparer.Ordinal);

    public PendingReferenceSet() { }
    public PendingReferenceSet(IEnumerable<PendingReference> references) => UnionWith(references);
    public int Count => _references.Count;
    public void Clear() => _references.Clear();

    public void Add(PendingReference reference)
    {
        if (!_references.TryGetValue(reference.ResolutionKey, out var existing))
        {
            _references.Add(reference.ResolutionKey, reference);
            return;
        }

        var common = existing.BoundOwners.Where(owner => reference.BoundOwners.Any(other => ReferenceEquals(owner, other))).ToArray();
        if (common.Length == existing.BoundOwners.Count)
            return;
        // The narrowed entry takes the place of the one it replaces: the set's order is the order of first writes.
        _references[existing.ResolutionKey] = new(existing.Head, existing.Members, common, existing.Origin, existing.OpenPath,
            existing.Selection);
    }

    public void UnionWith(IEnumerable<PendingReference> references)
    {
        foreach (var reference in references) Add(reference);
    }
    public bool SetEquals(PendingReferenceSet other)
        => Count == other.Count && _references.All(pair => other._references.TryGetValue(pair.Key, out var value) && pair.Value.Equals(value));
    public IEnumerator<PendingReference> GetEnumerator() => _references.Values.GetEnumerator();
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
}

/// <summary>
/// Recursive summary channel result: per-property recursive ancestor-capture facts — direct
/// required ancestor-owned parameter names plus summary edges to visible names and sibling
/// properties, consumed by the exposure resolver. (Implicit-argument resolution has no sibling
/// order to consume since B3-5★: it processes a level's properties in declaration order over
/// signatures selected beforehand.)
/// </summary>
internal sealed class PropertyDependencySummaryGraph
{
    private readonly Dictionary<string, int> propertyNameToIndex;
    private readonly PropertyDependencySummaryNode[] nodes;

    public PropertyDependencySummaryGraph(
        IReadOnlyList<Property> properties,
        Dictionary<string, int> propertyNameToIndex,
        PropertyDependencySummaryNode[] nodes)
    {
        Properties = properties;
        this.propertyNameToIndex = propertyNameToIndex;
        this.nodes = nodes;
    }

    public IReadOnlyList<Property> Properties { get; }

    public int Count => nodes.Length;

    public PropertyDependencySummaryNode this[int propertyIndex] => nodes[propertyIndex];

    public bool TryGetPropertyIndex(string propertyName, out int propertyIndex)
        => propertyNameToIndex.TryGetValue(propertyName, out propertyIndex);
}

/// <summary>
/// FE-4a: the order in which a level's fixed-point equations are FIRST evaluated — every equation
/// after the equations it statically reads (the postorder of a depth-first walk over those read edges,
/// cycles broken where the walk closes them). It is an evaluation order only: any fair iteration of
/// the level's monotone equations reaches the same least fixed point, but a dependency-first order lets
/// one pass carry a chain or a cycle whole instead of advancing one step per round, however the
/// properties are declared. The walk is iterative (a long chain costs no host stack).
/// </summary>
internal static class DependencyFirstOrder
{
    /// <param name="count">The number of equations.</param>
    /// <param name="isEquation">Whether an index is an equation to order (a name's representative).</param>
    /// <param name="reads">The equation indices an equation statically reads.</param>
    public static List<int> Of(int count, Func<int, bool> isEquation, Func<int, IEnumerable<int>> reads)
    {
        var order = new List<int>(count);
        var visited = new bool[count];
        var stack = new Stack<(int Index, IEnumerator<int> Reads)>();
        for (var root = 0; root < count; root++)
        {
            if (visited[root] || !isEquation(root))
                continue;

            visited[root] = true;
            stack.Push((root, reads(root).GetEnumerator()));
            while (stack.TryPeek(out var frame))
            {
                if (frame.Reads.MoveNext())
                {
                    var next = frame.Reads.Current;
                    if (!visited[next] && isEquation(next))
                    {
                        visited[next] = true;
                        stack.Push((next, reads(next).GetEnumerator()));
                    }

                    continue;
                }

                frame.Reads.Dispose();
                stack.Pop();
                order.Add(frame.Index);
            }
        }

        return order;
    }

    /// <summary>
    /// The strongly connected components of the equations over the static read edges, dependency
    /// first (Tarjan's order: a component is emitted after every component it reads). Iterative.
    /// </summary>
    public static List<List<int>> Components(int count, Func<int, bool> isEquation, Func<int, IEnumerable<int>> reads)
    {
        var components = new List<List<int>>();
        var index = new int[count];
        var lowLink = new int[count];
        var onStack = new bool[count];
        Array.Fill(index, -1);
        var nextIndex = 0;
        var stack = new Stack<int>();
        var frames = new Stack<(int Node, IEnumerator<int> Reads)>();
        for (var root = 0; root < count; root++)
        {
            if (index[root] >= 0 || !isEquation(root))
                continue;

            Enter(root);
            while (frames.TryPeek(out var frame))
            {
                if (frame.Reads.MoveNext())
                {
                    var next = frame.Reads.Current;
                    if (!isEquation(next))
                        continue;
                    if (index[next] < 0)
                        Enter(next);
                    else if (onStack[next])
                        lowLink[frame.Node] = Math.Min(lowLink[frame.Node], index[next]);
                    continue;
                }

                frame.Reads.Dispose();
                frames.Pop();
                if (frames.TryPeek(out var caller))
                    lowLink[caller.Node] = Math.Min(lowLink[caller.Node], lowLink[frame.Node]);
                if (lowLink[frame.Node] != index[frame.Node])
                    continue;

                var component = new List<int>();
                int member;
                do
                {
                    member = stack.Pop();
                    onStack[member] = false;
                    component.Add(member);
                }
                while (member != frame.Node);
                component.Reverse();
                components.Add(component);
            }
        }

        return components;

        void Enter(int node)
        {
            index[node] = lowLink[node] = nextIndex++;
            stack.Push(node);
            onStack[node] = true;
            frames.Push((node, reads(node).GetEnumerator()));
        }
    }
}

internal static class PropertyDependencyGraphBuilder
{
    /// <summary>
    /// Mutable name-set accumulator AND value of the summary channel. Callers mutate returned
    /// seeds in place (<see cref="UnionWith"/>) while accumulating an enclosing expression's
    /// contribution, so a completed summary admitted to a memo is stored as a PRISTINE CLONE
    /// and every reach — first or later — receives its own mutable copy; returning a stored
    /// instance directly would let one reader's accumulation corrupt every later reader. For
    /// the same reason there is deliberately NO shared <c>Empty</c> singleton: every empty
    /// seed is a fresh mutable instance.
    ///
    /// <para>SHARED ARGUMENT BUNDLES (FE-2): implicit lifting gives every lifted reference to one
    /// callable in a region the SAME synthesized argument bundle, so K call edges contribute one
    /// bundle's seed — L names. A call edge therefore takes a large completed bundle seed BY
    /// REFERENCE (<see cref="AbsorbCompleted"/>) instead of copying its names, clones and unions
    /// carry such references along, and the seed folds every distinct absorbed seed in exactly
    /// once — transitively, in absorption order — the first time any of its sets is read. The
    /// content of every set is the union it always was; only when the copying happens moved.
    /// A small completed seed is still copied (at most <see cref="CopiedCompletedEntries"/>
    /// entries per edge), so written calls keep their exact eager behavior.</para>
    /// </summary>
    internal sealed class SummarySeed
    {
        /// <summary>
        /// The largest completed seed an edge copies rather than references: copying it costs a
        /// constant per edge, and it keeps small written argument bundles out of the absorbed
        /// lists (a long operator chain of distinct small calls would otherwise carry one
        /// reference per call at every node of the chain).
        /// </summary>
        internal const int CopiedCompletedEntries = 8;

        // The four sets are created on first WRITE (SEC-S1): most seeds — a literal's, a resolved
        // name's, every completed seed's pristine clone — stay empty, and four eagerly allocated
        // empty collections per seed were the exposure pass's largest live cost on dense source.
        // Null means empty: every internal read treats it so, and each public accessor
        // materializes the real, mutable set callers may change in place, once.
        private HashSet<string>? _requiredAncestorOwnedParameterNames;
        private HashSet<string>? _visiblePropertyDependencyNames;
        private PendingReferenceSet? _pendingReferences;
        private HashSet<OwnerQualifiedParameter>? _ownerQualifiedParameters;

        // Completed seeds absorbed by reference, in absorption order, deduplicated by reference;
        // null once folded (or when nothing was absorbed). An absorbed seed is never mutated.
        private List<SummarySeed>? _absorbed;
        private HashSet<SummarySeed>? _absorbedSet;

        public SummarySeed(
            IEnumerable<string>? requiredAncestorOwnedParameterNames = null,
            IEnumerable<string>? visiblePropertyDependencyNames = null,
            IEnumerable<PendingReference>? pendingReferences = null,
            IEnumerable<OwnerQualifiedParameter>? ownerQualifiedParameters = null)
        {
            _requiredAncestorOwnedParameterNames = IsKnownEmpty(requiredAncestorOwnedParameterNames) ? null : NonEmptyOrNull(CreateNameSet(requiredAncestorOwnedParameterNames));
            _visiblePropertyDependencyNames = IsKnownEmpty(visiblePropertyDependencyNames) ? null : NonEmptyOrNull(CreateNameSet(visiblePropertyDependencyNames));
            _pendingReferences = IsKnownEmpty(pendingReferences) ? null : new PendingReferenceSet(pendingReferences!) is { Count: > 0 } references ? references : null;
            _ownerQualifiedParameters = IsKnownEmpty(ownerQualifiedParameters) ? null : NonEmptyOrNull(new HashSet<OwnerQualifiedParameter>(ownerQualifiedParameters!));
        }

        private static bool IsKnownEmpty<T>(IEnumerable<T>? items)
            => items is null || (items is IReadOnlyCollection<T> collection && collection.Count == 0);

        private static HashSet<T>? NonEmptyOrNull<T>(HashSet<T> set) => set.Count == 0 ? null : set;

        public HashSet<string> RequiredAncestorOwnedParameterNames
        {
            get { Fold(); return _requiredAncestorOwnedParameterNames ??= CreateNameSet(); }
        }

        public HashSet<OwnerQualifiedParameter> OwnerQualifiedParameters
        {
            get { Fold(); return _ownerQualifiedParameters ??= []; }
        }

        /// <summary>
        /// Bare names of a RAW walk that no level expansion has met yet. An expansion resolves a name its level declares
        /// and anchors every other one as a pending reference at the level's context, so an expanded seed carries none.
        /// </summary>
        public HashSet<string> VisiblePropertyDependencyNames
        {
            get { Fold(); return _visiblePropertyDependencyNames ??= CreateNameSet(); }
        }

        /// <summary>Member paths and open-shadowed names (see <see cref="PendingReference"/>).</summary>
        public PendingReferenceSet PendingReferences
        {
            get { Fold(); return _pendingReferences ??= new(); }
        }

        // Entries a copy of this seed would transfer, without folding it.
        private int EntryCount
            => (_requiredAncestorOwnedParameterNames?.Count ?? 0) + (_visiblePropertyDependencyNames?.Count ?? 0)
                + (_pendingReferences?.Count ?? 0) + (_ownerQualifiedParameters?.Count ?? 0) + (_absorbed?.Count ?? 0);

        public SummarySeed Clone()
        {
            var clone = new SummarySeed(
                _requiredAncestorOwnedParameterNames, _visiblePropertyDependencyNames, _pendingReferences, _ownerQualifiedParameters);
            clone.AbsorbAll(_absorbed);
            return clone;
        }

        public void UnionWith(SummarySeed other)
        {
            FrontEndStack.Ensure();
            UnionOwnSets(other);
            AbsorbAll(other._absorbed);
        }

        // Adds another seed's OWN sets (not its absorbed parts) to this seed's, creating a set
        // only when the other one contributes an entry.
        private void UnionOwnSets(SummarySeed other)
        {
            if (other._requiredAncestorOwnedParameterNames is { Count: > 0 } required)
                (_requiredAncestorOwnedParameterNames ??= CreateNameSet()).UnionWith(required);
            if (other._visiblePropertyDependencyNames is { Count: > 0 } visible)
                (_visiblePropertyDependencyNames ??= CreateNameSet()).UnionWith(visible);
            if (other._pendingReferences is { Count: > 0 } pending)
                (_pendingReferences ??= new()).UnionWith(pending);
            if (other._ownerQualifiedParameters is { Count: > 0 } qualified)
                (_ownerQualifiedParameters ??= []).UnionWith(qualified);
        }

        /// <summary><see cref="UnionWith"/> returning this seed, for expression-shaped folds.</summary>
        public SummarySeed Absorb(SummarySeed other)
        {
            UnionWith(other);
            return this;
        }

        /// <summary>
        /// Adds a COMPLETED seed — one a memo stores and nothing mutates afterwards: a large one
        /// by reference (a shared argument bundle's seed, FE-2), a small one by copying.
        /// </summary>
        public SummarySeed AbsorbCompleted(SummarySeed completed)
        {
            if (completed.EntryCount <= CopiedCompletedEntries)
                UnionWith(completed);
            else
                AbsorbReference(completed);
            return this;
        }

        private void AbsorbAll(List<SummarySeed>? parts)
        {
            if (parts is null)
                return;
            foreach (var part in parts)
                AbsorbReference(part);
        }

        // A short absorbed list deduplicates by scanning it; the reference set exists only once
        // the list outgrows this (SEC-S1: K seeds each absorbing ONE shared bundle seed kept K
        // one-element hash sets alive). Membership is the same reference-identity test either way.
        private const int AbsorbedScanLimit = 8;

        private void AbsorbReference(SummarySeed part)
        {
            if (_absorbedSet is { } set)
            {
                if (set.Add(part))
                    _absorbed!.Add(part);
                return;
            }

            var absorbed = _absorbed ??= [];
            if (AbsorbedListContains(absorbed, part))
                return;
            absorbed.Add(part);
            if (absorbed.Count > AbsorbedScanLimit)
                _absorbedSet = new(absorbed, ReferenceEqualityComparer.Instance);
        }

        private bool HasAbsorbed(SummarySeed part)
            => _absorbedSet?.Contains(part) ?? (_absorbed is { } absorbed && AbsorbedListContains(absorbed, part));

        private static bool AbsorbedListContains(List<SummarySeed> absorbed, SummarySeed part)
        {
            foreach (var existing in absorbed)
            {
                if (ReferenceEquals(existing, part))
                    return true;
            }

            return false;
        }

        /// <summary>
        /// FE-3: removes, WITHOUT folding it, every absorbed completed part whose whole content is
        /// required ancestor-owned names that <paramref name="owned"/> covers. Called only where
        /// the caller next qualifies and strips exactly the owned names at the owning level (an
        /// algorithm summary's output seed), where such a part contributes nothing to the result —
        /// so the result is the one folding would produce, while K owners that each absorbed one
        /// shared L-name argument-bundle seed no longer each copy, qualify, and strip its L names.
        /// The verdict per (part, owned set) is memoized on <paramref name="memo"/>.
        /// </summary>
        internal void DropOwnedAbsorbedParts(IReadOnlySet<string> owned, SummaryMemo memo)
        {
            if (_absorbed is not { } absorbed || owned.Count == 0)
                return;

            List<SummarySeed>? kept = null;
            for (var i = 0; i < absorbed.Count; i++)
            {
                var part = absorbed[i];
                if (memo.IsOwnedPureRequirement(part, owned))
                {
                    kept ??= absorbed.GetRange(0, i);
                    continue;
                }

                kept?.Add(part);
            }

            if (kept is null)
                return;
            _absorbed = kept.Count == 0 ? null : kept;
            _absorbedSet = kept.Count > AbsorbedScanLimit ? new HashSet<SummarySeed>(kept, ReferenceEqualityComparer.Instance) : null;
        }

        /// <summary>
        /// Whether this COMPLETED seed and every part it absorbed carry only required names, all in
        /// <paramref name="owned"/>. Reads the stored sets directly: a completed seed is never folded
        /// or mutated.
        /// </summary>
        internal bool IsPureRequirementWithin(IReadOnlySet<string> owned, FrontEndTraversalObservations? observations = null)
            => RequiredNamesOutside(owned, observations: observations) is { Length: 0 };

        /// <summary>
        /// When this COMPLETED seed and every part it absorbed carry only required names: those names
        /// that <paramref name="covered"/> does not contain (distinct, in walk order); otherwise null.
        /// Reads the stored sets directly: a completed seed is never folded or mutated.
        /// </summary>
        internal string[]? RequiredNamesOutside(IReadOnlySet<string> covered,
            Func<SummarySeed, IReadOnlySet<string>, string[]?>? residualOf = null,
            FrontEndTraversalObservations? observations = null)
        {
            List<string>? outside = null;
            HashSet<string>? seenOutside = null;
            var visited = new HashSet<SummarySeed>(ReferenceEqualityComparer.Instance);
            var pending = new Stack<SummarySeed>();
            pending.Push(this);
            while (pending.TryPop(out var part))
            {
                if (!visited.Add(part))
                    continue;
                if (part._visiblePropertyDependencyNames is { Count: > 0 }
                    || part._pendingReferences is { Count: > 0 }
                    || part._ownerQualifiedParameters is { Count: > 0 })
                {
                    return null;
                }

                foreach (var name in part._requiredAncestorOwnedParameterNames ?? [])
                {
                    observations?.RecordSummaryResidualNameProbe();
                    if (!covered.Contains(name) && (seenOutside ??= new(StringComparer.Ordinal)).Add(name))
                        (outside ??= []).Add(name);
                }

                if (part._absorbed is { } nested)
                {
                    foreach (var absorbedPart in nested)
                    {
                        if (residualOf is null)
                            pending.Push(absorbedPart);
                        else
                        {
                            var residual = residualOf(absorbedPart, covered);
                            if (residual is null)
                                return null;
                            foreach (var name in residual)
                                if ((seenOutside ??= new(StringComparer.Ordinal)).Add(name))
                                    (outside ??= []).Add(name);
                        }
                    }
                }
            }

            return outside is null ? [] : [.. outside];
        }

        // Folds every distinct absorbed seed into this seed's own sets — each once, depth-first in
        // absorption order, so the resulting content and insertion order are deterministic.
        private void Fold()
        {
            if (_absorbed is not { } absorbed)
                return;

            _absorbed = null;
            _absorbedSet = null;
            var folded = new HashSet<SummarySeed>(ReferenceEqualityComparer.Instance);
            var pending = new Stack<SummarySeed>();
            for (var i = absorbed.Count - 1; i >= 0; i--)
                pending.Push(absorbed[i]);
            while (pending.TryPop(out var part))
            {
                if (!folded.Add(part))
                    continue;

                UnionOwnSets(part);
                if (part._absorbed is { } nested)
                {
                    for (var i = nested.Count - 1; i >= 0; i--)
                        pending.Push(nested[i]);
                }
            }
        }

        /// <summary>
        /// Moves every requirement <paramref name="owner"/> binds into an owner-qualified one.
        /// Only the intersection with the owner's parameter names matters, so the SMALLER side
        /// is scanned (FE-1): a narrow seed under a wide owner costs its own size, never the
        /// owner's width, and <paramref name="ownerParameterNames"/> is the owner's set built
        /// once per resolution (<see cref="SummaryMemo.ParameterNamesOf"/>), never a live
        /// projection per property. Pending references carry no requirement of their own and
        /// are left as they are.
        /// </summary>
        public void QualifyParameters(
            Algorithm owner,
            IReadOnlySet<string> ownerParameterNames,
            FrontEndTraversalObservations? observations)
        {
            // Reads the folded sets directly, so a seed with nothing to qualify materializes none.
            Fold();
            if (_requiredAncestorOwnedParameterNames is not { Count: > 0 } required)
                return;

            foreach (var name in SharedNames(required, ownerParameterNames, observations))
            {
                required.Remove(name);
                (_ownerQualifiedParameters ??= []).Add(new(name, owner));
            }
        }

        /// <summary>
        /// Strips the names a level itself binds from every requirement the seed carries, and
        /// records that level as a bound owner of every pending reference riding along (what a
        /// reference requires of this owner is supplied here). <paramref name="ownerHasParameters"/>
        /// is whether <paramref name="owner"/> declares any parameter, decided once by the
        /// caller. Every intersection scans its smaller side (FE-1).
        /// </summary>
        public void RemoveRequiredAncestorOwnedParameterNames(
            IReadOnlySet<string> names,
            Algorithm owner,
            bool ownerHasParameters,
            FrontEndTraversalObservations? observations)
        {
            // Reads the folded sets directly, so a seed with nothing to strip materializes none.
            Fold();
            if (_requiredAncestorOwnedParameterNames is { Count: > 0 } required)
            {
                foreach (var name in SharedNames(required, names, observations))
                    required.Remove(name);
            }

            _ownerQualifiedParameters?.RemoveWhere(r => ReferenceEquals(r.Owner, owner) && names.Contains(r.Name));
            if (!ownerHasParameters || _pendingReferences is not { Count: > 0 } pendingReferences)
                return;

            var bound = new List<PendingReference>(pendingReferences.Count);
            foreach (var pending in pendingReferences)
                bound.Add(pending.BoundBy(owner, ownerHasParameters: true));
            pendingReferences.Clear();
            pendingReferences.UnionWith(bound);
        }

        // The names in both sets, found by scanning the SMALLER one (each examined name is one
        // qualification probe): the one intersection every requirement strip and qualification uses.
        private static List<string> SharedNames(
            HashSet<string> requirements,
            IReadOnlySet<string> names,
            FrontEndTraversalObservations? observations)
        {
            var shared = new List<string>();
            if (requirements.Count == 0 || names.Count == 0)
                return shared;

            if (requirements.Count <= names.Count)
            {
                foreach (var name in requirements)
                {
                    observations?.RecordSummaryQualificationProbe();
                    if (names.Contains(name))
                        shared.Add(name);
                }
            }
            else
            {
                foreach (var name in names)
                {
                    observations?.RecordSummaryQualificationProbe();
                    if (requirements.Contains(name))
                        shared.Add(name);
                }
            }

            return shared;
        }

        public bool SetEquals(SummarySeed other)
            => RequiredAncestorOwnedParameterNames.SetEquals(other.RequiredAncestorOwnedParameterNames)
                && VisiblePropertyDependencyNames.SetEquals(other.VisiblePropertyDependencyNames)
                && PendingReferences.SetEquals(other.PendingReferences)
                && OwnerQualifiedParameters.SetEquals(other.OwnerQualifiedParameters);

        /// <summary>
        /// FE-4a: whether the seed's content is empty, decided WITHOUT folding: its own sets and every
        /// seed it holds by reference (transitively) are empty. Reads only; a seed held by reference is
        /// never mutated, and the parts form no cycle (a seed only ever holds seeds built before it).
        /// </summary>
        internal bool IsEmptyWithoutFolding()
        {
            if (!OwnSetsEmpty(this))
                return false;
            if (_absorbed is null)
                return true;

            var visited = new HashSet<SummarySeed>(ReferenceEqualityComparer.Instance) { this };
            var pending = new Stack<SummarySeed>(_absorbed);
            while (pending.TryPop(out var part))
            {
                if (!visited.Add(part))
                    continue;
                if (!OwnSetsEmpty(part))
                    return false;
                if (part._absorbed is { } nested)
                {
                    foreach (var nestedPart in nested)
                        pending.Push(nestedPart);
                }
            }

            return true;

            static bool OwnSetsEmpty(SummarySeed seed)
                => (seed._requiredAncestorOwnedParameterNames?.Count ?? 0) == 0
                    && (seed._visiblePropertyDependencyNames?.Count ?? 0) == 0
                    && (seed._pendingReferences?.Count ?? 0) == 0
                    && (seed._ownerQualifiedParameters?.Count ?? 0) == 0;
        }

        /// <summary>
        /// FE-4a: a SUFFICIENT test of equal content that never folds: equal own sets and the same
        /// seeds held by reference. False means "not decided here" (compare <see cref="SetEquals"/>).
        /// </summary>
        internal bool StructurallyEquals(SummarySeed other)
        {
            // The absorbed lists are deduplicated by reference, so equal counts plus containment
            // is set equality.
            if ((_absorbed?.Count ?? 0) != (other._absorbed?.Count ?? 0))
                return false;
            if (_absorbed is { } parts)
            {
                foreach (var part in parts)
                {
                    if (!other.HasAbsorbed(part))
                        return false;
                }
            }

            return SameNames(_requiredAncestorOwnedParameterNames, other._requiredAncestorOwnedParameterNames)
                && SameNames(_visiblePropertyDependencyNames, other._visiblePropertyDependencyNames)
                && ((_pendingReferences?.Count ?? 0) == 0
                    ? (other._pendingReferences?.Count ?? 0) == 0
                    : other._pendingReferences is { } otherPending && _pendingReferences!.SetEquals(otherPending))
                && SameNames(_ownerQualifiedParameters, other._ownerQualifiedParameters);

            // Set equality with a missing set read as the empty set.
            static bool SameNames<T>(HashSet<T>? left, HashSet<T>? right)
                => (left?.Count ?? 0) == 0
                    ? (right?.Count ?? 0) == 0
                    : right is not null && left!.SetEquals(right);
        }

        public bool IsEmpty
        {
            get
            {
                Fold();
                return (_requiredAncestorOwnedParameterNames?.Count ?? 0) == 0
                    && (_visiblePropertyDependencyNames?.Count ?? 0) == 0
                    && (_pendingReferences?.Count ?? 0) == 0
                    && (_ownerQualifiedParameters?.Count ?? 0) == 0;
            }
        }

        /// <summary>Content identity (sorted), for seed equality within a fixed point.</summary>
        internal string ContentKey => ContentKeyFor(observations: null);

        internal string ContentKeyFor(FrontEndTraversalObservations? observations)
        {
            // Reads the folded sets directly: most seeds are empty, and a key must not materialize what it describes.
            var key = IsEmpty ? EmptyContentKey : PendingReference.KeyParts([
                _requiredAncestorOwnedParameterNames is { } required ? FrontEndRegionKeys.NameSet(required) : string.Empty,
                _visiblePropertyDependencyNames is { } visible ? FrontEndRegionKeys.NameSet(visible) : string.Empty,
                _pendingReferences is { } pending ? FrontEndRegionKeys.NameSet(pending.Select(static reference => reference.ContentKey)) : string.Empty,
                _ownerQualifiedParameters is { } qualified ? FrontEndRegionKeys.NameSet(qualified.Select(static r => r.ContentKey)) : string.Empty]);
            observations?.RecordSummaryKeyCharacters((IsEmpty ? key : IdFreeContentKey()).Length);
            return key;
        }

        /// <summary>
        /// <see cref="ContentKeyFor"/>'s key with every process-wide id written as <c>#</c>
        /// (<see cref="PendingReference.IdFreeContentKey"/>, <see cref="OwnerQualifiedParameter.IdFreeContentKey"/>):
        /// the text <see cref="FrontEndTraversalObservations.SummaryKeyCharacters"/> counts. Built only for an observer.
        /// </summary>
        private string IdFreeContentKey()
            => PendingReference.KeyParts([
                _requiredAncestorOwnedParameterNames is { } required ? FrontEndRegionKeys.NameSet(required) : string.Empty,
                _visiblePropertyDependencyNames is { } visible ? FrontEndRegionKeys.NameSet(visible) : string.Empty,
                _pendingReferences is { } pending ? FrontEndRegionKeys.NameSet(pending.Select(static reference => reference.IdFreeContentKey)) : string.Empty,
                _ownerQualifiedParameters is { } qualified ? FrontEndRegionKeys.NameSet(qualified.Select(static r => r.IdFreeContentKey)) : string.Empty]);

        private static readonly string EmptyContentKey = PendingReference.KeyParts([string.Empty, string.Empty, string.Empty, string.Empty]);
    }

    /// <summary>
    /// The completed summary of one algorithm node under the empty locally-owned context: the
    /// requirements of its OUTPUT (what evaluating the algorithm's value needs) and, per
    /// declared property, that member's requirements expanded through the algorithm's own
    /// sibling fixed point (relative to the algorithm's declaring level). The member seeds are
    /// what structural navigation (<c>Inner.X</c>) and <c>open</c>-provided names charge.
    /// Both are stored pristine; readers clone before accumulating.
    /// </summary>
    internal sealed class AlgorithmSummary(
        SummarySeed outputSeed,
        IReadOnlyDictionary<string, SummarySeed> memberSeeds)
    {
        public SummarySeed OutputSeed { get; } = outputSeed;

        public IReadOnlyDictionary<string, SummarySeed> MemberSeeds { get; } = memberSeeds;

        public static readonly IReadOnlyDictionary<string, SummarySeed> NoMembers =
            new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
    }

    /// <summary>
    /// Completed-summary memo for the summary channel. EVERY summary is computed in a completed
    /// structural context (<see cref="SummaryWalkMemos.CompletedContext"/>): there is ONE summary
    /// mode, and an entry is the finished summary of one occurrence, keyed by its facts and scope key
    /// (<see cref="ContextualAlgorithmSummaries"/>; reference identity, like every other front-end
    /// memo: two structurally equal but distinct nodes summarize independently, while host-DAG
    /// sharing is by reference). A summary whose computation used no context is kept by ALGORITHM
    /// node REFERENCE instead and serves every occurrence of that node
    /// (<see cref="IndependentAlgorithmSummaries"/>): the summary walk never queries what ancestors
    /// own — a free parameter reference is reported as a required ancestor-owned name regardless of
    /// the ancestor context — so such a summary carries no caller state. Conditional BRANCH bodies
    /// summarize under their per-branch binder names (a genuinely context-sensitive input) and have
    /// their own tables. Entries are admitted only AFTER a summary is fully computed (local fixed
    /// point converged, self-owned parameters stripped); the structural preflight guarantees
    /// acyclic inputs, so a node can never be reached again while its own summary is still
    /// in flight. Lifetime is the caller's: <see cref="PropertyExposureResolver"/> creates
    /// ONE memo per resolution (never static, never cross-run) so each context-independent
    /// summary is computed once per resolution instead of once per ancestor level, and a
    /// standalone <see cref="BuildSummaries"/> call creates its own. Stored seeds follow the
    /// clone discipline documented on <see cref="SummarySeed"/>.
    /// </summary>
    internal sealed class SummaryMemo(FrontEndTraversalObservations? observations = null)
    {
        internal long ExpansionCycleCuts;

        /// <summary>
        /// The source-processing token of the exposure resolution this memo spans (none for a standalone
        /// <see cref="BuildSummaries"/> call), observed once per frame of the level-expansion driver.
        /// </summary>
        internal CancellationToken CancellationToken { get; init; }

        internal void ObserveCancellation()
            => FrontEndTraversalObservations.ObserveCancellation(
                observations, FrontEndCancellationCheckpoint.SummaryChannel, CancellationToken);

        /// <summary>The bodies of the exposure input reached through several paths; null outside exposure, or when none is.</summary>
        internal SharedBodyCensus? SharedBodies;
        private RegionFreeNames? _regionNames;
        private Dictionary<CompletedBodyRegion, CompletedStructureContext>? _sharedRegions;

        /// <summary>
        /// The context whose summary stands for <paramref name="context"/>: the first one of the same shared body whose free
        /// names select the same declarations (<see cref="CompletedBodyRegion"/>). A summary's anchored origins lie in that
        /// representative, whose chain answers every escaping name exactly as this context's does, and every context below
        /// a representative is summarized once. Only the summary memo uses it: actual keys and publications stay distinct.
        /// </summary>
        internal CompletedStructureContext SharedRegionContext(CompletedStructureContext context, Algorithm body)
        {
            if (SharedBodies?.Holds(body) != true || body.IsModuleRoot) return context;
            _regionNames ??= new(new NameSetInterner());
            if (CompletedBodyRegion.Of(context.Facts, context.Key, body, _regionNames) is not { } region) return context;
            _sharedRegions ??= new();
            return _sharedRegions.TryAdd(region, context) ? context : _sharedRegions[region];
        }

        internal readonly BranchContextInterner BranchContexts = new();
        // Completed requirements carry an exact origin until exposure settlement. Their summaries
        // are occurrence-contextual: one entry per completed context.
        internal Dictionary<(StaticLookupFacts Facts, StaticScopeKey Key), AlgorithmSummary>? ContextualAlgorithmSummaries;

        // Q8 work sharing. A summary whose computation neither observed nor captured a contextual
        // selection is a function of the immutable body, not of the path by which it was reached,
        // so it is kept by body reference and serves every occurrence of that body.
        // ContextUses is a transitive effect: anchoring an escaping reference, observing a
        // selection, or reading a context-dependent cached result prevents independent reuse.
        // Such a summary is still computed in its occurrence's context: no walk runs without one.
        internal Dictionary<Algorithm, AlgorithmSummary>? IndependentAlgorithmSummaries;
        internal Dictionary<BranchBodySummaryKey, SummarySeed>? IndependentBranchSummaries;

        /// <summary>
        /// Completed call and dot-call argument-bundle seeds whose transparent walk used no context, by
        /// bundle reference (FE-2), kept for the memo lifetime: K owners sharing one synthesized argument
        /// bundle summarize it once, never once per owner region (FE-3). A bundle whose walk used a context
        /// stays in its region (<see cref="SummaryWalkMemos.ArgumentBundleSeeds"/>).
        /// </summary>
        internal Dictionary<OutputBundle, SummarySeed>? IndependentArgumentBundles;
        internal long ContextUses;
        internal void UseContext() => ContextUses++;

        internal bool BranchParametersAgree(Algorithm body, IReadOnlySet<string> binders,
            CompletedStructureContext context)
        {
            var parameters = context.Facts.Facts(context.Key)?.Parameters;
            if (parameters is null) return false;
            var own = ParameterNamesOf(body, observations);
            return parameters.Count == own.Count + binders.Count - binders.Count(own.Contains)
                && own.All(parameters.Contains) && binders.All(parameters.Contains);
        }

        private readonly Dictionary<object, bool> _bindingFree = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<(StaticLookupFacts Facts, StaticScopeKey Parent, Algorithm Body),
            List<CompletedStructureContext>> _bindingFreeRegions = new();

        // A binder-free branch introduces no binding identity to rename. The same immutable
        // binding-free subtree under the exact same parent is therefore the same Q8 equation
        // environment, even when literal patterns give it distinct structural graph keys.
        // This is only a summary representative: the actual keys/publications and runtime
        // branch scopes remain distinct. Unknown stays Unknown; availability must agree.
        internal CompletedStructureContext SummaryRegion(CompletedStructureContext context, Algorithm body)
        {
            context = RequirementContext(context, body);
            if (context is not { Key.BindingRegion: not null, Key.Parent: { } parent } at
                || at.Facts.Facts(at.Key) is not { Body: { } view, Parameters.Count: 0 } facts
                || !ReferenceEquals(view, body) || !BindingFree(body)) return context;
            var key = (at.Facts, parent, body);
            if (!_bindingFreeRegions.TryGetValue(key, out var regions))
                _bindingFreeRegions.Add(key, regions = []);
            foreach (var previous in regions)
            {
                var before = previous.Facts.Facts(previous.Key)!;
                if (ReferenceEquals(before.Body, body) && before.Parameters.Count == 0
                    && before.IsProvisional == facts.IsProvisional
                    && SameSelection(before.Receiver, previous.Key, facts.Receiver, at.Key)
                    && SameSelection(before.Open, previous.Key, facts.Open, at.Key)
                    && before.Providers.SequenceEqual(facts.Providers)
                    && SameNames(before.UnavailableOpenNames, facts.UnavailableOpenNames)
                    && SameNames(before.AmbiguousOpenNames, facts.AmbiguousOpenNames)) return previous;
            }
            regions.Add(at);
            return at;
        }

        private static bool SameNames(IReadOnlySet<string>? left, IReadOnlySet<string>? right)
            => ReferenceEquals(left, right) || left is not null && right is not null && left.SetEquals(right);

        private static bool SameSelection(CompletedStaticStructures.Selection left, StaticScopeKey leftScope,
            CompletedStaticStructures.Selection right, StaticScopeKey rightScope)
            => left.Kind == right.Kind && Equals(left.Identity, right.Identity)
                && (ReferenceEquals(left.Target, right.Target)
                    || ReferenceEquals(left.Target, leftScope) && ReferenceEquals(right.Target, rightScope));

        private bool BindingFree(Algorithm body)
        {
            if (_bindingFree.TryGetValue(body, out var known)) return known;
            var pending = new Stack<object>();
            var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
            pending.Push(body);
            while (pending.TryPop(out var node))
            {
                if (!seen.Add(node)) continue;
                if (_bindingFree.TryGetValue(node, out known))
                {
                    if (known) continue;
                    return _bindingFree[body] = false;
                }
                if (node is Algorithm.User { ParameterPatterns.Count: > 0 }
                    || node is Algorithm.Conditional family && family.Branches.Any(branch => branch.Pattern.BoundNames().Any()))
                    return _bindingFree[body] = false;
                for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++) pending.Push(child);
            }
            foreach (var node in seen) _bindingFree[node] = true;
            return true;
        }

        private readonly Dictionary<StaticLookupFacts, ElaboratedPropertyScope> _lookupRoots = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<(StaticLookupFacts Facts, StaticScopeKey Key), Algorithm> _requirementViews = new();
        private readonly Dictionary<(StaticLookupFacts Facts, StaticScopeKey Key), ElaboratedPropertyScope> _requirementLevels = new();
        private readonly Dictionary<StaticLookupFacts, RequirementLookupFacts> _requirementFacts = new(ReferenceEqualityComparer.Instance);

        [return: System.Diagnostics.CodeAnalysis.NotNullIfNotNull(nameof(context))]
        internal CompletedStructureContext? RequirementContext(CompletedStructureContext? context, Algorithm? body = null)
        {
            if (context is not { } at) return null;
            var source = at.Facts is RequirementLookupFacts existing ? existing.Source : at.Facts;
            if (source is not CompletedStaticStructures { HasProvisional: true }) return at;
            if (!_requirementFacts.TryGetValue(source, out var projection))
                _requirementFacts.Add(source, projection = new(source, _requirementViews));
            if (body is not null && source.Facts(at.Key)?.IsProvisional == true)
            {
                if (!ReferenceEquals(OpenProviderIdentity.DeclarationOf(body), at.Key.Declaration))
                    throw new InvalidOperationException("A provisional requirement frame must preserve its admitted declaration.");
                if (_requirementViews.TryAdd((source, at.Key), body)) projection.Revision++;
            }
            return projection.Context(at.Key);
        }

        // A Q8-only view of genuine Q1-Q7 answers plus the provisional tree the summary walk
        // received. It creates no answer, changes no completion eligibility and never escapes
        // the summary memo into a program, continuation or runtime activation.
        private sealed class RequirementLookupFacts(StaticLookupFacts source,
            Dictionary<(StaticLookupFacts Facts, StaticScopeKey Key), Algorithm> views) : StaticLookupFacts
        {
            internal StaticLookupFacts Source => source;
            internal int Revision;
            private int _cachedVersion = -1;
            private readonly Dictionary<StaticScopeKey, CompletedStaticStructures.BodyFacts> _projected = new(ReferenceEqualityComparer.Instance);
            internal override StaticScopeKey PreludeKey => source.PreludeKey;
            internal override IEnumerable<StaticScopeKey> Scopes => source.Scopes;
            internal override int ViewVersion => unchecked(source.ViewVersion + Revision);
            internal override void EnsureUsable() => source.EnsureUsable();
            internal override StaticScopeKey? Child(StaticScopeKey parent, Algorithm body, Pattern? pattern = null) => source.Child(parent, body, pattern);
            internal override CompletedStaticStructures.BodyFacts? Facts(StaticScopeKey key)
            {
                if (_cachedVersion != source.ViewVersion) { _projected.Clear(); _cachedVersion = source.ViewVersion; }
                if (_projected.TryGetValue(key, out var known)) return known;
                var facts = source.Facts(key);
                if (facts is not { IsProvisional: true } || !views.TryGetValue((source, key), out var body)) return facts;
                return _projected[key] = facts with { Body = body,
                    Receiver = facts.RequirementReceiver ?? CompletedStaticStructures.Selection.Unavailable,
                    Open = facts.RequirementOpen ?? CompletedStaticStructures.Selection.Unavailable };
            }
        }

        private ElaboratedPropertyScope LookupScope(CompletedStructureContext origin)
            => RequirementLevel(origin);

        internal ElaboratedPropertyScope RequirementLevel(CompletedStructureContext origin)
        {
            origin = RequirementContext(origin)!;
            if (!_lookupRoots.TryGetValue(origin.Facts, out var root))
            {
                root = ElaboratedScopeLookup.CreateScope(origin.Facts.Prelude,
                    completedContext: origin.Facts.Context(origin.Facts.PreludeKey),
                    memberIndexes: new OpenMemberIndexCache(observations), observations: observations);
                _lookupRoots.Add(origin.Facts, root);
                _requirementLevels.Add((origin.Facts, origin.Facts.PreludeKey), root);
            }
            var pending = new Stack<StaticScopeKey>();
            var key = origin.Key;
            while (!_requirementLevels.ContainsKey((origin.Facts, key)))
            {
                pending.Push(key);
                key = key.Parent ?? throw new InvalidOperationException("A requirement frame must reach its admitted prelude.");
            }
            var level = _requirementLevels[(origin.Facts, key)];
            while (pending.TryPop(out key))
            {
                var facts = origin.Facts.Facts(key);
                var body = facts?.Body
                    ?? throw new InvalidOperationException("An unavailable requirement frame has no admitted provisional view.");
                level = ElaboratedScopeLookup.CreateScope(body, level, observations: observations,
                    memberIndexes: root.MemberIndexes, completedContext: origin.Facts.Context(key));
                _requirementLevels.Add((origin.Facts, key), level);
            }
            return level;
        }

        /// <summary>
        /// The references that settle <paramref name="reference"/>: the reference rebound to the declaration Q1 selects
        /// for its head and, when that head is a bare name an open provides, the open-target walks of every level the
        /// lookup consulted, up to and including the deciding one (<see cref="PendingSelection.OpenWalks"/>). The
        /// evaluator resolves all of a consulted level's opens before it looks for the name, so their selections are
        /// checked whether or not they provide it; rebinding to the provider alone would drop them.
        /// </summary>
        internal IEnumerable<PendingReference> SelectedReferences(PendingReference reference)
        {
            if (reference.Origin is not null) UseContext();
            if (reference is not { Origin: { } origin, OpenPath: false, Selection: PendingSelection.Lexical }
                || origin.Facts.Facts(origin.Key)?.Body is null) return [reference];
            var scope = LookupScope(origin);
            var owned = ElaboratedScopeLookup.SelectOwnedDeclaration(scope, reference.Head, ElaboratedScopeLookup.OwnParameterBindings.Instance);
            CompletedStructureContext? selected = null;
            ElaboratedPropertyScope? deciding = null;
            if (owned.TryGetProperty(out var declaring, out _)) selected = declaring.CompletedContext;
            else if (owned.Kind == OwnedDeclarationKind.None && reference.Members.Count == 0)
            {
                // Navigating an opened head checks that member's accessibility before its
                // children. Keep its opening origin so settlement charges the head as well
                // as the remaining path. A lexical head at the provider would skip it.
                // A partial provider list cannot select an identity. Name presence alone never
                // licenses this bridge, even when one currently published provider offers it.
                for (var at = scope; at is not null; at = at.Parent)
                    if (at.CompletedContext is not { } context || context.Facts.Facts(context.Key) is not { Body: not null } facts
                        || facts.Providers.Any(provider => provider.Kind == StaticFactKind.Unknown)) return [reference];
                selected = ElaboratedScopeLookup.LookupSingleOpenMember(scope, reference.Head)?.MemberLevel.CompletedContext;
                if (selected is not null) deciding = ElaboratedScopeLookup.SelectFirstOpenLevel(scope, reference.Head).Level;
            }
            if (selected is null || ReferenceEquals(selected.Key, origin.Key)) return [reference];
            PendingReference rebound = new(reference.Head, reference.Members, reference.BoundOwners, selected);
            if (deciding is null) return [rebound];
            var references = new List<PendingReference> { rebound };
            for (var at = scope; at is not null; at = at.Parent)
            {
                if (OpenWalksMayCharge(at))
                    references.Add(OpenWalksOf(at.CompletedContext!, reference.BoundOwners));
                if (ReferenceEquals(at, deciding)) break;
            }
            return references;
        }

        /// <summary>The open-target walks of the level <paramref name="opening"/> is (<see cref="PendingSelection.OpenWalks"/>).</summary>
        internal static PendingReference OpenWalksOf(CompletedStructureContext opening, IReadOnlyList<Algorithm>? boundOwners = null)
            => new(string.Empty, [], boundOwners, opening, openPath: true, PendingSelection.OpenWalks);

        // Project a completed Q1 owner selection onto THIS live Q8 equation map. Context-bearing
        // paths, open choices and bound-owner exclusions keep their full symbolic representation.
        internal bool SelectsLocalMember(PendingReference reference, CompletedStructureContext level)
        {
            if (reference.Origin is not null) UseContext();
            if (reference is not { Origin: { } origin, OpenPath: false, Selection: PendingSelection.Lexical, Members.Count: 0, BoundOwners.Count: 0 }
                || !ReferenceEquals(origin.Facts, level.Facts) || origin.Facts.Facts(origin.Key)?.Body is null)
                return false;
            var scope = LookupScope(origin);
            var selected = ElaboratedScopeLookup.SelectOwnedDeclaration(scope, reference.Head, ElaboratedScopeLookup.OwnParameterBindings.Instance);
            return selected.TryGetProperty(out var declaring, out var hit)
                && ReferenceEquals(declaring.CompletedContext?.Key, level.Key)
                && ReferenceEquals(level.Facts.Member(level.Key, reference.Head), declaring.CompletedContext!.Facts.Member(level.Key, hit.Property.Name));
        }

        internal FrontEndTraversalObservations? Observations => observations;

        private Dictionary<(StaticLookupFacts Facts, int Version, StaticScopeKey Key, bool Opened), (StaticScopeKey Key, string Name, StaticScopeKey Declaring)?>? _referenceTerminals;
        private Dictionary<(StaticLookupFacts Facts, int Version, StaticScopeKey Key), bool>? _openWalkCharges;

        /// <summary>
        /// The reference whose VALUE requirement is what crossing the declaration <paramref name="key"/> (its name
        /// <paramref name="name"/>, declared at <paramref name="declaring"/>) as a receiver or open head charges, or null
        /// when the crossing selects nothing. A transparent reference's target walk selects in the reference's own scope
        /// (<c>aliasStepNavigateWith</c>, <c>openNavigateWith</c>), access-checking each member it selects: a target
        /// that selects a member, or whose head the owner walk does not find (an open provides it), selects exactly
        /// what the reference's VALUE requires, its head's value never being read. A member-less target naming a
        /// lexically found declaration selects nothing itself, so the walk follows it while it is a reference; a
        /// declaration that is not a transparent reference ends it with nothing charged. When the crossing OPENS the
        /// reference (<paramref name="opened"/>: an <c>open</c> head), a reference whose target is no static path — a
        /// runtime reference: a parameter row, a parameter-rooted path, an <c>.Algorithm</c> link, or a static chain
        /// that names one — also ends it with nothing charged: <c>openStructure</c> opens such a reference's OWN
        /// namespace, never establishing its target or reading its row (OD-C; owner decision 3, 2026-11-13). A
        /// receiver crossing keeps it as its terminal, since the evaluator reads that receiver at run time. Completed
        /// facts only; static chains end (OD-D) and a revisited key ends the walk. Every key a walk passes records the
        /// terminal, per completed view, version and mode, so a chain of N links costs O(N) over all of its crossings.
        /// </summary>
        internal (StaticScopeKey Key, string Name, StaticScopeKey Declaring)? ReferenceTerminal(StaticLookupFacts facts,
            StaticScopeKey key, string name, StaticScopeKey declaring, bool opened)
        {
            var terminals = _referenceTerminals ??= new();
            var version = facts.ViewVersion;
            HashSet<StaticScopeKey>? walked = null;
            (StaticScopeKey Key, string Name, StaticScopeKey Declaring)? terminal = null;
            while (true)
            {
                ObserveCancellation();
                if (terminals.TryGetValue((facts, version, key, opened), out var known)) { terminal = known; break; }
                (walked ??= new(ReferenceEqualityComparer.Instance)).Add(key);
                if (facts.Facts(key)?.Body is not Algorithm.Alias { IsReference: true } reference) break;
                // The evaluator's own test (OpenStructure): only a static-path target is followed when opened.
                if (opened && !StaticAliasTargets.IsStaticPath(reference.Target)) break;
                if (reference.Target.UnwrapGraceOperand() is Expr.Resolve(var head)
                    && ElaboratedScopeLookup.SelectOwnedDeclaration(RequirementLevel(facts.Context(key)), head,
                        ElaboratedScopeLookup.OwnParameterBindings.Instance).TryGetProperty(out var level, out var hit)
                    && level.CompletedContext?.Key is { } next && facts.Member(next, hit.Property.Name) is { } nextKey)
                {
                    if (walked.Contains(nextKey)) break;
                    (key, name, declaring) = (nextKey, hit.Property.Name, next);
                    continue;
                }
                terminal = (key, name, declaring);
                break;
            }
            foreach (var passed in walked ?? []) terminals[(facts, version, passed, opened)] = terminal;
            return terminal;
        }

        /// <summary>
        /// Whether the open target <paramref name="target"/> of the level <paramref name="opening"/> can charge its walk:
        /// a dotted target selects members; a member-less one charges only when its head is a transparent reference
        /// whose target walk selects (<see cref="ReferenceTerminal"/>, opened: a runtime reference selects nothing). A
        /// block head is rooted at the prelude, so nothing of the reader's chain is visible inside it.
        /// </summary>
        internal bool OpenTargetMayCharge(ElaboratedPropertyScope opening, Expr target)
        {
            if (target.OpenTargetHead(out var steps) is not Expr.Resolve(var head)) return false;
            if (steps.Count > 0) return true;
            return opening.CompletedContext is { Facts: var facts }
                && ElaboratedScopeLookup.ResolveOpenProviderHead(opening, new Expr.Resolve(head), out var declaring) is not null
                && declaring.CompletedContext?.Key is { } declaringKey && facts.Member(declaringKey, head) is { } headKey
                && ReferenceTerminal(facts, headKey, head, declaringKey, opened: true) is not null;
        }

        /// <summary>Whether any open target of <paramref name="opening"/> can charge its walk, once per level and view.</summary>
        internal bool OpenWalksMayCharge(ElaboratedPropertyScope opening)
        {
            if (opening.Opens.Count == 0 || opening.CompletedContext is not { } context) return false;
            var charges = _openWalkCharges ??= new();
            var key = (context.Facts, context.Facts.ViewVersion, context.Key);
            if (!charges.TryGetValue(key, out var known))
            {
                known = false;
                foreach (var target in opening.Opens)
                    if (OpenTargetMayCharge(opening, target)) { known = true; break; }
                charges.Add(key, known);
            }
            return known;
        }

        // Pure anchoring of an immutable completed seed. The exact source version and the entire
        // intervening owner path (declaring -> ancestor) decide it; no live requirement set is cached.
        internal Dictionary<(StaticLookupFacts Facts, int Version, SummarySeed Seed, StaticScopeKey? Declaring,
            StaticScopeKey Ancestor), SummarySeed>? AnchoredRequirements;

        /// <summary>
        /// Completed contextual branch computations retain their exact binding-region key.
        /// A computation certified free of contextual effects goes instead into
        /// <see cref="IndependentBranchSummaries"/>, by body reference and binder-name set,
        /// after agreement with the authoritative parameter facts. Ordinary property summaries
        /// use a separate cache. All stored seeds follow the same pristine-clone discipline.
        /// </summary>
        internal Dictionary<BranchBodySummaryKey, SummarySeed>? CompletedBranchBodySummaries;

        /// <summary>
        /// FE-3: whether a COMPLETED seed carries nothing but required names that an owner's name
        /// set covers, by (seed, set) reference pair — see <see cref="SummarySeed.DropOwnedAbsorbedParts"/>.
        /// </summary>
        internal Dictionary<(SummarySeed Part, IReadOnlySet<string> Owned), bool>? OwnedPureParts;

        internal bool IsOwnedPureRequirement(SummarySeed part, IReadOnlySet<string> owned)
        {
            // A composed owner signature's names are its owner-local head over a SHARED tail: the part
            // is decided against the tail once (per part and tail), and only the names the tail does not
            // cover are tested against this owner's own set — never the part's full width per owner.
            if (owned is ImplicitSignatureTemplate.NameSetView { Tail: { } tail })
            {
                if (ResidualOf(part, tail) is not { } residual)
                    return false;
                foreach (var name in residual)
                {
                    observations?.RecordSummaryResidualNameProbe();
                    if (!owned.Contains(name))
                        return false;
                }

                return true;
            }

            OwnedPureParts ??= new(OwnedPartKeyComparer.Instance);
            if (!OwnedPureParts.TryGetValue((part, owned), out var pure))
            {
                pure = part.IsPureRequirementWithin(owned, observations);
                OwnedPureParts.Add((part, owned), pure);
            }

            return pure;
        }

        private Dictionary<(SummarySeed Part, IReadOnlySet<string> Owned), string[]?>? _residuals;

        // The required names of a pure-requirement part that a tail name set does not cover (null
        // when the part carries anything but required names), once per (part, tail).
        private string[]? ResidualOf(SummarySeed part, IReadOnlySet<string> tail)
        {
            FrontEndStack.Ensure();
            _residuals ??= new(OwnedPartKeyComparer.Instance);
            if (!_residuals.TryGetValue((part, tail), out var residual))
            {
                residual = part.RequiredNamesOutside(tail, ResidualOf, observations);
                _residuals.Add((part, tail), residual);
            }

            return residual;
        }

        private sealed class OwnedPartKeyComparer : IEqualityComparer<(SummarySeed Part, IReadOnlySet<string> Owned)>
        {
            public static readonly OwnedPartKeyComparer Instance = new();

            public bool Equals((SummarySeed Part, IReadOnlySet<string> Owned) x, (SummarySeed Part, IReadOnlySet<string> Owned) y)
                => ReferenceEquals(x.Part, y.Part) && ReferenceEquals(x.Owned, y.Owned);

            public int GetHashCode((SummarySeed Part, IReadOnlySet<string> Owned) key)
                => HashCode.Combine(
                    System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Part),
                    System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Owned));
        }

        private Dictionary<Algorithm, IReadOnlySet<string>>? _ownerParameterNames;

        private static readonly IReadOnlySet<string> NoParameterNames = new HashSet<string>(StringComparer.Ordinal);

        /// <summary>
        /// <paramref name="owner"/>'s parameter NAMES, materialized once per memo lifetime (FE-1):
        /// every property summary, fixed-point iteration, and requirement strip at that owner
        /// shares this one set instead of re-reading the owner's live <c>Params</c> projection —
        /// W names allocated and scanned per property made an owner of W parameters and K
        /// properties cost K × W. Keyed by node reference: the pass never rewrites a node's
        /// parameter list while summarizing it, and a host AST is not mutated during analysis.
        /// </summary>
        internal IReadOnlySet<string> ParameterNamesOf(Algorithm owner, FrontEndTraversalObservations? observations)
        {
            if (owner is not Algorithm.User { ParameterPatterns.Count: > 0 } user)
                return NoParameterNames;

            // A shared implicit-signature template (FE-3) already holds its name set: every owner of
            // the template reads that one set instead of materializing its own.
            if (user.ParameterPatterns is ImplicitSignatureTemplate template)
                return template.Facts.NameSet;

            _ownerParameterNames ??= new(ReferenceEqualityComparer.Instance);
            if (!_ownerParameterNames.TryGetValue(owner, out var names))
            {
                IReadOnlyList<string> parameters = ParameterPattern.CapturesExpandingSharedNodesOnce(user.ParameterPatterns).Select(static capture => capture.Name).ToArray();
                observations?.RecordOwnerParameterNamesMaterialized(parameters.Count);
                names = new HashSet<string>(parameters, StringComparer.Ordinal);
                _ownerParameterNames.Add(owner, names);
            }

            return names;
        }
    }

    /// <summary>Key of <see cref="SummaryMemo.CompletedBranchBodySummaries"/>: body by reference, binders by content.</summary>
    internal sealed record BranchBodySummaryKey(Algorithm Body, int BinderNames, StaticScopeKey? Scope = null,
        StaticLookupFacts? Facts = null)
    {
        public bool Equals(BranchBodySummaryKey? other)
            => other is not null && ReferenceEquals(Body, other.Body) && BinderNames == other.BinderNames
                && ReferenceEquals(Scope, other.Scope) && ReferenceEquals(Facts, other.Facts);

        public override int GetHashCode()
            => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Body), BinderNames, Scope, Facts);
    }

    /// <summary>
    /// Reference-identity memo state for ONE summary-collection region (one algorithm-level
    /// analysis, or one <see cref="BuildSummaries"/> call's top property loop): the walk's
    /// two context flavors get separate expression maps — the region's PRIMARY (its local
    /// summaries and owned-here names) and the TRANSPARENT bundle context (empty summaries,
    /// empty owned-here — call/dot-call argument bundles and capture rows, identical however
    /// deeply they nest). Stored seeds follow a CLONE discipline: callers mutate returned
    /// seeds as accumulators, so a memo keeps a pristine clone and every reach (first or
    /// later) receives its own mutable copy — semantically identical to re-walking the
    /// equivalent duplicated tree, because seed contributions are name SETS. Whole
    /// nested-algorithm summaries (property values and <see cref="Expr.AlgorithmExpr"/>
    /// contents alike, all summarized under the empty locally-owned context) live on the
    /// region-spanning <see cref="SharedMemo"/> instead, so they are computed once per memo
    /// lifetime rather than once per region; conditional BRANCH bodies stay exempt (their
    /// binder-name context varies per branch). A region ALWAYS has its completed structural
    /// context (<see cref="CompletedContext"/>): what escapes it is anchored there, and no walk,
    /// expansion or settlement runs without one.
    /// </summary>
    internal sealed class SummaryWalkMemos(SummaryMemo sharedMemo, FrontEndTraversalObservations? observations,
        CompletedStructureContext completedContext)
    {
        public readonly CompletedStructureContext CompletedContext = completedContext;
        public Dictionary<Expr, SummarySeed>? TransparentSeeds;
        public Dictionary<OutputBundle, SummarySeed>? ArgumentBundleSeeds;
        public Dictionary<Expr, SummarySeed>? PrimarySeeds;

        public readonly SummaryMemo SharedMemo = sharedMemo;

        public readonly FrontEndTraversalObservations? Observations = observations;
    }

    /// <summary>
    /// The context ONE level offers to the seeds escaping from inside it: the level's
    /// algorithm (whose parameters qualify the requirements it binds) and
    /// its current local property summaries. Used by the builder for every nested level and
    /// by the exposure resolver when it expands a navigated member's seed through the
    /// algorithms of a member path.
    /// </summary>
    internal sealed class LevelContext(
        Algorithm algorithm,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        SummaryWalkMemos memos)
    {
        public Algorithm Algorithm { get; } = algorithm;

        public IReadOnlyDictionary<string, SummarySeed> LocalPropertySummaries { get; } = localPropertySummaries;

        public SummaryWalkMemos Memos { get; } = memos;

        // Only the dynamic extent of ONE ExpandAtLevel call at this exact level. The member map
        // cannot grow during an equation's evaluation; the next evaluation starts with no cache.
        internal Dictionary<string, SummarySeed>? ExpandedSeeds;

        public bool HasOpens => Algorithm.Opens.Count > 0;

        /// <summary>The level algorithm's parameter names, shared through the resolution's memo.</summary>
        public IReadOnlySet<string> ParameterNames => Memos.CompletedContext is { Key.BindingRegion: not null } context
            ? context.Facts.Facts(context.Key)?.Parameters ?? Memos.SharedMemo.ParameterNamesOf(Algorithm, Memos.Observations)
            : Memos.SharedMemo.ParameterNamesOf(Algorithm, Memos.Observations);
    }

    /// <summary>
    /// Recursive summary channel: per-property recursive ancestor-capture facts for the
    /// exposure resolver. A
    /// caller-supplied <paramref name="memo"/> extends completed-summary reuse across every
    /// <see cref="BuildSummaries"/> call of one logical analysis (the exposure resolver
    /// passes one memo per resolution, so a nested algorithm's summary is computed once
    /// rather than once per ancestor level); with no memo the call is standalone and
    /// creates its own. <paramref name="completedContext"/> is the completed structural context
    /// of <paramref name="algorithm"/> and is REQUIRED: summaries are computed in one mode only,
    /// in which every escaping name and path is anchored at the context it was written in. (The
    /// former contextless mode, whose escaping paths needed an origin from settlement,
    /// was deleted in November 2026; a standalone caller supplies
    /// <see cref="AnalyzedStaticStructures.ForBoundAst"/> of the tree it summarizes.)
    /// </summary>
    public static PropertyDependencySummaryGraph BuildSummaries(
        Algorithm algorithm,
        CompletedStructureContext completedContext,
        SummaryMemo? memo = null,
        FrontEndTraversalObservations? observations = null)
    {
        memo ??= new SummaryMemo(observations);
        var propertyNameToIndex = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var i = 0; i < algorithm.Properties.Count; i++)
            propertyNameToIndex[algorithm.Properties[i].Name] = i;

        // One memo bundle spans the whole BuildSummaries call: every property value below is
        // summarized under the same empty locally-owned context, so two properties sharing
        // ONE value algorithm summarize it once — and the caller's shared memo carries the
        // same completed summaries across nesting levels.
        var buildMemos = new SummaryWalkMemos(memo, observations, completedContext);
        var nodes = new PropertyDependencySummaryNode[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            buildMemos.SharedMemo.ObserveCancellation();
            var summarySeed = CollectSharedAlgorithmSummarySeed(algorithm.Properties[i].Value, buildMemos);
            if (summarySeed.IsEmpty)
            {
                nodes[i] = new PropertyDependencySummaryNode(i, [], [], [], [], []);
                continue;
            }

            var summarySiblingDependencyIndices = new HashSet<int>();
            var summaryVisiblePropertyDependencyNames = CreateNameSet();
            foreach (var dependencyName in summarySeed.VisiblePropertyDependencyNames)
            {
                if (propertyNameToIndex.TryGetValue(dependencyName, out var dependencyIndex)
                    && dependencyIndex != i)
                    summarySiblingDependencyIndices.Add(dependencyIndex);
                else
                    summaryVisiblePropertyDependencyNames.Add(dependencyName);
            }

            nodes[i] = new PropertyDependencySummaryNode(
                i,
                summarySiblingDependencyIndices.OrderBy(static idx => idx).ToArray(),
                summaryVisiblePropertyDependencyNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray(),
                summarySeed.RequiredAncestorOwnedParameterNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray(),
                summarySeed.PendingReferences.SelectMany(buildMemos.SharedMemo.SelectedReferences)
                    .Distinct().OrderBy(static pending => pending.ContentKey, StringComparer.Ordinal).ToArray(),
                summarySeed.OwnerQualifiedParameters.ToArray());
        }

        return new PropertyDependencySummaryGraph(algorithm.Properties, propertyNameToIndex, nodes);
    }

    private static CompletedStructureContext ChildContext(CompletedStructureContext parent, Algorithm body,
        Pattern? pattern = null, bool transparentFamily = false)
    {
        var facts = parent.Facts is AnalyzedStaticStructures ? parent.Facts : body.CompletedStructure?.Facts ?? parent.Facts;
        if (parent.Facts is not AnalyzedStaticStructures && body.CompletedStructure is { Entry: { } entry } publication)
            return publication.Facts.Context(entry);
        var declaring = transparentFamily ? parent.Key.Parent ?? facts.PreludeKey : parent.Key;
        var key = pattern is null && ReferenceEquals(facts.Facts(declaring)?.Body, body)
            ? declaring : facts.Child(declaring, body, pattern);
        return facts.Context(key ?? new StaticScopeKey(body.IsModuleRoot ? facts.PreludeKey : declaring,
            OpenProviderIdentity.DeclarationOf(body), pattern));
    }

    /// <summary>
    /// A fresh walk-memo bundle over a shared memo at <paramref name="completedContext"/>, for the exposure resolver's
    /// own charging calls.
    /// </summary>
    internal static SummaryWalkMemos CreateWalkMemos(SummaryMemo memo, FrontEndTraversalObservations? observations,
        CompletedStructureContext completedContext)
        => new(memo, observations, completedContext);

    /// <summary>
    /// Memo-shared nested-algorithm summary for the constant empty locally-owned context —
    /// see <see cref="SummaryMemo"/> for when that summary is shared by node reference and
    /// <see cref="SummarySeed"/> for the clone discipline. The observation counter records
    /// completed COMPUTATIONS (memo misses) only, so an observed analysis is pinned to at most
    /// one computation per distinct algorithm node and context per memo lifetime. A hoisted
    /// deconstruction source's rows are the declaring level's own written rows: they are walked
    /// RAW with that level's memos, so the bare names and paths they write reach the level's
    /// summary graph unanchored and are anchored where the level expands or settles them.
    /// </summary>
    private static SummarySeed CollectSharedAlgorithmSummarySeed(
        Algorithm algorithm,
        SummaryWalkMemos memos)
        => algorithm is Algorithm.User { IsAssignmentDeconstructionSource: true } source
            ? CollectSummarySeed(source.Output, new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
                CreateNameSet(), memos, inTransparentContext: false)
            : GetAlgorithmSummary(algorithm, memos).OutputSeed.Clone();

    /// <summary>
    /// The completed summary of a node (output seed and per-member seeds), computed at most
    /// once per memo lifetime and context. Conditional families and builtins have no members.
    /// The node's context is <paramref name="exactContext"/> when the caller holds it, and
    /// otherwise the node's occurrence below the walk's own context.
    /// </summary>
    internal static AlgorithmSummary GetAlgorithmSummary(Algorithm algorithm, SummaryWalkMemos memos,
        CompletedStructureContext? exactContext = null)
    {
        var context = exactContext ?? ChildContext(memos.CompletedContext, algorithm);
        context = memos.SharedMemo.RequirementContext(context, algorithm);
        context = memos.SharedMemo.SharedRegionContext(context, algorithm);
        var independent = memos.SharedMemo.IndependentAlgorithmSummaries ??= new(ReferenceEqualityComparer.Instance);
        var canShare = context.Key.BindingRegion is null;
        if (canShare && independent.TryGetValue(algorithm, out var shared)) return shared;
        var cache = memos.SharedMemo.ContextualAlgorithmSummaries ??= new();
        var key = (context.Facts, context.Key);
        if (cache.TryGetValue(key, out var result))
        {
            memos.SharedMemo.UseContext();
            return result;
        }
        var uses = memos.SharedMemo.ContextUses;
        if (!canShare) memos.SharedMemo.UseContext();
        memos.Observations?.RecordDependencyAlgorithmSummaryComputation();
        result = CollectAlgorithmSummary(algorithm, CreateNameSet(), memos.SharedMemo, memos.Observations, context);
        if (uses == memos.SharedMemo.ContextUses) independent.Add(algorithm, result);
        else cache[key] = result;
        return result;
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm algorithm,
        IReadOnlySet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext completedContext)
        => CollectAlgorithmSummary(algorithm, locallyOwnedNames, sharedMemo, observations, completedContext).OutputSeed;

    private static AlgorithmSummary CollectAlgorithmSummary(
        Algorithm algorithm,
        IReadOnlySet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext completedContext)
    {
        FrontEndStack.Ensure();
        sharedMemo.ObserveCancellation();
        // Only the Q8 walk supplies this already detected provisional view. It is a lexical
        // requirement frame, never a successful structural body or a raw-reference fallback.
        completedContext = sharedMemo.RequirementContext(completedContext, algorithm);
        return algorithm switch
        {
            // A callable alias is summarized exactly like a body with no parameters whose one row
            // is its target reference: what the alias requires is what reading its target requires
            // (its exposure follows that read), and its own declarations are its only members.
            Algorithm.User or Algorithm.Alias => CollectScopeBodySummary(algorithm, locallyOwnedNames, sharedMemo, observations, completedContext),
            Algorithm.Conditional conditional => new AlgorithmSummary(
                CollectSummarySeed(conditional, locallyOwnedNames, sharedMemo, observations, completedContext),
                AlgorithmSummary.NoMembers),
            Algorithm.Builtin => new AlgorithmSummary(new SummarySeed(), AlgorithmSummary.NoMembers),
        };
    }

    /// <summary>
    /// The summary of a SCOPE BODY — a user algorithm, or a callable alias (whose output is its one
    /// target row and which declares no parameters) — read through the total accessors.
    /// </summary>
    private static AlgorithmSummary CollectScopeBodySummary(
        Algorithm algorithm,
        IReadOnlySet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext completedContext)
    {
        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is self-contained: it
        // binds its own N-capture pattern and outputs one of those bound params, capturing no
        // ancestor-owned parameter and referencing no visible or sibling property (the shared
        // `$deconstruct$` source is referenced by the helper's ARGS, not the helper itself). Its
        // summary is therefore empty. Walking it costs O(N) per helper in its capture count
        // (the ownedHere union below and the fixed-point setup), so a wide deconstruction is
        // O(N^2) across its N sibling helpers without this leaf guard.
        if (algorithm is Algorithm.User { AssignmentDeconstructionTarget: not null })
            return new AlgorithmSummary(new SummarySeed(), AlgorithmSummary.NoMembers);

        var ownerParameterNames = sharedMemo.ParameterNamesOf(algorithm, observations);
        // The owned-here set is read only: with no locally owned names it IS the owner's parameter
        // set (a template owner's shared set), never a per-owner copy of it (FE-3).
        IReadOnlySet<string> ownedHere;
        if (locallyOwnedNames.Count == 0)
        {
            ownedHere = ownerParameterNames;
        }
        else
        {
            var union = CreateNameSet(locallyOwnedNames);
            union.UnionWith(ownerParameterNames);
            ownedHere = union;
        }

        // Ownership attribution follows the same transparency model as
        // ParameterDetector: transparent OutputBundle content (call/dot-call
        // argument bundles, surviving parenthesized groups) owns no names, so
        // its walk uses the enclosing algorithm's owned-name set. A parameter
        // reference inside such a layer therefore seeds the same
        // ancestor-capture requirement as the identical reference written
        // directly in the enclosing owner; the final
        // RemoveRequiredAncestorOwnedParameterNames strip below keeps each
        // algorithm's self-owned parameters out of the summary it returns. What
        // ancestors own is deliberately NOT an input: a parameter reference not
        // owned within this walk is reported as a required ancestor-owned name
        // regardless, which is what lets an empty-locals summary that used no
        // context be shared by node (see SummaryMemo).

        // One expression-memo bundle per algorithm-level analysis region: the property base
        // seeds and the opens/output walks below all run against this region's local-summary
        // and owned-here context (property values and nested AlgorithmExpr contents go
        // through the shared completed-summary memo instead).
        var memos = new SummaryWalkMemos(sharedMemo, observations, completedContext);
        var currentPropertySummaries = new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
        var propertyBaseSeeds = new SummarySeed[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            var property = algorithm.Properties[i];
            currentPropertySummaries[property.Name] = new SummarySeed();
            propertyBaseSeeds[i] = CollectSharedAlgorithmSummarySeed(property.Value, memos);
        }

        if (propertyBaseSeeds.Length > 0)
            SolveMemberSeeds(algorithm, propertyBaseSeeds, currentPropertySummaries, memos);

        var seed = CollectOpenTargetSeeds(algorithm.Opens, currentPropertySummaries, ownedHere, memos);
        seed.UnionWith(CollectSummarySeed(
            algorithm.Output,
            currentPropertySummaries,
            ownedHere,
            memos,
            inTransparentContext: false));

        // A name the opens/output walk reported unresolved from a transparent layer (a capture
        // row, a call or dot-call argument bundle — walked with empty local maps, see the arms
        // below) or from a nested block (whose completed summary knows nothing of this level)
        // is a reference written in THIS algorithm's lexical context, so ownership-first
        // resolution consults this algorithm's own properties before the name may escape to
        // the enclosing level — exactly as each property base seed is expanded against the
        // same local fixed point. Without this step `G = { Q = p + 1  (Q) }` reported the bare
        // name `Q` upward: an enclosing level with no `Q` dropped it (a local-only `G` leaked
        // through `open`), and an enclosing sibling `Q` was wrongly consulted (a self-contained
        // `G` was hidden). The same expansion turns each name this level's own `open`
        // declarations may provide into a pending reference carrying those providers.
        var finalLevel = new LevelContext(algorithm, currentPropertySummaries, memos);
        // Absorbed completed parts that only require names this level owns are exactly what the
        // expansion below would qualify and the strip after it remove: they are dropped by
        // reference, never folded (FE-3 — K owners that each absorbed one shared L-name argument
        // bundle seed would otherwise each copy, qualify, and strip its L names).
        seed.DropOwnedAbsorbedParts(ownedHere, sharedMemo);
        seed = ExpandAtLevel(seed, finalLevel);
        seed.RemoveRequiredAncestorOwnedParameterNames(ownedHere, algorithm,
            ownerHasParameters: ownerParameterNames.Count > 0 || locallyOwnedNames.Count > 0, observations);

        // A loaded module (Q-31 H-P) is wired to the prelude wherever it is held, exactly like an
        // inline open block: what still escapes its own levels is a
        // lookup only the prelude answers, so nothing of the holder's chain can be required.
        if (algorithm.IsModuleRoot)
            seed = SettledAtPrelude(seed);

        // Navigating a member does not call its owner. Retain the exact declaration
        // that binds each parameter instead of reinterpreting its name at the consumer:
        // every member seed is already qualified with this algorithm's parameter names, because
        // each one is its own expansion at this level (ExpandAtLevel qualifies with the same
        // names, and a shared seed is such an expansion too). Qualifying again would be a no-op
        // that folds, and so copies, every seed a member holds by reference (FE-4a).

        // The member seeds a consumer navigates into (`Inner.X`, an opened `X`) are the
        // level's final local summaries, which are relative to this level's PARENT: they keep
        // this level's own parameters as requirements (an `X = p` inside `Lib(p)` requires
        // `p` — that is exactly what makes it local-only), so only the output seed strips them.
        // A level that declares no property has no member to navigate into: it shares the one empty
        // member map instead of retaining its own empty dictionary in the completed-summary memo.
        return new AlgorithmSummary(seed, currentPropertySummaries.Count == 0 ? AlgorithmSummary.NoMembers : currentPropertySummaries);
    }

    /// <summary>
    /// The level expansion — THE ownership-first step of the summary channel at one level:
    /// a bare name that is one of the level's own properties resolves here to that property's
    /// summary, and so does a pending reference the completed structure proves to select one
    /// (<see cref="SummaryMemo.SelectsLocalMember"/>); anything else escapes to the enclosing
    /// level, anchored at this level's completed context and still UNSETTLED
    /// (<see cref="AddEscaping"/>). No member path is navigated and no <c>open</c> provider is
    /// selected here: the owning level's settlement does both, from the completed structure
    /// (<see cref="PropertyExposureResolver"/>). The requirements this level's own parameters
    /// bind are owner-qualified on the way out.
    /// </summary>
    internal static SummarySeed ExpandAtLevel(SummarySeed baseSeed, LevelContext level)
    {
        // A seed with no requirement, name or reference has nothing to resolve, escape or qualify at any level, and a cycle
        // cut cannot change that: its expansion is the empty seed, whatever the level.
        return baseSeed.IsEmpty ? new SummarySeed() : RunExpansion(ExpandFrame(baseSeed, level), level.Memos.SharedMemo).Seed!;
    }

    /// <summary>
    /// OOS-22: ONE suspended step of the level expansion — an expansion at a level
    /// (<see cref="ExpandAtLevelCore"/>) or the carrying of one escaping reference
    /// (<see cref="AddEscaping"/>). The steps never recurse on the host stack: each is a heap frame
    /// whose body yields the nested frame it needs next, and <see cref="RunExpansion"/> resumes it
    /// with that frame's result exactly where a recursive form would have returned. When an escaping
    /// step still settled an opened member's charge at the owner, the steps re-entered one another
    /// once per link of an opened chain; an escaping step now only carries its reference, so an
    /// expansion nests no deeper than the two kinds of step. The cancellation checkpoints and the
    /// unwinding of <see cref="RunExpansion"/> are unchanged.
    /// </summary>
    private sealed class ExpansionFrame
    {
        public IEnumerator<ExpansionFrame> Body = null!;
        public SummarySeed? Seed;
    }

    /// <summary>
    /// Runs <paramref name="root"/> to completion over an explicit stack: a frame yielding a nested
    /// frame is suspended until that frame completes. An exception unwinds every suspended frame
    /// innermost first, so each one's active key and level cache are released exactly as the
    /// recursion's <c>finally</c> blocks released them; no partial result is stored on that path.
    /// Each frame pushed is one cancellation checkpoint of <paramref name="memo"/>'s token (2.06), so a
    /// cancelled expansion unwinds the same way.
    /// </summary>
    private static ExpansionFrame RunExpansion(ExpansionFrame root, SummaryMemo memo)
    {
        var frames = new Stack<ExpansionFrame>();
        frames.Push(root);
        try
        {
            memo.ObserveCancellation();
            while (frames.TryPeek(out var frame))
            {
                if (frame.Body.MoveNext())
                {
                    frames.Push(frame.Body.Current);
                    memo.ObserveCancellation();
                }
                else
                    frames.Pop();
            }
        }
        finally
        {
            while (frames.TryPop(out var suspended))
                suspended.Body.Dispose();
        }

        return root;
    }

    private static ExpansionFrame ExpandFrame(SummarySeed baseSeed, LevelContext level)
    {
        var frame = new ExpansionFrame();
        frame.Body = ExpandAtLevelCore(frame, baseSeed, level);
        return frame;
    }

    private static ExpansionFrame EscapingFrame(SummarySeed expanded, PendingReference pending, LevelContext level)
    {
        var frame = new ExpansionFrame();
        frame.Body = AddEscaping(expanded, pending, level);
        return frame;
    }

    /// <summary>One expansion at <paramref name="level"/>; its result is <paramref name="self"/>'s <see cref="ExpansionFrame.Seed"/>.</summary>
    private static IEnumerator<ExpansionFrame> ExpandAtLevelCore(ExpansionFrame self, SummarySeed baseSeed, LevelContext level)
    {
        var outermost = level.ExpandedSeeds is null;
        var completed = level.ExpandedSeeds ??= new(StringComparer.Ordinal);
        try
        {
            var cacheKey = baseSeed.ContentKeyFor(level.Memos.Observations);
            if (completed.TryGetValue(cacheKey, out var cached))
            {
                self.Seed = cached.Clone();
                yield break;
            }

            var cuts = level.Memos.SharedMemo.ExpansionCycleCuts;
            var expanded = new SummarySeed(
                requiredAncestorOwnedParameterNames: baseSeed.RequiredAncestorOwnedParameterNames,
                ownerQualifiedParameters: baseSeed.OwnerQualifiedParameters);

            foreach (var dependencyName in baseSeed.VisiblePropertyDependencyNames)
            {
                if (level.LocalPropertySummaries.TryGetValue(dependencyName, out var localSummary))
                {
                    expanded.UnionWith(localSummary);
                    continue;
                }

                yield return EscapingFrame(expanded, new PendingReference(dependencyName, []), level);
            }

            var context = level.Memos.CompletedContext;
            foreach (var pending in baseSeed.PendingReferences)
            {
                level.Memos.SharedMemo.UseContext();
                // The same Q1-proved local equation bridge used by SolveMemberSeeds applies
                // when anchoring an external seed through this owner. Read the live map so
                // expansion-cache dependency tracking and invalidation remain unchanged.
                if (level.Memos.SharedMemo.SelectsLocalMember(pending, context)
                    && level.LocalPropertySummaries.TryGetValue(pending.Head, out var local))
                {
                    expanded.AbsorbCompleted(local);
                    continue;
                }
                expanded.PendingReferences.Add(pending.At(context));
            }

            expanded.QualifyParameters(level.Algorithm, level.ParameterNames, level.Memos.Observations);
            // A partial expansion depends on the active path. It must never be served elsewhere.
            if (cuts == level.Memos.SharedMemo.ExpansionCycleCuts)
                completed.TryAdd(cacheKey, expanded.Clone());
            self.Seed = expanded;
        }
        finally
        {
            if (outermost)
                level.ExpandedSeeds = null;
        }
    }

    /// <summary>
    /// Carries a requirement's context without settling a raw path or provider: the escaping reference is anchored
    /// at the level's completed context, so no expansion leaves a bare name or an origin-less path behind.
    /// </summary>
    private static IEnumerator<ExpansionFrame> AddEscaping(SummarySeed expanded, PendingReference pending, LevelContext level)
    {
        level.Memos.SharedMemo.UseContext();
        expanded.PendingReferences.Add(pending.At(level.Memos.CompletedContext));
        yield break;
    }

    /// <summary>Stops lexical requirement escape at the prelude without evaluating a provider.</summary>
    internal static SummarySeed SettledAtPrelude(SummarySeed seed)
        => new(seed.RequiredAncestorOwnedParameterNames, ownerQualifiedParameters: seed.OwnerQualifiedParameters);

    /// <summary>
    /// The static member path of a dot chain — a lexical head followed by argumentless dot
    /// steps, the shape the evaluator navigates structurally (<c>ResolveDotReceiver</c>) — with
    /// the final edge's member included whether or not it carries arguments. A step spelled
    /// <c>string</c> is navigated like any step (Q-17 S-C): navigation charges a declared
    /// member <c>string</c>, and a receiver the navigation stops at (the member is absent: the
    /// edge is the intrinsic, which reads that receiver's VALUE) charges its output exactly as
    /// the bare target seed would. False for every other receiver shape (a parameter, a block,
    /// a capture, a call). <paramref name="intermediates"/> are the argumentless edges strictly
    /// between the head and the final edge (<see cref="MemberPathSpine"/>).
    /// </summary>
    private static bool TryGetStaticMemberPath(Expr.DotCall dotCall, out string head, out IReadOnlyList<string> members,
        out IReadOnlyList<Expr.DotCall> intermediates)
    {
        if (MemberPathSpine(dotCall, out var reversed, out intermediates) is Expr.Resolve(var name))
        {
            reversed.Reverse();
            head = name;
            members = reversed;
            return true;
        }

        head = string.Empty;
        members = [];
        intermediates = [];
        return false;
    }

    /// <summary>
    /// The spine both path recognizers share: the head expression of a dot chain, the step names from the final
    /// edge back to the first (<paramref name="reversed"/>), and the INTERMEDIATE edges, the argumentless edges
    /// strictly between the head and the final edge, outermost first. Each intermediate edge is a selection of
    /// its own: where its receiver's structural lookup misses, the evaluator calls that edge's lexical fallback
    /// (<c>ResolveDotReceiver</c> hands the edge to <c>ResolveAlg</c>) before the path continues by value, so a
    /// path seed charges every intermediate fallback that may be selected, exactly like the final edge's
    /// (<see cref="CollectDotCallSummarySeed"/>).
    /// </summary>
    private static Expr MemberPathSpine(Expr.DotCall dotCall, out List<string> reversed,
        out IReadOnlyList<Expr.DotCall> intermediates)
    {
        reversed = [dotCall.Name];
        List<Expr.DotCall>? edges = null;
        var current = dotCall.Target.UnwrapGraceOperand();
        while (current is Expr.DotCall { Args: null } edge)
        {
            reversed.Add(edge.Name);
            (edges ??= []).Add(edge);
            current = edge.Target.UnwrapGraceOperand();
        }

        intermediates = edges is null ? [] : edges;
        return current;
    }

    /// <summary>
    /// The static member path of a dot chain whose head is an INLINE BLOCK (<c>{ … }.Sub.Q</c>, the same spine as
    /// <see cref="TryGetStaticMemberPath"/>), with the block's completed context. The evaluator selects the path's
    /// members from the block wired under the reading scope, checking each one's accessibility, and reads the block's
    /// VALUE only when the first step selects nothing, so the path is charged like a name-headed one
    /// (<see cref="PendingSelection.BlockHead"/>). A recognized block must have published body facts in this context;
    /// their absence is an invariant failure, never permission to charge the block's output instead. False for a
    /// loaded module's root, which is rooted at the prelude. The path's
    /// <paramref name="intermediates"/> are those of <see cref="MemberPathSpine"/>, as for a name-headed path.
    /// <para>A block written in a hoisted deconstruction right-hand side is found here too: the source's rows are
    /// walked with the memos of the level that declares the deconstruction, and that level's completed context is
    /// the one the static facts declare the block in (the source's own context holds no written expression).</para>
    /// </summary>
    private static bool TryGetBlockMemberPath(Expr.DotCall dotCall, SummaryWalkMemos memos,
        out CompletedStructureContext block, out string[] members, out IReadOnlyList<Expr.DotCall> intermediates)
    {
        block = null!;
        members = [];
        intermediates = [];
        if (MemberPathSpine(dotCall, out var reversed, out var edges) is not Expr.AlgorithmExpr(var body)
            || body.IsModuleRoot || body is not (Algorithm.User or Algorithm.Alias))
            return false;
        var context = memos.SharedMemo.RequirementContext(ChildContext(memos.CompletedContext, body), body);
        if (context.Facts.Facts(context.Key) is not { Body: not null })
            throw new InvalidOperationException("A completed block-head requirement body is unavailable.");
        memos.SharedMemo.UseContext();
        reversed.Reverse();
        block = context;
        members = [.. reversed];
        intermediates = edges;
        return true;
    }

    /// <summary>
    /// The opens walk of a level: a named target charges the navigated provider path
    /// (<c>open A</c> needs only A's identity; <c>open A.B</c> charges the
    /// requirements of the navigated member <c>B</c>), an inline-headed target charges
    /// nothing (its block is wired to the prelude), and
    /// any other (illegal, recovery) shape walks as an ordinary expression. An open target is
    /// not a call, so no lexical fallback is ever charged for it.
    /// </summary>
    private static SummarySeed CollectOpenTargetSeeds(
        IReadOnlyList<Expr> opens,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos)
    {
        var seed = new SummarySeed();
        foreach (var target in opens)
        {
            switch (target.OpenTargetHead(out var steps))
            {
                case Expr.Resolve(var head):
                    if (steps.Count > 0)
                        seed.UnionWith(new SummarySeed(pendingReferences: [new PendingReference(head, steps, origin: memos.CompletedContext, openPath: true)]));
                    break;

                // An inline provider is also an identity, never an evaluated output, and so is
                // a dotted path navigated from one: the block is wired to the prelude, so neither
                // it nor any member reached from it can require anything of the opener's chain.
                // Provider signature/form validity is checked independently.
                case Expr.AlgorithmExpr:
                    break;

                default:
                    seed.UnionWith(CollectSummarySeed(target, localPropertySummaries, ownedHere, memos, inTransparentContext: false));
                    break;
            }
        }

        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm.Conditional algorithm,
        IReadOnlySet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext completedContext)
    {
        var ownedHere = CreateNameSet(locallyOwnedNames);
        var localSummaries = new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
        var memos = new SummaryWalkMemos(sharedMemo, observations, completedContext);
        var seed = CollectOpenTargetSeeds(
            algorithm.Opens,
            localSummaries,
            ownedHere,
            memos);

        var contributed = new HashSet<BranchBodySummaryKey>();
        foreach (var branch in algorithm.Branches)
        {
            // Branch bodies deliberately bypass the node-keyed completed-summary memo: their
            // binder-name context varies per branch, so their summaries are NOT pure
            // functions of the body node (see SummaryMemo). They are pure functions of
            // (body, binder names), which the branch-body memo keys on — so a body shared by
            // several families under the same binders is summarized once (M4).
            var context = sharedMemo.BranchContexts.NamesOf(branch.Pattern);
            var binderNames = context.Names;
            var branchContext = ChildContext(completedContext, branch.Body, branch.Pattern, algorithm.Opens.Count == 0);
            var key = new BranchBodySummaryKey(branch.Body, context.Id, branchContext.Key, branchContext.Facts);
            // Union is idempotent. One family's repeated reach of the same region contributes
            // nothing new, so skip BEFORE cloning or merging its potentially wide summary.
            if (!contributed.Add(key))
                continue;
            var contribution = CollectBranchBodySummarySeed(branch, binderNames, key, sharedMemo, observations, branchContext);
            observations?.RecordBranchSummaryContribution(contribution.RequiredAncestorOwnedParameterNames.Count
                + contribution.VisiblePropertyDependencyNames.Count + contribution.PendingReferences.Count
                + contribution.OwnerQualifiedParameters.Count);
            seed.UnionWith(contribution);
        }

        // Host-built families can own opens. They are a static lookup level above
        // the branch bodies, just as at runtime: never charge a provider's output,
        // and anchor the branch references that escape this level at it.
        return algorithm.Opens.Count == 0 ? seed
            : ExpandAtLevel(seed, new LevelContext(algorithm, localSummaries, memos));
    }

    /// <summary>
    /// Memo-shared branch-body summary for one (body, binder-name set) — see
    /// <see cref="SummaryMemo.CompletedBranchBodySummaries"/>. Records completed computations
    /// (memo misses) only, like <see cref="CollectSharedAlgorithmSummarySeed"/>.
    /// </summary>
    private static SummarySeed CollectBranchBodySummarySeed(
        CondBranch branch,
        IReadOnlySet<string> binderNames,
        BranchBodySummaryKey key,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext completedContext)
    {
        completedContext = sharedMemo.SummaryRegion(completedContext, branch.Body);
        completedContext = sharedMemo.SharedRegionContext(completedContext, branch.Body);
        key = key with { Scope = completedContext.Key, Facts = completedContext.Facts };
        var independentKey = key with { Scope = null, Facts = null };
        var independent = sharedMemo.IndependentBranchSummaries ??= new();
        var canShare = sharedMemo.BranchParametersAgree(branch.Body, binderNames, completedContext);
        if (canShare && independent.TryGetValue(independentKey, out var shared)) return shared.Clone();
        var completedSummaries = sharedMemo.CompletedBranchBodySummaries ??= new();
        if (completedSummaries.TryGetValue(key, out var stored))
        {
            sharedMemo.UseContext();
            return stored.Clone();
        }

        var uses = sharedMemo.ContextUses;
        if (!canShare) sharedMemo.UseContext();
        observations?.RecordDependencyBranchBodySummaryComputation();
        var seed = CollectSummarySeed(branch.Body, CreateNameSet(binderNames), sharedMemo, observations, completedContext);
        if (canShare && uses == sharedMemo.ContextUses) independent.Add(independentKey, seed.Clone());
        else completedSummaries[key] = seed.Clone();
        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        IReadOnlyList<Expr> expressions,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        var seed = new SummarySeed();
        foreach (var expression in expressions)
            seed.UnionWith(CollectSummarySeed(expression, localPropertySummaries, ownedHere, memos, inTransparentContext));

        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        Expr expr,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        // DAG-safety: a shared node reference is summarized once per (region, context
        // flavor); every reach receives its own mutable CLONE of the pristine stored seed
        // (see SummaryWalkMemos), which is exactly what re-walking the duplicated tree
        // would contribute. The inTransparentContext flag travels in lock-step with the
        // empty summaries/owned-here maps the transparent arms pass. Childless leaves
        // build their seed in place.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return CollectSummarySeedCore(expr, localPropertySummaries, ownedHere, memos, inTransparentContext);

        var seedMap = inTransparentContext
            ? memos.TransparentSeeds ??= new(ReferenceEqualityComparer.Instance)
            : memos.PrimarySeeds ??= new(ReferenceEqualityComparer.Instance);
        if (seedMap.TryGetValue(expr, out var stored))
            return stored.Clone();

        memos.Observations?.RecordDependencySeedExpansion();
        var seed = CollectSummarySeedCore(expr, localPropertySummaries, ownedHere, memos, inTransparentContext);
        seedMap[expr] = seed.Clone();
        return seed;
    }

    private static SummarySeed CollectSummarySeedCore(
        Expr expr,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        FrontEndStack.Ensure();
        SummarySeed Seed(Expr child)
            => CollectSummarySeed(child, localPropertySummaries, ownedHere, memos, inTransparentContext);

        return expr switch
        {
            Expr.Param(var name) => ownedHere.Contains(name)
                ? new SummarySeed()
                : new SummarySeed(requiredAncestorOwnedParameterNames: [name]),

            Expr.Resolve(var name) => localPropertySummaries.TryGetValue(name, out var localPropertySummary)
                ? localPropertySummary.Clone()
                : new SummarySeed(visiblePropertyDependencyNames: [name]),

            Expr.Grace(var inner, _) => Seed(inner),
            Expr.Binary(_, var left, var right) => Seed(left).Absorb(Seed(right)),
            Expr.Comparison(var first, var links) => links.Aggregate(Seed(first), (seed, link) => seed.Absorb(Seed(link.Operand))),
            Expr.Unary(_, var operand) => Seed(operand),
            // Selector slots are written in the ENCLOSING context, like list elements.
            Expr.Index(var target, var selectors) => Seed(target).Absorb(CollectSummarySeed(
                selectors, localPropertySummaries, ownedHere, memos, inTransparentContext)),
            Expr.SequenceSpread(var operand) => Seed(operand),
            Expr.SequenceConstruct(var left, var right) => Seed(left).Absorb(Seed(right)),
            Expr.ListLiteral(var listItems) => CollectSummarySeed(
                listItems, localPropertySummaries, ownedHere, memos, inTransparentContext),

            Expr.AlgorithmExpr(var algorithm) => CollectSharedAlgorithmSummarySeed(algorithm, memos),

            // A capture owns no names: its rows walk with an empty
            // owned-here set and an empty local-summary map — exactly what
            // the pre-split transparent wrapper algorithm's output walk did
            // (the same attribution as call-argument bundles). The names it
            // reports unresolved are resolved against the enclosing
            // algorithm's own property summaries at the algorithm level
            // (CollectSummarySeed(Algorithm.User)), never left to escape.
            Expr.Capture(var captureBody) => CollectTransparentBundleSummarySeed(captureBody, memos),

            // An argument bundle owns no names: slots walk with an empty
            // owned-here set and an empty local-summary map — the same
            // attribution as capture rows (and as the pre-Track-B empty
            // transparent args wrapper). Its seed is a pure function of the
            // bundle, completed once per region and absorbed by reference when
            // large: a synthesized bundle shared by K call edges (FE-2) is
            // summarized once, not once per edge.
            Expr.Call(var function, var args) => Seed(function).AbsorbCompleted(CompletedArgumentBundleSeed(args, memos)),

            Expr.DotCall dotCall => CollectDotCallSummarySeed(
                dotCall, localPropertySummaries, ownedHere, memos, inTransparentContext),

            // Intentional leaves with no name occurrences: literals, the empty
            // sequence, and native-call bodies (whose argument names are
            // parameter references by construction).
            Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence or Expr.NativeCall => new SummarySeed(),
        };
    }

    /// <summary>
    /// Seed of a scope-less bundle (capture rows, argument slots): the rows walk with an
    /// empty owned-here set and an empty local-summary map in the transparent context.
    /// </summary>
    private static SummarySeed CollectTransparentBundleSummarySeed(OutputBundle bundle, SummaryWalkMemos memos)
    {
        var seed = CollectSummarySeed(
            bundle.Head,
            new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
            CreateNameSet(),
            memos,
            inTransparentContext: true);
        if (bundle.Tail is { } tail)
            seed.AbsorbCompleted(CompletedArgumentBundleSeed(tail, memos));
        return seed;
    }

    /// <summary>
    /// The COMPLETED seed of a call or dot-call argument bundle, computed once per bundle per
    /// region (the transparent walk's context is constant, so the seed is a pure function of the
    /// bundle) and never mutated afterwards — callers take it with
    /// <see cref="SummarySeed.AbsorbCompleted"/>. Implicit lifting shares one synthesized bundle
    /// between every lifted reference to a callee in a resolver region (FE-2).
    /// </summary>
    private static SummarySeed CompletedArgumentBundleSeed(OutputBundle bundle, SummaryWalkMemos memos)
    {
        FrontEndStack.Ensure();
        var independent = memos.SharedMemo.IndependentArgumentBundles ??= new(ReferenceEqualityComparer.Instance);
        if (independent.TryGetValue(bundle, out var shared)) return shared;
        var bundleSeeds = memos.ArgumentBundleSeeds ??= new(ReferenceEqualityComparer.Instance);
        if (!bundleSeeds.TryGetValue(bundle, out var seed))
        {
            var uses = memos.SharedMemo.ContextUses;
            memos.Observations?.RecordDependencyArgumentBundleSummary();
            seed = CollectTransparentBundleSummarySeed(bundle, memos);
            if (uses == memos.SharedMemo.ContextUses)
                independent.Add(bundle, seed);
            else bundleSeeds.Add(bundle, seed);
        }
        else memos.SharedMemo.UseContext();

        return seed;
    }

    /// <summary>
    /// The DotCall arm of <see cref="CollectSummarySeedCore"/>. A static member path
    /// (<c>Inner.X</c>, <c>Lib.Sub.Q</c>, <c>Lib.F(1)</c>) is charged by NAVIGATION at the
    /// level that resolves its head: every member the evaluator would navigate to charges
    /// its own requirements — so a container reading a captured member through
    /// <c>Inner.X</c> is itself local-only — and a receiver the walk stops at (the member
    /// is absent: the edge falls back) charges its output exactly as the bare target seed
    /// did. An inline-block head is navigated the same way, from the block itself
    /// (<see cref="TryGetBlockMemberPath"/>). A receiver of any other shape (a parameter, a
    /// capture, a call, the <c>string</c> intrinsic) is a value and keeps charging its own seed.
    /// <para>EVERY edge of a recognized path is charged its lexical fallback, not only the
    /// final one: the path is one pending reference over all its steps, and navigation
    /// settles the members it selects, so each intermediate edge (<c>Box.S.T</c> inside
    /// <c>Box.S.T.U</c>) contributes its own fallback seed here whenever that fallback MAY be
    /// selected. The evaluator calls the fallback <c>T(Box.S)</c> where <c>S</c> lacks
    /// <c>T</c> and continues by value, so <c>T</c>'s requirements are the path's; a path that
    /// dropped them left its reader exported and cached run-wide across activations. A
    /// declared structural hit is stamped NEVER, so an ordinary path (<c>Lib.Sub.Q</c>) charges
    /// no fallback at all. The cost is one leaf walk per intermediate edge.</para>
    /// <para>The stored lexical-fallback identity is an ordinary elaborated name expression
    /// (Resolve/Param) and participates in dependency analysis EXACTLY like a written
    /// callee name — through this same walk with the enclosing attribution — whenever the
    /// fallback MAY be selected at runtime (<see cref="AstHelpers.LexicalFallbackMayBeSelected"/>:
    /// the detector's stamped scope-aware verdict, or the raw shape classification on an
    /// unstamped edge). A receiver that declares the member never selects the fallback, so
    /// a Param fallback hidden behind a structural winner charges nothing and the property
    /// keeps its exported structural/open access; a receiver known to lack it — a sibling
    /// property whose value is a list, a call result, a literal — always does, so
    /// <c>Big = Data.f</c> with <c>f</c> an enclosing parameter is local-only exactly like
    /// the direct call <c>f(Data)</c>. Charging only CERTAIN selections left such a
    /// property exported although its value depends on the parameter: structural
    /// navigation could then read a dynamic binding through it, and the run-wide
    /// zero-argument property cache of an exported binding would have served one
    /// activation's value to another (SEMANTIC-ALIGNMENT, F3).</para>
    /// </summary>
    private static SummarySeed CollectDotCallSummarySeed(
        Expr.DotCall dotCall,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        SummarySeed seed;
        IReadOnlyList<Expr.DotCall> intermediates;
        if (TryGetStaticMemberPath(dotCall, out var pathHead, out var pathMembers, out intermediates))
            seed = new SummarySeed(pendingReferences: [new PendingReference(pathHead, pathMembers)]);
        else if (TryGetBlockMemberPath(dotCall, memos, out var block, out var blockMembers, out intermediates))
            seed = new SummarySeed(pendingReferences: [new PendingReference(blockMembers[0], blockMembers[1..],
                origin: block, selection: PendingSelection.BlockHead)]);
        else
            // Not a path: the target is walked as an expression, so every inner edge is charged by its own visit.
            seed = CollectSummarySeed(dotCall.Target, localPropertySummaries, ownedHere, memos, inTransparentContext);

        // The final edge, then each intermediate edge of a recognized path (none otherwise).
        ChargeFallback(dotCall);
        foreach (var edge in intermediates)
            ChargeFallback(edge);

        void ChargeFallback(Expr.DotCall edge)
        {
            if (edge.LexicalFallbackMayBeSelected())
                seed.UnionWith(CollectSummarySeed(
                    edge.EffectiveLexicalFallback,
                    localPropertySummaries,
                    ownedHere,
                    memos,
                    inTransparentContext));
        }

        if (dotCall.Args is { } argsOpt)
            seed.AbsorbCompleted(CompletedArgumentBundleSeed(argsOpt, memos));

        return seed;
    }

    /// <summary>
    /// FE-4a: the LEAST FIXED POINT of one algorithm's member-seed equations — member <c>i</c>'s seed is
    /// its base seed expanded at the level (<see cref="ExpandAtLevel"/>) against the current member
    /// seeds. Every expansion is monotone in those seeds (it unites them; which references escape and
    /// which providers settle them is structural), so any fair iteration from the empty seeds reaches
    /// the least fixed point the former round-by-round iteration reached. This one is dependency-driven:
    /// every equation is evaluated once and later only when a member seed it read has changed, so a
    /// chain of K members costs O(K) evaluations instead of K rounds of all K. The map is keyed by
    /// NAME and a name's equation is its LAST declaration's, exactly as the former last-write-wins map.
    ///
    /// <para>Evaluations SHARE seeds instead of copying them. A base seed that carries no path and only
    /// names local members (besides its own requirements) expands to exactly its own requirements,
    /// qualified here, united with those members' seeds — already expanded and qualified at this level.
    /// Content-empty member seeds contribute nothing; when the rest are ONE seed, the member IS that
    /// seed (no own requirements: K members aliasing one W-wide member hold one seed) or holds it BY
    /// REFERENCE beneath its own qualified delta (a member adding a few inputs to a shared W-wide member
    /// costs its delta). Base seeds of equal content expand to equal content while the member seeds
    /// they read stand, so any other expansion is reused, validated by those reads, for every member
    /// whose base seed has that content (K members reading one opened or navigated member expand it
    /// once). A member seed is never mutated after it enters the map (every one is its own expansion at
    /// this level, so it is already qualified), and every consumer clones a member seed before
    /// accumulating, so sharing is unobservable. Change detection compares structure first (own sets
    /// and the seeds held by reference) and folds only when that cannot decide.</para>
    /// </summary>
    private static void SolveMemberSeeds(
        Algorithm algorithm,
        SummarySeed[] baseSeeds,
        Dictionary<string, SummarySeed> seeds,
        SummaryWalkMemos memos)
    {
        var properties = algorithm.Properties;
        var recorded = new RecordingMemberSeeds(seeds);
        var level = new LevelContext(algorithm, recorded, memos);
        var equationOf = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var i = 0; i < properties.Count; i++)
            equationOf[properties[i].Name] = i;

        // Equivalent completed consumers can have distinct origin keys but select the same local
        // declaration. Bridge only that proven selection to the existing live dependency equation;
        // never substitute a completed summary snapshot for a fixed-point read.
        var completed = memos.CompletedContext;
        for (var i = 0; i < baseSeeds.Length; i++)
        {
            var seed = baseSeeds[i];
            if (seed.PendingReferences.Count > 0)
            {
                var references = seed.PendingReferences.SelectMany(memos.SharedMemo.SelectedReferences).ToArray();
                if (!references.SequenceEqual(seed.PendingReferences))
                {
                    seed = seed.Clone();
                    seed.PendingReferences.Clear();
                    seed.PendingReferences.UnionWith(references);
                    baseSeeds[i] = seed;
                }
            }
            SummarySeed? bridged = null;
            HashSet<PendingReference>? selected = null;
            foreach (var reference in seed.PendingReferences)
            {
                if (!equationOf.ContainsKey(reference.Head) || !memos.SharedMemo.SelectsLocalMember(reference, completed)) continue;
                bridged ??= seed.Clone();
                (selected ??= []).Add(reference);
                bridged.VisiblePropertyDependencyNames.Add(reference.Head);
            }
            if (bridged is not null)
            {
                bridged.PendingReferences.Clear();
                bridged.PendingReferences.UnionWith(seed.PendingReferences.Where(reference => !selected!.Contains(reference)));
                baseSeeds[i] = bridged;
            }
        }

        // Statically read members: the local names a base seed reads directly or heads a path with.
        IEnumerable<int> StaticReads(int index)
        {
            var baseSeed = baseSeeds[index];
            foreach (var name in baseSeed.VisiblePropertyDependencyNames)
                if (equationOf.TryGetValue(name, out var read))
                    yield return read;
            foreach (var pending in baseSeed.PendingReferences)
                if (equationOf.TryGetValue(pending.Head, out var read))
                    yield return read;
        }

        // Evaluation units, dependency first. A strongly connected component whose every member has the
        // SHARE shape (TryShareMemberSeed) is a system of pure unions over exactly its static edges, so
        // its least fixed point gives every member the SAME seed: the members' own requirements,
        // qualified here, united with the seeds the component reads from outside. It is solved as ONE
        // unit (its first member stands for it) instead of propagating each member's requirements
        // around the cycle member by member.
        var components = DependencyFirstOrder.Components(properties.Count, i => equationOf[properties[i].Name] == i, StaticReads);
        var componentOf = new int[properties.Count];
        Array.Fill(componentOf, -1);
        var queue = new Queue<int>();
        var queued = new bool[properties.Count];
        for (var c = 0; c < components.Count; c++)
        {
            var component = components[c];
            if (component.Count > 1 && component.TrueForAll(member => HasShareShape(baseSeeds[member], equationOf)))
            {
                foreach (var member in component)
                    componentOf[member] = c;
                queue.Enqueue(component[0]);
                queued[component[0]] = true;
                continue;
            }

            foreach (var member in component)
            {
                queue.Enqueue(member);
                queued[member] = true;
            }
        }

        var readers = new Dictionary<string, HashSet<int>>(StringComparer.Ordinal);
        var contentKeys = new string?[properties.Count];
        Dictionary<string, (SummarySeed Result, (string Name, SummarySeed Read)[] Reads)>? expansions = null;
        while (queue.TryDequeue(out var index))
        {
            queued[index] = false;
            memos.Observations?.RecordSummaryMemberEvaluation();
            recorded.Reads.Clear();
            var component = componentOf[index];
            var next = component < 0 ? EvaluateMemberSeed(index) : EvaluateComponent(components[component], component);
            foreach (var readName in recorded.Reads)
            {
                if (!readers.TryGetValue(readName, out var nameReaders))
                    readers.Add(readName, nameReaders = []);
                nameReaders.Add(index);
            }

            // The members of one unit share their previous seed after the unit's first evaluation,
            // so one comparison decides them all.
            SummarySeed? comparedPrevious = null;
            var comparedSame = false;
            foreach (var member in component < 0 ? [index] : components[component])
            {
                var name = properties[member].Name;
                var previous = seeds[name];
                if (!ReferenceEquals(previous, comparedPrevious))
                {
                    comparedPrevious = previous;
                    comparedSame = SameContent(next, previous);
                }

                if (comparedSame)
                    continue;

                seeds[name] = next;
                if (!readers.TryGetValue(name, out var dependents))
                    continue;
                foreach (var dependent in dependents)
                {
                    memos.Observations?.RecordSummaryMemberReaderNotification();
                    if (!queued[dependent])
                    {
                        queued[dependent] = true;
                        queue.Enqueue(dependent);
                    }
                }
            }
        }

        // One share-shaped component's seed: its members' own requirements qualified here, united with
        // the non-empty seeds it reads from outside itself (held by reference when large).
        SummarySeed EvaluateComponent(List<int> members, int component)
        {
            var value = new SummarySeed(
                members.SelectMany(member => baseSeeds[member].RequiredAncestorOwnedParameterNames),
                ownerQualifiedParameters: members.SelectMany(member => baseSeeds[member].OwnerQualifiedParameters));
            value.QualifyParameters(level.Algorithm, level.ParameterNames, memos.Observations);
            foreach (var member in members)
            {
                foreach (var name in baseSeeds[member].VisiblePropertyDependencyNames)
                {
                    if (componentOf[equationOf[name]] == component)
                        continue;
                    recorded.Reads.Add(name);
                    if (!seeds[name].IsEmptyWithoutFolding())
                        value.AbsorbCompleted(seeds[name]);
                }
            }

            return value;
        }

        SummarySeed EvaluateMemberSeed(int index)
        {
            var baseSeed = baseSeeds[index];
            if (TryShareMemberSeed(baseSeed, recorded, level) is { } shared)
                return shared;

            var key = contentKeys[index] ??= baseSeed.ContentKeyFor(memos.Observations);
            expansions ??= new(StringComparer.Ordinal);
            if (expansions.TryGetValue(key, out var expansion)
                && expansion.Reads.All(read => ReferenceEquals(seeds[read.Name], read.Read)))
            {
                foreach (var (readName, _) in expansion.Reads)
                    recorded.Reads.Add(readName);
                return expansion.Result;
            }

            memos.Observations?.RecordSummaryMemberExpansion();
            var expanded = ExpandAtLevel(baseSeed, level);
            expansions[key] = (expanded, [.. recorded.Reads.Select(readName => (readName, seeds[readName]))]);
            return expanded;
        }
    }

    // The SHARE shape: a base seed with no path whose visible names are all members of the level. Its
    // expansion is exactly its own requirements, qualified at the level, united with those members' seeds.
    private static bool HasShareShape(SummarySeed baseSeed, Dictionary<string, int> members)
        => baseSeed.PendingReferences.Count == 0
            && baseSeed.VisiblePropertyDependencyNames.Count != 0
            && baseSeed.VisiblePropertyDependencyNames.All(members.ContainsKey);

    // The expansion of a share-shaped base seed, built by SHARING the members' seeds it reads (see
    // SolveMemberSeeds): content-empty member seeds contribute nothing, and the rest must be ONE seed.
    // Null when the base seed does not have that shape or reads several distinct non-empty seeds.
    private static SummarySeed? TryShareMemberSeed(SummarySeed baseSeed, RecordingMemberSeeds seeds, LevelContext level)
    {
        if (baseSeed.PendingReferences.Count != 0 || baseSeed.VisiblePropertyDependencyNames.Count == 0)
            return null;

        SummarySeed? shared = null;
        SummarySeed? empty = null;
        foreach (var name in baseSeed.VisiblePropertyDependencyNames)
        {
            if (!seeds.Seeds.TryGetValue(name, out var member))
                return null;
            if (member.IsEmptyWithoutFolding())
            {
                empty ??= member;
                continue;
            }

            if (shared is not null && !ReferenceEquals(shared, member))
                return null;
            shared = member;
        }

        foreach (var name in baseSeed.VisiblePropertyDependencyNames)
            seeds.Reads.Add(name);
        if (baseSeed.RequiredAncestorOwnedParameterNames.Count == 0 && baseSeed.OwnerQualifiedParameters.Count == 0)
            return shared ?? empty;

        // Own requirements, qualified here exactly as a full expansion qualifies them (the shared
        // member is already qualified at this level, and qualification distributes over union).
        var delta = new SummarySeed(
            baseSeed.RequiredAncestorOwnedParameterNames,
            ownerQualifiedParameters: baseSeed.OwnerQualifiedParameters);
        delta.QualifyParameters(level.Algorithm, level.ParameterNames, level.Memos.Observations);
        return shared is null ? delta : delta.AbsorbCompleted(shared);
    }

    // Exact content equality of a member's new and previous seed, without folding when structure decides.
    private static bool SameContent(SummarySeed next, SummarySeed previous)
    {
        if (ReferenceEquals(next, previous))
            return true;
        if (previous.IsEmptyWithoutFolding())
            return next.IsEmptyWithoutFolding();
        return next.StructurallyEquals(previous) || next.SetEquals(previous);
    }

    /// <summary>
    /// The member-seed map of a level whose fixed point is being solved, recording which members'
    /// seeds an expansion READ (a <see cref="TryGetValue"/> hit): the solver re-evaluates a member
    /// exactly when a seed it read has changed. Presence tests (<see cref="ContainsKey"/>) are
    /// structural — which members a level declares never changes — and record nothing.
    /// </summary>
    private sealed class RecordingMemberSeeds(Dictionary<string, SummarySeed> seeds) : IReadOnlyDictionary<string, SummarySeed>
    {
        public Dictionary<string, SummarySeed> Seeds { get; } = seeds;

        public HashSet<string> Reads { get; } = new(StringComparer.Ordinal);

        public bool TryGetValue(string key, [System.Diagnostics.CodeAnalysis.MaybeNullWhen(false)] out SummarySeed value)
        {
            if (!Seeds.TryGetValue(key, out value))
                return false;
            Reads.Add(key);
            return true;
        }

        public SummarySeed this[string key]
        {
            get
            {
                var value = Seeds[key];
                Reads.Add(key);
                return value;
            }
        }

        public bool ContainsKey(string key) => Seeds.ContainsKey(key);

        public IEnumerable<string> Keys => Seeds.Keys;

        public IEnumerable<SummarySeed> Values => throw new NotSupportedException("A member-seed view is read by name.");

        public int Count => Seeds.Count;

        public IEnumerator<KeyValuePair<string, SummarySeed>> GetEnumerator()
            => throw new NotSupportedException("A member-seed view is read by name.");

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    private static HashSet<string> CreateNameSet(IEnumerable<string>? names = null)
        => names is null
            ? new HashSet<string>(StringComparer.Ordinal)
            : new HashSet<string>(names, StringComparer.Ordinal);
}
