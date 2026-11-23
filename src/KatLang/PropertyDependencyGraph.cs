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
    IReadOnlyList<(string Key, PendingReference Reference)> ReferenceInputs,
    IReadOnlyList<OwnerQualifiedParameter> OwnerQualifiedParameters)
{
    public IEnumerable<PendingReference> PendingReferences => ReferenceInputs.Select(static input => input.Reference);
}

/// <summary>
/// A member path in a summary seed. A raw path contains only its spelling and can be shared by argument
/// bundles across owner contexts. A <see cref="PendingReference"/> has already been anchored by its writer.
/// Equality compares the length-prefixed resolution key and the exact bound owners for the member fixed point.
/// </summary>
internal class SummaryReference : IEquatable<SummaryReference>
{
    internal SummaryReference(string head, IReadOnlyList<string> members, IReadOnlyList<Algorithm>? boundOwners = null)
        : this(head, members, boundOwners, string.Empty) { }

    private protected SummaryReference(string head, IReadOnlyList<string> members, IReadOnlyList<Algorithm>? boundOwners,
        string originKey)
    {
        Head = head;
        Members = members;
        BoundOwners = boundOwners ?? [];
        ResolutionKey = KeyParts([originKey, head, KeyParts(members)]);
        var boundKey = string.Join(",", BoundOwners.Select(OwnerQualifiedParameter.OwnerKey).Order());
        ContentKey = KeyParts([ResolutionKey, boundKey]);
    }

    public string Head { get; }
    public IReadOnlyList<string> Members { get; }
    public IReadOnlyList<Algorithm> BoundOwners { get; }
    internal string ContentKey { get; }
    internal string ResolutionKey { get; }

    // The level visited inputs in ordinal order of the decimal length prefix, including its colon.
    // That length included two characters for the former field. Preserve the traversal at digit
    // boundaries (e.g. 98 used to sort as "100:") without putting that field in any key.
    internal string LevelOrderPrefix => $"{ResolutionKey.Length + 2}:";

    internal PendingReference At(CompletedStructureContext origin)
        => this as PendingReference ?? new PendingReference(Head, Members, origin, BoundOwners);

    // The observation counts key characters with each process-wide id replaced by one character.
    private protected virtual string IdFreeOriginKey => string.Empty;
    internal string IdFreeContentKey => KeyParts([
        KeyParts([IdFreeOriginKey, Head, KeyParts(Members)]),
        string.Join(",", BoundOwners.Select(static _ => "#"))]);

    /// <summary>
    /// The decimal width of the widest PROCESS-WIDE id a key can hold (<see cref="long.MaxValue"/> has 19 digits): an
    /// owner's <see cref="OwnerQualifiedParameter.OwnerKey"/> and a completed origin's requirement identity are positive
    /// <see cref="long"/> counters, which grow with every id the process has issued, whatever the program.
    /// </summary>
    internal const int StableIdWidth = 19;

    /// <summary>
    /// The length <see cref="ContentKey"/> has with every process-wide id in it written at <see cref="StableIdWidth"/>
    /// digits, from the reference's structure alone: the same in every process, however many ids were issued before,
    /// and never shorter than the key itself (the settlement share's admission weight,
    /// <c>PropertyExposureResolver.SettlementShare.Key</c>). Builds no text.
    /// </summary>
    internal long StableContentKeyLength
    {
        get
        {
            long members = 0;
            foreach (var member in Members)
                members += PartLength(member.Length);
            var resolution = PartLength(StableOriginKeyLength) + PartLength(Head.Length) + PartLength(members);
            return PartLength(resolution) + PartLength(StableBoundOwnersKeyLength(BoundOwners.Count));
        }
    }

    /// <summary>The length of the comma-separated ids of <paramref name="owners"/> owners, each at <see cref="StableIdWidth"/> digits.</summary>
    internal static long StableBoundOwnersKeyLength(int owners) => owners == 0 ? 0 : (long)owners * (StableIdWidth + 1) - 1;

    // The origin part's length with its id at StableIdWidth digits (none here).
    private protected virtual int StableOriginKeyLength => 0;

    // The length KeyParts gives one part of `length` characters: its decimal length, a colon, the part.
    private static long PartLength(long length)
    {
        var digits = 1;
        for (var rest = length; rest >= 10; rest /= 10)
            digits++;
        return digits + 1 + length;
    }

    internal static string KeyParts(IEnumerable<string> parts)
        => string.Concat(parts.Select(static part => $"{part.Length}:{part}"));

    internal virtual SummaryReference WithBoundOwners(IReadOnlyList<Algorithm> owners) => new(Head, Members, owners);

    public SummaryReference BoundBy(Algorithm owner)
        => BoundOwners.Any(a => ReferenceEquals(a, owner)) ? this : WithBoundOwners([.. BoundOwners, owner]);

    public bool Equals(SummaryReference? other) => other is not null && ContentKey == other.ContentKey;
    public override bool Equals(object? obj) => Equals(obj as SummaryReference);
    public override int GetHashCode() => ContentKey.GetHashCode(StringComparison.Ordinal);
}

/// <summary>
/// A requirement of the completed context that wrote it. Settlement resolves its head by the owning level's
/// lexical lookup and open-provider rules and charges the selected members. Every graph input and every
/// reference in an expanded seed has this form.
/// </summary>
internal sealed class PendingReference(string head, IReadOnlyList<string> members, CompletedStructureContext origin,
    IReadOnlyList<Algorithm>? boundOwners = null, bool openPath = false, PendingSelection selection = PendingSelection.Lexical)
    : SummaryReference(head, members, boundOwners, OriginKey(origin.Identity.ToString(), openPath, selection))
{
    internal CompletedStructureContext Origin { get; } = origin;
    internal bool OpenPath { get; } = openPath;
    internal PendingSelection Selection { get; } = selection;

    private static string OriginKey(string identity, bool openPath, PendingSelection selection)
        => selection == PendingSelection.Lexical ? $"completed:{identity}:{openPath}" : $"completed:{identity}:{openPath}:{selection}";

    private protected override string IdFreeOriginKey => OriginKey("#", OpenPath, Selection);

    // OriginKey's length with the identity at StableIdWidth digits, per open-path flag and selection (values 0, 1, …):
    // rendered once, by OriginKey itself, so it follows the key's own layout.
    private static readonly int Selections = Enum.GetValues<PendingSelection>().Length;
    private static readonly int[] StableOriginKeyLengths =
        [.. from openPath in new[] { false, true }
            from selection in Enum.GetValues<PendingSelection>()
            select OriginKey(new string('0', StableIdWidth), openPath, selection).Length];

    private protected override int StableOriginKeyLength => StableOriginKeyLengths[(OpenPath ? Selections : 0) + (int)Selection];

    internal override SummaryReference WithBoundOwners(IReadOnlyList<Algorithm> owners)
        => new PendingReference(Head, Members, Origin, owners, OpenPath, Selection);
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
/// (<see cref="SummaryReference.ResolutionKey"/>), and a reference's own content never changes: it
/// carries no provider and nothing a provider charges, so nothing in it is derived from summaries
/// that grow during a fixed point. An entry changes only by losing bound owners, a summary
/// therefore only grows with the summaries it reads, and the member fixed point terminates around
/// a cycle of mutually opening libraries.</para>
/// </summary>
internal sealed class PendingReferenceSet : IReadOnlyCollection<SummaryReference>
{
    private readonly Dictionary<string, SummaryReference> _references = new(StringComparer.Ordinal);

    public PendingReferenceSet() { }
    public PendingReferenceSet(IEnumerable<SummaryReference> references) => UnionWith(references);
    public int Count => _references.Count;
    public void Clear() => _references.Clear();

    public void Add(SummaryReference reference)
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
        _references[existing.ResolutionKey] = existing.WithBoundOwners(common);
    }

    public void UnionWith(IEnumerable<SummaryReference> references)
    {
        foreach (var reference in references) Add(reference);
    }
    public bool SetEquals(PendingReferenceSet other)
        => Count == other.Count && _references.All(pair => other._references.TryGetValue(pair.Key, out var value) && pair.Value.Equals(value));
    public IEnumerator<SummaryReference> GetEnumerator() => _references.Values.GetEnumerator();
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
            IEnumerable<SummaryReference>? pendingReferences = null,
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
        ///
        /// <para>A part of required names that <paramref name="owned"/> covers only IN PART — an
        /// owner whose names meet the shared bundle's, such as a forwarding owner that reuses an
        /// enclosing binding of one of them (Q-04) — contributes exactly the names outside the set to
        /// the result, so it is replaced by those names (its RESIDUAL, read once per (part, owned set),
        /// <see cref="SummaryMemo.PartlyOwnedResidual"/>): the owner's summary then carries its real
        /// collisions as names, qualified at the levels that own them like any name, instead of
        /// folding, qualifying and stripping the bundle's whole width once per owner.</para>
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

                if (memo.PartlyOwnedResidual(part, owned) is { } residual)
                {
                    kept ??= absorbed.GetRange(0, i);
                    var required = _requiredAncestorOwnedParameterNames ??= CreateNameSet();
                    foreach (var name in residual)
                        required.Add(name);
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

        /// <summary>
        /// Re-anchor a completed seed, preserving its absorbed parts, order and sharing. An unchanged seed is its
        /// own copy. During staging, discover the anchors bottom-up. On adoption, skip unchanged subgraphs through
        /// the index built when the entry was staged.
        /// </summary>
        internal SummarySeed Reanchored(Func<PendingReference, PendingReference> reanchor,
            Dictionary<SummarySeed, SummarySeed> copies, IReadOnlySet<SummarySeed>? anchoredSeeds,
            CancellationToken cancellationToken)
        {
            cancellationToken.ThrowIfCancellationRequested();
            if (anchoredSeeds is not null && !anchoredSeeds.Contains(this))
                return this;
            if (copies.TryGetValue(this, out var cached))
                return cached;

            var pending = new Stack<(SummarySeed Seed, bool PartsDone)>();
            pending.Push((this, false));
            while (pending.TryPop(out var frame))
            {
                cancellationToken.ThrowIfCancellationRequested();
                var (seed, partsDone) = frame;
                if (copies.ContainsKey(seed) || anchoredSeeds is not null && !anchoredSeeds.Contains(seed))
                    continue;

                if (!partsDone && seed._absorbed is { Count: > 0 } parts)
                {
                    pending.Push((seed, true));
                    for (var i = parts.Count - 1; i >= 0; i--)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        pending.Push((parts[i], false));
                    }
                    continue;
                }

                // Complete each child before visiting the next sibling. Looking up a shared child then costs one
                // dictionary read even when its parents are themselves shared.
                if (anchoredSeeds is null && !NeedsCopy(seed))
                {
                    copies.Add(seed, seed);
                    continue;
                }

                var copy = new SummarySeed(seed._requiredAncestorOwnedParameterNames, seed._visiblePropertyDependencyNames,
                    ownerQualifiedParameters: seed._ownerQualifiedParameters);
                if (seed._pendingReferences is { Count: > 0 } references)
                {
                    var anchored = copy._pendingReferences = new PendingReferenceSet();
                    foreach (var reference in references)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        anchored.Add(reference is PendingReference item ? reanchor(item) : reference);
                    }
                }
                if (seed._absorbed is { } children)
                {
                    foreach (var child in children)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        copy.AbsorbReference(copies.GetValueOrDefault(child, child));
                    }
                }
                copies.Add(seed, copy);
            }
            return copies[this];

            bool NeedsCopy(SummarySeed seed)
            {
                if (seed._pendingReferences is { } references)
                    foreach (var reference in references)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        if (reference is PendingReference) return true;
                    }
                if (seed._absorbed is { } children)
                    foreach (var child in children)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        if (!ReferenceEquals(copies[child], child)) return true;
                    }
                return false;
            }
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

            var bound = new List<SummaryReference>(pendingReferences.Count);
            foreach (var pending in pendingReferences)
                bound.Add(pending.BoundBy(owner));
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

        /// <summary>
        /// The content as canonical text (sorted, length-prefixed): equal exactly when <see cref="ContentEquals"/> is.
        /// Only a test oracle and the shape of what <see cref="RecordKeyCharacters"/> measures: the member solver
        /// compares contents directly (<see cref="ContentHash"/>, <see cref="ContentEquals"/>) and builds no text.
        /// </summary>
        internal string ContentKey
            // Reads the folded sets directly: most seeds are empty, and a key must not materialize what it describes.
            => IsEmpty ? EmptyContentKey : SummaryReference.KeyParts([
                _requiredAncestorOwnedParameterNames is { } required ? FrontEndRegionKeys.NameSet(required) : string.Empty,
                _visiblePropertyDependencyNames is { } visible ? FrontEndRegionKeys.NameSet(visible) : string.Empty,
                _pendingReferences is { } pending ? FrontEndRegionKeys.NameSet(pending.Select(static reference => reference.ContentKey)) : string.Empty,
                _ownerQualifiedParameters is { } qualified ? FrontEndRegionKeys.NameSet(qualified.Select(static r => r.ContentKey)) : string.Empty]);

        /// <summary>
        /// <see cref="ContentKey"/> with every process-wide id written as <c>#</c>
        /// (<see cref="SummaryReference.IdFreeContentKey"/>, <see cref="OwnerQualifiedParameter.IdFreeContentKey"/>):
        /// the text <see cref="FrontEndTraversalObservations.SummaryKeyCharacters"/> counts. Built only for an observer.
        /// </summary>
        private string IdFreeContentKey()
            => SummaryReference.KeyParts([
                _requiredAncestorOwnedParameterNames is { } required ? FrontEndRegionKeys.NameSet(required) : string.Empty,
                _visiblePropertyDependencyNames is { } visible ? FrontEndRegionKeys.NameSet(visible) : string.Empty,
                _pendingReferences is { } pending ? FrontEndRegionKeys.NameSet(pending.Select(static reference => reference.IdFreeContentKey)) : string.Empty,
                _ownerQualifiedParameters is { } qualified ? FrontEndRegionKeys.NameSet(qualified.Select(static r => r.IdFreeContentKey)) : string.Empty]);

        private static readonly string EmptyContentKey = SummaryReference.KeyParts([string.Empty, string.Empty, string.Empty, string.Empty]);

        /// <summary>
        /// Records, for an observer, the id-free length of this seed's content text — the size of the content the member
        /// solver compares (<see cref="FrontEndTraversalObservations.SummaryKeyCharacters"/>); builds nothing without one.
        /// </summary>
        internal void RecordKeyCharacters(FrontEndTraversalObservations? observations)
        {
            if (observations is null)
                return;
            observations.RecordSummaryKeyCharacters((IsEmpty ? EmptyContentKey : IdFreeContentKey()).Length);
        }

        /// <summary>
        /// An order-independent hash of the folded content: equal content (<see cref="ContentEquals"/>), equal hash. Each
        /// set contributes its count and the sum and the mixed XOR of its elements' hashes under the set's own equality
        /// (a reference by its content key, a qualified parameter by name and owner); it builds no text.
        /// </summary>
        internal int ContentHash()
        {
            Fold();
            return HashCode.Combine(SetHash(_requiredAncestorOwnedParameterNames), SetHash(_visiblePropertyDependencyNames),
                PendingHash(_pendingReferences), SetHash(_ownerQualifiedParameters));

            static int SetHash<T>(HashSet<T>? set)
            {
                if (set is null || set.Count == 0)
                    return 0;
                var (sum, xor) = (0, 0);
                foreach (var item in set)
                {
                    var hash = set.Comparer.GetHashCode(item!);
                    sum = unchecked(sum + hash);
                    xor ^= unchecked(hash * -1640531535);
                }
                return HashCode.Combine(set.Count, sum, xor);
            }

            static int PendingHash(PendingReferenceSet? set)
            {
                if (set is null || set.Count == 0)
                    return 0;
                var (sum, xor) = (0, 0);
                foreach (var reference in set)
                {
                    var hash = reference.GetHashCode();
                    sum = unchecked(sum + hash);
                    xor ^= unchecked(hash * -1640531535);
                }
                return HashCode.Combine(set.Count, sum, xor);
            }
        }

        /// <summary>
        /// Equal folded content: the same four sets (<see cref="StructurallyEquals"/> once nothing is absorbed) — required
        /// names, visible names, pending references by content key, owner-qualified parameters by name and owner. Two seeds
        /// are content-equal exactly when their <see cref="ContentKey"/>s are equal.
        /// </summary>
        internal bool ContentEquals(SummarySeed other)
        {
            Fold();
            other.Fold();
            return StructurallyEquals(other);
        }
    }

    /// <summary>
    /// The completed summary of one algorithm node under the empty locally-owned context: the
    /// requirements of its OUTPUT (what evaluating the algorithm's value needs) and, per
    /// declared property, that member's requirements expanded through the algorithm's own
    /// sibling fixed point (relative to the algorithm's declaring level). The member seeds are
    /// what structural navigation (<c>Inner.X</c>) and <c>open</c>-provided names charge.
    /// Both are stored pristine; readers clone before accumulating.
    /// </summary>
    internal sealed class AlgorithmSummary
    {
        private SummarySeed? _outputSeed;
        private Func<SummarySeed>? _outputSeedSource;

        public AlgorithmSummary(SummarySeed outputSeed, IReadOnlyDictionary<string, SummarySeed> memberSeeds)
        {
            _outputSeed = outputSeed;
            MemberSeeds = memberSeeds;
        }

        /// <summary>
        /// A summary ADOPTED from <see cref="CompletedProviderSummaries"/>: its output seed is produced when first read
        /// and its member seeds one by one (<see cref="ReanchoredMemberSeeds"/>), so adopting a W-member provider to
        /// read one member costs that member's seed, never the provider's width.
        /// </summary>
        internal AlgorithmSummary(Func<SummarySeed> outputSeed, IReadOnlyDictionary<string, SummarySeed> memberSeeds)
        {
            _outputSeedSource = outputSeed;
            MemberSeeds = memberSeeds;
        }

        public SummarySeed OutputSeed
        {
            get
            {
                if (_outputSeed is { } seed)
                    return seed;
                seed = _outputSeedSource!();
                _outputSeed = seed;
                _outputSeedSource = null;
                return seed;
            }
        }

        public IReadOnlyDictionary<string, SummarySeed> MemberSeeds { get; }

        public static readonly IReadOnlyDictionary<string, SummarySeed> NoMembers =
            new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
    }

    /// <summary>
    /// The member seeds of an adopted summary (<see cref="CompletedProviderSummaries"/>): each stored seed re-anchored at
    /// the adopting resolution's contexts when it is first read (<see cref="SummarySeed.Reanchored"/>), and never
    /// before. Names, count and enumeration order are the stored map's.
    /// </summary>
    private sealed class ReanchoredMemberSeeds(IReadOnlyDictionary<string, SummarySeed> stored,
        Func<SummarySeed, SummarySeed> reanchored) : IReadOnlyDictionary<string, SummarySeed>
    {
        public int Count => stored.Count;
        public IEnumerable<string> Keys => stored.Keys;
        public IEnumerable<SummarySeed> Values => stored.Values.Select(reanchored);
        public SummarySeed this[string key] => reanchored(stored[key]);
        public bool ContainsKey(string key) => stored.ContainsKey(key);

        public bool TryGetValue(string key, [System.Diagnostics.CodeAnalysis.MaybeNullWhen(false)] out SummarySeed value)
        {
            if (stored.TryGetValue(key, out var seed))
            {
                value = reanchored(seed);
                return true;
            }

            value = null;
            return false;
        }

        public IEnumerator<KeyValuePair<string, SummarySeed>> GetEnumerator()
        {
            foreach (var (name, seed) in stored)
                yield return new(name, reanchored(seed));
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
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
        /// <summary>
        /// The source-processing token of the exposure resolution this memo spans (none for a standalone
        /// <see cref="BuildSummaries"/> call), observed when a level expansion starts and before each name it carries
        /// outward (<see cref="ExpandAtLevel"/>).
        /// </summary>
        internal CancellationToken CancellationToken { get; init; }

        internal void ObserveCancellation()
            => FrontEndTraversalObservations.ObserveCancellation(
                observations, FrontEndCancellationCheckpoint.SummaryChannel, CancellationToken);

        // ── Completed provider summaries (CompletedProviderSummaries) ──

        /// <summary>
        /// The materialization attempt's view of its loader's completed provider summaries; null in every resolution
        /// that is not a deferred branch's materialization (the eager parse, a standalone analysis, the semantic model),
        /// which then computes every summary itself, exactly as before the share existed.
        /// </summary>
        internal CompletedProviderSummaries.Attempt? CompletedProviders { get; init; }

        /// <summary>The unsealed unit this resolution completes (a materialization's own facts); null without one.</summary>
        internal CompletedStaticStructures? CompletingUnit { get; init; }

        /// <summary>The facts a context's lookups read: the table itself, or the one a requirement view projects.</summary>
        internal static StaticLookupFacts SourceOf(StaticLookupFacts facts)
            => facts is RequirementLookupFacts projected ? projected.Source : facts;

        /// <summary>
        /// TEST SEAM (<see cref="CompletedProviderSummaries.ModeForTesting"/>): every adopted summary is also computed by
        /// this resolution and compared with what it adopted. Never set by production code.
        /// </summary>
        internal bool VerifiesAdoptedProviders { get; init; }

        // The exact-context computation in progress that may be kept (its facts and key), how many of the share's
        // conditions it has broken so far, the contextual results computed since it began, and the contextual results of
        // every earlier window of this resolution that kept all of them (each was computed under the share's conditions,
        // so a later window may read it).
        private (CompletedStaticStructures Source, StaticScopeKey Key)? _providerWindow;
        private long _providerWindowTaints;
        private HashSet<object>? _providerWindowResults;
        private HashSet<object>? _keptWindowResults;

        /// <summary>
        /// The share key of an exact-context request for <paramref name="algorithm"/> at <paramref name="context"/>, or
        /// null when its summary cannot be kept or adopted: no share (not a materialization), facts that are neither a
        /// sealed table nor this resolution's own unit, or a context that is not completed inherited content
        /// (<see cref="CompletedStaticStructures.HoldsInheritedCompletedBody"/>).
        /// </summary>
        internal CompletedProviderSummaries.Key? CompletedProviderKey(CompletedStructureContext context, Algorithm algorithm)
        {
            if (CompletedProviders is null || CompletingUnit is not { } unit
                || SourceOf(context.Facts) is not CompletedStaticStructures source)
                return null;
            var own = ReferenceEquals(source, unit);
            if (!own && !source.IsSealed || !source.HoldsInheritedCompletedBody(context.Key, algorithm))
                return null;
            return new(own ? null : source, context.Key);
        }

        /// <summary>
        /// The summary an earlier operation kept for <paramref name="provider"/>, re-anchored at this resolution's
        /// contexts seed by seed, as each one is read (see <see cref="CompletedProviderSummaries"/>).
        /// </summary>
        internal bool TryAdoptCompletedProvider(CompletedProviderSummaries.Key provider,
            [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out AlgorithmSummary? adopted, out bool independent)
        {
            adopted = null;
            independent = false;
            if (CompletedProviders is not { } share || !share.TryGet(provider, out var entry))
                return false;

            observations?.RecordCompletedProviderSummaryAdoption();
            independent = entry.Independent;
            var copies = new Dictionary<SummarySeed, SummarySeed>(ReferenceEqualityComparer.Instance);
            Func<PendingReference, PendingReference> reanchor = pending =>
            {
                observations?.RecordCompletedProviderReferenceReanchor();
                var source = SourceOf(pending.Origin.Facts);
                // The computing unit's own table stands for "the asking unit": this resolution's. Every other origin
                // names a sealed table, which is the same object for every operation that inherits it.
                if (ReferenceEquals(source, entry.ComputedBy))
                    source = CompletingUnit!;
                return new PendingReference(pending.Head, pending.Members,
                    RequirementContext(source.Context(pending.Origin.Key))!, pending.BoundOwners, pending.OpenPath, pending.Selection);
            };
            Func<SummarySeed, SummarySeed> reanchored = seed => seed.Reanchored(reanchor, copies, entry.AnchoredSeeds, CancellationToken);
            var stored = entry.Summary;
            adopted = new AlgorithmSummary(() => reanchored(stored.OutputSeed),
                stored.MemberSeeds.Count == 0 ? AlgorithmSummary.NoMembers : new ReanchoredMemberSeeds(stored.MemberSeeds, reanchored));
            return true;
        }

        /// <summary>
        /// Opens the window of an exact-context computation that may be kept; <see cref="CloseProviderWindow"/> ends it.
        /// Exact-context requests come from the exposure resolver's charging calls, never from inside a summary walk, so
        /// a window never nests.
        /// </summary>
        internal void OpenProviderWindow(CompletedProviderSummaries.Key provider)
        {
            if (_providerWindow is not null)
                throw new InvalidOperationException("Internal error: an exact-context summary request was made inside another one.");
            _providerWindow = (provider.Sealed ?? CompletingUnit!, provider.Scope);
            _providerWindowTaints = 0;
            _providerWindowResults?.Clear();
        }

        /// <summary>Ends the window; true when the computation kept every condition of the share.</summary>
        internal bool CloseProviderWindow()
        {
            _providerWindow = null;
            var kept = _providerWindowTaints == 0;
            if (kept && _providerWindowResults is { Count: > 0 } results)
                (_keptWindowResults ??= new(ReferenceEqualityComparer.Instance)).UnionWith(results);
            _providerWindowResults?.Clear();
            return kept;
        }

        // A contextual result computed inside the window: a later hit of it, in this window or after a window that kept
        // every condition, was computed under the share's conditions.
        internal void NoteProviderWindowResult(object result)
        {
            if (_providerWindow is not null)
                (_providerWindowResults ??= new(ReferenceEqualityComparer.Instance)).Add(result);
        }

        // A summary this resolution adopted or kept: it is a summary of completed content computed under the share's
        // conditions, so a later window that reads it from the memo stays within them.
        internal void NoteKeptProviderResult(object result)
            => (_keptWindowResults ??= new(ReferenceEqualityComparer.Instance)).Add(result);

        // A contextual memo hit inside the window: an entry computed outside every such window was computed under
        // conditions nobody recorded, so the window's summary is not kept.
        internal void NoteProviderWindowReuse(object result)
        {
            if (_providerWindow is not null && _providerWindowResults?.Contains(result) != true
                && _keptWindowResults?.Contains(result) != true)
                _providerWindowTaints++;
        }

        /// <summary>
        /// TEST SEAM (<see cref="VerifiesAdoptedProviders"/>): whether <paramref name="adopted"/> is, seed by seed, the
        /// summary this resolution computed itself: the same member names; in every seed the same required names,
        /// visible names and owner-qualified parameters; and the same references in the same order, each anchored one at
        /// the same facts object and key with the same path, bound owners and selection. Returns the first difference.
        /// </summary>
        internal static string? AdoptedSummaryDifference(AlgorithmSummary adopted, AlgorithmSummary computed)
        {
            if (SeedDifference(adopted.OutputSeed, computed.OutputSeed) is { } output)
                return "output seed: " + output;
            if (adopted.MemberSeeds.Count != computed.MemberSeeds.Count)
                return $"member count {adopted.MemberSeeds.Count} / {computed.MemberSeeds.Count}";
            foreach (var (name, seed) in computed.MemberSeeds)
            {
                if (!adopted.MemberSeeds.TryGetValue(name, out var other))
                    return $"member '{name}' missing";
                if (SeedDifference(other, seed) is { } member)
                    return $"member '{name}': {member}";
            }

            return null;

            static string? SeedDifference(SummarySeed left, SummarySeed right)
            {
                // Clones fold their own copies: the compared seeds are never mutated.
                left = left.Clone();
                right = right.Clone();
                if (!left.RequiredAncestorOwnedParameterNames.SetEquals(right.RequiredAncestorOwnedParameterNames))
                    return "required names";
                if (!left.VisiblePropertyDependencyNames.SetEquals(right.VisiblePropertyDependencyNames))
                    return "visible names";
                if (!left.OwnerQualifiedParameters.SetEquals(right.OwnerQualifiedParameters))
                    return "owner-qualified parameters";
                var (leftReferences, rightReferences) = (left.PendingReferences.ToArray(), right.PendingReferences.ToArray());
                if (leftReferences.Length != rightReferences.Length)
                    return $"reference count {leftReferences.Length} / {rightReferences.Length}";
                for (var i = 0; i < leftReferences.Length; i++)
                {
                    var (a, b) = (leftReferences[i], rightReferences[i]);
                    if (a.ContentKey != b.ContentKey)
                        return $"reference {i} content";
                    var (anchoredLeft, anchoredRight) = (a as PendingReference, b as PendingReference);
                    if (anchoredLeft is null != anchoredRight is null)
                        return $"reference {i} anchoring";
                    if (anchoredLeft is not null && anchoredRight is not null
                        && (!ReferenceEquals(anchoredLeft.Origin.Facts, anchoredRight.Origin.Facts)
                            || !ReferenceEquals(anchoredLeft.Origin.Key, anchoredRight.Origin.Key)
                            || anchoredLeft.OpenPath != anchoredRight.OpenPath || anchoredLeft.Selection != anchoredRight.Selection))
                        return $"reference {i} origin";
                }

                return null;
            }
        }

        // The walk enters `body` at `context` inside the window: its facts must be sealed (or the window's own
        // context), hold exactly this body and not be provisional.
        private void NoteProviderWindowBody(CompletedStructureContext context, Algorithm body)
        {
            if (_providerWindow is not { } window)
                return;
            // A synthetic deconstruction helper has no published context of its own, and its summary is the constant
            // empty one, returned before anything is read (CollectScopeBodySummary).
            if (body is Algorithm.User { AssignmentDeconstructionTarget: not null })
                return;
            if (SourceOf(context.Facts) is not CompletedStaticStructures source
                || !source.IsSealed && !(ReferenceEquals(source, window.Source) && ReferenceEquals(context.Key, window.Key))
                || source.Facts(context.Key) is not { Body: { } view, IsProvisional: false }
                || !ReferenceEquals(view, body))
                _providerWindowTaints++;
        }

        /// <summary>
        /// The form in which <paramref name="summary"/> is kept for later operations: every anchored reference at the
        /// TABLE its origin reads (a sealed one, or <paramref name="unit"/>, the computing unit's own, which seals when
        /// its attempt publishes, the only time the summary becomes visible), never at this resolution's requirement
        /// view of it. A view is the memo's own object, with the provisional bodies its walks registered: kept seeds
        /// would retain it, and with it this attempt's context. Seeds that carry no anchored reference are kept as they
        /// are. Null when an origin reads facts that are neither a sealed table nor the unit: the summary is not kept.
        /// </summary>
        internal CompletedProviderSummaries.Entry? StoredForm(AlgorithmSummary summary, bool independent, CompletedStaticStructures unit)
        {
            var completed = true;
            var copies = new Dictionary<SummarySeed, SummarySeed>(ReferenceEqualityComparer.Instance);
            Func<PendingReference, PendingReference> atTable = reference =>
            {
                var facts = reference.Origin.Facts;
                if (SourceOf(facts) is not CompletedStaticStructures table || !table.IsSealed && !ReferenceEquals(table, unit))
                {
                    completed = false;
                    return reference;
                }

                return ReferenceEquals(table, facts) ? reference
                    : new PendingReference(reference.Head, reference.Members, table.Context(reference.Origin.Key),
                        reference.BoundOwners, reference.OpenPath, reference.Selection);
            };
            var output = summary.OutputSeed.Reanchored(atTable, copies, null, CancellationToken);
            var members = AlgorithmSummary.NoMembers;
            if (summary.MemberSeeds.Count != 0)
            {
                var stored = new Dictionary<string, SummarySeed>(summary.MemberSeeds.Count, StringComparer.Ordinal);
                foreach (var (name, seed) in summary.MemberSeeds)
                    stored.Add(name, seed.Reanchored(atTable, copies, null, CancellationToken));
                members = stored;
            }

            if (!completed) return null;
            var anchored = new HashSet<SummarySeed>(ReferenceEqualityComparer.Instance);
            foreach (var (original, stored) in copies)
            {
                CancellationToken.ThrowIfCancellationRequested();
                if (!ReferenceEquals(original, stored)) anchored.Add(stored);
            }
            return new(new AlgorithmSummary(output, members), independent, unit, anchored);
        }

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
            // The representative depends on which contexts this resolution's input reached first: never kept.
            if (_providerWindow is not null) _providerWindowTaints++;
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
        // In open-target recovery a block contributes no requirements. Even a context-independent
        // bundle computed there can differ from that bundle's seed in an ordinary row.
        internal Dictionary<OutputBundle, SummarySeed>? OpenTargetArgumentBundles;
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
                // Another context of the same body under the same parent (a body several branches share): which of them
                // stands for the region depends on the order this resolution met them, so the window's summary is not kept.
                if (_providerWindow is not null && !ReferenceEquals(previous.Key, at.Key)) _providerWindowTaints++;
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
            if (body is not null) NoteProviderWindowBody(at, body);
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
        internal IEnumerable<SummaryReference> SelectedReferences(SummaryReference reference)
        {
            if (reference is not PendingReference pending) return [reference];
            UseContext();
            var origin = pending.Origin;
            if (pending.OpenPath || pending.Selection != PendingSelection.Lexical
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
            PendingReference rebound = new(reference.Head, reference.Members, selected, reference.BoundOwners);
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
            => new(string.Empty, [], opening, boundOwners, openPath: true, PendingSelection.OpenWalks);

        // Project a completed Q1 owner selection onto THIS live Q8 equation map. Context-bearing
        // paths, open choices and bound-owner exclusions keep their full symbolic representation.
        internal bool SelectsLocalMember(SummaryReference reference, CompletedStructureContext level)
        {
            if (reference is not PendingReference pending) return false;
            UseContext();
            var origin = pending.Origin;
            if (pending.OpenPath || pending.Selection != PendingSelection.Lexical || pending.Members.Count != 0 || pending.BoundOwners.Count != 0
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

        /// <summary>
        /// FE-3: when a COMPLETED part carries only required names and an owner's TEMPLATE name set covers it only in part,
        /// the names the set leaves uncovered — the owner's real collisions with the part, which survive the owner's strip —
        /// in walk order; null otherwise (anything but required names, every name covered, or a name set that is not a shared
        /// signature template's). A flat template's answer is read once per (part, template set) for every owner of the
        /// template; a composed one's is its shared tail's residual, tested against the owner's head, like
        /// <see cref="IsOwnedPureRequirement"/>. An owner whose set is its own keeps folding the part, so nothing per owner
        /// is retained here.
        /// </summary>
        internal string[]? PartlyOwnedResidual(SummarySeed part, IReadOnlySet<string> owned)
        {
            if (owned is not ImplicitSignatureTemplate.NameSetView template)
                return null;
            if (template.Tail is not { } tail)
                return ResidualOf(part, owned) is { Length: > 0 } residual ? residual : null;
            if (ResidualOf(part, tail) is not { } tailResidual)
                return null;
            List<string>? outside = null;
            foreach (var name in tailResidual)
            {
                observations?.RecordSummaryResidualNameProbe();
                if (!owned.Contains(name))
                    (outside ??= []).Add(name);
            }

            return outside is null ? null : [.. outside];
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
        CompletedStructureContext completedContext, bool openTargetRegion = false)
    {
        public readonly CompletedStructureContext CompletedContext = completedContext;

        /// <summary>
        /// This region walks the open targets of its level that are neither name paths nor inline-headed
        /// (<see cref="CollectOpenTargetSeeds"/>). An algorithm written in such a target is declared at the prelude, not in
        /// <see cref="CompletedContext"/>, so the walk neither summarizes it nor navigates a path from it: it charges
        /// nothing.
        /// </summary>
        public readonly bool OpenTargetRegion = openTargetRegion;
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
                // A raw hoisted path and a nested reference rebound to this level can resolve identically.
                // The equation still visits each distinct input, in input-key order, before the settlement
                // share sees their common anchored key. This preserves the level's cancellation checkpoints.
                summarySeed.PendingReferences.SelectMany(buildMemos.SharedMemo.SelectedReferences)
                    .Distinct().OrderBy(static input => input.LevelOrderPrefix, StringComparer.Ordinal)
                    .ThenBy(static input => input.ContentKey, StringComparer.Ordinal)
                    .Select(input => (input.ContentKey, input.At(completedContext))).ToArray(),
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
    /// RAW with that level's memos, so the paths they write are anchored where the level expands
    /// them (a nested level's member fixed point) or where its summary graph is built
    /// (<see cref="BuildSummaries"/>), and the bare names they write stay names: the level solver
    /// settles one on the chain first and otherwise as a reference anchored at the level.
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
            memos.SharedMemo.NoteProviderWindowReuse(result);
            return result;
        }

        // COMPLETED PROVIDER SUMMARIES: an exact-context request of a deferred materialization for completed inherited
        // content takes the summary an earlier operation of the program kept, and keeps the one it computes itself
        // (CompletedProviderSummaries). Every other request, and every other resolution, is unchanged.
        var provider = exactContext is null ? null : memos.SharedMemo.CompletedProviderKey(context, algorithm);
        if (provider is { } kept && memos.SharedMemo.TryAdoptCompletedProvider(kept, out var adopted, out var adoptedIndependent))
        {
            if (memos.SharedMemo.VerifiesAdoptedProviders)
            {
                // TEST SEAM: this resolution's own computation, exactly as without the share, beside what it adopted. It
                // runs in a window like a first computation, so what it leaves in the memo is what one would leave.
                var before = memos.SharedMemo.ContextUses;
                AlgorithmSummary own;
                memos.SharedMemo.OpenProviderWindow(kept);
                try
                {
                    own = CollectAlgorithmSummary(algorithm, CreateNameSet(), memos.SharedMemo, memos.Observations, context);
                }
                finally
                {
                    memos.SharedMemo.CloseProviderWindow();
                }
                if ((canShare && before == memos.SharedMemo.ContextUses) != adoptedIndependent)
                    throw new InvalidOperationException("An adopted completed provider summary differs from the computed one: context use.");
                if (SummaryMemo.AdoptedSummaryDifference(adopted, own) is { } difference)
                    throw new InvalidOperationException($"An adopted completed provider summary differs from the computed one: {difference}.");
            }

            // The memo holds the adopted summary where its own computation would have put it.
            if (adoptedIndependent && canShare) independent.Add(algorithm, adopted);
            else
            {
                memos.SharedMemo.UseContext();
                cache[key] = adopted;
            }
            memos.SharedMemo.NoteKeptProviderResult(adopted);
            return adopted;
        }

        var uses = memos.SharedMemo.ContextUses;
        if (!canShare) memos.SharedMemo.UseContext();
        memos.Observations?.RecordDependencyAlgorithmSummaryComputation();
        if (provider is not { } computed)
        {
            result = CollectAlgorithmSummary(algorithm, CreateNameSet(), memos.SharedMemo, memos.Observations, context);
            if (uses == memos.SharedMemo.ContextUses) independent.Add(algorithm, result);
            else cache[key] = result;
            memos.SharedMemo.NoteProviderWindowResult(result);
            return result;
        }

        memos.SharedMemo.OpenProviderWindow(computed);
        bool keeps;
        try
        {
            result = CollectAlgorithmSummary(algorithm, CreateNameSet(), memos.SharedMemo, memos.Observations, context);
        }
        finally
        {
            keeps = memos.SharedMemo.CloseProviderWindow();
        }

        var isIndependent = uses == memos.SharedMemo.ContextUses;
        if (isIndependent) independent.Add(algorithm, result);
        else cache[key] = result;
        var unit = memos.SharedMemo.CompletingUnit!;
        if (keeps && memos.SharedMemo.StoredForm(result, isIndependent, unit) is { } stored)
        {
            memos.SharedMemo.CompletedProviders!.Stage(computed, stored);
            memos.SharedMemo.NoteKeptProviderResult(result);
            memos.Observations?.RecordCompletedProviderSummaryKept();
        }

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
        // declarations may provide into a reference anchored here for provider selection during settlement.
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
    /// <para>Each call reads the member map as it stands and keeps nothing: anchoring an escaping name requires no
    /// further expansion, so the expansion never nests, and every result is complete. (Until November 2026 every
    /// expansion first looked its seed up, by the seed's serialized key, in a cache that lived for one call; once the
    /// expansion stopped nesting, that cache answered none of 3.3 million lookups, and it was deleted.) A nonempty
    /// expansion observes <see cref="SummaryMemo.CancellationToken"/> on entry and before anchoring each escaping bare
    /// name, the checkpoints of the former frame driver.</para>
    /// </summary>
    internal static SummarySeed ExpandAtLevel(SummarySeed baseSeed, LevelContext level)
    {
        // A seed with no requirement, name or reference has nothing to resolve, escape or qualify at any level: its
        // expansion is the empty seed, whatever the level.
        if (baseSeed.IsEmpty)
            return new SummarySeed();

        var memo = level.Memos.SharedMemo;
        memo.ObserveCancellation();
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

            memo.ObserveCancellation();
            AddEscaping(expanded, dependencyName, level);
        }

        var context = level.Memos.CompletedContext;
        foreach (var pending in baseSeed.PendingReferences)
        {
            memo.UseContext();
            // The same Q1-proved local equation bridge used by SolveMemberSeeds applies
            // when anchoring an external seed through this owner. Read the live map so the
            // member solver's read recording and invalidation see this read.
            if (memo.SelectsLocalMember(pending, context)
                && level.LocalPropertySummaries.TryGetValue(pending.Head, out var local))
            {
                expanded.AbsorbCompleted(local);
                continue;
            }
            expanded.PendingReferences.Add(pending.At(context));
        }

        expanded.QualifyParameters(level.Algorithm, level.ParameterNames, level.Memos.Observations);
        return expanded;
    }

    /// <summary>
    /// Carries a requirement's context without settling a raw path or provider: the escaping reference is anchored
    /// at the level's completed context, so no expansion leaves a bare name or an origin-less path behind.
    /// </summary>
    private static void AddEscaping(SummarySeed expanded, string name, LevelContext level)
    {
        level.Memos.SharedMemo.UseContext();
        expanded.PendingReferences.Add(new PendingReference(name, [], level.Memos.CompletedContext));
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
    /// loaded module's root. In an open-target recovery walk a block path contributes an empty seed:
    /// its block is declared at the prelude and has no requirements on the opener. Its intermediate edges
    /// still participate in the recovery walk's usual fallback accounting. The path's
    /// <paramref name="intermediates"/> are those of <see cref="MemberPathSpine"/>, as for a name-headed path.
    /// <para>A block written in a hoisted deconstruction right-hand side is found here too: the source's rows are
    /// walked with the memos of the level that declares the deconstruction, and that level's completed context is
    /// the one the static facts declare the block in (the source's own context holds no written expression).</para>
    /// </summary>
    private static bool TryGetBlockMemberPathSeed(Expr.DotCall dotCall, SummaryWalkMemos memos,
        out SummarySeed seed, out IReadOnlyList<Expr.DotCall> intermediates)
    {
        seed = null!;
        intermediates = [];
        if (MemberPathSpine(dotCall, out var reversed, out var edges) is not Expr.AlgorithmExpr(var body)
            || body.IsModuleRoot || body is not (Algorithm.User or Algorithm.Alias))
            return false;
        intermediates = edges;
        if (memos.OpenTargetRegion)
        {
            seed = new SummarySeed();
            return true;
        }
        var context = memos.SharedMemo.RequirementContext(ChildContext(memos.CompletedContext, body), body);
        if (context.Facts.Facts(context.Key) is not { Body: not null })
            throw new InvalidOperationException("A completed block-head requirement body is unavailable.");
        memos.SharedMemo.UseContext();
        var firstMember = reversed[^1];
        reversed.RemoveAt(reversed.Count - 1);
        reversed.Reverse();
        seed = new SummarySeed(pendingReferences: [new PendingReference(firstMember, reversed,
            origin: context, selection: PendingSelection.BlockHead)]);
        return true;
    }

    /// <summary>
    /// The opens walk of a level: a named target charges the navigated provider path
    /// (<c>open A</c> needs only A's identity; <c>open A.B</c> charges the
    /// requirements of the navigated member <c>B</c>), an inline-headed target charges
    /// nothing (its block is wired to the prelude), and
    /// other shapes retain ordinary expression accounting for the names, parameters and fallbacks they contain.
    /// <para>That ordinary walk runs in an OPEN-TARGET REGION (<see cref="SummaryWalkMemos.OpenTargetRegion"/>): what it
    /// charges for the names and parameters such a shape writes is unchanged, but an ALGORITHM written in it charges
    /// nothing and is never resolved structurally. Every algorithm written in an open target is declared at the
    /// prelude — static admission keys it there, and parameter detection, implicit-argument resolution, open-provider
    /// validation and the exposure rewrite elaborate it there — so, as for the inline head above, nothing reached from
    /// it can require the opener's chain; and none of these shapes is ever evaluated as a value. Walked as an expression
    /// of this level, a block-headed path inside such a shape (<c>open [{ … }.X]</c>, <c>open F({ … }.X)</c>,
    /// <c>open load({ … }.X)</c>) looked for its block under the opener, where no key exists, and failed
    /// <see cref="TryGetBlockMemberPathSeed"/>'s completed-body invariant, which keeps holding for every block an admitted
    /// row reads.</para>
    /// </summary>
    private static SummarySeed CollectOpenTargetSeeds(
        IReadOnlyList<Expr> opens,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos)
    {
        var seed = new SummarySeed();
        SummaryWalkMemos? openTargetRegion = null;
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

                // A parameter-owned head, a load directive no module replaced, or a shape the parser rejects.
                default:
                    openTargetRegion ??= new SummaryWalkMemos(memos.SharedMemo, memos.Observations, memos.CompletedContext,
                        openTargetRegion: true);
                    seed.UnionWith(CollectSummarySeed(target, localPropertySummaries, ownedHere, openTargetRegion, inTransparentContext: false));
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
            // The pattern supplies the branch's binders. The representative supplies the context in which
            // its summary's escaping references are anchored.
            var context = sharedMemo.BranchContexts.NamesOf(branch.Pattern);
            var binderNames = context.Names;
            var branchContext = ChildContext(completedContext, branch.Body, branch.Pattern, algorithm.Opens.Count == 0);
            var representative = BranchSummaryRepresentative(branch.Body, sharedMemo, branchContext);
            var key = new BranchBodySummaryKey(branch.Body, context.Id, representative.Key, representative.Facts);
            // Every branch with this key receives the same seed. Skip its clone and union on later visits in this family.
            if (!contributed.Add(key))
                continue;
            var contribution = CollectBranchBodySummarySeed(branch.Body, binderNames, key, sharedMemo, observations, representative);
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
    /// The context whose summary stands for a branch body's in <paramref name="branchContext"/>: the body's binding-free
    /// summary region (<see cref="SummaryMemo.SummaryRegion"/>), then that region's shared-body representative
    /// (<see cref="SummaryMemo.SharedRegionContext"/>). Branches of one body and binder-name set with one representative
    /// receive one summary, whose anchored origins lie in the representative.
    /// </summary>
    private static CompletedStructureContext BranchSummaryRepresentative(Algorithm body, SummaryMemo sharedMemo,
        CompletedStructureContext branchContext)
        => sharedMemo.SharedRegionContext(sharedMemo.SummaryRegion(branchContext, body), body);

    /// <summary>
    /// Memo-shared branch-body summary for one (body, binder-name set) at its summary representative
    /// <paramref name="representative"/> (<see cref="BranchSummaryRepresentative"/>), which <paramref name="key"/> names —
    /// see <see cref="SummaryMemo.CompletedBranchBodySummaries"/>. Records completed computations (memo misses) only,
    /// like <see cref="CollectSharedAlgorithmSummarySeed"/>.
    /// </summary>
    private static SummarySeed CollectBranchBodySummarySeed(
        Algorithm body,
        IReadOnlySet<string> binderNames,
        BranchBodySummaryKey key,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext representative)
    {
        var independentKey = key with { Scope = null, Facts = null };
        var independent = sharedMemo.IndependentBranchSummaries ??= new();
        var canShare = sharedMemo.BranchParametersAgree(body, binderNames, representative);
        if (canShare && independent.TryGetValue(independentKey, out var shared)) return shared.Clone();
        var completedSummaries = sharedMemo.CompletedBranchBodySummaries ??= new();
        if (completedSummaries.TryGetValue(key, out var stored))
        {
            sharedMemo.UseContext();
            sharedMemo.NoteProviderWindowReuse(stored);
            return stored.Clone();
        }

        var uses = sharedMemo.ContextUses;
        if (!canShare) sharedMemo.UseContext();
        observations?.RecordDependencyBranchBodySummaryComputation();
        var seed = CollectSummarySeed(body, CreateNameSet(binderNames), sharedMemo, observations, representative);
        if (canShare && uses == sharedMemo.ContextUses) independent.Add(independentKey, seed.Clone());
        else
        {
            var kept = seed.Clone();
            completedSummaries[key] = kept;
            sharedMemo.NoteProviderWindowResult(kept);
        }
        return seed;
    }

    /// <summary>
    /// ONE branch body's contribution to its family's summary, exactly as the family's own walk computes it
    /// (<see cref="CollectSummarySeed(Algorithm.Conditional, IReadOnlySet{string}, SummaryMemo, FrontEndTraversalObservations?, CompletedStructureContext)"/>):
    /// the body summarized under the binder names of <paramref name="pattern"/> in its completed context
    /// <paramref name="branchContext"/>, through the same branch-body memo, so a body the memo already holds is not
    /// walked again. The binders are stripped; what the seed still carries is what the body requires from OUTSIDE its
    /// family. The caller owns the returned seed.
    /// <para>The one caller outside the family walk is a deferred module region's materialization (B2c, owner decision
    /// 2026-11-15 "refuse at load"): the family's walk summarized the branch's PROVISIONAL body before its module
    /// existed, and the materialized body's contribution is compared with what the family charged then
    /// (<see cref="PropertyExposureResolver.DeferredBranchContext"/>).</para>
    /// </summary>
    internal static SummarySeed BranchBodyContribution(
        Algorithm body,
        Pattern pattern,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext branchContext)
    {
        var binders = sharedMemo.BranchContexts.NamesOf(pattern);
        var representative = BranchSummaryRepresentative(body, sharedMemo, branchContext);
        return CollectBranchBodySummarySeed(body, binders.Names,
            new BranchBodySummaryKey(body, binders.Id, representative.Key, representative.Facts), sharedMemo, observations, representative);
    }

    /// <summary>
    /// THE SUBSET PREDICATE over settled contributions: the requirements of <paramref name="contribution"/> that
    /// <paramref name="charged"/> does not hold; the empty set exactly when the contribution is a subset. Elements are
    /// compared by OWNER-QUALIFIED identity, the identity every FE-4a requirement set is built from
    /// (<see cref="PropertyExposureResolver.Requirement"/>: the name AND the owning scope by reference), never by
    /// spelling: a parameter <c>y</c> of an inner owner is not charged by a same-named <c>y</c> of an outer one.
    /// Either operand may belong to another run's interner (a deferred materialization compares its own run's
    /// contribution with the eager run's); <paramref name="sets"/> adopts it by its elements, whose owner scopes are
    /// unchanged, so nothing is copied beyond the interner's one adoption per foreign set.
    /// </summary>
    internal static RequirementSet UnchargedRequirements(RequirementSet contribution, RequirementSet charged, RequirementSetInterner sets)
        => contribution.IsEmpty ? default : sets.Except(contribution, charged);

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

            Expr.AlgorithmExpr(var algorithm) => memos.OpenTargetRegion
                ? new SummarySeed()
                : CollectSharedAlgorithmSummarySeed(algorithm, memos),

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
        var independent = memos.OpenTargetRegion
            ? memos.SharedMemo.OpenTargetArgumentBundles ??= new(ReferenceEqualityComparer.Instance)
            : memos.SharedMemo.IndependentArgumentBundles ??= new(ReferenceEqualityComparer.Instance);
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
    /// (<see cref="TryGetBlockMemberPathSeed"/>). A receiver of any other shape (a parameter, a
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
    /// activation's value to another (finding F3).</para>
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
            seed = new SummarySeed(pendingReferences: [new SummaryReference(pathHead, pathMembers)]);
        else if (!TryGetBlockMemberPathSeed(dotCall, memos, out seed, out intermediates))
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
    /// once). Equal content is decided on the seeds themselves — a hash computed once per member, then
    /// set equality (<see cref="SeedContent"/>) — never on serialized text: measured on November 20 2026,
    /// computing and storing the former text keys cost more allocation than the expansions their hits avoided
    /// in both measured corpora. A member seed is never mutated after it enters the map (every one is its own expansion at
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
            HashSet<SummaryReference>? selected = null;
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
        var contents = new SeedContent?[properties.Count];
        Dictionary<SeedContent, (SummarySeed Result, (string Name, SummarySeed Read)[] Reads)>? expansions = null;
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

            var key = contents[index] ??= SeedContent.Of(baseSeed, memos.Observations);
            expansions ??= new(SeedContent.Comparer);
            if (expansions.TryGetValue(key, out var expansion) && ReadsStand(expansion.Reads))
            {
                foreach (var (readName, _) in expansion.Reads)
                    recorded.Reads.Add(readName);
                return expansion.Result;
            }

            memos.Observations?.RecordSummaryMemberExpansion();
            var expanded = ExpandAtLevel(baseSeed, level);
            var reads = new (string Name, SummarySeed Read)[recorded.Reads.Count];
            var at = 0;
            foreach (var readName in recorded.Reads)
                reads[at++] = (readName, seeds[readName]);
            expansions[key] = (expanded, reads);
            return expanded;
        }

        // Whether every member seed an expansion read is still the one it read.
        bool ReadsStand((string Name, SummarySeed Read)[] reads)
        {
            foreach (var (name, read) in reads)
                if (!ReferenceEquals(seeds[name], read))
                    return false;
            return true;
        }
    }

    // A base seed's CONTENT as the expansion cache's key (SolveMemberSeeds): its order-independent hash, computed once per
    // member, and content equality (SummarySeed.ContentEquals) — the four sets themselves, never serialized text. Base seeds
    // are not mutated while their level is solved, so a key stays valid for the whole solve.
    private readonly record struct SeedContent(SummarySeed Seed, int Hash)
    {
        public static SeedContent Of(SummarySeed seed, FrontEndTraversalObservations? observations)
        {
            seed.RecordKeyCharacters(observations);
            return new(seed, seed.ContentHash());
        }

        public static readonly IEqualityComparer<SeedContent> Comparer = new ContentComparer();

        private sealed class ContentComparer : IEqualityComparer<SeedContent>
        {
            public bool Equals(SeedContent x, SeedContent y)
                => x.Hash == y.Hash && (ReferenceEquals(x.Seed, y.Seed) || x.Seed.ContentEquals(y.Seed));

            public int GetHashCode(SeedContent content) => content.Hash;
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
