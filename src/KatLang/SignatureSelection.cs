using System.Collections.Immutable;
using System.Numerics;
using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// One value-role reference of a Q8 equation (B3-5★), in written order: the callee a formula reads. An INTERNAL target
/// (<paramref name="Target"/> ≥ 0) is another equation of the same selection, whose signature is selected; an EXTERNAL
/// target carries its FINAL lifting signature (a builtin, a Math member, a host operation, a clause family, a closed
/// body, a body an earlier operation completed). A guarded reference (<paramref name="Guard"/> ≥ 0) is active only when
/// its <c>.Algorithm</c> link is a calculation. <paramref name="Identity"/> deduplicates lifted callees, after activation.
/// </summary>
internal readonly record struct SignatureEquationReference(
    int Target,
    CallableSignature? External,
    object Identity,
    int Guard,
    Expr Reference,
    string DisplayName);

/// <summary>
/// The fact of one equation under one classification: its composed signature (recovered when it breaks a rule a written
/// signature is held to, X-02), that rule, whether the composition lifted anything, and what it was composed from —
/// opaque to the selector, which only reads the signature.
/// </summary>
internal sealed class SignatureFact(
    IReadOnlyList<ParameterPattern> patterns,
    ParameterSignatureViolation? violation,
    bool isLifted,
    object? composition,
    CallableSignature signature)
{
    private static long _nextId;

    /// <summary>This fact's exact identity within the process (a memo key; never a hash, which can collide).</summary>
    public long Id { get; } = Interlocked.Increment(ref _nextId);

    public IReadOnlyList<ParameterPattern> Patterns { get; } = patterns;

    public ParameterSignatureViolation? Violation { get; } = violation;

    /// <summary>Whether the composition appended lifted parameters to the body's own.</summary>
    public bool IsLifted { get; } = isLifted;

    /// <summary>What the composition read, for its consumer to check it reads the same; never read by the selector.</summary>
    public object? Composition { get; } = composition;

    public CallableSignature Signature { get; } = signature;

    /// <summary>Whether a value-role reference to this body lifts (Q-03: it cannot accept zero supplied arguments).</summary>
    public bool Requires { get; } = !ParameterPattern.AcceptsZeroSuppliedSlots(patterns);

    /// <summary>A link's class: a calculation exactly when its signature declares a parameter (META-S3-2).</summary>
    public bool IsNonempty => Patterns.Count != 0;
}

/// <summary>One equation exactly as a selection received it from the analysis (the correspondence bridge's input).</summary>
internal sealed record SignatureSelectionProbeEquation(
    string Name,
    IReadOnlyList<ParameterPattern> Own,
    IReadOnlyList<string> Forwardable,
    bool IsLink,
    IReadOnlyList<SignatureEquationReference> References);

/// <summary>
/// One real selection, as the correspondence bridge observes it (<see cref="FrontEndTraversalObservations.OnSignatureSelection"/>):
/// the analyzed equations it read, the outcome it reached, and its own composition law, so a control can run the real
/// selector over a deliberately changed system while the operation is alive. Test-only; it is valid during the callback.
/// </summary>
internal sealed record SignatureSelectionProbe(
    IReadOnlyList<SignatureSelectionProbeEquation> Equations,
    SignatureSelector.Selection Selection,
    SignatureSelector.Compose Compose,
    SignatureFact Closed);

/// <summary>Why a selection published nothing for a group of equations: rule G6's categories (B3-5★).</summary>
internal enum SignatureSelectionOutcome : byte
{
    /// <summary>The unique grounded classification was selected.</summary>
    Selected,

    /// <summary>Two or more grounded classifications.</summary>
    Ambiguous,

    /// <summary>No consistent classification, and no classification has a cycle that fails to settle.</summary>
    Contradiction,

    /// <summary>Only self-supporting (ungrounded) classifications.</summary>
    UngroundedOnly,

    /// <summary>Whether a classification supports itself is undecided: a counterfactual of it does not settle (U1).</summary>
    Undetermined,

    /// <summary>A recursive completion repeats an earlier state with a period above one: the group has no reached state.</summary>
    NonSettling,

    /// <summary>A reader of a group that failed (reported at that group, not here).</summary>
    Blocked,
}

/// <summary>
/// SIGNATURE SELECTION (B3-5★, owner direction 2026-11-05: X-04 = plain A-agree; research R2/R5/R6, rule G6). Every Q8
/// fact of one static operation — each open body's composed signature and, through it, each <c>.Algorithm</c> link's
/// class (a calculation exactly when its signature is nonempty) — is decided here, JOINTLY, before any consumer reads
/// one: no consumer ever observes a provisional signature, so no fact depends on a processing order.
///
/// <para>A classification (a guard VECTOR) assigns every link a class. Under a vector the active read graph is
/// evaluated dependency-first. A cyclic component is first evaluated with every member read as declaring no parameter
/// (the CLOSED GATE): when no read inside the cycle then lifts, that evaluation is the cycle's meaning (Lemma B1);
/// otherwise the cycle is a GENUINE LIFTING CYCLE, completed by SIMULTANEOUS ROUNDS from the closed gate
/// (<see cref="Complete"/>): the reached state is the answer, whatever other structural fixed point the equations have,
/// and only a cycle that does not settle has no meaning, nor has any body that reads it. A vector is CONSISTENT when
/// every link evaluates to its assigned class and every body has a meaning, and GROUNDED when every nonempty set of
/// calculation links is refuted — some member stays a nonempty calculation without the set's support; three-valued,
/// since a counterfactual can be meaningless (U1). Rule G6 selects the unique grounded consistent vector, each vector
/// having exactly one reading; otherwise the group is refused with its category.</para>
///
/// <para>Components are an optimization only: a dependency-first LOCAL pass settles every component that has a unique
/// grounded answer given the settled ones below it; a component that fails locally is re-solved JOINTLY with every
/// reader (a reader may exclude a lower answer), by alternative-carrying stratification over the region's dependency
/// cone: the cone's settled components are carried by their selected readings, and the whole cone is enumerated only to
/// decide a refusal's category (<see cref="SolveRegion"/>). A component's table is found by the CLASSIFICATION SEARCH
/// (<see cref="ClassificationSearch"/>, an optimization too): it never evaluates its 2^links vectors one by one, but one
/// reading per partial vector, split only where a reading consults a class it depends on, so vectors that read alike are
/// expanded once (a ring of links costs states linear in its links). A link-free component has exactly one vector, so a
/// link-free program costs one evaluation per equation, plus the closed gate of each cycle and the rounds of each genuine
/// lifting cycle, which recompose only the members whose reads changed. Work and storage are charged to the operation's
/// ledger (<see cref="StaticQueryResourceBudget"/>): exhaustion is <see cref="StaticQueryLimitExceededException"/>,
/// cancellation the operation's token, and a failed or cancelled selection publishes nothing.</para>
/// </summary>
internal sealed class SignatureSelector
{
    /// <summary>The ONE composition law: an equation's own patterns with the given lifted callees, in order.</summary>
    internal delegate SignatureFact Compose(int equation, IReadOnlyList<(int Reference, CallableSignature Signature)> lifted);

    /// <summary>The callees an equation lifts when its in-component targets read <paramref name="facts"/>, in written order.</summary>
    internal delegate IReadOnlyList<(int Reference, CallableSignature Signature)> LiftedFrom(
        int equation, IReadOnlyDictionary<int, SignatureFact> facts);

    /// <summary>
    /// Prepares a settled component's final facts: their structure is the settled state's and their origins are final, so
    /// every reader and the rewrite compose from them. The selector never reads origins.
    /// </summary>
    internal delegate IReadOnlyDictionary<int, SignatureFact> SealCompletion(
        IReadOnlyList<int> component, IReadOnlyDictionary<int, SignatureFact> settled, LiftedFrom liftedFrom);

    private readonly int _count;
    private readonly IReadOnlyList<SignatureEquationReference>[] _references;
    private readonly bool[] _isLink;
    private readonly Compose _compose;
    private readonly SealCompletion _seal;
    private readonly SignatureFact _closed;
    private readonly StaticQueryResourceBudget _resources;
    private readonly CancellationToken _cancellationToken;

    // One fact per equation per exact inputs, and one sealed component per exact settled facts: a table or a joint region
    // that evaluates an equation again from the same callees gets the very same objects. Every read of a selected signature
    // then sees one list, which the rewrite checks by reference, however many readings computed it. Both memos are hashed
    // by the identities they compare, so a lookup costs its inputs, never the number of readings already stored.
    private readonly Dictionary<IReadOnlyList<(int Reference, CallableSignature Signature)>, SignatureFact>?[] _composed;
    private readonly Dictionary<SignatureFact[], IReadOnlyDictionary<int, SignatureFact>>?[] _sealed;
    private readonly ExactInputs _exactInputs = new();
    private readonly ExactFacts _exactFacts = new();
    private readonly Dictionary<IReadOnlyList<ParameterPattern>, long> _patternNodes = new(ReferenceEqualityComparer.Instance);
    private long _classificationStates;

    /// <param name="references">Each equation's ordered references.</param>
    /// <param name="isLink">Whether each equation is an <c>.Algorithm</c> link (its class is a guard).</param>
    /// <param name="compose">The composition law (<see cref="ImplicitArgumentResolver"/>'s lifting).</param>
    /// <param name="seal">Prepares the final facts of a settled cycle (<see cref="ImplicitArgumentResolver"/>'s origins).</param>
    /// <param name="closed">The fact a cycle member is read as under the closed gate: no parameter at all.</param>
    /// <param name="resources">The operation's ledger: every evaluation and table row is charged to it.</param>
    /// <param name="cancellationToken">The operation's cancellation, observed at every charge.</param>
    internal SignatureSelector(
        IReadOnlyList<SignatureEquationReference>[] references,
        bool[] isLink,
        Compose compose,
        SealCompletion seal,
        SignatureFact closed,
        StaticQueryResourceBudget resources,
        CancellationToken cancellationToken)
    {
        _count = references.Length;
        _references = references;
        _isLink = isLink;
        _compose = compose;
        _seal = seal;
        _closed = closed;
        _resources = resources;
        _cancellationToken = cancellationToken;
        _composed = new Dictionary<IReadOnlyList<(int, CallableSignature)>, SignatureFact>?[_count];
        _sealed = new Dictionary<SignatureFact[], IReadOnlyDictionary<int, SignatureFact>>?[_count];
    }

    /// <summary>
    /// TEST SEAM: every table is built by the generic path — each classification vector read whole, and each counterfactual
    /// of each consistent one (<see cref="ClassificationSearch.EveryRow"/>) — instead of by the classification search, so a
    /// test can compare the search with exactly what it optimizes. Never set in production.
    /// </summary>
    internal bool EnumeratesEveryClassification { get; init; }

    /// <summary>
    /// The outcome of one selection: every published fact, and every refused group with its category — the equations it
    /// is reported at, and the <c>.Algorithm</c> links whose classification it could not decide (none for a cycle that does
    /// not settle under any classification).
    /// </summary>
    internal sealed class Selection
    {
        public Dictionary<int, SignatureFact> Facts { get; } = [];

        public List<(IReadOnlyList<int> Equations, IReadOnlyList<int> Links, SignatureSelectionOutcome Outcome)> Refusals { get; } = [];

        public bool Succeeded => Refusals.Count == 0;

        /// <summary>The components and edges visited forming the joint regions (an observation: linear in their cones).</summary>
        public long RegionVisits { get; set; }

        /// <summary>
        /// The classification states every table visited, groundedness included (<see cref="ClassificationSearch"/>; an
        /// observation: a ring of links visits a number linear in its links, where evaluating every vector visited 2^n).
        /// </summary>
        public long ClassificationStates { get; set; }
    }

    // ─── one equation, one vector ─────────────────────────────────────────────────────────────────

    /// <summary>
    /// One equation's fact under these reads: the stored fact of its exact lifted inputs, or a new composition. A round
    /// passes <paramref name="storedUnits"/>, its composition's charge, so the storage a NEW fact retains is charged before
    /// it is composed, and a reading that finds its fact retains nothing. A table passes the positions of the references
    /// that can lift there (<see cref="ClassificationSearch"/>), so a reading never rescans the ones that cannot.
    /// </summary>
    private SignatureFact EvaluateEquation(int equation, Func<int, SignatureFact> look, Func<int, bool> isOpen, long storedUnits = 0,
        int[]? positions = null)
    {
        _resources.Work(1, _cancellationToken);
        var lifted = Lifted(equation, look, isOpen, positions);
        var known = _composed[equation] ??= new(1, _exactInputs);
        // One hashed lookup, charged for the inputs it hashes and compares: the stored fact itself is returned, since a
        // selected composition and the rewrite are compared by reference.
        _resources.Work(1 + lifted.Count, _cancellationToken);
        if (known.TryGetValue(lifted, out var fact))
            return fact;

        if (storedUnits != 0)
            _resources.Metadata(storedUnits, work: 0, _cancellationToken);
        var composed = _compose(equation, lifted);
        known.Add(lifted, composed);
        return composed;
    }

    /// <summary>Exact composition inputs: the same reference positions with the same pattern lists, by reference.</summary>
    private sealed class ExactInputs : IEqualityComparer<IReadOnlyList<(int Reference, CallableSignature Signature)>>
    {
        public bool Equals(IReadOnlyList<(int Reference, CallableSignature Signature)>? left, IReadOnlyList<(int Reference, CallableSignature Signature)>? right)
            => SameInputs(left!, right!);

        public int GetHashCode(IReadOnlyList<(int Reference, CallableSignature Signature)> inputs)
        {
            var hash = new HashCode();
            hash.Add(inputs.Count);
            for (var index = 0; index < inputs.Count; index++)
            {
                hash.Add(inputs[index].Reference);
                hash.Add(RuntimeHelpers.GetHashCode(inputs[index].Signature.ParameterPatterns));
            }

            return hash.ToHashCode();
        }
    }

    /// <summary>Exact settled facts of one component, member by member, by reference.</summary>
    private sealed class ExactFacts : IEqualityComparer<SignatureFact[]>
    {
        public bool Equals(SignatureFact[]? left, SignatureFact[]? right)
        {
            if (left!.Length != right!.Length)
                return false;
            for (var index = 0; index < left.Length; index++)
            {
                if (!ReferenceEquals(left[index], right[index]))
                    return false;
            }

            return true;
        }

        public int GetHashCode(SignatureFact[] facts)
        {
            var hash = new HashCode();
            hash.Add(facts.Length);
            foreach (var fact in facts)
                hash.Add(RuntimeHelpers.GetHashCode(fact));
            return hash.ToHashCode();
        }
    }

    private static bool SameInputs(
        IReadOnlyList<(int Reference, CallableSignature Signature)> left,
        IReadOnlyList<(int Reference, CallableSignature Signature)> right)
    {
        if (left.Count != right.Count)
            return false;
        for (var index = 0; index < left.Count; index++)
        {
            if (left[index].Reference != right[index].Reference
                || !ReferenceEquals(left[index].Signature.ParameterPatterns, right[index].Signature.ParameterPatterns))
                return false;
        }

        return true;
    }

    /// <summary>
    /// The LIFTING RULE: the callees a reference lifts under these facts, in written order, each identity once. Given
    /// <paramref name="positions"/> (ascending), only those references are read: the caller guarantees that every other
    /// one reads a callee that accepts zero supplied arguments, which lifts nothing and marks no identity as seen.
    /// </summary>
    private IReadOnlyList<(int Reference, CallableSignature Signature)> Lifted(int equation, Func<int, SignatureFact> look, Func<int, bool> isOpen,
        int[]? positions = null)
    {
        List<(int, CallableSignature)>? lifted = null;
        HashSet<object>? seen = null;
        var references = _references[equation];
        var count = positions?.Length ?? references.Count;
        for (var at = 0; at < count; at++)
        {
            var index = positions is null ? at : positions[at];
            var reference = references[index];
            // The guard decides whether the reference is a value read at all — BEFORE its callee is deduplicated, so an
            // inactive first occurrence never hides an active later one.
            if (reference.Guard >= 0 && !isOpen(reference.Guard))
                continue;
            var signature = reference.Target >= 0 ? look(reference.Target).Signature : reference.External!;
            if (signature.AcceptsZeroSuppliedArguments)
                continue;
            if (!(seen ??= new(ReferenceEqualityComparer.Instance)).Add(reference.Identity))
                continue;
            (lifted ??= []).Add((index, signature));
        }

        return (IReadOnlyList<(int, CallableSignature)>?)lifted ?? [];
    }

    // ─── recursive completion ─────────────────────────────────────────────────────────────────────

    /// <summary>
    /// SIMULTANEOUS COMPLETION (X-04 plain A-agree): round k+1 is every member composed from round k's facts by the ONE
    /// composition law, with lower and external facts fixed, starting from the closed gate. The state is every member's
    /// full ordered pattern tree and X-02 flag. Two equal successive states settle, and the reached state is the answer: no
    /// other fixed point is sought and an intermediate capture or requirement may disappear. A state equal to an earlier
    /// one at a greater distance proves the rounds never settle (null). Composition is a pure function of the state, so
    /// that is exact; the earlier state is kept by Brent's rule, so the detector holds at most two snapshots however long
    /// the rounds run. Exhausting the ledger is never non-settling. The settled state is sealed (<see cref="SealCompletion"/>)
    /// before any reader composes from it.
    ///
    /// <para>SEMI-NAIVE, and exact: round one recomposes every member; a later round recomposes only the in-component
    /// readers of the members whose fact OBJECT changed in the round before, in ascending position, and every other member
    /// carries its fact. A member none of whose active reads changed would read the very facts it read last round, and the
    /// equation memo returns one fact per exact inputs, so its recomposition would return the fact it carries: every round's
    /// state is object for object the full round's. Settlement and repetition stay STRUCTURAL: only a changed member can
    /// differ from its previous fact, or newly differ from (or agree with) the detector's snapshot, so the detector keeps a
    /// count of the members that differ from its snapshot and updates it for changed members alone. Each recomposition is
    /// charged its composition's work before it runs, and a composition that retains a NEW fact its storage (round lists
    /// stay in the run's template interner); each comparison is charged per node.</para>
    /// </summary>
    private IReadOnlyDictionary<int, SignatureFact>? Complete(
        IReadOnlyList<int> component,
        HashSet<int> members,
        Dictionary<int, SignatureFact> closed,
        Func<int, SignatureFact> look,
        Func<int, bool> isOpen,
        Func<int, int[]> relevant)
    {
        var count = component.Count;
        var position = new Dictionary<int, int>(count);
        for (var index = 0; index < count; index++)
            position.Add(component[index], index);

        // The in-component readers of each member over the active references; the classification, so every guard, is fixed
        // during the call. A reader that reads a member twice is listed twice and recomposed once.
        var readers = new List<int>?[count];
        for (var reader = 0; reader < count; reader++)
        {
            var key = component[reader];
            var positions = relevant(key);
            _resources.Work(positions.Length, _cancellationToken);
            foreach (var index in positions)
            {
                var reference = _references[key][index];
                if (reference.Target >= 0 && position.TryGetValue(reference.Target, out var read) && (reference.Guard < 0 || isOpen(reference.Guard)))
                    (readers[read] ??= []).Add(reader);
            }
        }

        var state = new SignatureFact[count];
        for (var index = 0; index < count; index++)
            state[index] = closed[component[index]];
        SignatureFact Read(int target) => position.TryGetValue(target, out var at) ? state[at] : look(target);

        // Brent's detector: ONE snapshot, and which members (how many) differ from it structurally.
        var saved = (SignatureFact[])state.Clone();
        var differs = new bool[count];
        var differing = 0;
        var savedAge = 0L;
        var window = 1L;
        var recompose = new List<int>(count);
        for (var index = 0; index < count; index++)
            recompose.Add(index);
        var scheduled = new long[count];
        var changed = new List<(int Position, SignatureFact Fact)>();
        for (var round = 1L; ; round++)
        {
            // Every recomposition reads the previous round's state: changes are applied after the round.
            changed.Clear();
            foreach (var at in recompose)
            {
                var key = component[at];
                var positions = relevant(key);
                var units = CompositionUnits(key, Read, isOpen, positions);
                _resources.Work(units, _cancellationToken);
                var fact = EvaluateEquation(key, Read, isOpen, storedUnits: units, positions: positions);
                if (!ReferenceEquals(fact, state[at]))
                    changed.Add((at, fact));
            }

            var settled = true;
            foreach (var (at, fact) in changed)
            {
                if (!SameFact(state[at], fact))
                {
                    settled = false;
                    break;
                }
            }

            foreach (var (at, fact) in changed)
                state[at] = fact;
            if (settled)
                return Sealed(component, state, members, look, isOpen, relevant);

            savedAge++;
            foreach (var (at, fact) in changed)
            {
                var differsNow = !SameFact(saved[at], fact);
                if (differsNow != differs[at])
                {
                    differs[at] = differsNow;
                    differing += differsNow ? 1 : -1;
                }
            }

            if (differing == 0)
                return null;
            if (savedAge == window)
            {
                Array.Copy(state, saved, count);
                Array.Clear(differs);
                differing = 0;
                savedAge = 0;
                window *= 2;
            }

            recompose.Clear();
            foreach (var (at, _) in changed)
            {
                if (readers[at] is not { } list)
                    continue;
                foreach (var reader in list)
                {
                    if (scheduled[reader] == round)
                        continue;
                    scheduled[reader] = round;
                    recompose.Add(reader);
                }
            }

            recompose.Sort();
        }
    }

    /// <summary>The sealed facts of a settled state: sealed once for its exact facts, so every reading shares one result.</summary>
    private IReadOnlyDictionary<int, SignatureFact> Sealed(
        IReadOnlyList<int> component,
        SignatureFact[] state,
        HashSet<int> members,
        Func<int, SignatureFact> look,
        Func<int, bool> isOpen,
        Func<int, int[]> relevant)
    {
        var known = _sealed[component[0]] ??= new(1, _exactFacts);
        var facts = (SignatureFact[])state.Clone();
        _resources.Work(1 + facts.Length, _cancellationToken);
        if (known.TryGetValue(facts, out var published))
            return published;

        var settled = new Dictionary<int, SignatureFact>(component.Count);
        for (var index = 0; index < facts.Length; index++)
            settled.Add(component[index], facts[index]);
        var result = _seal(component, settled, (equation, read) =>
        {
            var positions = relevant(equation);
            _resources.Work(positions.Length, _cancellationToken);
            return Lifted(equation, target => members.Contains(target) ? read[target] : look(target), isOpen, positions);
        });
        known.Add(facts, result);
        return result;
    }

    /// <summary>
    /// One member's composition charge: its references and every node of every active callee, in this round, lower or
    /// fixed, since the merge builds a list from them before anything is filtered. A list's nodes are counted once, one
    /// charged step per node.
    /// </summary>
    private long CompositionUnits(int equation, Func<int, SignatureFact> read, Func<int, bool> isOpen, int[] positions)
    {
        var references = _references[equation];
        var units = 1L + positions.Length;
        foreach (var index in positions)
        {
            var reference = references[index];
            if (reference.Guard >= 0 && !isOpen(reference.Guard))
                continue;
            var signature = reference.Target < 0 ? reference.External! : read(reference.Target).Signature;
            units += NodesOf(signature.ParameterPatterns);
        }

        return units;
    }

    private long NodesOf(IReadOnlyList<ParameterPattern> patterns)
    {
        if (_patternNodes.TryGetValue(patterns, out var known))
            return known;
        var nodes = 0L;
        var pending = new Stack<IReadOnlyList<ParameterPattern>>();
        pending.Push(patterns);
        while (pending.TryPop(out var items))
        {
            for (var index = 0; index < items.Count; index++)
            {
                _resources.Work(1, _cancellationToken);
                nodes++;
                if (ParameterPattern.StructuralItems(items[index]) is { } nested)
                    pending.Push(nested);
            }
        }

        _patternNodes.Add(patterns, nodes);
        return nodes;
    }

    /// <summary>Whether two facts are the same member state: the X-02 flag and the exact ordered pattern tree.</summary>
    private bool SameFact(SignatureFact left, SignatureFact right)
        => left.Violation == right.Violation && SamePatterns(left.Patterns, right.Patterns);

    /// <summary>
    /// Structural equality of two pattern lists: node classes, capture names and kinds, grouping and order, one charged
    /// step per node. Records are ignored: an origin is no part of the state, and object identity is never structure.
    /// </summary>
    private bool SamePatterns(IReadOnlyList<ParameterPattern> left, IReadOnlyList<ParameterPattern> right)
    {
        if (ReferenceEquals(left, right))
            return true;
        var pending = new Stack<(IReadOnlyList<ParameterPattern> Left, IReadOnlyList<ParameterPattern> Right, int Index)>();
        pending.Push((left, right, 0));
        while (pending.TryPop(out var frame))
        {
            _resources.Work(1, _cancellationToken);
            if (frame.Left.Count != frame.Right.Count)
                return false;
            if (frame.Index >= frame.Left.Count)
                continue;
            pending.Push((frame.Left, frame.Right, frame.Index + 1));
            var (a, b) = (frame.Left[frame.Index], frame.Right[frame.Index]);
            if (a.GetType() != b.GetType())
                return false;
            if (a is CaptureParameterPattern capture)
            {
                var other = (CaptureParameterPattern)b;
                if (capture.Kind != other.Kind || !string.Equals(capture.Name, other.Name, StringComparison.Ordinal))
                    return false;
            }
            else if (ParameterPattern.StructuralItems(a) is { } items)
            {
                pending.Push((items, ParameterPattern.StructuralItems(b)!, 0));
            }
        }

        return true;
    }

    // ─── tables, groundedness, rule G6 ────────────────────────────────────────────────────────────

    private enum RowKind : byte { Meaningless, Consistent }

    private enum Groundedness : byte { Grounded, Undetermined, Ungrounded, NotApplicable }

    /// <summary>
    /// One row of a table: a classification vector that is NOT refuted, with its reading. A consistent row holds every key's
    /// fact and its groundedness; a meaningless row holds the facts of the keys that have a meaning and the keys that have
    /// none, so a joint region carries it without evaluating the vector again.
    /// </summary>
    private sealed class Row
    {
        public required RowKind Kind;
        public required HashSet<int> Gamma;
        public bool Cyclic;
        public Groundedness Grounded;
        public IReadOnlyDictionary<int, SignatureFact>? Facts;
        public IReadOnlySet<int>? Meaningless;
    }

    /// <summary>The links a set of equations observes that are among them and that no lower context fixes, ascending.</summary>
    private List<int> LinksIn(IReadOnlyCollection<int> keys, IReadOnlyDictionary<int, bool> lowerOpen)
    {
        var inKeys = keys as IReadOnlySet<int> ?? new HashSet<int>(keys);
        var links = new SortedSet<int>();
        foreach (var key in keys)
        {
            foreach (var reference in _references[key])
            {
                if (reference.Guard >= 0 && inKeys.Contains(reference.Guard) && !lowerOpen.ContainsKey(reference.Guard))
                    links.Add(reference.Guard);
            }
        }

        return [.. links];
    }

    /// <summary>
    /// The fixed limit on the links one table classifies together: 2^62 or more classifications are refused whatever the
    /// program or the host. A table does not visit its classifications one by one (<see cref="ClassificationSearch"/>), but
    /// what it decides among stays bounded by this constant.
    /// </summary>
    private void RequireBoundedClassification(int dimensions)
    {
        if (dimensions < 62)
            return;
        _resources.Fail();
        throw new StaticQueryLimitExceededException(
            $"Signature selection would enumerate 2^{dimensions} classifications of .Algorithm links.", StaticQueryBoundKind.SignatureEnumeration);
    }

    /// <summary>Charges the 2^<paramref name="dimensions"/> choices an enumeration visits one by one, before it visits any.</summary>
    private void ChargeEnumeration(int dimensions)
    {
        RequireBoundedClassification(dimensions);
        _resources.Work(1L << dimensions, _cancellationToken);
    }

    /// <summary>
    /// The table of <paramref name="keys"/> over their own links: every classification vector that is not refuted, with its
    /// reading and, when it is consistent, its groundedness, in subset order (by size, then lexicographically by position;
    /// deterministic, never declaration-ordered) — exactly what evaluating each of the 2^dimensions vectors gives, found by
    /// the classification search.
    /// </summary>
    private List<Row> Table(
        IReadOnlyList<int> keys,
        IReadOnlyDictionary<int, SignatureFact> lowerFacts,
        IReadOnlyDictionary<int, bool> lowerOpen,
        IReadOnlySet<int> lowerMeaningless)
    {
        var links = LinksIn(keys, lowerOpen);
        RequireBoundedClassification(links.Count);
        using var structure = _resources.Temporary();
        var search = new ClassificationSearch(this, keys, links, lowerFacts, lowerOpen, lowerMeaningless, structure);
        return EnumeratesEveryClassification ? search.EveryRow() : search.Rows();
    }

    /// <summary>
    /// THE CLASSIFICATION SEARCH of one table: its keys, their own links as the dimensions, and fixed lower facts, classes
    /// and keys without meaning. It finds every vector that is not refuted, with its reading, and each consistent vector's
    /// three-valued groundedness — what evaluating every vector, and every counterfactual of every consistent one, gives —
    /// without evaluating the vectors one by one, so the vectors that read alike are expanded once.
    ///
    /// <para>THE RELEVANT REFERENCES, decided once per table: a reference matters to a reading only as an edge to a key, as
    /// a read of a key with no meaning, or as a callee that can lift. One to a lower or external callee whose fixed
    /// signature accepts zero supplied arguments lifts nothing, orders nothing and marks no identity as seen under either
    /// class of its guard, so no reading consults its guard or rescans it.</para>
    ///
    /// <para>A STATE is a partial vector together with ONE reading run over it: Tarjan's components of the active edges in
    /// the order a single vector's reading takes them, each component evaluated as it completes, exactly as that reading
    /// evaluates it. The run stops where it consults a dimension the partial vector leaves open. Every vector extending the
    /// state reads identically up to there, so the two classes continue as two copies of the state, never from the start.
    /// A consulted link whose own fact the run already computed is FORCED: a vector giving it the other class contradicts
    /// that fact, so it is refuted (for groundedness, a link that is still a calculation cannot leave the support). A
    /// component whose link was decided against the fact it completes with refutes every vector of the state. A finished
    /// state stands for every vector extending it: a link it never consulted takes the class of its fact, and one with no
    /// meaning, which no reading consulted, is free — each choice is a row of its own with the same reading. So a vector is
    /// a row exactly when the search reaches it, with the reading its own evaluation gives, and the search visits a state
    /// per class the readings actually depend on: a ring of links costs a linear number of states, never 2^n.</para>
    ///
    /// <para>GROUNDEDNESS of a consistent vector (every nonempty set T of its calculation links refuted: some member of T is
    /// still a nonempty calculation without T) is the same search over the counterfactuals: the links outside the vector
    /// are runtime references (whatever they complete as), each consulted link of the vector is kept or removed, a removed
    /// link that completes as a nonempty calculation refutes the state, and the links a finished state removed are an
    /// unrefuted support (the links it never consulted change nothing). A support with no member without meaning makes the
    /// vector ungrounded; one with such a member, undetermined.</para>
    ///
    /// <para>Charged to the operation's ledger with its cancellation: the relevant references once, every state, every
    /// edge, consult and reference a reading visits, every copy of a state, the storage of every state alive and of the
    /// table's structure while it is searched, and the storage of every row it keeps. Storage is reserved before it is
    /// allocated: each key's part of the structure is counted first and then built at exactly that size, with no
    /// temporary buffer, so a refused reservation leaves nothing of that part allocated.</para>
    /// </summary>
    private sealed class ClassificationSearch
    {
        // How a reference's guard reads: no guard, a class fixed below (or no class: a runtime reference), or a dimension.
        private const int Unguarded = -1;
        private const int FixedClosed = -2;
        private const int FixedOpen = -3;

        private enum Read : byte { Closed, Open, Undecided }

        private enum Outcome : byte { Finished, Refuted, Undecided }

        /// <summary>What a reference is to a table (<see cref="RoleOf"/>).</summary>
        private enum Role : byte { Irrelevant, Edge, MeaninglessRead, Lifts }

        /// <summary>What a run checks the links of a completed component against.</summary>
        private enum Mode : byte
        {
            /// <summary>A table: a decided link must complete with its class, else the state's vectors are refuted.</summary>
            Table,

            /// <summary>The groundedness of <see cref="_vector"/>: a link removed from it must not complete as a nonempty calculation.</summary>
            Groundedness,

            /// <summary>One whole vector, nothing checked: the generic path's reading (<see cref="EveryRow"/>).</summary>
            Reading,
        }

        /// <summary>A reference to a key of the table: the key's position, the guard, and whether that key has no meaning below.</summary>
        private readonly record struct Edge(int Target, int Guard, bool LowerMeaningless);

        private struct Frame
        {
            public int Node;
            public int Position;
        }

        /// <summary>One state: a partial vector (decided dimensions and their classes) and its reading run so far.</summary>
        private sealed class State
        {
            public ulong Decided;
            public ulong Value;
            public SignatureFact?[] Facts = [];
            public bool[] Meaningless = [];
            public bool Cyclic;
            public int[] Index = [];
            public int[] Low = [];
            public bool[] OnStack = [];
            public int[] Stack = [];
            public int StackCount;
            public Frame[] Frames = [];
            public int FrameCount;
            public int Next;
            public int Root;
            public int[]? Pending;

            public static State Initial(int count)
            {
                var state = new State
                {
                    Facts = new SignatureFact?[count],
                    Meaningless = new bool[count],
                    Index = new int[count],
                    Low = new int[count],
                    OnStack = new bool[count],
                    Stack = new int[count],
                    Frames = new Frame[count],
                };
                Array.Fill(state.Index, -1);
                return state;
            }

            public State Copy() => new()
            {
                Decided = Decided,
                Value = Value,
                Facts = (SignatureFact?[])Facts.Clone(),
                Meaningless = (bool[])Meaningless.Clone(),
                Cyclic = Cyclic,
                Index = (int[])Index.Clone(),
                Low = (int[])Low.Clone(),
                OnStack = (bool[])OnStack.Clone(),
                Stack = (int[])Stack.Clone(),
                StackCount = StackCount,
                Frames = (Frame[])Frames.Clone(),
                FrameCount = FrameCount,
                Next = Next,
                Root = Root,
                Pending = Pending,
            };
        }

        private readonly SignatureSelector _selector;
        private readonly IReadOnlyDictionary<int, SignatureFact> _lowerFacts;
        private readonly IReadOnlyDictionary<int, bool> _lowerOpen;
        private readonly int[] _keys;
        private readonly Dictionary<int, int> _local;
        private readonly int[] _links;
        private readonly Dictionary<int, int> _bit;
        private readonly int[] _linkKey;
        private readonly int[] _bitOf;
        private readonly Edge[][] _edges;
        private readonly int[][] _meaninglessReads;
        private readonly bool[] _alwaysMeaningless;
        private readonly int[][] _relevant;
        private readonly int[][] _decides;
        private readonly int[] _mark;
        private readonly long _stateUnits;
        private int _stamp;
        private int _need;
        private Mode _mode;
        private ulong _vector;
        private bool _emptyIsConsistent;

        public ClassificationSearch(
            SignatureSelector selector,
            IReadOnlyList<int> keys,
            List<int> links,
            IReadOnlyDictionary<int, SignatureFact> lowerFacts,
            IReadOnlyDictionary<int, bool> lowerOpen,
            IReadOnlySet<int> lowerMeaningless,
            StaticQueryResourceBudget.Lease structure)
        {
            _selector = selector;
            _lowerFacts = lowerFacts;
            _lowerOpen = lowerOpen;
            structure.Add(8 + 3L * keys.Count + links.Count, selector._cancellationToken);
            _keys = [.. keys.Order()];
            var count = _keys.Length;
            _local = new Dictionary<int, int>(count);
            for (var key = 0; key < count; key++)
                _local.Add(_keys[key], key);
            _links = [.. links];
            _bit = new Dictionary<int, int>(_links.Length);
            _linkKey = new int[_links.Length];
            _bitOf = new int[count];
            Array.Fill(_bitOf, -1);
            for (var bit = 0; bit < _links.Length; bit++)
            {
                _bit.Add(_links[bit], bit);
                _linkKey[bit] = _local[_links[bit]];
                _bitOf[_linkKey[bit]] = bit;
            }

            _edges = new Edge[count][];
            _meaninglessReads = new int[count][];
            _alwaysMeaningless = new bool[count];
            _relevant = new int[count][];
            _decides = new int[count][];
            _mark = new int[count];
            for (var key = 0; key < count; key++)
            {
                // EXACT SIZE, RESERVED BEFORE IT IS ALLOCATED: a first pass classifies every reference and counts what
                // this key retains, the structure lease reserves exactly that, and only then are the key's arrays
                // allocated at their final size and filled, in written order, by a second pass over the same roles. No
                // temporary buffer exists to grow ahead of its reservation or to coexist with the retained arrays. The
                // two passes are one classification of each reference, charged once.
                var references = selector._references[_keys[key]];
                Charge(1 + references.Count);
                var (edgeCount, meaninglessCount, relevantCount, decides) = (0, 0, 0, 0UL);
                for (var position = 0; position < references.Count; position++)
                {
                    var reference = references[position];
                    if (reference.Guard >= 0 && lowerMeaningless.Contains(reference.Guard) && !lowerOpen.ContainsKey(reference.Guard))
                        _alwaysMeaningless[key] = true;
                    switch (RoleOf(reference, lowerMeaningless, out _))
                    {
                        case Role.Irrelevant:
                            continue;
                        case Role.MeaninglessRead:
                            meaninglessCount++;
                            continue;
                        case Role.Edge:
                            edgeCount++;
                            break;
                    }

                    relevantCount++;
                    var guard = GuardOf(reference.Guard);
                    if (guard >= 0)
                        decides |= 1UL << guard;
                }

                // Frames across all readings share these edges. Keeping their offsets in a state makes both a
                // suspension and a copy independent of how many successors its active frames have.
                var retained = (long)edgeCount + meaninglessCount + relevantCount + BitOperations.PopCount(decides);
                structure.Add((retained + 3) / 4, selector._cancellationToken);
                Charge((long)edgeCount * BitOperations.Log2((uint)Math.Max(1, edgeCount)));
                Edge[] edges = edgeCount == 0 ? [] : new Edge[edgeCount];
                int[] meaninglessReads = meaninglessCount == 0 ? [] : new int[meaninglessCount];
                int[] relevant = relevantCount == 0 ? [] : new int[relevantCount];
                var (edgeAt, meaninglessAt, relevantAt) = (0, 0, 0);
                for (var position = 0; position < references.Count; position++)
                {
                    var reference = references[position];
                    switch (RoleOf(reference, lowerMeaningless, out var target))
                    {
                        case Role.Irrelevant:
                            continue;
                        case Role.MeaninglessRead:
                            meaninglessReads[meaninglessAt++] = GuardOf(reference.Guard);
                            continue;
                        case Role.Edge:
                            edges[edgeAt++] = new Edge(target, GuardOf(reference.Guard), lowerMeaningless.Contains(reference.Target));
                            break;
                    }

                    relevant[relevantAt++] = position;
                }

                // The adjacency by target: one deterministic sort of the written-order sequence, in place.
                Array.Sort(edges, static (left, right) => left.Target.CompareTo(right.Target));
                _edges[key] = edges;
                _meaninglessReads[key] = meaninglessReads;
                _relevant[key] = relevant;
                var bits = new int[BitOperations.PopCount(decides)];
                for (var (rest, at) = (decides, 0); rest != 0; rest &= rest - 1, at++)
                    bits[at] = BitOperations.TrailingZeroCount(rest);
                _decides[key] = bits;
            }

            _stateUnits = 6 + (48L * count + 63) / 64;
        }

        private void Charge(long work) => _selector._resources.Work(work, _selector._cancellationToken);

        private int GuardOf(int guard)
        {
            if (guard < 0)
                return Unguarded;
            if (_lowerOpen.TryGetValue(guard, out var open))
                return open ? FixedOpen : FixedClosed;
            return _bit.TryGetValue(guard, out var bit) ? bit : FixedClosed;
        }

        /// <summary>
        /// What one reference is to this table (THE RELEVANT REFERENCES): an edge to a key of the table (relevant;
        /// <paramref name="target"/> is that key's index in the table), a read of a lower key without meaning (not
        /// relevant: active, it makes the component meaningless, so no reading of it lifts; inactive, it is skipped), a
        /// lower or external callee that can lift (relevant), or one that cannot. A pure function of the table's inputs,
        /// so both passes of the construction read the same roles.
        /// </summary>
        private Role RoleOf(in SignatureEquationReference reference, IReadOnlySet<int> lowerMeaningless, out int target)
        {
            target = -1;
            if (reference.Target < 0)
                return reference.External!.AcceptsZeroSuppliedArguments ? Role.Irrelevant : Role.Lifts;
            if (_local.TryGetValue(reference.Target, out var local))
            {
                target = local;
                return Role.Edge;
            }

            if (lowerMeaningless.Contains(reference.Target))
                return Role.MeaninglessRead;
            // A lower fact is fixed for the table; a callee the table cannot read keeps its read, which fails as before.
            return _lowerFacts.TryGetValue(reference.Target, out var lower) && lower.Signature.AcceptsZeroSuppliedArguments
                ? Role.Irrelevant
                : Role.Lifts;
        }

        /// <summary>The table's rows: the table search, then subset order.</summary>
        public List<Row> Rows()
        {
            var resources = _selector._resources;
            var found = new List<(ulong Gamma, Row Row)>();
            var states = new Stack<State>();
            resources.Reserve(_stateUnits, _selector._cancellationToken);
            states.Push(State.Initial(_keys.Length));
            while (states.TryPop(out var state))
            {
                var outcome = Step(state, states);
                if (outcome == Outcome.Finished)
                    Emit(state, found, GroundednessOf);
                if (outcome != Outcome.Undecided)
                    resources.Release(_stateUnits);
            }

            return InSubsetOrder(found);
        }

        /// <summary>
        /// THE GENERIC PATH, kept as the search's reference (<see cref="EnumeratesEveryClassification"/>, a test seam): each of
        /// the 2^dimensions vectors read whole and checked as the table rule states it, and the groundedness of each consistent
        /// one by reading every counterfactual. The rows the search finds, at the cost the search avoids.
        /// </summary>
        public List<Row> EveryRow()
        {
            using var readings = _selector._resources.Temporary();
            // The reference path holds the table reading while examining one counterfactual at a time.
            readings.Add(2 * _stateUnits, _selector._cancellationToken);
            _selector.ChargeEnumeration(_links.Length);
            var all = (1UL << _links.Length) - 1;
            var found = new List<(ulong Gamma, Row Row)>();
            for (var vector = 0UL; ; vector++)
            {
                var state = Reading(vector);
                var refuted = false;
                for (var bit = 0; bit < _links.Length && !refuted; bit++)
                    refuted = state.Facts[_linkKey[bit]] is { } fact && fact.IsNonempty != ((vector & (1UL << bit)) != 0);
                if (!refuted)
                    Emit(state, found, EveryGroundedness);
                if (vector == all)
                    break;
            }

            return InSubsetOrder(found);
        }

        /// <summary>The generic path's groundedness: every nonempty support of <paramref name="vector"/>, each counterfactual read whole.</summary>
        private Groundedness EveryGroundedness(ulong vector)
        {
            _selector.ChargeEnumeration(BitOperations.PopCount(vector));
            var undetermined = false;
            for (var support = vector; support != 0; support = (support - 1) & vector)
            {
                var state = Reading(vector & ~support);
                var (refuted, withoutMeaning) = (false, false);
                for (var rest = support; rest != 0 && !refuted; rest &= rest - 1)
                {
                    var fact = state.Facts[_linkKey[BitOperations.TrailingZeroCount(rest)]];
                    refuted = fact is { IsNonempty: true };
                    withoutMeaning |= fact is null;
                }

                if (refuted)
                    continue;
                if (!withoutMeaning)
                    return Groundedness.Ungrounded;
                undetermined = true;
            }

            return undetermined ? Groundedness.Undetermined : Groundedness.Grounded;
        }

        /// <summary>The reading of one whole vector, checking nothing.</summary>
        private State Reading(ulong vector)
        {
            _selector._classificationStates++;
            Charge(1 + _keys.Length / 8);
            var mode = _mode;
            _mode = Mode.Reading;
            try
            {
                var state = State.Initial(_keys.Length);
                state.Decided = (1UL << _links.Length) - 1;
                state.Value = vector;
                return Run(state) == Outcome.Finished ? state
                    : throw new InvalidOperationException("Signature selection left a dimension of a whole classification undecided.");
            }
            finally
            {
                _mode = mode;
            }
        }

        private List<Row> InSubsetOrder(List<(ulong Gamma, Row Row)> found)
        {
            Charge((long)found.Count * (1 + BitOperations.Log2((uint)Math.Max(1, found.Count))));
            found.Sort(static (left, right) => SubsetOrder(left.Gamma, right.Gamma));
            var rows = new List<Row>(found.Count);
            foreach (var (_, row) in found)
                rows.Add(row);
            return rows;
        }

        /// <summary>
        /// Runs <paramref name="state"/> on. When it stops at an undecided dimension it is split there — the runtime class
        /// (for groundedness: the link removed from the support) continues in the state itself, the calculation class (kept)
        /// in a copy, both pushed, the runtime class on top — and the outcome is <see cref="Outcome.Undecided"/>; otherwise
        /// the state has ended, refuted or finished.
        /// </summary>
        private Outcome Step(State state, Stack<State> states)
        {
            _selector._classificationStates++;
            Charge(1);
            var outcome = Run(state);
            if (outcome != Outcome.Undecided)
                return outcome;

            var mask = 1UL << _need;
            Charge(1 + _keys.Length / 8);
            _selector._resources.Reserve(_stateUnits, _selector._cancellationToken);
            var other = state.Copy();
            other.Decided |= mask;
            other.Value |= mask;
            state.Decided |= mask;
            states.Push(other);
            states.Push(state);
            return Outcome.Undecided;
        }

        /// <summary>The rows a finished state stands for: one per choice of its free links, with its one reading.</summary>
        private void Emit(State state, List<(ulong Gamma, Row Row)> found, Func<ulong, Groundedness> groundedness)
        {
            var value = state.Decided & state.Value;
            var free = 0UL;
            for (var bit = 0; bit < _links.Length; bit++)
            {
                var mask = 1UL << bit;
                if ((state.Decided & mask) != 0)
                    continue;
                if (state.Facts[_linkKey[bit]] is { } fact)
                {
                    if (fact.IsNonempty)
                        value |= mask;
                }
                else
                {
                    free |= mask;
                }
            }

            var count = _keys.Length;
            var resources = _selector._resources;
            var token = _selector._cancellationToken;
            var anyMeaningless = Array.IndexOf(state.Meaningless, true) >= 0;
            resources.Metadata(2 + count, work: 1 + count, token);
            var facts = new Dictionary<int, SignatureFact>(count);
            for (var key = 0; key < count; key++)
            {
                if (state.Facts[key] is { } fact)
                    facts.Add(_keys[key], fact);
            }

            if (!anyMeaningless)
            {
                resources.Metadata(2 + _links.Length, work: 1 + _links.Length, token);
                found.Add((value, new Row
                {
                    Kind = RowKind.Consistent,
                    Gamma = GammaOf(value),
                    Cyclic = state.Cyclic,
                    Facts = facts,
                    Grounded = groundedness(value),
                }));
                return;
            }

            var meaningless = new HashSet<int>();
            for (var key = 0; key < count; key++)
            {
                if (state.Meaningless[key])
                    meaningless.Add(_keys[key]);
            }

            _selector.ChargeEnumeration(BitOperations.PopCount(free));
            for (var choice = free; ; choice = (choice - 1) & free)
            {
                resources.Metadata(2 + _links.Length, work: 0, token);
                found.Add((value | choice, new Row
                {
                    Kind = RowKind.Meaningless,
                    Gamma = GammaOf(value | choice),
                    Cyclic = true,
                    Facts = facts,
                    Meaningless = meaningless,
                }));
                if (choice == 0)
                    break;
            }
        }

        private HashSet<int> GammaOf(ulong vector)
        {
            var gamma = new HashSet<int>(BitOperations.PopCount(vector));
            for (var rest = vector; rest != 0; rest &= rest - 1)
                gamma.Add(_links[BitOperations.TrailingZeroCount(rest)]);
            return gamma;
        }

        /// <summary>Subset order over vectors: by size, then the vector holding the lowest position where they differ.</summary>
        private static int SubsetOrder(ulong left, ulong right)
        {
            var sizes = BitOperations.PopCount(left).CompareTo(BitOperations.PopCount(right));
            if (sizes != 0 || left == right)
                return sizes;
            var differing = left ^ right;
            return (left & differing & (~differing + 1)) != 0 ? -1 : 1;
        }

        /// <summary>
        /// The three-valued groundedness of the consistent vector <paramref name="vector"/>: the counterfactual search. A
        /// finished state stands for the supports made of the links it removed and any links it never consulted; those links
        /// change no reading, so the support of its removed links alone decides: unrefuted (the run refuted none of them), it
        /// makes the vector ungrounded unless one of them has no meaning, which leaves it undetermined. A state that removed
        /// nothing reads the vector itself, whose links are all nonempty calculations: it holds no support.
        /// </summary>
        private Groundedness GroundednessOf(ulong vector)
        {
            if (vector == 0)
            {
                // Emit asks only for consistent rows. Removing every calculation from any other row
                // gives this same reading, in which every removed link has a meaning and is empty.
                _emptyIsConsistent = true;
                return Groundedness.Grounded;
            }
            if (_emptyIsConsistent)
                return Groundedness.Ungrounded;
            var resources = _selector._resources;
            var states = new Stack<State>();
            Charge(1 + _keys.Length / 8);
            resources.Reserve(_stateUnits, _selector._cancellationToken);
            var initial = State.Initial(_keys.Length);
            initial.Decided = ((1UL << _links.Length) - 1) & ~vector;
            states.Push(initial);
            var undetermined = false;
            (_mode, _vector) = (Mode.Groundedness, vector);
            try
            {
                while (states.TryPop(out var state))
                {
                    // The removed class (runtime) continues first: a support is found sooner.
                    var outcome = Step(state, states);
                    if (outcome == Outcome.Undecided)
                        continue;
                    resources.Release(_stateUnits);
                    if (outcome == Outcome.Refuted)
                        continue;
                    var removed = state.Decided & ~state.Value & vector;
                    if (removed == 0)
                        continue;
                    var withoutMeaning = false;
                    for (var rest = removed; rest != 0; rest &= rest - 1)
                        withoutMeaning |= state.Facts[_linkKey[BitOperations.TrailingZeroCount(rest)]] is null;
                    Charge(1 + _links.Length);
                    if (!withoutMeaning)
                    {
                        while (states.TryPop(out _))
                            resources.Release(_stateUnits);
                        return Groundedness.Ungrounded;
                    }

                    undetermined = true;
                }
            }
            finally
            {
                (_mode, _vector) = (Mode.Table, 0);
            }

            return undetermined ? Groundedness.Undetermined : Groundedness.Grounded;
        }

        /// <summary>
        /// Runs the reading of <paramref name="state"/> on: Tarjan's components of the active edges, dependency-first, each
        /// settled as it completes. Stops at an undecided dimension (<see cref="_need"/>; the state resumes there), at a
        /// refutation, or when every key is read. Idempotent once finished.
        /// </summary>
        private Outcome Run(State state)
        {
            var count = _keys.Length;
            while (true)
            {
                if (state.Pending is { } pending)
                {
                    var settled = Settle(state, pending);
                    if (settled != Outcome.Finished)
                        return settled;
                    state.Pending = null;
                    continue;
                }

                if (state.FrameCount == 0)
                {
                    while (state.Root < count && state.Index[state.Root] >= 0)
                    {
                        Charge(1);
                        state.Root++;
                    }
                    if (state.Root == count)
                        return Outcome.Finished;
                    Enter(state, state.Root);
                    continue;
                }

                // Frames never grow past one per key, so the reference stays valid when a successor is entered.
                ref var frame = ref state.Frames[state.FrameCount - 1];
                Charge(1);
                var edges = _edges[frame.Node];
                if (frame.Position < edges.Length)
                {
                    var edge = edges[frame.Position];
                    var read = Consult(state, edge.Guard);
                    if (read == Read.Undecided)
                        return Outcome.Undecided;
                    frame.Position++;
                    if (read == Read.Closed)
                        continue;
                    var successor = edge.Target;
                    if (state.Index[successor] < 0)
                    {
                        Enter(state, successor);
                        continue;
                    }

                    if (state.OnStack[successor])
                        state.Low[frame.Node] = Math.Min(state.Low[frame.Node], state.Index[successor]);
                    continue;
                }

                var node = frame.Node;
                state.FrameCount--;
                if (state.FrameCount > 0)
                {
                    var parent = state.Frames[state.FrameCount - 1].Node;
                    state.Low[parent] = Math.Min(state.Low[parent], state.Low[node]);
                }

                if (state.Low[node] != state.Index[node])
                    continue;
                var size = 1;
                while (state.Stack[state.StackCount - size] != node)
                    size++;
                var members = new int[size];
                for (var at = 0; at < size; at++)
                {
                    var member = state.Stack[--state.StackCount];
                    state.OnStack[member] = false;
                    members[at] = member;
                }

                Array.Sort(members);
                Charge(size);
                state.Pending = members;
            }
        }

        private static void Enter(State state, int key)
        {
            state.Index[key] = state.Low[key] = state.Next++;
            state.Stack[state.StackCount++] = key;
            state.OnStack[key] = true;
            state.Frames[state.FrameCount++] = new Frame { Node = key };
        }

        /// <summary>
        /// A guard's class under the state. An undecided dimension whose link the run has already read is forced (a vector
        /// giving it the other class is refuted; for groundedness, only a nonempty calculation is forced to stay); any other
        /// undecided dimension stops the run (<see cref="_need"/>).
        /// </summary>
        private Read Consult(State state, int guard)
        {
            switch (guard)
            {
                case Unguarded:
                case FixedOpen:
                    return Read.Open;
                case FixedClosed:
                    return Read.Closed;
            }

            var mask = 1UL << guard;
            if ((state.Decided & mask) != 0)
                return (state.Value & mask) != 0 ? Read.Open : Read.Closed;
            if (state.Facts[_linkKey[guard]] is { } fact && (_mode != Mode.Groundedness || fact.IsNonempty))
            {
                state.Decided |= mask;
                if (fact.IsNonempty)
                    state.Value |= mask;
                return fact.IsNonempty ? Read.Open : Read.Closed;
            }

            _need = guard;
            return Read.Undecided;
        }

        /// <summary>
        /// Settles one completed component of the run exactly as a single vector's reading does: no meaning when an active
        /// read reaches a key with none (or a guard below has no class), else its one evaluation, a cycle by the closed gate
        /// and simultaneous completion. Every class the evaluation reads is decided first, so the run stops before it
        /// evaluates anything. Then each link of the component is checked against its decided class.
        /// </summary>
        private Outcome Settle(State state, int[] members)
        {
            var stamp = ++_stamp;
            foreach (var member in members)
                _mark[member] = stamp;

            var meaningless = false;
            var scanned = 0L;
            foreach (var member in members)
                meaningless |= _alwaysMeaningless[member];
            if (!meaningless)
            {
                // An edge's guard was read when its key was entered; a read of a lower key with no meaning may need a class.
                foreach (var member in members)
                {
                    foreach (var edge in _edges[member])
                    {
                        scanned++;
                        if (_mark[edge.Target] != stamp && (state.Meaningless[edge.Target] || edge.LowerMeaningless)
                            && Consult(state, edge.Guard) == Read.Open)
                            meaningless = true;
                    }

                    foreach (var guard in _meaninglessReads[member])
                    {
                        scanned++;
                        if (guard is Unguarded or FixedOpen)
                            meaningless = true;
                    }
                }
            }

            if (!meaningless)
            {
                foreach (var member in members)
                {
                    foreach (var guard in _meaninglessReads[member])
                    {
                        if (guard < 0)
                            continue;
                        var read = Consult(state, guard);
                        if (read == Read.Undecided)
                        {
                            Charge(1 + scanned);
                            return Outcome.Undecided;
                        }

                        if (read == Read.Open)
                        {
                            meaningless = true;
                            break;
                        }
                    }

                    if (meaningless)
                        break;
                }
            }

            Charge(1 + scanned);
            if (meaningless)
            {
                foreach (var member in members)
                    state.Meaningless[member] = true;
                return Outcome.Finished;
            }

            var decided = 0L;
            foreach (var member in members)
            {
                foreach (var bit in _decides[member])
                {
                    decided++;
                    if (Consult(state, bit) == Read.Undecided)
                    {
                        Charge(decided);
                        return Outcome.Undecided;
                    }
                }
            }

            Charge(decided);

            bool IsOpen(int link)
            {
                if (_lowerOpen.TryGetValue(link, out var open))
                    return open;
                // Only a reference that cannot lift reads an undecided dimension here: either class reads the same.
                return _bit.TryGetValue(link, out var bit) && (state.Decided & state.Value & (1UL << bit)) != 0;
            }

            SignatureFact Look(int target)
                => _local.TryGetValue(target, out var key) && state.Facts[key] is { } fact ? fact
                    : _lowerFacts.TryGetValue(target, out var lower) ? lower
                    : throw new InvalidOperationException("Signature selection read an equation it has not decided.");

            var selfRead = false;
            if (members.Length == 1)
            {
                foreach (var edge in _edges[members[0]])
                    selfRead |= edge.Target == members[0] && Consult(state, edge.Guard) == Read.Open;
            }

            if (members.Length == 1 && !selfRead)
            {
                var key = members[0];
                Charge(_relevant[key].Length);
                state.Facts[key] = _selector.EvaluateEquation(_keys[key], Look, IsOpen, positions: _relevant[key]);
            }
            else
            {
                // THE CLOSED GATE: every member read as declaring nothing. A cycle whose own reads then lift is a genuine
                // lifting cycle, completed from here; otherwise this evaluation is its only non-lifting fixed point.
                state.Cyclic = true;
                var component = new int[members.Length];
                for (var at = 0; at < members.Length; at++)
                    component[at] = _keys[members[at]];
                var memberSet = new HashSet<int>(component);
                SignatureFact Closed(int target) => memberSet.Contains(target) ? _selector._closed : Look(target);
                var closed = new Dictionary<int, SignatureFact>(component.Length);
                foreach (var member in members)
                {
                    Charge(_relevant[member].Length);
                    closed[_keys[member]] = _selector.EvaluateEquation(_keys[member], Closed, IsOpen, positions: _relevant[member]);
                }

                var lifts = false;
                foreach (var member in members)
                {
                    foreach (var edge in _edges[member])
                        lifts |= _mark[edge.Target] == stamp && Consult(state, edge.Guard) == Read.Open && closed[_keys[edge.Target]].Requires;
                }

                IReadOnlyDictionary<int, SignatureFact> reached = closed;
                if (lifts)
                {
                    if (_selector.Complete(component, memberSet, closed, Look, IsOpen, key => _relevant[_local[key]]) is not { } completed)
                    {
                        foreach (var member in members)
                            state.Meaningless[member] = true;
                        return Outcome.Finished;
                    }

                    reached = completed;
                }

                foreach (var (key, fact) in reached)
                    state.Facts[_local[key]] = fact;
            }

            if (_mode == Mode.Reading)
                return Outcome.Finished;
            foreach (var member in members)
            {
                var bit = _bitOf[member];
                if (bit < 0 || state.Facts[member] is not { } fact)
                    continue;
                var mask = 1UL << bit;
                if ((state.Decided & mask) == 0)
                    continue;
                var calculation = (state.Value & mask) != 0;
                // A table refutes a link that completes against its class; groundedness only a link REMOVED from the vector
                // under test that completes as a calculation (a link outside it may complete as anything).
                if (_mode == Mode.Table ? calculation != fact.IsNonempty : (_vector & mask) != 0 && !calculation && fact.IsNonempty)
                    return Outcome.Refuted;
            }

            return Outcome.Finished;
        }
    }

    /// <summary>Rule G6 over one table's rows.</summary>
    private static (SignatureSelectionOutcome Outcome, Row? Selected) Rule(IReadOnlyList<Row> rows)
    {
        Row? grounded = null;
        var groundedCount = 0;
        var undetermined = false;
        var ungrounded = false;
        var meaningless = false;
        foreach (var row in rows)
        {
            switch (row.Kind)
            {
                case RowKind.Consistent when row.Grounded == Groundedness.Grounded:
                    groundedCount++;
                    grounded ??= row;
                    break;
                case RowKind.Consistent when row.Grounded == Groundedness.Undetermined:
                    undetermined = true;
                    break;
                case RowKind.Consistent:
                    ungrounded = true;
                    break;
                case RowKind.Meaningless:
                    meaningless = true;
                    break;
            }
        }

        if (groundedCount >= 2)
            return (SignatureSelectionOutcome.Ambiguous, null);
        if (groundedCount == 1 && !undetermined)
            return (SignatureSelectionOutcome.Selected, grounded);
        if (groundedCount == 1 || undetermined)
            return (SignatureSelectionOutcome.Undetermined, null);
        if (ungrounded)
            return (SignatureSelectionOutcome.UngroundedOnly, null);
        if (meaningless)
            return (SignatureSelectionOutcome.NonSettling, null);
        return (SignatureSelectionOutcome.Contradiction, null);
    }

    // ─── the selection: a dependency-first local pass, then joint regions ─────────────────────────

    /// <summary>The candidate graph: every reference's equation target and every link it is guarded by.</summary>
    private IEnumerable<int> CandidateSuccessors(int key)
    {
        foreach (var reference in _references[key])
        {
            if (reference.Target >= 0)
                yield return reference.Target;
            if (reference.Guard >= 0)
                yield return reference.Guard;
        }
    }

    private bool ReadsNeitherItselfNorItsClass(int key)
    {
        foreach (var reference in _references[key])
        {
            if (reference.Target == key || reference.Guard == key)
                return false;
        }

        return true;
    }

    private static readonly IReadOnlySet<int> NoKeys = new HashSet<int>();

    private static readonly IReadOnlyDictionary<int, bool> NoClasses = new Dictionary<int, bool>();

    internal Selection Solve()
    {
        var components = StronglyConnected(Enumerable.Range(0, _count).ToArray(), CandidateSuccessors);
        var componentOf = new int[_count];
        for (var c = 0; c < components.Count; c++)
        {
            foreach (var key in components[c])
                componentOf[key] = c;
        }

        // LOCAL pass, dependency-first: each component over its own links, given the settled facts and classes below. A
        // settled component has OTHER READINGS when its table holds a row besides the selected one that is not refuted.
        var settledFacts = new Dictionary<int, SignatureFact>();
        var settledOpen = new Dictionary<int, bool>();
        var failed = new HashSet<int>();
        var localOutcome = new SignatureSelectionOutcome[components.Count];
        var otherReadings = new bool[components.Count];
        for (var c = 0; c < components.Count; c++)
        {
            var component = components[c];
            if (failed.Count != 0
                && component.Any(key => CandidateSuccessors(key).Any(target => componentOf[target] != c && failed.Contains(componentOf[target]))))
            {
                failed.Add(c);
                localOutcome[c] = SignatureSelectionOutcome.Blocked;
                continue;
            }

            // A lone equation that reads neither itself nor its own class has exactly one reading — its one evaluation over
            // the settled facts and classes below it, the general table's only row (consistent, vacuously grounded) — so it
            // is evaluated directly: an ordinary program pays one evaluation per equation.
            if (component.Count == 1 && ReadsNeitherItselfNorItsClass(component[0]))
            {
                var key = component[0];
                var fact = EvaluateEquation(key, target => settledFacts[target],
                    link => settledOpen.TryGetValue(link, out var open) && open);
                localOutcome[c] = SignatureSelectionOutcome.Selected;
                settledFacts[key] = fact;
                if (_isLink[key])
                    settledOpen[key] = fact.IsNonempty;
                continue;
            }

            var rows = Table(component, settledFacts, settledOpen, NoKeys);
            otherReadings[c] = rows.Count >= 2;
            var (outcome, selected) = Rule(rows);
            localOutcome[c] = outcome;
            if (outcome != SignatureSelectionOutcome.Selected)
            {
                failed.Add(c);
                continue;
            }

            foreach (var key in component)
            {
                settledFacts[key] = selected!.Facts![key];
                if (_isLink[key])
                    settledOpen[key] = selected.Facts[key].IsNonempty;
            }
        }

        var selection = new Selection();
        if (failed.Count == 0)
        {
            foreach (var (key, fact) in settledFacts)
                selection.Facts[key] = fact;
            selection.ClassificationStates = _classificationStates;
            return selection;
        }

        // JOINT regions: the unsettled components — exactly those the local pass failed: the ones that failed on their own
        // and their readers — each with its dependency cone; components whose cones meet are one region, solved over its
        // whole cone, so a reader may exclude a lower answer. Cones are downward closed, so two of them meet exactly when
        // a path of dependency edges inside the unsettled components' cones joins their components: the regions are the
        // connected components of those edges — one walk and one union-find pass, linear in the cones, every visit charged.
        var inCone = new bool[components.Count];
        var coneComponents = new List<int>();
        var root = new int[components.Count];
        _resources.Metadata(1 + components.Count / 8, work: 1, _cancellationToken);
        int Find(int c)
        {
            while (root[c] != c)
            {
                root[c] = root[root[c]];
                c = root[c];
            }

            return c;
        }

        var walk = new Stack<int>(failed);
        while (walk.TryPop(out var c))
        {
            _resources.Work(1, _cancellationToken);
            selection.RegionVisits++;
            if (inCone[c])
                continue;
            inCone[c] = true;
            root[c] = c;
            coneComponents.Add(c);
            foreach (var key in components[c])
            {
                foreach (var target in CandidateSuccessors(key))
                {
                    if (componentOf[target] != c && !inCone[componentOf[target]])
                        walk.Push(componentOf[target]);
                }
            }
        }

        foreach (var c in coneComponents)
        {
            foreach (var key in components[c])
            {
                foreach (var target in CandidateSuccessors(key))
                {
                    _resources.Work(1, _cancellationToken);
                    selection.RegionVisits++;
                    var (a, b) = (Find(c), Find(componentOf[target]));
                    if (a != b)
                        root[Math.Max(a, b)] = Math.Min(a, b);
                }
            }
        }

        // Each region: its unsettled components and its whole cone, in component (dependency-first) order.
        var regions = new SortedDictionary<int, (List<int> Members, List<int> Cone)>();
        coneComponents.Sort();
        _resources.Metadata(2L * coneComponents.Count, work: coneComponents.Count, _cancellationToken);
        foreach (var c in coneComponents)
        {
            var r = Find(c);
            if (!regions.TryGetValue(r, out var region))
                regions.Add(r, region = ([], []));
            region.Cone.Add(c);
            if (failed.Contains(c))
                region.Members.Add(c);
        }

        foreach (var (key, fact) in settledFacts)
        {
            if (!failed.Contains(componentOf[key]))
                selection.Facts[key] = fact;
        }

        foreach (var (members, cone) in regions.Values.Where(static region => region.Members.Count != 0).OrderBy(static region => region.Members[0]))
        {
            var keys = cone.SelectMany(c => components[c]).Order().ToList();
            var dimensions = LinksIn(keys, NoClasses);
            // A cone without a link has no classification to choose: each of its components has exactly one reading, so a
            // component that failed on its own did so because it does not settle — and the joint reading is the same.
            var (outcome, chosen) = dimensions.Count == 0
                ? (SignatureSelectionOutcome.NonSettling, (Row?)null)
                : SolveRegion(members, cone, components, failed, otherReadings, settledFacts, settledOpen, dimensions);
            if (outcome == SignatureSelectionOutcome.Selected)
            {
                foreach (var c in members)
                {
                    foreach (var key in components[c])
                        selection.Facts[key] = chosen!.Facts![key];
                }

                continue;
            }

            // A region is reported at the components that failed on their own; a reader that failed only through them
            // is not reported again (A1's precedent: dependent lifts are suppressed, not cascaded).
            var own = members.Where(c => localOutcome[c] != SignatureSelectionOutcome.Blocked).ToList();
            if (outcome == SignatureSelectionOutcome.NonSettling)
            {
                // No reading at all: each component that failed on its own is reported for its OWN failure — a cycle of its
                // members that does not settle, or its own links' category — never as one group with components whose cones
                // merely meet.
                foreach (var c in own)
                {
                    var ownLinks = localOutcome[c] == SignatureSelectionOutcome.NonSettling ? [] : LinksIn(components[c], NoClasses);
                    selection.Refusals.Add(([.. components[c].Order()], ownLinks, localOutcome[c]));
                }

                continue;
            }

            var reported = own.SelectMany(c => components[c]).Order().ToList();
            selection.Refusals.Add((reported.Count == 0 ? members.SelectMany(c => components[c]).Order().ToList() : reported,
                dimensions, outcome));
        }

        selection.ClassificationStates = _classificationStates;
        return selection;
    }

    /// <summary>
    /// Rule G6 over one joint region whose cone has a link (<paramref name="dimensions"/>, the cone's links), in two phases
    /// that share one table per component and exact table inputs. PHASE 1 carries every locally settled component of the
    /// cone by its selected reading alone and enumerates the failed components (<paramref name="members"/>,
    /// dependency-first) over it. PHASE 2, only to decide the category of a refusal phase 1 could not decide, enumerates
    /// the whole cone.
    ///
    /// <para>Why phase 1 is exact. A component the local pass settled reads only settled components (a reader of a failed
    /// one is Blocked, so failed itself), so along the selected readings below it its table is its local table, and the
    /// equation and seal memos give it the very same facts. Its selected row is its only grounded row and it has no
    /// undetermined row, so an alternative of the full enumeration that carries another of its rows is ungrounded or
    /// meaningless, and stays so: Ungrounded never becomes grounded again, and the meaningless set never shrinks. Every
    /// alternative carried from it adds only an ungrounded or a meaningless row. The full enumeration's grounded rows and
    /// undetermined rows are therefore exactly phase 1's, and it holds every phase-1 row, so Selected, Ambiguous,
    /// Undetermined and UngroundedOnly are final. NonSettling and Contradiction are final too when no settled component of
    /// the cone has another reading at all: then no other alternative exists. Otherwise an ungrounded or meaningless row
    /// phase 1 did not carry can change that category, and phase 2 decides it.</para>
    /// </summary>
    private (SignatureSelectionOutcome Outcome, Row? Chosen) SolveRegion(
        List<int> members,
        List<int> cone,
        List<List<int>> components,
        HashSet<int> failed,
        bool[] otherReadings,
        Dictionary<int, SignatureFact> settledFacts,
        Dictionary<int, bool> settledOpen,
        IReadOnlyList<int> dimensions)
    {
        var tables = new Dictionary<(int Component, string Key), List<Row>>();
        var settledCone = cone.Where(c => !failed.Contains(c)).ToList();
        var settled = SettledReading(settledCone, components, settledFacts, settledOpen);
        var reading = Rule(AlternativeRows(Alternatives(settled, members, components, tables), dimensions));
        if (reading.Outcome is not (SignatureSelectionOutcome.NonSettling or SignatureSelectionOutcome.Contradiction)
            || !settledCone.Any(c => otherReadings[c]))
            return reading;

        var unclassified = new Alternative
        {
            Gamma = ImmutableHashSet<int>.Empty,
            Dimensions = ImmutableHashSet<int>.Empty,
            Assigned = ImmutableDictionary<int, bool>.Empty,
            Facts = ImmutableDictionary<int, SignatureFact>.Empty,
            Meaningless = ImmutableHashSet<int>.Empty,
            Grounded = Groundedness.Grounded,
        };
        return Rule(AlternativeRows(Alternatives(unclassified, cone, components, tables), dimensions));
    }

    /// <summary>
    /// The one alternative that carries settled components by their selected readings: their facts (the very objects the
    /// local pass settled), their own links as decided dimensions, and those of them that are calculations as the vector
    /// — what the full enumeration carries along their selected rows, charged as each of those carried alternatives is.
    /// </summary>
    private Alternative SettledReading(
        IReadOnlyList<int> settledCone,
        List<List<int>> components,
        Dictionary<int, SignatureFact> settledFacts,
        Dictionary<int, bool> settledOpen)
    {
        var facts = ImmutableDictionary.CreateBuilder<int, SignatureFact>();
        var gamma = ImmutableHashSet.CreateBuilder<int>();
        var dimensions = ImmutableHashSet.CreateBuilder<int>();
        foreach (var c in settledCone)
        {
            var component = components[c];
            var links = LinksIn(component, NoClasses);
            var calculations = links.Where(link => settledOpen.TryGetValue(link, out var open) && open).ToList();
            var added = calculations.Count + links.Count + component.Count;
            _resources.Metadata(4 + added, work: 1 + added, _cancellationToken);
            foreach (var key in component)
                facts.Add(key, settledFacts[key]);
            dimensions.UnionWith(links);
            gamma.UnionWith(calculations);
        }

        return new Alternative
        {
            Gamma = gamma.ToImmutable(),
            Dimensions = dimensions.ToImmutable(),
            Assigned = ImmutableDictionary<int, bool>.Empty,
            Facts = facts.ToImmutable(),
            Meaningless = ImmutableHashSet<int>.Empty,
            Grounded = Groundedness.Grounded,
        };
    }

    /// <summary>
    /// One partial classification carried through a region's cone. PERSISTENT: a carried alternative shares the state below
    /// it and pays only for what its component adds, so a long cone costs what it adds, never a copy per step.
    /// </summary>
    private sealed class Alternative
    {
        public required ImmutableHashSet<int> Gamma;
        public required ImmutableHashSet<int> Dimensions;
        public required ImmutableDictionary<int, bool> Assigned;
        public required ImmutableDictionary<int, SignatureFact> Facts;
        public required ImmutableHashSet<int> Meaningless;
        public required Groundedness Grounded;
        public bool Cyclic;
    }

    /// <summary>
    /// Alternative-carrying stratification over a region's dependency cone, from <paramref name="initial"/> through the
    /// components <paramref name="order"/> names (dependency-first; every component they read is in the initial
    /// alternative or earlier in the order): every partial vector that is consistent or meaningless so far is carried; the
    /// class of a lower link that is meaningless in an alternative is a free choice of the vector, branched once where a
    /// later component observes it. A component's table is built once per exact inputs in <paramref name="tables"/>,
    /// which the region's phases share. Every carried alternative is charged for the entries it adds before it is built.
    /// </summary>
    private List<Alternative> Alternatives(
        Alternative initial,
        IReadOnlyList<int> order,
        List<List<int>> components,
        Dictionary<(int Component, string Key), List<Row>> tables)
    {
        var alternatives = new List<Alternative> { initial };
        foreach (var c in order)
        {
            var component = components[c];
            var members = new HashSet<int>(component);
            var componentLinks = LinksIn(component, NoClasses);
            var observed = component.SelectMany(key => _references[key])
                .Where(reference => reference.Guard >= 0 && !members.Contains(reference.Guard))
                .Select(static reference => reference.Guard).Distinct().Order().ToList();
            var reads = component.SelectMany(CandidateSuccessors).Where(target => !members.Contains(target)).Distinct().Order().ToList();
            var next = new List<Alternative>();
            foreach (var alternative in alternatives)
            {
                var free = observed.Where(link => alternative.Meaningless.Contains(link)
                    && !alternative.Assigned.ContainsKey(link) && !alternative.Dimensions.Contains(link)).ToList();
                ChargeEnumeration(free.Count);
                for (var bits = 0L; bits < 1L << free.Count; bits++)
                {
                    // The choice's classes, and the table key built from every read and observed link below.
                    _resources.Metadata(free.Count, work: free.Count + reads.Count + observed.Count, _cancellationToken);
                    var assigned = alternative.Assigned;
                    for (var i = 0; i < free.Count; i++)
                        assigned = assigned.SetItem(free[i], (bits & (1L << i)) != 0);
                    var open = new Dictionary<int, bool>();
                    foreach (var target in reads)
                    {
                        if (_isLink[target] && alternative.Facts.TryGetValue(target, out var fact))
                            open[target] = fact.IsNonempty;
                    }

                    foreach (var link in observed)
                    {
                        if (alternative.Dimensions.Contains(link))
                            open[link] = alternative.Gamma.Contains(link);
                        if (assigned.TryGetValue(link, out var choice))
                            open[link] = choice;
                    }

                    var memoKey = (c, Key: TableKey(reads, alternative, open));
                    if (!tables.TryGetValue(memoKey, out var rows))
                    {
                        _resources.Metadata(2 + (memoKey.Key.Length + 31L) / 32, work: 0, _cancellationToken);
                        tables[memoKey] = rows = Table(component, alternative.Facts, open, alternative.Meaningless);
                    }
                    foreach (var row in rows)
                    {
                        var added = row.Gamma.Count + componentLinks.Count + component.Count;
                        _resources.Metadata(4 + added, work: 1 + added, _cancellationToken);
                        var carried = new Alternative
                        {
                            Gamma = alternative.Gamma.Union(row.Gamma),
                            Dimensions = alternative.Dimensions.Union(componentLinks),
                            Assigned = assigned,
                            Facts = alternative.Facts,
                            Meaningless = alternative.Meaningless,
                            Grounded = alternative.Grounded,
                            Cyclic = alternative.Cyclic || row.Cyclic,
                        };
                        if (row.Kind == RowKind.Consistent)
                        {
                            carried.Facts = alternative.Facts.SetItems(row.Facts!);
                            carried.Grounded = alternative.Grounded == Groundedness.NotApplicable ? Groundedness.NotApplicable
                                : alternative.Grounded == Groundedness.Ungrounded || row.Grounded == Groundedness.Ungrounded ? Groundedness.Ungrounded
                                : alternative.Grounded == Groundedness.Undetermined || row.Grounded == Groundedness.Undetermined ? Groundedness.Undetermined
                                : Groundedness.Grounded;
                        }
                        else
                        {
                            // The row's own reading holds the facts of the keys that have a meaning: the table's inputs are
                            // exactly this table key's, so evaluating the vector again would give the same objects.
                            var facts = alternative.Facts.ToBuilder();
                            foreach (var key in component)
                            {
                                if (!row.Meaningless!.Contains(key) && row.Facts!.TryGetValue(key, out var fact))
                                    facts[key] = fact;
                            }

                            carried.Facts = facts.ToImmutable();
                            carried.Meaningless = alternative.Meaningless.Union(row.Meaningless!);
                            carried.Grounded = Groundedness.NotApplicable;
                        }

                        next.Add(carried);
                    }
                }
            }

            alternatives = next;
        }

        return alternatives;
    }

    /// <summary>
    /// What a component's table depends on: each read target's EXACT fact (its <see cref="SignatureFact.Id"/>, never a
    /// hash) or meaninglessness, and the observed link classes.
    /// </summary>
    private static string TableKey(IReadOnlyList<int> reads, Alternative alternative, Dictionary<int, bool> open)
    {
        var builder = new System.Text.StringBuilder();
        foreach (var target in reads)
        {
            builder.Append(target).Append(':');
            if (alternative.Meaningless.Contains(target))
                builder.Append('u');
            else if (alternative.Facts.TryGetValue(target, out var fact))
                builder.Append(fact.Id);
            builder.Append(';');
        }

        // Every class is a read (a target or guard), and reads already have canonical order.
        foreach (var link in reads)
        {
            if (open.TryGetValue(link, out var value))
                builder.Append('o').Append(link).Append(value ? '+' : '-');
        }
        return builder.ToString();
    }

    private List<Row> AlternativeRows(IReadOnlyList<Alternative> alternatives, IReadOnlyList<int> dimensions)
    {
        var rows = new List<Row>(alternatives.Count);
        foreach (var alternative in alternatives)
        {
            _resources.Metadata(1 + alternative.Gamma.Count + dimensions.Count,
                work: 1 + alternative.Gamma.Count + alternative.Assigned.Count + dimensions.Count, _cancellationToken);
            var gamma = new HashSet<int>(alternative.Gamma);
            foreach (var (link, choice) in alternative.Assigned)
            {
                if (choice)
                    gamma.Add(link);
            }

            foreach (var link in dimensions)
            {
                if (alternative.Facts.TryGetValue(link, out var fact) && fact.IsNonempty)
                    gamma.Add(link);
            }

            gamma.IntersectWith(dimensions);
            rows.Add(alternative.Meaningless.Count != 0
                ? new Row { Kind = RowKind.Meaningless, Gamma = gamma, Cyclic = true, Meaningless = alternative.Meaningless }
                : new Row { Kind = RowKind.Consistent, Gamma = gamma, Grounded = alternative.Grounded, Facts = alternative.Facts, Cyclic = alternative.Cyclic });
        }

        return rows;
    }

    // ─── iterative Tarjan, dependency-first ───────────────────────────────────────────────────────

    /// <summary>Strongly connected components of the graph over <paramref name="keys"/>, dependencies first, without host recursion.</summary>
    private List<List<int>> StronglyConnected(IReadOnlyList<int> keys, Func<int, IEnumerable<int>> successors)
    {
        var index = new Dictionary<int, int>();
        var low = new Dictionary<int, int>();
        var onStack = new HashSet<int>();
        var stack = new Stack<int>();
        var components = new List<List<int>>();
        var next = 0;
        var ordered = keys.Order().ToArray();
        var inKeys = new HashSet<int>(ordered);
        IEnumerator<int> Successors(int node)
            => successors(node).Where(inKeys.Contains).Distinct().Order().GetEnumerator();
        foreach (var root in ordered)
        {
            if (index.ContainsKey(root))
                continue;
            var work = new Stack<(int Node, IEnumerator<int> Successors)>();
            index[root] = low[root] = next++;
            stack.Push(root);
            onStack.Add(root);
            work.Push((root, Successors(root)));
            while (work.Count > 0)
            {
                _resources.Work(0, _cancellationToken);
                var (node, enumerator) = work.Peek();
                if (enumerator.MoveNext())
                {
                    var successor = enumerator.Current;
                    if (!index.ContainsKey(successor))
                    {
                        index[successor] = low[successor] = next++;
                        stack.Push(successor);
                        onStack.Add(successor);
                        work.Push((successor, Successors(successor)));
                    }
                    else if (onStack.Contains(successor))
                    {
                        low[node] = Math.Min(low[node], index[successor]);
                    }

                    continue;
                }

                work.Pop();
                if (work.Count > 0)
                {
                    var parent = work.Peek().Node;
                    low[parent] = Math.Min(low[parent], low[node]);
                }

                if (low[node] == index[node])
                {
                    var component = new List<int>();
                    int member;
                    do
                    {
                        member = stack.Pop();
                        onStack.Remove(member);
                        component.Add(member);
                    }
                    while (member != node);
                    component.Sort();
                    components.Add(component);
                }
            }
        }

        return components;
    }
}
