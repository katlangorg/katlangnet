using System.Collections.Immutable;

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
/// cone. A link-free component has exactly one vector, so link-free programs cost one evaluation per equation (plus
/// the closed gate of each cycle). Work and storage are charged to the operation's ledger
/// (<see cref="StaticQueryResourceBudget"/>): exhaustion is <see cref="StaticQueryLimitExceededException"/>,
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
    // then sees one list, which the rewrite checks by reference, however many readings computed it.
    private readonly List<(IReadOnlyList<(int Reference, CallableSignature Signature)> Lifted, SignatureFact Fact)>?[] _composed;
    private readonly List<(SignatureFact[] Settled, IReadOnlyDictionary<int, SignatureFact> Published)>?[] _sealed;
    private readonly Dictionary<IReadOnlyList<ParameterPattern>, long> _patternNodes = new(ReferenceEqualityComparer.Instance);

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
        _composed = new List<(IReadOnlyList<(int, CallableSignature)>, SignatureFact)>?[_count];
        _sealed = new List<(SignatureFact[], IReadOnlyDictionary<int, SignatureFact>)>?[_count];
    }

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
    }

    // ─── one equation, one vector ─────────────────────────────────────────────────────────────────

    private SignatureFact EvaluateEquation(int equation, Func<int, SignatureFact> look, Func<int, bool> isOpen)
    {
        _resources.Work(1, _cancellationToken);
        var lifted = Lifted(equation, look, isOpen);
        var known = _composed[equation] ??= new(1);
        foreach (var (inputs, fact) in known)
        {
            _resources.Work(1 + inputs.Count, _cancellationToken);
            if (SameInputs(inputs, lifted))
                return fact;
        }

        var composed = _compose(equation, lifted);
        known.Add((lifted, composed));
        return composed;
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

    /// <summary>The LIFTING RULE: the callees a reference lifts under these facts, in written order, each identity once.</summary>
    private IReadOnlyList<(int Reference, CallableSignature Signature)> Lifted(int equation, Func<int, SignatureFact> look, Func<int, bool> isOpen)
    {
        List<(int, CallableSignature)>? lifted = null;
        HashSet<object>? seen = null;
        var references = _references[equation];
        for (var index = 0; index < references.Count; index++)
        {
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

    private sealed class Evaluation
    {
        public readonly Dictionary<int, SignatureFact> Facts = [];
        public readonly HashSet<int> Meaningless = [];
        public bool Cyclic;
    }

    /// <summary>
    /// The reading of <paramref name="keys"/> under the vector <paramref name="gamma"/>, given lower facts and link classes and the
    /// lower keys that have no meaning: dependency-first, a cyclic component by the closed gate.
    /// </summary>
    private Evaluation Evaluate(
        IReadOnlyList<int> keys,
        IReadOnlySet<int> gamma,
        IReadOnlyDictionary<int, SignatureFact> lowerFacts,
        IReadOnlyDictionary<int, bool> lowerOpen,
        IReadOnlySet<int> lowerMeaningless)
    {
        _resources.Metadata(1 + keys.Count, work: 0, _cancellationToken);
        var inKeys = new HashSet<int>(keys);
        var result = new Evaluation();

        bool IsOpen(int link) => lowerOpen.TryGetValue(link, out var open) ? open : gamma.Contains(link);

        SignatureFact Look(int target)
            => result.Facts.TryGetValue(target, out var fact) ? fact
                : lowerFacts.TryGetValue(target, out var lower) ? lower
                : throw new InvalidOperationException("Signature selection read an equation it has not decided.");

        IEnumerable<int> Active(int key)
        {
            foreach (var reference in _references[key])
            {
                if (reference.Target >= 0 && (reference.Guard < 0 || IsOpen(reference.Guard)))
                    yield return reference.Target;
            }
        }

        foreach (var component in StronglyConnected(keys, key => Active(key).Where(inKeys.Contains)))
        {
            var members = new HashSet<int>(component);
            var meaningless = false;
            foreach (var key in component)
            {
                foreach (var target in Active(key))
                {
                    if (!members.Contains(target) && (result.Meaningless.Contains(target) || lowerMeaningless.Contains(target)))
                        meaningless = true;
                }

                foreach (var reference in _references[key])
                {
                    if (reference.Guard >= 0 && lowerMeaningless.Contains(reference.Guard) && !lowerOpen.ContainsKey(reference.Guard))
                        meaningless = true;
                }
            }

            if (meaningless)
            {
                result.Meaningless.UnionWith(component);
                continue;
            }

            if (component.Count == 1 && !Active(component[0]).Contains(component[0]))
            {
                result.Facts[component[0]] = EvaluateEquation(component[0], Look, IsOpen);
                continue;
            }

            // THE CLOSED GATE: every member read as declaring nothing. A cycle whose own reads then lift is a genuine
            // lifting cycle, completed from here; otherwise this evaluation is its only non-lifting fixed point.
            result.Cyclic = true;
            SignatureFact Closed(int target) => members.Contains(target) ? _closed : Look(target);
            var closed = new Dictionary<int, SignatureFact>(component.Count);
            foreach (var key in component)
                closed[key] = EvaluateEquation(key, Closed, IsOpen);

            var lifts = false;
            foreach (var key in component)
            {
                foreach (var target in Active(key))
                {
                    if (members.Contains(target) && closed[target].Requires)
                        lifts = true;
                }
            }

            IReadOnlyDictionary<int, SignatureFact> reached = closed;
            if (lifts)
            {
                if (Complete(component, members, closed, Look, IsOpen) is not { } completed)
                {
                    result.Meaningless.UnionWith(component);
                    continue;
                }

                reached = completed;
            }

            foreach (var (key, fact) in reached)
                result.Facts[key] = fact;
        }

        return result;
    }

    // ─── recursive completion ─────────────────────────────────────────────────────────────────────

    /// <summary>
    /// SIMULTANEOUS COMPLETION (X-04 plain A-agree): round k+1 recomposes every member from round k's facts by the ONE
    /// composition law, with lower and external facts fixed, starting from the closed gate. The state is every member's
    /// full ordered pattern tree and X-02 flag. Two equal successive states settle, and the reached state is the answer: no
    /// other fixed point is sought and an intermediate capture or requirement may disappear. A state equal to an earlier
    /// one at a greater distance proves the rounds never settle (null). Composition is a pure function of the state, so
    /// that is exact; the earlier state is kept by Brent's rule, so the detector holds at most two snapshots however long
    /// the rounds run. Every round's lists stay in the run's template interner, so each composition is charged, in work and
    /// storage, before it runs, and each comparison per node. Exhausting the ledger is never non-settling. The settled state
    /// is sealed (<see cref="SealCompletion"/>) before any reader composes from it.
    /// </summary>
    private IReadOnlyDictionary<int, SignatureFact>? Complete(
        IReadOnlyList<int> component,
        HashSet<int> members,
        Dictionary<int, SignatureFact> closed,
        Func<int, SignatureFact> look,
        Func<int, bool> isOpen)
    {
        var previous = closed;
        var saved = closed;
        var savedAge = 0L;
        var window = 1L;
        while (true)
        {
            var current = new Dictionary<int, SignatureFact>(component.Count);
            foreach (var key in component)
            {
                ChargeComposition(key, previous, look, isOpen);
                var read = previous;
                current[key] = EvaluateEquation(key, target => members.Contains(target) ? read[target] : look(target), isOpen);
            }

            if (SameState(component, previous, current))
                return Sealed(component, current, members, look, isOpen);

            savedAge++;
            if (SameState(component, saved, current))
                return null;
            if (savedAge == window)
            {
                saved = current;
                savedAge = 0;
                window *= 2;
            }

            previous = current;
        }
    }

    /// <summary>The sealed facts of a settled state: sealed once for its exact facts, so every reading shares one result.</summary>
    private IReadOnlyDictionary<int, SignatureFact> Sealed(
        IReadOnlyList<int> component,
        Dictionary<int, SignatureFact> settled,
        HashSet<int> members,
        Func<int, SignatureFact> look,
        Func<int, bool> isOpen)
    {
        var known = _sealed[component[0]] ??= new(1);
        var facts = new SignatureFact[component.Count];
        for (var index = 0; index < facts.Length; index++)
            facts[index] = settled[component[index]];
        foreach (var (inputs, published) in known)
        {
            _resources.Work(1 + facts.Length, _cancellationToken);
            if (inputs.AsSpan().SequenceEqual(facts))
                return published;
        }

        var result = _seal(component, settled, (equation, read) => Lifted(equation,
            target => members.Contains(target) ? read[target] : look(target), isOpen));
        known.Add((facts, result));
        return result;
    }

    /// <summary>
    /// Charges one member's composition before it runs, in work and storage: its references and every node of every active
    /// callee, in this round, lower or fixed, since the merge builds a list from them before anything is filtered. A list's
    /// nodes are counted once, one charged step per node.
    /// </summary>
    private void ChargeComposition(int equation, Dictionary<int, SignatureFact> round, Func<int, SignatureFact> look, Func<int, bool> isOpen)
    {
        var references = _references[equation];
        var units = 1L + references.Count;
        for (var index = 0; index < references.Count; index++)
        {
            var reference = references[index];
            if (reference.Guard >= 0 && !isOpen(reference.Guard))
                continue;
            var signature = reference.Target < 0 ? reference.External!
                : round.TryGetValue(reference.Target, out var fact) ? fact.Signature
                : look(reference.Target).Signature;
            units += NodesOf(signature.ParameterPatterns);
        }

        _resources.Metadata(units, work: units, _cancellationToken);
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

    /// <summary>Whether two rounds have the same full state: every member's X-02 flag and exact ordered pattern tree.</summary>
    private bool SameState(IReadOnlyList<int> component, Dictionary<int, SignatureFact> left, Dictionary<int, SignatureFact> right)
    {
        foreach (var key in component)
        {
            if (left[key].Violation != right[key].Violation
                || !SamePatterns(left[key].Patterns, right[key].Patterns))
                return false;
        }

        return true;
    }

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

    private enum RowKind : byte { Refuted, Meaningless, Consistent }

    private enum Groundedness : byte { Grounded, Undetermined, Ungrounded, NotApplicable }

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

    /// <summary>Every subset, by size then lexicographically by position: deterministic, never declaration-ordered.</summary>
    private static IEnumerable<HashSet<int>> Subsets(IReadOnlyList<int> items)
    {
        for (var size = 0; size <= items.Count; size++)
        {
            var positions = new int[size];
            for (var i = 0; i < size; i++)
                positions[i] = i;
            while (true)
            {
                var set = new HashSet<int>(size);
                foreach (var position in positions)
                    set.Add(items[position]);
                yield return set;
                var advance = size - 1;
                while (advance >= 0 && positions[advance] == items.Count - size + advance)
                    advance--;
                if (advance < 0)
                    break;
                positions[advance]++;
                for (var j = advance + 1; j < size; j++)
                    positions[j] = positions[j - 1] + 1;
            }
        }
    }

    /// <summary>Charges the 2^<paramref name="dimensions"/> vectors of a table before any is evaluated.</summary>
    private void ChargeEnumeration(int dimensions)
    {
        if (dimensions >= 62)
        {
            _resources.Fail();
            throw new StaticQueryLimitExceededException(
                $"Signature selection would enumerate 2^{dimensions} classifications of .Algorithm links.");
        }

        _resources.Work(1L << dimensions, _cancellationToken);
    }

    private List<Row> Table(
        IReadOnlyList<int> keys,
        IReadOnlyDictionary<int, SignatureFact> lowerFacts,
        IReadOnlyDictionary<int, bool> lowerOpen,
        IReadOnlySet<int> lowerMeaningless)
    {
        var links = LinksIn(keys, lowerOpen);
        ChargeEnumeration(links.Count);
        var rows = new List<Row>();
        foreach (var gamma in Subsets(links))
        {
            _resources.Metadata(1 + links.Count, work: 0, _cancellationToken);
            var evaluation = Evaluate(keys, gamma, lowerFacts, lowerOpen, lowerMeaningless);
            var refuted = false;
            foreach (var link in links)
            {
                if (evaluation.Facts.TryGetValue(link, out var fact) && fact.IsNonempty != gamma.Contains(link))
                {
                    refuted = true;
                    break;
                }
            }

            if (refuted)
            {
                rows.Add(new Row { Kind = RowKind.Refuted, Gamma = gamma, Cyclic = evaluation.Cyclic });
            }
            else if (evaluation.Meaningless.Count != 0)
            {
                rows.Add(new Row
                {
                    Kind = RowKind.Meaningless,
                    Gamma = gamma,
                    Cyclic = true,
                    Meaningless = new HashSet<int>(evaluation.Meaningless),
                });
            }
            else
            {
                var facts = new Dictionary<int, SignatureFact>(keys.Count);
                foreach (var key in keys)
                    facts[key] = evaluation.Facts[key];
                rows.Add(new Row
                {
                    Kind = RowKind.Consistent,
                    Gamma = gamma,
                    Cyclic = evaluation.Cyclic,
                    Facts = facts,
                    Grounded = GroundednessOf(keys, gamma, lowerFacts, lowerOpen, lowerMeaningless),
                });
            }
        }

        return rows;
    }

    /// <summary>
    /// Three-valued groundedness of a consistent vector: every nonempty set T of its calculation links must be REFUTED —
    /// some member of T still evaluates to a nonempty calculation without T's support. A set whose members all evaluate
    /// to empty there is unfounded (ungrounded); one with a meaningless member is undetermined.
    /// </summary>
    private Groundedness GroundednessOf(
        IReadOnlyList<int> keys,
        HashSet<int> gamma,
        IReadOnlyDictionary<int, SignatureFact> lowerFacts,
        IReadOnlyDictionary<int, bool> lowerOpen,
        IReadOnlySet<int> lowerMeaningless)
    {
        ChargeEnumeration(gamma.Count);
        var undetermined = false;
        foreach (var support in Subsets([.. gamma.Order()]))
        {
            if (support.Count == 0)
                continue;
            var counterfactual = new HashSet<int>(gamma);
            counterfactual.ExceptWith(support);
            var evaluation = Evaluate(keys, counterfactual, lowerFacts, lowerOpen, lowerMeaningless);
            var refuted = false;
            var anyMeaningless = false;
            foreach (var link in support)
            {
                if (!evaluation.Facts.TryGetValue(link, out var fact))
                {
                    anyMeaningless = true;
                }
                else if (fact.IsNonempty)
                {
                    refuted = true;
                    break;
                }
            }

            if (refuted)
                continue;
            if (!anyMeaningless)
                return Groundedness.Ungrounded;
            undetermined = true;
        }

        return undetermined ? Groundedness.Undetermined : Groundedness.Grounded;
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

        // LOCAL pass, dependency-first: each component over its own links, given the settled facts and classes below.
        var settledFacts = new Dictionary<int, SignatureFact>();
        var settledOpen = new Dictionary<int, bool>();
        var failed = new HashSet<int>();
        var localOutcome = new SignatureSelectionOutcome[components.Count];
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

            var (outcome, selected) = Rule(Table(component, settledFacts, settledOpen, NoKeys));
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
                : Rule(AlternativeRows(Alternatives(cone.Select(c => (IReadOnlyList<int>)components[c]).ToList()), dimensions));
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

        return selection;
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
    /// Alternative-carrying stratification over a region's dependency cone (its components, dependency-first): every
    /// partial vector that is consistent or meaningless so far is carried; the class of a lower link that is
    /// meaningless in an alternative is a free choice of the vector, branched once where a later component observes it.
    /// Every carried alternative is charged for the entries it adds before it is built.
    /// </summary>
    private List<Alternative> Alternatives(IReadOnlyList<IReadOnlyList<int>> components)
    {
        var alternatives = new List<Alternative>
        {
            new()
            {
                Gamma = ImmutableHashSet<int>.Empty,
                Dimensions = ImmutableHashSet<int>.Empty,
                Assigned = ImmutableDictionary<int, bool>.Empty,
                Facts = ImmutableDictionary<int, SignatureFact>.Empty,
                Meaningless = ImmutableHashSet<int>.Empty,
                Grounded = Groundedness.Grounded,
            },
        };
        foreach (var component in components)
        {
            var members = new HashSet<int>(component);
            var componentLinks = LinksIn(component, NoClasses);
            var observed = component.SelectMany(key => _references[key])
                .Where(reference => reference.Guard >= 0 && !members.Contains(reference.Guard))
                .Select(static reference => reference.Guard).Distinct().Order().ToList();
            var reads = component.SelectMany(CandidateSuccessors).Where(target => !members.Contains(target)).Distinct().Order().ToList();
            var next = new List<Alternative>();
            var tables = new Dictionary<string, List<Row>>(StringComparer.Ordinal);
            foreach (var alternative in alternatives)
            {
                var free = observed.Where(link => alternative.Meaningless.Contains(link)
                    && !alternative.Assigned.ContainsKey(link) && !alternative.Dimensions.Contains(link)).ToList();
                ChargeEnumeration(free.Count);
                for (var bits = 0L; bits < 1L << free.Count; bits++)
                {
                    _resources.Metadata(free.Count, work: 0, _cancellationToken);
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

                    var memoKey = TableKey(reads, alternative, open);
                    if (!tables.TryGetValue(memoKey, out var rows))
                        tables[memoKey] = rows = Table(component, alternative.Facts, open, alternative.Meaningless);
                    foreach (var row in rows)
                    {
                        if (row.Kind == RowKind.Refuted)
                            continue;
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
                            var defined = Evaluate(component, row.Gamma, alternative.Facts, open, alternative.Meaningless);
                            var facts = alternative.Facts.ToBuilder();
                            foreach (var key in component)
                            {
                                if (!row.Meaningless!.Contains(key) && defined.Facts.TryGetValue(key, out var fact))
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

        foreach (var (link, value) in open.OrderBy(static pair => pair.Key))
            builder.Append('o').Append(link).Append(value ? '+' : '-');
        return builder.ToString();
    }

    private List<Row> AlternativeRows(IReadOnlyList<Alternative> alternatives, IReadOnlyList<int> dimensions)
    {
        var rows = new List<Row>(alternatives.Count);
        foreach (var alternative in alternatives)
        {
            _resources.Metadata(1 + alternative.Gamma.Count + dimensions.Count, work: 1, _cancellationToken);
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
