namespace KatLang;

internal static partial class ImplicitArgumentResolver
{
    /// <summary>
    /// Prepares a settled recursive completion's final facts (R1, owner direction 2026-11-05), inside the selection and
    /// charged to its ledger. The settled state fixes STRUCTURE; which round first produced a capture record means nothing,
    /// so origins are derived here from the FIRST-PROVIDER LAW: an own capture is its own origin; any other capture's origin
    /// is that of the first lifted, non-inert callee binding its name. A chain ending at an own capture or at a fixed
    /// callee's record is DETERMINED and takes that record (FE-3 record sharing, META and X-02 copies keeping their
    /// original). A chain that closes on itself has no derivable single origin, so the cycle and every chain entering it
    /// share one GENERATED record (<see cref="ParameterCycleOrigin"/>); exactly one reachable source collapses to it.
    ///
    /// <para>The final lists are then recomposed from themselves by the real composition law: the result must have the
    /// same structure and the same origin content, or this pass is defective. Its composition, read from the final
    /// signatures, is what <see cref="RequireSelectedComposition"/> compares by reference. Nothing here outlives the
    /// returned facts or writes to the tree, so a selection that is refused or cancelled publishes no origin, and one
    /// vector's origins cannot reach another's.</para>
    /// </summary>
    private static IReadOnlyDictionary<int, SignatureFact> SealCompletion(
        IReadOnlyList<int> component,
        IReadOnlyDictionary<int, SignatureFact> settled,
        SignatureSelector.LiftedFrom liftedFrom,
        SignatureAnalysis.Body[] equations,
        IReadOnlyList<SignatureEquationReference>[] references,
        SignatureSelector.Compose compose,
        SignatureAnalysis analysis,
        ResolutionRun run)
    {
        using var seal = new CycleOriginSeal(component, settled, liftedFrom, equations, references, analysis, run);
        return seal.Run(compose);
    }

    /// <summary>The working state of one <see cref="SealCompletion"/>: confined to that call, never retained.</summary>
    private sealed class CycleOriginSeal : IDisposable
    {
        private readonly IReadOnlyList<int> _component;
        private readonly HashSet<int> _members;
        private readonly IReadOnlyDictionary<int, SignatureFact> _settled;
        private readonly SignatureSelector.LiftedFrom _liftedFrom;
        private readonly SignatureAnalysis.Body[] _equations;
        private readonly IReadOnlyList<SignatureEquationReference>[] _references;
        private readonly SignatureAnalysis _analysis;
        private readonly ResolutionRun _run;
        private readonly StaticQueryResourceBudget _resources;
        private readonly StaticQueryResourceBudget.Lease _lease;

        private readonly Dictionary<IReadOnlyList<ParameterPattern>, Dictionary<string, ParameterDeclaration>> _firstCaptures
            = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<int, IReadOnlyList<(int Reference, CallableSignature Signature)>> _lifted = [];
        private readonly Dictionary<(int Equation, string Name), Node> _nodes = [];
        private readonly Dictionary<(int Equation, string Name), ParameterDeclaration> _origins = [];
        private readonly Dictionary<(ParameterDeclaration Origin, ParameterKind Kind), CaptureParameterPattern> _leaves
            = new(LeafKeyComparer.Instance);
        private readonly Dictionary<int[], ParameterCycleMember[]> _memberSets;

        internal CycleOriginSeal(
            IReadOnlyList<int> component,
            IReadOnlyDictionary<int, SignatureFact> settled,
            SignatureSelector.LiftedFrom liftedFrom,
            SignatureAnalysis.Body[] equations,
            IReadOnlyList<SignatureEquationReference>[] references,
            SignatureAnalysis analysis,
            ResolutionRun run)
        {
            _component = component;
            _members = [.. component];
            _settled = settled;
            _liftedFrom = liftedFrom;
            _equations = equations;
            _references = references;
            _analysis = analysis;
            _run = run;
            _resources = run.StructuralOperation!.Queries.Resources;
            _lease = _resources.Temporary();
            _lease.Add(2, run.CancellationToken);
            _memberSets = new(new MemberSetComparer(this));
        }

        public void Dispose() => _lease.Dispose();

        /// <summary>One node's provider edges, in written order: another member, or a fixed callee's record.</summary>
        private sealed class Node
        {
            public readonly List<Edge> Providers = [];
        }

        private readonly record struct Edge(int Member, ParameterDeclaration? Record, string Provider);

        private void Step(long units = 1)
        {
            _resources.Work(units, _run.CancellationToken);
            _run.Observations?.RecordSignatureSelectionStep();
        }

        /// <summary>The first capture of each name in a list: built once per list by a charged walk over its nodes.</summary>
        private Dictionary<string, ParameterDeclaration> FirstCaptures(IReadOnlyList<ParameterPattern> patterns)
        {
            Step();
            if (_firstCaptures.TryGetValue(patterns, out var known))
                return known;
            var index = new Dictionary<string, ParameterDeclaration>(StringComparer.Ordinal);
            var pending = new Stack<(IReadOnlyList<ParameterPattern> Items, int Next)>();
            pending.Push((patterns, 0));
            while (pending.TryPop(out var frame))
            {
                Step();
                if (frame.Next >= frame.Items.Count)
                    continue;
                pending.Push((frame.Items, frame.Next + 1));
                var pattern = frame.Items[frame.Next];
                if (pattern is CaptureParameterPattern capture)
                {
                    if (index.TryAdd(capture.Name, capture.Parameter))
                        _lease.Add(1, _run.CancellationToken);
                }
                else if (ParameterPattern.StructuralItems(pattern) is { } items)
                {
                    pending.Push((items, 0));
                }
            }

            _firstCaptures.Add(patterns, index);
            return index;
        }

        private IReadOnlyList<ParameterPattern> OwnOf(int equation) => _equations[equation].Written.ParameterPatterns;

        private bool OwnCapture(int equation, string name, out ParameterDeclaration own)
            => FirstCaptures(OwnOf(equation)).TryGetValue(name, out own!);

        private Node NodeOf(int equation, string name)
        {
            if (_nodes.TryGetValue((equation, name), out var node))
                return node;
            node = new Node();
            var own = OwnOf(equation);
            foreach (var (referenceIndex, signature) in _lifted[equation])
            {
                Step();
                // A callee the owner's single collecting stream forwards contributes no capture.
                if (CanForwardSingleCollectingStream(own, signature.ParameterPatterns))
                    continue;
                var reference = _references[equation][referenceIndex];
                var calleePatterns = reference.Target >= 0 && _members.Contains(reference.Target)
                    ? _settled[reference.Target].Patterns
                    : signature.ParameterPatterns;
                if (!FirstCaptures(calleePatterns).TryGetValue(name, out var record))
                    continue;
                node.Providers.Add(reference.Target >= 0 && _members.Contains(reference.Target)
                    ? new Edge(reference.Target, null, reference.DisplayName)
                    : new Edge(-1, record, reference.DisplayName));
            }

            _lease.Add(1 + node.Providers.Count, _run.CancellationToken);
            _nodes.Add((equation, name), node);
            if (node.Providers.Count == 0)
                throw new InvalidOperationException(
                    $"Signature selection completed '{_equations[equation].Name}' with the parameter '{name}', which no lifted callee provides.");
            return node;
        }

        /// <summary>The members' non-own capture names, in list order: every node an origin must be derived for.</summary>
        private List<(int Equation, string Name)> LiftedNodes()
        {
            var nodes = new List<(int, string)>();
            foreach (var equation in _component)
            {
                if (!_settled[equation].IsLifted)
                    continue;
                foreach (var name in FirstCaptures(_settled[equation].Patterns).Keys)
                {
                    if (!OwnCapture(equation, name, out _))
                        nodes.Add((equation, name));
                }
            }

            return nodes;
        }

        /// <summary>Follows every node's first provider, marking a chain's nodes with its end or with the cycle it enters.</summary>
        private void DeriveOrigins(List<(int Equation, string Name)> nodes)
        {
            foreach (var start in nodes)
            {
                if (_origins.ContainsKey(start))
                    continue;
                var path = new List<(int Equation, string Name)>();
                var onPath = new Dictionary<(int, string), int>();
                var current = start;
                ParameterDeclaration origin;
                while (true)
                {
                    Step();
                    if (_origins.TryGetValue(current, out var known))
                    {
                        origin = known;
                        break;
                    }

                    if (onPath.TryGetValue(current, out var at))
                    {
                        origin = CycleOriginOf(path.GetRange(at, path.Count - at));
                        break;
                    }

                    var first = NodeOf(current.Equation, current.Name).Providers[0];
                    if (first.Record is { } record)
                    {
                        onPath.Add(current, path.Count);
                        path.Add(current);
                        origin = record;
                        break;
                    }

                    onPath.Add(current, path.Count);
                    path.Add(current);
                    if (OwnCapture(first.Member, current.Name, out var own))
                    {
                        origin = own;
                        break;
                    }

                    current = (first.Member, current.Name);
                }

                foreach (var node in path)
                {
                    Step();
                    _origins[node] = origin;
                }

                _lease.Add(path.Count, _run.CancellationToken);
            }
        }

        /// <summary>
        /// The origin a first-provider cycle shares: its sources through EVERY provider edge, an earlier cycle origin
        /// contributing its own sources. One source collapses to it; otherwise a generated record names the set.
        /// </summary>
        private ParameterDeclaration CycleOriginOf(List<(int Equation, string Name)> cycle)
        {
            var name = cycle[0].Name;
            var roots = new Dictionary<ParameterOriginKey, ParameterCycleRoot>();
            var visited = new HashSet<int>();
            var queue = new Queue<int>();
            foreach (var (equation, _) in cycle)
                queue.Enqueue(equation);
            while (queue.TryDequeue(out var equation))
            {
                Step();
                if (!visited.Add(equation))
                    continue;
                _lease.Add(1, _run.CancellationToken);
                foreach (var edge in NodeOf(equation, name).Providers)
                {
                    Step();
                    if (edge.Record is { } record)
                        AddRoot(roots, record, edge.Provider);
                    else if (OwnCapture(edge.Member, name, out var own))
                        AddRoot(roots, own, _equations[edge.Member].Name);
                    else
                        queue.Enqueue(edge.Member);
                }
            }

            if (roots.Count == 1)
                return roots.Values.Single().Declaration;

            Step(cycle.Count + roots.Count);
            var members = SharedCycleMembers(cycle);
            var sources = roots.Values.ToArray();
            Array.Sort(sources, ParameterCycleRoot.RenderOrder);
            _resources.Metadata(2 + sources.Length, work: 0, _run.CancellationToken);
            return new ParameterDeclaration(name)
            {
                InferredProvenance = ImplicitParameterProvenance.ForCycle(name, new ParameterCycleOrigin(members, sources)),
            };
        }

        private void AddRoot(Dictionary<ParameterOriginKey, ParameterCycleRoot> roots, ParameterDeclaration record, string provider)
        {
            if (record.InferredProvenance?.CycleOrigin is { } earlier)
            {
                foreach (var root in earlier.Roots)
                {
                    Step();
                    AddRoot(roots, root.Declaration, root.Provider);
                }

                return;
            }

            var key = ParameterOriginKey.Of(record);
            if (roots.TryGetValue(key, out var known))
            {
                // The label only renders the source: a canonical one keeps rendering free of traversal order.
                if (string.CompareOrdinal(provider, known.Provider) < 0)
                    roots[key] = known with { Provider = provider };
            }
            else
            {
                roots.Add(key, new ParameterCycleRoot(record, provider));
                _lease.Add(1, _run.CancellationToken);
            }
        }

        /// <summary>
        /// Member paths depend on the semantic member SET, not the capture name or its provider order. Build them once
        /// per set in this seal: several wide captures must not each copy the same long paths. Keys are equation identities
        /// of this selection, so shared input lists or equal spellings never merge distinct declaring contexts.
        /// </summary>
        private ParameterCycleMember[] SharedCycleMembers(List<(int Equation, string Name)> cycle)
        {
            using var keyLease = _resources.Temporary();
            keyLease.Add(3 + 2L * cycle.Count, _run.CancellationToken);
            // SortedSet propagates the operation's refusal/cancellation directly from its comparisons. Every comparison
            // is a charged checkpoint; an opaque sort would hide that work or wrap a comparer exception.
            var ordered = new SortedSet<int>(Comparer<int>.Create((left, right) =>
            {
                Step();
                return left.CompareTo(right);
            }));
            foreach (var (equation, _) in cycle)
            {
                Step();
                ordered.Add(equation);
            }

            var key = new int[ordered.Count];
            var index = 0;
            foreach (var equation in ordered)
            {
                Step();
                key[index++] = equation;
            }

            if (_memberSets.TryGetValue(key, out var known))
                return known;

            var members = CycleMembers(cycle);
            Array.Sort(members, ParameterCycleMember.RenderOrder);
            // Transfer the admitted lookup key to the seal's retained temporary storage. Members themselves are final,
            // immutable metadata; no returned member array retains this cache, its comparer, the operation or its token.
            keyLease.Dispose();
            _lease.Add(1 + key.Length, _run.CancellationToken);
            _memberSets.Add(key, members);
            return members;
        }

        /// <summary>
        /// The cycle's members, each named relative to the innermost body declaring them all. One shared body can be served
        /// to several contexts with one record, so a name reaching above that body would be true of only one of them; below
        /// it every name holds in each, and a cycle reaching across contexts keeps the names that tell its members apart.
        /// </summary>
        private ParameterCycleMember[] CycleMembers(List<(int Equation, string Name)> cycle)
        {
            using var scratch = _resources.Temporary();
            scratch.Add(2 + cycle.Count, _run.CancellationToken);
            var chains = new List<StaticScopeKey>[cycle.Count];
            var shared = int.MaxValue;
            for (var i = 0; i < chains.Length; i++)
            {
                var chain = new List<StaticScopeKey>();
                for (var key = _equations[cycle[i].Equation].Key.Parent; key is not null; key = key.Parent)
                {
                    Step();
                    scratch.Add(1, _run.CancellationToken);
                    chain.Add(_analysis.Aliases!.Resolve(key));
                }

                chain.Reverse();
                chains[i] = chain;
                shared = i == 0 ? chain.Count : Math.Min(shared, CommonPrefix(chains[0], chain));
            }

            _resources.Metadata(1 + cycle.Count, work: 0, _run.CancellationToken);
            var members = new ParameterCycleMember[cycle.Count];
            for (var i = 0; i < members.Length; i++)
            {
                scratch.Add(2 + chains[i].Count - shared, _run.CancellationToken);
                var names = new List<string>();
                foreach (var key in chains[i].Skip(shared))
                {
                    Step();
                    if (_analysis.Bodies.TryGetValue(key, out var body) && !body.Name.StartsWith('<'))
                        names.Add(body.Name);
                }

                names.Add(_equations[cycle[i].Equation].Name);
                if (names.Count > 1)
                {
                    var length = (long)names.Count - 1;
                    foreach (var part in names)
                    {
                        Step();
                        length += part.Length;
                    }

                    // A joined path is newly stored text: reserve its header and UTF-16 payload, and charge copying it,
                    // before String.Join can allocate. A single name reuses the source string instead.
                    _resources.Metadata(1 + (length + 31) / 32, work: length, _run.CancellationToken);
                }

                members[i] = new ParameterCycleMember(names.Count == 1 ? names[0] : string.Join(".", names), _equations[cycle[i].Equation].Span);
            }

            return members;
        }

        private int CommonPrefix(List<StaticScopeKey> left, List<StaticScopeKey> right)
        {
            var length = 0;
            while (length < left.Count && length < right.Count && ReferenceEquals(left[length], right[length]))
            {
                Step();
                length++;
            }

            return length;
        }

        /// <summary>A leaf of the final list: one object per origin and kind, so two owners with one origin can share a list.</summary>
        private CaptureParameterPattern Leaf(ParameterDeclaration origin, ParameterKind kind)
        {
            if (_leaves.TryGetValue((origin, kind), out var leaf))
                return leaf;
            leaf = new CaptureParameterPattern(origin.Kind == kind ? origin : origin.WithKindOf(kind));
            _lease.Add(1, _run.CancellationToken);
            _leaves.Add((origin, kind), leaf);
            return leaf;
        }

        /// <summary>The pattern with every lifted capture holding its derived origin; own captures and shapes stay exactly.</summary>
        private ParameterPattern Rewrite(int equation, ParameterPattern pattern)
        {
            Step();
            if (pattern is CaptureParameterPattern capture)
            {
                if (OwnCapture(equation, capture.Name, out _))
                    return pattern;
                var origin = _origins[(equation, capture.Name)];
                return ReferenceEquals(capture.Parameter, origin) ? pattern : Leaf(origin, capture.Kind);
            }

            var items = ParameterPattern.StructuralItems(pattern);
            if (items is null)
                return pattern;
            var rewritten = new ParameterPattern[items.Count];
            var changed = false;
            for (var index = 0; index < rewritten.Length; index++)
            {
                rewritten[index] = Rewrite(equation, items[index]);
                changed |= !ReferenceEquals(rewritten[index], items[index]);
            }

            return changed ? ParameterPattern.WithStructuralItems(pattern, rewritten) : pattern;
        }

        private IReadOnlyList<ParameterPattern> FinalPatterns(int equation)
        {
            var settled = _settled[equation].Patterns;
            if (!_settled[equation].IsLifted)
                return settled;
            var rewritten = new ParameterPattern[settled.Count];
            var changed = false;
            for (var index = 0; index < rewritten.Length; index++)
            {
                rewritten[index] = Rewrite(equation, settled[index]);
                changed |= !ReferenceEquals(rewritten[index], settled[index]);
            }

            if (!changed)
                return settled;
            _resources.Metadata(1 + rewritten.Length, work: 0, _run.CancellationToken);
            return _run.Templates.InternFlat(rewritten);
        }

        /// <summary>
        /// Same structure and same origin content, one charged step per node. Origins compare by content: a recomposition
        /// rebuilds copies, and object identity proves nothing about provenance.
        /// </summary>
        private bool SameComposition(IReadOnlyList<ParameterPattern> left, IReadOnlyList<ParameterPattern> right)
        {
            Step();
            if (left.Count != right.Count)
                return false;
            for (var index = 0; index < left.Count; index++)
            {
                var (a, b) = (left[index], right[index]);
                Step();
                if (a.GetType() != b.GetType())
                    return false;
                if (a is CaptureParameterPattern capture)
                {
                    var other = (CaptureParameterPattern)b;
                    if (capture.Kind != other.Kind || !string.Equals(capture.Name, other.Name, StringComparison.Ordinal)
                        || !ParameterOriginKey.SameOrigin(capture.Parameter, other.Parameter))
                        return false;
                }
                else if (ParameterPattern.StructuralItems(a) is { } items && !SameComposition(items, ParameterPattern.StructuralItems(b)!))
                {
                    return false;
                }
            }

            return true;
        }

        internal IReadOnlyDictionary<int, SignatureFact> Run(SignatureSelector.Compose compose)
        {
            foreach (var equation in _component)
                _lifted.Add(equation, _liftedFrom(equation, _settled));
            DeriveOrigins(LiftedNodes());

            var final = new Dictionary<int, SignatureFact>(_component.Count);
            foreach (var equation in _component)
            {
                var settled = _settled[equation];
                var patterns = FinalPatterns(equation);
                final.Add(equation, ReferenceEquals(patterns, settled.Patterns)
                    ? settled
                    : new SignatureFact(patterns, settled.Violation, settled.IsLifted, composition: null,
                        CallableSignature.FromInferredPatterns(_equations[equation].Name, patterns)));
            }

            var published = new Dictionary<int, SignatureFact>(_component.Count);
            foreach (var equation in _component)
            {
                var fact = final[equation];
                var lifted = _liftedFrom(equation, final);
                // The recomposition merges every lifted list and can build new templates from them, as a round does.
                var units = 1L + lifted.Count;
                foreach (var (_, signature) in lifted)
                    units += signature.ParameterPatterns.Count + FirstCaptures(signature.ParameterPatterns).Count;
                _resources.Metadata(units, work: units, _run.CancellationToken);
                var recomposed = compose(equation, lifted);
                if (!SameLifted(_lifted[equation], lifted) || recomposed.Violation != fact.Violation || recomposed.IsLifted != fact.IsLifted
                    || !SameComposition(fact.Patterns, recomposed.Patterns))
                    throw new InvalidOperationException(
                        $"Signature selection sealed '{_equations[equation].Name}' with a signature its callees' final signatures do not compose.");
                published.Add(equation, new SignatureFact(fact.Patterns, fact.Violation, fact.IsLifted, recomposed.Composition, fact.Signature));
            }

            return published;
        }

        private static bool SameLifted(
            IReadOnlyList<(int Reference, CallableSignature Signature)> left,
            IReadOnlyList<(int Reference, CallableSignature Signature)> right)
        {
            if (left.Count != right.Count)
                return false;
            for (var index = 0; index < left.Count; index++)
            {
                if (left[index].Reference != right[index].Reference)
                    return false;
            }

            return true;
        }

        private sealed class MemberSetComparer(CycleOriginSeal owner) : IEqualityComparer<int[]>
        {
            public bool Equals(int[]? left, int[]? right)
            {
                if (ReferenceEquals(left, right))
                    return true;
                if (left is null || right is null || left.Length != right.Length)
                    return false;
                for (var i = 0; i < left.Length; i++)
                {
                    owner.Step();
                    if (left[i] != right[i])
                        return false;
                }

                return true;
            }

            public int GetHashCode(int[] members)
            {
                var hash = new HashCode();
                foreach (var member in members)
                {
                    owner.Step();
                    hash.Add(member);
                }

                return hash.ToHashCode();
            }
        }

        private sealed class LeafKeyComparer : IEqualityComparer<(ParameterDeclaration Origin, ParameterKind Kind)>
        {
            public static readonly LeafKeyComparer Instance = new();

            public bool Equals((ParameterDeclaration Origin, ParameterKind Kind) x, (ParameterDeclaration Origin, ParameterKind Kind) y)
                => ReferenceEquals(x.Origin, y.Origin) && x.Kind == y.Kind;

            public int GetHashCode((ParameterDeclaration Origin, ParameterKind Kind) key)
                => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Origin), key.Kind);
        }
    }
}
