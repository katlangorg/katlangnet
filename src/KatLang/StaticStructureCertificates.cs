namespace KatLang;

internal sealed partial class StaticStructureQueries
{
    /// <summary>
    /// A closed conservative graph certificate for an observer, never a selected identity or OD-D verdict.
    /// Each local equation is positive set union. Its complete least closure conservatively retains every
    /// member-bearing endpoint and blocking failure. Empty endpoints are omitted; runtime and static miss
    /// agree for these observers. This is not a complete target-identity domain. Only after quiescence may
    /// the observer prove absence/participation. Ordinary engine lower bounds prune alternatives conclusively;
    /// Unknown expands them. No speculative Follow, Boolean assignments or incomplete cycle-cut cache.
    /// </summary>
    private sealed class NamespaceCertificate(StaticStructureQueries queries, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        private sealed class Outcomes
        {
            internal readonly HashSet<StaticScopeKey> Scopes = new(ReferenceEqualityComparer.Instance);
            internal bool Runtime;
            internal bool Failure;
            internal bool Unresolved;
        }

        private sealed class Node(StaticQueryKey key)
        {
            internal StaticQueryKey Key = key;
            internal readonly Outcomes Value = new();
            internal readonly HashSet<Node> Readers = [];
            internal readonly HashSet<Node> Dependencies = [];
            internal bool Queued;
        }

        private readonly Dictionary<StaticQueryKey, Node> _nodes = [];
        private readonly Queue<Node> _pending = [];
        private Node? _running;
        private int _liveEntries;
        private int _temporaryEntries;

        private int Total(int extra = 0)
        {
            var total = (long)_liveEntries + _temporaryEntries + extra;
            if (total > int.MaxValue) throw new StaticQueryLimitExceededException("The namespace certificate exceeded its storage bound.");
            return (int)total;
        }
        private void Work() => reader.ChargeAuxiliary(Total());
        private void Admit()
        {
            reader.ChargeAuxiliary(Total(1));
            _liveEntries++;
        }
        private void Temporary()
        {
            reader.ChargeAuxiliary(Total(1));
            _temporaryEntries++;
        }
        private Outcomes NewOutcomes()
        {
            Temporary();
            return new();
        }
        private void Add(Outcomes result, StaticScopeKey scope)
        {
            Work();
            if (result.Scopes.Contains(scope)) return;
            Temporary();
            result.Scopes.Add(scope);
        }

        private void Include(Outcomes result, Outcomes other)
        {
            foreach (var scope in other.Scopes) Add(result, scope);
            result.Runtime |= other.Runtime;
            result.Failure |= other.Failure;
            result.Unresolved |= other.Unresolved;
        }

        private void Own(Outcomes result, StaticScopeKey scope, bool open)
        {
            Work();
            // Empty own endpoints have the same observer result as an empty set. Do not copy every transparent
            // prefix's empty namespace into every predecessor: a chain shares only its member-bearing terminals.
            var members = queries.ContextOf(scope).Members;
            if (open ? members.HasPublicMembers : members.HasMembers) Add(result, scope);
        }

        private static StaticQueryKey Namespace(StaticScopeKey scope, StaticCycleCheck stratum, bool open)
            => Project(StaticQueryKind.TargetWalk, scope, open ? StaticQueryProjection.OpenStructure : StaticQueryProjection.Default, stratum: stratum);
        private static StaticQueryKey Expression(StaticScopeKey scope, Expr expression, StaticCycleCheck stratum, bool direct)
            => Project(StaticQueryKind.TargetWalk, scope, direct ? StaticQueryProjection.OpenRowTarget : StaticQueryProjection.RowTarget, stratum: stratum, node: expression);
        private static StaticQueryKey ReceiverKey(StaticScopeKey scope, Expr expression, StaticCycleCheck stratum)
            => Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.Receiver, stratum: stratum, node: expression);

        private Node NodeOf(StaticQueryKey key)
        {
            if (_nodes.TryGetValue(key, out var found)) return found;
            Admit();
            var node = new Node(key);
            _nodes.Add(key, node);
            Schedule(node);
            return node;
        }

        private void Schedule(Node node)
        {
            if (node.Queued) return;
            node.Queued = true;
            _pending.Enqueue(node);
        }

        private Outcomes Read(StaticQueryKey key)
        {
            Work();
            var node = NodeOf(key);
            if (!_running!.Dependencies.Contains(node))
            {
                Admit();
                _running.Dependencies.Add(node);
                node.Readers.Add(_running);
            }
            return node.Value;
        }

        private Outcomes Solve(StaticQueryKey root)
        {
            var result = NodeOf(root);
            while (_pending.TryDequeue(out var node))
            {
                Work();
                node.Queued = false;
                _running = node;
                _temporaryEntries = 0;
                var next = Evaluate(node.Key);
                var changed = false;
                foreach (var scope in next.Scopes)
                {
                    Work();
                    if (node.Value.Scopes.Contains(scope)) continue;
                    Admit();
                    node.Value.Scopes.Add(scope);
                    changed = true;
                }
                if (next.Runtime && !node.Value.Runtime) { node.Value.Runtime = true; changed = true; }
                if (next.Failure && !node.Value.Failure) { node.Value.Failure = true; changed = true; }
                if (next.Unresolved && !node.Value.Unresolved) { node.Value.Unresolved = true; changed = true; }
                _temporaryEntries = 0;
                if (changed) foreach (var dependent in node.Readers) { Work(); Schedule(dependent); }
            }
            _running = null;
            return result.Value;
        }

        internal StaticFact OpenAbsence(StaticScopeKey scope, Expr? target, string? name, StaticCycleCheck stratum)
        {
            var outcomes = Solve(Project(StaticQueryKind.OpenProviders, scope, StaticQueryProjection.OpenTarget, stratum: stratum, node: target));
            if (outcomes.Unresolved) return StaticFact.Unknown;
            foreach (var provider in outcomes.Scopes)
            {
                Work();
                var members = queries.ContextOf(provider).Members;
                if (name is null ? members.HasPublicMembers : members.Public(name) is not null)
                    return name is null ? new(StaticFactKind.NamespaceCoverage) : StaticFact.Unknown;
            }
            return StaticFact.Yes;
        }

        /// <summary>
        /// A conclusive provider with this public name guarantees presence unless an earlier view of the SAME
        /// language provider can hide it with a namespace that lacks the name. This proves presence only, never
        /// the first view or a member binding. Unknown successors are explored by the same closed certificate.
        /// </summary>
        internal StaticFact PreservedOpenPresence(StaticScopeKey scope, int index, string name, StaticCycleCheck stratum)
        {
            var opens = queries.ContextOf(scope).Body.Opens;
            var exact = reader.Read(Project(StaticQueryKind.OpenProviders, scope, StaticQueryProjection.OpenTarget, stratum: stratum, node: opens[index]));
            if (exact.Data is not StaticScopeKey[] { Length: 1 } current || queries.ContextOf(current[0]).Members.Public(name) is null)
                return StaticFact.Unknown;
            var identity = queries.Keys.ProviderScope(current[0], queries.Resources, queries.OperationToken);
            for (var i = 0; i < index; i++)
            {
                Work();
                var alternatives = Solve(Project(StaticQueryKind.OpenProviders, scope, StaticQueryProjection.OpenTarget, stratum: stratum, node: opens[i]));
                if (alternatives.Unresolved) return StaticFact.Unknown;
                foreach (var provider in alternatives.Scopes)
                {
                    Work();
                    if (ReferenceEquals(identity, queries.Keys.ProviderScope(provider, queries.Resources, queries.OperationToken))
                        && queries.ContextOf(provider).Members.Public(name) is null) return StaticFact.Unknown;
                }
            }
            return StaticFact.Yes;
        }

        internal StaticFact FallbackParticipation(StaticScopeKey scope, Expr.DotCall edge)
        {
            var outcomes = Solve(ReceiverKey(scope, edge.Target, StaticCycleCheck.Formation));
            if (outcomes.Failure || outcomes.Unresolved) return StaticFact.Unknown;
            foreach (var receiver in outcomes.Scopes)
            {
                Work();
                var members = queries.ContextOf(receiver).Members;
                if (members.Declared(edge.Name) is not null || members.IsBranchOnly(edge.Name)) return StaticFact.Unknown;
            }
            // Runtime is MAY, a static miss ALWAYS: both participate, without selecting either exact Q5 value.
            return StaticFact.Yes;
        }

        private Outcomes Evaluate(StaticQueryKey key) => key.Kind switch
        {
            StaticQueryKind.Binding => Binding(key),
            StaticQueryKind.OpenProviders => Providers(key),
            StaticQueryKind.TargetWalk when key.Projection == StaticQueryProjection.Receiver => Receiver(key),
            StaticQueryKind.TargetWalk when key.Node is not null => Targets(key),
            _ => Structure(key),
        };

        private Outcomes Binding(StaticQueryKey key)
        {
            var result = NewOutcomes();
            var fact = reader.Read(key);
            if (fact.Kind == StaticFactKind.Declaration)
            {
                Add(result, queries.BodyIn(fact.Scope!, fact.Property!.Value));
                return result;
            }
            if (fact.Kind is StaticFactKind.Parameter or StaticFactKind.Missing) { result.Runtime = true; return result; }
            if (fact.Kind == StaticFactKind.Ambiguous) { result.Failure = true; return result; }
            var direct = key.Projection == StaticQueryProjection.OpenHeadBinding;
            for (var at = key.Scope; at is not null; at = queries.ContextOf(at).Parent)
            {
                Work();
                var context = queries.ContextOf(at);
                var phantom = direct && ReferenceEquals(at, queries.Root);
                if (!phantom && context.WrittenParameters.Contains(key.Name!)) { result.Runtime = true; return result; }
                if (context.Members.Declared(key.Name!) is { } property)
                {
                    Add(result, queries.BodyIn(at, property.Value));
                    return result;
                }
                if (!phantom && context.Infers && context.Syntax.Uses.ContainsKey(key.Name!))
                {
                    var input = reader.Read(StaticQueryKey.IsInput(at, key.Name!));
                    if (input.Kind != StaticFactKind.No) result.Runtime = true;
                    if (input.Kind == StaticFactKind.Yes) return result;
                }
            }
            if (direct) return result;
            for (var at = key.Scope; at is not null; at = queries.ContextOf(at).Parent)
            {
                Work();
                Temporary();
                var providers = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
                foreach (var open in queries.ContextOf(at).Body.Opens)
                {
                    Work();
                    var alternatives = Read(Project(StaticQueryKind.OpenProviders, at, StaticQueryProjection.OpenTarget, stratum: key.Stratum, node: open));
                    result.Unresolved |= alternatives.Unresolved;
                    foreach (var provider in alternatives.Scopes)
                    {
                        Work();
                        if (queries.ContextOf(provider).Members.Public(key.Name!) is not { } member) continue;
                        var identity = queries.Keys.ProviderScope(provider, queries.Resources, queries.OperationToken);
                        if (!providers.Contains(identity)) { Temporary(); providers.Add(identity); }
                        Add(result, queries.BodyIn(provider, member.Value));
                    }
                }
                // Conservatively retain ambiguity too, even if different possible providers are exclusive.
                if (providers.Count > 1) result.Failure = true;
            }
            return result;
        }

        private Outcomes Structure(StaticQueryKey key)
        {
            var result = NewOutcomes();
            var fact = reader.Read(key);
            var open = key.Projection == StaticQueryProjection.OpenStructure;
            if (fact.Kind == StaticFactKind.Structure) { Own(result, fact.Scope!, open); return result; }
            if (fact.Kind == StaticFactKind.Runtime) { result.Runtime = true; return result; }
            if (!fact.IsUnknown) return result;
            Own(result, key.Scope, open); // eligibility failure, calculation and OD-D refusal all keep own structure
            var context = queries.ContextOf(key.Scope);
            if (context.Body is Algorithm.Alias { ResolvedTargetCell.IsPending: true } or Algorithm.Alias { ResolvedStructureCell.IsPending: true })
            {
                result.Unresolved = true;
                return result;
            }
            if (!IsExpandable(context)) return result; // carriers/modules/closed bodies never inherit members
            var inputs = queries.NoInputs(context, reader);
            if (inputs.Kind == StaticFactKind.No) return result;
            var targets = Read(Expression(key.Scope, WrittenReferenceRow(context)!, key.Stratum, open));
            result.Unresolved |= targets.Unresolved;
            if (!open) result.Runtime |= targets.Runtime;
            foreach (var target in targets.Scopes)
            {
                Work();
                Include(result, Read(Namespace(target, key.Stratum, open)));
            }
            return result;
        }

        private Outcomes Providers(StaticQueryKey key)
        {
            var result = NewOutcomes();
            if (key.Node is null)
            {
                foreach (var target in queries.ContextOf(key.Scope).Body.Opens)
                {
                    Work();
                    Include(result, Read(Project(StaticQueryKind.OpenProviders, key.Scope, StaticQueryProjection.OpenTarget,
                        stratum: key.Stratum, node: target)));
                }
                return result;
            }
            var exact = reader.Read(key);
            if (!exact.IsUnknown)
            {
                foreach (var scope in (StaticScopeKey[])exact.Data!) Own(result, scope, open: true);
                return result;
            }
            var targets = Read(Expression(key.Scope, key.Node!, key.Stratum, direct: true));
            result.Unresolved |= targets.Unresolved;
            foreach (var target in targets.Scopes)
            {
                Work();
                Include(result, Read(Namespace(target, key.Stratum, open: true)));
            }
            return result;
        }

        private Outcomes Targets(StaticQueryKey key)
        {
            var expression = key.Node!.UnwrapGraceOperand();
            var direct = key.Projection == StaticQueryProjection.OpenRowTarget;
            if (expression is Expr.Resolve(var name))
                return Read(Project(StaticQueryKind.Binding, key.Scope,
                    direct ? StaticQueryProjection.OpenHeadBinding : StaticQueryProjection.Default, name, key.Stratum));
            var result = NewOutcomes();
            if (expression is Expr.Param) { result.Runtime = true; return result; }
            if (expression is Expr.AlgorithmExpr(var body))
            {
                Add(result, queries.BodyIn(direct ? queries.Keys.Root : key.Scope, body));
                return result;
            }
            if (expression is not Expr.DotCall { Args: null } edge) return result;
            Outcomes receivers;
            if (direct)
            {
                receivers = NewOutcomes();
                var targets = Read(Expression(key.Scope, edge.Target, key.Stratum, direct: true));
                receivers.Unresolved |= targets.Unresolved;
                foreach (var target in targets.Scopes)
                    Include(receivers, Read(Namespace(target, key.Stratum, open: true)));
            }
            else receivers = Read(ReceiverKey(key.Scope, edge.Target, key.Stratum));
            result.Runtime = receivers.Runtime;
            result.Unresolved |= receivers.Unresolved;
            if (!direct && edge.UsesDotAlgorithmIntrinsic()) result.Runtime = true;
            foreach (var receiver in receivers.Scopes)
            {
                Work();
                var members = queries.ContextOf(receiver).Members;
                var member = direct ? members.Public(edge.Name) : members.Declared(edge.Name);
                if (member is not null) Add(result, queries.BodyIn(receiver, member.Value));
                else if (!direct && edge.UsesDotAlgorithmIntrinsic()) result.Runtime = true;
            }
            return result;
        }

        private Outcomes Receiver(StaticQueryKey key)
        {
            var fact = reader.Read(key);
            var result = NewOutcomes();
            if (fact.Kind == StaticFactKind.Structure) { Own(result, fact.Scope!, open: false); return result; }
            if (fact.Kind == StaticFactKind.Runtime) { result.Runtime = true; return result; }
            if (fact.Kind == StaticFactKind.Failure) { result.Failure = true; return result; }
            if (!fact.IsUnknown) return result;
            var expression = key.Node!.UnwrapGraceOperand();
            if (expression is Expr.Param) { result.Runtime = true; return result; }
            if (expression is Expr.AlgorithmExpr(var body)) { Own(result, queries.BodyIn(key.Scope, body), open: false); return result; }
            if (expression is Expr.Resolve(var name))
            {
                var binding = Read(Project(StaticQueryKind.Binding, key.Scope, StaticQueryProjection.Default, name, key.Stratum));
                result.Runtime = binding.Runtime;
                result.Failure = binding.Failure;
                result.Unresolved |= binding.Unresolved;
                foreach (var target in binding.Scopes) { Work(); Include(result, Read(Namespace(target, key.Stratum, open: false))); }
                return result;
            }
            if (expression is not Expr.DotCall { Args: null } edge) return result;
            var receivers = Read(ReceiverKey(key.Scope, edge.Target, key.Stratum));
            result.Runtime = receivers.Runtime;
            result.Failure = receivers.Failure;
            result.Unresolved |= receivers.Unresolved;
            foreach (var receiver in receivers.Scopes)
            {
                Work();
                var members = queries.ContextOf(receiver).Members;
                if (members.Declared(edge.Name) is { } member)
                    Include(result, Read(Namespace(queries.BodyIn(receiver, member.Value), key.Stratum, open: false)));
                else if (members.IsBranchOnly(edge.Name)) result.Failure = true;
            }
            return result;
        }
    }
}
