using KatLang.Evaluation;

namespace KatLang;

/// <summary>
/// <b>J7 PER-SITE PLAN RETENTION</b> (C#-only optimization; no language, Lean or observable-outcome change).
/// A run whose admitted program reaches META only through the builtin loops
/// (<see cref="EvaluationBudget.UsesPerSiteInvocationPlans"/>: no <c>meta</c> capture or clause binder, no
/// deferred module region, no test seam) still retains invocation plans, but forms one only for a
/// call-shaped supplied cell that can REACH a META binder. Its only META binders are the <c>step</c>
/// parameters of <c>while</c>/<c>repeat</c>, and the reference they capture never leaves the builtin, so no
/// <c>Invoke()</c>, <c>Arguments</c> view or view spread exists. A cell then reaches a step only through
/// supply positions: written there, or transported as a parameter's EXISTING cell (<see cref="SupplyCell"/>).
/// So the decision is taken where a NEW cell is formed for a written call-shaped argument, with the
/// resolved, alias-normalized callee whose patterns bind it (<see cref="IsUnobservedSupplySlot"/>): an
/// ordinary cell only when that callee cannot pass the cell on. Every other formation — a META builtin, an
/// unknown slot after a spread, a callee kind this rule does not classify, every <c>retained: true</c> site
/// and every supply formed without a resolved callee (plan and view preparation, deconstruction,
/// selection) — stays a plan, as in a fully retaining run. A META binder that receives a call-shaped
/// cell that is not a plan in such a run is an internal defect and fails loudly
/// (<see cref="ThrowIfUnplannedCallReachesMeta"/>).
/// </summary>
public static partial class Evaluator
{
    // Optimization precision only: exceeding this width retains plans, with no semantic charge or refusal.
    // A fixed width bounds name propagation, head inspection and membership probes per graph node/edge.
    internal const int PerSiteAnalysisWidth = 64;

    /// <summary>
    /// A bounded conservative name summary. The default summary admits EVERY name; it is never an empty
    /// answer. Saturation therefore only retains more plans. Known summaries hold at most
    /// <see cref="PerSiteAnalysisWidth"/> names, keeping a shared graph's summaries linear in its physical size.
    /// </summary>
    internal readonly struct TransportNames(string[]? names)
    {
        internal bool IsAll => names is null;
        internal IReadOnlyList<string> KnownNames => names ?? [];
        internal bool Contains(string name) => names is null || Array.IndexOf(names, name) >= 0;
    }

    private struct TransportNameBuilder
    {
        private HashSet<string>? _names;
        private bool _all;

        internal void Add(string name)
        {
            if (_all) return;
            _names ??= new(StringComparer.Ordinal);
            if (_names.Add(name) && _names.Count > PerSiteAnalysisWidth)
            {
                _all = true;
                _names = null;
            }
        }

        internal void AddRange(TransportNames names)
        {
            if (_all) return;
            if (names.IsAll)
            {
                _all = true;
                _names = null;
                return;
            }
            foreach (var name in names.KnownNames)
                Add(name);
        }

        internal readonly TransportNames Result()
            => _all ? default : new(_names is { Count: > 0 } names ? [.. names] : []);
    }

    /// <summary>
    /// The resolved callee of the argument supplies the fused <c>filter</c>→<c>count</c> pipeline forms for its
    /// recognized stages (<see cref="TryEvaluateRecognizedSequencePipeline"/>): the <c>filter</c> stage's
    /// arguments and receiver, and the <c>range</c> source's bounds. Shared, allocation-free identities.
    /// </summary>
    private static readonly Algorithm FilterCallee = new Algorithm.Builtin(BuiltinId.@filter);

    /// <inheritdoc cref="FilterCallee"/>
    private static readonly Algorithm RangeCallee = new Algorithm.Builtin(BuiltinId.@range);

    /// <summary>
    /// Whether supply slot <paramref name="slot"/> (an EFFECTIVE slot: no spread precedes it) of a call to the
    /// resolved <paramref name="callee"/> can never pass its cell on, so a call-shaped argument there needs no
    /// plan in a per-site run. Conservative: <c>false</c> unless proved.
    /// <list type="bullet">
    /// <item>a builtin without a META parameter: every non-META builtin's native arm reads its arguments as
    /// VALUES (or projects a callable from them) and hands user code only Ready values — callback items, a
    /// <c>reduce</c> accumulator, an <c>if</c> branch's value;</item>
    /// <item>a user algorithm whose patterns up to the slot are plain, normal, fixed captures (no structural,
    /// collecting or META pattern before it, no repeated name in the list) and whose captured name is not
    /// TRANSPORTED anywhere in its body (<see cref="TransportedNamesOf"/>); an algorithm with an assignment
    /// deconstruction target binds through its own route and stays conservative;</item>
    /// <item>a clause family whose every clause head is a flat list of literals and normal binders, and every
    /// clause able to accept the slot holds a literal there or a once-written binder whose name the family
    /// does not transport.</item>
    /// </list>
    /// A META builtin (<c>while</c>, <c>repeat</c>), an alias, and anything else are never unobserved.
    /// </summary>
    internal static bool IsUnobservedSupplySlot(Algorithm callee, int slot, EvaluationBudget budget)
        => callee switch
        {
            Algorithm.Builtin(var id) => !BuiltinRegistry.GetBuiltin(id).DeclaresMetaParameter,
            Algorithm.User { AssignmentDeconstructionTarget: null } user => IsUnobservedUserSlot(user, slot, budget),
            Algorithm.Conditional family => IsUnobservedFamilySlot(family, slot, budget),
            _ => false,
        };

    private static bool IsUnobservedUserSlot(Algorithm.User callee, int slot, EvaluationBudget budget)
    {
        var patterns = callee.ParameterPatterns;
        if (patterns.Count > PerSiteAnalysisWidth || (uint)slot >= (uint)patterns.Count)
            return false;
        for (var i = 0; i <= slot; i++)
            if (patterns[i] is not CaptureParameterPattern { Kind: ParameterKind.Normal })
                return false;
        var name = ((CaptureParameterPattern)patterns[slot]).Name;
        for (var i = 0; i < patterns.Count; i++)
        {
            if (i == slot)
                continue;
            // A structural pattern elsewhere could bind the same name again: stay conservative.
            if (patterns[i] is not CaptureParameterPattern other || other.Name == name)
                return false;
        }
        return !CalleeTransportedNames(callee, budget).Contains(name) && !IsInheritedTransportName(name, budget);
    }

    private static bool IsUnobservedFamilySlot(Algorithm.Conditional family, int slot, EvaluationBudget budget)
    {
        if (family.Branches.Count > PerSiteAnalysisWidth)
            return false;
        TransportNames? transported = null;
        foreach (var branch in family.Branches)
        {
            if (branch.Pattern is not Pattern.SequenceValue head)
                return false;
            var items = head.Items;
            if (items.Count > PerSiteAnalysisWidth)
                return false;
            for (var i = 0; i < items.Count; i++)
                if (items[i] is not (Pattern.Bind { ParameterKind: ParameterKind.Normal } or Pattern.LitInt or Pattern.LitString or Pattern.LitBool))
                    return false;
            // A flat head without a collector accepts exactly its own count, so it never binds this slot.
            if (slot >= items.Count)
                continue;
            if (items[slot] is not Pattern.Bind bind)
                continue;
            for (var i = 0; i < items.Count; i++)
                if (i != slot && items[i] is Pattern.Bind other && other.Name == bind.Name)
                    return false;
            transported ??= CalleeTransportedNames(family, budget);
            if (transported.Value.Contains(bind.Name) || IsInheritedTransportName(bind.Name, budget))
                return false;
        }
        return true;
    }

    /// <summary>
    /// <see cref="TransportedNamesOf"/> for a resolved CALLEE, memoized by the callee's BODY rather than by the
    /// algorithm object: dispatch wires a callee to its context per call (a fresh <see cref="Algorithm.User"/> or
    /// <see cref="Algorithm.Conditional"/> record sharing the written body's lists), so an identity key would add one
    /// entry per call. The names depend only on those shared lists — a user algorithm's opens, properties, output
    /// rows and parameter patterns (the own-row rule), a family's opens and branches; the parent link is never
    /// followed — so every wiring of one body shares one entry.
    /// </summary>
    private static TransportNames CalleeTransportedNames(Algorithm callee, EvaluationBudget budget)
    {
        var key = callee switch
        {
            Algorithm.User user => new CalleeBodyKey(user.Output, user.Properties, user.Opens, user.ParameterPatterns),
            Algorithm.Conditional family => new CalleeBodyKey(family.Branches, family.Opens, null, null),
            _ => new CalleeBodyKey(callee, null, null, null),
        };
        var bodies = budget.CalleeTransportedNames;
        lock (budget.TransportedNames)
        {
            if (bodies.TryGetValue(key, out var known))
                return known;
        }
        var names = TransportedNamesOf(callee, budget);
        lock (budget.TransportedNames)
            bodies[key] = names;
        return names;
    }

    /// <summary>The shared body lists of a callee (<see cref="CalleeTransportedNames"/>), compared by reference identity.</summary>
    internal readonly struct CalleeBodyKey(object first, object? second, object? third, object? fourth) : IEquatable<CalleeBodyKey>
    {
        private readonly object _first = first;
        private readonly object? _second = second;
        private readonly object? _third = third;
        private readonly object? _fourth = fourth;

        public bool Equals(CalleeBodyKey other)
            => ReferenceEquals(_first, other._first) && ReferenceEquals(_second, other._second)
                && ReferenceEquals(_third, other._third) && ReferenceEquals(_fourth, other._fourth);

        public override bool Equals(object? obj) => obj is CalleeBodyKey other && Equals(other);

        public override int GetHashCode()
            => HashCode.Combine(
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(_first),
                _second is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(_second),
                _third is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(_third),
                _fourth is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(_fourth));
    }

    /// <summary>
    /// The TRANSPORTED NAMES of an admitted AST node: every name that occurs as an <see cref="Expr.Param"/> or
    /// <see cref="Expr.Resolve"/> anywhere below it (nested bodies, properties, opens, clause branches included;
    /// an inner same-named parameter counts) in any position other than a VALUE position, plus the argument
    /// names of a host-operation call and the default lexical-fallback name of a dot edge. Value positions —
    /// the only ones a cell's identity cannot leave through — are: an operand of a unary, binary or comparison
    /// operator; the receiver of a postfix selection; and an output row of a user algorithm that itself
    /// declares the name as a top-level capture (its result is that parameter's VALUE: <c>Id(x) = x</c>).
    /// Everything else counts as transport: a whole argument slot of a call or dot-call bundle, a dot receiver
    /// (<c>p.while</c>, <c>p.F(…)</c>), a callee or lexical fallback, a spread operand, a selector slot, a list or
    /// capture element, an alias target or property row (bare forwarding), an interpolation hole, a Grace
    /// wrapper and an <c>open</c>. Parent-scope links are not followed (a parameter's occurrences lie inside its
    /// owner). A pure function of the immutable node, memoized per run by reference identity
    /// (<see cref="EvaluationBudget.TransportedNames"/>): a shared subgraph is expanded once, so the work is
    /// linear in the distinct nodes and edges reached: summaries saturate at
    /// <see cref="PerSiteAnalysisWidth"/> names, conservatively admitting every name. Wide heads likewise
    /// stay planned; native argument-name lists are summarized once per node, not once per incoming edge.
    /// No CLR recursion; nothing is charged.
    /// </summary>
    internal static TransportNames TransportedNamesOf(object root, EvaluationBudget budget)
    {
        var memo = budget.TransportedNames;
        lock (memo)
        {
            if (memo.TryGetValue(root, out var known))
                return known;

            var frames = new List<TransportFrame> { TransportFrame.Enter(root) };
            while (frames.Count > 0)
            {
                var top = frames.Count - 1;
                var frame = frames[top];
                if (AstStructuralPreflight.TryGetChild(frame.Node, frame.Next, out var child))
                {
                    var index = frame.Next;
                    frame.Next++;
                    switch (child)
                    {
                        case ScopeCtx:
                            // A parent scope link (host-attached parent): outside the owner.
                            break;
                        case Expr.Param(var name):
                            if (!IsValueEdge(frame.Node, index, name))
                                frame.Add(name);
                            break;
                        case Expr.Resolve(var name):
                            if (!IsValueEdge(frame.Node, index, name))
                                frame.Add(name);
                            break;
                        default:
                            if (memo.TryGetValue(child, out var childNames))
                                frame.AddRange(childNames);
                            else
                            {
                                frames[top] = frame;
                                frames.Add(TransportFrame.Enter(child));
                                continue;
                            }
                            break;
                    }
                    frames[top] = frame;
                    continue;
                }

                var names = frame.Result();
                memo[frame.Node] = names;
                frames.RemoveAt(top);
                if (top > 0)
                {
                    var parent = frames[top - 1];
                    parent.AddRange(names);
                    frames[top - 1] = parent;
                }
            }
            return memo[root];
        }
    }

    // Whether child `index` of `parent`, an occurrence of `name`, is a VALUE position (see TransportedNamesOf).
    private static bool IsValueEdge(object parent, int index, string name)
    {
        switch (parent)
        {
            case Expr.Unary or Expr.Binary or Expr.Comparison:
                return true;
            case Expr.Index:
                return index == 0;
            case Algorithm.User user:
            {
                var row = index - (user.Parent is null ? 0 : 1) - user.Opens.Count - user.Properties.Count;
                if (row < 0 || row >= user.Output.Count)
                    return false;
                var patterns = user.ParameterPatterns;
                if (patterns.Count > PerSiteAnalysisWidth)
                    return false;
                for (var i = 0; i < patterns.Count; i++)
                    if (patterns[i] is CaptureParameterPattern { Kind: ParameterKind.Normal or ParameterKind.Collecting } capture
                        && capture.Name == name)
                        return true;
                return false;
            }
            default:
                return false;
        }
    }

    /// <summary>
    /// Whether <paramref name="name"/> is an INHERITED-READ name of the run's admitted program
    /// (<see cref="InheritedTransportNames"/>), so no parameter of that name is ever unobserved. Conservative
    /// when the run recorded no program.
    /// </summary>
    private static bool IsInheritedTransportName(string name, EvaluationBudget budget)
    {
        if (budget.AdmittedProgram is not { } program)
            return true;
        var names = budget.InheritedTransportNames;
        if (names is null)
        {
            lock (budget.TransportedNames)
                names = budget.InheritedTransportNames ??= InheritedTransportNames(program);
        }
        return names.Value.Contains(name);
    }

    /// <summary>
    /// The INHERITED-READ names of an admitted program: every name that occurs in a transport position
    /// (<see cref="TransportedNamesOf"/>'s classification) inside an algorithm that does NOT itself declare it as
    /// a parameter capture. Such a read is resolved through an enclosing activation or, where none owns the
    /// name, through the caller environment a callee inherits below its own bindings (<c>WithNeedBindings</c>,
    /// Lean <c>EvalCtx.bindParameters</c>), so it may observe the cell of a parameter it is not lexically
    /// inside, a channel the callee-local walk cannot see. A parameter whose name is in this set is never
    /// unobserved. The walk covers the whole admitted graph — root, nested bodies, families, opens, eager
    /// modules and host-attached parent scopes — once per run, bottom-up and memoized by reference identity
    /// (each node's pending and inherited names are context-free: pending names wait for their NEAREST
    /// enclosing algorithm, which either declares them or makes them inherited), so a shared subgraph is
    /// expanded once. Both name sets saturate at <see cref="PerSiteAnalysisWidth"/>, with saturation
    /// propagated as EVERY name (including across an algorithm boundary); no CLR recursion; nothing is charged.
    /// </summary>
    internal static TransportNames InheritedTransportNames(object root)
    {
        var memo = new Dictionary<object, (TransportNames Pending, TransportNames Inherited)>(ReferenceEqualityComparer.Instance);
        var onPath = new HashSet<object>(ReferenceEqualityComparer.Instance) { root };
        var frames = new List<InheritFrame> { InheritFrame.Enter(root) };
        (TransportNames Pending, TransportNames Inherited) outcome = (new([]), new([]));
        while (frames.Count > 0)
        {
            var top = frames.Count - 1;
            var frame = frames[top];
            if (AstStructuralPreflight.TryGetChild(frame.Node, frame.Next, out var child))
            {
                var index = frame.Next;
                frame.Next++;
                // An algorithm's parent scope is no part of its body: its names never meet its parameters.
                var scopeEdge = index == 0 && frame.Node is Algorithm { Parent: not null };
                switch (child)
                {
                    case Expr.Param(var name):
                        if (!IsValueEdge(frame.Node, index, name))
                            frame.AddPending(name);
                        break;
                    case Expr.Resolve(var name):
                        if (!IsValueEdge(frame.Node, index, name))
                            frame.AddPending(name);
                        break;
                    default:
                        if (memo.TryGetValue(child, out var known))
                            frame.Merge(known, scopeEdge);
                        else if (onPath.Add(child))
                        {
                            frame.ScopeChild = scopeEdge;
                            frames[top] = frame;
                            frames.Add(InheritFrame.Enter(child));
                            continue;
                        }
                        break;
                }
                frames[top] = frame;
                continue;
            }

            var result = frame.Complete();
            memo[frame.Node] = result;
            onPath.Remove(frame.Node);
            frames.RemoveAt(top);
            if (top > 0)
            {
                var parent = frames[top - 1];
                parent.Merge(result, parent.ScopeChild);
                parent.ScopeChild = false;
                frames[top - 1] = parent;
            }
            else
                outcome = result;
        }
        var all = new TransportNameBuilder();
        all.AddRange(outcome.Pending);
        all.AddRange(outcome.Inherited);
        return all.Result();
    }

    private struct InheritFrame
    {
        internal object Node;
        internal int Next;
        internal bool ScopeChild;
        private TransportNameBuilder _pending;
        private TransportNameBuilder _inherited;

        internal static InheritFrame Enter(object node)
        {
            var frame = new InheritFrame { Node = node };
            if (node is Expr.DotCall { LexicalFallback: null } edge)
                frame.AddPending(edge.Name);
            if (node is Expr.NativeCall native)
                foreach (var name in native.ArgNames)
                    frame.AddPending(name);
            return frame;
        }

        internal void AddPending(string name) => _pending.Add(name);

        private void AddInherited(string name) => _inherited.Add(name);

        internal void Merge((TransportNames Pending, TransportNames Inherited) child, bool scopeEdge)
        {
            _inherited.AddRange(child.Inherited);
            // A parent scope's unowned names stay unowned: they never meet this algorithm's parameters.
            if (scopeEdge) _inherited.AddRange(child.Pending);
            else _pending.AddRange(child.Pending);
        }

        internal (TransportNames Pending, TransportNames Inherited) Complete()
        {
            var pending = _pending.Result();
            if (Node is not (Algorithm or ScopeCtx))
                return (pending, _inherited.Result());
            if (pending.IsAll)
                _inherited.AddRange(pending);
            else
            {
                // Prove ownership only from a small top-level capture list. Do not flatten Parameters:
                // host pattern DAGs and shared implicit signatures may have enormous logical expansions.
                var declared = Node is Algorithm.User user && user.ParameterPatterns.Count <= PerSiteAnalysisWidth
                    ? user.ParameterPatterns : [];
                foreach (var name in pending.KnownNames)
                {
                    var owned = false;
                    for (var i = 0; i < declared.Count && !owned; i++)
                        owned = declared[i] is CaptureParameterPattern capture && capture.Name == name;
                    if (!owned)
                        AddInherited(name);
                }
            }
            return (new([]), _inherited.Result());
        }
    }

    private struct TransportFrame
    {
        internal object Node;
        internal int Next;
        private TransportNameBuilder _names;

        internal static TransportFrame Enter(object node)
        {
            // An algorithm's child 0 is its parent scope when it has one: never followed.
            var frame = new TransportFrame { Node = node, Next = node is Algorithm { Parent: not null } ? 1 : 0 };
            // A dot edge without a stored fallback falls back to `Resolve(Name)`: a callee position.
            if (node is Expr.DotCall { LexicalFallback: null } edge)
                frame.Add(edge.Name);
            if (node is Expr.NativeCall native)
                foreach (var name in native.ArgNames)
                    frame.Add(name);
            return frame;
        }

        internal void Add(string name) => _names.Add(name);

        internal void AddRange(TransportNames names) => _names.AddRange(names);

        internal readonly TransportNames Result() => _names.Result();
    }

    /// <summary>
    /// The per-cell J7 invariant of a per-site run (<see cref="EvaluationBudget.UsesPerSiteInvocationPlans"/>):
    /// every call-shaped cell a META binder can receive is a plan. A cell left ordinary by the per-site rule
    /// (a plain <see cref="ExpressionSuspension"/> over a written invocation, which a fully retaining run never
    /// forms) reaching a META binder is a defect of that rule, never a META refusal: fail loudly.
    /// </summary>
    private static void ThrowIfUnplannedCallReachesMeta(NeedCell cell, EvaluationBudget budget)
    {
        if (budget.UsesPerSiteInvocationPlans
            && cell.Suspension is { } suspension && suspension.GetType() == typeof(ExpressionSuspension)
            && cell.Source is { } source && IsPlannableCall(source))
            throw new InvalidOperationException(
                "A meta parameter received a call-shaped cell that per-site plan retention left unplanned (J7 false negative).");
    }
}
