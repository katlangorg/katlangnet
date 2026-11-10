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
/// ordinary cell only when that callee cannot pass the cell on — a callee body may still hand the
/// parameter to a value-only builtin it resolves at the occurrence (B9, <see cref="TransportsOnlyIntoValueBuiltins"/>).
/// Every other formation — a META builtin, an unknown slot after a spread, a callee kind this rule does not
/// classify, every <c>retained: true</c> site and every supply formed without a resolved callee (plan and view
/// preparation, deconstruction, selection) — stays a plan, as in a fully retaining run. So a cell reachable
/// from a stored reference through recorded plan supplies is always a plan. A META binder that receives a
/// call-shaped cell that is not a plan in such a run is an internal defect and fails loudly
/// (<see cref="ThrowIfUnplannedCallReachesMeta"/>).
/// <para><b>Plan/view preparation supplies stay fully planned (B8, researched 2026-11-10; not implemented).</b>
/// Giving a plan's VALUE preparation the callee its dispatch resolved would be sound only if a later loop
/// that captures the plan binds that sticky supply to the SAME callee, and only if E-18 covered the state it
/// creates. Neither holds in general. (1) The callees are obtained differently: the VALUE dispatch resolves
/// the written callee afresh (<c>ResolveCallee</c> in <c>EvalPlannedCallCounted</c>; the extension route resolves
/// its fallback by name), while the loop projects the plan's canonical callee cell, normalizes a projected
/// alias step itself, and dispatches a flat-binder family as a family where the VALUE dispatch binds its user
/// equivalent (<c>TryGetFlatBinderUserEquivalent</c>). Equality is a proof obligation for each route, not a fact
/// by construction. (2) A view-first capture prepares before any callee is known; projecting it there would
/// move a resolution ahead of LOOP-05 (a zero-round <c>repeat</c> never projects its step). (3) Even with equal
/// callees, a VALUE-then-META capture would leave ordinary cells reachable from the stored reference through
/// the captured plan's recorded supply. That state fails both E-18 candidate entry predicates
/// (<c>unreachableFromRefs</c>; <c>refFree</c>, which the Lean VALUE-then-META control already violates), and no
/// production invariant is discharged there, so the omission would rest on META behaviour E-18 leaves open.
/// A proof of (1) per route plus an E-18 statement for loop-only reachable states is the prerequisite.</para>
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
        // The distinct names, never mutated after construction: builders may share it (TransportNameBuilder).
        internal string[] KnownArray => names ?? [];
        internal bool Contains(string name) => names is null || Array.IndexOf(names, name) >= 0;
    }

    /// <summary>
    /// A bounded distinct-name set that saturates to EVERY name above <see cref="PerSiteAnalysisWidth"/>. Names
    /// mostly travel unchanged from a node to its ancestors, so the builder ADOPTS the first non-empty summary it
    /// receives (an immutable array, <see cref="TransportNames.KnownArray"/>) and copies it only when another name
    /// arrives; a few names live in a small array, more in a hash set. Membership and saturation are exactly
    /// those of one set: the representation changes only what a walk allocates (B10).
    /// </summary>
    private struct TransportNameBuilder
    {
        private const int SmallCapacity = 8;
        private string[]? _adopted;
        private string[]? _small;
        private int _smallCount;
        private HashSet<string>? _names;
        private bool _all;

        internal void Add(string name)
        {
            if (_all) return;
            if (_adopted is { } adopted)
            {
                if (Array.IndexOf(adopted, name) >= 0) return;
                _adopted = null;
                foreach (var known in adopted)
                    AddOwned(known);
            }
            AddOwned(name);
        }

        private void AddOwned(string name)
        {
            if (_all) return;
            if (_names is null)
            {
                for (var i = 0; i < _smallCount; i++)
                    if (_small![i] == name) return;
                if (_smallCount < SmallCapacity)
                {
                    (_small ??= new string[SmallCapacity])[_smallCount++] = name;
                    return;
                }
                _names = new(_small!, StringComparer.Ordinal);
                _small = null;
                _smallCount = 0;
            }
            if (_names.Add(name) && _names.Count > PerSiteAnalysisWidth)
                MarkAll();
        }

        private void MarkAll()
        {
            _all = true;
            _adopted = null;
            _small = null;
            _smallCount = 0;
            _names = null;
        }

        internal void AddRange(TransportNames names)
        {
            if (_all) return;
            if (names.IsAll)
            {
                MarkAll();
                return;
            }
            var known = names.KnownArray;
            if (known.Length == 0 || ReferenceEquals(known, _adopted)) return;
            if (_adopted is null && _smallCount == 0 && _names is null)
            {
                _adopted = known;
                return;
            }
            foreach (var name in known)
                Add(name);
        }

        internal readonly TransportNames Result()
            => _all ? default
                : _adopted is { } adopted ? new(adopted)
                : _names is { Count: > 0 } names ? new([.. names])
                : new(_smallCount > 0 ? _small!.AsSpan(0, _smallCount).ToArray() : []);
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
        if (CalleeTransportedNames(callee, budget).Contains(name) && !TransportsOnlyIntoValueBuiltins(callee, name, budget))
            return false;
        return !IsInheritedTransportName(name, budget);
    }

    /// <summary>
    /// <b>B9 — builtin-aware transport.</b> Whether every transport occurrence of the parameter
    /// <paramref name="name"/> in <paramref name="callee"/>'s body is a WHOLE ARGUMENT SLOT of a VALUE-ONLY
    /// BUILTIN CALL in the callee's own output rows — a call whose head is a NAME that resolves, at the
    /// occurrence, to a builtin without a META parameter — and every edge from that call up to its row is
    /// itself a value edge (<see cref="IsValueEdge"/>) or another value-only builtin call's whole slot:
    /// <c>F(x) = if(c, x, 0)</c>, <c>F(xs) = count(xs) + 1</c>, <c>F(xs) = max(count(xs), 1)</c>.
    /// <para>Why such a slot cannot pass the cell on. The slot receives the parameter's EXISTING cell
    /// (<see cref="SupplyCell"/> transports it), and a non-META builtin's arm treats a transported cell exactly
    /// as one formed at its own slot — which <see cref="IsUnobservedSupplySlot"/> already classifies as
    /// unobserved: it reads the VALUE, or projects a callable, and hands user code only Ready values. The
    /// condition on the call's ANCESTORS keeps the invariant every per-site run had before B9: a cell
    /// reachable from a stored reference through recorded plan supplies is a plan. Without it,
    /// <c>F(x) = count(x).while</c> would capture a plan of <c>count(x)</c> whose view-prepared supply
    /// transports x's ordinary cell, a state outside every candidate entry predicate of plan conservativity
    /// (E-18: <c>unreachableFromRefs</c>, <c>refFree</c>). With it, the builtin call is evaluated in place or
    /// supplied only to value-only builtins, so neither it nor x's cell ever reaches a META binder or a
    /// captured plan's supply, in this run or in a fully retaining one.</para>
    /// <para>Each head is resolved from RESOLVED OCCURRENCE FACTS, never from its spelling: the occurrence's
    /// scope is the activation of <paramref name="callee"/> itself (<see cref="EnterAlgorithmBody"/> pushes the
    /// bound callee — the very algorithm <see cref="FormNeedSupply"/> classifies against — and only a nested
    /// algorithm pushes another level), and a written name head resolves ownership-first
    /// (<see cref="LookupLexicalRaw"/>): its STRUCTURAL half (the callee's properties, then its parent chain,
    /// which ends at the run's prelude) is final when it selects a binding. So a head counts only when that
    /// structural walk selects a property whose value is the builtin itself. A shadowing declaration anywhere
    /// on the chain (<c>count(v) = v</c>), an alias, a structural miss (the <c>open</c> fallback, which may
    /// evaluate), a parameter or dot head and a META builtin all keep the slot transport. The check evaluates,
    /// charges and reports nothing: it reads the property lists the call's own lookup reads, through the same
    /// run-local index.</para>
    /// </summary>
    private static bool TransportsOnlyIntoValueBuiltins(Algorithm.User callee, string name, EvaluationBudget budget)
    {
        var summary = CalleeBuiltinSlotSummary(callee, budget);
        if (summary.Strict.Contains(name))
            return false;
        foreach (var (occurrence, head) in summary.Heads)
            if (occurrence == name && !ResolvesStructurallyToValueBuiltin(callee, head, budget))
                return false;
        return true;
    }

    // The structural half of the head's lexical lookup from the callee's activation (LookupLexicalStructural):
    // the callee's own properties, then each parent level's, through the run's property index.
    private static bool ResolvesStructurallyToValueBuiltin(Algorithm.User callee, string head, EvaluationBudget budget)
    {
        var property = budget.PropertyBindings.Lookup(callee.Properties, head);
        for (var level = callee.Parent; property is null && level is not null; level = level.Parent)
            property = budget.PropertyBindings.Lookup(level.Properties, head);
        return property?.Value is Algorithm.Builtin(var id) && !BuiltinRegistry.GetBuiltin(id).DeclaresMetaParameter;
    }

    /// <summary>
    /// A builtin-aware transport summary (<see cref="TransportsOnlyIntoValueBuiltins"/>). <see cref="Strict"/>
    /// names are transported unconditionally. A name with <see cref="Heads"/> pairs <c>(Name, Head)</c> occurs
    /// only below builtin-call slots: it is transported unless EVERY one of its heads resolves to a value-only
    /// builtin at the occurrence (a conjunction). Context-free — heads stay unresolved, so a node's summary is
    /// memoized by reference identity — and bounded: more than <see cref="PerSiteAnalysisWidth"/> pairs saturate
    /// <see cref="Strict"/> to EVERY name.
    /// </summary>
    internal readonly struct BuiltinSlotSummary(TransportNames strict, (string Name, string Head)[]? heads)
    {
        internal TransportNames Strict => strict;
        internal (string Name, string Head)[] Heads => heads ?? [];
    }

    // How a child's summary crosses the edge to its parent in the builtin-aware walk.
    private enum BuiltinSlotEdge
    {
        // A value edge (an operator operand, a selection's receiver) or a headed bundle's own call edge: pairs stay.
        Value,
        // A whole slot of a builtin-headed call: each paired name gains the call's head as one more condition.
        HeadedSlot,
        // Any other edge: the child may be a supplied cell that reaches META, so its paired names are transport.
        Opaque,
    }

    private struct BuiltinSlotSummaryBuilder
    {
        private TransportNameBuilder _strict;
        private HashSet<(string Name, string Head)>? _heads;
        private bool _all;

        internal void AddStrict(string name)
        {
            if (!_all) _strict.Add(name);
        }

        internal void AddStrict(TransportNames names)
        {
            if (_all) return;
            if (names.IsAll) MarkAll();
            else _strict.AddRange(names);
        }

        internal void AddHead(string name, string head)
        {
            if (_all) return;
            _heads ??= [];
            if (_heads.Add((name, head)) && _heads.Count > PerSiteAnalysisWidth)
                MarkAll();
        }

        internal void Add(BuiltinSlotSummary summary, BuiltinSlotEdge edge, string? slotHead)
        {
            AddStrict(summary.Strict);
            foreach (var (name, head) in summary.Heads)
            {
                if (edge == BuiltinSlotEdge.Opaque)
                {
                    AddStrict(name);
                    continue;
                }
                AddHead(name, head);
                if (edge == BuiltinSlotEdge.HeadedSlot)
                    AddHead(name, slotHead!);
            }
        }

        private void MarkAll()
        {
            _all = true;
            _heads = null;
            _strict.AddRange(default);
        }

        internal readonly BuiltinSlotSummary Result()
            => _all ? new(default, null) : new(_strict.Result(), _heads is { Count: > 0 } heads ? [.. heads] : null);
    }

    /// <summary>
    /// <see cref="BuiltinSlotSummaryOf"/> for a user CALLEE, memoized by its body lists like
    /// <see cref="CalleeTransportedNames"/>: its opens, properties and parameter patterns contribute their
    /// <see cref="TransportedNamesOf"/> names as strict transport (another scope, or no row); an output row
    /// that is a bare name is a value position for an own capture (<see cref="IsValueEdge"/>), and any other
    /// row contributes its builtin-aware summary — the row's value is the callee's result, never a supplied
    /// cell. The strict and paired names together are a subset of the callee's <see cref="TransportedNamesOf"/>
    /// names: the refinement only ever proves more names untransported.
    /// </summary>
    private static BuiltinSlotSummary CalleeBuiltinSlotSummary(Algorithm.User callee, EvaluationBudget budget)
    {
        var key = new CalleeBodyKey(callee.Output, callee.Properties, callee.Opens, callee.ParameterPatterns);
        lock (budget.TransportedNames)
        {
            var bodies = budget.CalleeBuiltinSlotSummaries;
            if (bodies.TryGetValue(key, out var known))
                return known;
            var builder = new BuiltinSlotSummaryBuilder();
            var firstRow = (callee.Parent is null ? 0 : 1) + callee.Opens.Count + callee.Properties.Count;
            for (var index = callee.Parent is null ? 0 : 1; AstStructuralPreflight.TryGetChild(callee, index, out var child); index++)
            {
                var row = index - firstRow;
                if (child is Expr.Param or Expr.Resolve)
                {
                    var param = child is Expr.Param(var parameterName) ? parameterName : ((Expr.Resolve)child).Name;
                    if (!IsValueEdge(callee, index, param))
                        builder.AddStrict(param);
                }
                else if (row >= 0 && row < callee.Output.Count)
                    builder.Add(BuiltinSlotSummaryOf(child, budget), BuiltinSlotEdge.Value, slotHead: null);
                else
                    builder.AddStrict(TransportedNamesOf(child, budget));
            }
            var summary = builder.Result();
            bodies[key] = summary;
            return summary;
        }
    }

    /// <summary>
    /// The builtin-aware summary (<see cref="BuiltinSlotSummary"/>) of an output-row node: exactly
    /// <see cref="TransportedNamesOf"/>'s classification, except that an occurrence that is a whole argument slot
    /// of <c>Call(Resolve(head), …)</c> becomes a <c>(name, head)</c> pair instead of a strict name, and a pair
    /// crosses each further edge only as <see cref="BuiltinSlotEdge"/> allows. The walk descends only through
    /// expressions and argument bundles of the row's own scope: an algorithm (a nested body, block or family)
    /// and every other node contribute their <see cref="TransportedNamesOf"/> names as strict transport.
    /// Memoized per node by reference identity (<see cref="EvaluationBudget.BuiltinSlotSummaries"/>), so a shared
    /// subgraph is expanded once. A call's argument bundle is summarized against ITS head and is therefore not
    /// memoized as a node (a lifted bundle may be shared by calls with different heads); only bundles of at most
    /// <see cref="PerSiteAnalysisWidth"/> slots are, each slot's subtree memoized, so the work stays linear. No
    /// CLR recursion; nothing is charged. Called under the run's analysis lock.
    /// </summary>
    private static BuiltinSlotSummary BuiltinSlotSummaryOf(object root, EvaluationBudget budget)
    {
        var memo = budget.BuiltinSlotSummaries;
        if (memo.TryGetValue(root, out var rootKnown))
            return rootKnown;
        if (!IsBuiltinSlotWalkNode(root))
            return new(TransportedNamesOf(root, budget), null);

        var frames = new List<BuiltinSlotFrame> { BuiltinSlotFrame.Enter(root, head: null, BuiltinSlotEdge.Value, slotHead: null) };
        while (true)
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
                        break;
                    case Expr.Param or Expr.Resolve:
                    {
                        var name = child is Expr.Param(var parameterName) ? parameterName : ((Expr.Resolve)child).Name;
                        if (frame.Head is { } head)
                            frame.Summary.AddHead(name, head);
                        else if (!IsValueEdge(frame.Node, index, name))
                            frame.Summary.AddStrict(name);
                        break;
                    }
                    case OutputBundle { Count: <= PerSiteAnalysisWidth } arguments
                        when frame.Node is Expr.Call { Function: Expr.Resolve(var callHead) } call && ReferenceEquals(call.Args, arguments):
                        frames[top] = frame;
                        frames.Add(BuiltinSlotFrame.Enter(arguments, callHead, BuiltinSlotEdge.Value, slotHead: null));
                        continue;
                    default:
                    {
                        var edge = frame.Head is not null ? BuiltinSlotEdge.HeadedSlot
                            : IsValueEdge(frame.Node, index, string.Empty) ? BuiltinSlotEdge.Value
                            : BuiltinSlotEdge.Opaque;
                        if (memo.TryGetValue(child, out var known))
                            frame.Summary.Add(known, edge, frame.Head);
                        else if (IsBuiltinSlotWalkNode(child))
                        {
                            frames[top] = frame;
                            frames.Add(BuiltinSlotFrame.Enter(child, head: null, edge, frame.Head));
                            continue;
                        }
                        else
                            frame.Summary.AddStrict(TransportedNamesOf(child, budget));
                        break;
                    }
                }
                frames[top] = frame;
                continue;
            }

            var summary = frame.Summary.Result();
            // A headed bundle's summary belongs to its call, not to the bundle node.
            if (frame.Head is null)
                memo[frame.Node] = summary;
            frames.RemoveAt(top);
            if (top == 0)
                return summary;
            var parent = frames[top - 1];
            parent.Summary.Add(summary, frame.Edge, frame.SlotHead);
            frames[top - 1] = parent;
        }
    }

    // The nodes the builtin-aware walk descends through: the row's own expressions and argument bundles.
    // An algorithm (its own scope) and every other node are summarized by TransportedNamesOf.
    private static bool IsBuiltinSlotWalkNode(object node)
        => node is OutputBundle || node is Expr and not Expr.AlgorithmExpr;

    private struct BuiltinSlotFrame
    {
        internal object Node;
        internal int Next;
        // Non-null for a call's argument bundle whose call head is this written name.
        internal string? Head;
        // How this node's summary crosses the edge to its parent frame (with the parent bundle's head).
        internal BuiltinSlotEdge Edge;
        internal string? SlotHead;
        internal BuiltinSlotSummaryBuilder Summary;

        internal static BuiltinSlotFrame Enter(object node, string? head, BuiltinSlotEdge edge, string? slotHead)
        {
            var frame = new BuiltinSlotFrame { Node = node, Head = head, Edge = edge, SlotHead = slotHead };
            // As TransportFrame.Enter: a dot edge's default fallback and a host call's argument names.
            if (node is Expr.DotCall { LexicalFallback: null } edgeNode)
                frame.Summary.AddStrict(edgeNode.Name);
            if (node is Expr.NativeCall native)
                foreach (var name in native.ArgNames)
                    frame.Summary.AddStrict(name);
            return frame;
        }
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
                names = budget.InheritedTransportNames ??= InheritedTransportNames(program, budget.AdmittedTreeNodeCount);
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
    internal static TransportNames InheritedTransportNames(object root, int treeNodeCount = 0)
        => treeNodeCount > 0 && InheritedTransportNamesCore(root, treeNodeCount) is { } tree
            ? tree
            : InheritedTransportNamesCore(root, treeNodeCount: 0)!.Value;

    /// <summary>
    /// <see cref="InheritedTransportNames"/>'s walk. With <paramref name="treeNodeCount"/> = 0 it memoizes every
    /// completed node and keeps the path set, so a shared subgraph is expanded once and a cycle is cut. A positive
    /// count is the ADMISSION FACT that the graph is a tree of that many distinct nodes
    /// (<see cref="AstStructuralPreflight.AdmittedProgramFacts.TreeNodeCount"/>, the same child enumeration): each
    /// node is then reached exactly once, so the memo and the path set are dead weight — the fixed per-run
    /// cost of a loop-only run (B10) — and the walk keeps neither. The count still BOUNDS it: a walk that would
    /// enter more frames than the admitted nodes is not over that tree (an unstable host collection), and returns
    /// null so the caller falls back to the memoized walk. Both modes compute the same names on a tree.
    /// </summary>
    private static TransportNames? InheritedTransportNamesCore(object root, int treeNodeCount)
    {
        var memo = treeNodeCount > 0 ? null
            : new Dictionary<object, (TransportNames Pending, TransportNames Inherited)>(ReferenceEqualityComparer.Instance);
        var onPath = treeNodeCount > 0 ? null : new HashSet<object>(ReferenceEqualityComparer.Instance) { root };
        var entered = 1;
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
                        if (memo is not null && memo.TryGetValue(child, out var known))
                            frame.Merge(known, scopeEdge);
                        else if (onPath is null ? ++entered <= treeNodeCount : onPath.Add(child))
                        {
                            frame.ScopeChild = scopeEdge;
                            frames[top] = frame;
                            frames.Add(InheritFrame.Enter(child));
                            continue;
                        }
                        else if (onPath is null)
                            return null; // more frames than the admitted tree holds: not that tree
                        break;
                }
                frames[top] = frame;
                continue;
            }

            var result = frame.Complete();
            if (memo is not null)
            {
                memo[frame.Node] = result;
                onPath!.Remove(frame.Node);
            }
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
