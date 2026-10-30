using System.Numerics;

namespace KatLang;

/// <summary>
/// Immutable written-occurrence DAG. Flow guards are graph edges, never copied root-to-node histories. Incoming
/// activation is OR; an edge into a lexical fallback is additionally guarded by that written dot's selection.
/// </summary>
internal sealed class StaticInputGraph
{
    internal sealed record Link(Expr Node, Expr.DotCall? Guard = null);
    internal sealed class Node(Expr expression)
    {
        internal Expr Expression { get; } = expression;
        internal List<Link> Children { get; } = [];
        internal List<Link> Parents { get; } = [];
        internal int Roots;
    }
    internal Dictionary<Expr, Node> Nodes { get; } = new(ReferenceEqualityComparer.Instance);
    internal Dictionary<string, List<Expr>> Uses { get; } = new(StringComparer.Ordinal);
    internal List<string> Names { get; } = [];
    internal IReadOnlyList<Expr> Rows { get; }
    internal List<Node> Topological { get; } = [];
    internal long RetainedStorageUnits { get; private set; }

    internal StaticInputGraph(IReadOnlyList<Expr> rows, StaticQueryResourceBudget? resourceBudget = null, CancellationToken cancellationToken = default)
    {
        Rows = rows;
        using var storage = resourceBudget?.Temporary();
        storage?.Add(2L * rows.Count, cancellationToken);
        var pending = new Stack<Expr>(rows.Reverse());
        while (pending.TryPop(out var expression))
        {
            cancellationToken.ThrowIfCancellationRequested();
            if (Nodes.ContainsKey(expression)) continue;
            resourceBudget?.Metadata(6, cancellationToken: cancellationToken);
            RetainedStorageUnits += 6;
            var node = new Node(expression);
            Nodes.Add(expression, node);
            if (expression is Expr.Resolve { Name.Length: > 0 } resolve)
            {
                if (!Uses.TryGetValue(resolve.Name, out var uses)) { Uses.Add(resolve.Name, uses = []); Names.Add(resolve.Name); }
                uses.Add(expression);
            }
            foreach (var child in Children(expression))
            {
                cancellationToken.ThrowIfCancellationRequested();
                resourceBudget?.Metadata(2, cancellationToken: cancellationToken);
                RetainedStorageUnits += 2;
                node.Children.Add(child);
            }
            for (var i = node.Children.Count - 1; i >= 0; i--) pending.Push(node.Children[i].Node);
        }
        foreach (var row in rows) Nodes[row].Roots++;
        foreach (var node in Nodes.Values)
            foreach (var child in node.Children)
            {
                cancellationToken.ThrowIfCancellationRequested();
                resourceBudget?.Metadata(2, cancellationToken: cancellationToken);
                RetainedStorageUnits += 2;
                Nodes[child.Node].Parents.Add(new(node.Expression, child.Guard));
            }
        storage?.Add(3L * Nodes.Count, cancellationToken);
        var counts = new Dictionary<Node, int>();
        var ready = new Queue<Node>();
        foreach (var node in Nodes.Values)
        {
            cancellationToken.ThrowIfCancellationRequested();
            counts.Add(node, node.Parents.Count);
            if (node.Parents.Count == 0) ready.Enqueue(node);
        }
        while (ready.TryDequeue(out var node))
        {
            cancellationToken.ThrowIfCancellationRequested();
            Topological.Add(node);
            foreach (var child in node.Children)
            {
                cancellationToken.ThrowIfCancellationRequested();
                if (--counts[Nodes[child.Node]] == 0) ready.Enqueue(Nodes[child.Node]);
            }
        }
        if (Topological.Count != Nodes.Count) throw new InvalidOperationException("Static inputs require a preflighted acyclic syntax graph.");
    }

    private static IEnumerable<Link> Children(Expr expression)
    {
        switch (expression)
        {
            case Expr.DotCall edge:
                yield return new(edge.Target);
                yield return new(edge.EffectiveLexicalFallback, edge);
                if (edge.Args is { } dotArguments) foreach (var argument in dotArguments) yield return new(argument);
                break;
            case Expr.Call(var callee, var arguments):
                yield return new(callee);
                foreach (var argument in arguments) yield return new(argument);
                break;
            case Expr.Binary(_, var left, var right):
                yield return new(left); yield return new(right); break;
            case Expr.SequenceConstruct(var left, var right):
                yield return new(left); yield return new(right); break;
            case Expr.Unary(_, var operand): yield return new(operand); break;
            case Expr.SequenceSpread(var operand): yield return new(operand); break;
            case Expr.Grace(var operand, _): yield return new(operand); break;
            case Expr.Comparison(var first, var links):
                yield return new(first); foreach (var link in links) yield return new(link.Operand); break;
            case Expr.Index(var target, var selectors):
                yield return new(target); foreach (var selector in selectors) yield return new(selector); break;
            case Expr.ListLiteral(var items): foreach (var item in items) yield return new(item); break;
            case Expr.Capture(var items): foreach (var item in items) yield return new(item); break;
            case Expr.InterpolatedString(_, var links): foreach (var link in links) yield return new(link.Hole); break;
            case Expr.Resolve or Expr.AlgorithmExpr or Expr.Num or Expr.Param or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence or Expr.NativeCall:
                break;
            default: throw new InvalidOperationException($"Unhandled static input expression: {expression.GetType().Name}");
        }
    }
}

internal sealed partial class StaticStructureQueries
{
    private static StaticFact And(StaticFact a, StaticFact b)
        => a.Kind == StaticFactKind.No || b.Kind == StaticFactKind.No ? StaticFact.No
            : a.Kind == StaticFactKind.Yes && b.Kind == StaticFactKind.Yes ? StaticFact.Yes : StaticFact.Unknown;
    private static StaticFact Or(StaticFact a, StaticFact b)
        => a.Kind == StaticFactKind.Yes || b.Kind == StaticFactKind.Yes ? StaticFact.Yes
            : a.Kind == StaticFactKind.No && b.Kind == StaticFactKind.No ? StaticFact.No : StaticFact.Unknown;
    private StaticFact FallbackUse(StaticScopeKey scope, Expr.DotCall edge, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (edge.UsesDotMissIntrinsic()) return StaticFact.No;
        var selection = reader.Read(StaticQueryKey.MissSelection(scope, edge));
        return selection.IsUnknown
            ? reader.Read(Project(StaticQueryKind.MissSelection, scope, StaticQueryProjection.FallbackParticipation, node: edge))
            : selection.Kind == StaticFactKind.Never ? StaticFact.No : StaticFact.Yes;
    }
    private StaticFact Activation(BodyContext context, Expr expression, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        var node = context.Syntax.Nodes[expression];
        return node.Roots != 0 ? StaticFact.Yes : reader.Read(StaticQueryKey.Project(StaticQueryKind.IsInput, context.Key,
            StaticQueryProjection.ActivationRange, node: expression, length: node.Parents.Count));
    }
    private StaticFact ActivationRange(BodyContext context, StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (key.Length == 0) return StaticFact.No;
        if (key.Length == 1)
        {
            var link = context.Syntax.Nodes[key.Node!].Parents[key.Offset];
            var active = reader.Read(Project(StaticQueryKind.IsInput, context.Key, StaticQueryProjection.InputUse, node: link.Node));
            return link.Guard is { } edge ? And(active, FallbackUse(context.Key, edge, reader)) : active;
        }
        var half = key.Length / 2;
        return Or(reader.Read(StaticQueryKey.Project(key.Kind, key.Scope, key.Projection, node: key.Node, offset: key.Offset, length: half)),
            reader.Read(StaticQueryKey.Project(key.Kind, key.Scope, key.Projection, node: key.Node, offset: key.Offset + half, length: key.Length - half)));
    }
    private StaticFact InputRange(BodyContext context, StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (key.Length == 0) return key.Name is null ? StaticFact.No : StaticFact.Yes;
        if (key.Length > 1)
        {
            var half = key.Length / 2;
            var a = reader.Read(StaticQueryKey.Project(key.Kind, key.Scope, key.Projection, key.Name, offset: key.Offset, length: half));
            var b = reader.Read(StaticQueryKey.Project(key.Kind, key.Scope, key.Projection, key.Name, offset: key.Offset + half, length: key.Length - half));
            return key.Name is null ? Or(a, b) : And(a, b);
        }
        var input = reader.Read(StaticQueryKey.IsInput(context.Key, context.Syntax.Names[key.Offset]));
        return key.Name == "none" ? input.IsUnknown ? input : input.Kind == StaticFactKind.Yes ? StaticFact.No : StaticFact.Yes
            : input.IsUnknown ? input : StaticFact.Yes;
    }
    private StaticFact NoInputs(BodyContext context, StaticQueryReader<StaticQueryKey, StaticFact> reader)
        => reader.Read(StaticQueryKey.Project(StaticQueryKind.IsInput, context.Key, StaticQueryProjection.InputRange,
            "none", length: context.Syntax.Names.Count));

    private StaticFact InputUses(BodyContext context, StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (key.Length == 0) return StaticFact.No;
        if (key.Length == 1)
            return reader.Read(Project(StaticQueryKind.IsInput, context.Key, StaticQueryProjection.InputUse, node: context.Syntax.Uses[key.Name!][key.Offset]));
        var half = key.Length / 2;
        return Or(reader.Read(StaticQueryKey.Project(key.Kind, key.Scope, key.Projection, key.Name, offset: key.Offset, length: half)),
            reader.Read(StaticQueryKey.Project(key.Kind, key.Scope, key.Projection, key.Name, offset: key.Offset + half, length: key.Length - half)));
    }

    private StaticFact IsInput(BodyContext context, string name, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (!context.Infers || context.WrittenParameters.Contains(name) || context.Members.Declared(name) is not null
            || !context.Syntax.Uses.TryGetValue(name, out var uses)) return StaticFact.No;
        var available = reader.Read(Project(StaticQueryKind.Binding, context.Key, StaticQueryProjection.InferenceBinding, name));
        var unbound = available.IsUnknown ? available : available.Kind == StaticFactKind.Missing ? StaticFact.Yes : StaticFact.No;
        if (unbound.Kind == StaticFactKind.No) return unbound;
        var participation = reader.Read(StaticQueryKey.Project(StaticQueryKind.IsInput, context.Key, StaticQueryProjection.InputUses,
            name, length: uses.Count));
        var result = And(unbound, participation);
        if (result.Kind == StaticFactKind.No || ReferenceEquals(context.Key, Root)) return result;
        // OD-B is decided from pre-existing ownership, excluding this body's candidate inference.
        if (context.Body is Algorithm.User { ParameterPatterns.Count: 0, Output.Count: 1 } body
            && context.Syntax.Rows.Count == 1 && body.Output[0] is Expr.DotCall { Args: null })
        {
            var head = body.Output[0];
            while (head is Expr.DotCall { Args: null } edge) head = edge.Target;
            var parameterRoot = head is Expr.Param ? StaticFact.Yes : head is Expr.Resolve resolve
                ? reader.Read(Project(StaticQueryKind.Binding, context.Key, StaticQueryProjection.InferenceBinding, resolve.Name)) : StaticFact.No;
            var exemption = parameterRoot.HasUnknownSelection ? StaticFact.Unknown : parameterRoot.Kind == StaticFactKind.Parameter ? StaticFact.Yes : StaticFact.No;
            return exemption.Kind == StaticFactKind.Yes ? StaticFact.No : exemption.IsUnknown ? StaticFact.Unknown : result;
        }
        return result;
    }

    private StaticFact Inputs(BodyContext context, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (!context.Infers) return new(StaticFactKind.Inputs, Data: Array.Empty<string>());
        var syntax = context.Syntax;
        var decided = reader.Read(StaticQueryKey.Project(StaticQueryKind.IsInput, context.Key, StaticQueryProjection.InputRange,
            "decided", length: syntax.Names.Count));
        if (decided.IsUnknown) return decided;
        using var storage = Resources.Temporary();
        storage.Add(6L * syntax.Nodes.Count + 4L * syntax.Names.Count + syntax.Rows.Count, _cancellationToken);
        var inferred = new HashSet<string>(StringComparer.Ordinal);
        foreach (var name in syntax.Names)
            if (reader.Read(StaticQueryKey.IsInput(context.Key, name)).Kind == StaticFactKind.Yes) inferred.Add(name);
        if (inferred.Count == 0) return new(StaticFactKind.Inputs, Data: Array.Empty<string>());
        var order = new List<string>();
        var ordered = new HashSet<string>(StringComparer.Ordinal);
        var weights = new Dictionary<string, BigInteger>(StringComparer.Ordinal);
        var seen = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Expr>(syntax.Rows.Reverse());
        while (pending.TryPop(out var expression))
        {
            Resources.Metadata(0, cancellationToken: _cancellationToken);
            if (!seen.Add(expression)) continue;
            if (expression is Expr.Resolve resolve && inferred.Contains(resolve.Name) && ordered.Add(resolve.Name)) order.Add(resolve.Name);
            var children = syntax.Nodes[expression].Children;
            for (var i = children.Count - 1; i >= 0; i--)
            {
                if (children[i].Guard is { } edge)
                {
                    var guard = FallbackUse(context.Key, edge, reader);
                    if (guard.IsUnknown) return guard;
                    if (guard.Kind == StaticFactKind.No) continue;
                }
                pending.Push(children[i].Node);
            }
        }
        var multiplicity = new Dictionary<Expr, BigInteger>(ReferenceEqualityComparer.Instance);
        foreach (var row in syntax.Rows) multiplicity[row] = multiplicity.GetValueOrDefault(row) + 1;
        foreach (var node in syntax.Topological)
        {
            Resources.Metadata(0, cancellationToken: _cancellationToken);
            multiplicity.Remove(node.Expression, out var count);
            if (count.IsZero) continue;
            if (node.Expression is Expr.Grace(var operand, var weight) && operand.UnwrapGraceOperand() is Expr.Resolve(var name) && inferred.Contains(name))
                weights[name] = weights.GetValueOrDefault(name) + weight * count;
            foreach (var child in node.Children)
            {
                if (child.Guard is { } edge)
                {
                    var guard = FallbackUse(context.Key, edge, reader);
                    if (guard.IsUnknown) return guard;
                    if (guard.Kind == StaticFactKind.No) continue;
                }
                multiplicity[child.Node] = multiplicity.GetValueOrDefault(child.Node) + count;
            }
        }
        GraceMovement.Apply(order, weights);
        Resources.Metadata(order.Count, cancellationToken: _cancellationToken);
        return new(StaticFactKind.Inputs, Data: order.ToArray());
    }
}
