using System.Collections.Immutable;
using System.Globalization;
using KatLang;
using KatLang.Tests.StructuralFuzz;

namespace KatLang.ParserFuzz;

/// <summary>
/// The WIDE nested-pattern production of the <c>seed-nested-wide</c> recipe (dotnet/fuzz/README.md
/// § Families and interactions). Where <see cref="SemanticGrammar.NestedPattern"/> is one two-level
/// clause, this production writes the shapes recent nested-pattern defects lived in: a parameter
/// list or a pattern group as the outer level, two or three levels, collectors at the outer and the
/// inner level, clause families that share one head name, runtime arity, kind and type failures,
/// every pattern group in one of three written extents (tight, padded, one item per line),
/// deconstruction of a nested result and of a nested collector, and intended front-end refusals.
///
/// <para><b>Head.</b> Level 1 is the outer structure — a pattern group <c>F((…))</c>, or the explicit
/// parameter list itself <c>F(…)</c>. Every level holds its structural child (or, at the deepest
/// level, a binder) and a fixed tail binder, so a sequence group never has one item; a collecting
/// level adds <c>*rest</c> (last at level 1, between the two fixed items below it). The call writes
/// data of exactly that shape: a list literal for a list level, a group for a sequence level, a
/// separate argument per parameter, one host effect (<c>trace</c>/<c>wait</c>, alternating in
/// source order) per leaf.</para>
///
/// <para><b>Expectation</b> follows the call-by-need laws (docs/design/language-rules/call-by-need.md):
/// cardinality is checked before any argument is demanded (NEED-05); a structural pattern demands
/// its argument's value (NEED-04) — a written SEQUENCE evaluates its items in source order, a written
/// LIST defers its elements, each run when it is first read (lazy collections, issue #204) — and
/// inspects it level by level: kind, count, then the items in written order, a nested level reading
/// its position, a literal reading its position, a name and a collector binding theirs unread; a
/// plain parameter keeps its cell until the body demands it, and a collected slice read only by
/// <c>count</c> runs nothing, while deconstructing a collector (<c>p, *q = rest</c>) demands its
/// VALUE, which runs every collected item in order (NEED-07). The body is a written list of every
/// binder in written order (a collector as its <c>count</c>): its elements run when the result is
/// READ — for a root row, when the run's assembled output is read
/// (<see cref="SemanticFragment.LateEvents"/>). The expectation is computed by a reference
/// evaluation of the written data (<see cref="Reference"/>), never by running the implementation.
/// Failures: a non-structure where a structure is expected and a list for a sequence (or the
/// reverse) are <c>TypeMismatch</c>; too many items for a level
/// without a collector, too many arguments, and a deconstruction that cannot bind are
/// <c>ArityMismatch</c>; a family none of whose clauses matches is <c>NoMatchingBranch</c>. Clauses
/// cannot collect, two clauses of one structure are duplicates whatever their extents, a one-item
/// sequence group is invalid, and all clauses take the same number of parameters (tutorial § Rules
/// for Clauses): those are the four intended refusals.</para>
///
/// <para>Every decision is a named pick (never a <see cref="SemanticChooser.Chance"/>), so the recipe
/// is finite and <see cref="SemanticExhaustive"/> enumerates it.</para>
/// </summary>
internal static class SemanticNestedWide
{
    internal static readonly ImmutableArray<string> Shapes =
        ["pattern", "parameters", "clauses", "deconstruct-result", "deconstruct-collector", "refusal"];

    internal static readonly ImmutableArray<string> Layouts = ["tight", "padded", "broken"];

    /// <summary>Single-definition outcomes; <c>arity</c> exists only when some level does not collect.</summary>
    internal static readonly ImmutableArray<string> Outcomes = ["ok", "type", "kind", "arity"];

    /// <summary>How the two clauses of a family differ at the deepest level.</summary>
    internal static readonly ImmutableArray<string> ClauseVariants = ["kind", "arity", "literal"];

    internal static readonly ImmutableArray<string> Targets = ["first", "second", "neither"];

    internal static readonly ImmutableArray<(string Name, DiagnosticCode Code, string Phase)> Refusals =
    [
        ("clause-collector", DiagnosticCode.InvalidCollectingBinding, SemanticExpectation.SyntaxPhase),
        ("duplicate-layout", DiagnosticCode.DuplicateBranchPattern, SemanticExpectation.SyntaxPhase),
        ("singleton-group", DiagnosticCode.SingletonSequencePattern, SemanticExpectation.SyntaxPhase),
        ("clause-arity", DiagnosticCode.BranchArityMismatch, SemanticExpectation.SyntaxPhase),
    ];

    /// <summary>The catch-all clause's whole result is <c>[0]</c>.</summary>
    internal const int CatchAllMarker = 0;

    /// <summary>The scalar written where a structure is expected (a <c>type</c> failure).</summary>
    internal const int NotAStructure = 99;

    /// <summary>One production and, unless it is a refusal, one consumer context around its row.</summary>
    internal static SemanticFragment Build(SemanticGrammar.Gen g)
    {
        SemanticFragment fragment;
        using (g.Span("production"))
        {
            fragment = Production(g);
            SemanticGrammar.DeferListRow(fragment);
        }

        if (fragment.Refusal is null)
        {
            using var contextSpan = g.Span("context");
            SemanticGrammar.ApplyContext(g, fragment, g.Pick("wide.context", SemanticGrammar.Contexts.Length));
        }

        return fragment;
    }

    private static SemanticFragment Production(SemanticGrammar.Gen g) => g.Pick("wide.shape", Shapes.Length) switch
    {
        0 => SingleShape(g, parameters: false),
        1 => SingleShape(g, parameters: true),
        2 => ClausesShape(g),
        3 => DeconstructResultShape(g),
        4 => DeconstructCollectorShape(g),
        _ => RefusalShape(g),
    };

    // ── Shapes ──────────────────────────────────────────────────────────────

    /// <summary>One definition: a pattern group (<paramref name="parameters"/> false) or a parameter list as level 1.</summary>
    private static SemanticFragment SingleShape(SemanticGrammar.Gen g, bool parameters)
    {
        var childLast = parameters && g.Pick("wide.order", 2) == 1;
        var depth = Depth(g);
        var kinds = Kinds(g, depth, parameters ? 2 : 1);
        var outerCollects = g.Pick("wide.collect", 2) == 1;
        var innerCollects = g.Pick("wide.collect", 2) == 1;
        int? arityLevel = !outerCollects ? 1 : !innerCollects ? 2 : depth == 3 ? 3 : null;
        var outcome = g.Pick("wide.outcome", arityLevel is null ? 3 : 4);
        // A scalar written for the deepest level of a two-level head removes that level's collector:
        // only ask for a width some written collector receives, so every choice sequence is its own program.
        var width = Width(g, outerCollects || (innerCollects && !(outcome == 1 && depth == 2)));
        var layout = g.Pick("wide.layout", Layouts.Length);

        var f = Fragment(parameters ? "parameters" : "pattern", depth, layout);
        var function = g.Fresh();
        var head = new Writer(g);
        var top = head.Levels(depth, kinds, outerCollects, innerCollects, childLast);
        var mutation = outcome switch
        {
            0 => Mutation.None,
            1 => Mutation.None with { AtomAt = depth },
            2 => Mutation.None with { SwapKindAt = depth },
            _ => Mutation.None with { ExtraAt = arityLevel },
        };

        var data = parameters ? head.Arguments(top, mutation, width) : [head.Data(top, mutation, width)];
        var body = head.Body(top);
        f.Decls.Add(new MDecl.Family(function, [new MClause(parameters ? head.ParameterHead(top, layout) : head.Pattern(top, layout),
            new MExpr.ListLit([.. body.Select(static b => b.Expr)]))]));
        f.Row = new MExpr.Call(function, data);
        Features(f, kinds, depth, outerCollects, innerCollects, parameters ? 2 : 1);

        if (parameters && mutation.ExtraAt == 1)
        {
            // One argument too many and no collecting parameter: rejected before any argument runs.
            f.FailureCategory = "ArityMismatch";
            f.Paths |= SemanticPath.CardinalityBeforeDemand;
        }
        else
        {
            var reference = new Reference(f);
            var binding = new Binding();
            string? error = null;
            if (parameters)
            {
                // A parameter list binds in written order: the structural parameter is inspected
                // at the call; plain parameters and collected arguments keep their cells.
                var at = 0;
                foreach (var item in top.Items())
                {
                    if (item == Item.Rest)
                    {
                        at += width;
                        continue;
                    }

                    var argument = new Cell(data[at++]);
                    if (item != Item.Child) binding.Bound[top.Tail] = argument;
                    else if ((error = Match(top.Child!, argument, binding, reference)) is not null) break;
                }
            }
            else
            {
                error = Match(top, new Cell(data[0]), binding, reference);
            }

            var expected = outcome switch { 0 => null, 3 => "ArityMismatch", _ => "TypeMismatch" };
            if (error != expected)
                throw new InvalidOperationException($"wide data is refused as {error ?? "nothing"}, its outcome says {expected ?? "nothing"}");
            if (outcome != 0) f.FailureCategory = expected;
            else
            {
                reference.ReadBody(body, binding);
                f.Value = new Result.ListValue([.. body.Select(static b => b.Value)]);
                if (parameters && outerCollects && width > 0) f.Paths |= SemanticPath.LazyTransport;
            }
        }

        if (outcome != 0) f.Features.UnionWith(["failure", "wide-outcome-" + Outcomes[outcome]]);
        return f;
    }

    /// <summary>A family of two clauses sharing one head name, differing at the deepest level, and optionally a catch-all.</summary>
    private static SemanticFragment ClausesShape(SemanticGrammar.Gen g)
    {
        var depth = Depth(g);
        var kinds = Kinds(g, depth, 1);
        var variant = g.Pick("wide.variant", ClauseVariants.Length);
        var catchAll = g.Pick("wide.catchAll", 2) == 1;
        var target = g.Pick("wide.target", Targets.Length);
        var layout = g.Pick("wide.layout", Layouts.Length);

        var f = Fragment("clauses", depth, layout);
        f.Features.UnionWith(["clause-family", "wide-variant-" + ClauseVariants[variant], "wide-target-" + Targets[target]]);
        if (catchAll) f.Features.Add("catch-all");
        var function = g.Fresh();
        var literal = variant == 2 ? g.Digit() : 0;
        var clauses = new Writer[2];
        var tops = new Level[2];
        for (var c = 0; c < 2; c++)
        {
            clauses[c] = new Writer(g);
            var top = clauses[c].Levels(depth, kinds, false, false, false);
            var deepest = top.Deepest;
            switch (variant)
            {
                case 0:
                    if (c == 1) deepest.IsList = !deepest.IsList;
                    break;
                case 1:
                    if (c == 1) deepest.Extra = g.Fresh();
                    break;
                default:
                    if (c == 0) deepest.HeadLiteral = literal;
                    break;
            }

            tops[c] = top;
        }

        // The data: the target clause's shape, or one no clause accepts.
        var chosen = target == 2 ? (variant == 1 ? 1 : 0) : target;
        var writer = clauses[chosen];
        var mutation = target != 2 ? Mutation.None
            : variant == 1 ? Mutation.None with { ExtraAt = depth } : Mutation.None with { AtomAt = depth };
        int? headValue = variant == 2 ? (target == 0 ? literal : (literal % 9) + 1) : null;
        var data = writer.Data(tops[chosen], mutation with { HeadValue = headValue }, 0);

        var familyClauses = new List<MClause>();
        for (var c = 0; c < 2; c++)
        {
            var body = clauses[c].Body(tops[c]);
            familyClauses.Add(new MClause(clauses[c].Pattern(tops[c], (layout + c) % Layouts.Length),
                new MExpr.ListLit([SemanticGrammar.Atom(c + 1), .. body.Select(static b => b.Expr)])));
        }

        if (catchAll)
            familyClauses.Add(new MClause(new MPattern.Binder(g.Fresh()), new MExpr.ListLit([SemanticGrammar.Atom(CatchAllMarker)])));
        f.Decls.Add(new MDecl.Family(function, familyClauses));
        f.Row = new MExpr.Call(function, [data]);
        Features(f, kinds, depth, false, false, 1);

        // The clauses are tried in order against ONE argument cell: what a refused clause read
        // stays read, and the next clause reads only what it inspects beyond that.
        var reference = new Reference(f);
        var argument = new Cell(data);
        var matched = -1;
        var binding = new Binding();
        for (var c = 0; c < 2 && matched < 0; c++)
        {
            binding = new Binding();
            if (Match(tops[c], argument, binding, reference) is null) matched = c;
        }

        if (matched != (target == 2 ? -1 : chosen))
            throw new InvalidOperationException($"wide clause data matches clause {matched}, its target says {target}");
        if (target != 2)
        {
            var body = writer.Body(tops[chosen]);
            reference.ReadBody(body, binding);
            f.Value = new Result.ListValue([SemanticGrammar.Res(chosen + 1), .. body.Select(static b => b.Value)]);
        }
        else if (catchAll)
        {
            f.Value = new Result.ListValue([SemanticGrammar.Res(CatchAllMarker)]);
        }
        else
        {
            f.FailureCategory = "NoMatchingBranch";
            f.Features.Add("failure");
        }

        return f;
    }

    /// <summary><c>p, *q = F(arg)</c> over a definition whose body is a sequence, or <c>p, q = …</c>, which cannot bind it.</summary>
    private static SemanticFragment DeconstructResultShape(SemanticGrammar.Gen g)
    {
        var depth = Depth(g);
        var kinds = Kinds(g, depth, 1);
        var outerCollects = g.Pick("wide.collect", 2) == 1;
        var innerCollects = g.Pick("wide.collect", 2) == 1;
        var width = Width(g, outerCollects || innerCollects);
        var collecting = g.Pick("wide.binders", 2) == 0;
        var layout = g.Pick("wide.layout", Layouts.Length);

        var f = Fragment("deconstruct-result", depth, layout);
        f.Features.Add("deconstruction");
        var function = g.Fresh();
        var head = new Writer(g);
        var top = head.Levels(depth, kinds, outerCollects, innerCollects, false);
        var data = head.Data(top, Mutation.None, width);
        var body = head.Body(top);
        f.Decls.Add(new MDecl.Family(function, [new MClause(head.Pattern(top, layout), new MExpr.Group([.. body.Select(static b => b.Expr)]))]));
        var p = g.Fresh();
        var q = g.Fresh();
        f.Decls.Add(new MDecl.Deconstruction([new MBinder(p, false), new MBinder(q, collecting)], new MExpr.Call(function, [data])));
        f.Row = new MExpr.ListLit([new MExpr.Ref(p), new MExpr.Ref(q)]);
        Features(f, kinds, depth, outerCollects, innerCollects, 1);

        // The row is a written list, read when the run's output is (DeferListRow). Its first
        // element p computes the shared right-hand side: the call — its pattern, then its body, a
        // written SEQUENCE, which reads every bound position in body order.
        var reference = new Reference(f);
        var binding = new Binding();
        if (Match(top, new Cell(data), binding, reference) is { } refused)
            throw new InvalidOperationException($"wide deconstruction data is refused as {refused}");
        reference.ReadPositions(body, binding);
        if (collecting)
        {
            f.Value = new Result.ListValue([body[0].Value, new Result.ListValue([.. body.Skip(1).Select(static b => b.Value)])]);
        }
        else
        {
            f.FailureCategory = "ArityMismatch"; // two names for at least three values
            f.Features.UnionWith(["failure", "wide-outcome-deconstruction-arity"]);
        }

        return f;
    }

    /// <summary>The body deconstructs the inner collector: <c>{ p, *q = rest ⏎ […, p, count(q), …] }</c>; an empty collector cannot bind <c>p</c>.</summary>
    private static SemanticFragment DeconstructCollectorShape(SemanticGrammar.Gen g)
    {
        var depth = Depth(g);
        var kinds = Kinds(g, depth, 1);
        var outerCollects = g.Pick("wide.collect", 2) == 1;
        var width = Width(g, true);
        var layout = g.Pick("wide.layout", Layouts.Length);

        var f = Fragment("deconstruct-collector", depth, layout);
        f.Features.Add("deconstruction");
        var function = g.Fresh();
        var head = new Writer(g);
        var top = head.Levels(depth, kinds, outerCollects, true, false);
        var data = head.Data(top, Mutation.None, width);
        var inner = top.Child!;
        var p = g.Fresh();
        var q = g.Fresh();
        var rows = new List<MExpr>();
        var values = new List<Result>();
        var bodyItems = head.Body(top);
        foreach (var item in bodyItems)
        {
            if (item.Collector == inner.Rest)
            {
                rows.Add(new MExpr.Ref(p));
                rows.Add(new MExpr.Prim("count", [new MExpr.Ref(q)]));
                if (width > 0)
                {
                    values.Add(SemanticGrammar.Res(head.CollectedValues(inner.Rest)[0]));
                    values.Add(SemanticGrammar.Res(width - 1));
                }

                continue;
            }

            rows.Add(item.Expr);
            values.Add(item.Value);
        }

        var block = new MExpr.Brace(new MScope(
            [new MDecl.Deconstruction([new MBinder(p, false), new MBinder(q, true)], new MExpr.Ref(inner.Rest))],
            [new MExpr.ListLit(rows)]));
        f.Decls.Add(new MDecl.Family(function, [new MClause(head.Pattern(top, layout), block)]));
        f.Row = new MExpr.Call(function, [data]);
        Features(f, kinds, depth, outerCollects, true, 1);

        var reference = new Reference(f);
        var binding = new Binding();
        if (Match(top, new Cell(data), binding, reference) is { } refused)
            throw new InvalidOperationException($"wide deconstruction data is refused as {refused}");

        // The body's list is read when the result is: each name in order, and at the inner
        // collector's place `p`, whose first read demands the deconstruction's right-hand side —
        // the collector's VALUE, which runs EVERY collected cell left to right (NEED-07), not only
        // the one `p` binds; `p` is then read whole, and `count(q)` after it runs nothing more.
        // An empty collector cannot bind `p`: that read is the failure, after the names before it.
        reference.ReadResult();
        foreach (var item in bodyItems)
        {
            if (item.Collector != inner.Rest)
            {
                reference.Read(item, binding);
                continue;
            }

            if (width == 0)
            {
                f.FailureCategory = "ArityMismatch"; // `p, *q` needs at least one collected item
                f.FailsLate = true;
                f.Features.UnionWith(["failure", "wide-outcome-deconstruction-arity"]);
                break;
            }

            var collected = binding.Collected[inner.Rest];
            foreach (var position in collected) reference.Force(position);
            reference.Whole(collected[0]);
        }

        if (width > 0) f.Value = new Result.ListValue(values);
        return f;
    }

    /// <summary>An intended front-end refusal; the row still calls the first clause with matching data.</summary>
    private static SemanticFragment RefusalShape(SemanticGrammar.Gen g)
    {
        var kind = g.Pick("wide.refusal", Refusals.Length);
        var depth = Depth(g);
        var kinds = Kinds(g, depth, 1);
        var layout = g.Pick("wide.layout", Layouts.Length);

        var f = Fragment("refusal", depth, layout);
        f.Refusal = Refusals[kind];
        var function = g.Fresh();
        var first = new Writer(g);
        var top = first.Levels(depth, kinds, false, kind == 0, false);
        var data = first.Data(top, Mutation.None, 1);
        var body = first.Body(top);
        var clauses = new List<MClause>();
        switch (kind)
        {
            case 0:
            case 1:
            {
                // A collecting first clause beside a second one of another deepest kind, or the
                // same structure again with fresh names in another written extent.
                var second = new Writer(g);
                var other = second.Levels(depth, kinds, false, false, false);
                if (kind == 0) other.Deepest.IsList = !other.Deepest.IsList;
                clauses.Add(new MClause(first.Pattern(top, layout), new MExpr.ListLit([SemanticGrammar.Atom(1), .. body.Select(static b => b.Expr)])));
                clauses.Add(new MClause(second.Pattern(other, (layout + 1) % Layouts.Length),
                    new MExpr.ListLit([SemanticGrammar.Atom(2), .. second.Body(other).Select(static b => b.Expr)])));
                break;
            }

            case 2:
                // `((inner), tail)`: the inner structure inside a redundant one-item sequence group.
                clauses.Add(new MClause(first.Pattern(top, layout, wrapChild: true), new MExpr.ListLit([.. body.Select(static b => b.Expr)])));
                break;
            default:
                clauses.Add(new MClause(first.Pattern(top, layout), new MExpr.ListLit([SemanticGrammar.Atom(1), .. body.Select(static b => b.Expr)])));
                clauses.Add(new MClause(new MPattern.LiteralPair(0, 0), new MExpr.ListLit([SemanticGrammar.Atom(2)])));
                break;
        }

        f.Decls.Add(new MDecl.Family(function, clauses));
        f.Row = new MExpr.Call(function, [data]);
        f.Value = new Result.ListValue([.. body.Select(static b => b.Value)]); // never observed: the front end refuses
        Features(f, kinds, depth, false, kind == 0, 1);
        f.Features.Add("refusal-" + Refusals[kind].Name);
        return f;
    }

    // ── Shared decisions ────────────────────────────────────────────────────

    private static int Depth(SemanticGrammar.Gen g) => 2 + g.Pick("wide.depth", 2);

    /// <summary>Each structural level's kind (true: list), from <paramref name="first"/> (2 when level 1 is a parameter list).</summary>
    private static bool[] Kinds(SemanticGrammar.Gen g, int depth, int first)
    {
        var kinds = new bool[depth + 1];
        for (var level = first; level <= depth; level++) kinds[level] = g.Pick("wide.kind", 2) == 1;
        return kinds;
    }

    /// <summary>Items each collector receives: none or two (asked only when something collects).</summary>
    private static int Width(SemanticGrammar.Gen g, bool collects) => collects && g.Pick("wide.width", 2) == 1 ? 2 : 0;

    private static SemanticFragment Fragment(string shape, int depth, int layout)
    {
        var f = new SemanticFragment("collect");
        f.Features.UnionWith(["collect", "nested-pattern", "nested-wide", "wide-" + shape, "layout-" + Layouts[layout]]);
        if (depth == 3) f.Features.Add("three-level");
        return f;
    }

    private static void Features(SemanticFragment f, bool[] kinds, int depth, bool outerCollects, bool innerCollects, int firstStructural)
    {
        for (var level = firstStructural; level <= depth; level++) f.Features.Add(kinds[level] ? "list-pattern" : "sequence-pattern");
        if (firstStructural == 2) f.Features.Add("parameter-list");
        if (outerCollects) f.Features.Add("collector-outer");
        if (innerCollects) f.Features.Add("collector-inner");
        if (outerCollects && innerCollects) f.Features.Add("collector-both-levels");
    }

    // ── Heads, data and expectations ────────────────────────────────────────

    /// <summary>Data changes that make a call fail: a scalar, the other kind, or one item too many at one level.</summary>
    private sealed record Mutation(int? AtomAt, int? SwapKindAt, int? ExtraAt, int? HeadValue)
    {
        public static readonly Mutation None = new(null, null, null, null);
    }

    /// <summary>One structural level of a head (level 1 is the outermost: a pattern group or the parameter list).</summary>
    private sealed class Level
    {
        public required int Number { get; init; }

        public required bool IsList { get; set; }

        public required bool Collects { get; init; }

        public required bool ChildLast { get; init; }

        public Level? Child { get; init; }

        public Sym Head { get; init; }

        public Sym Tail { get; init; }

        public Sym Rest { get; init; }

        /// <summary>A third fixed binder after the tail (the clause-arity variant).</summary>
        public Sym? Extra { get; set; }

        /// <summary>A literal written instead of the deepest head binder (the clause-literal variant).</summary>
        public int? HeadLiteral { get; set; }

        public Level Deepest => Child?.Deepest ?? this;

        /// <summary>The written items, in order.</summary>
        public IEnumerable<Item> Items()
        {
            var first = Child is null ? Item.Head : Item.Child;
            if (Number == 1)
            {
                if (ChildLast) yield return Item.Tail;
                yield return first;
                if (!ChildLast) yield return Item.Tail;
                if (Extra is not null) yield return Item.Extra;
                if (Collects) yield return Item.Rest;
                yield break;
            }

            yield return first;
            if (Collects) yield return Item.Rest;
            yield return Item.Tail;
            if (Extra is not null) yield return Item.Extra;
        }
    }

    private enum Item
    {
        Head,
        Child,
        Tail,
        Rest,
        Extra,
    }

    /// <summary>One body item: its expression, its constructed value, and the name it reads or the collector it counts.</summary>
    private sealed record BodyItem(MExpr Expr, Result Value, Sym? Collector, Sym? Binder = null);

    /// <summary>
    /// Writes one head, the matching call data and the expectation. Effects alternate trace and wait
    /// in source order (a fragment always has both kinds once it has two leaves).
    /// </summary>
    private sealed class Writer(SemanticGrammar.Gen g)
    {
        private readonly Dictionary<Sym, int> _bound = [];
        private readonly Dictionary<Sym, List<int>> _collected = [];
        private int _leaves;

        public List<int> CollectedValues(Sym collector) => _collected[collector];

        public Level Levels(int depth, bool[] kinds, bool outerCollects, bool innerCollects, bool childLast)
        {
            Level Make(int number)
            {
                var child = number < depth ? Make(number + 1) : null;
                var collects = number == 1 ? outerCollects : number == 2 && innerCollects;
                return new Level
                {
                    Number = number,
                    IsList = kinds[number],
                    Collects = collects,
                    ChildLast = number == 1 && childLast,
                    Child = child,
                    Head = child is null ? g.Fresh() : default,
                    Tail = g.Fresh(),
                    Rest = collects ? g.Fresh() : default,
                };
            }

            return Make(1);
        }

        /// <summary>The level as a structural pattern (all groups in one extent); <paramref name="wrapChild"/> writes <c>((child), …)</c>.</summary>
        public MPattern Pattern(Level level, int layout, bool wrapChild = false)
            => new MPattern.Structure(level.IsList, [.. level.Items().Select(item => ItemPattern(level, item, layout, wrapChild))], layout);

        /// <summary>Level 1 as an explicit parameter list.</summary>
        public MPattern ParameterHead(Level top, int layout)
            => new MPattern.ParameterList([.. top.Items().Select(item => ItemPattern(top, item, layout, false))]);

        private MPattern ItemPattern(Level level, Item item, int layout, bool wrapChild) => item switch
        {
            Item.Child when wrapChild => new MPattern.Structure(false, [Pattern(level.Child!, layout)], layout),
            Item.Child => Pattern(level.Child!, layout),
            Item.Head => level.HeadLiteral is { } literal ? new MPattern.Literal(literal) : new MPattern.Binder(level.Head),
            Item.Tail => new MPattern.Binder(level.Tail),
            Item.Extra => new MPattern.Binder(level.Extra!.Value),
            _ => new MPattern.Collecting(level.Rest),
        };

        /// <summary>The data of one structural level, written in source order.</summary>
        public MExpr Data(Level level, Mutation mutation, int width)
        {
            if (mutation.AtomAt == level.Number) return SemanticGrammar.Atom(NotAStructure);
            var items = new List<MExpr>();
            foreach (var item in level.Items()) items.AddRange(ItemData(level, item, mutation, width));
            if (mutation.ExtraAt == level.Number) items.Add(Effect(null, g.Digit()));
            var isList = mutation.SwapKindAt == level.Number ? !level.IsList : level.IsList;
            return isList ? new MExpr.ListLit(items) : new MExpr.Group(items);
        }

        /// <summary>Level 1 of a parameter list: one argument per written item (a collector's items are arguments too).</summary>
        public IReadOnlyList<MExpr> Arguments(Level top, Mutation mutation, int width)
        {
            var arguments = new List<MExpr>();
            foreach (var item in top.Items())
                arguments.AddRange(ItemData(top, item, mutation, width));

            if (mutation.ExtraAt == 1) arguments.Add(Effect(null, g.Digit()));
            return arguments;
        }

        private IEnumerable<MExpr> ItemData(Level level, Item item, Mutation mutation, int width)
        {
            switch (item)
            {
                case Item.Child:
                    yield return Data(level.Child!, mutation, width);
                    break;
                case Item.Head:
                    yield return Effect(level.HeadLiteral is null ? level.Head : null, mutation.HeadValue ?? g.Digit());
                    break;
                case Item.Tail:
                    yield return Effect(level.Tail, g.Digit());
                    break;
                case Item.Extra:
                    yield return Effect(level.Extra!.Value, g.Digit());
                    break;
                default:
                    var values = new List<int>();
                    _collected[level.Rest] = values;
                    for (var i = 0; i < width; i++)
                    {
                        var value = g.Digit();
                        values.Add(value);
                        yield return Effect(null, value);
                    }

                    break;
            }
        }

        private MExpr Effect(Sym? binder, int value)
        {
            var wait = _leaves++ % 2 == 1;
            if (binder is { } bound) _bound[bound] = value;
            return SemanticGrammar.Effect(wait, value);
        }

        /// <summary>Every binder in written order, depth first; a collector as its count.</summary>
        public List<BodyItem> Body(Level level)
        {
            var items = new List<BodyItem>();
            foreach (var item in level.Items())
            {
                switch (item)
                {
                    case Item.Child:
                        items.AddRange(Body(level.Child!));
                        break;
                    case Item.Head when level.HeadLiteral is not null:
                        break;
                    case Item.Rest:
                        var count = _collected.TryGetValue(level.Rest, out var values) ? values.Count : 0;
                        items.Add(new BodyItem(new MExpr.Prim("count", [new MExpr.Ref(level.Rest)]), SemanticGrammar.Res(count), level.Rest));
                        break;
                    default:
                        var binder = item switch { Item.Head => level.Head, Item.Tail => level.Tail, _ => level.Extra!.Value };
                        items.Add(new BodyItem(new MExpr.Ref(binder), SemanticGrammar.Res(_bound.GetValueOrDefault(binder)), null, binder));
                        break;
                }
            }

            return items;
        }
    }

    // ── The reference evaluation ────────────────────────────────────────────

    /// <summary>A value: a number, or a sequence/list of positions (a <see cref="V"/>, or an unread <see cref="Cell"/>).</summary>
    private abstract record V;

    private sealed record VScalar(int Value) : V;

    private sealed record VSeq(bool IsList, ImmutableArray<object> Items) : V;

    /// <summary>
    /// A deferred position — a written list's element, or a supplied argument — whose written
    /// data runs when the position is first read, once.
    /// </summary>
    private sealed class Cell(MExpr written)
    {
        public MExpr Written { get; } = written;

        public V? Value { get; set; }
    }

    /// <summary>The position each name is bound to, and the positions each collector took: all unread.</summary>
    private sealed class Binding
    {
        public Dictionary<Sym, object> Bound { get; } = [];

        public Dictionary<Sym, ImmutableArray<object>> Collected { get; } = [];
    }

    /// <summary>
    /// The reference evaluation of written data: each host effect is recorded when it runs — while
    /// the row is evaluated, or (after <see cref="ReadResult"/>) while the row's result is read.
    /// </summary>
    private sealed class Reference(SemanticFragment f)
    {
        private List<string> _events = f.Events;

        /// <summary>From here on the row's RESULT is being read: its effects are the fragment's late events.</summary>
        public void ReadResult()
        {
            _events = f.LateEvents;
            f.ReadsLate = true;
        }

        /// <summary>
        /// A written item's value. A sequence evaluates its items in order; a list defers every
        /// element that is not a literal number.
        /// </summary>
        public V Eval(MExpr written)
        {
            switch (written)
            {
                case MExpr.Atom atom:
                    return new VScalar((int)atom.Value);
                case MExpr.Prim { Name: "trace" or "wait" } effect:
                {
                    var value = (int)((MExpr.Atom)effect.Args[0]).Value;
                    _events.Add(effect.Name + ":" + value.ToString(CultureInfo.InvariantCulture));
                    if (effect.Name == "wait") f.Features.Add("async");
                    return new VScalar(value);
                }

                case MExpr.Group group:
                    return new VSeq(false, [.. group.Items.Select(item => (object)Eval(item))]);
                case MExpr.ListLit list:
                    return new VSeq(true, [.. list.Items.Select(item => item is MExpr.Atom ? (object)Eval(item) : new Cell(item))]);
                default:
                    throw new InvalidOperationException("not written data");
            }
        }

        /// <summary>A position's value: an unread cell runs now.</summary>
        public V Force(object position) => position is Cell cell ? cell.Value ??= Eval(cell.Written) : (V)position;

        /// <summary>A position's WHOLE value: every position below it read too, in order, depth first.</summary>
        public V Whole(object position)
        {
            var value = Force(position);
            if (value is VSeq sequence)
            {
                foreach (var below in sequence.Items) Whole(below);
            }

            return value;
        }

        /// <summary>One body item is read: a name reads its position whole; a collector's <c>count</c> reads none.</summary>
        public void Read(BodyItem item, Binding binding)
        {
            if (item.Binder is { } name) Whole(binding.Bound[name]);
        }

        /// <summary>The body's items are read in order, where the evaluation currently stands.</summary>
        public void ReadPositions(IEnumerable<BodyItem> body, Binding binding)
        {
            foreach (var item in body) Read(item, binding);
        }

        /// <summary>The body is a written list: its elements are read when the result is.</summary>
        public void ReadBody(IEnumerable<BodyItem> body, Binding binding)
        {
            ReadResult();
            ReadPositions(body, binding);
        }
    }

    /// <summary>
    /// One level against a position: its kind (the position is read), its count (exact, or at least
    /// the fixed items when it collects), then its items in written order, depth first — a nested
    /// level and a literal read their position, a name and a collector bind theirs unread. Returns
    /// the category of the first refusal (<c>NoMatch</c> for a literal that differs).
    /// </summary>
    private static string? Match(Level level, object position, Binding binding, Reference reference)
    {
        var value = reference.Force(position);
        if (value is not VSeq sequence || sequence.IsList != level.IsList) return "TypeMismatch";
        var items = level.Items().ToList();
        var fixedCount = items.Count(static item => item != Item.Rest);
        var count = sequence.Items.Length;
        if (level.Collects ? count < fixedCount : count != fixedCount) return "ArityMismatch";
        var at = 0;
        foreach (var item in items)
        {
            switch (item)
            {
                case Item.Rest:
                    binding.Collected[level.Rest] = [.. sequence.Items.Skip(at).Take(count - fixedCount)];
                    at += count - fixedCount;
                    break;
                case Item.Child:
                    if (Match(level.Child!, sequence.Items[at++], binding, reference) is { } refused) return refused;
                    break;
                case Item.Head when level.HeadLiteral is { } literal:
                    if (reference.Force(sequence.Items[at++]) is not VScalar scalar || scalar.Value != literal) return "NoMatch";
                    break;
                default:
                    var name = item switch { Item.Head => level.Head, Item.Tail => level.Tail, _ => level.Extra!.Value };
                    binding.Bound[name] = sequence.Items[at++];
                    break;
            }
        }

        return null;
    }
}
