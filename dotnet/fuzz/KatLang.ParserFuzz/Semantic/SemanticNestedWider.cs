using System.Collections.Immutable;
using System.Globalization;
using KatLang;
using KatLang.Tests.StructuralFuzz;

namespace KatLang.ParserFuzz;

/// <summary>
/// The WIDER nested-pattern production of the <c>seed-nested-wider</c> recipe (dotnet/fuzz/README.md
/// § Families and interactions). It writes what <see cref="SemanticNestedWide"/> does not:
/// collectors at every level including the third, each collecting level's collector placed first,
/// in the middle or last; repeated names in nested positions (NEED-04's group-aware repeated names,
/// ALIAS-UNIFY-1) in a single pattern, a parameter list and a clause family; spreads inside nested
/// data (a whole level, a leading pair, an empty spread); and META parameters over nested patterns —
/// a META parameter beside a nested structural parameter, and a META capture of a call whose target
/// has a nested head.
///
/// <para><b>Shapes.</b> <c>placement</c>: a two- or three-level pattern whose levels collect by a
/// chosen subset, each collector placed by a rotation of one choice, with an extra item at the deepest
/// non-collecting level or the deepest level's last item missing. <c>repeated</c>: one name written
/// twice — the deepest head and the outer tail, the deepest tail and its parent's tail, or the deepest
/// head and tail — with equal or unequal data, as a single pattern, a parameter list and a clause
/// family with a catch-all. <c>spread</c>: one level's data written as <c>(items)*</c>, a leading
/// <c>(i0, i1)*</c> or with an inserted <c>()*</c>, optionally one item more inside the spread.
/// <c>meta-head</c>: <c>F(meta m, (…), t)</c> or <c>F((…), t, meta m)</c> whose body counts or
/// invokes <c>m</c> (or ignores it), with a refused META argument or a scalar where the deepest
/// structure is expected. <c>meta-target</c>: <c>r = Cap(T(data))</c> over a nested head <c>T</c>,
/// then two operations among <c>r.Arguments.count</c>, <c>r.Invoke()</c>, <c>r.Algorithm(fresh)</c>
/// and <c>r.Algorithm(r.Arguments*)</c>, optionally followed by a fresh call of the wrong shape.</para>
///
/// <para><b>Expectation</b> is computed by a reference binder over the written data (never by running
/// the implementation), following docs/design/language-rules/call-by-need.md and the sequence rules:
/// a structural pattern demands its argument's value (NEED-04): a written SEQUENCE evaluates its
/// items in source order, while a written LIST defers its ordinary elements — each is one cell, run
/// when it is first read — and evaluates only its spread operands (lazy collections, issue #204); a
/// written group's spread items are spliced in place and a sequence of exactly one item is that item;
/// a level checks its kind (<c>TypeMismatch</c>), then its count — exact, or at least the fixed items
/// when it collects (<c>ArityMismatch</c>) — then its items left to right, depth first: a nested
/// level reads its position, a name binds its position UNREAD, and a collector takes the positions
/// between the fixed items before and after it, unread; the later occurrence of a repeated name
/// compares WHOLE values, the first occurrence's and then its own (<c>BadArity</c> when they differ,
/// a non-match in a clause family). A parameter list binds in written order: a structural parameter is
/// inspected as above, a repeated plain parameter is compared as above, a META parameter captures its
/// written call without running anything (a value is refused, <c>NotAnAlgorithm</c>), and a plain
/// parameter waits for the body; the first failure stops binding. A captured call's argument cells are
/// demanded at most once across <c>Invoke</c> and the rebuilt call. The body is a written list of
/// every name in written order, depth first, once (a collector as its <c>count</c>, which reads no
/// position): its elements run when the result is READ — for a root row, when the run's assembled
/// output is read, after every row has been evaluated (<see cref="SemanticFragment.LateEvents"/>).</para>
///
/// <para>Every decision is a named pick, so the recipe is finite and <see cref="SemanticExhaustive"/>
/// enumerates it. No program is an intended refusal: every one parses cleanly.</para>
/// </summary>
internal static class SemanticNestedWider
{
    internal static readonly ImmutableArray<string> Shapes = ["placement", "repeated", "spread", "meta-head", "meta-target"];

    /// <summary>Where a level's collector is written among its two fixed items.</summary>
    internal static readonly ImmutableArray<string> Placements = ["first", "middle", "last"];

    /// <summary>The heads a repeated name is written in.</summary>
    internal static readonly ImmutableArray<string> HeadForms = ["pattern", "parameters", "clauses"];

    /// <summary>The two positions sharing one name (the second is the later, compared occurrence).</summary>
    internal static readonly ImmutableArray<string> RepeatPairs = ["deep-head~outer-tail", "deep-tail~parent-tail", "deep-head~deep-tail"];

    internal static readonly ImmutableArray<string> SpreadForms = ["whole", "head-pair", "empty"];

    /// <summary>What a META-parameter body does with its parameter.</summary>
    internal static readonly ImmutableArray<string> MetaUses = ["count", "invoke", "unused"];

    /// <summary>The operations over a captured call of a nested-head target.</summary>
    internal static readonly ImmutableArray<string> MetaOps = ["count", "invoke", "fresh", "rebuilt"];

    /// <summary>The catch-all clause's whole result is <c>[0]</c>.</summary>
    internal const int CatchAllMarker = 0;

    /// <summary>The scalar written where a structure is expected.</summary>
    internal const int NotAStructure = 99;

    /// <summary>The value written for a META parameter: not a call, so the capture is refused.</summary>
    internal const int NotACall = 5;

    /// <summary>Items a collector receives when it receives any.</summary>
    internal const int CollectorWidth = 2;

    /// <summary>One production in one consumer context.</summary>
    internal static SemanticFragment Build(SemanticGrammar.Gen g)
    {
        SemanticFragment fragment;
        using (g.Span("production"))
            fragment = Production(g);
        using var contextSpan = g.Span("context");
        SemanticGrammar.ApplyContext(g, fragment, g.Pick("wider.context", SemanticGrammar.Contexts.Length));
        return fragment;
    }

    private static SemanticFragment Production(SemanticGrammar.Gen g) => g.Pick("wider.shape", Shapes.Length) switch
    {
        0 => PlacementShape(g),
        1 => RepeatedShape(g),
        2 => SpreadShape(g),
        3 => MetaHeadShape(g),
        _ => MetaTargetShape(g),
    };

    // ── Shapes ──────────────────────────────────────────────────────────────

    /// <summary>Collectors on a chosen subset of the levels (the third included), placed by a rotation.</summary>
    private static SemanticFragment PlacementShape(SemanticGrammar.Gen g)
    {
        var depth = Depth(g);
        var kinds = g.Pick("wider.kinds", 2);
        var mask = g.Pick("wider.collectors", 1 << depth);
        var place = mask == 0 ? 0 : g.Pick("wider.place", Placements.Length);
        var width = mask == 0 ? 0 : g.Pick("wider.width", 2) * CollectorWidth;
        var head = Head(g, depth, kinds, level => (mask & (1 << (level - 1))) == 0 ? null : (place + level - 1) % Placements.Length);
        var deepest = head.Deepest;
        var extraLevel = head.Chain().LastOrDefault(static l => !l.Collects);

        // A dropped item must leave a writable group: a list, or a sequence of two or more items.
        var deepestItems = deepest.FixedCount + (deepest.Collects ? width : 0);
        var outcomes = new List<string> { "ok" };
        if (extraLevel is not null) outcomes.Add("extra");
        if (deepest.IsList || deepestItems - 1 >= 2) outcomes.Add("missing");
        var outcome = outcomes[g.Pick("wider.outcome", outcomes.Count)];

        var f = Fragment("placement", depth);
        var data = new Data(g);
        var argument = data.Of(head, width);
        if (outcome == "extra") data.Groups[extraLevel!].Items.Add(data.Leaf());
        if (outcome == "missing") data.Groups[deepest].Items.RemoveAt(data.Groups[deepest].Items.Count - 1);
        if (outcome != "ok") f.Features.Add("wider-mutation-" + outcome);
        PatternCall(g, f, head, argument, clauses: false);
        HeadFeatures(f, head, parameters: false);
        return f;
    }

    /// <summary>One name written twice in nested positions, with equal or unequal data.</summary>
    private static SemanticFragment RepeatedShape(SemanticGrammar.Gen g)
    {
        var form = g.Pick("wider.form", HeadForms.Length);
        var depth = Depth(g);
        var kinds = g.Pick("wider.kinds", 2);
        var pair = g.Pick("wider.pair", RepeatPairs.Length);
        // The clause-family form writes fixed levels only; the wide recipe owns a family's direct
        // collector (its clause-collector refusal), and nested family collectors are pinned by
        // ClauseFamilyCollectingPatternTests (Q-47).
        var collects = form != 2 && g.Pick("wider.collect", 2) == 1;
        var equal = g.Pick("wider.equal", 2) == 0;
        var width = collects ? CollectorWidth : 0;
        var head = Head(g, depth, kinds, level => collects && level == depth ? 1 : null);
        var deepest = head.Deepest;
        var parent = head.Chain().Single(l => l.Child == deepest);
        var (firstLevel, firstIndex, repeatLevel, repeatIndex) = pair switch
        {
            0 => (deepest, deepest.BinderIndex(0), head, head.BinderIndex(0)),
            1 => (deepest, deepest.BinderIndex(1), parent, parent.BinderIndex(0)),
            _ => (deepest, deepest.BinderIndex(0), deepest, deepest.BinderIndex(1)),
        };
        repeatLevel.Slots[repeatIndex] = new Slot(SlotKind.Binder, firstLevel.Slots[firstIndex].Symbol, Repeat: true);

        var f = Fragment("repeated", depth);
        f.Features.UnionWith(["repeated-name", "wider-repeat-" + RepeatPairs[pair], "wider-form-" + HeadForms[form], equal ? "repeat-equal" : "repeat-unequal"]);
        var data = new Data(g) { Unequal = !equal };
        if (form == 1)
        {
            var arguments = data.Arguments(head, width);
            ParameterCall(g, f, head, arguments, use: null);
        }
        else
        {
            PatternCall(g, f, head, data.Of(head, width), clauses: form == 2);
        }

        HeadFeatures(f, head, parameters: form == 1);
        return f;
    }

    /// <summary>One level's data written through a spread.</summary>
    private static SemanticFragment SpreadShape(SemanticGrammar.Gen g)
    {
        var depth = Depth(g);
        var kinds = g.Pick("wider.kinds", 2);
        var placement = g.Pick("wider.collect", 1 + Placements.Length) - 1;
        var width = placement < 0 ? 0 : g.Pick("wider.width", 2) * CollectorWidth;
        var spreadAt = 1 + g.Pick("wider.spreadAt", depth);
        var head = Head(g, depth, kinds, level => placement >= 0 && level == depth ? placement : null);
        var level = head.Chain().ElementAt(spreadAt - 1);
        var items = level.FixedCount + (level.Collects ? width : 0);
        var forms = new List<int> { 0 };
        if (items >= 3) forms.Add(1);
        forms.Add(2);
        var form = forms[g.Pick("wider.spread", forms.Count)];
        var extra = form != 2 && g.Pick("wider.outcome", 2) == 1;

        var f = Fragment("spread", depth);
        f.Features.UnionWith(["spread", "spread-in-data", "spread-" + SpreadForms[form], "spread-level-" + spreadAt.ToString(CultureInfo.InvariantCulture)]);
        if (extra) f.Features.Add("wider-mutation-extra-in-spread");
        var data = new Data(g);
        var argument = data.Of(head, width);
        var group = data.Groups[level];
        switch (form)
        {
            case 0:
            {
                var all = new List<DItem>(group.Items);
                group.Items.Clear();
                group.Items.Add(new DSpread(all));
                if (extra) all.Add(data.Leaf());
                break;
            }

            case 1:
            {
                var pair = group.Items.Take(2).ToList();
                group.Items.RemoveRange(0, 2);
                group.Items.Insert(0, new DSpread(pair));
                if (extra) pair.Add(data.Leaf());
                break;
            }

            default:
                group.Items.Insert(1, new DSpread([]));
                f.Features.Add("empty-spread");
                break;
        }

        PatternCall(g, f, head, argument, clauses: false);
        HeadFeatures(f, head, parameters: false);
        return f;
    }

    /// <summary><c>F(meta m, (…), t)</c> or <c>F((…), t, meta m)</c> over <c>T(x, y) = x + y</c>.</summary>
    private static SemanticFragment MetaHeadShape(SemanticGrammar.Gen g)
    {
        var first = g.Pick("wider.metaAt", 2) == 0;
        var depth = Depth(g);
        var kinds = g.Pick("wider.kinds", 2);
        var collects = g.Pick("wider.collect", 2) == 1;
        var use = g.Pick("wider.use", MetaUses.Length);
        var outcome = g.Pick("wider.outcome", 3); // ok, a refused META argument, a scalar for the deepest structure
        var width = collects ? CollectorWidth : 0;

        var f = Fragment("meta-head", depth, family: "meta");
        f.Features.UnionWith(["meta", "meta-over-nested", "meta-at-" + (first ? "first" : "last"), "meta-use-" + MetaUses[use]]);
        var target = g.Fresh();
        var x = g.Fresh();
        var y = g.Fresh();
        f.Decls.Add(new MDecl.Func(target, [new MParam(x, false), new MParam(y, false)], new MExpr.Add(new MExpr.Ref(x), new MExpr.Ref(y))));
        var head = Head(g, depth, kinds, level => collects && level == depth ? 1 : null);
        var meta = new Slot(SlotKind.Meta, g.Fresh());
        head.Slots.Insert(first ? 0 : head.Slots.Count, meta);

        var data = new Data(g);
        DCall? captured = null;
        var arguments = new List<DItem>();
        foreach (var slot in head.Slots)
        {
            arguments.Add(slot.Kind switch
            {
                SlotKind.Meta when outcome == 1 => new DAtom(NotACall),
                SlotKind.Meta => captured = new DCall(target, [data.Leaf(), data.Leaf()]),
                SlotKind.Child => data.Of(head.Child!, width, atomAt: outcome == 2 ? head.Deepest : null),
                _ => data.Leaf(),
            });
        }

        if (outcome == 1) f.Features.Add("meta-refusal");
        if (outcome == 2) f.Features.Add("wider-mutation-scalar");
        ParameterCall(g, f, head, arguments, use is 2 ? null : (meta.Symbol, use == 1, captured));
        HeadFeatures(f, head, parameters: true);
        return f;
    }

    /// <summary><c>r = Cap(T(data))</c> over a nested head <c>T</c>, then two operations (and optionally a wrongly shaped fresh call).</summary>
    private static SemanticFragment MetaTargetShape(SemanticGrammar.Gen g)
    {
        var depth = Depth(g);
        var kinds = g.Pick("wider.kinds", 2);
        var collects = g.Pick("wider.collect", 2) == 1;
        int[] ops = [g.Pick("wider.op", MetaOps.Length), g.Pick("wider.op", MetaOps.Length)];
        var failing = g.Pick("wider.outcome", 2) == 1;
        var width = collects ? CollectorWidth : 0;

        var f = Fragment("meta-target", depth, family: "meta");
        f.Features.UnionWith(["meta", "meta-over-nested"]);
        var head = Head(g, depth, kinds, level => collects && level == depth ? Placements.Length - 1 : null);
        var target = g.Fresh();
        var body = BodySlots(head).ToList();
        f.Decls.Add(new MDecl.Family(target, [new MClause(Pattern(head), new MExpr.ListLit([.. body.Select(BodyExpr)]))]));
        var cap = g.Fresh();
        var op = g.Fresh();
        f.Decls.Add(new MDecl.Func(cap, [new MParam(op, Collecting: false, Meta: true)], new MExpr.Ref(op)));

        var data = new Data(g);
        var original = data.Of(head, width);
        var r = g.Fresh();
        f.Decls.Add(new MDecl.Value(r, [new MExpr.Call(cap, [new MExpr.Call(target, [Render(original)])])]));

        // Every operation is an element of the row's list: each runs, and its result is read
        // whole, before the next one (the row is deferred as a whole by its production).
        var reference = new Reference(f);
        var captured = new Cell(original); // the captured argument cell runs once
        Result Invocation(Cell argument)
        {
            var binding = new Binding();
            if (Match(head, argument, binding, reference) is { } error)
                throw new InvalidOperationException($"meta-target data does not match its head ({error})");
            return new Result.ListValue([.. body.Select(s => BodyValue(s, binding, reference))]);
        }

        MExpr Arguments() => new MExpr.Dot(new MExpr.Ref(r), "Arguments", null);
        var rows = new List<MExpr>();
        var values = new List<Result>();
        foreach (var kind in ops)
        {
            f.Features.Add("meta-op-" + MetaOps[kind]);
            switch (kind)
            {
                case 0:
                    rows.Add(new MExpr.Dot(Arguments(), "count", null));
                    values.Add(SemanticGrammar.Res(1));
                    break;
                case 1:
                case 3:
                    rows.Add(kind == 1
                        ? new MExpr.Dot(new MExpr.Ref(r), "Invoke", [])
                        : new MExpr.Dot(new MExpr.Ref(r), "Algorithm", [new MExpr.Spread(Arguments())]));
                    values.Add(Invocation(captured));
                    break;
                default:
                {
                    var fresh = data.Of(head, width, literal: true);
                    rows.Add(new MExpr.Dot(new MExpr.Ref(r), "Algorithm", [Render(fresh)]));
                    values.Add(Invocation(new Cell(fresh)));
                    break;
                }
            }
        }

        if (failing)
        {
            // A fresh call whose deepest structure is a scalar: refused by T's head, nothing runs.
            var wrong = data.Of(head, width, literal: true, atomAt: head.Deepest);
            rows.Add(new MExpr.Dot(new MExpr.Ref(r), "Algorithm", [Render(wrong)]));
            Fail(f, "TypeMismatch", "fresh-scalar");
        }
        else
        {
            f.Value = new Result.ListValue(values);
        }

        f.Row = new MExpr.ListLit(rows);
        f.DeferRow();
        HeadFeatures(f, head, parameters: false);
        return f;
    }

    // ── Calls and expectations ──────────────────────────────────────────────

    /// <summary>
    /// <c>F((…)) = [names]</c> (and with <paramref name="clauses"/> a second, catch-all clause
    /// <c>F(x) = [0]</c>, the first clause's body led by <c>1</c>) called with <paramref name="argument"/>.
    /// The structural pattern demands its argument and reads what its levels inspect; the body's
    /// names run when the result is read.
    /// </summary>
    private static void PatternCall(SemanticGrammar.Gen g, SemanticFragment f, Level head, DItem argument, bool clauses)
    {
        var function = g.Fresh();
        var body = BodySlots(head).ToList();
        MExpr[] lead = clauses ? [SemanticGrammar.Atom(1)] : [];
        var family = new List<MClause> { new(Pattern(head), new MExpr.ListLit([.. lead, .. body.Select(BodyExpr)])) };
        if (clauses)
        {
            family.Add(new MClause(new MPattern.Binder(g.Fresh()), new MExpr.ListLit([SemanticGrammar.Atom(CatchAllMarker)])));
            f.Features.UnionWith(["clause-family", "catch-all"]);
        }

        f.Decls.Add(new MDecl.Family(function, family));
        f.Row = new MExpr.Call(function, [Render(argument)]);
        var reference = new Reference(f);
        var binding = new Binding();
        if (Match(head, new Cell(argument), binding, reference) is { } error)
        {
            if (clauses) f.Value = new Result.ListValue([SemanticGrammar.Res(CatchAllMarker)]);
            else Fail(f, error, error switch { "TypeMismatch" => "type", "BadArity" => "repeat-differs", _ => "arity" });
            if (clauses) f.Features.Add("wider-outcome-catch-all");
            return;
        }

        Result[] first = clauses ? [SemanticGrammar.Res(1)] : [];
        reference.ReadResult();
        f.Value = new Result.ListValue([.. first, .. body.Select(s => BodyValue(s, binding, reference))]);
    }

    /// <summary>
    /// A parameter-list head <c>F(p1, …)</c> called with one argument per parameter, bound in written
    /// order (<see cref="SemanticNestedWider"/>); on success the body — the META use first, when
    /// <paramref name="use"/> names one — is read left to right when the result is read, a waiting
    /// plain parameter's leaves at its place.
    /// </summary>
    private static void ParameterCall(
        SemanticGrammar.Gen g, SemanticFragment f, Level head, IReadOnlyList<DItem> arguments, (Sym Meta, bool Invoke, DCall? Captured)? use)
    {
        var function = g.Fresh();
        var body = BodySlots(head).ToList();
        var lead = new List<MExpr>();
        if (use is { } u)
        {
            lead.Add(u.Invoke
                ? new MExpr.Dot(new MExpr.Ref(u.Meta), "Invoke", [])
                : new MExpr.Dot(new MExpr.Dot(new MExpr.Ref(u.Meta), "Arguments", null), "count", null));
        }

        f.Decls.Add(new MDecl.Family(function, [new MClause(ParameterHead(head), new MExpr.ListLit([.. lead, .. body.Select(BodyExpr)]))]));
        f.Row = new MExpr.Call(function, [.. arguments.Select(Render)]);

        var reference = new Reference(f);
        var binding = new Binding();
        for (var i = 0; i < head.Slots.Count; i++)
        {
            var slot = head.Slots[i];
            var argument = arguments[i];
            string? error = null;
            switch (slot.Kind)
            {
                case SlotKind.Meta:
                    if (argument is not DCall) error = "NotAnAlgorithm"; // the capture is inert; a value is refused
                    break;
                case SlotKind.Child:
                    error = Match(head.Child!, new Cell(argument), binding, reference);
                    break;
                case SlotKind.Binder when slot.Repeat:
                    error = Bind(binding, slot, new Cell(argument), reference); // a repeated name compares whole values
                    break;
                case SlotKind.Binder:
                    binding.Bound[slot.Symbol] = new Cell(argument); // a plain parameter waits for the body
                    break;
                default:
                    throw new InvalidOperationException("no collecting parameter at level 1");
            }

            if (error is not null)
            {
                Fail(f, error, error switch { "NotAnAlgorithm" => "meta-refused", "TypeMismatch" => "type", "BadArity" => "repeat-differs", _ => "arity" });
                return;
            }
        }

        reference.ReadResult();
        var values = new List<Result>();
        if (use is { } used)
        {
            var captured = used.Captured ?? throw new InvalidOperationException("a used META parameter captured a call");
            if (used.Invoke)
            {
                foreach (var argument in captured.Args) reference.Eval(argument); // x + y: x, then y
                values.Add(SemanticGrammar.Res(captured.Args.Sum(static a => ((DLeaf)a).Value)));
            }
            else
            {
                values.Add(SemanticGrammar.Res(captured.Args.Count));
            }
        }

        foreach (var slot in body)
            values.Add(BodyValue(slot, binding, reference));

        f.Value = new Result.ListValue(values);
    }

    private static void Fail(SemanticFragment f, string category, string what)
    {
        f.FailureCategory = category;
        f.Features.UnionWith(["failure", "wider-outcome-" + what]);
    }

    private static int Depth(SemanticGrammar.Gen g) => 2 + g.Pick("wider.depth", 2);

    private static SemanticFragment Fragment(string shape, int depth, string family = "collect")
    {
        var f = new SemanticFragment(family);
        f.Features.UnionWith(["nested-pattern", "nested-wider", "wider-" + shape]);
        if (depth == 3) f.Features.Add("three-level");
        return f;
    }

    private static void HeadFeatures(SemanticFragment f, Level head, bool parameters)
    {
        if (parameters) f.Features.Add("parameter-list");
        foreach (var level in head.Chain())
        {
            if (!(parameters && level.Number == 1)) f.Features.Add(level.IsList ? "list-pattern" : "sequence-pattern");
            var rest = level.Slots.FindIndex(static s => s.Kind == SlotKind.Rest);
            if (rest < 0) continue;
            var at = rest == 0 ? "first" : rest == level.Slots.Count - 1 ? "last" : "middle";
            var number = level.Number.ToString(CultureInfo.InvariantCulture);
            f.Features.UnionWith(["collect", "collector-level-" + number, "collector-" + at, "collector-level-" + number + "-" + at]);
        }
    }

    // ── Heads ───────────────────────────────────────────────────────────────

    private enum SlotKind
    {
        Child,
        Binder,
        Rest,
        Meta,
    }

    /// <summary>One written item of a level: the nested level, a name (or a repeated one), a collector, a META parameter.</summary>
    private sealed record Slot(SlotKind Kind, Sym Symbol, bool Repeat = false);

    /// <summary>One level of a head (level 1 is the outermost: a pattern group, or the parameter list).</summary>
    private sealed class Level(int number, bool isList)
    {
        public int Number { get; } = number;

        public bool IsList { get; } = isList;

        public Level? Child { get; set; }

        public List<Slot> Slots { get; } = [];

        public int FixedCount => Slots.Count(static s => s.Kind is SlotKind.Child or SlotKind.Binder);

        public bool Collects => Slots.Any(static s => s.Kind == SlotKind.Rest);

        public Level Deepest => Child?.Deepest ?? this;

        public IEnumerable<Level> Chain()
        {
            for (var level = this; level is not null; level = level.Child) yield return level;
        }

        /// <summary>The slot index of the <paramref name="ordinal"/>-th name of this level.</summary>
        public int BinderIndex(int ordinal)
            => Slots.Select(static (s, i) => (s, i)).Where(static p => p.s.Kind == SlotKind.Binder).ElementAt(ordinal).i;
    }

    /// <summary>
    /// Levels 1..<paramref name="depth"/>: each holds its child (the deepest: a name) and a tail name,
    /// and a collector at the index <paramref name="placement"/> gives (0 first, 1 middle, 2 last).
    /// Level kinds alternate, starting with a list when <paramref name="kinds"/> is 1.
    /// </summary>
    private static Level Head(SemanticGrammar.Gen g, int depth, int kinds, Func<int, int?> placement)
    {
        Level Make(int number)
        {
            var level = new Level(number, (kinds + number) % 2 == 0);
            if (number < depth)
            {
                level.Child = Make(number + 1);
                level.Slots.Add(new Slot(SlotKind.Child, default));
            }
            else
            {
                level.Slots.Add(new Slot(SlotKind.Binder, g.Fresh()));
            }

            level.Slots.Add(new Slot(SlotKind.Binder, g.Fresh()));
            if (placement(number) is { } at) level.Slots.Insert(at, new Slot(SlotKind.Rest, g.Fresh()));
            return level;
        }

        return Make(1);
    }

    private static MPattern Pattern(Level level) => new MPattern.Structure(level.IsList, [.. level.Slots.Select(s => SlotPattern(level, s))]);

    private static MPattern ParameterHead(Level top) => new MPattern.ParameterList([.. top.Slots.Select(s => SlotPattern(top, s))]);

    private static MPattern SlotPattern(Level level, Slot slot) => slot.Kind switch
    {
        SlotKind.Child => Pattern(level.Child!),
        SlotKind.Binder => slot.Repeat ? new MPattern.Repeat(slot.Symbol) : new MPattern.Binder(slot.Symbol),
        SlotKind.Rest => new MPattern.Collecting(slot.Symbol),
        _ => new MPattern.Meta(slot.Symbol),
    };

    /// <summary>Every name once, in written order, depth first; a collector as its count (a META parameter is not listed).</summary>
    private static IEnumerable<Slot> BodySlots(Level level) => level.Slots.SelectMany(slot => slot.Kind switch
    {
        SlotKind.Child => BodySlots(level.Child!),
        SlotKind.Meta => [],
        SlotKind.Binder when slot.Repeat => [],
        _ => (IEnumerable<Slot>)[slot],
    });

    private static MExpr BodyExpr(Slot slot)
        => slot.Kind == SlotKind.Rest ? new MExpr.Prim("count", [new MExpr.Ref(slot.Symbol)]) : new MExpr.Ref(slot.Symbol);

    private static Result BodyValue(Slot slot, Binding binding, Reference reference)
        => slot.Kind == SlotKind.Rest
            ? SemanticGrammar.Res(binding.Collected[slot.Symbol]) // `count` reads no position
            : ToResult(reference.Whole(binding.Bound[slot.Symbol]));

    // ── Data ────────────────────────────────────────────────────────────────

    /// <summary>A written data item.</summary>
    private abstract record DItem;

    /// <summary>A host effect <c>trace(v)</c> / <c>wait(v)</c>.</summary>
    private sealed record DLeaf(int Value, bool Wait) : DItem;

    /// <summary>A literal number.</summary>
    private sealed record DAtom(int Value) : DItem;

    /// <summary>A written group <c>(…)</c> or list <c>[…]</c>.</summary>
    private sealed record DGroup(bool IsList, List<DItem> Items) : DItem;

    /// <summary>A spread <c>(items)*</c> inside a group (never exactly one item).</summary>
    private sealed record DSpread(List<DItem> Items) : DItem;

    /// <summary>A written invocation <c>T(args)</c> (a META parameter's argument).</summary>
    private sealed record DCall(Sym Callee, List<DItem> Args) : DItem;

    /// <summary>
    /// Writes data for a head: one item per written slot, in written order (a collector's
    /// <c>width</c> items), effects alternating trace and wait. A repeated name's leaf repeats its
    /// first occurrence's value, or (<see cref="Unequal"/>) the next digit after it.
    /// </summary>
    private sealed class Data(SemanticGrammar.Gen g)
    {
        private readonly Dictionary<Sym, int> _written = [];
        private int _leaves;

        public bool Unequal { get; init; }

        /// <summary>Each level's written group (the last one written, for a head written twice).</summary>
        public Dictionary<Level, DGroup> Groups { get; } = [];

        public DLeaf Leaf(int? value = null) => new(value ?? g.Digit(), _leaves++ % 2 == 1);

        public DItem Of(Level level, int width, bool literal = false, Level? atomAt = null)
        {
            if (level == atomAt) return new DAtom(NotAStructure);
            var items = new List<DItem>();
            foreach (var slot in level.Slots)
                items.AddRange(Items(level, slot, width, literal, atomAt));
            var group = new DGroup(level.IsList, items);
            Groups[level] = group;
            return group;
        }

        /// <summary>Level 1 of a parameter-list head: one argument per parameter.</summary>
        public List<DItem> Arguments(Level top, int width)
            => [.. top.Slots.SelectMany(slot => Items(top, slot, width, false, null))];

        private IEnumerable<DItem> Items(Level level, Slot slot, int width, bool literal, Level? atomAt)
        {
            switch (slot.Kind)
            {
                case SlotKind.Child:
                    yield return Of(level.Child!, width, literal, atomAt);
                    break;
                case SlotKind.Binder when literal:
                    yield return new DAtom(g.Digit());
                    break;
                case SlotKind.Binder when slot.Repeat:
                    var first = _written[slot.Symbol];
                    yield return Leaf(Unequal ? first % 9 + 1 : first);
                    break;
                case SlotKind.Binder:
                    var leaf = Leaf();
                    _written[slot.Symbol] = leaf.Value;
                    yield return leaf;
                    break;
                case SlotKind.Rest:
                    for (var i = 0; i < width; i++) yield return literal ? new DAtom(g.Digit()) : Leaf();
                    break;
                default:
                    throw new InvalidOperationException("a META parameter's argument is written by its shape");
            }
        }
    }

    private static MExpr Render(DItem item) => item switch
    {
        DLeaf leaf => SemanticGrammar.Effect(leaf.Wait, leaf.Value),
        DAtom atom => SemanticGrammar.Atom(atom.Value),
        DGroup { IsList: true } list => new MExpr.ListLit([.. list.Items.Select(Render)]),
        DGroup group => new MExpr.Group([.. group.Items.Select(Render)]),
        DSpread spread => new MExpr.Spread(new MExpr.Group([.. spread.Items.Select(Render)])),
        DCall call => new MExpr.Call(call.Callee, [.. call.Args.Select(Render)]),
        _ => throw new InvalidOperationException("unknown data item"),
    };

    // ── The reference binder ────────────────────────────────────────────────

    /// <summary>A value: a number, or a sequence/list of positions (a <see cref="V"/>, or an unread <see cref="Cell"/>).</summary>
    private abstract record V;

    private sealed record VScalar(int Value) : V;

    private sealed record VSeq(bool IsList, ImmutableArray<object> Items) : V;

    /// <summary>
    /// A deferred position — a written list's ordinary element, or a supplied argument — whose
    /// written data runs when the position is first read, once.
    /// </summary>
    private sealed class Cell(DItem item)
    {
        public DItem Item { get; } = item;

        public V? Value { get; set; }
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
        /// A written item's value. A sequence evaluates its items in order; a list defers its
        /// ordinary elements and evaluates only its spread operands; spread items are spliced in
        /// place, and a sequence of one item is that item.
        /// </summary>
        public V Eval(DItem item)
        {
            switch (item)
            {
                case DLeaf leaf:
                    _events.Add((leaf.Wait ? "wait:" : "trace:") + leaf.Value.ToString(CultureInfo.InvariantCulture));
                    if (leaf.Wait) f.Features.Add("async");
                    return new VScalar(leaf.Value);
                case DAtom atom:
                    return new VScalar(atom.Value);
                case DGroup group:
                {
                    var items = ImmutableArray.CreateBuilder<object>();
                    foreach (var written in group.Items)
                    {
                        if (written is DSpread spread)
                            items.AddRange(Opened(Eval(new DGroup(false, spread.Items)), spread.Items.Count));
                        else if (group.IsList && written is not DAtom)
                            items.Add(new Cell(written));
                        else
                            items.Add(Eval(written));
                    }

                    var sequence = new VSeq(group.IsList, items.ToImmutable());
                    return !sequence.IsList && sequence.Items.Length == 1 ? Force(sequence.Items[0]) : sequence;
                }

                default:
                    throw new InvalidOperationException("not a data value");
            }
        }

        // The items a spread splices: its operand's (a written group of zero, two or more items).
        private static IEnumerable<object> Opened(V operand, int written)
            => written == 1 ? throw new InvalidOperationException("a generated spread never has exactly one item")
                : ((VSeq)operand).Items;

        /// <summary>A position's value: an unread cell runs now.</summary>
        public V Force(object position) => position is Cell cell ? cell.Value ??= Eval(cell.Item) : (V)position;

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
    }

    private sealed class Binding
    {
        /// <summary>The position each name is bound to, unread.</summary>
        public Dictionary<Sym, object> Bound { get; } = [];

        public Dictionary<Sym, int> Collected { get; } = [];
    }

    /// <summary>
    /// One level against a position: its kind (the position is read), its count (exact, or at least
    /// the fixed items when it collects), then its items in written order, depth first — the collector
    /// taking the items between the fixed items before and after it, unread. Returns the error
    /// category of the first failure.
    /// </summary>
    private static string? Match(Level level, object position, Binding binding, Reference reference)
    {
        var value = reference.Force(position);
        if (value is not VSeq sequence || sequence.IsList != level.IsList) return "TypeMismatch";
        var count = sequence.Items.Length;
        var fixedCount = level.FixedCount;
        if (level.Collects ? count < fixedCount : count != fixedCount) return "ArityMismatch";
        var at = 0;
        foreach (var slot in level.Slots)
        {
            switch (slot.Kind)
            {
                case SlotKind.Rest:
                    binding.Collected[slot.Symbol] = count - fixedCount;
                    at += count - fixedCount;
                    break;
                case SlotKind.Child:
                    if (Match(level.Child!, sequence.Items[at++], binding, reference) is { } error) return error;
                    break;
                default:
                    if (Bind(binding, slot, sequence.Items[at++], reference) is { } failure) return failure;
                    break;
            }
        }

        return null;
    }

    /// <summary>
    /// A name binds its position unread; its repeated occurrence compares WHOLE values — the first
    /// occurrence's, then its own (a difference is <c>BadArity</c>).
    /// </summary>
    private static string? Bind(Binding binding, Slot slot, object position, Reference reference)
    {
        if (!slot.Repeat)
        {
            binding.Bound[slot.Symbol] = position;
            return null;
        }

        return reference.Whole(binding.Bound[slot.Symbol]) is VScalar first && reference.Whole(position) is VScalar later
            ? first.Value == later.Value ? null : "BadArity"
            : throw new InvalidOperationException("a repeated name compares numbers only");
    }

    private static Result ToResult(V value) => value is VScalar scalar
        ? SemanticGrammar.Res(scalar.Value)
        : throw new InvalidOperationException("a generated name binds a number");
}
