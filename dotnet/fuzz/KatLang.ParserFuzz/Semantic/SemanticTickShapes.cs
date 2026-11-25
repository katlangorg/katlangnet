using System.Collections.Immutable;
using KatLang;
using KatLang.Tests.StructuralFuzz;

namespace KatLang.ParserFuzz;

/// <summary>
/// The named TICK block (SEM-2C): productions the 2026-11-20 C#/Lean differential bug hunt (§ 7) found
/// uncovered, each observed through the run's <c>tick()</c> counter — evaluation order inside callbacks,
/// loop rows and selectors; member reads through transparent references and forwarding carriers; and two
/// nested parameterized owners whose local properties must stay per activation.
///
/// <para><b>Why <c>tick()</c>.</b> <c>tick()</c> is an ordinary prelude builtin that Lean models
/// (<c>EvalState.tickCounter</c>): each run owns one counter starting at zero, and every executed
/// <c>tick()</c> returns the next integer. Its values are part of the RESULT, so the identity-prelude
/// member of <c>SemanticGeneratedLeanArtifactTests</c> carries the evaluation order to Lean — unlike the
/// host operations <c>trace</c>/<c>wait</c>, whose EVENTS remain C# evidence. Successful shapes therefore
/// emit no host event (their order is pinned by the value on both sides); the fault shapes wrap ticks in
/// <c>trace(…)</c>, so the C# event log pins what ran before the fault while Lean sees the error kind.</para>
///
/// <para><b>Controls.</b> Every successful shape ends its row with a trailing <c>tick()</c>: its value is one more
/// than the number of ticks the shape executed (the evaluation-count control). Every shape also constructs
/// the expectation of ONE NAMED REJECTED READING — a plausible wrong rule (eager initial state, selectors
/// before the receiver, an entry per reference, …) — which must differ from the intended expectation and
/// which the runner must reject (<c>SemanticTickShapeTests</c>). Shapes named as a variant pair differ in
/// one construct, and each one's rejected reading is its partner's rule where that is the contrast.</para>
///
/// <para><b>Compatibility.</b> The block is appended after the path block (<c>sys/tick/&lt;group&gt;/&lt;shape&gt;</c>),
/// its shapes draw no chooser decision of their own (a partner fragment, when present, uses the
/// systematic chooser of the case's block index), and no earlier production, recipe or id changes.
/// Expectations follow the cited rules, never a run of the implementation. A fault shape takes no
/// partner: a partner's <c>trace(d)</c> events would share their small values with the traced ticks.</para>
/// </summary>
internal static class SemanticTickShapes
{
    /// <summary>The local-id prefix of the block.</summary>
    internal const string LocalPrefix = "sys/tick/";

    /// <summary>The family every tick fragment reports (no family floor: the block is pinned by its id list).</summary>
    internal const string Family = "tick";

    /// <summary>
    /// One named shape: its group and name (the id is <c>sys/tick/&lt;group&gt;/&lt;name&gt;</c>), the rule its
    /// expectation follows, the rejected reading its control constructs, the production (<c>alternative</c>
    /// builds the rejected reading's expectation over the SAME program), an optional context
    /// (<see cref="SemanticGrammar.Contexts"/> index), an optional successful tick-free partner fragment, and
    /// the shape it forms a variant pair with.
    /// </summary>
    internal sealed record Shape(
        string Group,
        string Name,
        string Rule,
        string RejectedReading,
        Func<SemanticGrammar.Gen, bool, SemanticFragment> Build,
        int Context = 0,
        string? Partner = null,
        bool PartnerFirst = false,
        string? PairedWith = null)
    {
        public string LocalId => LocalPrefix + Group + "/" + Name;
    }

    private const int ListContext = 1;
    private const int IfTrue = 2;
    private const int IfFalse = 3;
    private const int Property = 4;
    private const int PropertyDouble = 5;
    private const int Wrapper = 6;
    private const int BraceContext = 7;

    /// <summary>The block, in corpus order. Appending keeps every earlier block index (and partner) unchanged.</summary>
    internal static readonly ImmutableArray<Shape> Shapes =
    [
        // ── Callbacks (Q-25 operational order, call-by-need) ────────────────────────────────────────
        new("callback", "map",
            "map runs nothing by itself: reading a mapped position reads its source position, then runs its transform, position by position",
            "map demands its whole collection before any transform, then runs one transform per element",
            Map, Context: PropertyDouble),
        new("callback", "filter",
            "filter reads its predicate's VALUE once per element, from the first element to the last; kept elements keep their order",
            "the predicate runs from the last element to the first",
            Filter, Context: IfFalse),
        new("callback", "reduce",
            "reduce demands its collection, then only its last step: each step's accumulator is the deferred previous step, run at its accumulator read, back to the initial value (the nested-call unfolding)",
            "reduce demands its initial value once, then runs each step to its ordinary call result, left to right",
            Reduce, Context: Wrapper),
        new("callback", "map-fault",
            "a failing transform ends the map and the run: no later transform or row element runs",
            "the map runs every transform before reporting the first failure",
            MapFault),

        // ── Loop rows (META-S3-3 initial state, LOOP-06 condition first) ────────────────────────────
        new("loop", "repeat-rows",
            "repeat forms the rows left to right; round 1 binds the captured call's original cells, each running at its first use",
            "the captured call's arguments run before the first round",
            (g, alternative) => RepeatRows(g, alternative, crossed: false), PairedWith: "repeat-rows-crossed"),
        new("loop", "repeat-rows-crossed",
            "the first round is the same whichever row reads which cell: a cell runs at its first use, in row order",
            "the captured call's arguments run before the first round",
            (g, alternative) => RepeatRows(g, alternative, crossed: true), PairedWith: "repeat-rows"),
        new("loop", "while-flag-first",
            "a while round reads its continuation flag first and forms the transition rows only after a true flag",
            "rows are formed left to right and the flag is read last (the retired step-first order)",
            WhileFlagFirst, Context: ListContext),
        new("loop", "while-dead-transition",
            "a false first flag returns the initial state without forming the transition row",
            "the round forms its transition row before reading the flag",
            WhileDeadTransition, Partner: "meta", PartnerFirst: true),
        new("loop", "while-fault",
            "a flag that fails ends the loop before its round's transition row; earlier rounds' rows ran",
            "rows are formed left to right and the flag is read last, so the old program succeeds",
            WhileFault),

        // ── Selectors (variadic postfix selection (E), NEED-07) ─────────────────────────────────────
        new("select", "receiver-first",
            "selection over a written list reads only the selected positions: each selector is demanded, then its position read, left to right",
            "the receiver's elements all run before any selector is demanded",
            ReceiverFirst, Partner: "cache", PartnerFirst: true),
        new("select", "spread-formation",
            "a spread selector runs during supply formation, before any ordinary selector is demanded",
            "selectors are formed and demanded strictly in written order",
            SpreadFormation, Context: BraceContext),
        new("select", "retained",
            "selection over a retained collector demands only the selected cells; a repeated position reuses its cell",
            "the collector's elements run in order when the selection reads it",
            (g, alternative) => RetainedSelection(g, alternative, retained: true), PairedWith: "eager-result"),
        new("select", "eager-result",
            "a call result is eager: selection after the call sees every argument demanded in order",
            "selection over a call result demands only the selected argument",
            (g, alternative) => RetainedSelection(g, alternative, retained: false), PairedWith: "retained"),
        new("select", "reject",
            "an out-of-range selector stops the selection: no later ordinary selector is demanded",
            "every selector is demanded before any is validated",
            RejectingSelector),

        // ── Member reads (M4★: transparent references and forwarding carriers) ─────────────────────
        new("member", "transparent",
            "a transparent reference's member IS its target's member: one declaration, one cache entry",
            "the transparent reference owns its own member entry",
            TransparentMember, PairedWith: "carrier"),
        new("member", "carrier",
            "a forwarding carrier keeps its own members: its member read never reaches the target's member",
            "a carrier's member read reaches its target's member",
            CarrierMember, PairedWith: "transparent"),
        new("member", "transparent-chain",
            "a chain of transparent references reads the target's member through every link: one entry",
            "every reference of the chain owns its own member entry",
            TransparentChain, Partner: "select"),
        new("member", "passed",
            "a passed transparent reference is its target, while a passed carrier keeps its own members",
            "a passed carrier transports its target, like a transparent reference",
            PassedMember, Context: IfTrue),

        // ── Two nested parameterized owners (activation independence) ──────────────────────────────
        new("owners", "inner-local",
            "a local property of the INNER owner is evaluated once per inner activation",
            "the inner property is cached per outer activation",
            (g, alternative) => Owners(g, alternative, innerOwned: true, sameArguments: false), PairedWith: "outer-local"),
        new("owners", "outer-local",
            "a local property of the OUTER owner is evaluated once per outer activation and shared by its inner calls",
            "the outer property is evaluated per inner activation",
            (g, alternative) => Owners(g, alternative, innerOwned: false, sameArguments: false), PairedWith: "inner-local"),
        new("owners", "inner-local-same-args",
            "activations are per call, never per argument value: equal arguments get fresh inner properties",
            "inner calls with equal arguments in the same outer activation share their property state",
            (g, alternative) => Owners(g, alternative, innerOwned: true, sameArguments: true), PairedWith: "outer-local-same-args"),
        new("owners", "outer-local-same-args",
            "activations are per call, never per argument value: equal arguments get a fresh outer property",
            "activations with equal arguments share their property state",
            (g, alternative) => Owners(g, alternative, innerOwned: false, sameArguments: true), PairedWith: "inner-local-same-args"),
        new("owners", "chain",
            "each owner's local property lives for that owner's activation: the outer one is shared by the inner calls, the inner one is not",
            "the inner property is shared by the inner calls of one outer activation",
            OwnerChain, Context: Property),
    ];

    /// <summary>Builds one shape's fragment inside a <c>production</c> span (reduction metadata only).</summary>
    internal static SemanticFragment Build(Shape shape, SemanticGrammar.Gen g, bool alternative)
    {
        using var span = g.Span("production");
        var fragment = shape.Build(g, alternative);
        SemanticGrammar.DeferListRow(fragment);
        return fragment;
    }

    internal static bool IsTickBlock(string localId) => localId.StartsWith(LocalPrefix, StringComparison.Ordinal);

    // ── Callbacks ───────────────────────────────────────────────────────────

    /// <summary><c>L = [tick(), tick()]</c>, <c>F(x) = x * 10 + tick()</c>, row <c>[map(L, F), tick()]</c>.</summary>
    private static SemanticFragment Map(SemanticGrammar.Gen g, bool alternative)
    {
        var f = Fragment("callback", "map");
        var l = g.Fresh();
        var fn = g.Fresh();
        var x = g.Fresh();
        f.Decls.Add(new MDecl.Value(l, [new MExpr.ListLit([Tick(), Tick()])]));
        f.Decls.Add(new MDecl.Func(fn, [new MParam(x, false)], new MExpr.Add(Times(new MExpr.Ref(x), 10), Tick())));
        f.Row = new MExpr.ListLit([new MExpr.Prim("map", [new MExpr.Ref(l), new MExpr.Ref(fn)]), Tick()]);

        // The written list L defers its elements and `map` its transforms (lazy collections,
        // issue #204): each mapped position is read when the row's list is — its source element
        // first, then its transform. The rejected reading is the former eager map.
        var clock = new TickClock();
        var mapped = new List<int>();
        if (!alternative)
        {
            for (var i = 0; i < 2; i++)
            {
                var element = clock.Next();
                mapped.Add(element * 10 + clock.Next());
            }
        }
        else
        {
            int[] elements = [clock.Next(), clock.Next()];
            foreach (var element in elements) mapped.Add(element * 10 + clock.Next());
        }

        f.Value = new Result.ListValue([Ints(mapped), Res(clock.Next())]);
        return f;
    }

    /// <summary><c>L = [2, 5, 1]</c>, <c>P(x) = x &gt; tick()</c>, row <c>[filter(L, P), tick()]</c>.</summary>
    private static SemanticFragment Filter(SemanticGrammar.Gen g, bool alternative)
    {
        var f = Fragment("callback", "filter");
        int[] items = [2, 5, 1];
        var l = g.Fresh();
        var p = g.Fresh();
        var x = g.Fresh();
        f.Decls.Add(new MDecl.Value(l, [new MExpr.ListLit([.. items.Select(v => (MExpr)Atom(v))])]));
        f.Decls.Add(new MDecl.Func(p, [new MParam(x, false)], new MExpr.Binary(">", new MExpr.Ref(x), Tick())));
        f.Row = new MExpr.ListLit([new MExpr.Prim("filter", [new MExpr.Ref(l), new MExpr.Ref(p)]), Tick()]);

        var clock = new TickClock();
        var keep = new bool[items.Length];
        var order = alternative ? Enumerable.Range(0, items.Length).Reverse() : Enumerable.Range(0, items.Length);
        foreach (var i in order) keep[i] = items[i] > clock.Next();
        f.Value = new Result.ListValue([Ints(items.Where((_, i) => keep[i])), Res(clock.Next())]);
        return f;
    }

    /// <summary>
    /// <c>L = [tick(), tick()]</c>, <c>R(x, acc) = tick() * x + acc</c>, row <c>[reduce(L, R, tick()), tick()]</c>. The
    /// collection is demanded whole first; then the fold demands only its LAST step, whose accumulator read runs the
    /// step before it, back to the initial value (lazy <c>reduce</c> accumulators, issue #203: Lean
    /// <c>EvalBody.evalReduceCounted</c>). The rejected reading is the former eager loop: the initial value, then
    /// every step from the first element to the last.
    /// </summary>
    private static SemanticFragment Reduce(SemanticGrammar.Gen g, bool alternative)
    {
        var f = Fragment("callback", "reduce");
        var l = g.Fresh();
        var r = g.Fresh();
        var x = g.Fresh();
        var acc = g.Fresh();
        f.Decls.Add(new MDecl.Value(l, [new MExpr.ListLit([Tick(), Tick()])]));
        f.Decls.Add(new MDecl.Func(r, [new MParam(x, false), new MParam(acc, false)],
            new MExpr.Add(new MExpr.Binary("*", Tick(), new MExpr.Ref(x)), new MExpr.Ref(acc))));
        f.Row = new MExpr.ListLit([new MExpr.Prim("reduce", [new MExpr.Ref(l), new MExpr.Ref(r), Tick()]), Tick()]);

        var clock = new TickClock();
        int[] items = [clock.Next(), clock.Next()];
        int folded;
        if (!alternative)
        {
            // R(x_n, R(x_{n-1}, … R(x_1, initial))): the outer step runs first, each inner one at its accumulator read.
            folded = Nested(items.Length - 1);

            int Nested(int k)
            {
                var head = clock.Next() * items[k];
                return head + (k == 0 ? clock.Next() : Nested(k - 1));
            }
        }
        else
        {
            folded = clock.Next();
            foreach (var item in items) folded = clock.Next() * item + folded;
        }

        f.Value = new Result.ListValue([Res(folded), Res(clock.Next())]);
        return f;
    }

    /// <summary><c>L = [1, 0, 2]</c>, <c>F(x) = trace(tick()) / x</c>, row <c>[map(L, F), trace(tick())]</c>: a division by zero at the second element.</summary>
    private static SemanticFragment MapFault(SemanticGrammar.Gen g, bool alternative)
    {
        var f = Fragment("callback", "map");
        int[] items = [1, 0, 2];
        var l = g.Fresh();
        var fn = g.Fresh();
        var x = g.Fresh();
        f.Decls.Add(new MDecl.Value(l, [new MExpr.ListLit([.. items.Select(v => (MExpr)Atom(v))])]));
        f.Decls.Add(new MDecl.Func(fn, [new MParam(x, false)], new MExpr.Binary("/", Traced(Tick()), new MExpr.Ref(x))));
        f.Row = new MExpr.ListLit([new MExpr.Prim("map", [new MExpr.Ref(l), new MExpr.Ref(fn)]), Traced(Tick())]);

        var clock = new TickClock();
        foreach (var item in items)
        {
            f.Events.Add(TraceEvent(clock.Next()));
            if (item == 0 && !alternative) break;
        }

        f.FailureCategory = "DivByZero";
        f.Paths |= SemanticPath.FirstFailureStops;
        f.Features.Add("failure");
        return f;
    }

    // ── Loop rows ───────────────────────────────────────────────────────────

    /// <summary>
    /// <c>Two(a, b) = { a * 10 + tick() ⏎ b * 10 + tick() }</c> (or the rows crossed: <c>b</c> first),
    /// row <c>[Two(tick(), tick()).repeat(1), tick()]</c>: ONE round over the captured call's original cells. Under
    /// call-by-need both spellings observe the same state, because each cell runs at its first use in row
    /// order; under the rejected eager reading they would differ.
    /// </summary>
    private static SemanticFragment RepeatRows(SemanticGrammar.Gen g, bool alternative, bool crossed)
    {
        var f = LoopFragment();
        f.Features.Add("repeat");
        f.Features.Add("lazy-initial-state");
        var two = g.Fresh();
        var a = g.Fresh();
        var b = g.Fresh();
        MExpr Row(Sym state) => new MExpr.Add(Times(new MExpr.Ref(state), 10), Tick());
        f.Decls.Add(new MDecl.Func(two, [new MParam(a, false), new MParam(b, false)],
            new MExpr.Brace(new MScope([], crossed ? [Row(b), Row(a)] : [Row(a), Row(b)]))));
        f.Row = new MExpr.ListLit([new MExpr.Dot(new MExpr.Call(two, [Tick(), Tick()]), "repeat", [Atom(1)]), Tick()]);

        var clock = new TickClock();
        var first = new LazyTick(clock);
        var second = new LazyTick(clock);
        if (alternative)
        {
            first.Demand();
            second.Demand();
        }

        // The one round over the original cells, each demanded at its first use, rows left to right.
        int s0, s1;
        if (!crossed)
        {
            s0 = first.Demand() * 10 + clock.Next();
            s1 = second.Demand() * 10 + clock.Next();
        }
        else
        {
            s0 = second.Demand() * 10 + clock.Next();
            s1 = first.Demand() * 10 + clock.Next();
        }

        f.Value = new Result.ListValue([new Result.SequenceValue([Res(s0), Res(s1)]), Res(clock.Next())]);
        f.Paths |= SemanticPath.GenericInsideOptimizedLoop;
        return f;
    }

    /// <summary><c>Step(x) = { x + tick() ⏎ tick() &lt; 3 }</c>, row <c>[Step(0).while, tick()]</c>.</summary>
    private static SemanticFragment WhileFlagFirst(SemanticGrammar.Gen g, bool alternative)
    {
        var f = LoopFragment();
        f.Features.UnionWith(["while", "condition-first"]);
        var step = g.Fresh();
        var x = g.Fresh();
        f.Decls.Add(new MDecl.Func(step, [new MParam(x, false)], new MExpr.Brace(new MScope([],
            [new MExpr.Add(new MExpr.Ref(x), Tick()), new MExpr.Binary("<", Tick(), Atom(3))]))));
        f.Row = new MExpr.ListLit([new MExpr.Dot(new MExpr.Call(step, [Atom(0)]), "while", null), Tick()]);

        var clock = new TickClock();
        var state = 0;
        while (true)
        {
            if (!alternative)
            {
                if (!(clock.Next() < 3)) break;
                state += clock.Next();
            }
            else
            {
                var next = state + clock.Next();
                if (!(clock.Next() < 3)) break;
                state = next;
            }
        }

        f.Value = new Result.ListValue([Res(state), Res(clock.Next())]);
        f.Paths |= SemanticPath.GenericInsideOptimizedLoop;
        return f;
    }

    /// <summary><c>Step(x) = { tick() * 100 ⏎ x &lt; 0 }</c>, row <c>[Step(0).while, tick()]</c>: zero accepted transitions.</summary>
    private static SemanticFragment WhileDeadTransition(SemanticGrammar.Gen g, bool alternative)
    {
        var f = LoopFragment();
        f.Features.UnionWith(["while", "condition-first", "zero-iterations"]);
        var step = g.Fresh();
        var x = g.Fresh();
        f.Decls.Add(new MDecl.Func(step, [new MParam(x, false)], new MExpr.Brace(new MScope([],
            [Times(Tick(), 100), new MExpr.Binary("<", new MExpr.Ref(x), Atom(0))]))));
        f.Row = new MExpr.ListLit([new MExpr.Dot(new MExpr.Call(step, [Atom(0)]), "while", null), Tick()]);

        var clock = new TickClock();
        if (alternative) _ = clock.Next();
        f.Value = new Result.ListValue([Res(0), Res(clock.Next())]);
        f.Paths |= SemanticPath.OptimizedLoop;
        return f;
    }

    /// <summary>
    /// <c>Step(x) = { x + trace(tick()) ⏎ 2 / (3 - trace(tick())) &gt; 0 }</c>, row <c>Step(0).while</c>: the
    /// second round's flag divides by zero. Every other quotient is EXACT: Lean's core numbers are integers and its
    /// <c>/</c> truncates a non-divisible quotient (<c>lean/KatLang.lean</c>, the <c>.div</c> arm), so a non-integer
    /// quotient would be a known model difference, never a C#/Lean differential (a draft with <c>1 / (3 - t)</c>
    /// read <c>0.5 &gt; 0</c> in C# and <c>0 &gt; 0</c> in Lean).
    /// </summary>
    private static SemanticFragment WhileFault(SemanticGrammar.Gen g, bool alternative)
    {
        var f = LoopFragment();
        f.Features.UnionWith(["while", "condition-first", "failure"]);
        var step = g.Fresh();
        var x = g.Fresh();
        var flag = new MExpr.Binary(">", new MExpr.Binary("/", Atom(2), new MExpr.Binary("-", Atom(3), Traced(Tick()))), Atom(0));
        f.Decls.Add(new MDecl.Func(step, [new MParam(x, false)], new MExpr.Brace(new MScope([],
            [new MExpr.Add(new MExpr.Ref(x), Traced(Tick())), flag]))));
        f.Row = new MExpr.Dot(new MExpr.Call(step, [Atom(0)]), "while", null);

        var clock = new TickClock();
        var state = 0;
        if (!alternative)
        {
            while (true)
            {
                var divisorTick = clock.Next();
                f.Events.Add(TraceEvent(divisorTick));
                if (3 - divisorTick == 0)
                {
                    f.FailureCategory = "DivByZero";
                    break;
                }

                if (!(ExactQuotient(2, 3 - divisorTick) > 0)) break;
                var transitionTick = clock.Next();
                f.Events.Add(TraceEvent(transitionTick));
                state += transitionTick;
            }

            f.Paths |= SemanticPath.FirstFailureStops;
        }
        else
        {
            while (true)
            {
                var transitionTick = clock.Next();
                f.Events.Add(TraceEvent(transitionTick));
                var next = state + transitionTick;
                var divisorTick = clock.Next();
                f.Events.Add(TraceEvent(divisorTick));
                if (3 - divisorTick == 0)
                {
                    f.FailureCategory = "DivByZero";
                    break;
                }

                if (!(ExactQuotient(2, 3 - divisorTick) > 0)) break;
                state = next;
            }
        }

        if (f.FailureCategory is null) f.Value = Res(state);
        f.Paths |= SemanticPath.GenericInsideOptimizedLoop;
        return f;
    }

    // ── Selectors ───────────────────────────────────────────────────────────

    /// <summary><c>R = [tick(), tick(), tick()]</c>, row <c>[R[tick() mod 3, tick() mod 3], tick()]</c>.</summary>
    private static SemanticFragment ReceiverFirst(SemanticGrammar.Gen g, bool alternative)
    {
        var f = Fragment("select", "list");
        var receiver = g.Fresh();
        f.Decls.Add(new MDecl.Value(receiver, [new MExpr.ListLit([Tick(), Tick(), Tick()])]));
        MExpr Selector() => new MExpr.Binary("mod", Tick(), Atom(3));
        f.Row = new MExpr.ListLit([new MExpr.Select(new MExpr.Ref(receiver), [Selector(), Selector()]), Tick()]);

        // The written list R defers its elements (lazy collections, issue #204): a position runs
        // when a selector first selects it, right after that selector. The rejected reading is the
        // former eager receiver.
        var clock = new TickClock();
        var selected = new List<int>();
        if (!alternative)
        {
            var elements = new int?[3];
            for (var s = 0; s < 2; s++)
            {
                var index = clock.Next() % 3;
                selected.Add(elements[index] ??= clock.Next());
            }
        }
        else
        {
            int[] elements = [clock.Next(), clock.Next(), clock.Next()];
            for (var s = 0; s < 2; s++) selected.Add(elements[clock.Next() % 3]);
        }

        f.Value = new Result.ListValue([new Result.SequenceValue([.. selected.Select(v => (Result)Res(v))]), Res(clock.Next())]);
        return f;
    }

    /// <summary><c>S = v1, v2, v3, v4</c>, row <c>[S[tick() - 1, (tick(), tick())*], tick()]</c>.</summary>
    private static SemanticFragment SpreadFormation(SemanticGrammar.Gen g, bool alternative)
    {
        var f = Fragment("select", "spread");
        var data = Enumerable.Range(0, 4).Select(_ => g.Value()).ToArray();
        var s = g.Fresh();
        f.Decls.Add(new MDecl.Value(s, [.. data.Select(v => (MExpr)Atom(v))]));
        f.Row = new MExpr.ListLit(
        [
            new MExpr.Select(new MExpr.Ref(s), [new MExpr.Binary("-", Tick(), Atom(1)), new MExpr.Spread(new MExpr.Group([Tick(), Tick()]))]),
            Tick(),
        ]);

        var clock = new TickClock();
        int[] indices;
        if (!alternative)
        {
            int[] spread = [clock.Next(), clock.Next()];
            indices = [clock.Next() - 1, .. spread];
        }
        else
        {
            var head = clock.Next() - 1;
            indices = [head, clock.Next(), clock.Next()];
        }

        f.Value = new Result.ListValue([new Result.SequenceValue([.. indices.Select(i => (Result)Res(data[i]))]), Res(clock.Next())]);
        return f;
    }

    /// <summary>
    /// Retained: <c>Pick(*xs) = xs[1, 1]</c>, row <c>[Pick(tick(), tick(), tick()), tick()]</c>. Eager:
    /// <c>Keep(*xs) = xs</c>, row <c>[Keep(tick(), tick(), tick())[1, 1], tick()]</c>.
    /// </summary>
    private static SemanticFragment RetainedSelection(SemanticGrammar.Gen g, bool alternative, bool retained)
    {
        var f = Fragment("select", "collect");
        var fn = g.Fresh();
        var xs = g.Fresh();
        MExpr[] supply = [Tick(), Tick(), Tick()];
        if (retained)
        {
            f.Decls.Add(new MDecl.Func(fn, [new MParam(xs, Collecting: true)], new MExpr.Select(new MExpr.Ref(xs), [Atom(1), Atom(1)])));
            f.Row = new MExpr.ListLit([new MExpr.Call(fn, supply), Tick()]);
            f.Features.Add("retained-collector");
        }
        else
        {
            f.Decls.Add(new MDecl.Func(fn, [new MParam(xs, Collecting: true)], new MExpr.Ref(xs)));
            f.Row = new MExpr.ListLit([new MExpr.Select(new MExpr.Call(fn, supply), [Atom(1), Atom(1)]), Tick()]);
            f.Features.Add("eager-call-result");
        }

        var clock = new TickClock();
        int selected;
        if (retained != alternative)
        {
            // Only the selected cell runs; the repeated position reuses its one outcome.
            selected = clock.Next();
        }
        else
        {
            int[] list = [clock.Next(), clock.Next(), clock.Next()];
            selected = list[1];
        }

        f.Value = new Result.ListValue([new Result.SequenceValue([Res(selected), Res(selected)]), Res(clock.Next())]);
        return f;
    }

    /// <summary><c>S = v1, v2, v3</c>, row <c>S[trace(tick()) - 1, 9, trace(tick())]</c>: the second selector is out of range.</summary>
    private static SemanticFragment RejectingSelector(SemanticGrammar.Gen g, bool alternative)
    {
        var f = Fragment("select");
        var s = g.Fresh();
        f.Decls.Add(new MDecl.Value(s, [.. Enumerable.Range(0, 3).Select(_ => (MExpr)Atom(g.Value()))]));
        f.Row = new MExpr.Select(new MExpr.Ref(s), [new MExpr.Binary("-", Traced(Tick()), Atom(1)), Atom(9), Traced(Tick())]);

        var clock = new TickClock();
        f.Events.Add(TraceEvent(clock.Next()));
        if (alternative) f.Events.Add(TraceEvent(clock.Next()));
        f.FailureCategory = "BadIndex";
        f.Paths |= SemanticPath.FirstFailureStops;
        f.Features.Add("failure");
        return f;
    }

    // ── Member reads ────────────────────────────────────────────────────────

    /// <summary><c>Lib = { M = tick() ⏎ d }</c>: a property with one member and an output row that is no reference.</summary>
    private static (Sym Lib, Sym Member) Library(SemanticGrammar.Gen g, SemanticFragment f)
    {
        var lib = g.Fresh();
        var member = g.Fresh();
        f.Decls.Add(new MDecl.Value(lib, [new MExpr.Brace(new MScope([new MDecl.Value(member, [Tick()])], [Atom(g.Digit())]))]));
        return (lib, member);
    }

    /// <summary><c>C = { M = tick() ⏎ Lib }</c>: a forwarding carrier of <c>Lib</c> declaring its OWN member under the same name.</summary>
    private static (Sym Carrier, Sym Member) Carrier(SemanticGrammar.Gen g, SemanticFragment f, Sym lib, Sym member)
    {
        var carrier = g.Fresh();
        var own = g.ShadowOf(member);
        f.Decls.Add(new MDecl.Value(carrier, [new MExpr.Brace(new MScope([new MDecl.Value(own, [Tick()])], [new MExpr.Ref(lib)]))]));
        f.Features.Add("carrier");
        return (carrier, own);
    }

    /// <summary><c>A = Lib</c>: a transparent reference.</summary>
    private static Sym Reference(SemanticGrammar.Gen g, SemanticFragment f, Sym target)
    {
        var reference = g.Fresh();
        f.Decls.Add(new MDecl.Value(reference, [new MExpr.Ref(target)]));
        f.Features.Add("transparent-reference");
        return reference;
    }

    private static MExpr Read(Sym receiver, Sym member, params Sym[] otherTargets)
        => new MExpr.MemberRead(new MExpr.Ref(receiver), member, otherTargets);

    /// <summary><c>A = Lib</c>, row <c>[A.M, Lib.M, tick()]</c>.</summary>
    private static SemanticFragment TransparentMember(SemanticGrammar.Gen g, bool alternative)
    {
        var f = MemberFragment();
        var (lib, member) = Library(g, f);
        var reference = Reference(g, f, lib);
        f.Row = new MExpr.ListLit([Read(reference, member), Read(lib, member), Tick()]);
        int[] reads = alternative ? [1, 2] : [1, 1];
        f.Value = new Result.ListValue([Res(reads[0]), Res(reads[1]), Res(reads.Max() + 1)]);
        Hits(f, 1);
        return f;
    }

    /// <summary><c>C = { M = tick() ⏎ Lib }</c>, row <c>[C.M, Lib.M, tick()]</c>.</summary>
    private static SemanticFragment CarrierMember(SemanticGrammar.Gen g, bool alternative)
    {
        var f = MemberFragment();
        var (lib, member) = Library(g, f);
        var (carrier, own) = Carrier(g, f, lib, member);
        f.Row = new MExpr.ListLit([Read(carrier, own), Read(lib, member), Tick()]);
        int[] reads = alternative ? [1, 1] : [1, 2];
        f.Value = new Result.ListValue([Res(reads[0]), Res(reads[1]), Res(reads.Max() + 1)]);
        return f;
    }

    /// <summary><c>A = Lib</c>, <c>B = A</c>, row <c>[B.M, A.M, Lib.M, tick()]</c>.</summary>
    private static SemanticFragment TransparentChain(SemanticGrammar.Gen g, bool alternative)
    {
        var f = MemberFragment();
        f.Features.Add("static-alias");
        var (lib, member) = Library(g, f);
        var first = Reference(g, f, lib);
        var second = Reference(g, f, first);
        f.Row = new MExpr.ListLit([Read(second, member), Read(first, member), Read(lib, member), Tick()]);
        int[] reads = alternative ? [1, 2, 3] : [1, 1, 1];
        f.Value = new Result.ListValue([.. reads.Select(r => (Result)Res(r)), Res(reads.Max() + 1)]);
        Hits(f, 2);
        return f;
    }

    /// <summary><c>A = Lib</c>, <c>C = { M = tick() ⏎ Lib }</c>, <c>Nav(t) = t.M</c>, row <c>[Nav(A), Nav(C), Lib.M, tick()]</c>.</summary>
    private static SemanticFragment PassedMember(SemanticGrammar.Gen g, bool alternative)
    {
        var f = MemberFragment();
        f.Features.Add("passed-callable");
        var (lib, member) = Library(g, f);
        var reference = Reference(g, f, lib);
        var (carrier, own) = Carrier(g, f, lib, member);
        var nav = g.Fresh();
        var t = g.Fresh();
        f.Decls.Add(new MDecl.Func(nav, [new MParam(t, false)], Read(t, member, own)));
        f.Row = new MExpr.ListLit([new MExpr.Call(nav, [new MExpr.Ref(reference)]), new MExpr.Call(nav, [new MExpr.Ref(carrier)]), Read(lib, member), Tick()]);
        int[] reads = alternative ? [1, 1, 1] : [1, 2, 1];
        f.Value = new Result.ListValue([.. reads.Select(r => (Result)Res(r)), Res(reads.Max() + 1)]);
        Hits(f, 1);
        return f;
    }

    // ── Nested parameterized owners ─────────────────────────────────────────

    /// <summary>
    /// <c>Outer(a) = { Inner(b) = { V = tick() ⏎ V * 100 + a * 10 + b } ⏎ [Inner(1), Inner(2)] }</c> (or
    /// <c>V = tick()</c> declared by <c>Outer</c>), row <c>[Outer(1), Outer(2), tick()]</c> (or equal arguments
    /// at both levels: <c>Inner(1), Inner(1)</c> inside <c>Outer(1), Outer(1)</c>).
    /// </summary>
    private static SemanticFragment Owners(SemanticGrammar.Gen g, bool alternative, bool innerOwned, bool sameArguments)
    {
        var f = OwnerFragment();
        if (sameArguments) f.Features.Add("same-arguments");
        var outer = g.Fresh();
        var a = g.Fresh();
        var inner = g.Fresh();
        var b = g.Fresh();
        var v = g.Fresh();
        MExpr formula = new MExpr.Add(new MExpr.Add(Times(new MExpr.Ref(v), 100), Times(new MExpr.Ref(a), 10)), new MExpr.Ref(b));
        var local = new MDecl.Value(v, [Tick()]);
        var innerDecl = innerOwned
            ? new MDecl.Func(inner, [new MParam(b, false)], new MExpr.Brace(new MScope([local], [formula])))
            : new MDecl.Func(inner, [new MParam(b, false)], formula);
        int[] innerArguments = sameArguments ? [1, 1] : [1, 2];
        var calls = new MExpr.ListLit([.. innerArguments.Select(i => (MExpr)new MExpr.Call(inner, [Atom(i)]))]);
        f.Decls.Add(new MDecl.Func(outer, [new MParam(a, false)], new MExpr.Brace(innerOwned
            ? new MScope([innerDecl], [calls])
            : new MScope([local, innerDecl], [calls]))));
        int[] outerArguments = sameArguments ? [1, 1] : [1, 2];
        f.Row = new MExpr.ListLit([.. outerArguments.Select(o => (MExpr)new MExpr.Call(outer, [Atom(o)])), Tick()]);

        // The intended lifetime: per inner activation (inner-owned) or per outer activation (outer-owned).
        // The rejected readings swap the owner (different arguments) or key the state by argument values.
        var perInner = sameArguments ? innerOwned : innerOwned != alternative;
        var byArgumentValue = sameArguments && alternative;
        var clock = new TickClock();
        var cache = new Dictionary<(int, int), int>();
        var results = new List<Result>();
        for (var o = 0; o < outerArguments.Length; o++)
        {
            var row = new List<Result>();
            for (var i = 0; i < innerArguments.Length; i++)
            {
                var outerKey = byArgumentValue && !innerOwned ? outerArguments[o] : o;
                var innerKey = byArgumentValue ? innerArguments[i] : i;
                var key = (outerKey, perInner ? innerKey : -1);
                if (!cache.TryGetValue(key, out var value)) cache[key] = value = clock.Next();
                row.Add(Res(value * 100 + outerArguments[o] * 10 + innerArguments[i]));
            }

            results.Add(new Result.ListValue(row));
        }

        results.Add(Res(clock.Next()));
        f.Value = new Result.ListValue(results);
        if (!innerOwned) Hits(f, outerArguments.Length * (innerArguments.Length - 1));
        return f;
    }

    /// <summary>
    /// <c>Outer(a) = { U = tick() ⏎ Inner(b) = { V = U * 10 + tick() ⏎ V + a * b } ⏎ [Inner(1), Inner(2)] }</c>,
    /// row <c>[Outer(1), Outer(2), tick()]</c>: both owners' local properties, each with its own lifetime.
    /// </summary>
    private static SemanticFragment OwnerChain(SemanticGrammar.Gen g, bool alternative)
    {
        var f = OwnerFragment();
        var outer = g.Fresh();
        var a = g.Fresh();
        var u = g.Fresh();
        var inner = g.Fresh();
        var b = g.Fresh();
        var v = g.Fresh();
        var innerBody = new MScope(
            [new MDecl.Value(v, [new MExpr.Add(Times(new MExpr.Ref(u), 10), Tick())])],
            [new MExpr.Add(new MExpr.Ref(v), new MExpr.Binary("*", new MExpr.Ref(a), new MExpr.Ref(b)))]);
        int[] innerArguments = [1, 2];
        f.Decls.Add(new MDecl.Func(outer, [new MParam(a, false)], new MExpr.Brace(new MScope(
            [new MDecl.Value(u, [Tick()]), new MDecl.Func(inner, [new MParam(b, false)], new MExpr.Brace(innerBody))],
            [new MExpr.ListLit([.. innerArguments.Select(i => (MExpr)new MExpr.Call(inner, [Atom(i)]))])]))));
        int[] outerArguments = [1, 2];
        f.Row = new MExpr.ListLit([.. outerArguments.Select(o => (MExpr)new MExpr.Call(outer, [Atom(o)])), Tick()]);

        var clock = new TickClock();
        var results = new List<Result>();
        foreach (var outerArgument in outerArguments)
        {
            int? outerU = null;
            int? sharedV = null;
            var row = new List<Result>();
            foreach (var innerArgument in innerArguments)
            {
                int V()
                {
                    outerU ??= clock.Next();
                    return outerU.Value * 10 + clock.Next();
                }

                int innerV;
                if (alternative)
                {
                    sharedV ??= V();
                    innerV = sharedV.Value;
                }
                else
                {
                    innerV = V();
                }

                row.Add(Res(innerV + outerArgument * innerArgument));
            }

            results.Add(new Result.ListValue(row));
        }

        results.Add(Res(clock.Next()));
        f.Value = new Result.ListValue(results);
        Hits(f, outerArguments.Length * (innerArguments.Length - 1));
        return f;
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    /// <summary>
    /// The run's ONE <c>tick()</c> counter as the rule states it: it starts at zero and each executed
    /// <c>tick()</c> advances it by one and returns the new value (<c>evaluator-and-hosting.md</c> § The
    /// <c>tick()</c> diagnostic counter). The expectations replay a shape's demand order on it.
    /// </summary>
    private sealed class TickClock
    {
        private int _count;

        public int Next() => ++_count;
    }

    /// <summary>A suspended <c>tick()</c> argument cell: it runs at its first VALUE demand and memoizes (NEED-02).</summary>
    private sealed class LazyTick(TickClock clock)
    {
        private int? _value;

        public int Demand()
        {
            _value ??= clock.Next();
            return _value.Value;
        }
    }

    private static SemanticFragment Fragment(params string[] features)
    {
        var f = new SemanticFragment(Family);
        f.Features.Add("tick-order");
        f.Features.UnionWith(features);
        return f;
    }

    private static SemanticFragment LoopFragment()
    {
        var f = Fragment("loop");
        f.IsLoop = true;
        return f;
    }

    private static SemanticFragment MemberFragment() => Fragment("member-read", "alias");

    private static SemanticFragment OwnerFragment() => Fragment("nested-owner", "activation-state");

    /// <summary>
    /// Records the minimum number of zero-argument cache hits the shape's repeated reads must show under
    /// the INTENDED rule. An alternative build keeps the same claim, so its control differs from the
    /// intended case only in the expected value or events.
    /// </summary>
    private static void Hits(SemanticFragment f, int hits)
    {
        if (hits <= 0) return;
        f.MinimumCacheHits = hits;
        f.Paths |= SemanticPath.CacheHit;
        f.Features.Add("cache");
    }

    private static MExpr Tick() => new MExpr.Prim("tick", []);

    private static MExpr Traced(MExpr value) => new MExpr.Prim("trace", [value]);

    private static string TraceEvent(int value) => "trace:" + value.ToString(System.Globalization.CultureInfo.InvariantCulture);

    private static MExpr Times(MExpr left, int factor) => new MExpr.Binary("*", left, Atom(factor));

    /// <summary>
    /// <paramref name="dividend"/> / <paramref name="divisor"/> for a divisor known to be non-zero, refusing a
    /// non-integer quotient: Lean's integer core truncates one, so a shape must stay exact to be a differential.
    /// </summary>
    private static int ExactQuotient(int dividend, int divisor)
    {
        if (divisor == 0 || dividend % divisor != 0)
            throw new InvalidOperationException($"tick shape quotient {dividend} / {divisor} is not an exact integer");
        return dividend / divisor;
    }

    private static MExpr.Atom Atom(int value) => SemanticGrammar.Atom(value);

    private static Result.Atom Res(int value) => SemanticGrammar.Res(value);

    private static Result.ListValue Ints(IEnumerable<int> values) => new([.. values.Select(v => (Result)Res(v))]);
}
