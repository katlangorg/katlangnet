using System.Collections.Immutable;
using System.Globalization;
using System.Numerics;
using KatLang;
using KatLang.Tests.StructuralFuzz;

namespace KatLang.ParserFuzz;

/// <summary>
/// Versioned identity of the SEM-2B generator. A descriptor names the generator and the recipe
/// version that built it; a recipe change that would make an existing case id mean a different
/// program MUST bump <see cref="RecipeVersion"/>, and replay refuses a version it does not build
/// rather than silently reinterpreting it.
/// </summary>
internal static class SemanticRecipe
{
    internal const string GeneratorId = "sem2b-grammar";

    internal const int RecipeVersion = 1;

    internal static string CasePrefix => "sem2b/v" + RecipeVersion.ToString(CultureInfo.InvariantCulture) + "/";
}

/// <summary>
/// Source of every generation decision. The systematic chooser cycles each named dimension through
/// all its values across consecutive case indices (each-choice coverage); the seeded chooser draws
/// from one independent SplitMix64 stream PER CASE, so one case can be rebuilt from (seed, index)
/// without generating any other case.
/// </summary>
internal abstract class SemanticChooser
{
    public abstract int Pick(string dimension, int count);

    public bool Chance(string dimension, int percent) => Pick(dimension, 100) < percent;

    internal static SemanticChooser Systematic(int index) => new SystematicChooser(index);

    internal static SemanticChooser Seeded(ulong seed, int index) => new SeededChooser(seed, index);

    /// <summary>FNV-1a over UTF-16 units: a platform-independent dimension offset.</summary>
    internal static int StableHash(string text)
    {
        unchecked
        {
            var hash = 2166136261u;
            foreach (var c in text)
            {
                hash ^= c;
                hash *= 16777619u;
            }

            return (int)(hash & 0x7FFFFFFF);
        }
    }

    /// <summary>
    /// Case <c>index</c> takes value <c>(index + hash(dimension) + occurrence) mod count</c>: across
    /// consecutive indices every dimension visits every value, and a dimension picked repeatedly
    /// within one case (a list of operations) advances instead of repeating.
    /// </summary>
    private sealed class SystematicChooser(int index) : SemanticChooser
    {
        private readonly Dictionary<string, int> _occurrences = new(StringComparer.Ordinal);

        public override int Pick(string dimension, int count)
        {
            if (count <= 0) throw new ArgumentOutOfRangeException(nameof(count));
            var occurrence = _occurrences.GetValueOrDefault(dimension);
            _occurrences[dimension] = occurrence + 1;
            return (int)(((long)index + StableHash(dimension) + occurrence) % count);
        }
    }

    private sealed class SeededChooser : SemanticChooser
    {
        private SplitMix64 _rng;

        public SeededChooser(ulong seed, int index)
            => _rng = new SplitMix64(seed ^ (0x9E3779B97F4A7C15UL * (ulong)(index + 1)));

        public override int Pick(string dimension, int count)
            => count <= 0 ? throw new ArgumentOutOfRangeException(nameof(count)) : _rng.Next(count);
    }
}

/// <summary>
/// One generated, self-contained piece of a program: its declarations, ONE root row, and that row's
/// construction-derived meaning (value or runtime failure, exact host events, intended paths). A
/// fragment's symbols are its own, so fragments compose without interacting except through the
/// one root evaluation order — which is exactly what the composite expectation models.
/// </summary>
internal sealed class SemanticFragment(string family)
{
    public string Family { get; } = family;

    public List<MDecl> Decls { get; } = [];

    public MExpr Row { get; set; } = null!;

    public Result? Value { get; set; }

    public string? FailureCategory { get; set; }

    public List<string> Events { get; } = [];

    public SortedSet<string> Features { get; } = new(StringComparer.Ordinal);

    public SemanticPath Paths { get; set; }

    public int MinimumCacheHits { get; set; }

    /// <summary>A loop fragment: loop evidence is aggregated per run, so a case carries at most one.</summary>
    public bool IsLoop { get; set; }

    /// <summary>The failure is raised when the run's VALUE is exported, after every row ran: it must be last.</summary>
    public bool FailsAtExport { get; set; }

    public bool Failing => FailureCategory is not null;
}

/// <summary>
/// The SEM-2B grammar-aware generator over the symbol-addressed structural model.
///
/// <para><b>Productions.</b> Eight families build fragments whose preconditions are explicit in
/// their construction (fixed arities, distinct argument values, bounded loop counts, terminating
/// steps), so no generated case is ever discarded: an unexpected parse rejection or runtime outcome
/// is an actionable failure. Contexts wrap a fragment's row in a consumer whose effect on the value
/// is known (list, live/dead <c>if</c> branch, property, cached double read, wrapper call, brace
/// scope). Composition concatenates fragments as root rows and models root row order, the first
/// terminal failure, and the root control row.</para>
///
/// <para><b>Expectations</b> are computed from the construction: arithmetic over the chosen
/// constants, the demand order the language rules prescribe (left-to-right operands, at-most-once
/// cells, eager collection values, lazy argument views, fresh invocations), and the documented
/// failure kinds. Nothing runs the implementation to learn an expectation.</para>
/// </summary>
internal static class SemanticGrammar
{
    internal static readonly ImmutableArray<string> Families =
        ["meta", "collect", "alias", "cache", "select", "loop", "failure", "async"];

    /// <summary>Contexts (consumers) a fragment row can be placed in. Index 0 is the bare row.</summary>
    internal static readonly ImmutableArray<string> Contexts =
        ["bare", "list", "if-true", "if-false", "property", "property-double", "wrapper", "brace"];

    /// <summary>Invalid front-end productions: name, diagnostic, phase.</summary>
    internal static readonly ImmutableArray<(string Name, DiagnosticCode Code, string Phase)> InvalidProductions =
    [
        ("meta-on-collector", DiagnosticCode.InvalidMetaParameter, SemanticExpectation.SyntaxPhase),
        ("duplicate-property", DiagnosticCode.DuplicateProperty, SemanticExpectation.SyntaxPhase),
        ("parameter-property-collision", DiagnosticCode.ParameterPropertyCollision, SemanticExpectation.ElaborationPhase),
        ("closed-parameter-list", DiagnosticCode.UndeclaredIdentifier, SemanticExpectation.ElaborationPhase),
    ];

    /// <summary>The tripwire atom a dead branch would trace; it must never appear in an event log.</summary>
    internal const int TripwireValue = 666;

    // ── Families ────────────────────────────────────────────────────────────

    internal static SemanticFragment Build(string family, Gen g, bool failing) => family switch
    {
        "meta" => Meta(g, failing),
        "collect" => Collect(g, failing),
        "alias" => Alias(g, failing),
        "cache" => Cache(g, failing),
        "select" => Selection(g, failing),
        "loop" => Loop(g, failing),
        "failure" => CompetingFailure(g, failing),
        "async" => Async(g, failing),
        _ => throw new ArgumentOutOfRangeException(nameof(family), family, "unknown SEM-2B family"),
    };

    /// <summary>
    /// META capture and lazy argument views: <c>Cap(meta op) = op</c> reached directly, through a
    /// callable alias, or through an ORDINARY forwarding parameter (which transports the original
    /// cell into the META slot); a captured written invocation of a fixed or collecting target; a
    /// list of operations over the one reference — count, view selection, cell-preserving spread
    /// into a picker, <c>Invoke()</c>, a fresh <c>Algorithm(...)</c> call and the rebuilt
    /// <c>Algorithm(Arguments*)</c>.
    /// </summary>
    private static SemanticFragment Meta(Gen g, bool failing)
    {
        var f = new SemanticFragment("meta");
        f.Features.Add("meta");

        var failure = failing ? g.Pick("meta.fail", 7) : -1;
        var route = failure == 6 ? 3 : g.Pick("meta.route", 3);
        var cap = MetaRoute(g, f, route);

        var collecting = !failing && g.Pick("meta.target", 3) == 2;
        var bodyEffect = g.Pick("meta.bodyEffect", 2) == 1;
        var k = 1 + g.Pick("meta.arity", 3);

        // The captured call's cells: k traced/waited arguments, plus a spread of a literal
        // property for a collecting target (spread items are effective cells with no effect).
        var cells = new List<(int Value, string? Event)>();
        var args = new List<MExpr>();
        for (var i = 0; i < k; i++)
        {
            var v = g.Digit();
            var wait = g.Chance("meta.wait", 25);
            args.Add(Effect(wait, v));
            cells.Add((v, (wait ? "wait:" : "trace:") + v.ToString(CultureInfo.InvariantCulture)));
            if (wait) f.Features.Add("async");
        }

        if (collecting && g.Chance("meta.spread", 50))
        {
            var p = g.Fresh();
            int[] rows = [g.Value(), g.Value()];
            f.Decls.Add(new MDecl.Value(p, rows.Select(r => (MExpr)Atom(r)).ToList()));
            args.Add(new MExpr.Spread(new MExpr.Ref(p)));
            cells.AddRange(rows.Select(r => (r, (string?)null)));
            f.Features.Add("spread");
        }

        if (collecting) f.Features.Add("collect");

        // Target T: fixed positional weights, or a collector counting its cells.
        var t = g.Fresh();
        var ps = new List<MParam>();
        MExpr body;
        if (collecting)
        {
            var xs = g.Fresh();
            ps.Add(new MParam(xs, Collecting: true));
            body = new MExpr.Prim("count", [new MExpr.Ref(xs)]);
        }
        else
        {
            for (var i = 0; i < k; i++) ps.Add(new MParam(g.Fresh(), Collecting: false));
            body = Weighted(ps.Select(p => (MExpr)new MExpr.Ref(p.Symbol)).ToList());
        }

        if (bodyEffect) body = new MExpr.Prim("trace", [body]);
        f.Decls.Add(new MDecl.Func(t, ps, body));

        int TargetValue(IReadOnlyList<int> values) => collecting ? values.Count : WeightedValue(values);

        var r = g.Fresh();
        var captured = failure == 0
            ? (MExpr)Atom(5) // a VALUE, not a written invocation: the META refusal
            : new MExpr.Call(t, args);
        f.Decls.Add(new MDecl.Value(r, [new MExpr.Call(cap, [captured])]));

        var demanded = new HashSet<int>();
        void Demand(int index)
        {
            if (demanded.Add(index) && cells[index].Event is { } e) f.Events.Add(e);
        }

        void Invocation(IReadOnlyList<int>? fresh)
        {
            if (fresh is null)
            {
                for (var i = 0; i < cells.Count; i++) Demand(i);
            }

            var value = TargetValue(fresh ?? cells.Select(c => c.Value).ToList());
            if (bodyEffect) f.Events.Add("trace:" + value.ToString(CultureInfo.InvariantCulture));
        }

        MExpr View() => new MExpr.Dot(new MExpr.Ref(r), "Arguments", null);

        var ops = new List<MExpr>();
        var values = new List<Result>();
        var invocations = 0;
        var picks = 0;
        var opCount = failure is 0 or 6 ? 0 : (failing ? g.Pick("meta.prefixOps", 3) : 1 + g.Pick("meta.ops", 4));
        for (var o = 0; o < opCount; o++)
        {
            switch (g.Pick("meta.op", 6))
            {
                case 0:
                    ops.Add(new MExpr.Dot(View(), "count", null));
                    values.Add(Res(cells.Count));
                    break;
                case 1:
                {
                    var i = g.Pick("meta.select", cells.Count);
                    ops.Add(new MExpr.Select(View(), [Atom(i)]));
                    Demand(i);
                    values.Add(Res(cells[i].Value));
                    break;
                }

                case 2:
                    ops.Add(new MExpr.Dot(new MExpr.Ref(r), "Invoke", []));
                    Invocation(null);
                    values.Add(Res(TargetValue(cells.Select(c => c.Value).ToList())));
                    invocations++;
                    break;
                case 3:
                {
                    // Cell-preserving spread into a picker: only the picked cell is demanded.
                    var j = g.Pick("meta.pick", cells.Count);
                    var pick = g.Fresh();
                    var xs = Enumerable.Range(0, cells.Count).Select(_ => new MParam(g.Fresh(), Collecting: false)).ToList();
                    f.Decls.Add(new MDecl.Func(pick, xs, new MExpr.Ref(xs[j].Symbol)));
                    ops.Add(new MExpr.Call(pick, [new MExpr.Spread(View())]));
                    Demand(j);
                    values.Add(Res(cells[j].Value));
                    picks++;
                    break;
                }

                case 4:
                {
                    // A fresh call of the captured callee with new literal arguments.
                    var fresh = Enumerable.Range(0, collecting ? 1 + g.Pick("meta.freshCount", 3) : k).Select(_ => g.Digit()).ToList();
                    ops.Add(new MExpr.Dot(new MExpr.Ref(r), "Algorithm", fresh.Select(v => (MExpr)Atom(v)).ToList()));
                    Invocation(fresh);
                    values.Add(Res(TargetValue(fresh)));
                    invocations++;
                    break;
                }

                default:
                    // The rebuilt invocation over the ORIGINAL cells.
                    ops.Add(new MExpr.Dot(new MExpr.Ref(r), "Algorithm", [new MExpr.Spread(View())]));
                    Invocation(null);
                    values.Add(Res(TargetValue(cells.Select(c => c.Value).ToList())));
                    invocations++;
                    break;
            }
        }

        if (picks > 0 && demanded.Count < cells.Count(c => c.Event is not null)) f.Paths |= SemanticPath.LazyTransport;
        if (bodyEffect && invocations >= 2) f.Paths |= SemanticPath.FreshInvocation;

        if (!failing)
        {
            f.Row = new MExpr.ListLit(ops);
            f.Value = new Result.ListValue(values);
            return f;
        }

        // A failing operation ends the list: the prefix operations' effects happened, nothing after.
        switch (failure)
        {
            case 0:
                ops.Add(new MExpr.Dot(new MExpr.Ref(r), "Invoke", []));
                f.FailureCategory = "NotAnAlgorithm";
                f.Features.Add("meta-refusal");
                break;
            case 1:
                ops.Add(new MExpr.Dot(new MExpr.Ref(r), "Invoke", [Atom(8)]));
                f.FailureCategory = "ArityMismatch";
                break;
            case 2:
                ops.Add(new MExpr.Dot(new MExpr.Ref(r), "Arguments", []));
                f.FailureCategory = "IllegalInEval";
                break;
            case 3:
                ops.Add(new MExpr.Select(View(), [Atom(cells.Count)]));
                f.FailureCategory = "BadIndex";
                f.Features.Add("select");
                break;
            case 4:
                ops.Add(new MExpr.Select(View(), [new MExpr.Binary("/", Atom(1), Atom(0))]));
                f.FailureCategory = "DivByZero";
                f.Features.Add("select");
                break;
            case 5:
                // The reference itself would leave its run: refused when the run's value is exported.
                ops.Add(new MExpr.Ref(r));
                f.FailureCategory = "TypeMismatch";
                f.FailsAtExport = true;
                break;
            default:
                // META forwarded into META: the inner capture sees an existing reference.
                ops.Add(new MExpr.Dot(new MExpr.Ref(r), "Invoke", []));
                f.FailureCategory = "NotAnAlgorithm";
                f.Features.Add("meta-refusal");
                break;
        }

        f.Features.Add("failure");
        f.Row = new MExpr.ListLit(ops);
        return f;
    }

    /// <summary>
    /// Declares <c>Cap(meta op) = op</c> and returns the symbol a capture calls: the helper itself
    /// (route 0), a callable alias of it (1), an ordinary forwarding wrapper (2), or — the declared
    /// META-to-META refusal — a forwarding wrapper whose own parameter is META (3).
    /// </summary>
    private static Sym MetaRoute(Gen g, SemanticFragment f, int route)
    {
        var cap = g.Fresh();
        var op = g.Fresh();
        f.Decls.Add(new MDecl.Func(cap, [new MParam(op, Collecting: false, Meta: true)], new MExpr.Ref(op)));
        switch (route)
        {
            case 1:
            {
                var alias = g.Fresh();
                f.Decls.Add(new MDecl.Value(alias, [new MExpr.Ref(cap)]));
                f.Features.Add("alias");
                return alias;
            }

            case 2:
            case 3:
            {
                var forward = g.Fresh();
                var o = g.Fresh();
                f.Decls.Add(new MDecl.Func(forward, [new MParam(o, Collecting: false, Meta: route == 3)],
                    new MExpr.Call(cap, [new MExpr.Ref(o)])));
                f.Features.Add("forwarding");
                return forward;
            }

            default:
                return cap;
        }
    }

    /// <summary>
    /// Collectors and supply boundaries: fixed prefix/suffix around a collector, literal, spread,
    /// empty-spread and forwarded supplies, the collected LIST value, nested sequence and list
    /// patterns, and cardinality failures that precede every demand.
    /// </summary>
    private static SemanticFragment Collect(Gen g, bool failing)
    {
        var f = new SemanticFragment("collect");
        f.Features.Add("collect");

        if (failing)
        {
            f.Features.Add("failure");
            switch (g.Pick("collect.fail", 4))
            {
                case 0:
                {
                    // Too few for a prefix + suffix collector: rejected before any argument runs.
                    var fn = g.Fresh();
                    var a = g.Fresh();
                    var rest = g.Fresh();
                    var z = g.Fresh();
                    f.Decls.Add(new MDecl.Func(fn, [new(a, false), new(rest, true), new(z, false)], new MExpr.Ref(a)));
                    f.Row = new MExpr.Call(fn, [Effect(false, g.Digit())]);
                    f.FailureCategory = "VariadicArityMismatch";
                    f.Paths |= SemanticPath.CardinalityBeforeDemand;
                    return f;
                }

                case 1:
                {
                    var fn = g.Fresh();
                    var a = g.Fresh();
                    var b = g.Fresh();
                    f.Decls.Add(new MDecl.Func(fn, [new(a, false), new(b, false)], new MExpr.Add(new MExpr.Ref(a), new MExpr.Ref(b))));
                    f.Row = new MExpr.Call(fn, [Effect(false, g.Digit()), Effect(false, g.Digit()), Effect(false, g.Digit())]);
                    f.FailureCategory = "ArityMismatch";
                    f.Paths |= SemanticPath.CardinalityBeforeDemand;
                    return f;
                }

                case 2:
                {
                    var (fn, _) = ListPatternFunc(g, f);
                    f.Row = new MExpr.Call(fn, [new MExpr.ListLit([])]);
                    f.FailureCategory = "ArityMismatch";
                    f.Features.Add("list-pattern");
                    return f;
                }

                default:
                {
                    var fn = SequencePatternFunc(g, f);
                    f.Row = new MExpr.Call(fn, [Atom(g.Value())]);
                    f.FailureCategory = "TypeMismatch";
                    f.Features.Add("sequence-pattern");
                    return f;
                }
            }
        }

        switch (g.Pick("collect.kind", 4))
        {
            case 1:
            {
                // H((a, *b)) = count(b) * 10 + a over a multi-row property: one received sequence.
                var fn = SequencePatternFunc(g, f);
                var p = g.Fresh();
                var m = 2 + g.Pick("collect.patternWidth", 3);
                var rows = Enumerable.Range(0, m).Select(_ => g.Digit()).ToList();
                f.Decls.Add(new MDecl.Value(p, rows.Select(v => (MExpr)Atom(v)).ToList()));
                f.Row = new MExpr.Call(fn, [new MExpr.Ref(p)]);
                f.Value = Res((m - 1) * 10 + rows[0]);
                f.Features.Add("sequence-pattern");
                return f;
            }

            case 2:
            {
                // G([x, *y]) = x + count(y) over an exact list.
                var (fn, _) = ListPatternFunc(g, f);
                var m = 1 + g.Pick("collect.patternWidth", 3);
                var items = Enumerable.Range(0, m).Select(_ => g.Digit()).ToList();
                f.Row = new MExpr.Call(fn, [new MExpr.ListLit(items.Select(v => (MExpr)Atom(v)).ToList())]);
                f.Value = Res(items[0] + (m - 1));
                f.Features.Add("list-pattern");
                return f;
            }

            default:
                break;
        }

        var prefix = g.Pick("collect.prefix", 2) == 1;
        var suffix = g.Pick("collect.suffix", 2) == 1;
        var restCount = g.Pick("collect.rest", 4);
        var shape = g.Pick("collect.shape", 4);
        if (shape == 1 && restCount < 2) shape = 0; // a spread property needs at least two rows
        var consumer = g.Pick("collect.consumer", 4);
        if (consumer == 1 && !prefix && !suffix) consumer = 0;
        if (consumer == 3 && restCount == 0) consumer = 0;

        var func = g.Fresh();
        var aSym = prefix ? g.Fresh() : default;
        var restSym = g.Fresh();
        var zSym = suffix ? g.Fresh() : default;
        var ps = new List<MParam>();
        if (prefix) ps.Add(new MParam(aSym, false));
        ps.Add(new MParam(restSym, true));
        if (suffix) ps.Add(new MParam(zSym, false));

        var aValue = prefix ? g.Digit() : 0;
        var zValue = suffix ? g.Digit() : 0;
        var restValues = Enumerable.Range(0, restCount).Select(_ => g.Digit()).ToList();
        var traceRest = shape != 1;

        MExpr body;
        Result value;
        var events = new List<string>();
        void RestEvents()
        {
            if (traceRest) events.AddRange(restValues.Select(v => "trace:" + v.ToString(CultureInfo.InvariantCulture)));
        }

        switch (consumer)
        {
            case 1:
                body = prefix ? new MExpr.Ref(aSym) : new MExpr.Ref(zSym);
                value = Res(prefix ? aValue : zValue);
                events.Add("trace:" + (prefix ? aValue : zValue).ToString(CultureInfo.InvariantCulture));
                break;
            case 2:
                body = new MExpr.Ref(restSym);
                value = new Result.ListValue(restValues.Select(v => (Result)Res(v)).ToList());
                RestEvents(); // demanding the collected LIST value evaluates its items, in order
                f.Features.Add("list");
                break;
            case 3:
                body = new MExpr.Select(new MExpr.Ref(restSym), [Atom(0)]);
                value = Res(restValues[0]);
                RestEvents();
                f.Features.Add("select");
                break;
            default:
                body = new MExpr.Prim("count", [new MExpr.Ref(restSym)]);
                value = Res(restCount);
                RestEvents();
                break;
        }

        f.Decls.Add(new MDecl.Func(func, ps, body));

        var supply = new List<MExpr>();
        if (prefix) supply.Add(Effect(false, aValue));
        switch (shape)
        {
            case 1:
            {
                var p = g.Fresh();
                f.Decls.Add(new MDecl.Value(p, restValues.Select(v => (MExpr)Atom(v)).ToList()));
                supply.Add(new MExpr.Spread(new MExpr.Ref(p)));
                f.Features.Add("spread");
                break;
            }

            case 2:
            {
                var e = g.Fresh();
                f.Decls.Add(new MDecl.Value(e, [new MExpr.Group([])]));
                supply.AddRange(restValues.Select(v => Effect(false, v)));
                supply.Add(new MExpr.Spread(new MExpr.Ref(e)));
                f.Features.Add("empty-spread");
                break;
            }

            default:
                supply.AddRange(restValues.Select(v => Effect(false, v)));
                break;
        }

        if (suffix) supply.Add(Effect(false, zValue));

        var callee = func;
        if (shape == 3)
        {
            // W(*xs) = F(xs*): forwarding transports the collected cells unforced.
            var w = g.Fresh();
            var xs = g.Fresh();
            f.Decls.Add(new MDecl.Func(w, [new MParam(xs, true)], new MExpr.Call(func, [new MExpr.Spread(new MExpr.Ref(xs))])));
            callee = w;
            f.Features.Add("forwarding");
        }

        f.Row = new MExpr.Call(callee, supply);
        f.Value = value;
        f.Events.AddRange(events);
        if (consumer == 1 && (restCount > 0 || (prefix && suffix))) f.Paths |= SemanticPath.LazyTransport;
        return f;
    }

    private static Sym SequencePatternFunc(Gen g, SemanticFragment f)
    {
        var fn = g.Fresh();
        var a = g.Fresh();
        var b = g.Fresh();
        f.Decls.Add(new MDecl.SeqPatternFunc(fn, [new MBinder(a, false), new MBinder(b, true)],
            new MExpr.Add(new MExpr.Binary("*", new MExpr.Prim("count", [new MExpr.Ref(b)]), Atom(10)), new MExpr.Ref(a))));
        return fn;
    }

    private static (Sym Function, Sym Head) ListPatternFunc(Gen g, SemanticFragment f)
    {
        var fn = g.Fresh();
        var x = g.Fresh();
        var y = g.Fresh();
        f.Decls.Add(new MDecl.SeqPatternFunc(fn, [new MBinder(x, false), new MBinder(y, true)],
            new MExpr.Add(new MExpr.Ref(x), new MExpr.Prim("count", [new MExpr.Ref(y)])), ListPattern: true));
        return (fn, x);
    }

    /// <summary>
    /// Callable aliases and ownership: static alias chains, nested owners activated repeatedly,
    /// deliberate shadowing of a callable inside a nested owner, a runtime-target alias of a
    /// captured callee, and independent per-activation property state.
    /// </summary>
    private static SemanticFragment Alias(Gen g, bool failing)
    {
        var f = new SemanticFragment("alias");
        f.Features.Add("alias");

        if (failing)
        {
            // A bare read of a runtime alias is its link's VALUE: the captured callee read with
            // an empty supply, which a one-parameter target rejects.
            var cap = MetaRoute(g, f, 0);
            var t = g.Fresh();
            var x = g.Fresh();
            f.Decls.Add(new MDecl.Func(t, [new MParam(x, false)], new MExpr.Ref(x)));
            var r = g.Fresh();
            f.Decls.Add(new MDecl.Value(r, [new MExpr.Call(cap, [new MExpr.Call(t, [Atom(g.Digit())])])]));
            var ra = g.Fresh();
            f.Decls.Add(new MDecl.Value(ra, [new MExpr.Dot(new MExpr.Ref(r), "Algorithm", null)]));
            f.Row = new MExpr.Ref(ra);
            f.FailureCategory = "ArityMismatch";
            f.Features.Add("meta");
            f.Features.Add("failure");
            return f;
        }

        switch (g.Pick("alias.kind", 5))
        {
            case 0:
            {
                var fn = g.Fresh();
                var x = g.Fresh();
                var m = 2 + g.Pick("alias.factor", 4);
                f.Decls.Add(new MDecl.Func(fn, [new MParam(x, false)], new MExpr.Binary("*", new MExpr.Ref(x), Atom(m))));
                var target = fn;
                var depth = 1 + g.Pick("alias.depth", 2);
                for (var d = 0; d < depth; d++)
                {
                    var alias = g.Fresh();
                    f.Decls.Add(new MDecl.Value(alias, [new MExpr.Ref(target)]));
                    target = alias;
                }

                var v = g.Digit();
                f.Row = new MExpr.Call(target, [Atom(v)]);
                f.Value = Res(v * m);
                f.Features.Add("static-alias");
                return f;
            }

            case 1:
            {
                // Outer(k) = { Inner(x) = x + k  Inner(c) }, activated twice with different k.
                var outer = g.Fresh();
                var kSym = g.Fresh();
                var inner = g.Fresh();
                var x = g.Fresh();
                var c = g.Digit();
                f.Decls.Add(new MDecl.Func(outer, [new MParam(kSym, false)], new MExpr.Brace(new MScope(
                    [new MDecl.Func(inner, [new MParam(x, false)], new MExpr.Add(new MExpr.Ref(x), new MExpr.Ref(kSym)))],
                    [new MExpr.Call(inner, [Atom(c)])]))));
                var k1 = g.Value();
                var k2 = g.Value();
                f.Row = new MExpr.ListLit([new MExpr.Call(outer, [Atom(k1)]), new MExpr.Call(outer, [Atom(k2)])]);
                f.Value = new Result.ListValue([Res(c + k1), Res(c + k2)]);
                f.Features.Add("nested-owner");
                return f;
            }

            case 2:
            {
                // G(y) = { F(x) = x + 100  F(y) } shadows the root F(x) = x + 1 by NAME.
                var fn = g.Fresh();
                var x = g.Fresh();
                f.Decls.Add(new MDecl.Func(fn, [new MParam(x, false)], new MExpr.Add(new MExpr.Ref(x), Atom(1))));
                var gfn = g.Fresh();
                var y = g.Fresh();
                var shadow = g.ShadowOf(fn);
                var x2 = g.Fresh();
                f.Decls.Add(new MDecl.Func(gfn, [new MParam(y, false)], new MExpr.Brace(new MScope(
                    [new MDecl.Func(shadow, [new MParam(x2, false)], new MExpr.Add(new MExpr.Ref(x2), Atom(100)))],
                    [new MExpr.Call(shadow, [new MExpr.Ref(y)])]))));
                var v = g.Digit();
                f.Row = new MExpr.ListLit([new MExpr.Call(gfn, [Atom(v)]), new MExpr.Call(fn, [Atom(v)])]);
                f.Value = new Result.ListValue([Res(v + 100), Res(v + 1)]);
                f.Features.Add("shadowing");
                return f;
            }

            case 3:
            {
                // RA = R.Algorithm: a runtime-target alias of the captured callee.
                var cap = MetaRoute(g, f, 0);
                var t = g.Fresh();
                var a = g.Fresh();
                var b = g.Fresh();
                f.Decls.Add(new MDecl.Func(t, [new MParam(a, false), new MParam(b, false)],
                    Weighted([new MExpr.Ref(a), new MExpr.Ref(b)])));
                var a1 = g.Digit();
                var a2 = g.Digit();
                var r = g.Fresh();
                f.Decls.Add(new MDecl.Value(r, [new MExpr.Call(cap, [new MExpr.Call(t, [Effect(false, a1), Effect(false, a2)])])]));
                var ra = g.Fresh();
                f.Decls.Add(new MDecl.Value(ra, [new MExpr.Dot(new MExpr.Ref(r), "Algorithm", null)]));
                var w1 = g.Digit();
                var w2 = g.Digit();
                var items = new List<MExpr> { new MExpr.Call(ra, [Atom(w1), Atom(w2)]) };
                var values = new List<Result> { Res(WeightedValue([w1, w2])) };
                if (g.Chance("alias.rebuild", 50))
                {
                    items.Add(new MExpr.Call(ra, [new MExpr.Spread(new MExpr.Dot(new MExpr.Ref(r), "Arguments", null))]));
                    values.Add(Res(WeightedValue([a1, a2])));
                    f.Events.Add("trace:" + a1.ToString(CultureInfo.InvariantCulture));
                    f.Events.Add("trace:" + a2.ToString(CultureInfo.InvariantCulture));
                }

                f.Row = new MExpr.ListLit(items);
                f.Value = new Result.ListValue(values);
                f.Features.Add("runtime-alias");
                f.Features.Add("meta");
                return f;
            }

            default:
            {
                // Mk(n) = { V = trace(n)  V + V }: one property evaluation PER activation.
                var mk = g.Fresh();
                var n = g.Fresh();
                var vSym = g.Fresh();
                var wait = g.Chance("alias.wait", 30);
                f.Decls.Add(new MDecl.Func(mk, [new MParam(n, false)], new MExpr.Brace(new MScope(
                    [new MDecl.Value(vSym, [new MExpr.Prim(wait ? "wait" : "trace", [new MExpr.Ref(n)])])],
                    [new MExpr.Add(new MExpr.Ref(vSym), new MExpr.Ref(vSym))]))));
                var a = g.Digit();
                f.Row = new MExpr.ListLit([new MExpr.Call(mk, [Atom(a)]), new MExpr.Call(mk, [Atom(a)])]);
                f.Value = new Result.ListValue([Res(2 * a), Res(2 * a)]);
                var e = (wait ? "wait:" : "trace:") + a.ToString(CultureInfo.InvariantCulture);
                f.Events.Add(e);
                f.Events.Add(e);
                f.MinimumCacheHits = 2;
                f.Paths |= SemanticPath.CacheHit;
                f.Features.Add("activation-state");
                f.Features.Add("cache");
                if (wait) f.Features.Add("async");
                return f;
            }
        }
    }

    /// <summary>
    /// Property cache versus NeedCell sharing: cached reads against fresh explicit invocations
    /// (CACHE-PUB-1 orders), one supplied cell reused by a body, forwarded through a wrapper, and
    /// separate activations that must NOT share.
    /// </summary>
    private static SemanticFragment Cache(Gen g, bool failing)
    {
        var f = new SemanticFragment("cache");
        f.Features.Add("cache");
        var wait = g.Chance("cache.wait", 30);
        if (wait) f.Features.Add("async");
        string Ev(int v) => (wait ? "wait:" : "trace:") + v.ToString(CultureInfo.InvariantCulture);

        if (failing)
        {
            // P = trace(a) / 0: the first read fails after its effect; nothing later runs.
            var p = g.Fresh();
            var a = g.Digit();
            f.Decls.Add(new MDecl.Value(p, [new MExpr.Binary("/", Effect(wait, a), Atom(0))]));
            f.Row = new MExpr.ListLit([new MExpr.Ref(p), new MExpr.Ref(p)]);
            f.Events.Add(Ev(a));
            f.FailureCategory = "DivByZero";
            f.Features.Add("failure");
            return f;
        }

        var kind = g.Pick("cache.kind", 7);
        switch (kind)
        {
            case 0:
            case 1:
            case 2:
            case 3:
            {
                // Reads and explicit calls of one property, in each CACHE-PUB-1 order.
                var p = g.Fresh();
                var a = g.Digit();
                f.Decls.Add(new MDecl.Value(p, [Effect(wait, a)]));
                var pattern = kind;
                MExpr Read() => new MExpr.Ref(p);
                MExpr Call() => new MExpr.Call(p, []);
                (MExpr First, MExpr Second, int Effects, int Hits) shape = pattern switch
                {
                    0 => (Read(), Read(), 1, 1),   // P, P: one evaluation, a real hit
                    1 => (Call(), Call(), 2, 0),   // P(), P(): two fresh invocations, equal output
                    2 => (Read(), Call(), 2, 0),   // P, P(): the call never reads the entry
                    _ => (Call(), Read(), 1, 1),   // P(), P: the call establishes the empty entry
                };
                f.Row = new MExpr.ListLit([shape.First, shape.Second]);
                f.Value = new Result.ListValue([Res(a), Res(a)]);
                for (var i = 0; i < shape.Effects; i++) f.Events.Add(Ev(a));
                if (shape.Hits > 0)
                {
                    f.MinimumCacheHits = shape.Hits;
                    f.Paths |= SemanticPath.CacheHit;
                }
                else
                {
                    f.Paths |= SemanticPath.FreshInvocation;
                }

                f.Features.Add("cache-order-" + pattern.ToString(CultureInfo.InvariantCulture));
                return f;
            }

            case 4:
            case 5:
            {
                // Twice(x) = x + x reuses ONE supplied cell; W(y) = Twice(y) forwards it.
                var twice = g.Fresh();
                var x = g.Fresh();
                f.Decls.Add(new MDecl.Func(twice, [new MParam(x, false)], new MExpr.Add(new MExpr.Ref(x), new MExpr.Ref(x))));
                var callee = twice;
                if (kind == 5)
                {
                    var w = g.Fresh();
                    var y = g.Fresh();
                    f.Decls.Add(new MDecl.Func(w, [new MParam(y, false)], new MExpr.Call(twice, [new MExpr.Ref(y)])));
                    callee = w;
                    f.Features.Add("forwarding");
                }

                var a = g.Digit();
                f.Row = new MExpr.Call(callee, [Effect(wait, a)]);
                f.Value = Res(2 * a);
                f.Events.Add(Ev(a));
                f.Features.Add("need-cell");
                return f;
            }

            default:
            {
                // Two written calls are two cells: separate activations never share.
                var twice = g.Fresh();
                var x = g.Fresh();
                f.Decls.Add(new MDecl.Func(twice, [new MParam(x, false)], new MExpr.Add(new MExpr.Ref(x), new MExpr.Ref(x))));
                var a = g.Digit();
                f.Row = new MExpr.ListLit([new MExpr.Call(twice, [Effect(wait, a)]), new MExpr.Call(twice, [Effect(wait, a)])]);
                f.Value = new Result.ListValue([Res(2 * a), Res(2 * a)]);
                f.Events.Add(Ev(a));
                f.Events.Add(Ev(a));
                f.Features.Add("separate-activations");
                return f;
            }
        }
    }

    /// <summary>
    /// Postfix selection and value boundaries: single, multiple and empty selection from a
    /// multi-row property, from a list, explicit spread of selected values into a call, demanded
    /// selectors in order, and the documented precedence of invalid indices and failing selectors.
    /// </summary>
    private static SemanticFragment Selection(Gen g, bool failing)
    {
        var f = new SemanticFragment("select");
        f.Features.Add("select");
        var s = g.Fresh();
        var data = Enumerable.Range(0, 3).Select(_ => g.Value()).ToList();
        var fromList = g.Pick("select.receiver", 3) == 2;
        MExpr Receiver() => fromList
            ? new MExpr.ListLit(data.Select(v => (MExpr)Atom(v)).ToList())
            : new MExpr.Ref(s);
        if (!fromList) f.Decls.Add(new MDecl.Value(s, data.Select(v => (MExpr)Atom(v)).ToList()));
        else f.Features.Add("list");

        if (failing)
        {
            f.Features.Add("failure");
            switch (g.Pick("select.fail", 4))
            {
                case 0:
                    f.Row = new MExpr.Select(Receiver(), [Atom(9)]);
                    f.FailureCategory = "BadIndex";
                    return f;
                case 1:
                {
                    // Validated left to right: the out-of-range index stops before a later selector.
                    var first = g.Pick("select.first", 3);
                    f.Row = new MExpr.Select(Receiver(), [Effect(false, first), Atom(9), Effect(false, 1)]);
                    f.Events.Add("trace:" + first.ToString(CultureInfo.InvariantCulture));
                    f.FailureCategory = "BadIndex";
                    f.Paths |= SemanticPath.FirstFailureStops;
                    return f;
                }

                case 2:
                    // An explicit spread selector runs during formation, before any validation.
                    f.Row = new MExpr.Select(Receiver(), [Atom(9), new MExpr.Spread(new MExpr.Binary("/", Atom(1), Atom(0)))]);
                    f.FailureCategory = "DivByZero";
                    f.Features.Add("spread");
                    return f;
                default:
                    f.Row = new MExpr.Select(Receiver(), [new MExpr.Binary("/", Atom(1), Atom(0)), Atom(9)]);
                    f.FailureCategory = "DivByZero";
                    return f;
            }
        }

        switch (g.Pick("select.kind", 5))
        {
            case 0:
            {
                var i = g.Pick("select.index", 3);
                f.Row = new MExpr.Select(Receiver(), [Atom(i)]);
                f.Value = Res(data[i]);
                return f;
            }

            case 1:
            {
                var i = g.Pick("select.index", 3);
                var j = g.Pick("select.second", 3);
                f.Row = new MExpr.Select(Receiver(), [Atom(i), Atom(j)]);
                f.Value = new Result.SequenceValue([Res(data[i]), Res(data[j])]);
                f.Features.Add("multi-select");
                return f;
            }

            case 2:
                f.Row = new MExpr.Select(Receiver(), []);
                f.Value = new Result.SequenceValue([]);
                f.Features.Add("empty-select");
                return f;
            case 3:
            {
                // Sum2(S[i, j]*): the selected values become two supplied arguments.
                var i = g.Pick("select.index", 3);
                var j = g.Pick("select.second", 3);
                var sum = g.Fresh();
                var a = g.Fresh();
                var b = g.Fresh();
                f.Decls.Add(new MDecl.Func(sum, [new MParam(a, false), new MParam(b, false)], new MExpr.Add(new MExpr.Ref(a), new MExpr.Ref(b))));
                f.Row = new MExpr.Call(sum, [new MExpr.Spread(new MExpr.Select(Receiver(), [Atom(i), Atom(j)]))]);
                f.Value = Res(data[i] + data[j]);
                f.Features.Add("spread");
                return f;
            }

            default:
            {
                // Demanded selectors, in written order.
                var i = g.Pick("select.index", 3);
                var j = g.Pick("select.second", 3);
                f.Row = new MExpr.Select(Receiver(), [Effect(false, i), Effect(false, j)]);
                f.Value = new Result.SequenceValue([Res(data[i]), Res(data[j])]);
                f.Events.Add("trace:" + i.ToString(CultureInfo.InvariantCulture));
                f.Events.Add("trace:" + j.ToString(CultureInfo.InvariantCulture));
                f.Features.Add("multi-select");
                return f;
            }
        }
    }

    /// <summary>
    /// Loops under the current interface (<c>repeat(meta step, count)</c>, condition-first
    /// <c>while(meta step)</c>): optimized repeat and while, the zero-iteration short circuit,
    /// steps the planner deliberately declines (clause family, collector), a generic expression
    /// inside an optimized loop, a META loop over a rebuilt projection, and the documented refusals.
    /// </summary>
    private static SemanticFragment Loop(Gen g, bool failing)
    {
        var f = new SemanticFragment("loop") { IsLoop = true };
        f.Features.Add("loop");

        if (failing)
        {
            f.Features.Add("failure");
            switch (g.Pick("loop.fail", 3))
            {
                case 0:
                {
                    // Run(meta s) = s.repeat(2): the step is an EXISTING reference — the META refusal.
                    var run = g.Fresh();
                    var sp = g.Fresh();
                    f.Decls.Add(new MDecl.Func(run, [new MParam(sp, false, Meta: true)],
                        new MExpr.Dot(new MExpr.Ref(sp), "repeat", [Atom(2)])));
                    var inc = IncStep(g, f, 1, effect: null);
                    f.Row = new MExpr.Call(run, [new MExpr.Call(inc, [Atom(g.Digit())])]);
                    f.FailureCategory = "NotAnAlgorithm";
                    f.Features.Add("meta");
                    f.Features.Add("meta-refusal");
                    return f;
                }

                case 1:
                {
                    // Start = Step(0) / Start.while: no implicit provenance.
                    var step = WhileStep(g, f, 3);
                    var start = g.Fresh();
                    f.Decls.Add(new MDecl.Value(start, [new MExpr.Call(step, [Atom(0)])]));
                    f.Row = new MExpr.Dot(new MExpr.Ref(start), "while", null);
                    f.FailureCategory = "NotAnAlgorithm";
                    f.Features.Add("meta-refusal");
                    return f;
                }

                default:
                {
                    // A non-Boolean continuation flag (read FIRST, before any transition row).
                    var step = g.Fresh();
                    var x = g.Fresh();
                    f.Decls.Add(new MDecl.Func(step, [new MParam(x, false)],
                        new MExpr.Brace(new MScope([], [new MExpr.Add(new MExpr.Ref(x), Atom(1)), new MExpr.Add(new MExpr.Ref(x), Atom(2))]))));
                    f.Row = new MExpr.Dot(new MExpr.Call(step, [Atom(0)]), "while", null);
                    f.FailureCategory = "TypeMismatch";
                    return f;
                }
            }
        }

        var start0 = g.Digit();
        switch (g.Pick("loop.kind", 6))
        {
            case 0:
            {
                var c = 1 + g.Pick("loop.increment", 3);
                var n = 1 + g.Pick("loop.count", 4);
                var inc = IncStep(g, f, c, effect: null);
                f.Row = RepeatOf(g, new MExpr.Call(inc, [Atom(start0)]), n);
                f.Value = Res(start0 + c * n);
                f.Paths |= SemanticPath.OptimizedLoop;
                f.Features.Add("repeat");
                return f;
            }

            case 1:
            {
                var inc = IncStep(g, f, 1, effect: null);
                f.Row = RepeatOf(g, new MExpr.Call(inc, [Atom(start0)]), 0);
                f.Value = Res(start0);
                f.Paths |= SemanticPath.LoopShortCircuit;
                f.Features.Add("repeat");
                f.Features.Add("zero-iterations");
                return f;
            }

            case 2:
            {
                // Step(x) = x + 1, x < m from 0 completes at m (m = 0: zero accepted transitions).
                var m = g.Pick("loop.bound", 5);
                var step = WhileStep(g, f, m);
                f.Row = new MExpr.Dot(new MExpr.Call(step, [Atom(0)]), "while", null);
                f.Value = Res(m);
                f.Paths |= SemanticPath.OptimizedLoop;
                f.Features.Add("while");
                if (m == 0) f.Features.Add("zero-iterations");
                return f;
            }

            case 3:
            {
                // A step the planner declines: a clause family, or a collecting step.
                var n = 1 + g.Pick("loop.count", 4);
                Sym step;
                if (g.Pick("loop.fallbackShape", 2) == 0)
                {
                    step = g.Fresh();
                    var x = g.Fresh();
                    f.Decls.Add(new MDecl.Family(step,
                    [
                        new MClause(new MPattern.Literal(0m), Atom(100)),
                        new MClause(new MPattern.Binder(x), new MExpr.Add(new MExpr.Ref(x), Atom(1))),
                    ]));
                    f.Features.Add("clause-family");
                }
                else
                {
                    step = g.Fresh();
                    var xs = g.Fresh();
                    f.Decls.Add(new MDecl.Func(step, [new MParam(xs, true)],
                        new MExpr.Add(new MExpr.Select(new MExpr.Ref(xs), [Atom(0)]), Atom(1))));
                    f.Features.Add("collect");
                }

                f.Row = RepeatOf(g, new MExpr.Call(step, [Atom(start0)]), n);
                f.Value = Res(start0 + n);
                f.Paths |= SemanticPath.LoopFallback;
                f.Features.Add("repeat");
                return f;
            }

            case 4:
            {
                // Inc(x) = trace(x) + 1: a host call is a generic expression inside the planned loop.
                var n = 1 + g.Pick("loop.count", 4);
                var wait = g.Chance("loop.wait", 40);
                var inc = IncStep(g, f, 1, effect: wait ? "wait" : "trace");
                f.Row = RepeatOf(g, new MExpr.Call(inc, [Atom(start0)]), n);
                f.Value = Res(start0 + n);
                for (var i = 0; i < n; i++) f.Events.Add((wait ? "wait:" : "trace:") + (start0 + i).ToString(CultureInfo.InvariantCulture));
                f.Paths |= SemanticPath.GenericInsideOptimizedLoop;
                f.Features.Add("repeat");
                if (wait) f.Features.Add("async");
                return f;
            }

            default:
            {
                // Loop(meta op) = op.Algorithm(op.Arguments*).repeat(n) / .while: META composition.
                var loop = g.Fresh();
                var op = g.Fresh();
                var rebuilt = new MExpr.Dot(new MExpr.Ref(op), "Algorithm",
                    [new MExpr.Spread(new MExpr.Dot(new MExpr.Ref(op), "Arguments", null))]);
                f.Features.Add("meta");
                if (g.Pick("loop.metaKind", 2) == 0)
                {
                    var n = 1 + g.Pick("loop.count", 4);
                    f.Decls.Add(new MDecl.Func(loop, [new MParam(op, false, Meta: true)], new MExpr.Dot(rebuilt, "repeat", [Atom(n)])));
                    var inc = IncStep(g, f, 1, effect: null);
                    f.Row = new MExpr.Call(loop, [new MExpr.Call(inc, [Atom(start0)])]);
                    f.Value = Res(start0 + n);
                    f.Features.Add("repeat");
                }
                else
                {
                    var m = 1 + g.Pick("loop.bound", 4);
                    f.Decls.Add(new MDecl.Func(loop, [new MParam(op, false, Meta: true)], new MExpr.Dot(rebuilt, "while", null)));
                    var step = WhileStep(g, f, m);
                    f.Row = new MExpr.Call(loop, [new MExpr.Call(step, [Atom(0)])]);
                    f.Value = Res(m);
                    f.Features.Add("while");
                }

                f.Paths |= SemanticPath.OptimizedLoop;
                return f;
            }
        }
    }

    /// <summary><c>Inc(x) = x + c</c>, or <c>Inc(x) = effect(x) + c</c>.</summary>
    private static Sym IncStep(Gen g, SemanticFragment f, int c, string? effect)
    {
        var inc = g.Fresh();
        var x = g.Fresh();
        MExpr operand = effect is null ? new MExpr.Ref(x) : new MExpr.Prim(effect, [new MExpr.Ref(x)]);
        f.Decls.Add(new MDecl.Func(inc, [new MParam(x, false)], new MExpr.Add(operand, Atom(c))));
        return inc;
    }

    /// <summary><c>Step(x) = { x + 1, x &lt; m }</c>: the last row is the continuation flag.</summary>
    private static Sym WhileStep(Gen g, SemanticFragment f, int bound)
    {
        var step = g.Fresh();
        var x = g.Fresh();
        f.Decls.Add(new MDecl.Func(step, [new MParam(x, false)], new MExpr.Brace(new MScope([],
            [new MExpr.Add(new MExpr.Ref(x), Atom(1)), new MExpr.Binary("<", new MExpr.Ref(x), Atom(bound))]))));
        return step;
    }

    /// <summary>The plain or the dot spelling of <c>repeat</c>; both are the ordinary call rules.</summary>
    private static MExpr RepeatOf(Gen g, MExpr captured, int count)
    {
        if (g.Pick("loop.spelling", 2) == 0) return new MExpr.Dot(captured, "repeat", [Atom(count)]);
        return new MExpr.Prim("repeat", [captured, Atom(count)]);
    }

    /// <summary>
    /// Competing failures: operand order between two distinguishable failures, a dead failing
    /// argument, cardinality before demand, a repeated-name binding conflict, the first failure in
    /// a list stopping later effects, and a dead failing branch.
    /// </summary>
    private static SemanticFragment CompetingFailure(Gen g, bool failing)
    {
        var f = new SemanticFragment("failure");
        f.Features.Add("failure");

        if (!failing)
        {
            switch (g.Pick("failure.dead", 2))
            {
                case 0:
                {
                    // First(a, b) = a: the failing second argument is never demanded.
                    var first = g.Fresh();
                    var a = g.Fresh();
                    var b = g.Fresh();
                    f.Decls.Add(new MDecl.Func(first, [new MParam(a, false), new MParam(b, false)], new MExpr.Ref(a)));
                    var v = g.Digit();
                    f.Row = new MExpr.Call(first, [Effect(false, v), new MExpr.Binary("/", Effect(false, TripwireValue), Atom(0))]);
                    f.Value = Res(v);
                    f.Events.Add("trace:" + v.ToString(CultureInfo.InvariantCulture));
                    break;
                }

                default:
                {
                    var v = g.Digit();
                    f.Row = new MExpr.If(new MExpr.Bool(true), Atom(v), new MExpr.Binary("/", Effect(false, TripwireValue), Atom(0)));
                    f.Value = Res(v);
                    f.Features.Add("if");
                    break;
                }
            }

            f.Paths |= SemanticPath.DeadComputationUntouched;
            return f;
        }

        switch (g.Pick("failure.kind", 5))
        {
            case 0:
            case 1:
            {
                // Two(a, b) = a + b  (or b + a) over a division failure and an index failure:
                // the operand demanded FIRST decides the reported error.
                var two = g.Fresh();
                var a = g.Fresh();
                var b = g.Fresh();
                var swapped = g.Pick("failure.order", 2) == 1;
                f.Decls.Add(new MDecl.Func(two, [new MParam(a, false), new MParam(b, false)], swapped
                    ? new MExpr.Add(new MExpr.Ref(b), new MExpr.Ref(a))
                    : new MExpr.Add(new MExpr.Ref(a), new MExpr.Ref(b))));
                var va = g.Digit();
                var vb = g.Digit();
                f.Row = new MExpr.Call(two,
                [
                    new MExpr.Binary("/", Effect(false, va), Atom(0)),
                    new MExpr.Select(new MExpr.ListLit([Effect(false, vb)]), [Atom(5)]),
                ]);
                f.Events.Add("trace:" + (swapped ? vb : va).ToString(CultureInfo.InvariantCulture));
                f.FailureCategory = swapped ? "BadIndex" : "DivByZero";
                f.Features.Add(swapped ? "operand-order-swapped" : "operand-order");
                return f;
            }

            case 2:
            {
                var two = g.Fresh();
                var a = g.Fresh();
                var b = g.Fresh();
                f.Decls.Add(new MDecl.Func(two, [new MParam(a, false), new MParam(b, false)], new MExpr.Add(new MExpr.Ref(a), new MExpr.Ref(b))));
                f.Row = new MExpr.Call(two, [Effect(false, g.Digit()), Effect(false, g.Digit()), Effect(false, g.Digit())]);
                f.FailureCategory = "ArityMismatch";
                f.Paths |= SemanticPath.CardinalityBeforeDemand;
                return f;
            }

            case 3:
            {
                // A list's first failing element ends it: later elements never run.
                var a = g.Digit();
                var b = g.Digit();
                f.Row = new MExpr.ListLit([Effect(false, a), new MExpr.Binary("/", Atom(1), Atom(0)), Effect(false, b)]);
                f.Events.Add("trace:" + a.ToString(CultureInfo.InvariantCulture));
                f.FailureCategory = "DivByZero";
                f.Paths |= SemanticPath.FirstFailureStops;
                f.Features.Add("list");
                return f;
            }

            default:
            {
                // A live failing branch: the dead one is the tripwire.
                f.Row = new MExpr.If(new MExpr.Bool(false), Effect(false, TripwireValue), new MExpr.Binary("/", Atom(1), Atom(0)));
                f.FailureCategory = "DivByZero";
                f.Paths |= SemanticPath.DeadComputationUntouched;
                f.Features.Add("if");
                return f;
            }
        }
    }

    /// <summary>
    /// Genuinely asynchronous host work: memoized waited cells, cached waited properties, waits
    /// in written order, a waited META argument view, and a failure after a completed wait.
    /// </summary>
    private static SemanticFragment Async(Gen g, bool failing)
    {
        var f = new SemanticFragment("async");
        f.Features.Add("async");

        if (failing)
        {
            var a = g.Digit();
            f.Row = new MExpr.ListLit([Effect(true, a), new MExpr.Binary("/", Atom(1), Atom(0)), Effect(true, g.Digit())]);
            f.Events.Add("wait:" + a.ToString(CultureInfo.InvariantCulture));
            f.FailureCategory = "DivByZero";
            f.Paths |= SemanticPath.FirstFailureStops;
            f.Features.Add("failure");
            return f;
        }

        switch (g.Pick("async.kind", 4))
        {
            case 0:
            {
                var twice = g.Fresh();
                var x = g.Fresh();
                f.Decls.Add(new MDecl.Func(twice, [new MParam(x, false)], new MExpr.Add(new MExpr.Ref(x), new MExpr.Ref(x))));
                var a = g.Digit();
                f.Row = new MExpr.Call(twice, [Effect(true, a)]);
                f.Value = Res(2 * a);
                f.Events.Add("wait:" + a.ToString(CultureInfo.InvariantCulture));
                f.Features.Add("need-cell");
                return f;
            }

            case 1:
            {
                var p = g.Fresh();
                var a = g.Digit();
                f.Decls.Add(new MDecl.Value(p, [Effect(true, a)]));
                f.Row = new MExpr.ListLit([new MExpr.Ref(p), new MExpr.Ref(p)]);
                f.Value = new Result.ListValue([Res(a), Res(a)]);
                f.Events.Add("wait:" + a.ToString(CultureInfo.InvariantCulture));
                f.MinimumCacheHits = 1;
                f.Paths |= SemanticPath.CacheHit;
                f.Features.Add("cache");
                return f;
            }

            case 2:
            {
                var a = g.Digit();
                var b = g.Digit();
                f.Row = new MExpr.ListLit([Effect(true, a), Effect(true, b)]);
                f.Value = new Result.ListValue([Res(a), Res(b)]);
                f.Events.Add("wait:" + a.ToString(CultureInfo.InvariantCulture));
                f.Events.Add("wait:" + b.ToString(CultureInfo.InvariantCulture));
                f.Features.Add("list");
                return f;
            }

            default:
            {
                // A captured call over waited arguments: select one cell, then invoke.
                var cap = MetaRoute(g, f, 0);
                var t = g.Fresh();
                var a = g.Fresh();
                var b = g.Fresh();
                f.Decls.Add(new MDecl.Func(t, [new MParam(a, false), new MParam(b, false)], Weighted([new MExpr.Ref(a), new MExpr.Ref(b)])));
                var v1 = g.Digit();
                var v2 = g.Digit();
                var r = g.Fresh();
                f.Decls.Add(new MDecl.Value(r, [new MExpr.Call(cap, [new MExpr.Call(t, [Effect(true, v1), Effect(true, v2)])])]));
                f.Row = new MExpr.ListLit(
                [
                    new MExpr.Select(new MExpr.Dot(new MExpr.Ref(r), "Arguments", null), [Atom(1)]),
                    new MExpr.Dot(new MExpr.Ref(r), "Invoke", []),
                ]);
                f.Value = new Result.ListValue([Res(v2), Res(WeightedValue([v1, v2]))]);
                f.Events.Add("wait:" + v2.ToString(CultureInfo.InvariantCulture));
                f.Events.Add("wait:" + v1.ToString(CultureInfo.InvariantCulture));
                f.Features.Add("meta");
                return f;
            }
        }
    }

    // ── Contexts ────────────────────────────────────────────────────────────

    /// <summary>A bounded two-level pattern: ([a, *rest], z) or [(a, *rest), z].
    /// Delimiters, symbols and collectors remain structural model data, not source fragments.</summary>
    internal static SemanticFragment NestedPattern(Gen g, bool outerList, bool failing)
    {
        var f = new SemanticFragment("collect");
        f.Features.UnionWith(["collect", "sequence-pattern", "list-pattern", "nested-pattern"]);
        var function = g.Fresh();
        var a = g.Fresh();
        var rest = g.Fresh();
        var z = g.Fresh();
        var innerPattern = new MPattern.Structure(!outerList, [new MPattern.Binder(a), new MPattern.Collecting(rest)]);
        var pattern = new MPattern.Structure(outerList, [innerPattern, new MPattern.Binder(z)]);
        f.Decls.Add(new MDecl.Family(function, [new MClause(pattern,
            new MExpr.ListLit([new MExpr.Ref(a), new MExpr.Prim("count", [new MExpr.Ref(rest)]), new MExpr.Ref(z)]))]));
        var values = Enumerable.Range(0, 2 + g.Pick("nested.width", 3)).Select(_ => g.Digit()).ToList();
        var tail = g.Digit();
        var data = new List<MExpr>();
        if (!failing)
        {
            foreach (var value in values)
            {
                var wait = g.Chance("nested.wait", 50);
                data.Add(Effect(wait, value));
                f.Events.Add((wait ? "wait:" : "trace:") + value.ToString(CultureInfo.InvariantCulture));
                if (wait) f.Features.Add("async");
            }
        }
        MExpr innerValue = failing ? Atom(99)
            : outerList ? new MExpr.Group(data) : new MExpr.ListLit(data);
        MExpr[] items = [innerValue, Effect(false, tail)];
        f.Row = new MExpr.Call(function, [outerList ? new MExpr.ListLit(items) : new MExpr.Group(items)]);
        f.Events.Add("trace:" + tail.ToString(CultureInfo.InvariantCulture));
        if (failing)
        {
            f.FailureCategory = "TypeMismatch";
            f.Features.Add("failure");
        }
        else f.Value = new Result.ListValue([Res(values[0]), Res(values.Count - 1), Res(tail)]);
        return f;
    }

    /// <summary>Independent condition-first loop anchors: a false or invalid flag never demands
    /// the transition, and accepted transitions each perform exactly one gated host operation.</summary>
    internal static SemanticFragment WhileGuard(Gen g, int variant)
    {
        var f = new SemanticFragment("loop") { IsLoop = true };
        f.Features.UnionWith(["loop", "while", "condition-first"]);
        var step = g.Fresh();
        var x = g.Fresh();
        var transition = variant == 1
            ? (MExpr)new MExpr.Prim("wait", [new MExpr.Add(new MExpr.Ref(x), Atom(1))])
            : new MExpr.Binary("/", Effect(false, TripwireValue), Atom(0));
        var flag = variant == 2 ? (MExpr)Atom(42)
            : new MExpr.Binary("<", new MExpr.Ref(x), Atom(variant == 1 ? 2 : 0));
        f.Decls.Add(new MDecl.Func(step, [new MParam(x, false)],
            new MExpr.Brace(new MScope([], [transition, flag]))));
        f.Row = new MExpr.Dot(new MExpr.Call(step, [Atom(0)]), "while", null);
        if (variant == 2)
        {
            f.FailureCategory = "TypeMismatch";
            f.Features.Add("failure");
        }
        else f.Value = Res(variant == 1 ? 2 : 0);
        if (variant == 1)
        {
            f.Events.AddRange(["wait:1", "wait:2"]);
            f.Features.Add("async");
        }
        else f.Paths |= SemanticPath.DeadComputationUntouched;
        return f;
    }

    /// <summary>Places the fragment's row in a consumer whose effect on value and events is known.</summary>
    internal static void ApplyContext(Gen g, SemanticFragment f, int context)
    {
        switch (context)
        {
            case 0:
                return;
            case 1:
                f.Row = new MExpr.ListLit([f.Row]);
                if (f.Value is { } listed) f.Value = new Result.ListValue([listed]);
                break;
            case 2:
                f.Row = new MExpr.If(new MExpr.Bool(true), f.Row, Effect(false, TripwireValue));
                f.Paths |= SemanticPath.DeadComputationUntouched;
                break;
            case 3:
                f.Row = new MExpr.If(new MExpr.Bool(false), Effect(false, TripwireValue), f.Row);
                f.Paths |= SemanticPath.DeadComputationUntouched;
                break;
            case 4:
            {
                var q = g.Fresh();
                f.Decls.Add(new MDecl.Value(q, [f.Row]));
                f.Row = new MExpr.Ref(q);
                break;
            }

            case 5:
            {
                // [Q, Q]: one evaluation, a real cache hit for the second read.
                var q = g.Fresh();
                f.Decls.Add(new MDecl.Value(q, [f.Row]));
                f.Row = new MExpr.ListLit([new MExpr.Ref(q), new MExpr.Ref(q)]);
                if (f.Value is { } doubled)
                {
                    f.Value = new Result.ListValue([doubled, doubled]);
                    f.MinimumCacheHits += 1;
                    f.Paths |= SemanticPath.CacheHit;
                }

                break;
            }

            case 6:
            {
                var id = g.Fresh();
                var x = g.Fresh();
                f.Decls.Add(new MDecl.Func(id, [new MParam(x, false)], new MExpr.Ref(x)));
                f.Row = new MExpr.Call(id, [f.Row]);
                break;
            }

            default:
            {
                var local = g.Fresh();
                f.Row = new MExpr.Brace(new MScope([new MDecl.Value(local, [Atom(0)])], [f.Row]));
                break;
            }
        }

        f.Features.Add("ctx-" + Contexts[context]);
    }

    /// <summary>
    /// The declarations of one invalid front-end production, added to an otherwise valid program.
    /// These deliberately violate the naming model (a duplicate, a collision, an undeclared
    /// reference), so an invalid case is never passed through binding validation.
    /// </summary>
    internal static IReadOnlyList<MDecl> InvalidDeclarations(Gen g, int production)
    {
        switch (production)
        {
            case 0:
            {
                var fn = g.Fresh();
                var x = g.Fresh();
                return [new MDecl.Func(fn, [new MParam(x, Collecting: true, Meta: true)], new MExpr.Ref(x))];
            }

            case 1:
            {
                // The second declaration shares the first one's rendered name in the same scope.
                var first = g.Fresh();
                return [new MDecl.Value(first, [Atom(1)]), new MDecl.Value(g.ShadowOf(first), [Atom(2)])];
            }

            case 2:
            {
                var fn = g.Fresh();
                var x = g.Fresh();
                var shadow = g.ShadowOf(x);
                return [new MDecl.Func(fn, [new MParam(x, false)],
                    new MExpr.Brace(new MScope([new MDecl.Value(shadow, [Atom(1)])], [new MExpr.Ref(shadow)])))];
            }

            default:
            {
                var fn = g.Fresh();
                var x = g.Fresh();
                var undeclared = g.Fresh();
                return [new MDecl.Func(fn, [new MParam(x, false)], new MExpr.Add(new MExpr.Ref(x), new MExpr.Ref(undeclared)))];
            }
        }
    }

    // ── Small constructors and expectation arithmetic ──────────────────────

    internal static MExpr.Atom Atom(int value) => new(value);

    internal static Result.Atom Res(int value) => new(value);

    /// <summary><c>trace(v)</c> or <c>wait(v)</c>.</summary>
    internal static MExpr Effect(bool wait, int value) => new MExpr.Prim(wait ? "wait" : "trace", [Atom(value)]);

    /// <summary><c>p1 * 10^(k-1) + … + pk</c>, evaluated (and demanded) left to right.</summary>
    private static MExpr Weighted(IReadOnlyList<MExpr> operands)
    {
        var k = operands.Count;
        MExpr? sum = null;
        for (var i = 0; i < k; i++)
        {
            var weight = (int)Math.Pow(10, k - 1 - i);
            MExpr term = weight == 1 ? operands[i] : new MExpr.Binary("*", operands[i], Atom(weight));
            sum = sum is null ? term : new MExpr.Add(sum, term);
        }

        return sum!;
    }

    private static int WeightedValue(IReadOnlyList<int> values)
    {
        var sum = 0;
        foreach (var v in values) sum = (sum * 10) + v;
        return sum;
    }

    /// <summary>Per-program generation state: names, distinct constants, and the decision source.</summary>
    internal sealed class Gen(SemanticChooser chooser)
    {
        private readonly ProgramBuilder _builder = new();
        private int _digit;
        private int _value = 10;

        public int Pick(string dimension, int count) => chooser.Pick(dimension, count);

        public bool Chance(string dimension, int percent) => chooser.Chance(dimension, percent);

        public Sym Fresh() => _builder.NewSym();

        public Sym ShadowOf(Sym outer) => _builder.NewShadowOf(outer);

        /// <summary>A digit 1..9, cycling, so positional weights stay exact and adjacent arguments differ.</summary>
        public int Digit() => (_digit++ % 9) + 1;

        /// <summary>A program-unique two-digit constant.</summary>
        public int Value() => ++_value;

        public StructuralProgram Finish(MScope root) => _builder.Finish(root);
    }
}
