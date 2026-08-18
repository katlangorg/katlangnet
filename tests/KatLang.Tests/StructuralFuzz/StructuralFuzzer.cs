namespace KatLang.Tests.StructuralFuzz;

/// <summary>
/// One generated base case: the program (model + names + absolute anchors),
/// a stable id, and the structural features it exercises (for pairwise
/// interaction accounting). Construction validates the naming map, so a
/// generator bug that would change binding identity fails at generation time,
/// not as a mysterious semantic diff.
/// </summary>
public sealed record GeneratedCase(string CaseId, StructuralProgram Program, IReadOnlyList<string> Features)
{
    public static GeneratedCase Create(string caseId, StructuralProgram program, params string[] features)
    {
        program.ValidateNaming();
        return new GeneratedCase(caseId, program, features);
    }

    public override string ToString() => CaseId;
}

/// <summary>SplitMix64 — the same tiny platform-independent PRNG convention as
/// <c>AstGraphFuzzer</c>, so seeds are stable across machines and runtimes.</summary>
public struct SplitMix64(ulong seed)
{
    private ulong _state = seed;

    public ulong Next()
    {
        _state += 0x9E3779B97F4A7C15UL;
        var z = _state;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
        return z ^ (z >> 31);
    }

    public int Next(int exclusiveMax) => (int)(Next() % (ulong)exclusiveMax);

    public bool Chance(int percent) => Next(100) < percent;

    public T Pick<T>(IReadOnlyList<T> items) => items[Next(items.Count)];
}

/// <summary>
/// Mutable program assembler: allocates symbols, assigns names (unique by
/// default; SAME name on purpose for shadow pairs), tracks per-program
/// sentinel/tripwire pools, and records the model-derived absolute anchors
/// (which sentinel atoms MUST / MUST NOT appear in the observation — the
/// generator knows the selected branch/clause by construction, which is what
/// keeps metamorphic pairs from being blind to uniform breaks).
/// </summary>
internal sealed class ProgramBuilder
{
    private readonly Dictionary<Sym, string> _names = [];
    private readonly List<decimal> _mustContain = [];
    private readonly List<decimal> _mustNotContain = [];
    private int _nextSym;
    private int _nextName;
    private int _sentinel;
    private int _tripwire;

    public Sym NewSym(string? sameNameAs = null)
    {
        var sym = new Sym(_nextSym++);
        _names[sym] = sameNameAs ?? $"v{++_nextName}";
        return sym;
    }

    /// <summary>Deliberate shadow: the new symbol renders with EXACTLY the same
    /// name as the given outer symbol.</summary>
    public Sym NewShadowOf(Sym outer) => NewSym(_names[outer]);

    public string NameOf(Sym sym) => _names[sym];

    public decimal NextSentinel()
    {
        var value = StructuralProgram.FirstSentinel + _sentinel++;
        if (_sentinel >= 49)
            throw new InvalidOperationException("sentinel pool exhausted — generated program too large");
        return value;
    }

    public decimal NextTripwireAtom() => StructuralProgram.FirstTripwire + 40 + (_tripwire++ % 20);

    public void ExpectContains(decimal sentinel) => _mustContain.Add(sentinel);

    public void ExpectAbsent(decimal sentinel) => _mustNotContain.Add(sentinel);

    public StructuralProgram Finish(MScope root)
        => new(root, new Dictionary<Sym, string>(_names), _mustContain.ToList(), _mustNotContain.ToList());
}

/// <summary>
/// The deterministic corpus: a bounded-exhaustive tiny tier (systematic
/// structure families) plus a seeded composed tier (SplitMix64-driven larger
/// combinations). Both tiers are pure functions — enumerating the corpus never
/// evaluates anything, so meta-tests can re-enumerate it cheaply for coverage
/// accounting.
/// </summary>
public static class StructuralCorpus
{
    /// <summary>Fixed CI seed set. Reproducing one failing case never requires
    /// rerunning the corpus: the case id carries the seed and index.</summary>
    public static IReadOnlyList<ulong> Seeds { get; } =
        Enumerable.Range(1, 24).Select(i => 0x5EED_0000UL + (ulong)i).ToList();

    public static IReadOnlyList<GeneratedCase> All()
        => ExhaustiveCases().Concat(SeededCases()).ToList();

    // ── Bounded-exhaustive tiny structures ──────────────────────────────────

    public static IReadOnlyList<GeneratedCase> ExhaustiveCases()
    {
        var cases = new List<GeneratedCase>();
        AddShadowChainCases(cases);
        AddConditionalCases(cases);
        AddFamilyCases(cases);
        AddParameterCases(cases);
        AddSequencePatternCases(cases);
        AddDeconstructionCases(cases);
        AddDeltaFocusCases(cases);
        AddZeroOutputCases(cases);
        AddInteractionCases(cases);
        return cases;
    }

    /// <summary>Shadow chains: depth ≤ 2 nested braces, every shadow-mask and
    /// reference-target combination that the scope model permits.</summary>
    private static void AddShadowChainCases(List<GeneratedCase> cases)
    {
        var index = 0;
        foreach (var shadowLevel1 in new[] { false, true })
        {
            foreach (var shadowLevel2 in new[] { false, true })
            {
                foreach (var producerOuter in new[] { false, true })
                {
                    var b = new ProgramBuilder();
                    var outer = b.NewSym("x");
                    var outerRows = producerOuter
                        ? new List<MExpr> { new MExpr.Atom(1m), new MExpr.Atom(2m) }
                        : [new MExpr.Atom(1m)];

                    var level1 = shadowLevel1 ? b.NewShadowOf(outer) : b.NewSym();
                    var level2 = shadowLevel2 ? b.NewShadowOf(outer) : b.NewSym();

                    // Innermost brace references the NEAREST visible "x"-named
                    // symbol; the generator states that target explicitly.
                    var innerTarget = shadowLevel2 ? level2 : shadowLevel1 ? level1 : outer;

                    var inner = new MExpr.Brace(new MScope(
                        [new MDecl.Value(level2, [new MExpr.Atom(7m)])],
                        [new MExpr.Ref(innerTarget), new MExpr.Ref(level2)]));
                    var middle = new MExpr.Brace(new MScope(
                        [new MDecl.Value(level1, [new MExpr.Atom(2m)])],
                        [new MExpr.Ref(level1), inner]));

                    var root = new MScope(
                        [new MDecl.Value(outer, outerRows)],
                        [new MExpr.Ref(outer), middle]);

                    cases.Add(GeneratedCase.Create(
                        $"exh/shadow/{index++:000}",
                        b.Finish(root),
                        "shadow", "brace", producerOuter ? "multiOut" : "scalar"));
                }
            }
        }
    }

    /// <summary>Conditionals with literal conditions in three evaluated
    /// placements, sentinel-anchored: the generator KNOWS the selected branch.</summary>
    private static void AddConditionalCases(List<GeneratedCase> cases)
    {
        var index = 0;
        foreach (var cond in new[] { 0m, 1m, 2m })
        {
            foreach (var placement in new[] { "row", "value", "func" })
            {
                foreach (var braceBranches in new[] { false, true })
                {
                    var b = new ProgramBuilder();
                    var thenSentinel = b.NextSentinel();
                    var elseSentinel = b.NextSentinel();
                    var condTrue = cond != 0m;
                    b.ExpectContains(condTrue ? thenSentinel : elseSentinel);
                    b.ExpectAbsent(condTrue ? elseSentinel : thenSentinel);

                    MExpr Branch(decimal sentinel, string name)
                    {
                        if (!braceBranches)
                            return new MExpr.Atom(sentinel);
                        var local = b.NewSym(name); // both branches use the SAME local name
                        return new MExpr.Brace(new MScope(
                            [new MDecl.Value(local, [new MExpr.Atom(sentinel)])],
                            [new MExpr.Ref(local)]));
                    }

                    var ifExpr = new MExpr.If(new MExpr.Atom(cond), Branch(thenSentinel, "loc"), Branch(elseSentinel, "loc"));

                    MScope root;
                    switch (placement)
                    {
                        case "row":
                            root = new MScope([], [ifExpr]);
                            break;
                        case "value":
                        {
                            var holder = b.NewSym();
                            root = new MScope([new MDecl.Value(holder, [ifExpr])], [new MExpr.Ref(holder)]);
                            break;
                        }

                        default:
                        {
                            var func = b.NewSym();
                            var param = b.NewSym();
                            root = new MScope(
                                [new MDecl.Func(func, [new MParam(param, Collecting: false)], new MExpr.Add(new MExpr.Ref(param), ifExpr))],
                                [new MExpr.Call(func, [new MExpr.Atom(0m)])]);
                            break;
                        }
                    }

                    cases.Add(GeneratedCase.Create(
                        $"exh/if/{index++:000}",
                        b.Finish(root),
                        "if", braceBranches ? "brace" : "scalar", placement == "func" ? "userCall" : placement));
                }
            }
        }
    }

    /// <summary>Clause families: literal sets × catch-all presence × call
    /// targets, each clause body a distinct sentinel — the matched clause is
    /// model knowledge and anchors the observation absolutely.</summary>
    private static void AddFamilyCases(List<GeneratedCase> cases)
    {
        var index = 0;
        foreach (var withCatchAll in new[] { false, true })
        {
            foreach (var literals in new[] { new[] { 0m, 1m }, new[] { 0m, 1m, 2m } })
            {
                foreach (var callChoice in new[] { "firstLiteral", "lastLiteral", "catchAll" })
                {
                    if (callChoice == "catchAll" && !withCatchAll)
                        continue;

                    foreach (var binderShadow in new[] { false, true })
                    {
                        if (binderShadow && !withCatchAll)
                            continue;

                        var b = new ProgramBuilder();
                        var outer = b.NewSym("s");
                        var family = b.NewSym();

                        var clauses = new List<MClause>();
                        var sentinels = new List<decimal>();
                        foreach (var literal in literals)
                        {
                            var sentinel = b.NextSentinel();
                            sentinels.Add(sentinel);
                            clauses.Add(new MClause(new MPattern.Literal(literal), new MExpr.Atom(sentinel)));
                        }

                        decimal? catchAllSentinel = null;
                        if (withCatchAll)
                        {
                            var binder = binderShadow ? b.NewShadowOf(outer) : b.NewSym();
                            catchAllSentinel = b.NextSentinel();
                            // Body uses the binder AND keeps the sentinel as its
                            // own atom (a group, not a sum — arithmetic would
                            // fold the sentinel token out of the observation).
                            clauses.Add(new MClause(
                                new MPattern.Binder(binder),
                                new MExpr.Group([new MExpr.Ref(binder), new MExpr.Atom(catchAllSentinel.Value)])));
                        }

                        var callArg = callChoice switch
                        {
                            "firstLiteral" => literals[0],
                            "lastLiteral" => literals[^1],
                            _ => 7m, // matches no literal → catch-all
                        };

                        var matchedIndex = callChoice switch
                        {
                            "firstLiteral" => 0,
                            "lastLiteral" => literals.Length - 1,
                            _ => -1,
                        };

                        if (matchedIndex >= 0)
                        {
                            b.ExpectContains(sentinels[matchedIndex]);
                            foreach (var (sentinel, i) in sentinels.Select((s, i) => (s, i)))
                            {
                                if (i != matchedIndex)
                                    b.ExpectAbsent(sentinel);
                            }
                        }
                        else
                        {
                            b.ExpectContains(catchAllSentinel!.Value);
                            foreach (var sentinel in sentinels)
                                b.ExpectAbsent(sentinel);
                        }

                        var root = new MScope(
                            [new MDecl.Value(outer, [new MExpr.Atom(2m)]), new MDecl.Family(family, clauses)],
                            [new MExpr.Call(family, [new MExpr.Atom(callArg)]), new MExpr.Ref(outer)]);

                        cases.Add(GeneratedCase.Create(
                            $"exh/family/{index++:000}",
                            b.Finish(root),
                            "family", withCatchAll ? "catchAll" : "literalOnly", binderShadow ? "shadow" : "plain"));
                    }
                }
            }
        }
    }

    /// <summary>Flat parameter lists: fixed/collecting/mixed, spread-fed calls,
    /// and parameter names that shadow outer declarations.</summary>
    private static void AddParameterCases(List<GeneratedCase> cases)
    {
        var index = 0;
        foreach (var shape in new[] { "fixed1", "fixed2", "collecting", "mixedFront", "mixedBoth" })
        {
            foreach (var paramShadow in new[] { false, true })
            {
                foreach (var spreadCall in new[] { false, true })
                {
                    // The 2-item spread supply cannot satisfy a single fixed
                    // parameter (spread slots obey ordinary arity).
                    if (spreadCall && shape == "fixed1")
                        continue;

                    var b = new ProgramBuilder();
                    var outer = b.NewSym("s");
                    var producer = b.NewSym();
                    var func = b.NewSym();

                    var params_ = new List<MParam>();
                    MExpr body;
                    switch (shape)
                    {
                        case "fixed1":
                        {
                            var a = paramShadow ? b.NewShadowOf(outer) : b.NewSym();
                            params_.Add(new(a, false));
                            body = new MExpr.Add(new MExpr.Ref(a), new MExpr.Atom(1m));
                            break;
                        }

                        case "fixed2":
                        {
                            var a = paramShadow ? b.NewShadowOf(outer) : b.NewSym();
                            var c = b.NewSym();
                            params_.Add(new(a, false));
                            params_.Add(new(c, false));
                            body = new MExpr.Add(new MExpr.Ref(a), new MExpr.Ref(c));
                            break;
                        }

                        case "collecting":
                        {
                            var rest = paramShadow ? b.NewShadowOf(outer) : b.NewSym();
                            params_.Add(new(rest, true));
                            body = new MExpr.Ref(rest); // the collected exact list
                            break;
                        }

                        case "mixedFront":
                        {
                            var a = b.NewSym();
                            var rest = paramShadow ? b.NewShadowOf(outer) : b.NewSym();
                            params_.Add(new(a, false));
                            params_.Add(new(rest, true));
                            body = new MExpr.Group([new MExpr.Ref(a), new MExpr.Ref(rest)]);
                            break;
                        }

                        default:
                        {
                            var a = b.NewSym();
                            var rest = b.NewSym();
                            var z = paramShadow ? b.NewShadowOf(outer) : b.NewSym();
                            params_.Add(new(a, false));
                            params_.Add(new(rest, true));
                            params_.Add(new(z, false));
                            body = new MExpr.Group([new MExpr.Ref(a), new MExpr.Ref(z)]);
                            break;
                        }
                    }

                    var minArity = params_.Count(p => !p.Collecting) + (spreadCall ? 0 : 0);
                    var args = new List<MExpr>();
                    if (spreadCall)
                    {
                        // P has 2 items; ensure fixed params are still satisfiable.
                        args.Add(new MExpr.Spread(new MExpr.Ref(producer)));
                        for (var i = 2; i < minArity; i++)
                            args.Add(new MExpr.Atom(1m));
                    }
                    else
                    {
                        for (var i = 0; i < Math.Max(minArity, params_.Any(p => p.Collecting) ? minArity + 1 : minArity); i++)
                            args.Add(new MExpr.Atom(i));
                    }

                    if (spreadCall && minArity > 2)
                        continue; // unreachable with current shapes; kept for safety

                    var root = new MScope(
                        [
                            new MDecl.Value(outer, [new MExpr.Atom(7m)]),
                            new MDecl.Value(producer, [new MExpr.Atom(1m), new MExpr.Atom(2m)]),
                            new MDecl.Func(func, params_, body),
                        ],
                        [new MExpr.Call(func, args), new MExpr.Ref(outer)]);

                    cases.Add(GeneratedCase.Create(
                        $"exh/params/{index++:000}",
                        b.Finish(root),
                        "userCall",
                        shape.StartsWith("mixed", StringComparison.Ordinal) || shape == "collecting" ? "collecting" : "fixedParams",
                        paramShadow ? "shadow" : "plain",
                        spreadCall ? "spread" : "directArgs"));
                }
            }
        }
    }

    /// <summary>Single-clause sequence-value patterns: <c>H((a, *m, z))</c>
    /// opening one received structure with generator-known item counts.</summary>
    private static void AddSequencePatternCases(List<GeneratedCase> cases)
    {
        var index = 0;
        foreach (var binderShape in new[] { "fixed2", "frontCollect", "bothCollect" })
        {
            foreach (var itemCount in new[] { 2, 3, 4 })
            {
                foreach (var namedArg in new[] { false, true })
                {
                    var fixedCount = binderShape switch { "fixed2" => 2, "frontCollect" => 1, _ => 2 };
                    var hasCollect = binderShape != "fixed2";
                    if (!hasCollect && itemCount != fixedCount)
                        continue;
                    if (hasCollect && itemCount < fixedCount)
                        continue;

                    var b = new ProgramBuilder();
                    var producer = b.NewSym();
                    var func = b.NewSym();

                    var binders = new List<MBinder>();
                    switch (binderShape)
                    {
                        case "fixed2":
                            binders.Add(new(b.NewSym(), false));
                            binders.Add(new(b.NewSym(), false));
                            break;
                        case "frontCollect":
                            binders.Add(new(b.NewSym(), false));
                            binders.Add(new(b.NewSym(), true));
                            break;
                        default:
                            binders.Add(new(b.NewSym(), false));
                            binders.Add(new(b.NewSym(), true));
                            binders.Add(new(b.NewSym(), false));
                            break;
                    }

                    var body = new MExpr.Group(binders.Select(x => (MExpr)new MExpr.Ref(x.Symbol)).ToList());
                    var items = Enumerable.Range(1, itemCount).Select(v => (MExpr)new MExpr.Atom(v)).ToList();
                    var producerRows = Enumerable.Range(1, itemCount).Select(v => (MExpr)new MExpr.Atom(v)).ToList();

                    var arg = namedArg ? (MExpr)new MExpr.Ref(producer) : new MExpr.Group(items);
                    var root = new MScope(
                        [
                            new MDecl.Value(producer, producerRows),
                            new MDecl.SeqPatternFunc(func, binders, body),
                        ],
                        [new MExpr.Call(func, [arg])]);

                    cases.Add(GeneratedCase.Create(
                        $"exh/seqpat/{index++:000}",
                        b.Finish(root),
                        "seqPattern", hasCollect ? "collecting" : "fixedParams", namedArg ? "namedArg" : "groupArg"));
                }
            }
        }
    }

    /// <summary>Assignment deconstruction with known item counts and optional
    /// binder-shadows of outer names.</summary>
    private static void AddDeconstructionCases(List<GeneratedCase> cases)
    {
        var index = 0;
        foreach (var binderShape in new[] { "fixed2", "frontCollect", "bothCollect" })
        {
            foreach (var itemCount in new[] { 2, 3, 4 })
            {
                foreach (var binderShadow in new[] { false, true })
                {
                    var fixedCount = binderShape switch { "fixed2" => 2, "frontCollect" => 1, _ => 2 };
                    var hasCollect = binderShape != "fixed2";
                    if (!hasCollect && itemCount != fixedCount)
                        continue;
                    if (hasCollect && itemCount < fixedCount)
                        continue;

                    var b = new ProgramBuilder();
                    var outer = b.NewSym("s");

                    var binders = new List<MBinder>();
                    switch (binderShape)
                    {
                        case "fixed2":
                            binders.Add(new(binderShadow ? b.NewShadowOf(outer) : b.NewSym(), false));
                            binders.Add(new(b.NewSym(), false));
                            break;
                        case "frontCollect":
                            binders.Add(new(binderShadow ? b.NewShadowOf(outer) : b.NewSym(), false));
                            binders.Add(new(b.NewSym(), true));
                            break;
                        default:
                            binders.Add(new(b.NewSym(), false));
                            binders.Add(new(binderShadow ? b.NewShadowOf(outer) : b.NewSym(), true));
                            binders.Add(new(b.NewSym(), false));
                            break;
                    }

                    // Binder shadowing the root-scope outer name would collide in
                    // the SAME scope (deconstruction binds into the root scope), so
                    // shadow variants nest the deconstruction inside a brace.
                    var items = Enumerable.Range(1, itemCount).Select(v => (MExpr)new MExpr.Atom(v)).ToList();
                    var decon = new MDecl.Deconstruction(binders, new MExpr.Group(items));
                    var binderRefs = binders.Select(x => (MExpr)new MExpr.Ref(x.Symbol)).ToList();

                    MScope root;
                    if (binderShadow)
                    {
                        var brace = new MExpr.Brace(new MScope([decon], binderRefs));
                        root = new MScope([new MDecl.Value(outer, [new MExpr.Atom(7m)])], [new MExpr.Ref(outer), brace]);
                    }
                    else
                    {
                        root = new MScope(
                            [new MDecl.Value(outer, [new MExpr.Atom(7m)]), decon],
                            binderRefs.Prepend(new MExpr.Ref(outer)).ToList());
                    }

                    cases.Add(GeneratedCase.Create(
                        $"exh/decon/{index++:000}",
                        b.Finish(root),
                        "deconstruct", hasCollect ? "collecting" : "fixedParams", binderShadow ? "shadow" : "plain"));
                }
            }
        }
    }

    /// <summary>Sole-row focus programs for the two known-delta rules, with
    /// scope noise (same-named unused inner declarations) around the producer.</summary>
    private static void AddDeltaFocusCases(List<GeneratedCase> cases)
    {
        var index = 0;
        foreach (var rows in new[] { 2, 3 })
        {
            foreach (var soleRowKind in new[] { "spread", "ref" })
            {
                foreach (var noise in new[] { false, true })
                {
                    var b = new ProgramBuilder();
                    var producer = b.NewSym("p");
                    var decls = new List<MDecl>
                    {
                        new MDecl.Value(producer, Enumerable.Range(1, rows).Select(v => (MExpr)new MExpr.Atom(10m * v)).ToList()),
                    };

                    if (noise)
                    {
                        var noiseSym = b.NewSym();
                        var innerShadow = b.NewShadowOf(producer);
                        decls.Add(new MDecl.Value(noiseSym, [
                            new MExpr.Brace(new MScope(
                                [new MDecl.Value(innerShadow, [new MExpr.Atom(0m)])],
                                [new MExpr.Ref(innerShadow)])),
                        ]));
                    }

                    MExpr soleRow = soleRowKind == "spread"
                        ? new MExpr.Spread(new MExpr.Ref(producer))
                        : new MExpr.Ref(producer);

                    cases.Add(GeneratedCase.Create(
                        $"exh/delta/{index++:000}",
                        b.Finish(new MScope(decls, [soleRow])),
                        "multiOut", soleRowKind == "spread" ? "spread" : "namedRef", noise ? "shadow" : "plain"));
                }
            }
        }
    }

    /// <summary>Zero-output programs (spread of the empty sequence) with scope noise.</summary>
    private static void AddZeroOutputCases(List<GeneratedCase> cases)
    {
        var index = 0;
        foreach (var noise in new[] { false, true })
        {
            var b = new ProgramBuilder();
            var zero = b.NewSym("z");
            var decls = new List<MDecl> { new MDecl.Value(zero, [new MExpr.Group([])]) };
            if (noise)
            {
                var inner = b.NewShadowOf(zero);
                decls.Add(new MDecl.Value(b.NewSym(), [
                    new MExpr.Brace(new MScope(
                        [new MDecl.Value(inner, [new MExpr.Atom(1m)])],
                        [new MExpr.Ref(inner)])),
                ]));
            }

            cases.Add(GeneratedCase.Create(
                $"exh/zero/{index++:000}",
                b.Finish(new MScope(decls, [new MExpr.Spread(new MExpr.Ref(zero))])),
                "zeroOut", noise ? "shadow" : "plain"));
        }
    }

    /// <summary>Hand-curated pairwise interaction showcases the systematic
    /// families do not already produce.</summary>
    private static void AddInteractionCases(List<GeneratedCase> cases)
    {
        // if inside a clause body (conditional × clause dispatch × shadow).
        {
            var b = new ProgramBuilder();
            var outer = b.NewSym("s");
            var family = b.NewSym();
            var binder = b.NewShadowOf(outer);
            var thenS = b.NextSentinel();
            var elseS = b.NextSentinel();
            var litS = b.NextSentinel();
            b.ExpectContains(thenS);
            b.ExpectAbsent(elseS);
            b.ExpectAbsent(litS);
            var clauses = new List<MClause>
            {
                new(new MPattern.Literal(0m), new MExpr.Atom(litS)),
                new(new MPattern.Binder(binder),
                    new MExpr.Group([
                        new MExpr.Ref(binder),
                        new MExpr.If(new MExpr.Atom(1m), new MExpr.Atom(thenS), new MExpr.Atom(elseS)),
                    ])),
            };
            cases.Add(GeneratedCase.Create(
                "exh/mix/if-in-clause",
                b.Finish(new MScope(
                    [new MDecl.Value(outer, [new MExpr.Atom(2m)]), new MDecl.Family(family, clauses)],
                    [new MExpr.Call(family, [new MExpr.Atom(7m)]), new MExpr.Ref(outer)])),
                "family", "if", "shadow"));
        }

        // Collecting forward: Q(*items) = items*, called with a spread argument
        // (collecting × spread interaction, forwarding law).
        {
            var b = new ProgramBuilder();
            var producer = b.NewSym();
            var func = b.NewSym();
            var items = b.NewSym();
            cases.Add(GeneratedCase.Create(
                "exh/mix/collect-forward",
                b.Finish(new MScope(
                    [
                        new MDecl.Value(producer, [new MExpr.Atom(1m), new MExpr.Atom(2m), new MExpr.Atom(7m)]),
                        new MDecl.Func(func, [new MParam(items, Collecting: true)], new MExpr.Spread(new MExpr.Ref(items))),
                    ],
                    [new MExpr.Call(func, [new MExpr.Spread(new MExpr.Ref(producer))])])),
                "collecting", "spread", "multiOut"));
        }

        // Conditional branches that are braces with SAME-named locals AND a
        // dead runtime tripwire in the unselected branch (branch isolation ×
        // runtime-error tripwire).
        {
            var b = new ProgramBuilder();
            var thenLocal = b.NewSym("w");
            var elseLocal = b.NewSym("w");
            var thenS = b.NextSentinel();
            b.ExpectContains(thenS);
            var thenBrace = new MExpr.Brace(new MScope(
                [new MDecl.Value(thenLocal, [new MExpr.Atom(thenS)])],
                [new MExpr.Ref(thenLocal)]));
            var elseBrace = new MExpr.Brace(new MScope(
                [new MDecl.Value(elseLocal, [new MExpr.IndexErr()])],
                [new MExpr.Ref(elseLocal)]));
            cases.Add(GeneratedCase.Create(
                "exh/mix/branch-isolation-tripwire",
                b.Finish(new MScope([], [new MExpr.If(new MExpr.Atom(2m), thenBrace, elseBrace)])),
                "if", "brace", "runtimeTripwire"));
        }

        // Deconstruction of a producer reference inside a brace, result used
        // in an if condition position? Conditions stay literal — instead use
        // binders in both branches (deconstruct × capture × nested scope).
        {
            var b = new ProgramBuilder();
            var producer = b.NewSym();
            var x = b.NewSym();
            var m = b.NewSym();
            var z = b.NewSym();
            var brace = new MExpr.Brace(new MScope(
                [new MDecl.Deconstruction([new(x, false), new(m, true), new(z, false)], new MExpr.Ref(producer))],
                [new MExpr.Group([new MExpr.Ref(x), new MExpr.Ref(z)]), new MExpr.Ref(m)]));
            cases.Add(GeneratedCase.Create(
                "exh/mix/decon-of-producer-in-brace",
                b.Finish(new MScope(
                    [new MDecl.Value(producer, [new MExpr.Atom(1m), new MExpr.Atom(2m), new MExpr.Atom(7m)])],
                    [brace, new MExpr.Spread(new MExpr.Ref(producer))])),
                "deconstruct", "brace", "multiOut", "collecting"));
        }
    }

    // ── Seeded composed tier ────────────────────────────────────────────────

    public static IReadOnlyList<GeneratedCase> SeededCases()
    {
        var cases = new List<GeneratedCase>();
        foreach (var seed in Seeds)
        {
            var rng = new SplitMix64(seed);
            for (var i = 0; i < 4; i++)
                cases.Add(ComposeCase(seed, i, ref rng));
        }

        return cases;
    }

    /// <summary>Composes one larger valid program: root values/producers, an
    /// optional function/family/deconstruction, nested braces with deliberate
    /// shadows, and rows mixing refs, calls, ifs, spreads and braces. Every
    /// choice is drawn from the seed stream; visibility is tracked so every
    /// reference has a generator-chosen target.</summary>
    private static GeneratedCase ComposeCase(ulong seed, int index, ref SplitMix64 rng)
    {
        var b = new ProgramBuilder();
        var features = new HashSet<string>(StringComparer.Ordinal);
        var decls = new List<MDecl>();
        var rootValues = new List<Sym>();
        var scalarValues = new List<Sym>();

        var valueCount = 1 + rng.Next(3);
        for (var i = 0; i < valueCount; i++)
        {
            var sym = b.NewSym();
            var producer = rng.Chance(40);
            var rows = producer
                ? Enumerable.Range(1, 2 + rng.Next(2)).Select(v => (MExpr)new MExpr.Atom(v)).ToList()
                : new List<MExpr> { new MExpr.Atom(StructuralProgram.NormalAtoms[rng.Next(4)]) };
            if (producer)
                features.Add("multiOut");
            else
                scalarValues.Add(sym);
            decls.Add(new MDecl.Value(sym, rows));
            rootValues.Add(sym);
        }

        Sym? funcSym = null;
        var funcCollecting = false;
        if (rng.Chance(60))
        {
            funcSym = b.NewSym();
            funcCollecting = rng.Chance(40);
            features.Add(funcCollecting ? "collecting" : "fixedParams");
            features.Add("userCall");
            var paramShadow = rng.Chance(40);
            if (paramShadow)
                features.Add("shadow");
            var p = paramShadow ? b.NewShadowOf(rootValues[0]) : b.NewSym();

            // The body operand must be SCALAR (arithmetic on a multi-output
            // sequence value is a type error), and a shadowing parameter makes
            // the shadowed root value unreferencable from the body — the
            // generator must not create a reference whose rendered name would
            // re-bind to the parameter.
            var visibleOuter = scalarValues.Where(s => !paramShadow || s != rootValues[0]).ToList();
            var outerOperand = visibleOuter.Count > 0
                ? (MExpr)new MExpr.Ref(visibleOuter[rng.Next(visibleOuter.Count)])
                : new MExpr.Atom(2m);
            var body = funcCollecting
                ? (MExpr)new MExpr.Ref(p)
                : new MExpr.Add(new MExpr.Ref(p), outerOperand);
            decls.Add(new MDecl.Func(funcSym.Value, [new MParam(p, funcCollecting)], body));
        }

        Sym? familySym = null;
        decimal familyLiteral = 0m;
        if (rng.Chance(50))
        {
            familySym = b.NewSym();
            features.Add("family");
            var s1 = b.NextSentinel();
            var s2 = b.NextSentinel();
            familyLiteral = rng.Next(2);
            var clauses = new List<MClause>
            {
                new(new MPattern.Literal(0m), new MExpr.Atom(s1)),
                new(new MPattern.Literal(1m), new MExpr.Atom(s2)),
            };
            if (rng.Chance(50))
            {
                var binder = b.NewSym();
                clauses.Add(new MClause(new MPattern.Binder(binder), new MExpr.Ref(binder)));
                features.Add("catchAll");
            }

            b.ExpectContains(familyLiteral == 0m ? s1 : s2);
            b.ExpectAbsent(familyLiteral == 0m ? s2 : s1);
            decls.Add(new MDecl.Family(familySym.Value, clauses));
        }

        var rootRows = new List<MExpr>();
        var rowCount = 1 + rng.Next(3);
        for (var i = 0; i < rowCount; i++)
        {
            switch (rng.Next(5))
            {
                case 0:
                    rootRows.Add(new MExpr.Ref(rootValues[rng.Next(rootValues.Count)]));
                    break;
                case 1 when funcSym is { } f:
                    rootRows.Add(new MExpr.Call(f, [new MExpr.Atom(1m)]));
                    break;
                case 2:
                {
                    features.Add("if");
                    var cond = (decimal)rng.Next(3);
                    var thenS = b.NextSentinel();
                    var elseS = b.NextSentinel();
                    b.ExpectContains(cond != 0m ? thenS : elseS);
                    b.ExpectAbsent(cond != 0m ? elseS : thenS);
                    rootRows.Add(new MExpr.If(new MExpr.Atom(cond), new MExpr.Atom(thenS), new MExpr.Atom(elseS)));
                    break;
                }

                case 3:
                {
                    features.Add("brace");
                    features.Add("shadow");
                    var inner = b.NewShadowOf(rootValues[rng.Next(rootValues.Count)]);
                    rootRows.Add(new MExpr.Brace(new MScope(
                        [new MDecl.Value(inner, [new MExpr.Atom(7m)])],
                        [new MExpr.Ref(inner)])));
                    break;
                }

                default:
                {
                    features.Add("spread");
                    rootRows.Add(new MExpr.Spread(new MExpr.Ref(rootValues[rng.Next(rootValues.Count)])));
                    break;
                }
            }
        }

        if (familySym is { } fam)
            rootRows.Add(new MExpr.Call(fam, [new MExpr.Atom(familyLiteral)]));

        return GeneratedCase.Create(
            $"seed/0x{seed:X}/{index}",
            b.Finish(new MScope(decls, rootRows)),
            features.Append("composed").ToArray());
    }
}
