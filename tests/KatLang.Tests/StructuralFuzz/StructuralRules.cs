using System.Numerics;

namespace KatLang.Tests.StructuralFuzz;

/// <summary>
/// The metamorphic rule taxonomy. Every member must produce candidates in the
/// deterministic corpus (meta-enforced), and every candidate records WHY the
/// relation is expected (the precondition), so a failure names a semantic law,
/// not a random divergence.
/// </summary>
public enum StructuralRule
{
    /// <summary>Consistent rename of one non-shadowed declaration + its references.</summary>
    AlphaRenameLocal,

    /// <summary>Consistent rename of one parameter/pattern/deconstruction binder.</summary>
    AlphaRenamePatternBinder,

    /// <summary>Rename only the OUTER declaration of a same-name shadow pair.</summary>
    RenameShadowedOuter,

    /// <summary>Rename only the INNER (shadowing) declaration of a shadow pair.</summary>
    RenameShadowingInner,

    /// <summary>Rename EVERY symbol to a fresh distinct name universe: the
    /// binding graph is preserved exactly, all textual coincidence (including
    /// shadowing) is erased. Strongest text-vs-graph discriminator.</summary>
    ScopeGraphIsomorphism,

    /// <summary>Insert an unused, guaranteed-fresh value declaration. Properties
    /// are evaluated on demand, so an unreferenced declaration is semantically
    /// inert; insertion position varies (first/last, outer/inner scope).</summary>
    InsertFreshUnusedBinding,

    /// <summary>Bulk-rename all declarations local to one brace/sibling scope
    /// (lexically invisible outside it); other scopes must be unaffected.</summary>
    SiblingScopeIsolation,

    /// <summary>Replace the never-evaluated ELSE of a known-true literal
    /// condition with a tripwire (runtime error, different cardinality, or a
    /// unique sentinel). Valid because `if` evaluates only the selected branch
    /// (Lean applyBuiltinCounted .ifBuiltin).</summary>
    KnownTrueDeadBranchMutation,

    /// <summary>Symmetric: mutate the THEN of a known-false condition.</summary>
    KnownFalseDeadBranchMutation,

    /// <summary>Replace <c>if(literal, T, E)</c> by the selected branch
    /// expression. Valid because the literal condition is semantically inert
    /// and `if` re-counts the selected branch at a value boundary exactly like
    /// the branch expression standing alone in the same slot.</summary>
    KnownConditionReduction,

    /// <summary>Replace <c>if(literal, {A}, {B})</c> (brace branches with
    /// deliberately colliding local names) by the selected brace alone: the
    /// unselected branch's same-named declarations must have contributed
    /// nothing.</summary>
    ConditionalBranchScopeIsolation,

    /// <summary>Swap two literal clauses of one family (both before any
    /// catch-all). Distinct literals are disjoint, so source-order first-match
    /// dispatch may not depend on their relative order.</summary>
    PermuteDisjointClauses,

    /// <summary>Insert a literal clause that provably cannot match the
    /// observed call (fresh literal, tripwire body) into the literal prefix.</summary>
    InsertUnreachableClause,

    /// <summary>KNOWN-DELTA: sole root row <c>P*</c> (supply n ≥ 2) becomes
    /// <c>(P*)</c>. Capture reifies the supply into ONE value: raw structure
    /// unchanged, emitted count becomes 1 (counted-matrix law).</summary>
    CaptureKnownDelta,

    /// <summary>KNOWN-DELTA: sole root row <c>P</c> (a named multi-row producer,
    /// value boundary, n = 1) becomes <c>P*</c>: raw unchanged, emitted count
    /// becomes the producer's row count (counted-matrix law).</summary>
    SpreadKnownDelta,

    /// <summary>KNOWN-ERROR: change a literal-only family call's argument to a
    /// literal matching no clause → err branch (Lean noMatchingBranch).</summary>
    ForceKnownNonMatchingClause,

    /// <summary>KNOWN-ERROR: remove the unique declaration of a name referenced
    /// from root rows → the name becomes an unresolved top-level implicit
    /// parameter → err unresolvedImplicitParams (pinned by EvaluatorTests).</summary>
    RemoveRequiredBinding,

    /// <summary>KNOWN-FRONT-END-ERROR: make one clause's top-level pattern
    /// arity 2 in an arity-1 family → front-end uniform-arity rejection.</summary>
    IntroduceInvalidFamilyShape,
}

/// <summary>Expected relation between the original and transformed observation.</summary>
public abstract record ExpectedRelation
{
    /// <summary>Neutral raw + count + display all equal.</summary>
    public sealed record Equivalent : ExpectedRelation;

    /// <summary>Raw structure identical; emitted count becomes exactly this.</summary>
    public sealed record RawPreservedCountBecomes(int NewCount) : ExpectedRelation;

    /// <summary>ok → err with exactly this category.</summary>
    public sealed record BecomesRuntimeError(string Category) : ExpectedRelation;

    /// <summary>ok → front-end rejection (parseError outcome).</summary>
    public sealed record BecomesFrontEndError : ExpectedRelation;

    public override string ToString() => this switch
    {
        Equivalent => "exact semantic equivalence",
        RawPreservedCountBecomes c => $"raw preserved, emitted count becomes {c.NewCount}",
        BecomesRuntimeError e => $"ok → err {e.Category}",
        BecomesFrontEndError => "ok → front-end rejection",
        _ => GetType().Name,
    };
}

/// <summary>
/// One applicable transformation: the transformed program, the rule, the
/// expected relation, and the human-readable precondition justifying it.
/// Known-error transforms deliberately break naming/model validity, so they
/// opt out of the transformed-side naming validation.
/// </summary>
public sealed record TransformCandidate(
    StructuralRule Rule,
    string Description,
    StructuralProgram Transformed,
    ExpectedRelation Relation,
    bool ValidateTransformedNaming = true);

/// <summary>Identity-addressed structural rewriting. Generated models never
/// share node instances, so replacing BY REFERENCE is exact single-site
/// surgery: ancestors along the path are rebuilt, everything else is shared.</summary>
internal static class ModelRewriter
{
    public static MScope ReplaceExpr(MScope scope, MExpr target, MExpr replacement)
        => MapScope(scope, e => ReferenceEquals(e, target) ? replacement : null);

    public static MScope ReplaceDecl(MScope scope, MDecl target, MDecl? replacement)
    {
        var decls = new List<MDecl>();
        var changed = false;
        foreach (var decl in scope.Decls)
        {
            if (ReferenceEquals(decl, target))
            {
                changed = true;
                if (replacement is not null)
                    decls.Add(replacement);
                continue;
            }

            var rewritten = MapDecl(decl, e => null, s => ReplaceDecl(s, target, replacement));
            changed |= !ReferenceEquals(rewritten, decl);
            decls.Add(rewritten);
        }

        var rows = scope.Rows.Select(r => MapExpr(r, e => null, s => ReplaceDecl(s, target, replacement))).ToList();
        var rowsChanged = rows.Zip(scope.Rows).Any(p => !ReferenceEquals(p.First, p.Second));
        return changed || rowsChanged ? new MScope(decls, rows) : scope;
    }

    public static MScope InsertDecl(MScope scope, MScope targetScope, int index, MDecl decl)
    {
        if (ReferenceEquals(scope, targetScope))
        {
            var decls = new List<MDecl>(scope.Decls);
            decls.Insert(Math.Min(index, decls.Count), decl);
            return new MScope(decls, scope.Rows);
        }

        var newDecls = scope.Decls.Select(d => MapDecl(d, e => null, s => InsertDecl(s, targetScope, index, decl))).ToList();
        var newRows = scope.Rows.Select(r => MapExpr(r, e => null, s => InsertDecl(s, targetScope, index, decl))).ToList();
        return new MScope(newDecls, newRows);
    }

    /// <summary>Single-site expression rewrite: <paramref name="exprMap"/>
    /// returns a replacement or null to keep walking.</summary>
    private static MScope MapScope(MScope scope, Func<MExpr, MExpr?> exprMap)
        => new(
            scope.Decls.Select(d => MapDecl(d, exprMap, s => MapScope(s, exprMap))).ToList(),
            scope.Rows.Select(r => MapExpr(r, exprMap, s => MapScope(s, exprMap))).ToList());

    private static MDecl MapDecl(MDecl decl, Func<MExpr, MExpr?> exprMap, Func<MScope, MScope> scopeMap)
        => decl switch
        {
            MDecl.Value v => new MDecl.Value(v.Symbol, v.Rows.Select(r => MapExpr(r, exprMap, scopeMap)).ToList()),
            MDecl.Func f => new MDecl.Func(f.Symbol, f.Params, MapExpr(f.Body, exprMap, scopeMap)),
            MDecl.Family fam => new MDecl.Family(
                fam.Symbol,
                fam.Clauses.Select(c => new MClause(c.Pattern, MapExpr(c.Body, exprMap, scopeMap))).ToList()),
            MDecl.SeqPatternFunc sp => new MDecl.SeqPatternFunc(sp.Symbol, sp.Binders, MapExpr(sp.Body, exprMap, scopeMap)),
            MDecl.Deconstruction d => new MDecl.Deconstruction(d.Binders, MapExpr(d.Rhs, exprMap, scopeMap)),
            _ => throw new InvalidOperationException($"Unhandled decl kind {decl.GetType().Name}"),
        };

    private static MExpr MapExpr(MExpr expr, Func<MExpr, MExpr?> exprMap, Func<MScope, MScope> scopeMap)
    {
        if (exprMap(expr) is { } replaced)
            return replaced;

        return expr switch
        {
            MExpr.Atom or MExpr.Ref or MExpr.IndexErr => expr,
            MExpr.Add a => new MExpr.Add(MapExpr(a.Left, exprMap, scopeMap), MapExpr(a.Right, exprMap, scopeMap)),
            MExpr.Group g => new MExpr.Group(g.Items.Select(i => MapExpr(i, exprMap, scopeMap)).ToList()),
            MExpr.Spread s => new MExpr.Spread(MapExpr(s.Operand, exprMap, scopeMap)),
            MExpr.Call c => new MExpr.Call(c.Callee, c.Args.Select(a => MapExpr(a, exprMap, scopeMap)).ToList()),
            MExpr.If i => new MExpr.If(
                MapExpr(i.Cond, exprMap, scopeMap),
                MapExpr(i.Then, exprMap, scopeMap),
                MapExpr(i.Else, exprMap, scopeMap)),
            MExpr.Brace b => new MExpr.Brace(scopeMap(b.Scope)),
            _ => throw new InvalidOperationException($"Unhandled expr kind {expr.GetType().Name}"),
        };
    }

    /// <summary>References in an expression WITHOUT descending into brace
    /// scopes — used where "referenced directly from this scope's rows" (not
    /// from a nested algorithm) is the precondition.</summary>
    public static IReadOnlyList<MExpr.Ref> CollectRefsShallow(MExpr expr)
    {
        var found = new List<MExpr.Ref>();
        Visit(expr);
        return found;

        void Visit(MExpr e)
        {
            switch (e)
            {
                case MExpr.Ref r:
                    found.Add(r);
                    return;
                case MExpr.Add a:
                    Visit(a.Left);
                    Visit(a.Right);
                    return;
                case MExpr.Group g:
                    foreach (var item in g.Items) Visit(item);
                    return;
                case MExpr.Spread s:
                    Visit(s.Operand);
                    return;
                case MExpr.Call c:
                    foreach (var arg in c.Args) Visit(arg);
                    return;
                case MExpr.If i:
                    Visit(i.Cond);
                    Visit(i.Then);
                    Visit(i.Else);
                    return;
                default:
                    return; // Atom, IndexErr, Brace (deliberately not entered)
            }
        }
    }

    public static IReadOnlyList<T> CollectExprs<T>(MScope scope) where T : MExpr
    {
        var found = new List<T>();
        Collect(scope);
        return found;

        void Collect(MScope s)
        {
            foreach (var decl in s.Decls)
                MapDecl(decl, Visit, sc => { Collect(sc); return sc; });
            foreach (var row in s.Rows)
                MapExpr(row, Visit, sc => { Collect(sc); return sc; });
        }

        MExpr? Visit(MExpr e)
        {
            if (e is T match)
                found.Add(match);
            return null;
        }
    }

    public static IReadOnlyList<MScope> CollectScopes(MScope root)
    {
        var found = new List<MScope> { root };
        foreach (var decl in root.Decls)
            MapDecl(decl, e => null, s => { found.AddRange(CollectScopes(s)); return s; });
        foreach (var row in root.Rows)
            MapExpr(row, e => null, s => { found.AddRange(CollectScopes(s)); return s; });
        return found;
    }
}

/// <summary>
/// Enumerates every applicable transformation of a program, deterministically
/// ordered. Rename rules operate purely on the NAME MAP and revalidate the
/// binding graph; structural rules rewrite the model by node identity;
/// known-error rules record their expected category/phase.
/// </summary>
public static class StructuralTransforms
{
    public static IReadOnlyList<TransformCandidate> Enumerate(StructuralProgram program)
    {
        var candidates = new List<TransformCandidate>();
        var graph = ScopeGraph.Build(program.Root);
        var declarations = program.AllDeclarations();
        var usedNames = new HashSet<string>(program.Names.Values, StringComparer.Ordinal);

        var freshCounter = 0;
        string FreshName()
        {
            string name;
            do
            {
                name = $"fr{++freshCounter}";
            }
            while (!usedNames.Add(name));
            return name;
        }

        // ── Rename rules (name-map only) ────────────────────────────────────
        var shadowPairs = FindShadowPairs(declarations, graph.AllScopes, program.Names);
        var shadowSymbols = shadowPairs.SelectMany(p => new[] { p.Outer, p.Inner }).ToHashSet();

        foreach (var (symbol, _, kind) in declarations)
        {
            var isBinder = kind is "param" or "collectingParam" or "clauseBinder" or "seqBinder"
                or "seqCollectingBinder" or "deconstructBinder" or "deconstructCollecting";
            if (shadowSymbols.Contains(symbol))
                continue;

            var rule = isBinder ? StructuralRule.AlphaRenamePatternBinder : StructuralRule.AlphaRenameLocal;
            AddRename(rule, symbol, $"rename {kind} {symbol} '{program.Names[symbol]}'");
        }

        foreach (var pair in shadowPairs)
        {
            AddRename(
                StructuralRule.RenameShadowedOuter, pair.Outer,
                $"rename OUTER {pair.Outer} of shadow pair '{program.Names[pair.Outer]}' (inner {pair.Inner} keeps the name)");
            AddRename(
                StructuralRule.RenameShadowingInner, pair.Inner,
                $"rename INNER {pair.Inner} of shadow pair '{program.Names[pair.Inner]}' (outer {pair.Outer} keeps the name)");
        }

        void AddRename(StructuralRule rule, Sym symbol, string description)
        {
            var fresh = FreshName();
            var names = new Dictionary<Sym, string>(program.Names) { [symbol] = fresh };
            if (!graph.RenameKeepsBindings(symbol, fresh, program.Names))
                return;

            candidates.Add(new TransformCandidate(
                rule,
                $"{description} → '{fresh}'; binding graph revalidated",
                program with { Names = names },
                new ExpectedRelation.Equivalent()));
        }

        // ScopeGraphIsomorphism: every symbol gets a fresh distinct name.
        if (declarations.Count >= 2)
        {
            var isoNames = declarations
                .Select((d, i) => (d.Symbol, Name: $"n{i + 1}"))
                .ToDictionary(p => p.Symbol, p => p.Name);
            candidates.Add(new TransformCandidate(
                StructuralRule.ScopeGraphIsomorphism,
                $"rename ALL {declarations.Count} symbols into a distinct fresh name universe; binding graph preserved exactly",
                program with { Names = isoNames },
                new ExpectedRelation.Equivalent()));
        }

        // SiblingScopeIsolation: bulk-rename everything declared inside one brace.
        foreach (var brace in ModelRewriter.CollectExprs<MExpr.Brace>(program.Root))
        {
            var localSymbols = ScopeGraph.Build(brace.Scope).Declarations.Select(d => d.Symbol).ToList();
            if (localSymbols.Count == 0)
                continue;

            var names = new Dictionary<Sym, string>(program.Names);
            foreach (var symbol in localSymbols)
                names[symbol] = FreshName();

            candidates.Add(new TransformCandidate(
                StructuralRule.SiblingScopeIsolation,
                $"bulk-rename the {localSymbols.Count} declarations local to one brace scope (lexically invisible outside it)",
                program with { Names = names },
                new ExpectedRelation.Equivalent()));
        }

        // ── Conditional rules ───────────────────────────────────────────────
        var tripwireCounter = 0;
        foreach (var ifNode in ModelRewriter.CollectExprs<MExpr.If>(program.Root))
        {
            if (ifNode.Cond is not MExpr.Atom cond)
                continue;

            var condTrue = cond.Value != 0m;
            var dead = condTrue ? ifNode.Else : ifNode.Then;
            var selected = condTrue ? ifNode.Then : ifNode.Else;

            MExpr[] tripwires =
            [
                new MExpr.IndexErr(),
                new MExpr.Atom(StructuralProgram.FirstTripwire + (++tripwireCounter % 30)),
                new MExpr.Group([new MExpr.Atom(StructuralProgram.FirstTripwire + 31), new MExpr.Atom(StructuralProgram.FirstTripwire + 32)]),
            ];
            var tripwire = tripwires[tripwireCounter % tripwires.Length];
            var mutated = condTrue
                ? new MExpr.If(ifNode.Cond, ifNode.Then, tripwire)
                : new MExpr.If(ifNode.Cond, tripwire, ifNode.Else);

            candidates.Add(new TransformCandidate(
                condTrue ? StructuralRule.KnownTrueDeadBranchMutation : StructuralRule.KnownFalseDeadBranchMutation,
                $"condition literal {cond.Value} is known {(condTrue ? "TRUE" : "FALSE")} (first-flattened-atom rule); "
                + $"the {(condTrue ? "else" : "then")} branch is never evaluated (lazy if) — replaced with {tripwire.GetType().Name}",
                program with { Root = ModelRewriter.ReplaceExpr(program.Root, ifNode, mutated) },
                new ExpectedRelation.Equivalent()));

            candidates.Add(new TransformCandidate(
                StructuralRule.KnownConditionReduction,
                $"if(literal {cond.Value}, T, E) reduced to the selected branch: the literal condition is inert and "
                + "`if` re-counts the selected branch at the same value boundary",
                program with { Root = ModelRewriter.ReplaceExpr(program.Root, ifNode, selected) },
                new ExpectedRelation.Equivalent()));

            if (ifNode.Then is MExpr.Brace && ifNode.Else is MExpr.Brace)
            {
                candidates.Add(new TransformCandidate(
                    StructuralRule.ConditionalBranchScopeIsolation,
                    "if(literal, {A}, {B}) with same-named branch-local declarations replaced by the selected brace alone: "
                    + "the unselected branch's declarations must contribute nothing",
                    program with { Root = ModelRewriter.ReplaceExpr(program.Root, ifNode, selected) },
                    new ExpectedRelation.Equivalent()));
            }
        }

        // ── Clause-family rules ─────────────────────────────────────────────
        foreach (var (_, decl) in CollectFamilyDecls(program.Root))
        {
            var family = (MDecl.Family)decl;
            var literalPrefix = family.Clauses.TakeWhile(c => c.Pattern is MPattern.Literal).Count();

            if (literalPrefix >= 2)
            {
                var permuted = new List<MClause>(family.Clauses);
                (permuted[0], permuted[literalPrefix - 1]) = (permuted[literalPrefix - 1], permuted[0]);
                candidates.Add(new TransformCandidate(
                    StructuralRule.PermuteDisjointClauses,
                    $"swap literal clauses 0 and {literalPrefix - 1} of family '{program.Names[family.Symbol]}': distinct "
                    + "literals are disjoint, so first-match order between them cannot matter",
                    program with { Root = ModelRewriter.ReplaceDecl(program.Root, family, new MDecl.Family(family.Symbol, permuted)) },
                    new ExpectedRelation.Equivalent()));
            }

            var literals = family.Clauses.Select(c => c.Pattern).OfType<MPattern.Literal>().Select(l => l.Value).ToHashSet();
            var calls = ModelRewriter.CollectExprs<MExpr.Call>(program.Root)
                .Where(c => c.Callee == family.Symbol && c.Args is [MExpr.Atom])
                .ToList();

            if (calls.Count > 0)
            {
                var freshLiteral = Enumerable.Range(30, 40).Select(v => (Decimal128)v)
                    .First(v => !literals.Contains(v) && calls.All(c => ((MExpr.Atom)c.Args[0]).Value != v));
                var withUnreachable = new List<MClause>(family.Clauses);
                withUnreachable.Insert(0, new MClause(
                    new MPattern.Literal(freshLiteral),
                    new MExpr.Atom(StructuralProgram.FirstTripwire + 33)));
                candidates.Add(new TransformCandidate(
                    StructuralRule.InsertUnreachableClause,
                    $"insert literal clause ({freshLiteral} → tripwire) FIRST in family '{program.Names[family.Symbol]}': the "
                    + "literal matches no observed call argument and duplicates no existing pattern, so dispatch must ignore it",
                    program with { Root = ModelRewriter.ReplaceDecl(program.Root, family, new MDecl.Family(family.Symbol, withUnreachable)) },
                    new ExpectedRelation.Equivalent()));
            }

            var hasCatchAll = family.Clauses.Any(c => c.Pattern is MPattern.Binder);
            if (!hasCatchAll && calls.Count > 0)
            {
                var target = calls[0];
                var nonMatching = StructuralProgram.NormalAtoms.Concat(Enumerable.Range(50, 20).Select(v => (Decimal128)v))
                    .First(v => !literals.Contains(v));
                candidates.Add(new TransformCandidate(
                    StructuralRule.ForceKnownNonMatchingClause,
                    $"literal-only family '{program.Names[family.Symbol]}' called with {nonMatching}, which matches no clause "
                    + "→ noMatchingBranch (err branch)",
                    program with
                    {
                        Root = ModelRewriter.ReplaceExpr(program.Root, target, new MExpr.Call(family.Symbol, [new MExpr.Atom(nonMatching)])),
                    },
                    new ExpectedRelation.BecomesRuntimeError("branch")));
            }

            if (family.Clauses[0].Pattern is MPattern.Literal firstLiteral)
            {
                var invalid = new List<MClause>(family.Clauses)
                {
                    [0] = new MClause(new MPattern.LiteralPair(firstLiteral.Value, 0m), family.Clauses[0].Body),
                };
                candidates.Add(new TransformCandidate(
                    StructuralRule.IntroduceInvalidFamilyShape,
                    $"first clause of family '{program.Names[family.Symbol]}' becomes top-level arity 2 in an arity-1 family "
                    + "→ front-end uniform-arity rejection",
                    program with { Root = ModelRewriter.ReplaceDecl(program.Root, family, new MDecl.Family(family.Symbol, invalid)) },
                    new ExpectedRelation.BecomesFrontEndError(),
                    ValidateTransformedNaming: false));
            }
        }

        // ── InsertFreshUnusedBinding (positions: first/last of root + first of one brace) ──
        {
            var freshTargets = new List<(MScope Scope, int Index, string Where)>
            {
                (program.Root, 0, "first in root scope"),
                (program.Root, program.Root.Decls.Count, "last in root scope"),
            };
            var firstBrace = ModelRewriter.CollectExprs<MExpr.Brace>(program.Root).FirstOrDefault();
            if (firstBrace is not null)
                freshTargets.Add((firstBrace.Scope, 0, "first in a nested brace scope"));

            foreach (var (scope, index, where) in freshTargets)
            {
                var freshSym = new Sym(10_000 + candidates.Count);
                var names = new Dictionary<Sym, string>(program.Names) { [freshSym] = FreshName() };
                candidates.Add(new TransformCandidate(
                    StructuralRule.InsertFreshUnusedBinding,
                    $"insert unused fresh value declaration ({where}); unreferenced properties are never evaluated, so it is inert",
                    program with
                    {
                        Root = ModelRewriter.InsertDecl(program.Root, scope, index, new MDecl.Value(freshSym, [new MExpr.Atom(9m)])),
                        Names = names,
                    },
                    new ExpectedRelation.Equivalent()));
            }
        }

        // ── Known-delta rules (sole-row focus programs) ─────────────────────
        if (program.Root.Rows is [MExpr.Spread { Operand: MExpr.Ref pref }]
            && FindValueDecl(program.Root, pref.Target) is { } producer
            && producer.Rows.Count >= 2
            && producer.Rows.All(r => r is MExpr.Atom))
        {
            candidates.Add(new TransformCandidate(
                StructuralRule.CaptureKnownDelta,
                $"sole root row P* (supply {producer.Rows.Count}) becomes (P*): capture reifies the supply into ONE value "
                + "— raw unchanged, emitted count 1",
                program with
                {
                    Root = new MScope(program.Root.Decls, [new MExpr.Group([new MExpr.Spread(new MExpr.Ref(pref.Target))])]),
                },
                new ExpectedRelation.RawPreservedCountBecomes(1)));
        }

        if (program.Root.Rows is [MExpr.Ref soleRef]
            && FindValueDecl(program.Root, soleRef.Target) is { } refProducer
            && refProducer.Rows.Count >= 2
            && refProducer.Rows.All(r => r is MExpr.Atom))
        {
            candidates.Add(new TransformCandidate(
                StructuralRule.SpreadKnownDelta,
                $"sole root row P (value boundary, n=1) becomes P*: spread re-supplies the {refProducer.Rows.Count} items "
                + "— raw unchanged, emitted count becomes the supply count",
                program with
                {
                    Root = new MScope(program.Root.Decls, [new MExpr.Spread(new MExpr.Ref(soleRef.Target))]),
                },
                new ExpectedRelation.RawPreservedCountBecomes(refProducer.Rows.Count)));
        }

        // ── RemoveRequiredBinding ───────────────────────────────────────────
        foreach (var (scope, decl) in CollectRootDecls(program.Root))
        {
            if (!ReferenceEquals(scope, program.Root) || decl is not MDecl.Value value)
                continue;

            var name = program.Names[value.Symbol];
            var nameUnique = program.Names.Count(kv => kv.Value == name) == 1;

            // Only DIRECT root-row references qualify: a reference inside a
            // nested brace would make that inner algorithm the implicit-param
            // owner, which reports a different category than the pinned
            // top-level unresolvedImplicitParams.
            var directRootRowRefs = program.Root.Rows
                .SelectMany(ModelRewriter.CollectRefsShallow)
                .Count(r => r.Target == value.Symbol);
            var totalRefs = ModelRewriter
                .CollectExprs<MExpr.Ref>(program.Root)
                .Count(r => r.Target == value.Symbol);
            var calledAnywhere = ModelRewriter.CollectExprs<MExpr.Call>(program.Root).Any(c => c.Callee == value.Symbol);

            if (nameUnique && directRootRowRefs > 0 && directRootRowRefs == totalRefs && !calledAnywhere)
            {
                candidates.Add(new TransformCandidate(
                    StructuralRule.RemoveRequiredBinding,
                    $"remove the unique declaration of '{name}' referenced from root rows: the free name becomes an "
                    + "unresolved top-level implicit parameter → err unresolvedImplicitParams",
                    program with { Root = ModelRewriter.ReplaceDecl(program.Root, value, null) },
                    new ExpectedRelation.BecomesRuntimeError("unresolvedImplicitParams"),
                    ValidateTransformedNaming: false));
                break;
            }
        }

        return candidates;
    }

    private static MDecl.Value? FindValueDecl(MScope root, Sym symbol)
        => root.Decls.OfType<MDecl.Value>().FirstOrDefault(v => v.Symbol == symbol);

    private static IReadOnlyList<(MScope Scope, MDecl Decl)> CollectRootDecls(MScope root)
        => root.Decls.Select(d => (root, d)).ToList();

    private static IReadOnlyList<(MScope Scope, MDecl Decl)> CollectFamilyDecls(MScope root)
    {
        var found = new List<(MScope, MDecl)>();
        foreach (var scope in ModelRewriter.CollectScopes(root))
        {
            foreach (var decl in scope.Decls)
            {
                if (decl is MDecl.Family)
                    found.Add((scope, decl));
            }
        }

        return found;
    }

    private static IReadOnlyList<(Sym Outer, Sym Inner)> FindShadowPairs(
        IReadOnlyList<(Sym Symbol, ScopeInfo Scope, string Kind)> declarations,
        IReadOnlyList<ScopeInfo> allScopes,
        IReadOnlyDictionary<Sym, string> names)
    {
        var scopesById = allScopes.ToDictionary(s => s.Id);
        var pairs = new List<(Sym, Sym)>();
        foreach (var group in declarations.GroupBy(d => names[d.Symbol], StringComparer.Ordinal))
        {
            var members = group.ToList();
            if (members.Count < 2)
                continue;

            foreach (var outer in members)
            {
                foreach (var inner in members)
                {
                    if (outer.Symbol != inner.Symbol && IsAncestorScope(outer.Scope, inner.Scope, scopesById))
                        pairs.Add((outer.Symbol, inner.Symbol));
                }
            }
        }

        return pairs;
    }

    private static bool IsAncestorScope(
        ScopeInfo candidate,
        ScopeInfo descendant,
        IReadOnlyDictionary<int, ScopeInfo> scopesById)
    {
        var current = descendant;
        while (current.ParentId is { } parentId)
        {
            if (parentId == candidate.Id)
                return true;
            current = scopesById[parentId];
        }

        return false;
    }
}
