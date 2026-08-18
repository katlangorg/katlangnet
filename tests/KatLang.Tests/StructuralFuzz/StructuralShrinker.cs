namespace KatLang.Tests.StructuralFuzz;

/// <summary>
/// Semantic-aware minimization: reductions operate on the MODEL (never on
/// source substrings), and every accepted reduction must (a) keep the naming
/// map binding-valid, (b) keep the metamorphic rule APPLICABLE (the rule's
/// transform enumerator still yields a candidate on the reduced program), and
/// (c) keep that candidate VIOLATING per the caller's oracle. Rule
/// preconditions are therefore preserved by construction — an alpha-rename
/// shrink cannot lose its binding, a dead-branch shrink cannot lose its
/// known-truth condition, a clause-permutation shrink cannot lose disjointness
/// — because the same precondition-checking enumerator gates every step.
/// </summary>
public static class StructuralShrinker
{
    public sealed record ShrinkResult(
        StructuralProgram Program,
        TransformCandidate FailingCandidate,
        int OriginalSize,
        int ShrunkSize,
        int AcceptedReductions);

    /// <summary>
    /// Greedy fixpoint shrink. <paramref name="violates"/> receives a reduced
    /// BASE program and one of its rule candidates and reports whether the
    /// violation still reproduces (including any base-program validity the
    /// rule requires). Bounded by attempt count so a pathological oracle can
    /// never hang the suite.
    /// </summary>
    public static ShrinkResult Shrink(
        StructuralProgram program,
        StructuralRule rule,
        Func<StructuralProgram, TransformCandidate, bool> violates,
        int maxAttempts = 300)
    {
        var current = program;
        var currentCandidate = FirstViolating(current, rule, violates)
            ?? throw new InvalidOperationException("Shrink started from a non-violating program.");
        var accepted = 0;
        var attempts = 0;
        var progress = true;

        while (progress && attempts < maxAttempts)
        {
            progress = false;
            foreach (var reduced in Reductions(current))
            {
                if (++attempts >= maxAttempts)
                    break;

                if (!NamingStillValid(reduced))
                    continue;

                if (FirstViolating(reduced, rule, violates) is not { } stillFailing)
                    continue;

                current = reduced;
                currentCandidate = stillFailing;
                accepted++;
                progress = true;
                break;
            }
        }

        return new ShrinkResult(current, currentCandidate, Size(program), Size(current), accepted);
    }

    private static TransformCandidate? FirstViolating(
        StructuralProgram program,
        StructuralRule rule,
        Func<StructuralProgram, TransformCandidate, bool> violates)
    {
        IReadOnlyList<TransformCandidate> candidates;
        try
        {
            candidates = StructuralTransforms.Enumerate(program).Where(c => c.Rule == rule).ToList();
        }
        catch (InvalidOperationException)
        {
            return null; // reduction broke the model — reject
        }

        foreach (var candidate in candidates)
        {
            if (violates(program, candidate))
                return candidate;
        }

        return null;
    }

    private static bool NamingStillValid(StructuralProgram program)
    {
        try
        {
            program.ValidateNaming();
            return true;
        }
        catch (InvalidOperationException)
        {
            return false;
        }
    }

    /// <summary>Node-count size metric over declarations and expressions.</summary>
    public static int Size(StructuralProgram program)
    {
        var size = 0;
        foreach (var scope in ModelRewriter.CollectScopes(program.Root))
            size += scope.Decls.Count + scope.Rows.Count;
        size += ModelRewriter.CollectExprs<MExpr>(program.Root).Count;
        return size;
    }

    /// <summary>Deterministically ordered candidate reductions, largest-effect first.</summary>
    private static IEnumerable<StructuralProgram> Reductions(StructuralProgram program)
    {
        // 1. Remove one declaration anywhere (root or nested).
        foreach (var scope in ModelRewriter.CollectScopes(program.Root))
        {
            foreach (var decl in scope.Decls)
                yield return program with { Root = ModelRewriter.ReplaceDecl(program.Root, decl, null) };
        }

        // 2. Remove one root row (keep at least one).
        if (program.Root.Rows.Count > 1)
        {
            for (var i = 0; i < program.Root.Rows.Count; i++)
            {
                var rows = program.Root.Rows.Where((_, j) => j != i).ToList();
                yield return program with { Root = new MScope(program.Root.Decls, rows) };
            }
        }

        // 3. Trim a multi-row producer to its first two rows.
        foreach (var scope in ModelRewriter.CollectScopes(program.Root))
        {
            foreach (var decl in scope.Decls)
            {
                if (decl is MDecl.Value { Rows.Count: > 2 } value)
                {
                    yield return program with
                    {
                        Root = ModelRewriter.ReplaceDecl(
                            program.Root, value, new MDecl.Value(value.Symbol, value.Rows.Take(2).ToList())),
                    };
                }
            }
        }

        // 4. Replace one brace expression with an atom.
        foreach (var brace in ModelRewriter.CollectExprs<MExpr.Brace>(program.Root))
            yield return program with { Root = ModelRewriter.ReplaceExpr(program.Root, brace, new MExpr.Atom(1m)) };

        // 5. Drop one clause from a family (dispatch preconditions re-checked
        // by the rule enumerator on the reduced program).
        foreach (var scope in ModelRewriter.CollectScopes(program.Root))
        {
            foreach (var decl in scope.Decls)
            {
                if (decl is MDecl.Family { Clauses.Count: > 1 } family)
                {
                    for (var i = 0; i < family.Clauses.Count; i++)
                    {
                        var clauses = family.Clauses.Where((_, j) => j != i).ToList();
                        yield return program with
                        {
                            Root = ModelRewriter.ReplaceDecl(program.Root, family, new MDecl.Family(family.Symbol, clauses)),
                        };
                    }
                }
            }
        }

        // 6. Replace one if-expression with its selected branch (keeps other
        // if-targets alive; the reduced program simply has one fewer).
        foreach (var ifNode in ModelRewriter.CollectExprs<MExpr.If>(program.Root))
        {
            if (ifNode.Cond is MExpr.Atom cond)
            {
                var selected = cond.Value != 0m ? ifNode.Then : ifNode.Else;
                yield return program with { Root = ModelRewriter.ReplaceExpr(program.Root, ifNode, selected) };
            }
        }
    }
}
