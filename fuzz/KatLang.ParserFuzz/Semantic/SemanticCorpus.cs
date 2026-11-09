using System.Collections.Immutable;
using System.Globalization;
using KatLang;
using KatLang.Tests.StructuralFuzz;

namespace KatLang.ParserFuzz;

/// <summary>
/// The SEM-2B fixed corpus: a small SYSTEMATIC tier (each family's dimensions cycled, its failure
/// variants, a context sweep, the invalid productions, explicit selected interactions and the
/// cancellation fixtures) and a SEEDED compositional tier (1–3 fragments from any families, nested
/// contexts, at most one failure, occasionally an invalid declaration). Enumerating the corpus only
/// GENERATES; nothing is evaluated, so tests and replay can re-enumerate it cheaply.
///
/// <para>Case ids are durable: <c>sem2b/v1/sys/…</c> or <c>sem2b/v1/seed/&lt;hex&gt;/&lt;index&gt;</c>.
/// A seeded case draws from its own stream, so <see cref="TryReconstruct"/> rebuilds exactly that
/// case without generating any other.</para>
/// </summary>
internal static class SemanticCorpus
{
    internal static readonly ImmutableArray<ulong> Seeds =
        [0x5EED_2B00_0001UL, 0x5EED_2B00_0002UL, 0x5EED_2B00_0003UL, 0x5EED_2B00_0004UL, 0x5EED_2B00_0005UL, 0x5EED_2B00_0006UL];

    internal const int CasesPerSeed = 16;
    internal const int SystematicSuccessPerFamily = 8;
    internal const int SystematicFailuresPerFamily = 4;

    /// <summary>Explicit selected pairwise interactions (fragment families composed in one program).</summary>
    internal static readonly ImmutableArray<(string A, string B, bool FailB)> SelectedPairs =
    [
        ("meta", "cache", false),
        ("meta", "select", true),
        ("collect", "select", false),
        ("alias", "meta", false),
        ("cache", "async", false),
        ("loop", "meta", false),
        ("select", "failure", true),
        ("async", "collect", true),
        ("loop", "async", false),
        ("collect", "cache", true),
    ];

    /// <summary>Targeted higher-order compositions (three families, one with a failure).</summary>
    internal static readonly ImmutableArray<(string A, string B, string C, bool FailC)> SelectedTriples =
    [
        ("meta", "loop", "async", false),
        ("collect", "meta", "failure", true),
        ("alias", "cache", "select", false),
    ];

    /// <summary>
    /// Feature interactions the fixed corpus must exercise with at least one ACCEPTED case. These are
    /// semantic interactions built INTO productions (a META capture over a collecting target and a
    /// spread supply, a runtime alias of a captured callee, a waited loop step, …), not merely two
    /// unrelated fragments sharing a program.
    /// </summary>
    internal static readonly ImmutableArray<(string A, string B)> RequiredInteractions =
    [
        ("meta", "collect"), ("meta", "spread"), ("meta", "select"), ("meta", "alias"), ("meta", "forwarding"),
        ("meta", "loop"), ("meta", "async"), ("meta", "failure"), ("meta", "meta-refusal"),
        ("cache", "alias"), ("cache", "async"), ("cache", "forwarding"),
        ("collect", "failure"), ("collect", "spread"), ("collect", "empty-spread"), ("collect", "forwarding"),
        ("collect", "list-pattern"), ("collect", "sequence-pattern"), ("collect", "loop"),
        ("select", "failure"), ("select", "spread"), ("select", "list"),
        ("loop", "async"), ("loop", "failure"), ("loop", "clause-family"),
        ("alias", "shadowing"), ("alias", "nested-owner"), ("alias", "runtime-alias"),
        ("ctx-property", "meta"), ("ctx-property-double", "cache"), ("ctx-list", "loop"), ("ctx-if-true", "failure"),
        ("ctx-wrapper", "collect"), ("ctx-brace", "select"),
        ("loop", "condition-first"),
        ("collect", "nested-pattern"),
    ];

    internal static IReadOnlyList<SemanticCase> All() => [.. Systematic(), .. Seeded()];

    internal static IReadOnlyList<SemanticCase> Systematic() => [.. SystematicBuilders().Select(static b => b.Build())];

    /// <summary>
    /// One builder per systematic case, in corpus order. Each builder owns the chooser its case was
    /// always built from (<see cref="SemanticChooser.Systematic"/> at a fixed index) and the exact
    /// production sequence, so <see cref="Systematic"/> is unchanged while a reducer can rebuild ONE
    /// case from any chooser. Enumerating builders generates nothing.
    /// </summary>
    internal static IEnumerable<SemanticCaseBuilder> SystematicBuilders()
    {
        foreach (var family in SemanticGrammar.Families)
        {
            for (var j = 0; j < SystematicSuccessPerFamily; j++)
            {
                var at = j;
                var id = $"sys/{family}/{j}";
                yield return SemanticCaseBuilder.Systematic(id, at, g =>
                    Assemble(id, "systematic", null, at, g, [SemanticGrammar.Build(family, g, failing: false)], null, false));
            }

            for (var j = 0; j < SystematicFailuresPerFamily; j++)
            {
                var at = j;
                var id = $"sys/{family}-fail/{j}";
                yield return SemanticCaseBuilder.Systematic(id, at, g =>
                    Assemble(id, "systematic", null, at, g, [SemanticGrammar.Build(family, g, failing: true)], null, false));
            }
        }

        // Context sweep: every consumer around two different families.
        for (var context = 1; context < SemanticGrammar.Contexts.Length; context++)
        {
            for (var r = 0; r < 2; r++)
            {
                var family = SemanticGrammar.Families[(context * 2 + r) % SemanticGrammar.Families.Length];
                var at = context;
                var id = $"sys/context/{SemanticGrammar.Contexts[context]}/{family}";
                yield return SemanticCaseBuilder.Systematic(id, context + r, g =>
                {
                    var fragment = SemanticGrammar.Build(family, g, failing: false);
                    SemanticGrammar.ApplyContext(g, fragment, at);
                    return Assemble(id, "systematic", null, at, g, [fragment], null, false);
                });
            }
        }

        // Each invalid production inside an otherwise valid generated program.
        for (var p = 0; p < SemanticGrammar.InvalidProductions.Length; p++)
        {
            var at = p;
            var id = $"sys/invalid/{SemanticGrammar.InvalidProductions[p].Name}";
            yield return SemanticCaseBuilder.Systematic(id, at, g =>
            {
                var fragment = SemanticGrammar.Build(SemanticGrammar.Families[at], g, failing: false);
                return Assemble(id, "systematic", null, at, g, [fragment], at, false);
            });
        }

        for (var i = 0; i < SelectedPairs.Length; i++)
        {
            var (a, b, failB) = SelectedPairs[i];
            var at = i;
            var id = $"sys/pair/{a}+{b}{(failB ? "-fail" : "")}";
            yield return SemanticCaseBuilder.Systematic(id, at, g =>
                Assemble(id, "systematic", null, at, g,
                    [SemanticGrammar.Build(a, g, failing: false), SemanticGrammar.Build(b, g, failing: failB)], null, false));
        }

        for (var i = 0; i < SelectedTriples.Length; i++)
        {
            var (a, b, c, failC) = SelectedTriples[i];
            var at = i;
            var id = $"sys/triple/{a}+{b}+{c}{(failC ? "-fail" : "")}";
            yield return SemanticCaseBuilder.Systematic(id, at + 1, g =>
            {
                var first = SemanticGrammar.Build(a, g, failing: false);
                SemanticGrammar.ApplyContext(g, first, 1 + (at % 7));
                return Assemble(id, "systematic", null, at, g,
                    [first, SemanticGrammar.Build(b, g, failing: false), SemanticGrammar.Build(c, g, failing: failC)], null, false);
            });
        }

        // Bounded cancellation fixtures: the first suspended wait is cancelled.
        for (var i = 0; i < 2; i++)
        {
            var at = i;
            var id = $"sys/cancel/{i}";
            yield return SemanticCaseBuilder.Systematic(id, at, g =>
            {
                var waits = SemanticGrammar.Build("async", g, failing: false);
                var after = SemanticGrammar.Build(at == 0 ? "cache" : "meta", g, failing: false);
                return Assemble(id, "systematic", null, at, g, [waits, after], null, cancellation: true);
            });
        }

        // Additional named cases leave every existing recipe/seed unchanged.
        for (var variant = 0; variant < 3; variant++)
        {
            var at = variant;
            var whileId = $"sys/guard/while-condition-first/{variant}";
            yield return SemanticCaseBuilder.Systematic(whileId, at, g =>
                Assemble(whileId, "systematic", null, at, g, [SemanticGrammar.WhileGuard(g, at)], null, false));
            var nestedId = $"sys/guard/nested-pattern/{variant}";
            yield return SemanticCaseBuilder.Systematic(nestedId, at, nested =>
                Assemble(nestedId, "systematic", null, at, nested,
                    [SemanticGrammar.NestedPattern(nested, outerList: at == 1, failing: at == 2)], null, false));
        }
    }

    internal static IReadOnlyList<SemanticCase> Seeded()
    {
        var cases = new List<SemanticCase>();
        foreach (var seed in Seeds)
        {
            for (var index = 0; index < CasesPerSeed; index++)
                cases.Add(SeededCase(seed, index));
        }

        // A new, explicit recipe identity preserves every existing seed/<seed>/<index> source.
        foreach (var seed in Seeds.Take(2))
            for (var index = 0; index < 4; index++) cases.Add(NestedSeededCase(seed, index));

        return cases;
    }

    /// <summary>One seeded compositional case, rebuilt from (seed, index) alone.</summary>
    internal static SemanticCase SeededCase(ulong seed, int index) => SeededBuilder(seed, index).Build();

    internal static SemanticCase NestedSeededCase(ulong seed, int index) => NestedSeededBuilder(seed, index).Build();

    /// <summary>The builder of <c>seed/&lt;hex&gt;/&lt;index&gt;</c>: its own SplitMix64 stream by default, any chooser on request.</summary>
    internal static SemanticCaseBuilder SeededBuilder(ulong seed, int index)
    {
        var localId = "seed/" + seed.ToString("X", CultureInfo.InvariantCulture) + "/" + index.ToString(CultureInfo.InvariantCulture);
        return new SemanticCaseBuilder(localId, () => SemanticChooser.Seeded(seed, index), g =>
        {
            var count = 1 + g.Pick("compose.count", 3);
            var failAt = g.Chance("compose.failing", 35) ? g.Pick("compose.failAt", count) : -1;
            var fragments = new List<SemanticFragment>();
            var loopUsed = false;
            for (var i = 0; i < count; i++)
            {
                var family = SemanticGrammar.Families[g.Pick("compose.family", SemanticGrammar.Families.Length)];
                if (family == "loop" && loopUsed) family = "cache"; // loop evidence is per run: one loop fragment
                var fragment = SemanticGrammar.Build(family, g, failing: i == failAt);
                loopUsed |= fragment.IsLoop;
                var depth = g.Pick("compose.depth", 3);
                for (var d = 0; d < depth; d++)
                    SemanticGrammar.ApplyContext(g, fragment, 1 + g.Pick("compose.context", SemanticGrammar.Contexts.Length - 1));
                fragments.Add(fragment);
            }

            int? invalid = g.Chance("compose.invalid", 10) ? g.Pick("compose.invalidKind", SemanticGrammar.InvalidProductions.Length) : null;
            return Assemble(localId, "seeded", seed, index, g, fragments, invalid, cancellation: false);
        });
    }

    /// <summary>The builder of <c>seed-nested/&lt;hex&gt;/&lt;index&gt;</c>.</summary>
    internal static SemanticCaseBuilder NestedSeededBuilder(ulong seed, int index)
    {
        var localId = "seed-nested/" + seed.ToString("X", CultureInfo.InvariantCulture) + "/" + index.ToString(CultureInfo.InvariantCulture);
        return new SemanticCaseBuilder(localId, () => SemanticChooser.Seeded(seed, index), g =>
        {
            var fragment = SemanticGrammar.NestedPattern(g, g.Pick("nested.outer", 2) == 1, g.Chance("nested.fail", 25));
            var depth = 1 + g.Pick("nested.depth", 2);
            for (var d = 0; d < depth; d++)
                SemanticGrammar.ApplyContext(g, fragment, 1 + g.Pick("nested.context", SemanticGrammar.Contexts.Length - 1));
            return Assemble(localId, "seeded", seed, index, g, [fragment], null, false);
        });
    }

    /// <summary>
    /// Rebuilds one case from its durable id under THIS recipe version. Fails clearly for another
    /// version or an unknown id; never reinterprets an id with a different generator.
    /// </summary>
    internal static bool TryReconstruct(string caseId, int recipeVersion, out SemanticCase semanticCase, out string problem)
    {
        semanticCase = null!;
        if (!TryBuilder(caseId, recipeVersion, out var builder, out problem)) return false;
        semanticCase = builder.Build();
        return true;
    }

    /// <summary>
    /// The builder behind a durable recipe id (seeded, nested-seeded or systematic) under THIS recipe
    /// version, without generating any case. Reduced ids (<see cref="SemanticReduction.ReducedLocalPrefix"/>)
    /// are refused: a reduced case is rebuilt from its recorded choice sequence, never from a recipe id.
    /// </summary>
    internal static bool TryBuilder(string caseId, int recipeVersion, out SemanticCaseBuilder builder, out string problem)
    {
        builder = null!;
        if (recipeVersion != SemanticRecipe.RecipeVersion)
        {
            problem = $"recipe version {recipeVersion.ToString(CultureInfo.InvariantCulture)} is not built by this generator " +
                $"({SemanticRecipe.GeneratorId} v{SemanticRecipe.RecipeVersion.ToString(CultureInfo.InvariantCulture)}); replay the recorded source with --exact-source instead.";
            return false;
        }

        if (!caseId.StartsWith(SemanticRecipe.CasePrefix, StringComparison.Ordinal))
        {
            problem = $"case id '{caseId}' does not carry the '{SemanticRecipe.CasePrefix}' recipe prefix.";
            return false;
        }

        if (SemanticReduction.IsReducedCaseId(caseId))
        {
            problem = SemanticReduction.RecipeRefusal(caseId);
            return false;
        }

        var local = caseId[SemanticRecipe.CasePrefix.Length..];
        if (local.StartsWith("seed/", StringComparison.Ordinal) || local.StartsWith("seed-nested/", StringComparison.Ordinal))
        {
            var parts = local.Split('/');
            if (parts.Length != 3
                || !ulong.TryParse(parts[1], NumberStyles.HexNumber, CultureInfo.InvariantCulture, out var seed)
                || !int.TryParse(parts[2], NumberStyles.None, CultureInfo.InvariantCulture, out var index)
                || index < 0 || index >= 1_000_000)
            {
                problem = $"malformed seeded case id '{caseId}'.";
                return false;
            }

            builder = parts[0] == "seed-nested" ? NestedSeededBuilder(seed, index) : SeededBuilder(seed, index);
            problem = "";
            return true;
        }

        var found = SystematicBuilders().FirstOrDefault(b => string.Equals(b.CaseId, caseId, StringComparison.Ordinal));
        if (found is null)
        {
            problem = $"no systematic case '{caseId}' exists in recipe v{SemanticRecipe.RecipeVersion.ToString(CultureInfo.InvariantCulture)}.";
            return false;
        }

        builder = found;
        problem = "";
        return true;
    }

    // ── Assembly ────────────────────────────────────────────────────────────

    /// <summary>
    /// Composes fragments into one program and derives the composite expectation: root rows run in
    /// order; the first failing row ends the run (no later row's effect); a successful run's value
    /// is the sequence of row values followed by the root control row; an invalid declaration
    /// stops everything in the front end.
    /// </summary>
    private static SemanticBuiltCase Assemble(
        string localId,
        string tier,
        ulong? seed,
        int? index,
        SemanticGrammar.Gen g,
        IReadOnlyList<SemanticFragment> fragments,
        int? invalidProduction,
        bool cancellation)
    {
        var ordered = fragments.Where(f => !f.FailsAtExport).Concat(fragments.Where(f => f.FailsAtExport)).ToList();
        if (ordered.Count(f => f.Failing) > 1)
            throw new InvalidOperationException("A SEM-2B case composes at most one failing fragment.");
        if (ordered.Count(f => f.IsLoop) > 1)
            throw new InvalidOperationException("A SEM-2B case composes at most one loop fragment.");

        var decls = ordered.SelectMany(f => f.Decls).ToList();
        if (invalidProduction is { } production)
            decls.AddRange(SemanticGrammar.InvalidDeclarations(g, production));
        var program = g.Finish(new MScope(decls, ordered.Select(f => f.Row).ToList()));
        if (invalidProduction is null)
            program.ValidateNaming(); // a generator bug that changes binding identity fails HERE

        var events = new List<string>();
        var values = new List<Result>();
        string? failure = null;
        var paths = SemanticPath.None;
        var minimumCacheHits = 0;
        var ran = 0;
        foreach (var fragment in ordered)
        {
            ran++;
            events.AddRange(fragment.Events);
            paths |= fragment.Paths;
            minimumCacheHits += fragment.MinimumCacheHits;
            if (fragment.Failing)
            {
                failure = fragment.FailureCategory;
                break;
            }

            values.Add(fragment.Value ?? throw new InvalidOperationException($"fragment {fragment.Family} has no value"));
        }

        if (failure is not null && ordered.Skip(ran).Any(f => f.Events.Count > 0))
            paths |= SemanticPath.FirstFailureStops;
        if (events.Any(e => e.StartsWith("wait:", StringComparison.Ordinal)))
            paths |= SemanticPath.AsyncSuspension;

        // Dead fragments after the first failure cannot satisfy semantic coverage floors.
        var active = ordered.Take(ran).ToList();
        var families = active.Select(f => f.Family).Distinct().Order(StringComparer.Ordinal).ToImmutableArray();
        var features = new SortedSet<string>(active.SelectMany(f => f.Features), StringComparer.Ordinal);
        if (ordered.Count > 1)
            features.Add("compose:" + string.Join("+", ordered.Select(f => f.Family).Order(StringComparer.Ordinal)));

        SemanticExpectation expected;
        if (invalidProduction is { } p)
        {
            var (name, code, phase) = SemanticGrammar.InvalidProductions[p];
            expected = new SemanticExpectation(SemanticCaseKind.InvalidFrontEnd, null, null, null, code, phase, []);
            features.Add("invalid-" + name);
            paths = SemanticPath.None;
            minimumCacheHits = 0;
        }
        else if (failure is not null)
        {
            expected = new SemanticExpectation(SemanticCaseKind.ValidRuntimeFailure, null, null, failure, null, null, [.. events]);
        }
        else
        {
            values.Add(new Result.Atom(StructuralProgram.RootControl));
            expected = new SemanticExpectation(
                SemanticCaseKind.ValidSuccess, new Result.SequenceValue(values), values.Count, null, null, null, [.. events]);
        }

        if (cancellation)
        {
            var firstWait = events.FindIndex(e => e.StartsWith("wait:", StringComparison.Ordinal));
            if (firstWait < 0)
                throw new InvalidOperationException("A cancellation fixture needs a demanded wait.");
            expected = expected with { CancelledEventsPrefix = [.. events.Take(firstWait + 1)] };
            paths |= SemanticPath.Cancellation;
            features.Add("cancellation");
        }

        var members = new List<SemanticMember> { new(SemanticMember.BaseRole, program.Render()) };
        if (invalidProduction is null)
        {
            members.Add(new SemanticMember(SemanticMember.AlphaRenameRole, AlphaRename(program).Render()));
            if (program.Root.Decls.Count >= 2)
            {
                var reordered = program with { Root = new MScope(program.Root.Decls.Reverse().ToList(), program.Root.Rows) };
                reordered.ValidateNaming();
                members.Add(new SemanticMember(SemanticMember.DeclarationReorderRole, reordered.Render()));
            }
        }

        var caseId = SemanticRecipe.CasePrefix + localId;
        var semanticCase = new SemanticCase(
            caseId, tier, seed, index, expected, [.. members], families, [.. features], paths, minimumCacheHits,
            Profiles(tier, index ?? 0, expected, invalidProduction is not null, cancellation));
        return new SemanticBuiltCase(semanticCase, ordered.Count, program.AllDeclarations().Count);
    }

    /// <summary>
    /// Renames every declaration BY NAME to a fresh pool (so deliberate shadow pairs keep sharing a
    /// name) and re-validates the binding graph: the transformation provably preserves binding
    /// identity, or generation fails.
    /// </summary>
    internal static StructuralProgram AlphaRename(StructuralProgram program)
    {
        var map = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var (_, name) in program.Names.OrderBy(pair => pair.Key.Id))
        {
            if (!map.ContainsKey(name))
                map[name] = "w" + (map.Count + 1).ToString(CultureInfo.InvariantCulture);
        }

        var renamed = program with { Names = program.Names.ToDictionary(pair => pair.Key, pair => map[pair.Value]) };
        renamed.ValidateNaming();
        return renamed;
    }

    private static ImmutableArray<string> Profiles(string tier, int index, SemanticExpectation expected, bool invalid, bool cancellation)
    {
        if (invalid)
            return [SemanticProfiles.SyncOptimized, SemanticProfiles.EngineRun, SemanticProfiles.EngineRunAsync];

        var systematic = tier == "systematic";
        var waits = expected.Events.Any(e => e.StartsWith("wait:", StringComparison.Ordinal));
        var profiles = new List<string> { SemanticProfiles.SyncGeneric, SemanticProfiles.SyncOptimized, SemanticProfiles.AsyncTwin };
        if (systematic || index % 3 == 0) profiles.Add(SemanticProfiles.EngineRun);
        if (waits || index % 4 == 1) profiles.Add(SemanticProfiles.EngineRunAsync);
        if (systematic || index % 3 == 1) profiles.Add(SemanticProfiles.SyncOptimizedRerun);
        if (cancellation)
        {
            profiles.Add(SemanticProfiles.AsyncTwinCancel);
            profiles.Add(SemanticProfiles.EngineRunAsyncCancel);
        }

        return [.. profiles];
    }
}
