using KatLang.Evaluation;

namespace KatLang.Tests.ExposureCensus;

/// <summary>One census finding: the check, its class, the case or family, the reader and a detail.</summary>
internal sealed record CensusGap(string Check, string Class, string Id, string Reader, string Detail)
{
    public string Line => $"{Check}\t{Class}\t{Id}\t{Reader}\t{Detail}";

    public static CensusGap? Parse(string line)
    {
        var parts = line.Split('\t');
        return parts.Length == 5 ? new CensusGap(parts[0], parts[1], parts[2], parts[3], parts[4]) : null;
    }
}

/// <summary>
/// A tree the model check evaluates in Lean: a real program (role <c>real</c>) or a host-built copy with
/// one requirement removed (role <c>copy-needed</c>, <c>copy-unneeded</c> or <c>copy-undetermined</c>,
/// after O's verdict), with the C# outcome Lean must reproduce (M4).
/// </summary>
internal sealed record CensusLeanItem(string Id, string CaseId, string CopyKey, string Role, Algorithm.User Tree, string CSharpOutcome);

internal sealed class CensusCaseResult
{
    public required CensusCase Case { get; init; }
    public string? Skipped { get; init; }
    public List<CensusGap> Gaps { get; } = [];

    /// <summary>
    /// The impossible-check class (see <see cref="CensusRunner.Run"/>): observations that are no gap. An exported
    /// reader's escaped read fails at a member whose check can never pass where the evaluator performs it.
    /// </summary>
    public List<CensusGap> Impossible { get; } = [];

    /// <summary>Every published requirement no level of its declaring chain can supply (<c>path: name@depth</c>).</summary>
    public List<string> UnsuppliedRequirements { get; } = [];
    public List<CensusLeanItem> Lean { get; } = [];
    public Dictionary<string, string> Outcomes { get; } = new(StringComparer.Ordinal);
    public Dictionary<string, string> Metadata { get; } = new(StringComparer.Ordinal);
    public bool InsideWorks { get; set; }

    /// <summary>A module cell's observed provider verdict (check P; <see cref="CensusGrid.ExpectedProviderVerdict"/>), else null.</summary>
    public string? ProviderVerdict { get; set; }
}

/// <summary>
/// Evaluates census cases: parses each probe program, evaluates it on every route, and applies the
/// under-charge check U and the over-charge check O (brief section 2), for a deconstruction cell the twin
/// check T (a refusal inside the owner's own call is neither U nor O), for a callable <c>rt-alg</c> cell the
/// static-route check R, and for a module cell the provider check P (its provider verdict and its provider twin). A case
/// that loads modules is parsed through the asynchronous front end over a deterministic in-memory server of its own
/// sources, and its engine routes are the asynchronous ones. Engine disagreements are findings of their own class. The
/// model check (M) consumes <see cref="CensusCaseResult.Lean"/>, whose trees hold the loaded module graph as parsed.
/// </summary>
internal static class CensusRunner
{
    private static readonly HostOperations AsyncRoute = HostOperations.Create(HostOperation.CreateAsync(
        "UnusedCensusRoute", static (_, _) => throw new InvalidOperationException("The census route marker must never run.")));

    public const string Inside5 = "F(5)";
    public const string Inside7 = "F(7)";
    public const string SameRun = "F(5), F(7)";

    public static string Render(EvalResult<Result> result)
    {
        if (!result.IsError) return "ok " + SemanticExplorerHarness.Neutral(result.Value);
        var inner = result.Error;
        while (inner is EvalError.WithContext context) inner = context.Inner;
        var category = SemanticExplorerHarness.ErrorCategory(result.Error);
        return inner switch
        {
            EvalError.LocalOnlyProperty local => $"err {category}:{local.PropertyName}",
            EvalError.UnknownName unknown => $"err {category}:{unknown.Name}",
            EvalError.UnknownProperty property => $"err {category}:{property.PropertyName}",
            _ => $"err {category}",
        };
    }

    internal static string RenderEngine(RunResult result) => result switch
    {
        RunResult.Success success => "ok " + SemanticExplorerHarness.Neutral(success.Value),
        RunResult.EvalFailure failure => string.Join(" | ", failure.Errors.Select(e => e.Source is { } source
            ? Render(EvalResult<Result>.Err(source)) : $"diagnostic {e.Code}")),
        _ => result.GetType().Name,
    };

    /// <summary>The three evaluator routes over a tree; disagreement is reported, the sync outcome returned.</summary>
    public static async Task<(string Outcome, string? Disagreement)> EvaluateTree(Algorithm.User root)
    {
        var expression = new Expr.AlgorithmExpr(root);
        var sync = Render(Evaluator.Run(expression));
        var ordinary = Render(await Evaluator.RunAsync(expression));
        var forced = Render(await Evaluator.RunAsync(expression, AsyncRoute, null, null, default));
        return (sync, sync == ordinary && sync == forced ? null : $"sync={sync}; async={ordinary}; forced-async={forced}");
    }

    private static async Task<string?> EngineDisagreement(CensusCase @case, string source, string treeOutcome)
    {
        if (@case.Modules is not null)
        {
            // Source loading is asynchronous only: the engine routes of a module case are RunAsync over a fresh server,
            // with synchronous and with asynchronous host operations.
            var loaded = RenderEngine(await KatLangEngine.RunAsync(source, ModuleServer(@case).Options()));
            var loadedForced = RenderEngine(await KatLangEngine.RunAsync(source, ModuleServer(@case).Options(AsyncRoute)));
            return loaded == treeOutcome && loadedForced == treeOutcome
                ? null
                : $"tree={treeOutcome}; RunAsync={loaded}; RunAsync(async)={loadedForced}";
        }
        var run = RenderEngine(KatLangEngine.Run(source));
        var ordinary = RenderEngine(await KatLangEngine.RunAsync(source));
        var forced = RenderEngine(await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = AsyncRoute }));
        return run == treeOutcome && ordinary == treeOutcome && forced == treeOutcome
            ? null
            : $"tree={treeOutcome}; Run={run}; RunAsync={ordinary}; RunAsync(async)={forced}";
    }

    /// <summary>A fresh deterministic in-memory module server over exactly the case's sources (unknown URLs fail).</summary>
    internal static ModuleRouteAgreement.Modules ModuleServer(CensusCase @case)
        => new([.. (@case.Modules ?? throw new ArgumentException($"The case loads no modules: {@case.Id}", nameof(@case)))
            .Select(m => (m.Key, m.Value))]);

    /// <summary>
    /// The front end of one probe source: the synchronous parser, or for a case that loads modules the asynchronous front
    /// end over a fresh server of its sources. Returns the error codes, or null for a clean parse.
    /// </summary>
    private static async Task<string?> Prescreen(CensusCase @case, string source)
    {
        var result = @case.Modules is null ? Parser.Parse(source) : await Parser.ParseAsync(source, ModuleServer(@case).Options());
        return result.HasErrors ? ErrorCodes(result) : null;
    }

    internal static string ErrorCodes(ParseResult result)
        => string.Join(",", result.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)
            .Select(d => d.Code.ToString()).Distinct().Order(StringComparer.Ordinal));

    /// <summary>
    /// The clean tree of one probe source through the repository's explicit clean-source assertion boundary
    /// (<see cref="SourceProvenance.ParseValid"/>, or <see cref="SourceProvenance.ParseValidAsync"/> over a fresh module
    /// server), with the URLs that server was asked for (empty for a case that loads nothing).
    /// </summary>
    internal static async Task<(Algorithm.User Root, IReadOnlyList<string> Fetched)> ParseValid(CensusCase @case, string source)
    {
        if (@case.Modules is null) return (SourceProvenance.ParseValid(source).Root, []);
        var server = ModuleServer(@case);
        var root = (await SourceProvenance.ParseValidAsync(source, server.Options())).Root;
        lock (server.Fetches)
            return (root, server.Fetches.Keys.Order(StringComparer.Ordinal).ToArray());
    }

    /// <summary>
    /// The distinct loaded-module identities of a tree: every module root (<c>IsModuleRoot</c>) reachable through
    /// properties, opens, rows and expressions, counted by its declaration (Q-32 I-U: one canonical URL is one module).
    /// </summary>
    internal static int ModuleIdentities(Algorithm root)
    {
        var modules = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node)) continue;
            if (node is Algorithm { IsModuleRoot: true } module)
                modules.Add(module.Declaration ?? throw new InvalidDataException("A loaded module has no declaration identity."));
            for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++) pending.Push(child);
        }
        return modules.Count;
    }

    internal static Property? Find(Algorithm root, IReadOnlyList<string> path)
    {
        Algorithm current = root;
        Property? found = null;
        foreach (var name in path)
        {
            IReadOnlyList<Property> properties = current switch
            {
                Algorithm.User user => user.Properties,
                Algorithm.Alias alias => alias.Properties,
                _ => [],
            };
            found = properties.FirstOrDefault(p => p.Name == name);
            if (found is null) return null;
            current = found.Value;
        }
        return found;
    }

    internal static Algorithm.User Replace(Algorithm.User root, IReadOnlyList<string> path, Func<Property, Property> change)
        => (Algorithm.User)ReplaceIn(root, path, 0, change);

    private static Algorithm ReplaceIn(Algorithm algorithm, IReadOnlyList<string> path, int index, Func<Property, Property> change)
    {
        Property Step(Property property)
            => property.Name != path[index] ? property
                : index == path.Count - 1 ? change(property)
                : property with { Value = ReplaceIn(property.Value, path, index + 1, change) };
        return algorithm switch
        {
            Algorithm.User user => user with { Properties = user.Properties.Select(Step).ToArray() },
            Algorithm.Alias alias => alias with { Properties = alias.Properties.Select(Step).ToArray() },
            _ => throw new InvalidOperationException($"No property container at {string.Join(".", path)}"),
        };
    }

    internal static IReadOnlyList<CapturedParameterRequirement> Requirements(Property property)
        => property.CaptureRequirements is { } requirements
            ? requirements
            : property.RequiredAncestorParameters.Select(name => new CapturedParameterRequirement(name, -1)).ToArray();

    internal static string Describe(Property? property)
        => property is null ? "absent"
            : property.Exposure == PropertyExposure.Exported ? "exported"
            : $"{property.Exposure}[{string.Join(",", Requirements(property).Select(Requirement))}]";

    internal static string Requirement(CapturedParameterRequirement r) => $"{r.Name}@{r.OwnerDepth}";

    /// <summary>The property with requirement <paramref name="removed"/> dropped (exported once none remains).</summary>
    internal static Property Without(Property property, CapturedParameterRequirement removed)
    {
        var remaining = Requirements(property).Where(r => r != removed).ToArray();
        if (remaining.Length == 0)
            return property with { Exposure = PropertyExposure.Exported, RequiredAncestorParameters = [], CaptureRequirements = null };
        return property with
        {
            RequiredAncestorParameters = remaining.Select(r => r.Name).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray(),
            CaptureRequirements = property.CaptureRequirements is null ? null : remaining,
        };
    }

    private static bool Consistent(string same, string five, string seven, out bool differ)
    {
        differ = false;
        if (!same.StartsWith("ok ", StringComparison.Ordinal) || !five.StartsWith("ok ", StringComparison.Ordinal)
            || !seven.StartsWith("ok ", StringComparison.Ordinal))
            return false;
        differ = same != $"ok S[{five[3..]}, {seven[3..]}]";
        return true;
    }

    /// <summary>
    /// THE INVARIANT of owner decision Q1 (2026-11-14): no declaration of an elaborated source tree publishes a
    /// requirement that no level of its declaring chain can supply, either an owner-qualified requirement with a
    /// negative owner depth or a names-only requirement no enclosing level binds. Returns each one as
    /// <c>path: name@depth</c>; the walk passes every algorithm of the tree, those written inside expressions included.
    /// </summary>
    internal static List<string> UnsuppliedRequirements(Algorithm root)
    {
        var found = new List<string>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<(object Node, string Path, EnclosingNames Bound)>();
        pending.Push((root, "root", EnclosingNames.None));
        while (pending.TryPop(out var item))
        {
            if (!seen.Add(item.Node)) continue;
            switch (item.Node)
            {
                case Algorithm.Conditional conditional:
                    foreach (var open in conditional.Opens) pending.Push((open, item.Path + "#open", item.Bound));
                    for (var b = 0; b < conditional.Branches.Count; b++)
                        pending.Push((conditional.Branches[b].Body, $"{item.Path}#{b}",
                            item.Bound.Push(conditional.Branches[b].Pattern.BoundNames())));
                    break;
                case Algorithm algorithm:
                {
                    var bound = item.Bound.Push(algorithm is Algorithm.User user ? user.Params : []);
                    foreach (var property in algorithm.Properties)
                    {
                        var path = $"{item.Path}.{property.Name}";
                        if (property.CaptureRequirements is { } captures)
                        {
                            foreach (var capture in captures)
                                if (capture.OwnerDepth < 0) found.Add($"{path}: {Requirement(capture)}");
                        }
                        else
                        {
                            foreach (var name in property.RequiredAncestorParameters)
                                if (!bound.Binds(name)) found.Add($"{path}: {name}@names-only");
                        }
                        pending.Push((property.Value, path, bound));
                    }
                    foreach (var open in algorithm.Opens) pending.Push((open, item.Path + "#open", bound));
                    foreach (var row in algorithm.Output) pending.Push((row, item.Path + "#row", bound));
                    break;
                }
                default:
                    // An expression, an argument bundle or a pattern: the walk continues through whatever it nests.
                    for (var i = 0; AstStructuralPreflight.TryGetChild(item.Node, i, out var child); i++)
                        pending.Push((child, item.Path, item.Bound));
                    break;
            }
        }
        found.Sort(StringComparer.Ordinal);
        return found;
    }

    /// <summary>The parameter names of the levels enclosing a position, innermost first.</summary>
    internal sealed class EnclosingNames
    {
        public static readonly EnclosingNames None = new([], null);
        private readonly IReadOnlyList<string> _names;
        private readonly EnclosingNames? _outer;

        private EnclosingNames(IReadOnlyList<string> names, EnclosingNames? outer) => (_names, _outer) = (names, outer);

        public EnclosingNames Push(IReadOnlyList<string> names) => new(names, this);

        public bool Binds(string name)
        {
            for (var level = this; level is not null; level = level._outer)
                if (level._names.Contains(name, StringComparer.Ordinal)) return true;
            return false;
        }
    }

    /// <summary>
    /// The outcomes of the three inside probes of a case on the synchronous route (the comparison with HEAD
    /// a4b545e8 reads them; <see cref="Run"/> checks the other routes), or null when a probe does not parse cleanly.
    /// </summary>
    public static async Task<IReadOnlyList<(string Label, string Outcome)>?> InsideOutcomes(CensusCase @case)
    {
        var outcomes = new List<(string, string)>(3);
        foreach (var (label, row) in new[] { ("in5", Inside5), ("in7", Inside7), ("same", SameRun) })
        {
            var source = @case.Body + row + "\n";
            if (await Prescreen(@case, source) is not null) return null;
            var (root, _) = await ParseValid(@case, source);
            outcomes.Add((label, Render(Evaluator.Run(new Expr.AlgorithmExpr(root)))));
        }
        return outcomes;
    }

    private static (string Label, string Source)[] ProbeSources(CensusCase @case)
    {
        var rows = new List<(string Label, string Row)> { ("in5", Inside5), ("in7", Inside7), ("same", SameRun) };
        rows.AddRange(@case.Readers.Select(r => ($"esc:{r.Label}", r.Escaped)));
        return rows.Select(r => (r.Label, Source: @case.Body + r.Row + "\n")).ToArray();
    }

    /// <summary>Every probe program of a case, or null when one fails elaboration.</summary>
    public static async Task<IReadOnlyList<(string Label, string Source)>?> Probes(CensusCase @case)
    {
        var sources = ProbeSources(@case);
        foreach (var (_, source) in sources)
            if (await Prescreen(@case, source) is not null) return null;
        return sources;
    }
    /// <summary>
    /// Runs every check of one case. <paramref name="hostBuilt"/> is the harness's own seam: it rewrites each probe's
    /// front-end tree before the checks read it (a host-built tree, as the O check's copies are), so a negative control
    /// can show the census a tree the front end no longer produces. The engine comparison, which runs the SOURCE, is
    /// skipped for such a tree.
    /// </summary>
    public static async Task<CensusCaseResult> Run(CensusCase @case, bool collectLean, Func<Algorithm.User, Algorithm.User>? hostBuilt = null)
    {
        var probes = ProbeSources(@case);
        var parsed = new Dictionary<string, Algorithm.User>(StringComparer.Ordinal);
        var sources = new Dictionary<string, string>(StringComparer.Ordinal);
        var fetched = new Dictionary<string, IReadOnlyList<string>>(StringComparer.Ordinal);
        foreach (var (label, source) in probes)
        {
            if (await Prescreen(@case, source) is { } codes)
            {
                var skipped = new CensusCaseResult { Case = @case, Skipped = label == "in5" ? codes : $"{codes} (probe {label})" };
                // P: a module cell parses exactly when its provider twin does, so a missing download or a module cell
                // dropped from the census is a gap, never a silent skip.
                if (@case.Kind == "module" && await Probes(CensusGrid.ModuleTwin(@case)) is not null)
                    skipped.Gaps.Add(new CensusGap("P", "module-validity-differs", @case.Id, "-", $"{label}: module cell {codes}; provider twin parses cleanly"));
                return skipped;
            }
            // The pre-screen above keeps diagnostics for skipped cells; every evaluated source then
            // crosses the repository's explicit clean-source assertion boundary.
            var (root, urls) = await ParseValid(@case, source);
            parsed[label] = hostBuilt is null ? root : hostBuilt(root);
            sources[label] = source;
            fetched[label] = urls;
        }

        var outcome = new CensusCaseResult { Case = @case };
        outcome.UnsuppliedRequirements.AddRange(UnsuppliedRequirements(parsed["in5"]));
        foreach (var reader in @case.Readers)
        {
            var described = Describe(Find(parsed["in5"], reader.Path));
            outcome.Metadata[reader.Label] = described;
            foreach (var (label, _) in probes)
                if (Describe(Find(parsed[label], reader.Path)) != described)
                    outcome.Gaps.Add(new CensusGap("H", "harness-metadata-varies-with-probe", @case.Id, reader.Label, label));
        }

        foreach (var (label, _) in probes)
        {
            var (result, disagreement) = await EvaluateTree(parsed[label]);
            outcome.Outcomes[label] = result;
            if (disagreement is not null)
                outcome.Gaps.Add(new CensusGap("E", "engine-disagreement", @case.Id, "-", $"{label}: {disagreement}"));
            else if (hostBuilt is null && await EngineDisagreement(@case, sources[label], result) is { } engine)
                outcome.Gaps.Add(new CensusGap("E", "engine-disagreement", @case.Id, "-", $"{label}: {engine}"));
            if (collectLean)
                outcome.Lean.Add(new CensusLeanItem($"{@case.Id}#real#{label}", @case.Id, "real", "real", parsed[label], result));
        }

        var o = outcome.Outcomes;
        outcome.InsideWorks = o["in5"].StartsWith("ok ", StringComparison.Ordinal) && o["in7"].StartsWith("ok ", StringComparison.Ordinal);

        // U: an exported reader is under-charged when the same run gives other values than separate runs (U1),
        // or its escaped read alone fails on an access check (U2).
        if (Consistent(o["same"], o["in5"], o["in7"], out var differ) && differ)
            outcome.Gaps.Add(new CensusGap("U", "under-charge-wrong-value", @case.Id, "-", $"same={o["same"]}; separate={o["in5"]} / {o["in7"]}"));
        foreach (var reader in @case.Readers)
        {
            var property = Find(parsed["in5"], reader.Path);
            if (property is null || property.Exposure != PropertyExposure.Exported) continue;
            var escaped = o[$"esc:{reader.Label}"];
            // U2 is the brief's escaped-access check on EVERY valid program. An unrelated failure in F
            // does not remove this tree from the source-domain census; keep that context in the detail.
            if (!escaped.StartsWith("err localOnlyProperty", StringComparison.Ordinal)) continue;
            // THE IMPOSSIBLE-CHECK CLASS (owner decision Q1, 2026-11-14): the escaped read fails at a member whose
            // check can never pass where the evaluator performs it, so leaving the reader exported is correct and the
            // observation is no gap. Two independent means decide it and must agree: the grid's own description of
            // the cell, and the behavior (every inside probe fails at that same member). A disagreement is a gap of
            // its own class, never silently classified.
            var byGrid = escaped == $"err localOnlyProperty:{CensusGrid.ImpossibleMember(@case)}";
            var byBehavior = o["in5"] == escaped && o["in7"] == escaped && o["same"] == escaped;
            if (byGrid && byBehavior)
                outcome.Impossible.Add(new CensusGap("U", "impossible-check", @case.Id, reader.Label, escaped));
            else if (byGrid != byBehavior)
                outcome.Gaps.Add(new CensusGap("U", "impossible-check-disagreement", @case.Id, reader.Label,
                    $"{escaped}; grid={(byGrid ? "impossible" : "possible")}; inside={o["in5"]} / {o["in7"]} / {o["same"]}"));
            else
                outcome.Gaps.Add(new CensusGap("U", "under-charge-masked-access", @case.Id, reader.Label,
                    outcome.InsideWorks ? escaped : $"{escaped}; inside={o["in5"]}"));
        }

        // O: drop each requirement of a local-only reader on a host-built copy and evaluate the copy directly.
        foreach (var reader in @case.Readers)
        {
            var property = Find(parsed["in5"], reader.Path);
            if (property is null || property.Exposure != PropertyExposure.LocalOnlyCapturedAncestorParameters) continue;
            foreach (var requirement in Requirements(property).Distinct())
            {
                var copyLabels = new[] { "in5", "in7", "same", $"esc:{reader.Label}" };
                var copies = copyLabels.ToDictionary(l => l, l => Replace(parsed[l], reader.Path, p => Without(p, requirement)), StringComparer.Ordinal);
                var results = new Dictionary<string, string>(StringComparer.Ordinal);
                foreach (var label in copyLabels)
                {
                    var (result, disagreement) = await EvaluateTree(copies[label]);
                    results[label] = result;
                    if (disagreement is not null)
                        outcome.Gaps.Add(new CensusGap("E", "engine-disagreement", @case.Id, reader.Label, $"copy -{Requirement(requirement)} {label}: {disagreement}"));
                }
                var escaped = results[$"esc:{reader.Label}"];
                var consistent = Consistent(results["same"], results["in5"], results["in7"], out var valuesDiffer);
                string verdict;
                // Apply the specified verdict to the copy, including when the original's inside call fails.
                if (escaped.StartsWith("err localOnlyProperty", StringComparison.Ordinal)
                    || escaped == $"err unknownName:{requirement.Name}"
                    || (consistent && valuesDiffer))
                    verdict = "needed";
                else if (escaped.StartsWith("ok ", StringComparison.Ordinal) && consistent && !valuesDiffer)
                    verdict = "unneeded";
                else
                    verdict = "undetermined";
                var detail = $"r={Requirement(requirement)}";
                if (verdict == "unneeded")
                    outcome.Gaps.Add(new CensusGap("O", "over-charge", @case.Id, reader.Label, detail));
                else if (verdict == "undetermined")
                    outcome.Gaps.Add(new CensusGap("O", "undetermined", @case.Id, reader.Label,
                        $"{detail}; escaped={escaped}; same={results["same"]}; separate={results["in5"]} / {results["in7"]}"));
                if (collectLean)
                    foreach (var label in copyLabels)
                        outcome.Lean.Add(new CensusLeanItem($"{@case.Id}#copy:{reader.Label}:{Requirement(requirement)}#{label}",
                            @case.Id, $"{reader.Label}:{Requirement(requirement)}", "copy-" + verdict, copies[label], results[label]));
            }
        }

        // T: a deconstruction cell against its rows twin (CensusGrid.DeconstructionTwin), always built from SOURCE, so a
        // host-built cell is compared with the front end's own twin.
        if (@case.Kind == "grid" && @case.Dims.Count > 0 && @case.Dim("pos") == "deconstruction")
        {
            var (twinOutcomes, twinMetadata) = TwinFacts(CensusGrid.DeconstructionTwin(@case), probes.Select(p => p.Label).ToArray());
            outcome.Gaps.AddRange(TwinDifferences(@case.Id, outcome.Outcomes, outcome.Metadata, twinOutcomes, twinMetadata));
        }

        // R: every callable rt-alg cell against its static-route twin (CensusGrid.StaticRouteTwin), also built from SOURCE.
        // Include open positions: although OD-C opens the runtime reference's own namespace, this fixture's valid cells
        // must still agree with the static route on their outcomes and reader metadata.
        if (HasStaticRouteTwin(@case))
        {
            var (twinOutcomes, twinMetadata) = TwinFacts(CensusGrid.StaticRouteTwin(@case), probes.Select(p => p.Label).ToArray());
            outcome.Gaps.AddRange(RouteDifferences(@case.Id, outcome.Outcomes, outcome.Metadata, twinOutcomes, twinMetadata));
        }

        // P: a module cell's provider verdict (CensusGrid.ExpectedProviderVerdict), the same on every probe, and for one module
        // its provider twin, the same cell with `Other` as the second provider, built from SOURCE: one module is one provider
        // of the text Other holds, so every probe and every reader's metadata must equal the twin's. The control's qualified
        // fixture reads `ModA` lexically, a different lookup, so it has its verdict and the other checks but no twin.
        if (@case.Kind == "module")
        {
            var unqualified = CensusGrid.ModuleUnqualifiedRead(@case);
            var errors = unqualified == @case ? null : await Prescreen(unqualified, unqualified.Body + Inside5 + "\n");
            var verdicts = parsed.ToDictionary(pair => pair.Key,
                pair => ProviderVerdict(@case, pair.Value, fetched[pair.Key], errors), StringComparer.Ordinal);
            outcome.ProviderVerdict = verdicts["in5"];
            var expected = CensusGrid.ExpectedProviderVerdict(@case);
            if (outcome.ProviderVerdict != expected)
                outcome.Gaps.Add(new CensusGap("P", "provider-verdict-differs", @case.Id, "-", $"expected {expected}; observed {outcome.ProviderVerdict}"));
            if (verdicts.Values.Any(verdict => verdict != outcome.ProviderVerdict))
                outcome.Gaps.Add(new CensusGap("P", "provider-verdict-differs", @case.Id, "-",
                    "probes differ: " + string.Join("; ", verdicts.Select(v => $"{v.Key}: {v.Value}"))));
            if (HasModuleTwin(@case))
            {
                var (twinOutcomes, twinMetadata) = TwinFacts(CensusGrid.ModuleTwin(@case), probes.Select(p => p.Label).ToArray());
                outcome.Gaps.AddRange(ModuleTwinDifferences(@case.Id, outcome.Outcomes, outcome.Metadata, twinOutcomes, twinMetadata));
            }
        }
        return outcome;
    }

    /// <summary>
    /// Read the production lookup for X at the innermost reader, including the selected branch of a clause family.
    /// A holder can occur in the loaded graph even if its module supplies no name at this open level.
    /// </summary>
    private static string ProviderVerdict(CensusCase @case, Algorithm.User root, IReadOnlyList<string> fetched, string? errors)
    {
        var scope = ElaboratedScopeLookup.CreateScope(root);
        Algorithm reader = root;
        foreach (var name in @case.Readers.MaxBy(r => r.Path.Count)!.Path)
        {
            reader = reader.Properties.Single(p => p.Name == name).Value;
            scope = ElaboratedScopeLookup.CreateScope(reader, scope);
        }
        if (reader is Algorithm.Conditional family)
        {
            var branch = family.Branches[0];
            scope = ElaboratedScopeLookup.CreateScope(branch.Body, scope, branchPattern: branch.Pattern);
        }
        var providers = ElaboratedScopeLookup.SelectFirstOpenLevel(scope, "X").Providers();
        var modules = providers.Count(p => p.Target.IsModuleRoot);
        var count = modules == providers.Count ? $"{modules}" : $"{providers.Count} ({modules} loaded)";
        return $"providers {count}; identities {ModuleIdentities(root)}; fetched {string.Join(",", fetched)}; unqualified {errors ?? "clean"}";
    }

    /// <summary>
    /// Check P's twin verdict: every probe outcome and every reader's metadata of a module cell equal its provider twin's,
    /// one gap per differing probe or reader (class <c>module-twin-differs</c>); no difference is exempt.
    /// </summary>
    internal static List<CensusGap> ModuleTwinDifferences(string id, IReadOnlyDictionary<string, string> outcomes, IReadOnlyDictionary<string, string> metadata,
        IReadOnlyDictionary<string, string> twinOutcomes, IReadOnlyDictionary<string, string> twinMetadata)
        => PairDifferences("P", "module-twin-differs", "module", "twin", id, outcomes, metadata, twinOutcomes, twinMetadata);

    /// <summary>Whether check P compares the case with its provider twin: every module cell of one module (not the control).</summary>
    internal static bool HasModuleTwin(CensusCase @case) => @case.Kind == "module" && @case.Dim("module") != "two-urls";

    /// <summary>Whether check R compares the case with its static-route twin: every <c>rt-alg-call</c> grid cell.</summary>
    internal static bool HasStaticRouteTwin(CensusCase @case)
        => @case.Kind == "grid" && @case.Dims.Count > 0 && @case.Dim("head") == "rt-alg-call";

    /// <summary>
    /// Check R's verdict: every probe outcome and every reader's metadata of a callable <c>rt-alg</c> cell equal its
    /// static-route twin's, one gap per differing probe or reader (class <c>static-route-differs</c>); no difference is
    /// exempt.
    /// </summary>
    internal static List<CensusGap> RouteDifferences(string id, IReadOnlyDictionary<string, string> outcomes, IReadOnlyDictionary<string, string> metadata,
        IReadOnlyDictionary<string, string> twinOutcomes, IReadOnlyDictionary<string, string> twinMetadata)
        => PairDifferences("R", "static-route-differs", "runtime", "static", id, outcomes, metadata, twinOutcomes, twinMetadata);

    // The shared verdict of checks R, T and P: one gap per probe whose outcome differs from the twin's (a probe the twin lacks
    // is "absent", never a match) and per reader whose metadata differs, each spelled with the pair's two names.
    private static List<CensusGap> PairDifferences(string check, string @class, string cellName, string twinName, string id,
        IReadOnlyDictionary<string, string> outcomes, IReadOnlyDictionary<string, string> metadata,
        IReadOnlyDictionary<string, string> twinOutcomes, IReadOnlyDictionary<string, string> twinMetadata)
    {
        var gaps = new List<CensusGap>();
        foreach (var (label, cell) in outcomes.OrderBy(o => o.Key, StringComparer.Ordinal))
        {
            var twin = twinOutcomes.TryGetValue(label, out var value) ? value : "absent";
            if (twin != cell)
                gaps.Add(new CensusGap(check, @class, id, "-", $"{label}: {cellName}={cell}; {twinName}={twin}"));
        }
        foreach (var (reader, cell) in metadata.OrderBy(m => m.Key, StringComparer.Ordinal))
        {
            var twin = twinMetadata.TryGetValue(reader, out var value) ? value : "absent";
            if (twin != cell)
                gaps.Add(new CensusGap(check, @class, id, reader, $"metadata: {cellName}={cell}; {twinName}={twin}"));
        }
        return gaps;
    }

    /// <summary>
    /// The facts check T compares of a rows twin, on the synchronous route (check E covers the cell's routes): every
    /// probe's outcome and every reader's metadata, read from the <c>in5</c> probe as for the cell. A probe that does not
    /// parse cleanly has the outcome <c>invalid</c>, which no evaluated cell outcome equals.
    /// </summary>
    internal static (Dictionary<string, string> Outcomes, Dictionary<string, string> Metadata) TwinFacts(CensusCase twin, IReadOnlyList<string> labels)
    {
        var rows = new Dictionary<string, string>(StringComparer.Ordinal) { ["in5"] = Inside5, ["in7"] = Inside7, ["same"] = SameRun };
        foreach (var reader in twin.Readers) rows[$"esc:{reader.Label}"] = reader.Escaped;
        var outcomes = new Dictionary<string, string>(StringComparer.Ordinal);
        var metadata = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var label in labels)
        {
            var source = twin.Body + rows[label] + "\n";
            if (Parser.Parse(source).HasErrors)
            {
                outcomes[label] = "invalid";
                continue;
            }
            var root = SourceProvenance.ParseValid(source).Root;
            if (label == "in5")
                foreach (var reader in twin.Readers)
                    metadata[reader.Label] = Describe(Find(root, reader.Path));
            outcomes[label] = Render(Evaluator.Run(new Expr.AlgorithmExpr(root)));
        }
        return (outcomes, metadata);
    }

    /// <summary>
    /// Check T's verdict: every probe outcome and every reader's metadata of a deconstruction cell equal its rows twin's.
    /// One gap per differing probe or reader (class <c>deconstruction-twin-differs</c>); no difference is exempt.
    /// </summary>
    internal static List<CensusGap> TwinDifferences(string id, IReadOnlyDictionary<string, string> outcomes, IReadOnlyDictionary<string, string> metadata,
        IReadOnlyDictionary<string, string> twinOutcomes, IReadOnlyDictionary<string, string> twinMetadata)
        => PairDifferences("T", "deconstruction-twin-differs", "deconstruction", "rows", id, outcomes, metadata, twinOutcomes, twinMetadata);
}
