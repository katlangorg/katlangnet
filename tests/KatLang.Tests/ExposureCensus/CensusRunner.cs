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
    public List<CensusLeanItem> Lean { get; } = [];
    public Dictionary<string, string> Outcomes { get; } = new(StringComparer.Ordinal);
    public Dictionary<string, string> Metadata { get; } = new(StringComparer.Ordinal);
    public bool InsideWorks { get; set; }
}

/// <summary>
/// Evaluates census cases: parses each probe program, evaluates it on every route, and applies the
/// under-charge check U and the over-charge check O (brief section 2). Engine disagreements are
/// findings of their own class. The model check (M) consumes <see cref="CensusCaseResult.Lean"/>.
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

    private static async Task<string?> EngineDisagreement(string source, string treeOutcome)
    {
        var run = RenderEngine(KatLangEngine.Run(source));
        var ordinary = RenderEngine(await KatLangEngine.RunAsync(source));
        var forced = RenderEngine(await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = AsyncRoute }));
        return run == treeOutcome && ordinary == treeOutcome && forced == treeOutcome
            ? null
            : $"tree={treeOutcome}; Run={run}; RunAsync={ordinary}; RunAsync(async)={forced}";
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

    /// <summary>Every probe program of a case (label, source), or null when one does not parse cleanly.</summary>
    public static IReadOnlyList<(string Label, string Source)>? Probes(CensusCase @case)
    {
        var rows = new List<(string Label, string Row)> { ("in5", Inside5), ("in7", Inside7), ("same", SameRun) };
        rows.AddRange(@case.Readers.Select(r => ($"esc:{r.Label}", r.Escaped)));
        var sources = rows.Select(r => (r.Label, Source: @case.Body + r.Row + "\n")).ToArray();
        return sources.Any(s => Parser.Parse(s.Source).HasErrors) ? null : sources;
    }

    public static async Task<CensusCaseResult> Run(CensusCase @case, bool collectLean)
    {
        var probes = new List<(string Label, string Row)> { ("in5", Inside5), ("in7", Inside7), ("same", SameRun) };
        probes.AddRange(@case.Readers.Select(r => ($"esc:{r.Label}", r.Escaped)));
        var parsed = new Dictionary<string, Algorithm.User>(StringComparer.Ordinal);
        var sources = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var (label, row) in probes)
        {
            var source = @case.Body + row + "\n";
            var result = Parser.Parse(source);
            if (result.HasErrors)
            {
                var codes = string.Join(",", result.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)
                    .Select(d => d.Code.ToString()).Distinct().Order(StringComparer.Ordinal));
                return new CensusCaseResult { Case = @case, Skipped = label == "in5" ? codes : $"{codes} (probe {label})" };
            }
            // The pre-screen above keeps diagnostics for skipped cells; every evaluated source then
            // crosses the repository's explicit clean-source assertion boundary.
            parsed[label] = SourceProvenance.ParseValid(source).Root;
            sources[label] = source;
        }

        var outcome = new CensusCaseResult { Case = @case };
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
            else if (await EngineDisagreement(sources[label], result) is { } engine)
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
            if (escaped.StartsWith("err localOnlyProperty", StringComparison.Ordinal))
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
        return outcome;
    }
}
