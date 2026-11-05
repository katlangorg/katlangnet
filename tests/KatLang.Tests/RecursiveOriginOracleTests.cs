using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// THE INDEPENDENT MODEL of recursive inference and R1 over a documented small domain: random source programs of up to five
/// open bodies in the top level and one enclosing context, reading each other and fixed declarations (plain, collecting,
/// META, sequence-group and list-group parameters), in shuffled declaration order. The model is written here, over its own
/// pattern type, and calls no production composition, selection or provenance code; the real front end is only observed
/// through published signatures and capture records.
///
/// <para>The domain is finite and its limits are real: no <c>.Algorithm</c> guards (the whole-system rule G6 oracle covers
/// them), no owner with a lone collector (so no grouped-collector forwarding, pinned by
/// <see cref="RecursiveParameterInferenceTests"/>) and no module content. Agreement here proves nothing beyond this
/// domain. The mutation controls show that the comparison can fail: each one changes one rule of the model and must
/// disagree with production.</para>
/// </summary>
public sealed class RecursiveOriginOracleTests
{
    private abstract record Pat;

    private sealed record Cap(string Name, char Kind) : Pat;

    private sealed record Grp(char Shape, Pat[] Items) : Pat;

    private sealed record Reference(int Target, int External);

    private sealed record Sys(string[][] Own, Reference[][] Refs, bool[] Nested, string[] Lines);

    private static readonly (string Line, Pat[] Patterns)[] Fixed =
    [
        ("X0(a) = a", [new Cap("a", 'n')]),
        ("X1(b) = b", [new Cap("b", 'n')]),
        ("X2(a, b) = a", [new Cap("a", 'n'), new Cap("b", 'n')]),
        ("X3(*r) = 0", [new Cap("r", 'c')]),
        ("X4(c, *r) = c", [new Cap("c", 'n'), new Cap("r", 'c')]),
        ("X5(d, *s) = d", [new Cap("d", 'n'), new Cap("s", 'c')]),
        ("X6((a, e)) = a", [new Grp('(', [new Cap("a", 'n'), new Cap("e", 'n')])]),
        ("X7([b, f]) = b", [new Grp('[', [new Cap("b", 'n'), new Cap("f", 'n')])]),
        ("X8(meta g) = g", [new Cap("g", 'm')]),
        ("X9(a, *z) = a", [new Cap("a", 'n'), new Cap("z", 'c')]),
        ("X10(c, r) = c", [new Cap("c", 'n'), new Cap("r", 'n')]),
    ];

    /// <summary>The declarations whose names meet: a ring over these is where cycles share sources and kinds change.</summary>
    private static readonly int[] Meeting = [0, 2, 4, 6, 9, 10];

    [Flags]
    private enum Mutation
    {
        None = 0,
        NamesOnly = 1,
        KindBlind = 2,
        InPlaceRounds = 4,
        MissingReference = 8,
        ConflatedContext = 16,
        StaleOrigin = 32,
        ArbitraryRoot = 64,
        ResourceAsNonSettling = 128,

        /// <summary>The former rule, not a defect: a genuine lifting cycle has no meaning.</summary>
        FormerRule = 256,
    }

    // ── the domain ──────────────────────────────────────────────────────────────────────────────

    private static Sys Generate(Random random)
    {
        var count = random.Next(1, 6);
        var nested = new bool[count];
        var useContext = random.NextDouble() < 0.4;
        for (var i = 0; i < count; i++)
            nested[i] = useContext && random.NextDouble() < 0.5;
        var own = new string[count][];
        var refs = new Reference[count][];
        var ring = random.NextDouble() < 0.5;
        for (var i = 0; i < count; i++)
        {
            own[i] = random.NextDouble() < 0.25 ? [nested[i] ? "v" : random.NextDouble() < 0.5 ? "a" : "v"] : [];
            refs[i] = new Reference[random.Next(0, 4)];
            for (var r = 0; r < refs[i].Length; r++)
            {
                refs[i][r] = random.NextDouble() < 0.6
                    ? new Reference(random.Next(count), -1)
                    : new Reference(-1, random.Next(Fixed.Length));
            }
        }

        if (ring)
        {
            for (var i = 0; i < count; i++)
            {
                // A member reads its neighbour first, then a declaration whose names meet another member's.
                refs[i] = [new Reference((i + 1) % count, -1), new Reference(-1, Meeting[random.Next(Meeting.Length)]), .. refs[i].Take(1)];
            }
        }

        string Written(int from, Reference reference)
            => reference.Target < 0 ? $"X{reference.External}"
                : nested[reference.Target] && !nested[from] ? $"Outer.E{reference.Target}" : $"E{reference.Target}";

        string Body(int i)
        {
            var terms = own[i].Concat(refs[i].Select(reference => Written(i, reference))).Append("0").Append("0");
            return string.Join(" + ", terms);
        }

        var top = new List<string>(Fixed.Select(static item => item.Line));
        top.AddRange(Enumerable.Range(0, count).Where(i => !nested[i]).Select(i => $"E{i} = {Body(i)}"));
        var inner = Enumerable.Range(0, count).Where(i => nested[i]).Select(i => $"    public E{i} = {Body(i)}").ToArray();
        if (useContext)
            top.Add("Outer(a) = {\n" + string.Join("\n", inner.Append("    0")) + "\n}");
        var shuffled = top.OrderBy(_ => random.Next()).ToArray();
        return new Sys(own, refs, nested, [.. shuffled]);
    }

    // ── the model ───────────────────────────────────────────────────────────────────────────────

    private sealed class Fact
    {
        public required Pat[] Patterns;
        public bool Violation;
    }

    private static bool Requires(Pat[] patterns) => patterns.Any(static pattern => pattern is not Cap { Kind: 'c' });

    private static IEnumerable<string> Names(IEnumerable<Pat> patterns)
    {
        foreach (var pattern in patterns)
        {
            if (pattern is Cap capture)
            {
                yield return capture.Name;
            }
            else
            {
                foreach (var name in Names(((Grp)pattern).Items))
                    yield return name;
            }
        }
    }

    private static Pat? Missing(Pat pattern, HashSet<string> bound, bool filtersContext)
    {
        if (pattern is Cap capture)
        {
            if ((filtersContext && capture.Name == "a") || !bound.Add(capture.Name))
                return null;
            return capture.Kind == 'm' ? capture with { Kind = 'n' } : capture;
        }

        var group = (Grp)pattern;
        var items = group.Items.Select(item => Missing(item, bound, filtersContext)).OfType<Pat>().ToArray();
        return items.Length == 0 ? null
            : items.Length == 1 && group.Shape == '(' && items[0] is Cap { Kind: not 'c' } ? items[0]
            : group with { Items = items };
    }

    private static bool ManyCollectors(Pat[] level)
        => level.Count(static pattern => pattern is Cap { Kind: 'c' }) > 1
            || level.OfType<Grp>().Any(static group => ManyCollectors(group.Items));

    private static Pat[] Recover(Pat[] level)
    {
        var seen = false;
        var kept = new Pat[level.Length];
        for (var i = 0; i < level.Length; i++)
        {
            kept[i] = level[i] switch
            {
                Cap { Kind: 'c' } capture when seen => capture with { Kind = 'n' },
                Grp group => group with { Items = Recover(group.Items) },
                var other => other,
            };
            seen |= level[i] is Cap { Kind: 'c' };
        }

        return kept;
    }

    private static List<Pat[]> Lifted(Sys system, int equation, Func<int, Fact> read, Mutation mutation, out List<Reference> order)
    {
        order = [];
        var lifted = new List<Pat[]>();
        var seen = new HashSet<Reference>();
        var references = system.Refs[equation];
        if ((mutation & Mutation.MissingReference) != 0 && references.Length >= 2)
            references = references[..^1];
        foreach (var reference in references)
        {
            var callee = reference.Target >= 0 ? read(reference.Target).Patterns : Fixed[reference.External].Patterns;
            if (!Requires(callee) || !seen.Add(reference))
                continue;
            lifted.Add(callee);
            order.Add(reference);
        }

        return lifted;
    }

    private static Fact Compose(Sys system, int equation, Func<int, Fact> read, Mutation mutation)
    {
        var patterns = system.Own[equation].Select(static name => (Pat)new Cap(name, 'n')).ToList();
        var bound = new HashSet<string>(system.Own[equation]);
        var filters = system.Nested[equation] && (mutation & Mutation.ConflatedContext) == 0;
        var ownCount = patterns.Count;
        foreach (var callee in Lifted(system, equation, read, mutation, out _))
            patterns.AddRange(callee.Select(pattern => Missing(pattern, bound, filters)).OfType<Pat>());
        var result = patterns.ToArray();
        var violation = patterns.Count != ownCount && ManyCollectors(result);
        return new Fact { Patterns = violation ? Recover(result) : result, Violation = violation };
    }

    private static string Render(IEnumerable<Pat> patterns, bool kinds = true)
        => string.Join(", ", patterns.Select(pattern => pattern switch
        {
            Cap capture => (kinds && capture.Kind == 'c' ? "*" : "") + capture.Name,
            Grp group => kinds
                ? (group.Shape == '(' ? "(" : "[") + Render(group.Items) + (group.Shape == '(' ? ")" : "]")
                : Render(group.Items, kinds: false),
            _ => throw new InvalidOperationException(),
        }));

    private sealed class Outcome
    {
        public readonly Dictionary<int, Fact> Facts = [];
        public readonly Dictionary<int, Fact> ClosedFacts = [];
        public readonly HashSet<int> Failed = [];
        public readonly HashSet<int> Completed = [];
        public readonly Dictionary<int, int> ComponentOf = [];
    }

    private static string StateOf(List<int> component, Dictionary<int, Fact> round, Mutation mutation)
        => string.Join(";", component.Select(key => (mutation & Mutation.NamesOnly) != 0
            ? string.Join(",", Names(round[key].Patterns).Order(StringComparer.Ordinal))
            : Render(round[key].Patterns, kinds: (mutation & Mutation.KindBlind) == 0) + (round[key].Violation ? "!" : "")));

    private static Outcome Solve(Sys system, Mutation mutation)
    {
        var count = system.Own.Length;
        var reach = new bool[count, count];
        for (var i = 0; i < count; i++)
        {
            foreach (var reference in system.Refs[i])
            {
                if (reference.Target >= 0)
                    reach[i, reference.Target] = true;
            }
        }

        for (var k = 0; k < count; k++)
        {
            for (var i = 0; i < count; i++)
            {
                for (var j = 0; j < count; j++)
                    reach[i, j] |= reach[i, k] && reach[k, j];
            }
        }

        var outcome = new Outcome();
        var done = new HashSet<int>();
        while (done.Count < count)
        {
            var key = Enumerable.Range(0, count).First(candidate => !done.Contains(candidate)
                && Enumerable.Range(0, count).All(other => done.Contains(other) || !reach[candidate, other] || reach[other, candidate]));
            var component = Enumerable.Range(0, count).Where(other => other == key || (reach[key, other] && reach[other, key])).ToList();
            done.UnionWith(component);
            foreach (var member in component)
                outcome.ComponentOf[member] = key;
            var members = component.ToHashSet();
            if (component.Any(member => system.Refs[member].Any(reference => reference.Target >= 0 && !members.Contains(reference.Target) && outcome.Failed.Contains(reference.Target))))
            {
                outcome.Failed.UnionWith(component);
                continue;
            }

            var empty = new Fact { Patterns = [] };
            Fact Lower(int target) => outcome.Facts[target];
            if (!reach[key, key])
            {
                outcome.Facts[key] = Compose(system, key, Lower, mutation);
                continue;
            }

            var closed = component.ToDictionary(member => member, member => Compose(system, member, target => members.Contains(target) ? empty : Lower(target), mutation));
            foreach (var (member, fact) in closed)
                outcome.ClosedFacts[member] = fact;
            if (!component.Any(member => system.Refs[member].Any(reference => reference.Target >= 0 && members.Contains(reference.Target) && Requires(closed[reference.Target].Patterns))))
            {
                foreach (var (member, fact) in closed)
                    outcome.Facts[member] = fact;
                continue;
            }

            if ((mutation & Mutation.FormerRule) != 0)
            {
                outcome.Failed.UnionWith(component);
                continue;
            }

            var previous = closed;
            var seen = new HashSet<string> { StateOf(component, previous, mutation) };
            var rounds = 0;
            while (true)
            {
                var read = previous;
                var next = new Dictionary<int, Fact>();
                foreach (var member in component)
                {
                    next[member] = Compose(system, member, target => members.Contains(target)
                        ? (mutation & Mutation.InPlaceRounds) != 0 && next.TryGetValue(target, out var updated) ? updated : read[target]
                        : Lower(target), mutation);
                }

                if (StateOf(component, next, mutation) == StateOf(component, previous, mutation))
                {
                    foreach (var member in component)
                    {
                        outcome.Facts[member] = next[member];
                        outcome.Completed.Add(member);
                    }

                    break;
                }

                if (!seen.Add(StateOf(component, next, mutation)) || ((mutation & Mutation.ResourceAsNonSettling) != 0 && ++rounds > 2))
                {
                    outcome.Failed.UnionWith(component);
                    break;
                }

                previous = next;
            }
        }

        return outcome;
    }

    // ── the model of R1 ─────────────────────────────────────────────────────────────────────────

    private static IReadOnlyList<string> FixedSources(int external) => [$"X{external}"];

    /// <summary>An origin: determined (one label), or a shared set (<c>Shared</c>, possibly empty).</summary>
    private sealed record Origin(bool Shared, string[] Sources)
    {
        public override string ToString() => (Shared ? "shared" : "single") + (Sources.Length == 0 ? "" : " " + string.Join(" ", Sources.Order(StringComparer.Ordinal)));
    }

    private static Dictionary<(int, string), Origin> Origins(Sys system, Outcome outcome, Mutation mutation)
    {
        var origins = new Dictionary<(int, string), Origin>();

        List<(int Member, int External)> Providers(int equation, string name)
        {
            var found = new List<(int, int)>();
            Lifted(system, equation, target => outcome.Facts[target], Mutation.None, out var order);
            foreach (var reference in order)
            {
                var callee = reference.Target >= 0 ? outcome.Facts[reference.Target].Patterns : Fixed[reference.External].Patterns;
                if (Names(callee).Contains(name))
                    found.Add((reference.Target, reference.External));
            }

            return found;
        }

        Origin? Direct(int equation, string name)
            => system.Own[equation].Contains(name) ? new Origin(false, [$"E{equation}"]) : null;

        Origin Shared(List<(int Equation, string Name)> cycle, string name)
        {
            var sources = new SortedSet<string>(StringComparer.Ordinal);
            var visited = new HashSet<int>();
            var queue = new Queue<int>(cycle.Select(static node => node.Equation));
            var component = outcome.ComponentOf[cycle[0].Equation];
            while (queue.TryDequeue(out var member))
            {
                if (!visited.Add(member))
                    continue;
                if (Direct(member, name) is { } rooted)
                {
                    sources.UnionWith(rooted.Sources);
                    continue;
                }

                foreach (var (next, external) in Providers(member, name))
                {
                    if (external >= 0)
                        sources.UnionWith(FixedSources(external));
                    else if (outcome.ComponentOf[next] == component)
                        queue.Enqueue(next);
                    else
                        sources.UnionWith(Resolve(next, name).Sources);
                }
            }

            return sources.Count == 1 || ((mutation & Mutation.ArbitraryRoot) != 0 && sources.Count > 0)
                ? new Origin(false, [sources.Min!])
                : new Origin(true, [.. sources]);
        }

        Origin Resolve(int equation, string name)
        {
            var path = new List<(int Equation, string Name)>();
            var current = (Equation: equation, Name: name);
            Origin? origin = null;
            while (origin is null)
            {
                if (origins.TryGetValue(current, out var known))
                {
                    origin = known;
                    break;
                }

                if (Direct(current.Equation, name) is { } own)
                {
                    origin = own;
                    break;
                }

                if (path.IndexOf(current) is >= 0 and var at)
                {
                    origin = Shared(path.GetRange(at, path.Count - at), name);
                    break;
                }

                path.Add(current);
                if ((mutation & Mutation.StaleOrigin) != 0 && outcome.Completed.Contains(current.Equation)
                    && outcome.ClosedFacts.TryGetValue(current.Equation, out var closed) && Names(closed.Patterns).Contains(name))
                {
                    var stale = system.Refs[current.Equation].FirstOrDefault(reference => reference.External >= 0 && Names(Fixed[reference.External].Patterns).Contains(name));
                    if (stale is not null)
                    {
                        origin = new Origin(false, [$"X{stale.External}"]);
                        break;
                    }
                }

                var (member, external) = Providers(current.Equation, name)[0];
                if (external >= 0)
                    origin = new Origin(false, [$"X{external}"]);
                else
                    current = (member, name);
            }

            foreach (var node in path)
                origins[node] = origin;
            origins[(equation, name)] = origin;
            return origin;
        }

        foreach (var equation in outcome.Facts.Keys.Order())
        {
            foreach (var name in Names(outcome.Facts[equation].Patterns).Distinct())
                Resolve(equation, name);
        }

        return origins;
    }

    // ── the observation ─────────────────────────────────────────────────────────────────────────

    private static string Label(string source, SourceSpan? span)
    {
        if (span is not { } at)
            return "-";
        var line = source.Split('\n')[at.Start.Line - 1].Trim();
        if (line.StartsWith("public ", StringComparison.Ordinal))
            line = line["public ".Length..];
        return line[..line.IndexOfAny(['(', ' '])];
    }

    /// <summary>What the model predicts, or what production published, in one comparable text.</summary>
    private static string Observe(Sys system, string source, ParseResult parsed)
    {
        var count = system.Own.Length;
        var errors = parsed.Diagnostics.Where(static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error).ToArray();
        if (errors.Any(static error => error.Code == DiagnosticCode.SelfDependentInferredParameters))
            return "non-settling";
        if (errors.Length != 0)
            return string.Join(",", errors.Select(static error => error.Code).Distinct().Order());
        var model = SemanticModelBuilder.Build(parsed);
        var lines = new List<string>();
        for (var i = 0; i < count; i++)
        {
            var property = Assert.Single(model.FindProperties($"E{i}"));
            var parameters = property.DisplaySignature.Length > $"E{i}".Length ? property.DisplaySignature[$"E{i}(".Length..^1] : "";
            var body = system.Nested[i]
                ? parsed.Root.Properties.Single(static p => p.Name == "Outer").Value.Properties.Single(p => p.Name == $"E{i}").Value
                : parsed.Root.Properties.Single(p => p.Name == $"E{i}").Value;
            var origins = new SortedDictionary<string, string>(StringComparer.Ordinal);
            foreach (var capture in ParameterPattern.FlattenCaptures(body.ParameterPatterns))
            {
                origins.TryAdd(capture.Name, capture.InferredProvenance?.CycleOrigin is { } cycle
                    ? new Origin(true, [.. cycle.Roots.Select(root => Label(source, root.Span))]).ToString()
                    : new Origin(false, [Label(source, capture.OriginSpan)]).ToString());
            }

            lines.Add($"E{i}({parameters}) {string.Join("; ", origins.Select(static pair => pair.Key + "=" + pair.Value))}");
        }

        return string.Join("\n", lines);
    }

    private static string Predict(Sys system, Mutation mutation)
    {
        var outcome = Solve(system, mutation);
        if (outcome.Failed.Count != 0)
            return "non-settling";
        if (outcome.Facts.Values.Any(static fact => fact.Violation))
            return nameof(DiagnosticCode.InvalidCollectingBinding);
        var origins = Origins(system, outcome, mutation);
        var lines = new List<string>();
        for (var i = 0; i < system.Own.Length; i++)
        {
            var names = new SortedDictionary<string, string>(StringComparer.Ordinal);
            foreach (var name in Names(outcome.Facts[i].Patterns))
                names.TryAdd(name, origins[(i, name)].ToString());
            lines.Add($"E{i}({Render(outcome.Facts[i].Patterns)}) {string.Join("; ", names.Select(static pair => pair.Key + "=" + pair.Value))}");
        }

        return string.Join("\n", lines);
    }

    [Theory]
    [InlineData(11)]
    [InlineData(12)]
    [InlineData(13)]
    [InlineData(14)]
    [InlineData(15)]
    [InlineData(16)]
    public void Production_AgreesWithTheIndependentModel(int seed)
    {
        var random = new Random(seed);
        var (completed, shared, nonSettling) = (0, 0, 0);
        for (var trial = 0; trial < 400; trial++)
        {
            var system = Generate(random);
            var source = string.Join("\n", system.Lines) + "\n0";
            var parsed = Parser.Parse(source);
            var expected = Predict(system, Mutation.None);
            Assert.True(expected == Observe(system, source, parsed), $"seed {seed}, trial {trial}\n{source}\nmodel:\n{expected}\nproduction:\n{Observe(system, source, parsed)}");
            // Lemma C and P1 over this domain: where the former rule selects, signatures, order and origins are unchanged.
            var former = Predict(system, Mutation.FormerRule);
            if (former != "non-settling")
                Assert.Equal(former, expected);
            completed += Solve(system, Mutation.None).Completed.Count != 0 ? 1 : 0;
            shared += expected.Contains("shared", StringComparison.Ordinal) ? 1 : 0;
            nonSettling += expected == "non-settling" ? 1 : 0;
        }

        // The domain reaches the outcomes it claims to compare.
        Assert.InRange(completed, 40, 400);
        Assert.InRange(shared, 3, 400);
        Assert.InRange(nonSettling, 1, 400);
    }

    /// <summary>Each control is one defect a real implementation could have: production must disagree with it somewhere.</summary>
    [Theory]
    [InlineData(Mutation.NamesOnly)]
    [InlineData(Mutation.KindBlind)]
    [InlineData(Mutation.InPlaceRounds)]
    [InlineData(Mutation.MissingReference)]
    [InlineData(Mutation.ConflatedContext)]
    [InlineData(Mutation.StaleOrigin)]
    [InlineData(Mutation.ArbitraryRoot)]
    [InlineData(Mutation.ResourceAsNonSettling)]
    private void AMutatedRule_IsExposedByTheComparison(Mutation mutation)
    {
        var random = new Random(4242);
        var disagreements = 0;
        for (var trial = 0; trial < 6000 && disagreements == 0; trial++)
        {
            var system = Generate(random);
            var source = string.Join("\n", system.Lines) + "\n0";
            if (Predict(system, mutation) != Observe(system, source, Parser.Parse(source)))
                disagreements++;
        }

        Assert.True(disagreements > 0, $"{mutation} went unnoticed.");
    }
}
