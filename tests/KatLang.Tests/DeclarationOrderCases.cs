namespace KatLang.Tests;

/// <summary>
/// Hand cases whose outcome must not depend on declaration order. A case is <c>### id title</c>, an optional
/// <c>#= expected</c> line, then declarations separated by <c>--</c> lines. <c>@first </c> and <c>@last </c> pin a
/// declaration's position; every other declaration is permuted. Every order must first pass syntax-only validation,
/// and must then give one outcome: <c>compiles</c> (a clean front end and no program output), <c>ok value</c>,
/// <c>err Code</c> (the run's structured failure codes) or <c>front A+B</c> (the SORTED MULTISET of front-end error
/// codes, so duplicate reporting stays visible). A host exception is never an outcome: it fails the test.
/// </summary>
internal static class DeclarationOrderCases
{
    /// <summary>The finite evaluation options every case and every inlined twin share.</summary>
    internal static readonly RunOptions Options = new() { EvaluationLimits = new EvaluationLimits { MaxDepth = 64, MaxSteps = 1_000_000 } };

    internal sealed record Case(string Id, string? Expected, IReadOnlyList<string> First, IReadOnlyList<string> Free, IReadOnlyList<string> Last)
    {
        public override string ToString() => Id;
    }

    internal static IReadOnlyList<Case> Parse(string text)
    {
        var cases = new List<Case>();
        string? id = null, expected = null;
        var lines = new List<string>();
        foreach (var raw in text.Replace("\r\n", "\n").Split('\n').Append("### <end>"))
        {
            if (raw.StartsWith("### ", StringComparison.Ordinal))
            {
                if (id is not null) cases.Add(Build(id, expected, lines));
                (id, expected) = (raw[4..].Trim(), null);
                lines = [];
                continue;
            }
            if (raw.StartsWith("#= ", StringComparison.Ordinal)) { expected = raw[3..].Trim(); continue; }
            if (raw.Length != 0) lines.Add(raw);
        }
        return cases;

        static Case Build(string id, string? expected, List<string> lines)
        {
            var sections = new List<List<string>> { new() };
            foreach (var line in lines)
                if (line == "--") sections.Add([]); else sections[^1].Add(line);
            var first = new List<string>();
            var free = new List<string>();
            var last = new List<string>();
            foreach (var section in sections.Where(static s => s.Count != 0))
            {
                var head = section[0];
                if (head.StartsWith("@first ", StringComparison.Ordinal)) first.Add(Join(head[7..], section));
                else if (head.StartsWith("@last ", StringComparison.Ordinal)) last.Add(Join(head[6..], section));
                else free.Add(string.Join("\n", section));
            }
            return new(id[..Math.Max(id.IndexOf(' ') is var space and > 0 ? space : id.Length, 1)], expected, first, free, last);
        }

        static string Join(string head, List<string> section) => string.Join("\n", section.Skip(1).Prepend(head));
    }

    internal static Case Single(IReadOnlyList<Case> cases, string id) => cases.Single(c => c.Id == id);

    /// <summary>Every declaration order of <paramref name="value"/>, pinned declarations kept in place.</summary>
    internal static IEnumerable<string> Orders(Case value)
    {
        foreach (var order in Permutations(value.Free.Count))
            yield return string.Join("\n", value.First.Concat(order.Select(i => value.Free[i])).Concat(value.Last)) + "\n";
    }

    internal static IEnumerable<int[]> Permutations(int count)
    {
        var items = Enumerable.Range(0, count).ToArray();
        return Recurse(items, 0);

        static IEnumerable<int[]> Recurse(int[] items, int start)
        {
            if (start >= items.Length - 1) { yield return (int[])items.Clone(); yield break; }
            for (var i = start; i < items.Length; i++)
            {
                (items[start], items[i]) = (items[i], items[start]);
                foreach (var permutation in Recurse(items, start + 1)) yield return permutation;
                (items[start], items[i]) = (items[i], items[start]);
            }
        }
    }

    /// <summary>The comparable outcome of one program; the source must be syntactically valid.</summary>
    internal static string Outcome(string source)
    {
        SourceProvenance.ParseSyntaxValidRoot(source);
        var parsed = Parser.Parse(source, Options);
        var codes = parsed.Diagnostics.Where(static d => d.Severity == DiagnosticSeverity.Error)
            .Select(static d => d.Code.ToString()).Order(StringComparer.Ordinal).ToArray();
        var run = KatLangEngine.Run(source, Options);
        var outcome = run switch
        {
            RunResult.Success success => "ok " + success.ToDisplayString(),
            RunResult.EvalFailure failure => "err " + string.Join(",", failure.Errors.Select(static e => e.Code)),
            RunResult.ParseFailure failure => "front " + string.Join("+", failure.Errors.Select(static e => e.Code.ToString()).Order(StringComparer.Ordinal)),
            RunResult.NoProgramOutput => codes.Length == 0 ? "compiles" : "front " + string.Join("+", codes),
            _ => run.GetType().Name,
        };
        // The parse route and the engine route must agree on the front end.
        Assert.True(codes.Length == 0 ? !outcome.StartsWith("front ", StringComparison.Ordinal) : outcome == "front " + string.Join("+", codes),
            $"Parser.Parse reported [{string.Join("+", codes)}] but the engine answered {outcome}\nsource:\n{source}");
        return outcome;
    }

    /// <summary>The one outcome of every order of <paramref name="value"/>; fails on order dependence.</summary>
    internal static string OutcomeInEveryOrder(Case value)
    {
        var outcomes = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var orders = 0;
        foreach (var source in Orders(value))
        {
            orders++;
            var outcome = Outcome(source);
            outcomes[outcome] = outcomes.GetValueOrDefault(outcome) + 1;
        }
        Assert.True(orders > 0, value.Id);
        Assert.True(outcomes.Count == 1,
            $"{value.Id}: order-dependent outcome: {string.Join(" || ", outcomes.Select(static p => $"{p.Value}x {p.Key}"))}");
        return outcomes.Keys.Single();
    }
}
