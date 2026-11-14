using System.Text;

namespace KatLang.Tests.ExposureCensus;

/// <summary>A doubling family of the work check W: its id and its program at width M.</summary>
internal sealed record CensusFamily(string Id, Func<int, string> Program, Func<Algorithm.User, int, IReadOnlyList<Property?>> Readers);

/// <summary>
/// The work check W (brief section 2): for every combination of the dimensions that decide sharing
/// (reader, placement, open level, the open target's head, used or unused), a doubling family of M
/// readers and M open targets at M = 25, 50 and 100. Doubling may at most a little more than double
/// both the settlement frames and the summary-channel checkpoints (the 2.5 bound of
/// <see cref="ExposureAccessCheckComplexityTests"/>). Depth families put one reader at each of D nested
/// levels and count each level's open-walk settlements.
/// </summary>
internal static class CensusWork
{
    public static readonly int[] Widths = [25, 50, 100];
    public const double Bound = 2.5;
    public static readonly string[] Levels = ["own", "enc1", "enc2", "F", "two"];

    private static bool RuntimeHead(string head) => head is "rt-param" or "rt-member" or "rt-alg";

    private static string Placement(string place) => place switch { "in-lib" => "Lib", "in-box" => "Box", "in-mid" => "Mid", _ => "F" };

    // The concrete level a relative W level names; "reader" marks a per-reader level (own, or a block or
    // deep reader's enclosing level). Null: no such level below the root.
    private static string? Concrete(string level, string reader, string place) => level switch
    {
        "own" => "reader-own",
        "enc1" => reader is "block" or "deep" ? "reader-enc" : Placement(place),
        "enc2" => reader is "block" or "deep" ? Placement(place) : place switch { "outside" => null, "in-lib" => "F", _ => "Lib" },
        "F" => "F",
        "two" => "reader-two",
        _ => throw new ArgumentOutOfRangeException(nameof(level)),
    };

    public static IEnumerable<(CensusFamily Family, string? Excluded)> Families()
    {
        foreach (var head in CensusGrid.Heads)
        foreach (var reader in CensusGrid.ReaderKinds)
        foreach (var place in CensusGrid.Places)
        foreach (var level in Levels)
        foreach (var use in new[] { "used", "unused" })
        {
            var id = $"W|head={head}|reader={reader}|place={place}|level={level}|use={use}";
            var concrete = Concrete(level, reader, place);
            string? excluded = head == "opened" ? "an open-target head cannot itself be open-provided (provided reader names are covered by used families)"
                : concrete is null ? "no such level below the root"
                : RuntimeHead(head) && use == "used" ? "a runtime reference opens its own namespace: nothing provides the read name"
                : level != "F" && Levels.TakeWhile(l => l != level).Any(l => Concrete(l, reader, place) == concrete) ? "same concrete level as a lower relative level"
                : level == "F" && Concrete("enc1", reader, place) == "F" ? "same concrete level as enc1"
                : level == "F" && Concrete("enc2", reader, place) == "F" ? "same concrete level as enc2"
                : null;
            yield return (new CensusFamily(id, m => Program(head, reader, place, concrete ?? "F", use, m), (root, m) => Readers(root, reader, place, m)), excluded);
        }
    }

    private static string Target(string head, int i) => head switch
    {
        "name" => $"X{i}.Sub",
        // An inline open target whose member reads y is a front-end IllegalInOpen: the literal reads nothing.
        "block" => $"{{ public Sub = {{ public Q{i} = 1 }} }}.Sub",
        "group-name" => $"(X{i}.Sub)",
        "group-block" => $"({{ public Sub = {{ public Q{i} = 1 }} }}.Sub)",
        "ref1" or "blockref" or "rt-param" or "rt-member" or "rt-alg" => $"L{i}",
        "chain2" => $"J{i}",
        "refmem" => $"M{i}",
        _ => throw new ArgumentOutOfRangeException(nameof(head)),
    };

    private static IEnumerable<string> References(string head, int i) => head switch
    {
        "ref1" => [$"L{i} = X{i}.Sub"],
        "chain2" => [$"L{i} = X{i}.Sub", $"J{i} = L{i}"],
        "refmem" => [$"P{i} = X{i}", $"M{i} = P{i}.Sub"],
        "blockref" => [$"L{i} = {{ public Sub = {{ public Q{i} = 1\n y }} }}.Sub"],
        "rt-param" => [$"L{i} = y"],
        "rt-member" => [$"L{i} = y.C"],
        "rt-alg" => [$"L{i} = X{i}.Sub.Algorithm"],
        _ => [],
    };

    private static string Program(string head, string reader, string place, string concrete, string use, int m)
    {
        var path = place switch { "in-box" => "Lib.Box.Sub", "in-mid" => "Lib.Mid.Sub", _ => "Lib.Sub" };
        var other = use == "unused" ? ", Other" : "";
        var shared = $"open {path}, {string.Join(", ", Enumerable.Range(0, m).Select(i => Target(head, i)))}{other}\n";
        var enclosing = Concrete("enc1", reader, place);
        string Opens(string level) => concrete == level || (concrete == "reader-two" && enclosing == level) ? shared : "";
        string Own(int i) => $"open {Target(head, i)}{other}";
        string Expression(int i) => use == "used" ? $"Q{i} + 0" : "X + 0";
        string Value(int i, bool own) => own ? $"{{\n  {Own(i)}\n  {Expression(i)}\n}}" : Expression(i);

        var readers = new StringBuilder();
        for (var i = 0; i < m; i++)
        {
            var own = concrete == "reader-own";
            var enc = concrete == "reader-enc" ? Own(i) + "\n"
                : concrete == "reader-two" && enclosing == "reader-enc" ? Own(i) + "\n" : "";
            string ReadValue() => concrete == "reader-two" ? $"{{\n  open Near\n  {Expression(i)}\n}}" : Value(i, own);
            readers.Append(reader switch
            {
                "plain" => $"A{i} = {ReadValue()}\n",
                "param" => $"A{i}(z) = {ReadValue()}\n",
                "clause" => $"K{i}(0) = {ReadValue()}\nK{i}(n) = n\n",
                "block" => $"B{i}(w) = {{\n{CensusGrid.Indent(enc + "D = " + ReadValue() + "\nD", 2)}\n}}\n",
                "deep" => $"N{i} = {{\n{CensusGrid.Indent(enc + "A = " + ReadValue() + "\nA", 2)}\n}}\n",
                _ => throw new ArgumentOutOfRangeException(nameof(reader)),
            });
        }
        var readerText = readers.ToString().TrimEnd('\n');
        const string sub = "public Sub = {\n  public Q = 1\n  y\n}";
        string Level(string level, string members, string output)
            => CensusGrid.Indent(Opens(level) + members + "\n" + output, 2);
        var lib = place switch
        {
            "in-box" => $"Lib = {{\n{Level("Lib", $"public Box = {{\n{Level("Box", sub + "\n" + readerText, "0")}\n}}", "0")}\n}}",
            "in-mid" => $"Lib = {{\n{Level("Lib", $"public Mid(p) = {{\n{Level("Mid", sub + "\n" + readerText, "0")}\n}}", "0")}\n}}",
            "in-lib" => $"Lib = {{\n{Level("Lib", sub + "\n" + readerText, "0")}\n}}",
            _ => $"Lib = {{\n{Level("Lib", sub, "0")}\n}}",
        };
        var members = new List<string> { lib, "Other = {\n  public X = 1\n}" };
        if (concrete == "reader-two") members.Add("Near = { public Irrelevant = 1 }");
        for (var i = 0; i < m; i++)
        {
            members.Add($"X{i} = {{\n  public Sub = {{\n    public Q{i} = 1\n    y\n  }}\n  0\n}}");
            members.AddRange(References(head, i));
        }
        if (head == "rt-member") members.Add("C(r) = r");
        if (place == "outside") members.Add(readerText);
        return $"F(y) = {{\n{Level("F", string.Join("\n", members), "0")}\n}}\nF(5)\n";
    }

    private static IReadOnlyList<Property?> Readers(Algorithm.User root, string reader, string place, int m)
    {
        string[] prefix = place switch
        {
            "in-lib" => ["F", "Lib"],
            "in-box" => ["F", "Lib", "Box"],
            "in-mid" => ["F", "Lib", "Mid"],
            _ => ["F"],
        };
        return Enumerable.Range(0, m).Select(i => CensusRunner.Find(root, reader switch
        {
            "plain" or "param" => [.. prefix, $"A{i}"],
            "clause" => [.. prefix, $"K{i}"],
            "block" => [.. prefix, $"B{i}", "D"],
            "deep" => [.. prefix, $"N{i}", "A"],
            _ => throw new ArgumentOutOfRangeException(nameof(reader)),
        })).ToArray();
    }

    /// <summary>The Box family of the 2026-11-14 host check, verbatim (a self-check W must flag).</summary>
    public static CensusFamily BoxSelfCheck() => new("W|selfcheck=box-param-readers", n =>
    {
        var s = new StringBuilder("F(y) = {\n  open Lib.Box.Sub");
        for (var i = 0; i < n; i++) s.Append($", X{i}.Sub");
        s.Append("\n  Lib = {\n    public Box = {\n      public Sub = { public T = 1\n        y }\n");
        for (var i = 0; i < n; i++) s.Append($"      A{i}(z) = Q{i} + 0\n");
        s.Append("      0\n    }\n    0\n  }\n");
        for (var i = 0; i < n; i++) s.Append($"  X{i} = {{ public Sub = {{ public Q{i} = 1 }}\n    0 }}\n");
        s.Append("  Lib.Box.A0(0)\n}\nF(1)\n");
        return s.ToString();
    }, (root, n) => Enumerable.Range(0, n).Select(i => CensusRunner.Find(root, ["F", "Lib", "Box", $"A{i}"])).ToArray());

    /// <summary>The reviewer's Mid(p) discharge family, verbatim (a self-check W must flag).</summary>
    public static CensusFamily DischargeSelfCheck() => new("W|selfcheck=mid-discharge", n =>
    {
        var s = new StringBuilder("F(y) = {\n  open Lib.Mid.Sub");
        for (var i = 0; i < n; i++) s.Append($", X{i}.Sub");
        s.Append("\n  Lib = {\n    public Mid(p) = {\n      public Sub = { public T = 1\n        p }\n");
        for (var i = 0; i < n; i++) s.Append($"      A{i}(z) = Q{i} + 0\n");
        s.Append("      A0(0) + T\n    }\n    0\n  }\n");
        for (var i = 0; i < n; i++) s.Append($"  X{i} = {{ public Sub = {{ public Q{i} = 1 }}\n    0 }}\n");
        s.Append("  Lib.Mid(5)\n}\nF(1)\n");
        return s.ToString();
    }, (root, n) => Enumerable.Range(0, n).Select(i => CensusRunner.Find(root, ["F", "Lib", "Mid", $"A{i}"])).ToArray());

    public sealed record Measurement(string Id, long[] Frames, long[] Checkpoints, string? Problem)
    {
        public bool WithinBound => Problem is null;
    }

    private static T WithOpenWalks<T>(bool perReader, Func<T> work)
    {
        var previous = PropertyExposureResolver.OpenWalksPerReaderForTesting.Value;
        PropertyExposureResolver.OpenWalksPerReaderForTesting.Value = perReader;
        try { return work(); }
        finally { PropertyExposureResolver.OpenWalksPerReaderForTesting.Value = previous; }
    }

    /// <summary>Front-end diagnostics of a family program, or null when it parses cleanly.</summary>
    public static string? Diagnostics(string source)
    {
        var parsed = Parser.Parse(source);
        return parsed.HasErrors
            ? string.Join(",", parsed.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).Select(d => d.Code.ToString()).Distinct().Order(StringComparer.Ordinal))
            : null;
    }

    public static Measurement Measure(CensusFamily family)
    {
        var frames = new long[Widths.Length];
        var checkpoints = new long[Widths.Length];
        var problems = new List<string>();
        string? expectedMetadata = null;
        for (var k = 0; k < Widths.Length; k++)
        {
            var source = family.Program(Widths[k]);
            var observations = new FrontEndTraversalObservations();
            var root = ExposureOpenChainComplexityTests.Exposed(source, observations);
            frames[k] = observations.RequiredAncestorSettlementFrames;
            checkpoints[k] = observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel);
            var readers = family.Readers(root, Widths[k]);
            var described = readers.Select(CensusRunner.Describe).Distinct(StringComparer.Ordinal).ToArray();
            if (described.Length != 1 || readers.Any(r => r is null))
                problems.Add($"readers differ at M={Widths[k]}: {string.Join(" / ", described)}");
            if (readers.Count != Widths[k]) problems.Add($"missing readers at M={Widths[k]}");
            expectedMetadata ??= described.FirstOrDefault();
            if (readers.Any(r => CensusRunner.Describe(r) != expectedMetadata))
                problems.Add($"reader metadata changes with width at M={Widths[k]}");
            if (k == 0)
            {
                var perReader = WithOpenWalks(true, () => ExposureOpenChainComplexityTests.Exposed(source, new FrontEndTraversalObservations()));
                if (MetadataOf(perReader) != MetadataOf(root))
                    problems.Add("published metadata differs from the per-reader settlement");
            }
        }
        for (var k = 1; k < Widths.Length; k++)
        {
            if (frames[k] > Bound * frames[k - 1]) problems.Add($"frames {frames[k - 1]} -> {frames[k]}");
            if (checkpoints[k] > Bound * checkpoints[k - 1]) problems.Add($"summary checkpoints {checkpoints[k - 1]} -> {checkpoints[k]}");
        }
        return new Measurement(family.Id, frames, checkpoints, problems.Count == 0 ? null : string.Join("; ", problems));
    }

    internal static string MetadataOf(Algorithm root)
    {
        var lines = new List<string>();
        var pending = new Stack<(Algorithm Algorithm, string Path)>();
        pending.Push((root, "root"));
        while (pending.TryPop(out var item))
        {
            if (item.Algorithm is Algorithm.Conditional conditional)
            {
                for (var b = 0; b < conditional.Branches.Count; b++) pending.Push((conditional.Branches[b].Body, $"{item.Path}#{b}"));
                continue;
            }
            IReadOnlyList<Property> properties = item.Algorithm switch
            {
                Algorithm.User user => user.Properties,
                Algorithm.Alias alias => alias.Properties,
                _ => [],
            };
            foreach (var property in properties)
            {
                lines.Add($"{item.Path}.{property.Name}: {CensusRunner.Describe(property)}");
                pending.Push((property.Value, $"{item.Path}.{property.Name}"));
            }
        }
        return string.Join("\n", lines);
    }

    /// <summary>
    /// D nested levels, each with its own chargeable open spelled by <paramref name="head"/> and a reader of
    /// kind <paramref name="reader"/> reading the name only the OUTERMOST level's open provides.
    /// </summary>
    public static string DepthProgram(string head, string reader, int depth)
    {
        var s = new StringBuilder("F(y) = {\n");
        for (var k = 0; k < depth; k++)
        {
            var indent = new string(' ', 2 * k + 2);
            s.Append($"{indent}open {Target(head, k).Replace($"Q{k}", k == 0 ? "Q" : $"Q{k}")}\n");
            s.Append($"{indent}X{k} = {{\n{indent}  public Sub = {{\n{indent}    public {(k == 0 ? "Q" : $"Q{k}")} = 1\n{indent}    y\n{indent}  }}\n{indent}  0\n{indent}}}\n");
            foreach (var reference in References(head, k)) s.Append($"{indent}{reference.Replace($"Q{k}", k == 0 ? "Q" : $"Q{k}").Replace("\n", "\n" + indent)}\n");
            if (head == "rt-member" && k == 0) s.Append($"{indent}C(r) = r\n");
            s.Append(indent + reader switch
            {
                "plain" => $"R{k} = Q + 0\n",
                "param" => $"R{k}(z) = Q + 0\n",
                "clause" => $"R{k}(0) = Q + 0\n{indent}R{k}(n) = n\n",
                "block" => $"R{k}(w) = {{\n{indent}  D = Q + 0\n{indent}  D\n{indent}}}\n",
                "deep" => $"R{k} = {{\n{indent}  D = Q + 0\n{indent}  D\n{indent}}}\n",
                _ => throw new ArgumentOutOfRangeException(nameof(reader)),
            });
            if (k + 1 < depth) s.Append($"{indent}N{k + 1} = {{\n");
        }
        for (var k = depth - 1; k >= 0; k--)
        {
            var indent = new string(' ', 2 * k + 2);
            s.Append($"{indent}0\n");
            if (k > 0) s.Append($"{new string(' ', 2 * k)}}}\n");
        }
        s.Append("}\nF(5)\n");
        return s.ToString();
    }

    /// <summary>The largest number of times one level's open walks were computed, and the level count.</summary>
    public static (long MaxPerLevel, int Levels, long WithBoundOwners) MeasureDepth(string source, int depth)
    {
        var observations = new FrontEndTraversalObservations();
        var root = ExposureOpenChainComplexityTests.Exposed(source, observations);
        var perReader = WithOpenWalks(true, () => ExposureOpenChainComplexityTests.Exposed(source, new FrontEndTraversalObservations()));
        Assert.Equal(MetadataOf(perReader), MetadataOf(root));
        var prefix = new List<string> { "F" };
        for (var k = 0; k < depth; k++)
        {
            var path = prefix.Append($"R{k}").ToArray();
            var actual = CensusRunner.Find(root, path);
            Assert.NotNull(actual);
            Assert.Equal(CensusRunner.Describe(CensusRunner.Find(perReader, path)), CensusRunner.Describe(actual));
            prefix.Add($"N{k + 1}");
        }
        return (observations.OpenWalksSettlements.Count == 0 ? 0 : observations.OpenWalksSettlements.Values.Max(),
            observations.OpenWalksSettlements.Count, observations.OpenWalksSettlementsWithBoundOwners);
    }
}
