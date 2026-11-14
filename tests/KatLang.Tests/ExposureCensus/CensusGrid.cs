using System.Text;

namespace KatLang.Tests.ExposureCensus;

/// <summary>
/// One generated census program: a source body declaring <c>F(y)</c> (no root row), the readers the
/// checks examine and the dimension values that produced it. <see cref="Dims"/> is empty for a fixed
/// control or self-check case.
/// </summary>
internal sealed record CensusCase(
    string Id,
    IReadOnlyList<KeyValuePair<string, string>> Dims,
    string Body,
    IReadOnlyList<CensusReader> Readers,
    string Kind = "grid")
{
    public string Dim(string name) => Dims.First(d => d.Key == name).Value;
}

/// <summary>
/// A property the checks examine: its declaration path from the program root and its escaped probe
/// row (read alone, with nothing before it in the run).
/// </summary>
internal sealed record CensusReader(string Label, IReadOnlyList<string> Path, string Escaped);

/// <summary>A dimension value combination the generator does not build, with the reason.</summary>
internal sealed record CensusExclusion(string Id, string Reason);

/// <summary>
/// The E-18 route census grid (deterministic, no randomness): every program lives inside <c>F(y)</c>,
/// and each dimension of the census brief is one axis here. A value combination that has no meaning
/// (a dead construction, a runtime ending for a fallback) is EXCLUDED with a reason; the rest is
/// generated, and the runner then keeps only cases that parse cleanly.
/// </summary>
internal static class CensusGrid
{
    // 1. The selection's head (the spelling of the selected container).
    public static readonly string[] Heads =
        ["name", "block", "group-name", "group-block", "ref1", "chain2", "refmem", "blockref", "rt-param", "rt-member", "rt-alg", "opened"];

    // 2. Where the reader uses it. `open` opens the container written by the head (member-less for a
    // reference, dotted for a path, an inline block for a block head); `open-dotted` opens `<head>.T`.
    public static readonly string[] Positions = ["value", "callee", "spread", "fallback", "open", "open-dotted"];

    // 3. Which open level the lookup consults (used: the target provides the name; unused: Other does).
    public static readonly string[] OpenLevels =
        ["none", "own-unused", "enc1-unused", "own-used", "enc1-used", "enc2-used", "enc2-unused", "two"];

    // 4. The reader.
    public static readonly string[] ReaderKinds = ["plain", "param", "clause", "block", "deep"];

    // 5. Where the reader sits relative to the open target's path.
    public static readonly string[] Places = ["outside", "in-lib", "in-box", "in-mid"];

    // 6. How the selection ends.
    public static readonly string[] Ends = ["found", "runtime", "missing"];

    // 7. What the selected declarations require.
    public static readonly string[] Requirements = ["none", "container", "member", "deep"];

    public static readonly string[] DimensionNames = ["head", "pos", "open", "reader", "place", "end", "req"];

    public static IReadOnlyList<string[]> DimensionValues =>
        [Heads, Positions, OpenLevels, ReaderKinds, Places, Ends, Requirements];

    public static bool IsOpenPosition(string pos) => pos is "open" or "open-dotted";

    public static string IdOf(IReadOnlyList<string> values)
        => string.Join("|", DimensionNames.Select((name, i) => $"{name}={values[i]}"));

    /// <summary>Why a combination is not built, or <c>null</c> when it is generated.</summary>
    public static string? Exclusion(string head, string pos, string open, string reader, string place, string end, string req)
    {
        if (head == "opened")
        {
            if (IsOpenPosition(pos)) return "an open-target head is direct-lexical, never open-provided";
            if (open == "none") return "an open-provided head needs an open level";
            if (place != "outside") return "inside the target's container the owner walk finds its head before opens";
        }
        if (IsOpenPosition(pos))
        {
            if (open == "none") return "an open position needs an open level";
        }
        else if (head != "opened" && open is not ("none" or "own-unused" or "enc1-unused"))
            return "a non-open position consults only unused opens (the head is not an opened name)";
        if (open.StartsWith("enc2", StringComparison.Ordinal) && place == "outside" && reader is not ("block" or "deep"))
            return "no second enclosing level below the root (the open would not see F's declarations)";
        switch (end)
        {
            case "runtime" when pos == "fallback":
                return "the fallback receiver is the found member";
            case "missing" when pos is "callee" or "spread" or "fallback":
                return "a missing member ends only a value read or an open target";
        }
        return null;
    }

    public static (IReadOnlyList<CensusCase> Cases, IReadOnlyList<CensusExclusion> Excluded) Generate()
    {
        var cases = new List<CensusCase>();
        var excluded = new List<CensusExclusion>();
        foreach (var head in Heads)
        foreach (var pos in Positions)
        foreach (var open in OpenLevels)
        foreach (var reader in ReaderKinds)
        foreach (var place in Places)
        foreach (var end in Ends)
        foreach (var req in Requirements)
        {
            string[] values = [head, pos, open, reader, place, end, req];
            var id = IdOf(values);
            if (Exclusion(head, pos, open, reader, place, end, req) is { } reason)
            {
                excluded.Add(new CensusExclusion(id, reason));
                continue;
            }
            cases.Add(Build(values));
        }
        return (cases, excluded);
    }

    public static CensusCase Build(IReadOnlyList<string> v)
    {
        var builder = new ProgramShape(v[0], v[1], v[2], v[3], v[4], v[5], v[6]);
        var dims = DimensionNames.Select((name, i) => new KeyValuePair<string, string>(name, v[i])).ToArray();
        return new CensusCase(IdOf(v), dims, builder.Body(), builder.Readers());
    }

    public static CensusCase? TryParseId(string id)
    {
        var parts = id.Split('|');
        if (parts.Length != DimensionNames.Length) return null;
        var values = new string[parts.Length];
        for (var i = 0; i < parts.Length; i++)
        {
            var prefix = DimensionNames[i] + "=";
            if (!parts[i].StartsWith(prefix, StringComparison.Ordinal)) return null;
            values[i] = parts[i][prefix.Length..];
        }
        return Build(values);
    }

    /// <summary>
    /// Fixed cases: the controls the brief requires to stay exported, and the self-check programs the
    /// census must detect (section 3 of the brief).
    /// </summary>
    public static IReadOnlyList<CensusCase> Fixed()
    {
        static CensusCase Control(string name, string body)
            => new($"control={name}", [], body, [new CensusReader("A", ["F", "A"], "F.A")], "control");
        static CensusCase Self(string name, string body)
            => new($"selfcheck={name}", [], body, [new CensusReader("A", ["F", "A"], "F.A")], "selfcheck");
        return
        [
            Control("value-only-reference", "F(y) = {\n  Lib = {\n    public Q = 1\n    y\n  }\n  L = Lib\n  A = L.Q + 0\n  A\n}\n"),
            Control("named-member-only-head", "F(y) = {\n  B = {\n    public Q = 1\n    y + 0\n  }\n  A = B.Q + 0\n  A\n}\n"),
            Control("inline-open-block", "F(y) = {\n  A = {\n    open { public Sub = { public Q = 1 } }.Sub\n    Q + 0\n  }\n  A\n}\n"),
            Control("owner-walk-name", "F(y) = {\n  open Lib.Sub\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  X = 2\n  A = X + 0\n  A\n}\n"),
            Control("prelude-name", "F(y) = {\n  open Lib.Sub\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  A = max([1, 2]) + 0\n  A\n}\n"),
            // I25: the eager charge of an algorithm's own dotted opens (an inherited over-charge O must flag).
            Self("I25-eager-own-open", "F(y) = {\n  A = {\n    open Lib.Sub\n    1\n  }\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  A\n}\n"),
            // The audit's S1 program: an inline-block member read of y (wrong values on HEAD a4b545e8).
            Self("S1-audit-inline-block", "F(y) = {\n  A = { public Q = y }.Q + 0\n  A\n}\n"),
            // The review's static-prefix runtime open (M2 must flag its host-built exported copy).
            // Fallbacks that never read their receiver (the I16 shape and the I28 dot control): O decides
            // whether the receiver's charge is a read the evaluator performs.
            Self("fallback-unread-receiver", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  A = L.Missing + 0\n  Missing(r) = 2\n  A\n}\n"),
            Self("runtime-dot-unread-receiver", "F(y) = {\n  L = y\n  Q(r) = 1\n  A = L.Q + 0\n  A\n}\n"),
            Self("static-prefix-runtime-open","F(y) = {\n  open L, Other\n  L = Lib.Sub.Algorithm\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  Other = { public Z = 2 }\n  A = Z + 0\n  A\n}\n"),
        ];
    }

    /// <summary>
    /// A deterministic subset covering every combination of three dimension values that occurs in some
    /// case of <paramref name="cases"/> (greedy covering array; ties broken by generation order).
    /// </summary>
    public static IReadOnlyList<CensusCase> ThreeWayCover(IReadOnlyList<CensusCase> cases)
    {
        var dims = DimensionNames.Length;
        var triples = new List<(int, int, int)>();
        for (var a = 0; a < dims; a++)
            for (var b = a + 1; b < dims; b++)
                for (var c = b + 1; c < dims; c++)
                    triples.Add((a, b, c));
        var keysOf = new string[cases.Count][];
        var uncovered = new HashSet<string>(StringComparer.Ordinal);
        for (var i = 0; i < cases.Count; i++)
        {
            var v = cases[i].Dims;
            keysOf[i] = triples.Select(t => $"{t.Item1}={v[t.Item1].Value};{t.Item2}={v[t.Item2].Value};{t.Item3}={v[t.Item3].Value}").ToArray();
            uncovered.UnionWith(keysOf[i]);
        }
        var chosen = new List<CensusCase>();
        var taken = new bool[cases.Count];
        while (uncovered.Count > 0)
        {
            var best = -1;
            var bestGain = 0;
            for (var i = 0; i < cases.Count; i++)
            {
                if (taken[i]) continue;
                var gain = 0;
                foreach (var key in keysOf[i])
                    if (uncovered.Contains(key)) gain++;
                if (gain > bestGain)
                {
                    best = i;
                    bestGain = gain;
                    if (gain == triples.Count) break;
                }
            }
            taken[best] = true;
            chosen.Add(cases[best]);
            foreach (var key in keysOf[best]) uncovered.Remove(key);
        }
        return chosen;
    }

    public static int TripleCount(IReadOnlyList<CensusCase> cases)
    {
        var keys = new HashSet<string>(StringComparer.Ordinal);
        var dims = DimensionNames.Length;
        foreach (var @case in cases)
            for (var a = 0; a < dims; a++)
                for (var b = a + 1; b < dims; b++)
                    for (var c = b + 1; c < dims; c++)
                        keys.Add($"{a}={@case.Dims[a].Value};{b}={@case.Dims[b].Value};{c}={@case.Dims[c].Value}");
        return keys.Count;
    }

    /// <summary>The program text of one grid cell.</summary>
    private sealed class ProgramShape(string head, string pos, string open, string reader, string place, string end, string req)
    {
        private readonly string[] _path = place switch
        {
            "in-box" when req == "deep" => ["Lib", "Box", "Mid", "Sub"],
            "in-box" => ["Lib", "Box", "Sub"],
            "in-mid" => ["Lib", "Mid", "Sub"],
            _ when req == "deep" => ["Lib", "Mid", "Sub"],
            _ => ["Lib", "Sub"],
        };

        private string Path => string.Join(".", _path);
        private string Q => req == "member" ? "y" : "1";
        private string G => req == "member" ? "x + y" : "x";
        private string SubRow => req switch { "container" => "y", "deep" => "p", _ => "0" };

        private string Sub()
            => $"public Sub = {{\n  public Q = {Q}\n  public G(x) = {G}\n  public T = {{\n    public Q = {Q}\n  }}\n  {SubRow}\n}}";

        // Requirement ownership is independent of reader placement. A reader outside Mid can still
        // select Mid.Sub; its eventual access failure is census evidence, not a generation exclusion.
        private string PlacedSub() => req == "deep" && place != "in-mid"
            ? $"public Mid(p) = {{\n{Indent(Sub(), 2)}\n  0\n}}" : Sub();

        // The container literal for an inline-block head (no readers, no opens).
        private string BlockHead()
        {
            var inner = place switch
            {
                "in-box" => $"public Box = {{\n{Indent(PlacedSub(), 2)}\n  0\n}}",
                "in-mid" => $"public Mid(p) = {{\n{Indent(Sub(), 2)}\n  0\n}}",
                _ => PlacedSub(),
            };
            var tail = string.Join(".", _path.Skip(1));
            return $"{{\n{Indent(inner, 2)}\n}}.{tail}";
        }

        private bool Runtime => head is "rt-param" or "rt-member" or "rt-alg";

        // The written container, as the reader's expression spells it, and the references it needs.
        private (string Container, string[] Declarations) Head() => head switch
        {
            "name" => (Path, []),
            "block" => (BlockHead(), []),
            "group-name" => ($"({Path})", []),
            "group-block" => ($"({BlockHead()})", []),
            "ref1" => ("L", [$"L = {Path}"]),
            "chain2" => ("L1", [$"L0 = {Path}", "L1 = L0"]),
            "refmem" => ("M", [$"L0 = {string.Join(".", _path.SkipLast(1))}", "M = L0.Sub"]),
            "blockref" => ("L", [$"L = {BlockHead()}"]),
            "rt-param" => ("L", ["L = y"]),
            "rt-member" => ("L", ["L = y.C"]),
            "rt-alg" => ("L", [$"L = {Path}.Algorithm"]),
            "opened" => (string.Join(".", _path.Skip(1)), []),
            _ => throw new ArgumentOutOfRangeException(nameof(head), head, null),
        };

        private string Step => end == "runtime" ? ".Algorithm" : "";

        // The reader's expression and the open target its position or open level writes.
        private (string Expression, string? OpenTarget) Use(string container)
        {
            if (CensusGrid.IsOpenPosition(pos))
            {
                var target = container + Step + (pos == "open-dotted" ? ".T" : "") + (end == "missing" ? ".Missing" : "");
                var used = open.EndsWith("-used", StringComparison.Ordinal) || open == "two";
                return (used ? "Q + 0" : "X + 0", target);
            }
            var expression = (pos, end) switch
            {
                ("value", "missing") => $"{container}.Missing + 0",
                ("value", _) => $"{container}{Step}.Q + 0",
                ("callee", _) => $"{container}{Step}.G(1) + 0",
                ("spread", _) => $"sum({container}{Step}.Q*) + 0",
                ("fallback", _) => $"{container}.Q.Missing + 0",
                _ => throw new InvalidOperationException(pos),
            };
            return (expression, open == "none" ? null : head == "opened" ? "Lib" : container);
        }

        // Concrete level names: "own" (the reader's value block), "B" / "N" (a block or deep reader's
        // enclosing level), the placement level (F, Lib, Box, Mid), and its parent.
        private string Level(string relative) => relative switch
        {
            "own" => "own",
            "enc1" => reader switch { "block" => "B", "deep" => "N", _ => PlacementLevel },
            "enc2" => reader is "block" or "deep" ? PlacementLevel : PlacementParent,
            _ => throw new ArgumentOutOfRangeException(nameof(relative)),
        };

        private string PlacementLevel => place switch { "in-lib" => "Lib", "in-box" => "Box", "in-mid" => "Mid", _ => "F" };
        private string PlacementParent => place switch { "in-lib" => "F", "in-box" or "in-mid" => "Lib", _ => "root" };

        private Dictionary<string, string> Opens(string? target)
        {
            var opens = new Dictionary<string, string>(StringComparer.Ordinal);
            if (target is null) return opens;
            if (open == "two")
            {
                opens["own"] = "open Other";
                opens[Level("enc1")] = $"open {target}";
                return opens;
            }
            var relative = open[..open.IndexOf('-')];
            var used = open.EndsWith("-used", StringComparison.Ordinal);
            opens[Level(relative)] = used ? $"open {target}"
                : head == "opened" ? $"open {Path}, Lib" : $"open {target}, Other";
            return opens;
        }

        private static string OpenLine(Dictionary<string, string> opens, string level)
            => opens.TryGetValue(level, out var line) ? line + "\n" : "";

        private string ReaderCall => reader switch
        {
            "plain" => "A", "param" => "A(0)", "clause" => "K(0)", "block" => "B(0)", "deep" => "N",
            _ => throw new ArgumentOutOfRangeException(nameof(reader)),
        };

        private string ReaderDeclarations(string expression, Dictionary<string, string> opens)
        {
            var inner = opens.ContainsKey("own") ? $"{{\n  {opens["own"]}\n  {Indent(expression, 2).TrimStart()}\n}}" : expression;
            return reader switch
            {
                "plain" => $"A = {inner}",
                "param" => $"A(z) = {inner}",
                "clause" => $"K(0) = {inner}\nK(n) = n",
                "block" => $"B(w) = {{\n{Indent(OpenLine(opens, "B") + "D = " + inner + "\nD", 2)}\n}}",
                "deep" => $"N = {{\n{Indent(OpenLine(opens, "N") + "A = " + inner + "\nA", 2)}\n}}",
                _ => throw new ArgumentOutOfRangeException(nameof(reader)),
            };
        }

        public string Body()
        {
            var (container, declarations) = Head();
            var (expression, target) = Use(container);
            var opens = Opens(target);
            var readers = ReaderDeclarations(expression, opens);

            string LevelBody(string level, string members, string output)
                => Indent(OpenLine(opens, level) + members + (members.Length > 0 ? "\n" : "") + output, 2);

            var sub = PlacedSub();
            string lib = place switch
            {
                "in-box" => $"Lib = {{\n{LevelBody("Lib", $"public Box = {{\n{LevelBody("Box", sub + "\n" + readers, "0")}\n}}", "0")}\n}}",
                "in-mid" => $"Lib = {{\n{LevelBody("Lib", $"public Mid(p) = {{\n{LevelBody("Mid", sub + "\n" + readers, ReaderCall)}\n}}", "0")}\n}}",
                "in-lib" => $"Lib = {{\n{LevelBody("Lib", sub + "\n" + readers, "0")}\n}}",
                _ => $"Lib = {{\n{LevelBody("Lib", sub, "0")}\n}}",
            };

            var members = new List<string> { lib, "Other = {\n  public X = 1\n  public Z = 2\n}" };
            members.AddRange(declarations);
            // Every fallback READS its receiver (`r * 0`), so the receiver's value is a read the evaluator
            // performs; the unread form is the fixed case `fallback-unread-receiver`.
            if (!CensusGrid.IsOpenPosition(pos) && (pos == "fallback" || end == "missing"))
                members.Add("Missing(r) = r * 0 + 2");
            if (head is "rt-param" or "rt-member" && !CensusGrid.IsOpenPosition(pos))
            {
                members.Add("Q(r) = r * 0 + 1");
                members.Add("G(r, k) = r * 0 + k");
            }
            if (head == "rt-member") members.Add("C(r) = r");
            if (place == "outside") members.Add(readers);
            var output = place switch
            {
                "in-lib" => "Lib." + ReaderCall,
                "in-box" => "Lib.Box." + ReaderCall,
                "in-mid" => "Lib.Mid(y)",
                _ => ReaderCall,
            };
            var root = OpenLine(opens, "root");
            return $"{root}F(y) = {{\n{LevelBody("F", string.Join("\n", members), output)}\n}}\n";
        }

        public IReadOnlyList<CensusReader> Readers()
        {
            string[] prefix = place switch
            {
                "in-lib" => ["F", "Lib"],
                "in-box" => ["F", "Lib", "Box"],
                "in-mid" => ["F", "Lib", "Mid"],
                _ => ["F"],
            };
            var dotted = string.Join(".", prefix);
            CensusReader R(string label, string[] tail, string escaped)
                => new(label, [.. prefix, .. tail], $"{dotted}.{escaped}");
            return reader switch
            {
                "plain" => [R("A", ["A"], "A")],
                "param" => [R("A", ["A"], "A(0)")],
                "clause" => [R("K", ["K"], "K(0)")],
                "block" => [R("B", ["B"], "B(0)"), R("D", ["B", "D"], "B.D")],
                "deep" => [R("A", ["N", "A"], "N.A"), R("N", ["N"], "N")],
                _ => throw new ArgumentOutOfRangeException(nameof(reader)),
            };
        }
    }

    internal static string Indent(string text, int spaces)
    {
        var pad = new string(' ', spaces);
        var builder = new StringBuilder();
        var lines = text.Split('\n');
        for (var i = 0; i < lines.Length; i++)
        {
            if (i > 0) builder.Append('\n');
            if (lines[i].Length > 0) builder.Append(pad).Append(lines[i]);
        }
        return builder.ToString();
    }
}
