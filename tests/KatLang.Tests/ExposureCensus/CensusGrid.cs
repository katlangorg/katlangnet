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
    string Kind = "grid",
    string? ImpossibleSubject = null)
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
    // `deconstruction` reads the selection in a deconstruction right-hand side, `a, b = <selection> + 0, 0`,
    // and returns the targets: the evaluators wire whatever that side writes (an inline block head) under the
    // synthetic source property, one runtime level below the reader (da209fa0). Its twin returns the same
    // right-hand side as the reader's own row (`DeconstructionTwin`, check T of `CensusRunner.Run`).
    public static readonly string[] Positions = ["value", "callee", "spread", "fallback", "open", "open-dotted", "deconstruction"];

    // 3. Which open level the lookup consults (used: the target provides the name; unused: Other does).
    public static readonly string[] OpenLevels =
        ["none", "own-unused", "enc1-unused", "own-used", "enc1-used", "enc2-used", "enc2-unused", "two"];

    // 4. The reader.
    public static readonly string[] ReaderKinds = ["plain", "param", "clause", "block", "deep"];

    // 5. Where the reader sits relative to the open target's path.
    public static readonly string[] Places = ["outside", "in-lib", "in-box", "in-mid"];

    // 6. How the selection ends. `missing` misses at the FINAL edge (`<head>.Missing`); `mid-fallback` misses at
    // an INTERMEDIATE edge and continues through a further fallback (`<head>.Missing.Next`, or after the found
    // member, `<head>.Q.Missing.Next`, in the fallback position): the evaluator calls `Missing` and continues by
    // value, so the path charges that intermediate fallback's callee (da209fa0).
    public static readonly string[] Ends = ["found", "runtime", "missing", "mid-fallback"];

    // 7. What the selected declarations require. `fallback`: nothing in the container, but the lexical fallback
    // `Missing` the selection calls reads `y` (the audit's `T(v) = v + y`); every other value's `Missing` does not.
    public static readonly string[] Requirements = ["none", "container", "member", "deep", "fallback"];

    public static readonly string[] DimensionNames = ["head", "pos", "open", "reader", "place", "end", "req"];

    public static IReadOnlyList<string[]> DimensionValues =>
        [Heads, Positions, OpenLevels, ReaderKinds, Places, Ends, Requirements];

    // THE EXTENSION (2026-11-17): dimension values that only GenerateExtension builds, so that the grid above keeps
    // its cells, its stored cover and every count. Its cells are the combinations of the widened dimensions that use a
    // new value; their own cover is census-extension-subset.txt.
    //
    // Heads. `rt-capture` is a runtime head whose value reads nothing of F: `L = Cap(Seed()).Algorithm`, the
    // algorithm of a captured call of `Seed = 3` (`Cap(meta op) = op`). A dot on it is a runtime dot, as on
    // `rt-param`'s `L = y`, but no y reaches the reader through L, so an intermediate fallback edge that reads y is
    // the reader's only charge (the witness rt-param and rt-member cannot give: their head already charges y).
    // `rt-alg-call` is rt-alg made callable: the same `L = <path>.Algorithm`, over a fixture whose Sub returns a
    // captured call, `Cap(Run())`, of its member `public Run = <Sub's former row>`, so the `.Algorithm` step yields
    // Run's algorithm and the cells produce values (rt-alg applies it to Sub's number and fails with a type error).
    // Its static-route twin selects `<path>.Run` instead (check R of CensusRunner.Run).
    public static readonly string[] ExtensionHeads = ["rt-capture", "rt-alg-call"];

    // Endings. `result-member` misses at an intermediate edge and then reads a MEMBER OF THE FALLBACK'S RESULT. A
    // fallback continues by value and a KatLang value has no declared members (a block a fallback returns is evaluated
    // to its rows, and `.V` after it is itself an extension fallback), so the members a result can have are the
    // intrinsics of a call reference: the fallback returns `Cap(Mk(0))` for its local `Mk(k)`, and the selection reads
    // `.Invoke()` (`.Algorithm(1)` in the callee position), which runs `Mk` and so reads the fallback's receiver.
    public static readonly string[] ExtensionEnds = ["result-member"];

    public static readonly string[] AllHeads = [.. Heads, .. ExtensionHeads];
    public static readonly string[] AllEnds = [.. Ends, .. ExtensionEnds];

    public static bool IsExtension(string head, string end) => ExtensionHeads.Contains(head) || ExtensionEnds.Contains(end);

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
            case "mid-fallback" when IsOpenPosition(pos):
                return "an open target never calls a lexical fallback, so it has no intermediate fallback edge";
            case "result-member" when IsOpenPosition(pos):
                return "an open target never calls a lexical fallback, so it has no fallback result to read a member of";
        }
        if (req == "fallback")
        {
            if (IsOpenPosition(pos)) return "an open target never calls a lexical fallback that could read y";
            if (pos != "fallback" && end is not ("missing" or "mid-fallback" or "result-member"))
                return IsExtension(head, end)
                    ? "the selection calls no Missing fallback (only a missing, mid-fallback or result-member ending or the fallback position does)"
                    : "the selection calls no Missing fallback (only a missing or mid-fallback ending or the fallback position does)";
            if (head == "rt-alg")
                return "rt-alg's L = <path>.Algorithm fails (type) on Sub's numeric value before any fallback reads y";
        }
        return null;
    }

    /// <summary>The grid of <see cref="Heads"/> × … × <see cref="Ends"/> (the cells, cover and counts every mode pins).</summary>
    public static (IReadOnlyList<CensusCase> Cases, IReadOnlyList<CensusExclusion> Excluded) Generate()
        => Generate(Heads, Ends, extension: false);

    /// <summary>
    /// THE EXTENSION GRID: every combination of <see cref="AllHeads"/> × … × <see cref="AllEnds"/> that uses an
    /// <see cref="ExtensionHeads"/> head or an <see cref="ExtensionEnds"/> ending, in generation order. It is disjoint
    /// from <see cref="Generate()"/>, whose cells it never alters, and the two together are the widened grid.
    /// </summary>
    public static (IReadOnlyList<CensusCase> Cases, IReadOnlyList<CensusExclusion> Excluded) GenerateExtension()
        => Generate(AllHeads, AllEnds, extension: true);

    private static (IReadOnlyList<CensusCase> Cases, IReadOnlyList<CensusExclusion> Excluded) Generate(string[] heads, string[] ends, bool extension)
    {
        var cases = new List<CensusCase>();
        var excluded = new List<CensusExclusion>();
        foreach (var head in heads)
        foreach (var pos in Positions)
        foreach (var open in OpenLevels)
        foreach (var reader in ReaderKinds)
        foreach (var place in Places)
        foreach (var end in ends)
        foreach (var req in Requirements)
        {
            if (extension != IsExtension(head, end)) continue;
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

    public static CensusCase Build(IReadOnlyList<string> v) => Build(v, "grid");

    private static CensusCase Build(IReadOnlyList<string> v, string kind)
    {
        var builder = new ProgramShape(v[0], v[1], v[2], v[3], v[4], v[5], v[6], kind == "deconstruction-twin", kind == "static-route-twin");
        var dims = DimensionNames.Select((name, i) => new KeyValuePair<string, string>(name, v[i])).ToArray();
        return new CensusCase(IdOf(v), dims, builder.Body(), builder.Readers(), kind);
    }

    /// <summary>
    /// THE ROWS TWIN of a <c>pos=deconstruction</c> cell: the same program with the reader's deconstruction
    /// <c>a, b = &lt;selection&gt; + 0, 0</c> and the row <c>a, b</c> returning its targets replaced by the right-hand side
    /// itself as the reader's row, <c>&lt;selection&gt; + 0, 0</c>; the dimensions, the readers and every other line are the
    /// cell's own. Returning the targets in order returns the items, so the two programs must give the same probe
    /// outcomes and the same reader metadata (check T of <see cref="CensusRunner.Run"/>). (Two ordinary declarations
    /// <c>a = …</c>, <c>b = 0</c> are no twin: an ordinary declaration infers an implicit parameter for a free name, a
    /// deconstruction target cannot.) The twin is the census's witness for a refusal the evaluator makes INSIDE the
    /// owner's own call, which U and O cannot see: before da209fa0 an inline block written in the right-hand side, wired
    /// under the synthetic source property one runtime level deeper than the same block in the twin's row, published its
    /// members' capture positions on the written chain, and the access was refused (<c>LocalOnlyProperty</c>).
    /// </summary>
    public static CensusCase DeconstructionTwin(CensusCase @case)
    {
        if (@case.Kind != "grid" || @case.Dims.Count == 0 || @case.Dim("pos") != "deconstruction")
            throw new ArgumentException($"Only a pos=deconstruction grid cell has a rows twin: {@case.Id}", nameof(@case));
        return Build(@case.Dims.Select(d => d.Value).ToArray(), "deconstruction-twin");
    }

    /// <summary>
    /// THE STATIC-ROUTE TWIN of a <c>head=rt-alg-call</c> cell: the same program with <c>L = &lt;path&gt;.Algorithm</c>
    /// replaced by <c>L = &lt;path&gt;.Run</c>, the static selection of the algorithm whose call Sub's row captures; the
    /// dimensions, the readers and every other line are the cell's own. The runtime route evaluates Sub, takes its call
    /// reference's algorithm and reads it as a value (it needs no argument, so reading runs it); the static route selects
    /// that same algorithm by name. Every dot the reader writes on <c>L</c> then dispatches on the same value, and both
    /// references read Run (and through it Sub's former row) in L's own scope, so the two programs must give the same
    /// outcome on every probe and the same reader metadata (check R of <see cref="CensusRunner.Run"/>). Open positions are
    /// compared too: OD-C opens the runtime reference's own namespace, but every valid cell of this fixture must still
    /// agree with its static route on the observed outcomes and metadata.
    /// </summary>
    public static CensusCase StaticRouteTwin(CensusCase @case)
    {
        if (@case.Kind != "grid" || @case.Dims.Count == 0 || @case.Dim("head") != "rt-alg-call")
            throw new ArgumentException($"Only a head=rt-alg-call grid cell has a static-route twin: {@case.Id}", nameof(@case));
        return Build(@case.Dims.Select(d => d.Value).ToArray(), "static-route-twin");
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
    /// THE DECLARED COPY of a block-headed reference cell (owner decision D2, 2026-11-15): the same program with the
    /// literal given a name. In the body, the declaration <c>L = { literal }.path</c> becomes <c>Lit = { literal }</c>
    /// followed by <c>L = Lit.path</c> at the same indentation; the dimensions and the readers are the cell's own. It
    /// is the twin Q3 speaks of (a block-headed reference resolves like a named one): the two programs differ in
    /// nothing but how <c>L</c>'s target is headed. The grid's <c>ref1</c> cell is no twin: it points at the real
    /// <c>Lib</c>, which holds the reader and whose <c>Mid</c> is activated, while the literal is a stripped copy
    /// (<c>ProgramShape.BlockHead</c>). A body without exactly one block-headed <c>L</c> declaration throws: no cell
    /// is ever skipped.
    /// </summary>
    public static CensusCase DeclaredCopy(CensusCase @case)
    {
        if (@case.Dims.Count == 0 || @case.Dim("head") != "blockref")
            throw new ArgumentException($"Only a head=blockref cell has a declared copy: {@case.Id}", nameof(@case));
        const string opening = "L = {";
        const string copyName = "Lit";
        var lines = @case.Body.Split('\n').ToList();
        if (lines.Any(line => line.Split(' ', '.', '(', ')', ',').Contains(copyName, StringComparer.Ordinal)))
            throw new InvalidDataException($"The body already uses the name {copyName}: {@case.Id}");
        var starts = Enumerable.Range(0, lines.Count).Where(i => lines[i].TrimStart(' ') == opening).ToArray();
        if (starts.Length != 1)
            throw new InvalidDataException($"Expected one block-headed L declaration, found {starts.Length}: {@case.Id}");
        var start = starts[0];
        var indent = lines[start][..^opening.Length];
        // The literal's lines are indented deeper; the first line that is not is its closer, `}.path`.
        var end = start + 1;
        while (end < lines.Count && lines[end].StartsWith(indent + " ", StringComparison.Ordinal)) end++;
        var closer = indent + "}.";
        var path = end < lines.Count && lines[end].StartsWith(closer, StringComparison.Ordinal) ? lines[end][closer.Length..] : "";
        if (path.Length == 0 || !path.Split('.').All(step => step.Length > 0 && step.All(char.IsAsciiLetter)))
            throw new InvalidDataException($"The block-headed L declaration does not end in a member path: {@case.Id}");
        lines[start] = $"{indent}{copyName} = {{";
        lines[end] = indent + "}";
        lines.Insert(end + 1, $"{indent}L = {copyName}.{path}");
        return @case with { Body = string.Join("\n", lines), Kind = "declared-copy" };
    }

    /// <summary>
    /// THE IMPOSSIBLE CHECK of a grid cell, described from the grid's own terms and never from exposure metadata: the
    /// member whose access check can never pass at the site where the evaluator performs it, or null when the cell has
    /// none (owner decisions Q1 and Q2, 2026-11-14: such a check charges nothing). Only a <c>req=deep</c> cell has a
    /// candidate: <c>Sub</c> requires <c>p</c> of <c>Mid(p)</c>, so its check passes only at a site inside that
    /// <c>Mid</c>. The site is:
    /// <list type="bullet">
    /// <item>nowhere, for a head written as a literal (<c>block</c>, <c>group-block</c>, <c>blockref</c>): the
    /// <c>Mid</c> it selects is declared inside the literal, so no site lies inside it;</item>
    /// <item>the CONSULTED level, the level that holds the <c>open</c>, for an open position (a crossed reference's
    /// target walk included);</item>
    /// <item>the reference's OWN scope for a value crossing (<c>ref1</c>, <c>chain2</c>, <c>refmem</c>, and the
    /// route navigation of <c>rt-alg</c>): every reference is declared in <c>F</c>, outside <c>Mid</c>;</item>
    /// <item>the READING site for a written path (<c>name</c>, <c>group-name</c>) and for an opened head, which is
    /// placed outside only. A deconstruction's right-hand side is read in the reader's own body, so that is its
    /// reading site too, and an intermediate or final fallback reads its receiver only after the path has selected
    /// it there.</item>
    /// </list>
    /// A runtime head (<c>rt-param</c>, <c>rt-member</c>, <c>rt-capture</c>) selects nothing statically; the callable
    /// <c>rt-alg-call</c> navigates its route in the reference's own scope, as <c>rt-alg</c> does. A settlement case
    /// carries its impossible member, derived from its own program (<see cref="CensusCase.ImpossibleSubject"/>).
    /// </summary>
    public static string? ImpossibleMember(CensusCase @case)
    {
        if (@case.Kind == "settlement") return @case.ImpossibleSubject;
        if (@case.Dims.Count == 0 || @case.Dim("req") != "deep") return null;
        var (head, pos, place) = (@case.Dim("head"), @case.Dim("pos"), @case.Dim("place"));
        if (head is "rt-param" or "rt-member" or "rt-capture") return null;
        if (head is "block" or "group-block" or "blockref") return "Sub";
        if (IsOpenPosition(pos)) return ConsultedLevelIsInsideMid(@case.Dim("open"), @case.Dim("reader"), place) ? null : "Sub";
        return head is "name" or "group-name" && place == "in-mid" ? null : "Sub";
    }

    // The level an open position writes its target on (ProgramShape.Opens): the reader's own value block, a block or
    // deep reader's enclosing level, the placement level, or the placement level's parent. Inside Lib.Mid exactly
    // when the reader is placed there and the level is not Mid's parent.
    private static bool ConsultedLevelIsInsideMid(string open, string reader, string place)
    {
        if (place != "in-mid") return false;
        var relative = open == "two" ? "enc1" : open[..open.IndexOf('-')];
        return relative != "enc2" || reader is "block" or "deep";
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
    /// THE SETTLEMENT FAMILIES (2026-11-17): the nested-read and re-entry witnesses of
    /// <see cref="ExposureSettlementFootprintTests"/> (0a1718d2), written as census cases inside <c>F(y)</c> so that
    /// every check of <see cref="CensusRunner.Run"/> examines them. The nested-read programs read a member of
    /// <c>Mid(y)</c> back through <c>F.Mid</c> from inside <c>Mid</c>, one to three frames deep (the footprint must
    /// keep the settlement under <c>Mid</c> apart from the one without it); <c>Mid</c> is called with <c>y + 2</c>
    /// (the footprint tests' <c>Mid(7)</c>) so that the inside probes depend on the activation. The re-entry programs
    /// reach <c>F.G</c> from the off-chain <c>K.M</c> and from <c>F</c> itself, and the hop program reads
    /// <c>F.Mid.X</c> from <c>Mid</c>'s sibling <c>Hop</c>. A check made at <c>K.M</c>'s or <c>Hop</c>'s site can
    /// never pass there, so it charges nothing (owner decision Q1, 2026-11-14): each re-entry case names that member
    /// as its <see cref="CensusCase.ImpossibleSubject"/>, derived from the program and not from its metadata.
    /// </summary>
    public static IReadOnlyList<CensusCase> SettlementFamilies()
    {
        static CensusReader R(string label, string path, string escaped) => new(label, path.Split('.'), escaped);
        static CensusCase Family(string name, string body, string? impossible, params CensusReader[] readers)
            => new($"settlement={name}", [], body, readers, "settlement", impossible);
        CensusReader[] mid = [R("Mid", "F.Mid", "F.Mid(1)"), R("X", "F.Mid.X", "F.Mid.X")];
        const string offChain = "K = {\n  public M(z) = F.G + z\n}\n";
        return
        [
            Family("nested-read-1", "F(y) = {\n  Mid(y) = {\n    public X = y\n    Read = F.Mid.X\n    Read\n  }\n  Mid(y + 2)\n}\n", null,
                [.. mid, R("Read", "F.Mid.Read", "F.Mid.Read")]),
            Family("nested-read-2", "F(y) = {\n  Mid(y) = {\n    public X = y\n    public Y = F.Mid.X\n    Read = F.Mid.Y\n    Read\n  }\n  Mid(y + 2)\n}\n", null,
                [.. mid, R("Y", "F.Mid.Y", "F.Mid.Y"), R("Read", "F.Mid.Read", "F.Mid.Read")]),
            Family("nested-read-3",
                "F(y) = {\n  Mid(y) = {\n    public X = y\n    public Y = F.Mid.X + 1\n    public Z = F.Mid.Y + 1\n    Read = F.Mid.Z\n    Read\n  }\n  Mid(y + 2)\n}\n", null,
                [.. mid, R("Y", "F.Mid.Y", "F.Mid.Y"), R("Z", "F.Mid.Z", "F.Mid.Z"), R("Read", "F.Mid.Read", "F.Mid.Read")]),
            Family("nested-read-4", "F(y) = {\n  Mid(y) = {\n    public X = y\n    public Y(k) = F.Mid.X + k\n    Read = F.Mid.Y(1)\n    Read\n  }\n  Mid(y + 2)\n}\n", null,
                [.. mid, R("Y", "F.Mid.Y", "F.Mid.Y(1)"), R("Read", "F.Mid.Read", "F.Mid.Read")]),
            // Two owners with the same parameter spelling around the same nested-read shape (SameNamedParametersOfDistinctOwners).
            Family("nested-read-owners",
                "F(y) = {\n  O(y) = {\n    Mid(y) = {\n      public X = y\n      public Y = O.Mid.X\n      Read = O.Mid.Y\n      Read\n    }\n    Mid(y + 2)\n  }\n"
                + "  P(y) = {\n    Mid(y) = {\n      public X = y\n      public Y = P.Mid.X\n      Read = P.Mid.Y\n      Read\n    }\n    Mid(y + 3)\n  }\n  O(y) + P(y)\n}\n", null,
                R("O", "F.O", "F.O(1)"), R("P", "F.P", "F.P(1)"), R("OX", "F.O.Mid.X", "F.O.Mid.X"),
                R("ORead", "F.O.Mid.Read", "F.O.Mid.Read"), R("PRead", "F.P.Mid.Read", "F.P.Mid.Read")),
            Family("re-entry-1", offChain + "F(y) = {\n  public G = y + 1\n  public H = K.M(1)\n  H\n}\n", "G",
                R("G", "F.G", "F.G"), R("H", "F.H", "F.H")),
            Family("re-entry-2", "F(y) = {\n  public G = y + 1\n  public H(k) = K.M(1) + k\n  H(1)\n}\n" + offChain, "G",
                R("G", "F.G", "F.G"), R("H", "F.H", "F.H(1)")),
            Family("re-entry-3", "F(y) = {\n  public G = y + 1\n  public H(k) = F.G + k\n  public H3(k) = F.G + k\n  H3(1)\n}\n" + offChain, "G",
                R("G", "F.G", "F.G"), R("H", "F.H", "F.H(1)"), R("H3", "F.H3", "F.H3(1)")),
            Family("re-entry-4", "F(y) = {\n  public G = y + 1\n  public H(k) = F.G + k\n  public H3(k) = K.M(1) + k\n  H3(1)\n}\n" + offChain, "G",
                R("G", "F.G", "F.G"), R("H", "F.H", "F.H(1)"), R("H3", "F.H3", "F.H3(1)")),
            Family("re-entry-5", "F(y) = {\n  public G = y + 1\n  public H(k) = F.G + k\n  H(1)\n}\n" + offChain, "G",
                R("G", "F.G", "F.G"), R("H", "F.H", "F.H(1)")),
            Family("re-entry-hop",
                "F(y) = {\n  Mid(y) = {\n    public X = y\n    public Y = Hop.V\n    Read = F.Mid.Y\n    Read\n  }\n  Hop = {\n    public V = F.Mid.X\n  }\n  Mid(y + 2)\n}\n", "X",
                [.. mid, R("Y", "F.Mid.Y", "F.Mid.Y"), R("Read", "F.Mid.Read", "F.Mid.Read"), R("V", "F.Hop.V", "F.Hop.V")]),
        ];
    }

    /// <summary>
    /// A deterministic subset covering every combination of three dimension values that occurs in some
    /// case of <paramref name="cases"/> (greedy covering array; ties broken by generation order).
    /// </summary>
    public static IReadOnlyList<CensusCase> ThreeWayCover(IReadOnlyList<CensusCase> cases) => ThreeWayCover(cases, covered: null);

    /// <summary>
    /// The greedy cover of every triple of <paramref name="cases"/> that <paramref name="covered"/> lacks (the extension's
    /// cover: the extension cells' triples that no valid cell of the grid has, so that the two stored covers together hold
    /// every valid triple of the widened grid). With no <paramref name="covered"/> it is <see cref="ThreeWayCover(IReadOnlyList{CensusCase})"/>.
    /// </summary>
    public static IReadOnlyList<CensusCase> ThreeWayCover(IReadOnlyList<CensusCase> cases, IReadOnlySet<string>? covered)
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
        if (covered is not null) uncovered.ExceptWith(covered);
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

    public static int TripleCount(IReadOnlyList<CensusCase> cases) => Triples(cases).Count;

    /// <summary>Every combination of three dimension values that occurs in some case (the keys the cover counts).</summary>
    public static HashSet<string> Triples(IReadOnlyList<CensusCase> cases)
    {
        var keys = new HashSet<string>(StringComparer.Ordinal);
        var dims = DimensionNames.Length;
        foreach (var @case in cases)
            for (var a = 0; a < dims; a++)
                for (var b = a + 1; b < dims; b++)
                    for (var c = b + 1; c < dims; c++)
                        keys.Add($"{a}={@case.Dims[a].Value};{b}={@case.Dims[b].Value};{c}={@case.Dims[c].Value}");
        return keys;
    }

    /// <summary>
    /// The program text of one grid cell (with <paramref name="rowsTwin"/>, its <see cref="DeconstructionTwin"/>; with
    /// <paramref name="staticRoute"/>, its <see cref="StaticRouteTwin"/>).
    /// </summary>
    private sealed class ProgramShape(string head, string pos, string open, string reader, string place, string end, string req, bool rowsTwin,
        bool staticRoute = false)
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

        // The callable variant of rt-alg-call: Sub's row moves into its member Run, and Sub returns a captured call of Run.
        private string Sub() => head == "rt-alg-call"
            ? $"public Sub = {{\n  public Q = {Q}\n  public G(x) = {G}\n  public T = {{\n    public Q = {Q}\n  }}\n  public Run = {SubRow}\n  Cap(Run())\n}}"
            : $"public Sub = {{\n  public Q = {Q}\n  public G(x) = {G}\n  public T = {{\n    public Q = {Q}\n  }}\n  {SubRow}\n}}";

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

        // A head whose dots are runtime dots on L's value, answered by F's fallbacks Q and G.
        private bool RuntimeValueHead => head is "rt-param" or "rt-member" or "rt-capture" or "rt-alg-call";

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
            "rt-capture" => ("L", ["Seed = 3", "L = Cap(Seed()).Algorithm"]),
            "rt-alg-call" => ("L", [staticRoute ? $"L = {Path}.Run" : $"L = {Path}.Algorithm"]),
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
                ("value", "mid-fallback") => $"{container}.Missing.Next + 0",
                ("value", "result-member") => $"{container}.Missing.Invoke() + 0",
                ("value", _) => $"{container}{Step}.Q + 0",
                // The intermediate miss's continuation is the final edge, here a call (`Next(v, k)`; for a member of the
                // fallback's result, the captured algorithm called afresh, `Mk(1)`).
                ("callee", "mid-fallback") => $"{container}.Missing.Next(1) + 0",
                ("callee", "result-member") => $"{container}.Missing.Algorithm(1) + 0",
                ("callee", _) => $"{container}{Step}.G(1) + 0",
                ("spread", "mid-fallback") => $"sum({container}.Missing.Next*) + 0",
                ("spread", "result-member") => $"sum({container}.Missing.Invoke()*) + 0",
                ("spread", _) => $"sum({container}{Step}.Q*) + 0",
                // The found member is the receiver: the miss after it is intermediate (the audit's `Box.S.T.U`).
                ("fallback", "mid-fallback") => $"{container}.Q.Missing.Next + 0",
                ("fallback", "result-member") => $"{container}.Q.Missing.Invoke() + 0",
                ("fallback", _) => $"{container}.Q.Missing + 0",
                // A deconstruction, then the row returning its targets; the rows twin returns the right-hand side itself.
                ("deconstruction", _) => rowsTwin
                    ? $"{Selected(container)} + 0, 0"
                    : $"a, b = {Selected(container)} + 0, 0\na, b",
                _ => throw new InvalidOperationException(pos),
            };
            return (expression, open == "none" ? null : head == "opened" ? "Lib" : container);
        }

        // The selection a value read makes, by ending (the value position's expression without `+ 0`).
        private string Selected(string container) => end switch
        {
            "missing" => $"{container}.Missing",
            "mid-fallback" => $"{container}.Missing.Next",
            "result-member" => $"{container}.Missing.Invoke()",
            _ => $"{container}{Step}.Q",
        };

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
            // A deconstruction and its rows are always the reader's own body (braces are no scope of their own);
            // its other clause then returns two items too.
            var inner = pos == "deconstruction" ? $"{{\n{Indent(OpenLine(opens, "own") + expression, 2)}\n}}"
                : opens.ContainsKey("own") ? $"{{\n  {opens["own"]}\n  {Indent(expression, 2).TrimStart()}\n}}" : expression;
            return reader switch
            {
                "plain" => $"A = {inner}",
                "param" => $"A(z) = {inner}",
                "clause" => $"K(0) = {inner}\nK(n) = {(pos == "deconstruction" ? "n, n" : "n")}",
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
            // The extension's call references: the rt-capture and rt-alg-call heads and a result-member fallback capture.
            if (head is "rt-capture" or "rt-alg-call" || (!CensusGrid.IsOpenPosition(pos) && end == "result-member"))
                members.Add("Cap(meta op) = op");
            members.AddRange(declarations);
            // Every fallback READS its receiver (`r * 0`), so the receiver's value is a read the evaluator
            // performs; the unread form is the fixed case `fallback-unread-receiver`. Under `req=fallback` the
            // callee `Missing` also reads `y`; the continuation `Next` of an intermediate miss never does. A
            // result-member ending's `Missing` returns a captured call of its local `Mk`, which reads the receiver
            // (and y) when the selection's `.Invoke()` or `.Algorithm(1)` runs it.
            if (!CensusGrid.IsOpenPosition(pos) && end == "result-member")
                members.Add($"Missing(r) = {{\n  Mk(k) = r * 0 + k + {(req == "fallback" ? "y" : "2")}\n  Cap(Mk(0))\n}}");
            else if (!CensusGrid.IsOpenPosition(pos) && (pos == "fallback" || end is "missing" or "mid-fallback"))
                members.Add(req == "fallback" ? "Missing(r) = r * 0 + y" : "Missing(r) = r * 0 + 2");
            if (!CensusGrid.IsOpenPosition(pos) && end == "mid-fallback")
                members.Add(pos == "callee" ? "Next(v, k) = v + k" : "Next(v) = v");
            if (RuntimeValueHead && !CensusGrid.IsOpenPosition(pos))
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
