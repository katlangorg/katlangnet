using System.Text;

namespace KatLang.Tests.ExposureCensus;

/// <summary>
/// One generated census program: a source body declaring <c>F(y)</c> (no root row), the readers the
/// checks examine and the dimension values that produced it. <see cref="Dims"/> is empty for a fixed
/// control or self-check case. A case whose body loads modules carries the sources its in-memory module
/// server answers (<see cref="Modules"/>, URL to text): the runner then parses every probe through the
/// asynchronous front end over a fresh server of exactly those sources.
/// </summary>
internal sealed record CensusCase(
    string Id,
    IReadOnlyList<KeyValuePair<string, string>> Dims,
    string Body,
    IReadOnlyList<CensusReader> Readers,
    string Kind = "grid",
    string? ImpossibleSubject = null,
    IReadOnlyList<KeyValuePair<string, string>>? Modules = null)
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

    // THE MODULE DIMENSION (2026-11-19): how the open level's SECOND provider, the one that gives the reader its name, is
    // reached when it is a loaded module. A module cell is a cell of the widened grid (its PROVIDER TWIN, the grid or
    // extension cell of the same seven values) whose open level writes the module instead of `Other`: `open <target>,
    // ModA, ModB` for `holders` (two root holders, `ModA = load(<url>)` and `ModB = load(<url>)`, of ONE canonical URL) and
    // `open <target>, ModA, load(<url>)` for `holder-load` (one holder and a written load of it). The module text is
    // `Other`'s members, so one module is one provider of `X` exactly as `Other` is (Q-32 I-U), and the cell must give what
    // its twin gives (check P). The control `two-urls` holds two DISTINCT canonical URLs serving that same text, so the two
    // holders are two providers: the unqualified read `X` is the front end's AmbiguousOpen (the control's provider verdict),
    // and the evaluated fixture reads `ModA.X` instead, a clean qualified access in the same program. That read is lexical
    // (the owner walk finds `ModA` before any open), so it is no twin of the cell reading `X`. Only an open position's unused level reads a name the
    // second provider gives, so module cells exist there alone; every cell's dimensions are its twin's seven plus `module`,
    // and its id is the twin's id followed by `|module=<value>`.
    public static readonly string[] ModuleValues = ["holders", "holder-load", "two-urls"];

    public static readonly string[] ModuleDimensionNames = [.. DimensionNames, "module"];

    public const string ModuleUrl = "https://mods.test/other.kat";
    public const string ModuleCopyUrl = "https://mods.test/other-copy.kat";

    /// <summary>The loaded module's text: <c>Other</c>'s members (<c>Other = { public X = 1; public Z = 2 }</c>).</summary>
    public const string ModuleText = "public X = 1\npublic Z = 2\n";

    /// <summary>The sources a module cell's server answers: one URL for one module, two serving the same text for the control.</summary>
    public static IReadOnlyList<KeyValuePair<string, string>> ModuleSources(string module) => module == "two-urls"
        ? [new(ModuleUrl, ModuleText), new(ModuleCopyUrl, ModuleText)]
        : [new(ModuleUrl, ModuleText)];

    /// <summary>Whether the widened grid's cell of these values is the provider twin of module cells.</summary>
    public static bool HasModuleCells(string pos, string open) => IsOpenPosition(pos) && open.EndsWith("-unused", StringComparison.Ordinal);

    /// <summary>Why a module cell of a provider twin is not built, or <c>null</c> when it is generated.</summary>
    public static string? ModuleExclusion(string reader, string open, string module)
    {
        if (module == "holder-load" && reader == "clause" && open == "own-unused")
            return "a written load in a clause branch is a deferred module region, which the synchronous routes and the Lean encoding refuse";
        return null;
    }

    /// <summary>
    /// The provider verdict a module cell must show: the module providers of X at the reader, the distinct module
    /// identities in its tree, the URLs its probe downloaded, and the front end's verdict on the UNQUALIFIED read
    /// <c>X</c> (the cell itself, except for the control, whose evaluated fixture reads <c>ModA.X</c>).
    /// </summary>
    public static string ExpectedProviderVerdict(CensusCase @case) => @case.Kind == "carrier" ? Carrier(@case).Verdict
        : @case.Dim("module") == "two-urls"
        ? $"providers 2; identities 2; fetched {ModuleCopyUrl},{ModuleUrl}; unqualified AmbiguousOpen"
        : $"providers 1; identities 1; fetched {ModuleUrl}; unqualified clean";

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
    /// THE MODULE CELLS (2026-11-19): for every generated cell of the widened grid (<see cref="Generate()"/>, then
    /// <see cref="GenerateExtension"/>) that has module cells (<see cref="HasModuleCells"/>), one cell per
    /// <see cref="ModuleValues"/> value, in that order. The cells of both grids are untouched: a module cell is a program of
    /// its own, its twin's body with the second provider loaded (<see cref="ModuleValues"/>).
    /// </summary>
    public static (IReadOnlyList<CensusCase> Cases, IReadOnlyList<CensusExclusion> Excluded) GenerateModules()
    {
        var cases = new List<CensusCase>();
        var excluded = new List<CensusExclusion>();
        foreach (var head in AllHeads)
        foreach (var pos in Positions)
        foreach (var open in OpenLevels)
        foreach (var reader in ReaderKinds)
        foreach (var place in Places)
        foreach (var end in AllEnds)
        foreach (var req in Requirements)
        {
            if (!HasModuleCells(pos, open) || Exclusion(head, pos, open, reader, place, end, req) is not null) continue;
            foreach (var module in ModuleValues)
            {
                string[] values = [head, pos, open, reader, place, end, req, module];
                if (ModuleExclusion(reader, open, module) is { } reason)
                {
                    excluded.Add(new CensusExclusion(ModuleIdOf(values), reason));
                    continue;
                }
                cases.Add(BuildModule(values));
            }
        }
        return (cases, excluded);
    }

    public static string ModuleIdOf(IReadOnlyList<string> values) => $"{IdOf(values)}|module={values[7]}";

    /// <summary>A module cell from its eight values (the twin's seven and <c>module</c>).</summary>
    public static CensusCase BuildModule(IReadOnlyList<string> v)
    {
        if (v.Count != ModuleDimensionNames.Length || !ModuleValues.Contains(v[7]) || !HasModuleCells(v[1], v[2]))
            throw new ArgumentException($"Not a module cell: {string.Join("|", v)}", nameof(v));
        var builder = new ProgramShape(v[0], v[1], v[2], v[3], v[4], v[5], v[6], rowsTwin: false, module: v[7]);
        var dims = ModuleDimensionNames.Select((name, i) => new KeyValuePair<string, string>(name, v[i])).ToArray();
        return new CensusCase(ModuleIdOf(v), dims, builder.Body(), builder.Readers(), "module", Modules: ModuleSources(v[7]));
    }

    // The control's qualified fixture, the only place a module cell reads a module member through its holder.
    private const string QualifiedRead = "ModA.X + 0";

    /// <summary>The PROVIDER TWIN of a module cell: the grid or extension cell of its first seven values (check P).</summary>
    public static CensusCase ModuleTwin(CensusCase @case)
    {
        if (@case.Kind != "module") throw new ArgumentException($"Only a module cell has a provider twin: {@case.Id}", nameof(@case));
        return Build(@case.Dims.Take(DimensionNames.Length).Select(d => d.Value).ToArray());
    }

    /// <summary>
    /// The UNQUALIFIED READ of a module cell, the front-end control of its provider verdict: the cell's own program reading
    /// <c>X</c>. It is the cell itself when the body reads <c>X</c> already (one module); the control <c>two-urls</c>'s
    /// fixture reads <c>ModA.X</c> once, and the read replaces it, so two providers of <c>X</c> make it AmbiguousOpen. A
    /// carrier case (<see cref="CarrierFamilies"/>) and its ordinary twin have theirs by the same rule.
    /// </summary>
    public static CensusCase ModuleUnqualifiedRead(CensusCase @case)
    {
        if (@case.Kind is not ("module" or "carrier" or "carrier-twin"))
            throw new ArgumentException($"Only a module cell or a carrier case has an unqualified read: {@case.Id}", nameof(@case));
        var at = @case.Body.IndexOf(QualifiedRead, StringComparison.Ordinal);
        if (at < 0) return @case;
        if (@case.Body.IndexOf(QualifiedRead, at + 1, StringComparison.Ordinal) >= 0)
            throw new InvalidDataException($"The module cell reads {QualifiedRead} more than once: {@case.Id}");
        return @case with { Body = @case.Body[..at] + "X + 0" + @case.Body[(at + QualifiedRead.Length)..], Kind = "module-unqualified" };
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
        if (@case.Kind == "deconstruction-family")
            return @case with { Body = Deconstruction(@case).Body(rowsTwin: true, staticRoute: false), Kind = "deconstruction-twin" };
        if (!HasRowsTwin(@case))
            throw new ArgumentException($"Only a pos=deconstruction grid cell or a deconstruction family case has a rows twin: {@case.Id}", nameof(@case));
        return Build(@case.Dims.Select(d => d.Value).ToArray(), "deconstruction-twin");
    }

    /// <summary>Whether check T compares the case with its rows twin: a <c>pos=deconstruction</c> grid cell or a deconstruction family case.</summary>
    public static bool HasRowsTwin(CensusCase @case)
        => @case.Kind == "deconstruction-family" || (@case.Kind == "grid" && @case.Dims.Count > 0 && @case.Dim("pos") == "deconstruction");

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
        if (@case.Kind == "deconstruction-family" && Deconstruction(@case).StaticSelection is not null)
            return @case with { Body = Deconstruction(@case).Body(rowsTwin: false, staticRoute: true), Kind = "static-route-twin" };
        if (!HasStaticRouteTwin(@case))
            throw new ArgumentException($"Only a head=rt-alg-call grid cell or the inline .Algorithm family case has a static-route twin: {@case.Id}", nameof(@case));
        return Build(@case.Dims.Select(d => d.Value).ToArray(), "static-route-twin");
    }

    /// <summary>
    /// Whether check R compares the case with its static-route twin: every <c>rt-alg-call</c> grid cell, and the deconstruction
    /// family case that writes the same <c>.Algorithm</c> route inline.
    /// </summary>
    public static bool HasStaticRouteTwin(CensusCase @case)
        => @case.Kind == "deconstruction-family" ? Deconstruction(@case).StaticSelection is not null
            : @case.Kind == "grid" && @case.Dims.Count > 0 && @case.Dim("head") == "rt-alg-call";

    /// <summary>The grid or extension cell of a seven-value id, or the module cell of an eight-value one (null otherwise).</summary>
    public static CensusCase? TryParseId(string id)
    {
        var parts = id.Split('|');
        if (parts.Length != DimensionNames.Length && parts.Length != ModuleDimensionNames.Length) return null;
        var values = new string[parts.Length];
        for (var i = 0; i < parts.Length; i++)
        {
            var prefix = ModuleDimensionNames[i] + "=";
            if (!parts[i].StartsWith(prefix, StringComparison.Ordinal)) return null;
            values[i] = parts[i][prefix.Length..];
        }
        if (values.Length == DimensionNames.Length) return Build(values);
        return ModuleValues.Contains(values[7]) && HasModuleCells(values[1], values[2]) ? BuildModule(values) : null;
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
    /// carries its impossible member, derived from its own program (<see cref="CensusCase.ImpossibleSubject"/>). A module
    /// cell has its provider twin's: a loaded second provider moves no check site.
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

    // ── The deconstruction family (2026-11-20) ────────────────────────────────────────────────────

    /// <summary>
    /// One program of <see cref="DeconstructionFamilies"/>: F's declarations and the SELECTION the reader's deconstruction
    /// reads (<c>a, b = &lt;selection&gt; + 0, 0</c>, then the row <c>a, b</c>), with the same selection over the static route
    /// when the case has one.
    /// </summary>
    private sealed record DeconstructionShape(string Name, string[] Declarations, string Selection, string? StaticSelection = null)
    {
        public string Body(bool rowsTwin, bool staticRoute)
        {
            var selection = staticRoute ? StaticSelection ?? throw new InvalidOperationException($"{Name} has no static route.") : Selection;
            var rows = rowsTwin ? $"{selection} + 0, 0" : $"a, b = {selection} + 0, 0\na, b";
            return $"F(y) = {{\n{Indent(string.Join("\n", [.. Declarations, $"A = {{\n{Indent(rows, 2)}\n}}", "A"]), 2)}\n}}\n";
        }
    }

    private const string CapDeclaration = "Cap(meta op) = op";
    private const string ResultMemberFallback = "Missing(r) = {\n  Mk(k) = r * 0 + k + 2\n  Cap(Mk(0))\n}";

    private static readonly DeconstructionShape[] DeconstructionShapes =
    [
        // rt-alg-call's route with its fixture written in the right-hand side: Sub returns a captured call of its member Run.
        new("inline-alg-call", [CapDeclaration],
            "{\n  public Sub = {\n    public Run = y\n    Cap(Run())\n  }\n}.Sub.Algorithm",
            "{\n  public Sub = {\n    public Run = y\n    Cap(Run())\n  }\n}.Sub.Run"),
        // rt-capture's route with the captured call's holder written in the right-hand side, read by either intrinsic.
        new("inline-capture", [CapDeclaration], "Cap({\n  public Seed = y\n}.Seed()).Algorithm"),
        new("inline-capture-invoke", [CapDeclaration], "Cap({\n  public Seed = y\n}.Seed()).Invoke()"),
        // The result-member ending's callee form: the fallback result's captured algorithm called afresh, its argument read
        // from a block written in the right-hand side.
        new("result-member-argument", [CapDeclaration, "Lib = {\n  public Sub = {\n    public Q = 1\n    0\n  }\n  0\n}", ResultMemberFallback],
            "Lib.Sub.Missing.Algorithm({\n  public Q = y\n}.Q)"),
        // The result-member ending over a block written in the right-hand side, the route of the extension's own cells.
        new("result-member-receiver", [CapDeclaration, ResultMemberFallback], "{\n  public Sub = {\n    y\n  }\n}.Sub.Missing.Invoke()"),
    ];

    private static DeconstructionShape Deconstruction(CensusCase @case)
        => DeconstructionShapes.FirstOrDefault(shape => $"deconstruction={shape.Name}" == @case.Id)
            ?? throw new ArgumentException($"Not a deconstruction family case: {@case.Id}", nameof(@case));

    /// <summary>
    /// THE DECONSTRUCTION FAMILY (2026-11-20): the extension's routes with a block WRITTEN IN a deconstruction right-hand
    /// side, each a census case of its own inside <c>F(y)</c> whose reader is <c>A = { a, b = &lt;selection&gt; + 0, 0; a, b }</c>.
    /// The evaluators wire such a block under the synthetic source property, one runtime level below the reader, and
    /// exposure counts that level in the capture positions the block's members publish (da209fa0,
    /// <c>ExposureWalkMemos.ForDeconstructionSourceRows</c>). A position counted on the written chain alone names the
    /// source's level, which binds nothing, and the member is refused inside its own owner's call: the rows twin
    /// (<see cref="DeconstructionTwin"/>), whose block is wired under the reader itself, then gives other outcomes, which is
    /// check T's finding.
    ///
    /// <para>Of the original extension's 5,985 valid deconstruction cells, 5,545 write no
    /// block in its right-hand side (the heads <c>rt-capture</c> and <c>rt-alg-call</c> select through the reference
    /// <c>L</c>, and so does a <c>result-member</c> ending over any head but a literal), so no level is opened from the
    /// source's region. The other 440 have a <c>block</c> or <c>group-block</c> head under <c>result-member</c>, where a selection
    /// reads at most the literal's <c>Sub</c>. With <c>req</c> none, member or fallback, Sub's row is a constant and Sub
    /// publishes no position. With <c>req</c> deep Sub requires the literal's own <c>Mid(p)</c>, a check no site can pass
    /// (<see cref="ImpossibleMember"/>). With <c>req</c> container Sub is captured from <c>F</c>, but the selection is
    /// refused as it stands: a block-headed path that continues through a lexical fallback into a call reference's intrinsic
    /// (<c>{ … }.Sub.Missing.Invoke()</c>) refuses the block's captured member in both evaluators, C# and Lean, in the cell
    /// and in its rows twin alike (<c>LocalOnlyProperty: Sub</c>, also where the fallback's result never reads its
    /// receiver; the same block continued by a lexical edge, <c>.Missing.Next</c>, is admitted). A wrong position
    /// therefore changes no runtime outcome there. <c>result-member-receiver</c> keeps that route as a case, pinned as refused.
    /// The static model checks the positions of unselected declarations too. Under mutation B, M1 refused two existing
    /// extension-cover cells with <c>req=member</c>, one of each block head, on all five probes. The remaining existing
    /// cells with <c>req=member</c> or <c>req=container</c> were outside that model sample.</para>
    ///
    /// <para>The other four write an extension route where the position decides: the callable <c>.Algorithm</c> route over
    /// a block whose <c>Sub</c> returns a captured call of its member (<c>inline-alg-call</c>, with its static route
    /// <c>.Sub.Run</c> for check R), a captured call of a block's member read by either intrinsic (<c>inline-capture</c>,
    /// <c>inline-capture-invoke</c>), and the result-member callee form whose argument is a block's member
    /// (<c>result-member-argument</c>). Each gives one value per activation and is refused outside the call.</para>
    /// </summary>
    public static IReadOnlyList<CensusCase> DeconstructionFamilies()
        => DeconstructionShapes.Select(shape => new CensusCase($"deconstruction={shape.Name}", [], shape.Body(rowsTwin: false, staticRoute: false),
            [new CensusReader("A", ["F", "A"], "F.A")], "deconstruction-family")).ToArray();

    // ── The loaded alias carrier (2026-11-20) ─────────────────────────────────────────────────────

    public const string CarrierUrl = "https://mods.test/carrier.kat";
    public const string CarrierCopyUrl = "https://mods.test/carrier-copy.kat";

    /// <summary>
    /// The carrier module's text. Its ONE row names an algorithm, so the loaded root elaborates to an alias that keeps
    /// the module mark: a structural forwarding carrier (<c>Algorithm.Alias</c>, never a transparent reference). The row
    /// <c>W</c> and the member <c>V</c> read a name only the module's own <c>open</c> provides; <c>X</c> and <c>Z</c> are
    /// <c>Other</c>'s members, the names an open level reads through a second provider.
    /// </summary>
    public const string CarrierText = "open Lib\nLib = {\n  public W = 3\n}\npublic X = 1\npublic Z = 2\npublic V = W + 0\nW\n";

    /// <summary>
    /// One program of <see cref="CarrierFamilies"/>: the text with the carrier loaded (<c>ordinary: false</c>) or written
    /// (<c>true</c>, the ordinary alias twin), the provider verdict the loaded program must show, the URLs it loads, and
    /// whether the twin must DIFFER because a holder level declares the name the carrier's row and member read (the cut).
    /// </summary>
    private sealed record CarrierShape(string Name, Func<bool, string> Body, string Verdict, bool TwoUrls = false, bool Cut = false);

    // The census's Lib with what an open walk charges: Sub's row reads y.
    private const string CarrierLib = "Lib = {\n  public Sub = {\n    public Q = 1\n    y\n  }\n  0\n}";

    private static string WrittenCarrier(string name) => $"{name} = {{\n{Indent(CarrierText.TrimEnd('\n'), 2)}\n}}";

    private static string LoadedCarrier(string name, string url) => $"{name} = load('{url}')";

    private static string CarrierProgram(string root, params string[] members)
        => $"{root}F(y) = {{\n{Indent(string.Join("\n", [.. members, "A"]), 2)}\n}}\n";

    private static readonly string OneCarrier = $"providers 1; identities 1; fetched {CarrierUrl}; unqualified clean";
    private static readonly string NoCarrierProvider = $"providers 0; identities 1; fetched {CarrierUrl}; unqualified clean";

    private static readonly CarrierShape[] CarrierShapes =
    [
        // THE SAME-URL CONTROL: two root holders of one canonical URL are one provider of X; the twin's second holder is
        // a transparent reference to the written carrier.
        new("open-same-url", ordinary => CarrierProgram(
            ordinary ? $"{WrittenCarrier("ModA")}\nModB = ModA\n" : $"{LoadedCarrier("ModA", CarrierUrl)}\n{LoadedCarrier("ModB", CarrierUrl)}\n",
            "open Lib.Sub, ModA, ModB", CarrierLib, "A = X + 0"), OneCarrier),
        // The same control's other spelling: a holder and a written load of it; the twin opens its one declaration twice.
        new("open-holder-load", ordinary => CarrierProgram(
            ordinary ? $"{WrittenCarrier("ModA")}\n" : $"{LoadedCarrier("ModA", CarrierUrl)}\n",
            ordinary ? "open Lib.Sub, ModA, ModA" : $"open Lib.Sub, ModA, load('{CarrierUrl}')", CarrierLib, "A = X + 0"), OneCarrier),
        // THE DISTINCT-URL CONTROL: two canonical URLs serving the carrier's text are two providers, so the unqualified read
        // is AmbiguousOpen and the fixture qualifies it; the twin writes the carrier twice, two declarations too.
        new("open-two-urls", ordinary => CarrierProgram(
            ordinary ? $"{WrittenCarrier("ModA")}\n{WrittenCarrier("ModB")}\n" : $"{LoadedCarrier("ModA", CarrierUrl)}\n{LoadedCarrier("ModB", CarrierCopyUrl)}\n",
            "open Lib.Sub, ModA, ModB", CarrierLib, $"A = {QualifiedRead}"),
            $"providers 2; identities 2; fetched {CarrierCopyUrl},{CarrierUrl}; unqualified AmbiguousOpen", TwoUrls: true),
        // The carrier's single output, read as a value: the alias forwards to the row's target.
        new("row", ordinary => CarrierProgram(
            ordinary ? $"{WrittenCarrier("ModA")}\n" : $"{LoadedCarrier("ModA", CarrierUrl)}\n", "A = ModA + 0"), NoCarrierProvider),
        // THE CUT: the holder is declared in F beside `W = y`. The loaded carrier is rooted at the prelude, so its row and its
        // member read its own opened W; the written one reads F's.
        new("cut-row", ordinary => CarrierProgram("", "W = y", ordinary ? WrittenCarrier("M") : LoadedCarrier("M", CarrierUrl), "A = M + 0"),
            NoCarrierProvider, Cut: true),
        new("cut-member", ordinary => CarrierProgram("", "W = y", ordinary ? WrittenCarrier("M") : LoadedCarrier("M", CarrierUrl), "A = M.V + 0"),
            NoCarrierProvider, Cut: true),
        new("cut-open", ordinary => CarrierProgram("", "open M", "W = y", ordinary ? WrittenCarrier("M") : LoadedCarrier("M", CarrierUrl), "A = V + 0"),
            OneCarrier, Cut: true),
    ];

    private static CarrierShape Carrier(CensusCase @case)
        => CarrierShapes.FirstOrDefault(shape => $"carrier={shape.Name}" == @case.Id)
            ?? throw new ArgumentException($"Not a carrier case: {@case.Id}", nameof(@case));

    /// <summary>
    /// THE CARRIER FAMILY (2026-11-20): a SOURCE-LOADED MODULE WHOSE SINGLE OUTPUT IS AN ALIAS CARRIER
    /// (<see cref="CarrierText"/>), the one source-reachable module shape the module dimension's text (members only, no
    /// row) does not have. Each case is a census case of its own inside <c>F(y)</c>, parsed by the asynchronous front end
    /// over a server of <see cref="CarrierUrl"/> (and <see cref="CarrierCopyUrl"/> for the distinct-URL control), with an
    /// ORDINARY ALIAS TWIN (<see cref="CarrierTwin"/>): the same program with every loaded holder written at its own place
    /// as an ordinary declaration, the first as the carrier's text in braces (a structural forwarding carrier too), a
    /// second holder of the same URL as a transparent reference to it. Check P requires each case's provider verdict
    /// (<see cref="ExpectedProviderVerdict"/>) and its twin relation (<see cref="CarrierContrast"/>).
    /// <list type="bullet">
    /// <item><c>open-same-url</c>, <c>open-holder-load</c> (the same-URL control in both spellings): one canonical URL is
    /// one provider of <c>X</c> at <c>F</c>'s unused open level, whose walk of <c>Lib.Sub</c> charges the reader; equal to
    /// the twin.</item>
    /// <item><c>open-two-urls</c> (the distinct-URL control): two providers, the unqualified read AmbiguousOpen, the
    /// qualified fixture a lexical read; equal to the twin, which writes the carrier twice.</item>
    /// <item><c>row</c>: the carrier's single output read as a value from a root holder; equal to the twin.</item>
    /// <item><c>cut-row</c>, <c>cut-member</c>, <c>cut-open</c>: the holder stands in <c>F</c> beside <c>W = y</c>. A loaded
    /// module is rooted at the prelude (Q-31 H-P), so the row, the member read by a path and the member read through
    /// <c>open M</c> give the module's own 3 and the reader stays exported; the twin reads <c>F</c>'s <c>W</c>, gives one
    /// value per activation and is charged <c>y</c>. The twin relation is that difference, exactly.</item>
    /// </list>
    /// What each case can witness (measured 2026-11-20 against the two earlier static models, scratch evidence): the model
    /// before the alias-root cut (3fba28fe) refused the source trees of the three cut cases; the model before one module
    /// was one provider (bb1314f2) admitted the two same-URL cases with the reader's requirement removed; both earlier
    /// models agree with today's on <c>open-two-urls</c> and <c>row</c>, whose evidence is the runtime's and the front
    /// end's alone. Not built: a carrier under the extension heads, a written load in a clause branch (a deferred region,
    /// as <see cref="ModuleExclusion"/>), and a module-marked transparent reference, which no source produces.
    /// </summary>
    public static IReadOnlyList<CensusCase> CarrierFamilies()
        => CarrierShapes.Select(shape => new CensusCase($"carrier={shape.Name}", [], shape.Body(false),
            [new CensusReader("A", ["F", "A"], "F.A")], "carrier",
            Modules: shape.TwoUrls ? [new(CarrierUrl, CarrierText), new(CarrierCopyUrl, CarrierText)] : [new(CarrierUrl, CarrierText)])).ToArray();

    /// <summary>The ORDINARY ALIAS TWIN of a carrier case: its program with every loaded holder written (it loads nothing).</summary>
    public static CensusCase CarrierTwin(CensusCase @case)
        => @case.Kind == "carrier" ? @case with { Body = Carrier(@case).Body(true), Kind = "carrier-twin", Modules = null }
            : throw new ArgumentException($"Only a carrier case has an ordinary alias twin: {@case.Id}", nameof(@case));

    /// <summary>
    /// The twin relation of a carrier case, as the differences check P must find between it and its ordinary alias twin
    /// (reader or <c>-</c>, and the detail): none for a case the holder's chain cannot change, and for a cut case the
    /// module's constant against the twin's read of <c>F</c>'s <c>W</c> on every probe, with the reader's metadata.
    /// </summary>
    public static IReadOnlyList<(string Reader, string Detail)> CarrierContrast(CensusCase @case) => Carrier(@case).Cut
        ?
        [
            ("-", "esc:A: module=ok 3; ordinary=err localOnlyProperty:A"),
            ("-", "in5: module=ok 3; ordinary=ok 5"),
            ("-", "in7: module=ok 3; ordinary=ok 7"),
            ("-", "same: module=ok S[3, 3]; ordinary=ok S[5, 7]"),
            ("A", "metadata: module=exported; ordinary=LocalOnlyCapturedAncestorParameters[y@0]"),
        ]
        : [];

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
        var dims = DimensionCount(cases);
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

    // The dimension count every case of one cover shares: the grid's seven, or a module cell's eight.
    private static int DimensionCount(IReadOnlyList<CensusCase> cases)
    {
        if (cases.Count == 0) return DimensionNames.Length;
        var count = cases[0].Dims.Count;
        if (cases.Any(c => c.Dims.Count != count))
            throw new ArgumentException("A cover's cases must share one dimension list.", nameof(cases));
        return count;
    }

    public static int TripleCount(IReadOnlyList<CensusCase> cases) => Triples(cases).Count;

    /// <summary>Every combination of three dimension values that occurs in some case (the keys the cover counts).</summary>
    public static HashSet<string> Triples(IReadOnlyList<CensusCase> cases)
    {
        var keys = new HashSet<string>(StringComparer.Ordinal);
        var dims = DimensionCount(cases);
        foreach (var @case in cases)
            for (var a = 0; a < dims; a++)
                for (var b = a + 1; b < dims; b++)
                    for (var c = b + 1; c < dims; c++)
                        keys.Add($"{a}={@case.Dims[a].Value};{b}={@case.Dims[b].Value};{c}={@case.Dims[c].Value}");
        return keys;
    }

    /// <summary>
    /// The program text of one grid cell (with <paramref name="rowsTwin"/>, its <see cref="DeconstructionTwin"/>; with
    /// <paramref name="staticRoute"/>, its <see cref="StaticRouteTwin"/>; with a <paramref name="module"/> value, the module
    /// cell of that value).
    /// </summary>
    private sealed class ProgramShape(string head, string pos, string open, string reader, string place, string end, string req, bool rowsTwin,
        bool staticRoute = false, string? module = null)
    {
        // The unused level's second provider: `Other`, or the loaded module reached as the module value spells it.
        private string SecondProvider => module switch
        {
            null => "Other",
            "holder-load" => $"ModA, load('{ModuleUrl}')",
            _ => "ModA, ModB",
        };

        // The name an open position's unused level gives the reader (the control's fixture qualifies it).
        private string UnusedRead => module == "two-urls" ? "ModA.X" : "X";

        // The module cell's root holders, written before F.
        private string ModuleHolders => module switch
        {
            null => "",
            "holders" => $"ModA = load('{ModuleUrl}')\nModB = load('{ModuleUrl}')\n",
            "holder-load" => $"ModA = load('{ModuleUrl}')\n",
            "two-urls" => $"ModA = load('{ModuleUrl}')\nModB = load('{ModuleCopyUrl}')\n",
            _ => throw new ArgumentOutOfRangeException(nameof(module), module, null),
        };

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
                return (used ? "Q + 0" : $"{UnusedRead} + 0", target);
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
                : head == "opened" ? $"open {Path}, Lib" : $"open {target}, {SecondProvider}";
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
            var root = ModuleHolders + OpenLine(opens, "root");
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
