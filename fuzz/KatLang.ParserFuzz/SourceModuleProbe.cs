using System.Diagnostics;
using System.Globalization;
using System.Reflection;
using System.Text;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Phase-6 pre-evaluation RESOURCE probe: how source text and module graphs turn into
/// tokens, AST nodes, diagnostics, and downloader work BEFORE the evaluator runs. This is
/// the measurement and deterministic-regression backbone for the source/module input-size
/// policy. Production parsing and module-loading ceilings remain active during the probe.
///
///   source-probe [--out FILE]        deterministic source shapes, in-process counts
///   source-probe-child SHAPE N       one source built+parsed+elaborated, self-reports RSS
///   module-probe [--out FILE]        module-graph scenarios via an in-memory fake downloader
///   module-depth-search [--max N]    isolated deep-chain no-crash/resource-error validation
///   module-depth-child N             one isolated import chain under production ceilings
///
/// Counts (source length in UTF-16 code units, tokens, nodes, diagnostics, downloader calls,
/// aggregate source) are deterministic and architecture-independent. Elapsed time, GC
/// allocation, and peak working set are recorded for CALIBRATION ONLY and are never proposed
/// as public limit units. No network access: the module probe uses a generative in-memory
/// downloader keyed by URL.
/// </summary>
internal static class SourceModuleProbe
{
    // Generation is bounded so a probe can never ask for an unbounded string.
    private const int MaxGenCodeUnits = 64 * 1024 * 1024;

    // ── source shapes ─────────────────────────────────────────────────────────

    private sealed record SourceShape(string Id, string Kind, Func<int, string> Gen, int[] Sizes);

    private static string Repeat(string unit, int n)
    {
        long len = (long)unit.Length * n;
        if (len > MaxGenCodeUnits) throw new InvalidOperationException($"generator bound exceeded ({len})");
        var sb = new StringBuilder(checked((int)len));
        for (var i = 0; i < n; i++) sb.Append(unit);
        return sb.ToString();
    }

    private static readonly int[] Small = [10, 100, 1_000, 10_000];
    private static readonly int[] Mid = [10, 100, 1_000, 10_000, 100_000];
    private static readonly int[] Big = [1_000, 10_000, 100_000, 1_000_000];

    private static readonly SourceShape[] SourceShapes =
    [
        // ── long flat source ──────────────────────────────────────────────────
        // One very long identifier (per-token length vs total source).
        new("long_ident", "flat", n => { var id = "A" + Repeat("a", n); return $"{id} = 1\n{id}"; }, Big),
        // One very long string literal.
        new("long_string", "flat", n => $"'{Repeat("x", n)}'", Big),
        // One very long comment.
        new("long_comment", "flat", n => $"# {Repeat("x", n)}\n1", Big),
        // Repeated whitespace.
        new("ws_repeat", "flat", n => $"1{Repeat(" ", n)}", Big),
        // One very long numeric literal.
        new("long_number", "flat", n => $"{Repeat("9", n)}", Mid),

        // ── many tiny expressions ─────────────────────────────────────────────
        new("many_num_oneline", "wide", n => Repeat("1 ", n), Mid),
        new("many_num_lines", "many", n => Repeat("1\n", n) + "1", Mid),
        new("many_props", "many", n => Concat(n, i => $"A{i} = {i}\n") + "A0", Mid),
        new("many_funcs", "many", n => Concat(n, i => $"F{i}(x) = x + {i}\n") + "F0(1)", Mid),
        new("many_lists", "many", n => Repeat("[1] ", n), Mid),
        new("many_empty", "many", n => Concat(n, i => $"A{i} = ()\n") + "A0", Mid),

        // ── deep but legal syntax (near parser MaxNestingDepth) ────────────────
        // Confirms the existing depth guard constrains recursive shape but not node count.
        new("deep_nesting", "deep", n => $"{Repeat("(", n)}1{Repeat(")", n)}", [50, 100, 200, 280]),

        // ── wide syntax ───────────────────────────────────────────────────────
        new("wide_args", "wide", n => $"F({Concat(n, i => i == 0 ? "x0" : $", x{i}")}) = x0\nF({Concat(n, i => i == 0 ? "1" : ", 1")})", [10, 100, 1_000, 10_000]),
        new("wide_list", "wide", n => "[" + Repeat("1,", n) + "1]", Mid),
        new("wide_seq", "wide", n => "sum((" + Repeat("1,", n) + "1))", Mid),
        new("wide_deconstruct", "wide", n => $"{Concat(n, i => i == 0 ? "x0" : $", x{i}")} = range(1, {n})\nx0", [10, 100, 1_000, 10_000]),

        // ── frontend amplification: conditional clause family ──────────────────
        // The historical exponential-blowup shape. postNodes/rawNodes must stay linear.
        new("many_clauses", "frontend", n => Concat(n, i => $"F({i}) = {i}\n") + "F(0)", [10, 100, 1_000, 5_000]),
        new("many_callbacks", "frontend", n => Concat(n, i => $"G{i}(x) = x + {i}\n") + "Values = range(1, 10)\n" + Concat(n, i => i == 0 ? "Values.map(G0)" : $", Values.map(G{i})") , [10, 100, 1_000]),

        // ── diagnostic-heavy malformed input ──────────────────────────────────
        new("diag_per_token", "diag", n => Repeat("@ ", n), Mid),
        new("diag_bad_strings", "diag", n => Repeat("'\n", n), Mid),
        new("diag_bad_idents", "diag", n => Repeat(((char)0x0300) + " ", n), Mid),  // lone combining mark U+0300
        new("diag_eof_brackets", "diag", n => Repeat("[", n), [50, 100, 200, 280]),
        new("diag_semicolons", "diag", n => Repeat("1;", n), Mid),
    ];

    private static string Concat(int n, Func<int, string> f)
    {
        if (n < 0) throw new ArgumentOutOfRangeException(nameof(n));

        var sb = new StringBuilder();
        for (var i = 0; i < n; i++)
        {
            var part = f(i);
            if (part.Length > MaxGenCodeUnits - sb.Length)
            {
                throw new InvalidOperationException(
                    $"generator bound exceeded ({(long)sb.Length + part.Length})");
            }

            sb.Append(part);
        }

        return sb.ToString();
    }

    private static SourceShape? FindSource(string id) => SourceShapes.FirstOrDefault(s => s.Id == id);

    // ── in-process source measurement ─────────────────────────────────────────

    private sealed record SourceRow(string Id, string Kind, int Size, int SrcLen, int Tokens, int RawNodes,
        int PostNodes, int ParseDiags, int FeDiags, double TokPerSrc, double NodePerSrc, double PostPerRaw,
        double DiagPerSrc, long AllocKb, double Ms, string Note);

    public static int RunSource(string[] args)
    {
        string outPath = "";
        var selected = new List<string>();
        for (var i = 1; i < args.Length; i++)
            switch (args[i])
            {
                case "--out": outPath = args[++i]; break;
                case "--shapes": selected = args[++i].Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries).ToList(); break;
            }

        var shapes = selected.Count > 0 ? SourceShapes.Where(s => selected.Contains(s.Id)).ToArray() : SourceShapes;

        // Warm the pipeline so the first measured row is not paying JIT.
        for (var i = 0; i < 3; i++) MeasureSource("A = 1\nA", out _);

        Console.WriteLine($"# source resource probe  build={BuildConfig()}  shapes={shapes.Length}");
        Console.WriteLine($"{"shape",-18}{"kind",-9}{"size",8}{"srcLen",10}{"tokens",9}{"rawNode",9}{"postNode",9}{"pDiag",7}{"feDiag",7}  {"tok/src",8}{"node/src",9}{"post/raw",9}{"diag/src",9}{"allocKb",10}{"ms",8}");
        var rows = new List<SourceRow>();
        foreach (var shape in shapes)
        {
            foreach (var size in shape.Sizes)
            {
                var row = MeasureShape(shape, size);
                rows.Add(row);
                Console.WriteLine(
                    $"{shape.Id,-18}{shape.Kind,-9}{size,8}{row.SrcLen,10}{row.Tokens,9}{row.RawNodes,9}{row.PostNodes,9}{row.ParseDiags,7}{row.FeDiags,7}  " +
                    $"{row.TokPerSrc,8:F3}{row.NodePerSrc,9:F3}{row.PostPerRaw,9:F3}{row.DiagPerSrc,9:F4}{row.AllocKb,10}{row.Ms,8:F1} {row.Note}");
            }
        }

        if (outPath.Length > 0) WriteJson(outPath, rows);
        return 0;
    }

    private static SourceRow MeasureShape(SourceShape shape, int size)
    {
        string source;
        try { source = shape.Gen(size); }
        catch (Exception ex) { return new SourceRow(shape.Id, shape.Kind, size, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, $"gen-fail:{ex.Message}"); }

        var before = GC.GetTotalAllocatedBytes();
        var sw = Stopwatch.StartNew();
        var m = MeasureSource(source, out var note);
        sw.Stop();
        var allocKb = (GC.GetTotalAllocatedBytes() - before) / 1024;

        double srcLen = source.Length == 0 ? 1 : source.Length;
        return new SourceRow(shape.Id, shape.Kind, size, source.Length, m.Tokens, m.RawNodes, m.PostNodes,
            m.ParseDiags, m.FeDiags,
            m.Tokens / srcLen, m.RawNodes / srcLen,
            m.RawNodes == 0 ? 0 : (double)m.PostNodes / m.RawNodes,
            m.ParseDiags / srcLen, allocKb, sw.Elapsed.TotalMilliseconds, note);
    }

    private sealed record SourceMeasure(int Tokens, int RawNodes, int PostNodes, int ParseDiags, int FeDiags);

    private static SourceMeasure MeasureSource(string source, out string note)
    {
        note = "";
        var (tokens, _) = Lexer.Tokenize(source);
        var syntax = Parser.ParseSyntax(source);
        var rawNodes = FrontEndStageProbe.CountNodes(syntax.Root);
        var parseDiags = syntax.Diagnostics.Count;

        // Default public front-end (no downloader): the same path KatLangEngine.Run takes.
        var pipeline = FrontEndPipeline.Process(source);
        var postNodes = FrontEndStageProbe.CountNodes(pipeline.ToParseResult().Root);
        var feDiags = pipeline.Diagnostics.Count;
        return new SourceMeasure(tokens.Count, rawNodes, postNodes, parseDiags, feDiags);
    }

    // ── isolated child: RSS calibration for one big source ─────────────────────

    public static int RunSourceChild(string[] args)
    {
        if (args.Length < 3) { Console.Error.WriteLine("source-probe-child SHAPE N"); return 2; }
        var shape = FindSource(args[1]);
        if (shape is null) { Console.Error.WriteLine($"unknown shape: {args[1]}"); return 2; }
        if (!int.TryParse(args[2], out var n)) { Console.Error.WriteLine("bad N"); return 2; }

        string source;
        try { source = shape.Gen(n); }
        catch (Exception ex) { Console.Error.WriteLine($"gen-fail: {ex.Message}"); return 2; }

        Console.Out.WriteLine($"CHILD shape={shape.Id} n={n} srcLen={source.Length}");
        try
        {
            var syntax = Parser.ParseSyntax(source);
            var nodes = FrontEndStageProbe.CountNodes(syntax.Root);
            var pipeline = FrontEndPipeline.Process(source);
            var postNodes = FrontEndStageProbe.CountNodes(pipeline.ToParseResult().Root);
            Console.Out.WriteLine($"NODES raw={nodes} post={postNodes} pDiag={syntax.Diagnostics.Count} feDiag={pipeline.Diagnostics.Count}");
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine($"UNEXPECTED {ex.GetType().FullName}: {ex.Message}");
            return 21;
        }

        Console.Out.WriteLine(
            $"RESOURCE peakWorkingSetKb={Process.GetCurrentProcess().PeakWorkingSet64 / 1024} " +
            $"allocatedKb={GC.GetTotalAllocatedBytes() / 1024}");
        return 0;
    }

    // ── module-graph probe (in-memory generative downloader) ───────────────────

    private const string Host = "https://katlang.org/gen/";

    /// <summary>
    /// Generative fake downloader. Counts every call. URL grammar:
    ///   chain/K       -> loads chain/(K-1); chain/0 is a leaf
    ///   leaf/K        -> a tiny leaf module (public V{K} = K)
    ///   fill/K/S      -> a leaf padded to S code units of comment
    ///   diamond/{a,b,c,d} -> fixed 4-node diamond
    /// Anything else throws (a 404), exercising the failed-download path.
    /// </summary>
    private sealed class FakeDownloader
    {
        public int Calls;
        public long DownloadedChars;
        private readonly int _pad;
        public FakeDownloader(int pad = 0) { _pad = pad; }

        public string Get(string url)
        {
            Calls++;
            var body = Body(url);
            DownloadedChars += body.Length;
            return body;
        }

        private string Body(string url)
        {
            if (!url.StartsWith(Host, StringComparison.Ordinal)) throw new Exception($"404 {url}");
            var path = url[Host.Length..];
            var parts = path.Split('/');
            switch (parts[0])
            {
                case "chain":
                    var k = int.Parse(parts[1], CultureInfo.InvariantCulture);
                    return k <= 0
                        ? $"public V = {0}"
                        : $"public Inner = load('{Host}chain/{k - 1}')\npublic V = {k}";
                case "leaf":
                    return $"public V{parts[1]} = {parts[1]}";
                case "fill":
                    var size = int.Parse(parts[2], CultureInfo.InvariantCulture);
                    return $"# {new string('x', Math.Max(0, size))}\npublic V{parts[1]} = {parts[1]}";
                case "pad" when _pad > 0:
                    return $"# {new string('x', _pad)}\npublic V{parts[1]} = {parts[1]}";
                default:
                    throw new Exception($"404 {url}");
            }
        }
    }

    private sealed record ModuleRow(string Scenario, int Param, int DownloaderCalls, long DownloadedChars,
        int MainSrcLen, int ResultNodes, int ErrorDiags, string Outcome, double Ms, string Note);

    public static int RunModule(string[] args)
    {
        string outPath = "";
        for (var i = 1; i < args.Length; i++)
            if (args[i] == "--out") outPath = args[++i];

        Console.WriteLine($"# module-graph resource probe  build={BuildConfig()}");
        Console.WriteLine($"{"scenario",-20}{"param",7}{"dlCalls",9}{"dlChars",12}{"mainLen",9}{"nodes",9}{"errDiag",9}  {"outcome",-24}{"ms",8}  note");

        var rows = new List<ModuleRow>();
        void Row(ModuleRow r)
        {
            rows.Add(r);
            Console.WriteLine($"{r.Scenario,-20}{r.Param,7}{r.DownloaderCalls,9}{r.DownloadedChars,12}{r.MainSrcLen,9}{r.ResultNodes,9}{r.ErrorDiags,9}  {r.Outcome,-24}{r.Ms,8:F1}  {r.Note}");
        }

        // chain: main -> chain/N -> ... -> chain/0 (all distinct). Distinct modules = N+1.
        foreach (var n in new[] { 1, 5, 50, 200, 500 })
            Row(RunModuleScenario($"chain", n, $"open Lib\npublic Lib = load('{Host}chain/{n}')\nLib.V"));

        // wide: main opens N distinct tiny leaf modules. Distinct modules = N.
        foreach (var n in new[] { 1, 10, 100, 1_000 })
            Row(RunModuleScenario("wide", n,
                Concat(n, i => $"public L{i} = load('{Host}leaf/{i}')\n") + "L0.V0"));

        // diamond: A->B,C ; B->D ; C->D. D must be fetched ONCE (cache).
        Row(RunModuleScenario("diamond", 4, $"public A = load('{Host}dia/a')\nA.B.V", DiamondFiles()));

        // repeat: main loads the SAME url from N sites. downloaderCalls must be 1.
        foreach (var n in new[] { 2, 10, 100, 1_000 })
            Row(RunModuleScenario("repeat", n,
                Concat(n, i => $"public R{i} = load('{Host}leaf/7')\n") + "R0.V7"));

        // many_tiny: N distinct tiny modules — each tiny, aggregate grows with N.
        foreach (var n in new[] { 100, 1_000, 5_000 })
            Row(RunModuleScenario("many_tiny", n,
                Concat(n, i => $"public L{i} = load('{Host}leaf/{i}')\n") + "L0.V0"));

        // aggregate: N modules each padded to ~1 MiB (each < 2 MiB per-module cap), sum = N MiB.
        foreach (var n in new[] { 1, 4, 16, 64 })
            Row(RunModuleScenarioPadded("aggregate", n, 1024 * 1024,
                Concat(n, i => $"public L{i} = load('{Host}pad/{i}')\n") + "L0.V0"));

        // one_large: one module near/over the 2 MiB per-module cap.
        Row(RunModuleScenario("one_large_ok", 1, $"public L = load('{Host}fill/0/2000000')\nL.V0"));
        Row(RunModuleScenario("one_large_over", 1, $"public L = load('{Host}fill/0/3000000')\nL.V0"));

        // cycle: self, 2-cycle, longer.
        Row(RunModuleScenario("cycle_self", 1, $"public A = load('{Host}cyc/self')\nA.V", CycleSelfFiles()));
        Row(RunModuleScenario("cycle_two", 2, $"public A = load('{Host}cyc/a')\nA.V", CycleTwoFiles()));

        // failed: N sites to DISTINCT missing URLs (each 404). downloaderCalls and diags?
        foreach (var n in new[] { 1, 10, 100, 1_000 })
            Row(RunModuleScenario("failed_distinct", n,
                Concat(n, i => $"public F{i} = load('{Host}missing/{i}')\n") + "F0.V"));

        // failed_repeat: N sites to the SAME missing URL. Cached failure or re-fetch?
        foreach (var n in new[] { 1, 10, 100 })
            Row(RunModuleScenario("failed_repeat", n,
                Concat(n, i => $"public F{i} = load('{Host}missing/same')\n") + "F0.V"));

        if (outPath.Length > 0) WriteJson(outPath, rows);
        return 0;
    }

    private static ModuleRow RunModuleScenario(string scenario, int param, string mainSource,
        Dictionary<string, string>? files = null)
        => RunModuleImpl(scenario, param, mainSource, files, 0);

    private static ModuleRow RunModuleScenarioPadded(string scenario, int param, int pad, string mainSource)
        => RunModuleImpl(scenario, param, mainSource, null, pad);

    private static ModuleRow RunModuleImpl(string scenario, int param, string mainSource,
        Dictionary<string, string>? files, int pad)
    {
        var dl = new FakeDownloader(pad);
        Func<string, string> fetch = files is null
            ? dl.Get
            : url => { dl.Calls++; var body = Lookup(files, url); dl.DownloadedChars += body?.Length ?? 0; return body ?? throw new Exception($"404 {url}"); };
        // Source loading is async-only; the in-memory fetch completes synchronously,
        // so ParseAsync completes synchronously and GetResult extracts the result.
        Func<string, CancellationToken, ValueTask<string>> downloader =
            (url, _) => ValueTask.FromResult(fetch(url));

        var sw = Stopwatch.StartNew();
        ParseResult result;
        string outcome, note = "";
        try
        {
            result = Parser.ParseAsync(mainSource, new RunOptions { DownloadCode = downloader })
                .GetAwaiter().GetResult();
            var errs = result.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
            var nodes = FrontEndStageProbe.CountNodes(result.Root);
            outcome = errs.Count == 0 ? "ok" : $"errors={errs.Count}";
            if (errs.Count > 0) note = Trunc(errs[0].Message, 60);
            sw.Stop();
            return new ModuleRow(scenario, param, dl.Calls, dl.DownloadedChars, mainSource.Length, nodes, errs.Count, outcome, sw.Elapsed.TotalMilliseconds, note);
        }
        catch (Exception ex)
        {
            sw.Stop();
            return new ModuleRow(scenario, param, dl.Calls, dl.DownloadedChars, mainSource.Length, -1, -1, $"EXC:{ex.GetType().Name}", sw.Elapsed.TotalMilliseconds, Trunc(ex.Message, 60));
        }
    }

    private static string? Lookup(Dictionary<string, string> files, string url)
    {
        if (files.TryGetValue(url, out var c)) return c;
        return files.TryGetValue(url.TrimEnd('/'), out c) ? c : null;
    }

    private static Dictionary<string, string> DiamondFiles() => new()
    {
        [$"{Host}dia/a"] = $"public B = load('{Host}dia/b')\npublic C = load('{Host}dia/c')",
        [$"{Host}dia/b"] = $"public D = load('{Host}dia/d')",
        [$"{Host}dia/c"] = $"public D = load('{Host}dia/d')",
        [$"{Host}dia/d"] = "public V = 1",
    };

    private static Dictionary<string, string> CycleSelfFiles() => new()
    {
        [$"{Host}cyc/self"] = $"public Me = load('{Host}cyc/self')\npublic V = 1",
    };

    private static Dictionary<string, string> CycleTwoFiles() => new()
    {
        [$"{Host}cyc/a"] = $"public B = load('{Host}cyc/b')\npublic V = 1",
        [$"{Host}cyc/b"] = $"public A = load('{Host}cyc/a')\npublic V = 2",
    };

    // ── import-chain stack-depth boundary search (isolated child) ──────────────

    public static int RunModuleDepthChild(string[] args)
    {
        if (args.Length < 2 || !int.TryParse(args[1], out var n)) { Console.Error.WriteLine("module-depth-child N"); return 2; }
        var dl = new FakeDownloader();
        var main = $"public Lib = load('{Host}chain/{n}')\nLib.V";
        Console.Out.WriteLine($"CHILD depth n={n}");
        try
        {
            Func<string, CancellationToken, ValueTask<string>> downloader =
                (url, _) => ValueTask.FromResult(dl.Get(url));
            var result = Parser.ParseAsync(main, new RunOptions { DownloadCode = downloader })
                .GetAwaiter().GetResult();
            var errs = result.Diagnostics.Count(d => d.Severity == DiagnosticSeverity.Error);
            Console.Out.WriteLine($"RESOURCE peakWorkingSetKb={Process.GetCurrentProcess().PeakWorkingSet64 / 1024} calls={dl.Calls}");
            Console.Out.WriteLine($"OK depth={n} errors={errs}");
            return 0;
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine($"UNEXPECTED {ex.GetType().FullName}: {ex.Message}");
            return 21;
        }
    }

    public static int RunModuleDepthSearch(string[] args)
    {
        int max = 1_000_000, timeoutMs = 15000;
        for (var i = 1; i < args.Length; i++)
            switch (args[i]) { case "--max": max = int.Parse(args[++i]); break; case "--timeout-ms": timeoutMs = int.Parse(args[++i]); break; }

        Console.WriteLine($"# import-chain depth search  build={BuildConfig()}  max={max}  timeout={timeoutMs}ms");
        int lo = 0, hi = -1;
        (int n, string cls, int exit, long peakKb)? loRun = null, hiRun = null;
        int probe = 1;
        while (true)
        {
            var r = LaunchDepth(probe, timeoutMs);
            Console.WriteLine($"  depth={probe,-8} {r.cls} exit={r.exit} peakKb={r.peakKb}");
            if (r.cls == "completed") { lo = probe; loRun = r; }
            else { hi = probe; hiRun = r; break; }
            if (probe >= max) break;
            probe = (int)Math.Min((long)probe * 4, max);
        }
        if (hi != -1)
        {
            while (hi - lo > 1)
            {
                int mid = lo + (hi - lo) / 2;
                var r = LaunchDepth(mid, timeoutMs);
                Console.WriteLine($"  depth={mid,-8} {r.cls} exit={r.exit} peakKb={r.peakKb}");
                if (r.cls == "completed") { lo = mid; loRun = r; } else { hi = mid; hiRun = r; }
            }
        }
        Console.WriteLine(hi == -1
            ? $"# completed through max depth={lo} (no stack boundary below {max})"
            : $"# largest completed import depth={lo}; first failure depth={hi} [{hiRun!.Value.cls} exit={hiRun.Value.exit}]");
        return 0;
    }

    private static (int n, string cls, int exit, long peakKb) LaunchDepth(int n, int timeoutMs)
    {
        var (so, se, exit, timedOut, peakKb) = LaunchChild(["module-depth-child", n.ToString()], timeoutMs);
        bool soe = se.Contains("Stack overflow", StringComparison.OrdinalIgnoreCase) || exit is -1073741571 or 134 or 139;
        string cls = timedOut ? "timeout" : exit == 0 ? "completed" : soe ? "stack-overflow" : exit == 21 ? "unexpected-exception" : exit is null ? "killed" : $"crash(exit={exit})";
        return (n, cls, exit ?? -999, peakKb);
    }

    // ── shared child-process launcher (mirrors EvaluatorProbe) ─────────────────

    private static (string so, string se, int? exit, bool timedOut, long peakKb) LaunchChild(string[] childArgs, int timeoutMs)
    {
        string host = Environment.ProcessPath!;
        string? dll = Assembly.GetEntryAssembly()?.Location;
        string? self = Assembly.GetEntryAssembly()?.GetName().Name;
        bool selfContained = self is not null && string.Equals(Path.GetFileNameWithoutExtension(host), self, StringComparison.OrdinalIgnoreCase);

        var psi = new ProcessStartInfo(host) { RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false, CreateNoWindow = true };
        if (!selfContained && !string.IsNullOrEmpty(dll)) psi.ArgumentList.Add(dll);
        foreach (var a in childArgs) psi.ArgumentList.Add(a);

        using var proc = new Process { StartInfo = psi };
        proc.Start();
        var o = proc.StandardOutput.ReadToEndAsync();
        var e = proc.StandardError.ReadToEndAsync();
        bool timedOut = false;
        if (!proc.WaitForExit(timeoutMs)) { timedOut = true; try { proc.Kill(true); } catch { } proc.WaitForExit(2000); }
        string so = Safe(o), se = Safe(e);
        int? exit = null; long peak = 0;
        try { exit = proc.ExitCode; } catch { }
        try { peak = proc.PeakWorkingSet64 / 1024; } catch { }
        return (so, se, exit, timedOut, peak);
    }

    private static string Safe(Task<string> t) { try { return t.GetAwaiter().GetResult() ?? ""; } catch { return ""; } }
    private static string Trunc(string s, int n) => string.IsNullOrEmpty(s) ? s : (s.Length <= n ? s : s[..n]);
    private static string BuildConfig() =>
#if DEBUG
        "debug";
#else
        "release";
#endif

    private static void WriteJson<T>(string outPath, List<T> rows)
    {
        try
        {
            var dir = Path.GetDirectoryName(outPath);
            if (!string.IsNullOrEmpty(dir)) Directory.CreateDirectory(dir);
            File.WriteAllText(outPath, System.Text.Json.JsonSerializer.Serialize(rows, new System.Text.Json.JsonSerializerOptions { WriteIndented = true }), new UTF8Encoding(false));
            Console.WriteLine($"# wrote {rows.Count} rows -> {outPath}");
        }
        catch (Exception ex) { Console.Error.WriteLine($"warning: json write failed: {ex.Message}"); }
    }
}
