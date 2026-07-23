using System.Diagnostics;
using System.Reflection;
using System.Text;
using System.Text.Json;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Process-isolated evaluator RESOURCE probes (Phase-4 Part 2). Recursive, looping, and
/// allocation-heavy programs can exhaust the stack, run forever, or allocate without a
/// practical bound, so the dangerous evaluation always runs in a CHILD process and the
/// parent records the outcome. Intentional non-termination is a characterization result,
/// not automatically a defect.
///
///   eval-probe-child FAMILY N   evaluate exactly one generated program via KatLangEngine
///   eval-probe [options]        parent: exponential + binary search per family
/// </summary>
internal static class EvaluatorProbe
{
    private const int ExitCompleted = 0;    // Success / NoProgramOutput
    private const int ExitStructured = 20;  // ParseFailure / EvalFailure — an expected outcome
    private const int ExitUnexpected = 21;  // unexpected managed exception — MATERIAL
    private const int ExitBadArgs = 2;

    private sealed record Family(string Id, string Kind, Func<int, string> Gen, int MaxParam, bool ExpectedUnbounded);

    private static readonly Family[] Families =
    [
        // ── recursion ────────────────────────────────────────────────────────
        new("rec_infinite",   "recursion", _ => "f(x) = f(x)\nOutput = f(1)", 1, true),
        new("rec_mutual",     "recursion", _ => "f(x) = g(x)\ng(x) = f(x)\nOutput = f(1)", 1, true),
        new("rec_property",   "recursion", _ => "A = A\nOutput = A", 1, true),
        new("rec_prop_mutual","recursion", _ => "A = B\nB = A\nOutput = A", 1, true),
        // Parameter ceilings are deliberately modest: the goal is a clear growth/failure
        // curve, not to consume the machine's memory (see the task's resource guidance).
        new("rec_finite",     "recursion", n => $"f(0) = 0\nf(n) = f(n - 1)\nOutput = f({n})", 1_000_000, false),
        new("rec_callback",   "recursion", n => $"F(x) = [x].map(F)\nOutput = F({n})", 1, true),
        // Depth-ceiling calibration shapes (Phase-5). Each recurses once per level but
        // through a different dispatch path, so the largest completed n measures the
        // per-level host-stack cost of that path.
        new("rec_if_finite",  "recursion", n => $"f(n) = if(n > 0, f(n - 1), 0)\nOutput = f({n})", 1_000_000, false),
        new("rec_nested_finite", "recursion", n => $"f(0) = 0\nf(n) = {new string('(', 10)}f(n - 1){new string(')', 10)}\nOutput = f({n})", 1_000_000, false),
        new("rec_cb_finite",  "recursion", n => $"F(0) = 0\nF(n) = [n - 1].map(F).first\nOutput = F({n})", 1_000_000, false),
        new("rec_dot_finite", "recursion", n => $"f(0) = 0\nf(n) = (n - 1).f\nOutput = f({n})", 1_000_000, false),
        // ── loops ────────────────────────────────────────────────────────────
        new("while_infinite", "loop", _ => "Step = x, 1\nOutput = Step.while(0)", 1, true),
        new("while_finite",   "loop", n => $"Step = x - 1, x > 1\nOutput = Step.while({n})", 10_000_000, false),
        new("repeat_count",   "loop", n => $"Inc = x + 1\nOutput = Inc.repeat({n}, 0)", 10_000_000, false),
        new("while_multislot","loop", n => $"Step = a + 1, b + a, a < {n}\nOutput = Step.while(0, 0)", 10_000_000, false),
        new("loop_callback",  "loop", n => $"G(y) = y + 1\nInc = G(x)\nOutput = Inc.repeat({n}, 0)", 1_000_000, false),
        // ── allocation growth ────────────────────────────────────────────────
        new("range_alloc",    "allocation", n => $"Output = range(1, {n}).count", 5_000_000, false),
        new("map_pipeline",   "allocation", n => $"F(x) = x + 1\nOutput = range(1, {n}).map(F).count", 2_000_000, false),
        new("distinct_large", "allocation", n => $"Output = range(1, {n}).distinct.count", 2_000_000, false),
        new("order_large",    "allocation", n => $"Output = range(1, {n}).orderDesc.count", 2_000_000, false),
        new("nested_list",    "allocation", n => $"F(x) = [x, x]\nOutput = range(1, {n}).map(F).count", 1_000_000, false),
        // ── rendering / string growth ────────────────────────────────────────
        // Display flattens a value recursively, so these render far larger than they
        // evaluate. `display_nested` is the compact-source reproducer: every extra line
        // adds two item slots and DOUBLES the rendered length.
        new("display_nested",  "render", n => "A = range(1, 1000)\n"
            + string.Concat(Enumerable.Range(0, n).Select(i => $"L{i} = [{(i == 0 ? "A" : $"L{i - 1}")}, {(i == 0 ? "A" : $"L{i - 1}")}]\n"))
            + $"Output = L{Math.Max(0, n - 1)}", 40, false),
        // The sharpest reproducer: string elements contribute NO host atoms and each level
        // adds only two item slots, so no evaluation limit sees it grow — only rendering
        // does, doubling per line.
        new("display_str_nested", "render", n => "ToText(x) = x.string\nValues = range(1, 40000).map(ToText)\n"
            + string.Concat(Enumerable.Range(0, n).Select(i => $"L{i} = [{(i == 0 ? "Values" : $"L{i - 1}")}, {(i == 0 ? "Values" : $"L{i - 1}")}]\n"))
            + $"Output = L{Math.Max(0, n - 1)}", 40, false),
        new("display_list",    "render", n => $"Output = range(1, {n})", 1_000_000, false),
        new("display_rows",    "render", n => $"Output = range(1, {n})...", 1_000_000, false),
        new("display_string",  "render", n => $"Values = range(1, {n})\nOutput = Values.map(ToText)\nToText(x) = x.string", 1_000_000, false),
        // ── arithmetic stress ────────────────────────────────────────────────
        new("pow_chain",      "arithmetic", n => $"Output = 2 ^ {n}", 100_000, false),
        new("sum_large",      "arithmetic", n => $"Output = range(1, {n}).sum", 5_000_000, false),
        // ── wide deconstruction: DEMAND every target ─────────────────────────
        // One N-target deconstruction whose N targets are all forced through one
        // compact sum. Historically each demanded target re-bound the shared
        // N-capture pattern (O(N^2)); the shared run-scoped bind makes it linear.
        new("eval_all_deconstruct", "deconstruct",
            n => $"{string.Join(", ", Enumerable.Range(0, n).Select(i => $"x{i}"))} = range(1, {n})\n"
                + $"Output = sum(({string.Join(", ", Enumerable.Range(0, n).Select(i => $"x{i}"))}))",
            30_000, false),
        // ── conditional clause family: CALL it (runtime duplicate-branch scan) ─
        // A family of N literal clauses, invoked once. The runtime path scans the
        // branch list for match-equivalent duplicates before dispatch; the indexed
        // lookup makes that scan linear.
        new("eval_clause_family", "frontend",
            n => string.Concat(Enumerable.Range(0, n).Select(i => $"F({i}) = {i}\n")) + "Output = F(0)", 30_000, false),
    ];

    private static Family? Find(string id) => Families.FirstOrDefault(f => f.Id == id);

    // ── child ────────────────────────────────────────────────────────────────
    public static int RunChild(string[] args)
    {
        if (args.Length < 3) { Console.Error.WriteLine("eval-probe-child FAMILY N"); return ExitBadArgs; }
        var family = Find(args[1]);
        if (family is null) { Console.Error.WriteLine($"unknown family: {args[1]}"); return ExitBadArgs; }
        if (!int.TryParse(args[2], out int n)) { Console.Error.WriteLine("bad N"); return ExitBadArgs; }

        var source = family.Gen(n);
        Console.Out.WriteLine($"CHILD family={family.Id} n={n} len={source.Length}");

        // Default options by design: the probes characterize what a caller gets with no
        // configuration, which is exactly where the process-termination defect lived.
        // KATLANG_PROBE_MAX_STEPS opts one probe run into a step budget so the
        // work-budget side can be characterized on the same harness.
        var options = Environment.GetEnvironmentVariable("KATLANG_PROBE_MAX_STEPS") is { Length: > 0 } rawSteps
            && long.TryParse(rawSteps, out var maxSteps)
                ? new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = maxSteps } }
                : null;

        RunResult result;
        try
        {
            result = KatLangEngine.Run(source, options);   // real public engine; no downloader, no network
        }
        catch (Exception ex)
        {
            // A structured EvalError is the expected failure channel; a managed exception
            // escaping the engine is a material finding.
            Console.Error.WriteLine($"UNEXPECTED {ex.GetType().FullName}: {ex.Message}");
            Console.Error.WriteLine(ex.StackTrace);
            return ExitUnexpected;
        }

        // Rendering is part of what a public caller does, and it is the path that can
        // allocate far beyond the evaluated value, so the probe always renders.
        int displayLength;
        try
        {
            displayLength = result.ToDisplayString().Length;
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine($"UNEXPECTED during display {ex.GetType().FullName}: {ex.Message}");
            return ExitUnexpected;
        }

        // Self-reported resource use: the parent cannot read PeakWorkingSet64 after the
        // child exits, so the child prints its own peak before returning.
        Console.Out.WriteLine($"DISPLAY chars={displayLength}");
        Console.Out.WriteLine(
            $"RESOURCE peakWorkingSetKb={Process.GetCurrentProcess().PeakWorkingSet64 / 1024} " +
            $"allocatedKb={GC.GetTotalAllocatedBytes() / 1024}");

        switch (result)
        {
            case RunResult.Success s:
                Console.Out.WriteLine($"OK success atoms={s.Atoms.Count}");
                return ExitCompleted;
            case RunResult.NoProgramOutput:
                Console.Out.WriteLine("OK no-output");
                return ExitCompleted;
            case RunResult.ParseFailure p:
                Console.Out.WriteLine($"STRUCTURED parse errors={p.Errors.Count}");
                return ExitStructured;
            case RunResult.EvalFailure e:
                Console.Out.WriteLine($"STRUCTURED eval errors={e.Errors.Count} first={e.Errors.FirstOrDefault()?.Message}");
                return ExitStructured;
            default:
                Console.Out.WriteLine("STRUCTURED unknown");
                return ExitStructured;
        }
    }

    // ── parent ───────────────────────────────────────────────────────────────
    private sealed record Run(bool Completed, int? Exit, bool TimedOut, int Len, long Ms, long PeakKb, string Class, string Err);

    private sealed record Row(string Family, string Kind, string Platform, int LargestOk, int LargestOkLen, long LargestOkMs,
        long LargestOkPeakKb, int? FirstFail, int? FirstFailLen, long? FirstFailMs, string Classification,
        int? FailExit, string? FailErr, bool ReachedBound, bool ExpectedUnbounded);

    public static int RunParent(string[] args)
    {
        int timeoutMs = 3000, startN = 1;
        string outPath = "", platform = OperatingSystem.IsWindows() ? "windows" : "linux";
        var selected = new List<string>();
        for (int i = 1; i < args.Length; i++)
            switch (args[i])
            {
                case "--families": selected = args[++i].Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries).ToList(); break;
                case "--timeout-ms": timeoutMs = int.Parse(args[++i]); break;
                case "--start": startN = int.Parse(args[++i]); break;
                case "--out": outPath = args[++i]; break;
                case "--platform": platform = args[++i]; break;
            }

        var fams = selected.Count > 0 ? Families.Where(f => selected.Contains(f.Id)).ToArray() : Families;
        Console.WriteLine($"# evaluator resource probe  platform={platform}  child-timeout={timeoutMs}ms");

        var rows = new List<Row>();
        foreach (var f in fams)
        {
            var row = Characterize(f, timeoutMs, startN, platform);
            rows.Add(row);
            string b = row.ReachedBound
                ? $"completed-through n={row.LargestOk}"
                : $"OK<={row.LargestOk} FAIL@{row.FirstFail} len={row.FirstFailLen} [{row.Classification}] {row.FirstFailMs}ms";
            Console.WriteLine($"{f.Id,-16}{f.Kind,-12}{b}");
        }

        if (outPath.Length > 0)
        {
            try
            {
                var dir = Path.GetDirectoryName(outPath);
                if (!string.IsNullOrEmpty(dir)) Directory.CreateDirectory(dir);
                File.WriteAllText(outPath, JsonSerializer.Serialize(new { platform, timeoutMs, rows }, new JsonSerializerOptions { WriteIndented = true }), new UTF8Encoding(false));
                Console.WriteLine($"# wrote {rows.Count} rows -> {outPath}");
            }
            catch (Exception ex) { Console.Error.WriteLine($"warning: json write failed: {ex.Message}"); }
        }
        return 0;
    }

    private static Row Characterize(Family f, int timeoutMs, int startN, string platform)
    {
        int lo = 0, hi = -1;
        Run? loRun = null, hiRun = null;
        int probe = Math.Min(startN, f.MaxParam);

        while (true)
        {
            var r = Launch(f, probe, timeoutMs);
            if (r.Completed) { lo = probe; loRun = r; }
            else { hi = probe; hiRun = r; break; }
            if (probe >= f.MaxParam) break;
            probe = (int)Math.Min((long)probe * 4, f.MaxParam);
        }

        if (hi != -1)
        {
            while (hi - lo > 1)
            {
                int mid = lo + (hi - lo) / 2;
                var r = Launch(f, mid, timeoutMs);
                if (r.Completed) { lo = mid; loRun = r; } else { hi = mid; hiRun = r; }
            }
        }

        loRun ??= Launch(f, Math.Max(0, lo), timeoutMs);

        return hi == -1
            ? new Row(f.Id, f.Kind, platform, lo, loRun.Len, loRun.Ms, loRun.PeakKb, null, null, null,
                "completed-through-bound", null, null, true, f.ExpectedUnbounded)
            : new Row(f.Id, f.Kind, platform, lo, loRun.Len, loRun.Ms, loRun.PeakKb, hi, hiRun!.Len, hiRun.Ms,
                hiRun.Class, hiRun.Exit, Trunc(hiRun.Err, 200), false, f.ExpectedUnbounded);
    }

    private static Run Launch(Family f, int n, int timeoutMs)
    {
        string host = Environment.ProcessPath!;
        string? dll = Assembly.GetEntryAssembly()?.Location;
        string? self = Assembly.GetEntryAssembly()?.GetName().Name;
        bool selfContained = self is not null && string.Equals(Path.GetFileNameWithoutExtension(host), self, StringComparison.OrdinalIgnoreCase);

        var psi = new ProcessStartInfo(host) { RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false, CreateNoWindow = true };
        if (!selfContained && !string.IsNullOrEmpty(dll)) psi.ArgumentList.Add(dll);
        psi.ArgumentList.Add("eval-probe-child");
        psi.ArgumentList.Add(f.Id);
        psi.ArgumentList.Add(n.ToString());

        var sw = Stopwatch.StartNew();
        using var proc = new Process { StartInfo = psi };
        proc.Start();
        var o = proc.StandardOutput.ReadToEndAsync();
        var e = proc.StandardError.ReadToEndAsync();
        bool timedOut = false;
        if (!proc.WaitForExit(timeoutMs)) { timedOut = true; try { proc.Kill(true); } catch { } proc.WaitForExit(2000); }
        sw.Stop();

        string so = Safe(o), se = Safe(e);
        int? exit = null; long peak = 0;
        try { exit = proc.ExitCode; } catch { }
        try { peak = proc.PeakWorkingSet64 / 1024; } catch { }

        int len = ParseLen(so);
        bool soe = se.Contains("Stack overflow", StringComparison.OrdinalIgnoreCase)
                   || exit is -1073741571 or -1073740791 or 134 or 139;
        bool oom = se.Contains("OutOfMemory", StringComparison.OrdinalIgnoreCase) || exit is 137;

        string cls =
            timedOut ? "timeout" :
            exit == ExitCompleted ? "completed" :
            exit == ExitStructured ? "structured-error" :
            exit == ExitUnexpected ? "unexpected-exception" :
            soe ? "stack-overflow" :
            oom ? "oom-or-killed" :
            exit is null ? "killed" : $"process-crash(exit={exit})";

        // "Completed" for boundary search means the child finished without crashing:
        // a structured EvalError is an expected outcome, not a failure.
        bool completed = !timedOut && (exit == ExitCompleted || exit == ExitStructured);
        return new Run(completed, exit, timedOut, len, sw.ElapsedMilliseconds, peak, cls, se);
    }

    private static string Safe(Task<string> t) { try { return t.GetAwaiter().GetResult() ?? ""; } catch { return ""; } }
    private static string Trunc(string s, int n) => string.IsNullOrEmpty(s) ? s : (s.Length <= n ? s : s[..n]);

    private static int ParseLen(string stdout)
    {
        foreach (var line in stdout.Split('\n'))
        {
            int i = line.IndexOf("len=", StringComparison.Ordinal);
            if (i < 0) continue;
            var num = new string(line[(i + 4)..].TakeWhile(char.IsDigit).ToArray());
            if (int.TryParse(num, out int v)) return v;
        }
        return -1;
    }
}
