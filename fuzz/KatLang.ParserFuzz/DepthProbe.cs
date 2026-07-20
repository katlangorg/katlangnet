using System.Diagnostics;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.Json;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Phase-2 deterministic depth-limit characterization for the raw KatLang parser.
///
/// The dangerous parse of a deeply nested input can trigger an UNCATCHABLE
/// <see cref="StackOverflowException"/> that terminates the process, so it must never
/// run inside the coordinator (or inside xUnit). This tool therefore has two roles:
///
///   * CHILD  (<c>probe-child FAMILY DEPTH MODE MAXBYTES</c>): generates exactly one
///     input for (family, depth), calls <c>Parser.ParseSyntax</c>, and — when MODE is
///     "invariants" — runs the existing fuzz invariants. Managed exceptions are caught
///     and reported with a phase-specific exit code; a fatal stack overflow is left to
///     terminate the process so the parent can observe it.
///
///   * PARENT (<c>probe [options]</c>): launches child processes with a timeout and
///     captured exit code / stdout / stderr / elapsed time / input length, uses
///     exponential then binary search to locate each family's success/failure boundary,
///     writes machine-readable JSON under the gitignored artifacts dir, and prints a
///     compact table.
///
/// Isolating MODE=parser vs MODE=invariants separates a genuine PARSER stack overflow
/// (fails in parser-only mode) from a HARNESS AST-walker overflow (parser-only succeeds
/// but +invariants fails at a lower depth).
/// </summary>
internal static class DepthProbe
{
    // Child exit codes (fatal stack overflow uses the platform's own code instead).
    private const int ExitParseOk = 0;
    private const int ExitParseManagedException = 10;
    private const int ExitInvariantManagedException = 11;
    private const int ExitSizeCapped = 12;
    private const int ExitBadArgs = 2;

    // ── Source families ──────────────────────────────────────────────────────
    private sealed record Family(string Id, Func<int, string> Gen, int BaseBytes, int PerLevel, string Kind);

    private static string Rep(string s, int n) => n <= 0 ? "" : string.Concat(Enumerable.Repeat(s, n));

    private static readonly Family[] Families =
    [
        // Balanced value nesting.
        new("paren",  d => new string('(', d) + "1" + new string(')', d),           1,  2, "balanced"),
        new("list",   d => new string('[', d) + "1" + new string(']', d),           1,  2, "balanced"),
        new("brace",  d => new string('{', d) + "1" + new string('}', d),           1,  2, "balanced"),
        new("mixed",  d => Rep("([{", d) + "1" + Rep("}])", d),                      1,  6, "balanced"),
        new("call",   d => Rep("F(", d) + "1" + new string(')', d),                  1,  3, "balanced"),
        // Prefix / operator recursion.
        new("neg",    d => new string('-', d) + "1",                                1,  1, "prefix"),
        new("not",    d => Rep("not ", d) + "1",                                     1,  4, "prefix"),
        new("pow",    d => Rep("1 ^ ", d) + "1",                                     1,  4, "operator"),
        // Pattern recursion (clause head + clause-definition lookahead).
        new("patParen", d => "F" + new string('(', d) + "x" + new string(')', d) + " = x\nF(1)", 12, 2, "pattern"),
        new("patComma", d => "F" + new string('(', d) + "x, y" + new string(')', d) + " = x\nF(1)", 15, 2, "pattern"),
        // Malformed nesting / recovery (should complete WITH diagnostics, not crash).
        new("unclosedParen", d => new string('(', d) + "1",                         1,  1, "malformed"),
        new("unclosedList",  d => new string('[', d) + "1",                         1,  1, "malformed"),
        new("unclosedBrace", d => new string('{', d) + "1",                         1,  1, "malformed"),
        new("closersOnly",   d => new string(')', d),                               0,  1, "malformed"),
        new("unclosedCall",  d => Rep("F(", d) + "1",                               1,  2, "malformed"),
    ];

    private static Family? Find(string id) => Families.FirstOrDefault(f => f.Id == id);

    // ── Child mode ───────────────────────────────────────────────────────────
    public static int RunChild(string[] args)
    {
        // args: probe-child FAMILY DEPTH MODE MAXBYTES
        if (args.Length < 4)
        {
            Console.Error.WriteLine("probe-child FAMILY DEPTH MODE [MAXBYTES]");
            return ExitBadArgs;
        }

        var family = Find(args[1]);
        if (family is null) { Console.Error.WriteLine($"unknown family: {args[1]}"); return ExitBadArgs; }
        if (!int.TryParse(args[2], out int depth)) { Console.Error.WriteLine("bad depth"); return ExitBadArgs; }
        string mode = args[3];
        int maxBytes = args.Length >= 5 && int.TryParse(args[4], out int mb) ? mb : 1 << 20;

        // Guard against building an oversized input (the parent should already avoid
        // this, but the child is the real enforcement point).
        long projected = (long)family.BaseBytes + (long)family.PerLevel * depth;
        if (projected > maxBytes)
        {
            Console.Out.WriteLine($"CHILD family={family.Id} depth={depth} mode={mode} len=~{projected} SIZECAP");
            return ExitSizeCapped;
        }

        string source = family.Gen(depth);
        // Flushed immediately (Console.Out.AutoFlush is true) so the parent still sees
        // the length even if the following parse overflows the stack and dies.
        Console.Out.WriteLine($"CHILD family={family.Id} depth={depth} mode={mode} len={source.Length}");

        SyntaxParseResult result;
        try
        {
            result = Parser.ParseSyntax(source);
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine($"PARSE_EXCEPTION {ex.GetType().FullName}: {ex.Message}");
            Console.Error.WriteLine(ex.StackTrace);
            return ExitParseManagedException;
        }

        Console.Out.WriteLine($"PARSE_OK diags={result.Diagnostics.Count}");

        if (mode == "invariants")
        {
            try
            {
                FuzzInvariants.Check(source, result);
            }
            catch (Exception ex)
            {
                Console.Error.WriteLine($"INVARIANT_EXCEPTION {ex.GetType().FullName}: {ex.Message}");
                Console.Error.WriteLine(ex.StackTrace);
                return ExitInvariantManagedException;
            }
            Console.Out.WriteLine("INVARIANTS_OK");
        }

        return ExitParseOk;
    }

    // ── Parent mode ──────────────────────────────────────────────────────────
    private sealed record ChildRun(bool Success, int? ExitCode, bool TimedOut, int Length, long ElapsedMs, string Classification, string StderrSnippet, long PeakWorkingSetKb);

    private sealed record FamilyResult(
        string Family, string Kind, string Mode, string Platform,
        int LargestSuccessDepth, int LargestSuccessLen, long LargestSuccessMs,
        int? SmallestFailDepth, int? SmallestFailLen, long? SmallestFailMs,
        string Classification, int? BoundaryExitCode, string? BoundaryStderr,
        bool ReachedBound, int DepthCap);

    private sealed class Options
    {
        public List<string> Families = [];
        public string Mode = "both";          // parser | invariants | both
        public int MaxDepth = 200_000;
        public int MaxBytes = 1 << 20;         // 1 MiB
        public int TimeoutMs = 5000;
        public int StartDepth = 8;
        public string OutPath = "";
        public string Platform = ShortPlatform();
    }

    public static int RunParent(string[] args)
    {
        var opt = ParseOptions(args);
        var selected = opt.Families.Count > 0
            ? Families.Where(f => opt.Families.Contains(f.Id)).ToArray()
            : Families;

        if (selected.Length == 0) { Console.Error.WriteLine("no matching families"); return ExitBadArgs; }

        var modes = opt.Mode switch
        {
            "parser" => new[] { "parser" },
            "invariants" => new[] { "invariants" },
            _ => new[] { "parser", "invariants" },
        };

        Console.WriteLine($"# depth probe  platform={opt.Platform}  timeout={opt.TimeoutMs}ms  maxDepth={opt.MaxDepth}  maxBytes={opt.MaxBytes}");
        Console.WriteLine($"# families={string.Join(",", selected.Select(f => f.Id))}  modes={string.Join(",", modes)}");

        var results = new List<FamilyResult>();
        foreach (var fam in selected)
        {
            int? parserFirstFail = null;
            foreach (var mode in modes)
            {
                // For invariants mode, cap the search at the parser-only failure depth:
                // the parser runs first, so invariants can never survive past it.
                int cap = ComputeDepthCap(fam, opt);
                if (mode == "invariants" && parserFirstFail is int pf) cap = Math.Min(cap, pf);

                var res = Characterize(fam, mode, opt, cap);
                results.Add(res);
                if (mode == "parser") parserFirstFail = res.SmallestFailDepth;

                PrintRow(res);
            }
        }

        WriteJson(opt, results);
        Console.WriteLine();
        Console.WriteLine($"# wrote {results.Count} rows -> {opt.OutPath}");
        return 0;
    }

    private static int ComputeDepthCap(Family fam, Options opt)
    {
        long byBytes = fam.PerLevel <= 0 ? opt.MaxDepth : (opt.MaxBytes - fam.BaseBytes) / fam.PerLevel;
        return (int)Math.Min(opt.MaxDepth, Math.Max(1, byBytes));
    }

    private static FamilyResult Characterize(Family fam, string mode, Options opt, int depthCap)
    {
        // Exponential growth to bracket the boundary.
        int lo = 0;                 // largest confirmed success
        int hi = -1;                // smallest confirmed failure
        ChildRun? loRun = null, hiRun = null;

        int probe = Math.Min(opt.StartDepth, depthCap);
        while (true)
        {
            var r = Launch(fam, probe, mode, opt);
            if (r.Success) { lo = probe; loRun = r; }
            else { hi = probe; hiRun = r; break; }

            if (probe >= depthCap) break;             // reached configured bound, no failure
            probe = Math.Min(probe * 2, depthCap);
            if (probe == lo) break;                    // clamped at cap and already succeeded there
        }

        // Binary search for the exact boundary when a failure was found.
        if (hi != -1)
        {
            while (hi - lo > 1)
            {
                int mid = lo + (hi - lo) / 2;
                var r = Launch(fam, mid, mode, opt);
                if (r.Success) { lo = mid; loRun = r; }
                else { hi = mid; hiRun = r; }
            }

            // Reproducibility: confirm the boundary failure repeats.
            var confirm = Launch(fam, hi, mode, opt);
            if (confirm.Success)
            {
                // Flaky boundary — treat as success-through and report cautiously.
                lo = hi; loRun = confirm; hi = -1; hiRun = null;
            }
            else
            {
                hiRun = confirm;
            }
        }

        if (loRun is null) loRun = Launch(fam, Math.Max(1, lo), mode, opt);

        return hi == -1
            ? new FamilyResult(fam.Id, fam.Kind, mode, opt.Platform, lo, loRun.Length, loRun.ElapsedMs,
                null, null, null, "success-through-bound", null, null, ReachedBound: true, depthCap)
            : new FamilyResult(fam.Id, fam.Kind, mode, opt.Platform, lo, loRun.Length, loRun.ElapsedMs,
                hi, hiRun!.Length, hiRun.ElapsedMs, hiRun.Classification, hiRun.ExitCode,
                Trunc(hiRun.StderrSnippet, 240), ReachedBound: false, depthCap);
    }

    private static ChildRun Launch(Family fam, int depth, string mode, Options opt)
    {
        var (host, prefixArgs) = SelfInvocation();
        var psi = new ProcessStartInfo(host)
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true,
        };
        foreach (var a in prefixArgs) psi.ArgumentList.Add(a);
        psi.ArgumentList.Add("probe-child");
        psi.ArgumentList.Add(fam.Id);
        psi.ArgumentList.Add(depth.ToString());
        psi.ArgumentList.Add(mode);
        psi.ArgumentList.Add(opt.MaxBytes.ToString());

        var sw = Stopwatch.StartNew();
        using var proc = new Process { StartInfo = psi };
        proc.Start();
        var outTask = proc.StandardOutput.ReadToEndAsync();
        var errTask = proc.StandardError.ReadToEndAsync();

        bool timedOut = false;
        if (!proc.WaitForExit(opt.TimeoutMs))
        {
            timedOut = true;
            try { proc.Kill(entireProcessTree: true); } catch { /* already gone */ }
            proc.WaitForExit(2000);
        }
        sw.Stop();

        string stdout = SafeResult(outTask);
        string stderr = SafeResult(errTask);
        int? exit = null;
        long peakKb = 0;
        try { exit = proc.ExitCode; } catch { /* killed */ }
        try { peakKb = proc.PeakWorkingSet64 / 1024; } catch { /* not available on this OS */ }

        int len = ParseLen(stdout);
        var (success, classification) = Classify(timedOut, exit, stdout, stderr);
        return new ChildRun(success, exit, timedOut, len, sw.ElapsedMilliseconds, classification, stderr, peakKb);
    }

    private static (bool success, string classification) Classify(bool timedOut, int? exit, string stdout, string stderr)
    {
        if (timedOut) return (false, "timeout");
        if (exit == ExitParseOk) return (true, stdout.Contains("PARSE_OK diags=0") ? "ok" : "ok-with-diagnostics");
        if (exit == ExitSizeCapped) return (true, "size-capped");        // not a failure, just skipped

        bool soe = stderr.Contains("Stack overflow", StringComparison.OrdinalIgnoreCase)
                   || exit is -1073741571 or -1073740791     // Windows STATUS_STACK_OVERFLOW / FailFast
                   || exit is 134 or 139 or 132;             // Linux SIGABRT / SIGSEGV / SIGILL

        if (exit == ExitParseManagedException)
            return (false, soe ? "parser-stack-overflow" : "parser-managed-exception");
        if (exit == ExitInvariantManagedException)
            return (false, soe ? "invariant-stack-overflow" : "invariant-managed-exception");

        if (soe) return (false, "stack-overflow");
        return (false, exit is null ? "killed" : $"process-crash(exit={exit})");
    }

    // ── Self re-invocation (framework-dependent dotnet host OR self-contained apphost) ──
    private static (string host, string[] prefix) SelfInvocation()
    {
        string host = Environment.ProcessPath!;
        string? entryDll = Assembly.GetEntryAssembly()?.Location;
        string? selfName = Assembly.GetEntryAssembly()?.GetName().Name;
        bool selfContained = selfName is not null
            && string.Equals(Path.GetFileNameWithoutExtension(host), selfName, StringComparison.OrdinalIgnoreCase);

        // Self-contained apphost: run it directly. dotnet host: pass the managed dll.
        return selfContained || string.IsNullOrEmpty(entryDll)
            ? (host, [])
            : (host, [entryDll]);
    }

    // ── Option parsing / helpers ─────────────────────────────────────────────
    private static Options ParseOptions(string[] args)
    {
        var o = new Options();
        for (int i = 1; i < args.Length; i++)
        {
            switch (args[i])
            {
                case "--families": o.Families = Next(args, ref i).Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries).ToList(); break;
                case "--mode": o.Mode = Next(args, ref i); break;
                case "--max-depth": o.MaxDepth = int.Parse(Next(args, ref i)); break;
                case "--max-bytes": o.MaxBytes = int.Parse(Next(args, ref i)); break;
                case "--timeout-ms": o.TimeoutMs = int.Parse(Next(args, ref i)); break;
                case "--start-depth": o.StartDepth = int.Parse(Next(args, ref i)); break;
                case "--out": o.OutPath = Next(args, ref i); break;
                case "--platform": o.Platform = Next(args, ref i); break;
            }
        }
        if (string.IsNullOrEmpty(o.OutPath))
            o.OutPath = Path.Combine(Directory.GetCurrentDirectory(), $"depth-probe-{o.Platform}.json");
        return o;
    }

    private static string Next(string[] args, ref int i)
        => ++i < args.Length ? args[i] : throw new ArgumentException($"missing value after {args[i - 1]}");

    private static int ParseLen(string stdout)
    {
        foreach (var line in stdout.Split('\n'))
        {
            int idx = line.IndexOf("len=", StringComparison.Ordinal);
            if (idx >= 0)
            {
                var rest = line[(idx + 4)..].TrimStart('~').Trim();
                var num = new string(rest.TakeWhile(char.IsDigit).ToArray());
                if (int.TryParse(num, out int v)) return v;
            }
        }
        return -1;
    }

    private static string SafeResult(Task<string> t)
    {
        try { return t.GetAwaiter().GetResult() ?? ""; }
        catch { return ""; }
    }

    private static string Trunc(string s, int n) => string.IsNullOrEmpty(s) ? s : (s.Length <= n ? s : s[..n]);

    private static string ShortPlatform()
    {
        if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) return "windows";
        if (RuntimeInformation.IsOSPlatform(OSPlatform.Linux)) return "linux";
        if (RuntimeInformation.IsOSPlatform(OSPlatform.OSX)) return "macos";
        return "unknown";
    }

    private static void PrintRow(FamilyResult r)
    {
        string boundary = r.ReachedBound
            ? $"success-through depth={r.LargestSuccessDepth} (len={r.LargestSuccessLen})"
            : $"OK<={r.LargestSuccessDepth} FAIL@{r.SmallestFailDepth} len={r.SmallestFailLen} [{r.Classification}] exit={r.BoundaryExitCode}";
        Console.WriteLine($"{r.Family,-14} {r.Mode,-11} {boundary}");
    }

    private static void WriteJson(Options opt, List<FamilyResult> results)
    {
        try
        {
            var dir = Path.GetDirectoryName(opt.OutPath);
            if (!string.IsNullOrEmpty(dir)) Directory.CreateDirectory(dir);
            var json = JsonSerializer.Serialize(new
            {
                platform = opt.Platform,
                timeoutMs = opt.TimeoutMs,
                maxDepth = opt.MaxDepth,
                maxBytes = opt.MaxBytes,
                results,
            }, new JsonSerializerOptions { WriteIndented = true });
            File.WriteAllText(opt.OutPath, json, new UTF8Encoding(false));
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine($"warning: could not write results json: {ex.Message}");
        }
    }
}
