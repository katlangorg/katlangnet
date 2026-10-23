using System.Diagnostics;
using System.Diagnostics.Tracing;
using System.Globalization;
using System.Reflection;
using System.Runtime;
using System.Runtime.InteropServices;
using System.Text;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// SEC-S1 front-end MEMORY probe. Two modes that are never mixed:
///
///   fe-mem [options]                          parent: serially launches one isolated child per
///                                             (shape, size, route) under a GC heap hard limit, a
///                                             Windows job-object commit limit (parent polling
///                                             elsewhere), and a wall-clock timeout
///   fe-mem-child faithful ROUTE SHAPE CHARS   ONE public operation, realistic lifetimes
///   fe-mem-child census SHAPE CHARS           stage attribution with EXPLICIT retention
///   fe-mem-diff OUT DIR...                    per-input semantic hashes, to diff two builds
///
/// Routes: lex, parse, parse-async, parse-async-dl (the shape is a module loaded through an
/// in-memory downloader that genuinely suspends), run, run-async, and the diagnostic
/// parse-cancel-N (cancellation latency). <c>--max-peak-commit-mb N</c> turns a parent run into a
/// regression check: any child over the envelope, or any incomplete measurement, fails it.
/// Diagnostic-only environment switches (never set by default): FE_MEM_LIVE_SAMPLE_MS (forced
/// full collections during the operation — a live-set measurement that perturbs time),
/// FE_MEM_DUMP_AT_MB / FE_MEM_DUMP_AFTER_RELEASE with FE_MEM_DUMP_TOOL / FE_MEM_DUMP_PATH (a heap
/// dump at the live peak, with the measured thread suspended, or after release).
///
/// FAITHFUL (mode A) runs exactly one public entry point (Lexer.Tokenize, Parser.Parse,
/// Parser.ParseAsync, KatLangEngine.Run/RunAsync) on the generated source, after warming the
/// same route on a 1 KiB instance of the same shape. Further JIT/tiering during the measured call
/// remains included; the warmup does not establish a fully warmed steady state.
/// It reports the operation's allocated bytes (GC.GetTotalAllocatedBytes(precise) delta, valid
/// across async/thread transitions because it is process-wide; the only other thread is an
/// allocation-free sampler), the maximum managed heap size sampled during the operation, the
/// managed heap retained with the result deliberately alive and after it is released (both
/// after forced full blocking compacting collections — a SEPARATE step after the peak
/// measurement), and process peak working set / peak private bytes (the parent's job object
/// reports the child's exact peak commit). The source string itself is allocated before the
/// baseline, so it is never counted as operation allocation.
///
/// CENSUS (mode B) instruments individual stages and explicitly retains raw and elaborated graphs
/// together for the sharing census: the token list, raw syntax tree and elaborated tree, with
/// distinct-reference node counts, token kind histograms, identifier text counts, the number of
/// elaborated nodes physically shared with the raw tree, and a sampled allocation-by-type profile
/// of one Parser.Parse (runtime AllocationTick events). Its numbers are ATTRIBUTION, not
/// production peak memory.
/// </summary>
internal static class FrontEndMemoryProbe
{
    // ── shapes: generated up to a target length in UTF-16 code units ─────────────

    private sealed record Shape(string Id, string Kind, string Prefix, Func<int, string> Unit, Func<int, string> Suffix);

    private static string Names(string prefix, int count)
        => string.Join(", ", Enumerable.Range(0, count).Select(i => $"{prefix}{i}"));

    private static readonly Shape[] Shapes =
    [
        // valid dense declarations, many small tokens, trivial output
        new("dense_props", "dense", "", i => $"A{i} = {i}\n", _ => "A0"),
        new("dense_funcs", "dense", "", i => $"F{i}(x) = x + {i}\n", _ => "F0(1)"),
        new("dense_exprs", "dense", "", i => $"E{i} = (1 + 2) * 3 - 4 / 5 + 6\n", _ => "1"),
        // repeated identifier text versus mostly unique (dense_props)
        new("repeated_ident", "dense", "Same = 1\n", i => $"R{i} = Same + Same + Same + Same\n", _ => "1"),
        // wide legal constructs
        new("wide_list", "wide", "L = [", _ => "1, ", _ => "1]\n1"),
        new("wide_seq", "wide", "S = sum((", _ => "1, ", _ => "1))\n1"),
        new("wide_params", "wide", "F(", i => $"x{i}, ", _ => "y) = y\n1"),
        new("wide_decon", "wide", "", i => $"x{i}, ", n => $"x{n} = range(1, {n + 1})\nx0"),
        // low-token controls of comparable length
        new("ws", "control", "1", _ => "        ", _ => ""),
        new("comment", "control", "# ", _ => "xxxxxxxx", _ => "\n1"),
        new("long_string", "control", "S = '", _ => "xxxxxxxx", _ => "'\n1"),
        // already-fixed sharing shapes (FE-2 implicit lifting, FE-3/FE-4 ancestor requirements)
        new("implicit_lift", "sharing", $"G = {Names("v", 300)}\nH = ", _ => "abs(G), ", _ => "abs(G)\n1"),
        new("ancestor_blocks", "sharing", $"F({Names("v", 150)}) = v0", i => $", {{b{i} = a + 1\nb{i}}}", _ => "\n1"),
        new("nested_opens", "sharing", "Lib = {\n    public X = 1\n}\n", i => $"B{i} = {{\n    open Lib\n    C = {{\n        open Lib\n        X + {i}\n    }}\n    C\n}}\n", _ => "1"),
        // bounded malformed input (diagnostic list capped by MaxDiagnosticCount)
        new("diag_tokens", "malformed", "", _ => "@ ", _ => ""),
        new("diag_props", "malformed", "", i => $"A{i} = 1 +\n", _ => "1"),
    ];

    private static Shape? Find(string id) => Shapes.FirstOrDefault(s => s.Id == id);

    private const int SuffixReserve = 64;

    private static string Generate(Shape shape, int targetChars)
    {
        var sb = new StringBuilder(targetChars + SuffixReserve);
        sb.Append(shape.Prefix);
        var n = 0;
        while (true)
        {
            var unit = shape.Unit(n);
            if (sb.Length + unit.Length + SuffixReserve > targetChars) break;
            sb.Append(unit);
            n++;
        }

        sb.Append(shape.Suffix(n));
        return sb.ToString();
    }

    private static readonly string[] Routes = ["lex", "parse", "parse-async", "run", "run-async"];

    // ── parent ────────────────────────────────────────────────────────────────

    public static int RunParent(string[] args)
    {
        var shapes = Shapes.Select(s => s.Id).ToList();
        var routes = new List<string> { "parse" };
        var sizes = new List<int> { 16 * 1024, 64 * 1024, 256 * 1024 };
        var mode = "faithful";
        long heapLimitMb = 2048, jobLimitMb = 3072;
        int timeoutMs = 120_000, repeat = 1;
        long maxPeakCommitMb = 0;
        string outPath = "";
        var extraEnv = new List<string>();
        for (var i = 1; i < args.Length; i++)
            switch (args[i])
            {
                case "--shapes": shapes = Split(args[++i]); break;
                case "--routes": routes = Split(args[++i]); break;
                case "--sizes": sizes = Split(args[++i]).Select(ParseSize).ToList(); break;
                case "--mode": mode = args[++i]; break;
                case "--heap-limit-mb": heapLimitMb = long.Parse(args[++i], CultureInfo.InvariantCulture); break;
                case "--job-limit-mb": jobLimitMb = long.Parse(args[++i], CultureInfo.InvariantCulture); break;
                case "--timeout-ms": timeoutMs = int.Parse(args[++i], CultureInfo.InvariantCulture); break;
                case "--repeat": repeat = int.Parse(args[++i], CultureInfo.InvariantCulture); break;
                case "--out": outPath = args[++i]; break;
                case "--env": extraEnv.Add(args[++i]); break;
                case "--max-peak-commit-mb": maxPeakCommitMb = long.Parse(args[++i], CultureInfo.InvariantCulture); break;
                default: Console.Error.WriteLine($"unknown option {args[i]}"); return 2;
            }

        if (mode is not ("faithful" or "census") || shapes.Count == 0 || routes.Count == 0
            || sizes.Count == 0 || sizes.Any(size => size <= 0) || repeat <= 0
            || heapLimitMb <= 0 || jobLimitMb <= 0 || timeoutMs <= 0 || maxPeakCommitMb < 0)
        {
            Console.Error.WriteLine("Expected a nonempty matrix, positive caps/timeout/repeat, and faithful or census mode.");
            return 2;
        }

        Console.WriteLine($"# fe-mem mode={mode} build={BuildConfig()} runtime={RuntimeInformation.FrameworkDescription} " +
                          $"os={RuntimeInformation.OSDescription} arch={RuntimeInformation.ProcessArchitecture} " +
                          $"heapLimitMb={heapLimitMb} jobLimitMb={jobLimitMb} timeoutMs={timeoutMs} maxPeakCommitMb={maxPeakCommitMb}");
        var failures = 0;
        var lines = new List<string>();
        foreach (var shape in shapes)
        foreach (var size in sizes)
        foreach (var route in mode == "census" ? ["census"] : routes)
        for (var r = 0; r < repeat; r++)
        {
            string[] childArgs = mode == "census"
                ? ["fe-mem-child", "census", shape, size.ToString(CultureInfo.InvariantCulture)]
                : ["fe-mem-child", "faithful", route, shape, size.ToString(CultureInfo.InvariantCulture)];
            var outcome = Launch(childArgs, heapLimitMb, jobLimitMb, timeoutMs, extraEnv);
            // ENVELOPE (opt-in regression check): a child over the peak-commit envelope fails the
            // run, and so does any incomplete measurement (timeout, cap hit, OOM) — never a pass.
            var status = maxPeakCommitMb > 0 && outcome.Status == "ok" && outcome.JobPeakKb > maxPeakCommitMb * 1024 ? "over-envelope" : outcome.Status;
            if (status != "ok")
                failures++;
            var line = $"{status} shape={shape} size={size} route={route} jobPeakCommitKb={outcome.JobPeakKb} exit={outcome.Exit} {outcome.Result}";
            Console.WriteLine(line);
            if (outcome.Status != "ok" && outcome.Stderr.Length > 0)
                Console.WriteLine($"  stderr: {Trunc(outcome.Stderr.ReplaceLineEndings(" | "), 400)}");
            lines.Add(line);
        }

        if (outPath.Length > 0)
        {
            var dir = Path.GetDirectoryName(outPath);
            if (!string.IsNullOrEmpty(dir)) Directory.CreateDirectory(dir);
            File.WriteAllLines(outPath, lines, new UTF8Encoding(false));
        }

        if (maxPeakCommitMb > 0)
            Console.WriteLine($"# envelope {maxPeakCommitMb} MB: {(failures == 0 ? "PASS" : $"FAIL ({failures} run(s) over the envelope or incomplete)")}");
        Console.WriteLine($"# measurements={lines.Count} failures={failures}");
        return failures == 0 ? 0 : 1;
    }

    private static List<string> Split(string s) => s.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries).ToList();

    private static int ParseSize(string s)
    {
        if (s.EndsWith('k') || s.EndsWith('K')) return int.Parse(s[..^1], CultureInfo.InvariantCulture) * 1024;
        if (s.EndsWith('m') || s.EndsWith('M')) return int.Parse(s[..^1], CultureInfo.InvariantCulture) * 1024 * 1024;
        return int.Parse(s, CultureInfo.InvariantCulture);
    }

    private sealed record Outcome(string Status, int? Exit, long JobPeakKb, string Result, string Stderr);

    private static Outcome Launch(string[] childArgs, long heapLimitMb, long jobLimitMb, int timeoutMs, List<string> extraEnv)
    {
        string host = Environment.ProcessPath!;
        string? dll = Assembly.GetEntryAssembly()?.Location;
        string? self = Assembly.GetEntryAssembly()?.GetName().Name;
        bool selfContained = self is not null && string.Equals(Path.GetFileNameWithoutExtension(host), self, StringComparison.OrdinalIgnoreCase);

        var psi = new ProcessStartInfo(host)
        {
            RedirectStandardOutput = true, RedirectStandardError = true, RedirectStandardInput = true,
            UseShellExecute = false, CreateNoWindow = true,
        };
        if (!selfContained && !string.IsNullOrEmpty(dll)) psi.ArgumentList.Add(dll);
        foreach (var a in childArgs) psi.ArgumentList.Add(a);
        psi.Environment["DOTNET_GCHeapHardLimit"] = "0x" + (heapLimitMb * 1024 * 1024).ToString("X", CultureInfo.InvariantCulture);
        foreach (var key in psi.Environment.Keys.Where(k => k.StartsWith("KATLANG_", StringComparison.OrdinalIgnoreCase)).ToList())
            psi.Environment.Remove(key);
        foreach (var pair in extraEnv)
        {
            var eq = pair.IndexOf('=');
            if (eq > 0) psi.Environment[pair[..eq]] = pair[(eq + 1)..];
        }

        using var proc = new Process { StartInfo = psi };
        proc.Start();
        using var job = OperatingSystem.IsWindows() ? JobLimit.TryCreate(proc, jobLimitMb * 1024 * 1024) : null;
        // The child generates nothing until the job holds it.
        proc.StandardInput.WriteLine("go");
        proc.StandardInput.Flush();

        var o = proc.StandardOutput.ReadToEndAsync();
        var e = proc.StandardError.ReadToEndAsync();
        var sw = Stopwatch.StartNew();
        string status = "ok";
        long polledPeak = 0;
        while (!proc.WaitForExit(50))
        {
            try { proc.Refresh(); polledPeak = Math.Max(polledPeak, proc.PrivateMemorySize64); } catch { }
            if (job is null && polledPeak > jobLimitMb * 1024 * 1024) { status = "killed-envelope"; Kill(proc); break; }
            if (sw.ElapsedMilliseconds > timeoutMs) { status = "timeout"; Kill(proc); break; }
        }

        proc.WaitForExit();
        int? exit = null;
        try { exit = proc.ExitCode; } catch { }
        var so = Safe(o);
        var se = Safe(e);
        long jobPeak = job?.PeakProcessMemoryUsed() / 1024 ?? polledPeak / 1024;
        var result = string.Join(" ", so.Split('\n').Where(l => l.StartsWith("RESULT ", StringComparison.Ordinal)).Select(l => l["RESULT ".Length..].TrimEnd('\r')));
        if (status == "ok" && exit != 0)
            status = se.Contains("OutOfMemory", StringComparison.Ordinal) ? "oom" : $"failed";
        if (status == "ok" && result.Length == 0) status = "no-result";
        return new Outcome(status, exit, jobPeak, result, se);
    }

    private static void Kill(Process p) { try { p.Kill(true); } catch { } }
    private static string Safe(Task<string> t) { try { return t.GetAwaiter().GetResult() ?? ""; } catch { return ""; } }
    private static string Trunc(string s, int n) => s.Length <= n ? s : s[..n];
    private static string BuildConfig() =>
#if DEBUG
        "debug";
#else
        "release";
#endif

    // ── semantic differential (baseline vs candidate builds) ────────────────────

    /// <summary>
    /// fe-mem-diff OUT DIR...: one line per input — every file of the given corpus directories
    /// (decoded as UTF-8, as the byte fuzzers do) plus every shape at 1 and 4 KiB — with a SHA-256 of
    /// the public parse fingerprint (diagnostics with spans, the elaborated tree, exposure), every
    /// property's RequiredAncestorParameters and owner-qualified CaptureRequirements, and, for a
    /// valid program, the KatLangEngine.Run outcome under a 2 s evaluation cancellation. Run the
    /// SAME command with a baseline build and a candidate build and compare the files.
    /// </summary>
    public static int RunDiff(string[] args)
    {
        if (args.Length < 2) { Console.Error.WriteLine("fe-mem-diff OUT [DIR...]"); return 2; }
        // Corpus parsing/fingerprinting is hostile work too: it belongs in a capped, supervised
        // child, never in the launcher. These defaults are deliberately below the large stress lane.
        var outcome = Launch(["fe-mem-diff-child", .. args.Skip(1)], 512, 1024, 600_000, []);
        Console.WriteLine($"# diff status={outcome.Status} exit={outcome.Exit} {outcome.Result}");
        if (outcome.Stderr.Length > 0) Console.Error.WriteLine(Trunc(outcome.Stderr, 1000));
        return outcome.Status == "ok" ? 0 : 1;
    }

    public static int RunDiffChild(string[] args)
    {
        _ = Console.In.ReadLine();
        if (args.Length < 2) { Console.Error.WriteLine("fe-mem-diff OUT [DIR...]"); return 2; }
        var inputs = new List<(string Id, string Source)>();
        foreach (var dir in args.Skip(2))
        {
            foreach (var file in Directory.EnumerateFiles(dir).Order(StringComparer.Ordinal))
            {
                var bytes = File.ReadAllBytes(file);
                if (bytes.Length > 1 << 20) continue;
                inputs.Add(($"{Path.GetFileName(dir)}/{Path.GetFileName(file)}", Encoding.UTF8.GetString(bytes)));
            }
        }

        foreach (var shape in Shapes)
        foreach (var size in new[] { 1024, 4096 })
            inputs.Add(($"shape/{shape.Id}/{size}", Generate(shape, size)));

        using var writer = new StreamWriter(args[1], append: false, new UTF8Encoding(false));
        foreach (var (id, source) in inputs)
            writer.WriteLine($"{id}\t{DiffLine(source)}");
        Console.WriteLine($"RESULT diff inputs={inputs.Count} output={args[1]}");
        return 0;
    }

    private static string DiffLine(string source)
    {
        var text = new StringBuilder();
        try
        {
            var parsed = Parser.Parse(source);
            text.Append(FrontEndFingerprint.ComputeParseResult(parsed.Root, parsed.Diagnostics)).Append('\n');
            text.Append(RequirementFingerprint(parsed.Root));
            if (!parsed.HasErrors)
            {
                using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(2));
                var run = KatLangEngine.Run(source, new RunOptions { EvaluationCancellationToken = timeout.Token });
                text.Append("\nrun:").Append(run switch
                {
                    RunResult.Success success => $"ok:rows={success.EmittedCount}:" + ValueFingerprint(success.Value),
                    RunResult.EvalFailure failure => "eval:" + string.Join("|", failure.Errors.Select(error => error.ToString())),
                    _ => run.GetType().Name,
                });
            }
        }
        catch (OperationCanceledException) { text.Append("\nrun:cancelled"); }

        return Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(Encoding.UTF8.GetBytes(text.ToString())))[..24];
    }

    internal static string ValueFingerprint(Result value)
    {
        var text = new StringBuilder();
        Append(value);
        return text.ToString();

        void Append(Result item)
        {
            switch (item)
            {
                case Result.Atom atom: Field(text, "n", atom.Value.ToString(CultureInfo.InvariantCulture)); break;
                case Result.Str str: Field(text, "s", str.Value); break;
                case Result.Bool boolean: text.Append(boolean.Value ? "t" : "f"); break;
                case Result.SequenceValue sequence: Items("q", sequence.Items); break;
                case Result.ListValue list: Items("l", list.Items); break;
                default: throw new InvalidOperationException($"Unexpected exported result {item.GetType().Name}");
            }
        }

        void Items(string tag, IReadOnlyList<Result> items)
        {
            text.Append(tag).Append(items.Count).Append('[');
            foreach (var item in items) Append(item);
            text.Append(']');
        }
    }

    private static void Field(StringBuilder text, string tag, string value)
        => text.Append(tag).Append(value.Length).Append(':').Append(value);

    internal static string RequirementFingerprint(Algorithm root)
    {
        var text = new StringBuilder();
        new RequirementWalker(text).VisitAlgorithm(root);
        return text.ToString();
    }

    // Walk all stored semantic children, including algorithms in output/call/capture expressions.
    // The previous properties-only recursion silently skipped those owners' annotations.
    private sealed class RequirementWalker(StringBuilder text) : AstWalker
    {
        private readonly HashSet<object> _seen = new(ReferenceEqualityComparer.Instance);
        protected override bool VisitsExplicitParameterDeclarations => false;

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (!_seen.Add(algorithm)) return;
            base.VisitAlgorithm(algorithm);
        }

        public override void VisitExpr(Expr expression)
        {
            if (!_seen.Add(expression)) return;
            base.VisitExpr(expression);
        }

        private protected override void VisitCallArguments(OutputBundle arguments)
        {
            if (_seen.Add(arguments)) base.VisitCallArguments(arguments);
        }

        protected override void VisitAliasAlgorithm(Algorithm.Alias algorithm)
        {
            // The shared fingerprint predates aliases and otherwise emits only "Alg?Alias".
            // Encode the alias's stored children through its ordinary user-body view as well.
            text.Append(algorithm.HasRuntimeTarget ? "runtime-alias:" : "static-alias:");
            var body = new Algorithm.User(algorithm.Parent, [], algorithm.Opens, algorithm.Properties, [algorithm.Target]);
            Field(text, "body", FrontEndFingerprint.ComputeParseResult(body, []));
            base.VisitAliasAlgorithm(algorithm);
        }

        protected override void VisitProperty(Property property)
        {
            Field(text, "property", property.Name ?? "");
            text.Append("req[");
            foreach (var name in property.RequiredAncestorParameters) Field(text, "", name);
            text.Append("]cap[");
            foreach (var capture in property.CaptureRequirements ?? [])
            {
                Field(text, "", capture.Name);
                text.Append('@').Append(capture.OwnerDepth).Append(';');
            }
            text.Append(']');
            base.VisitProperty(property);
        }
    }

    // ── child ─────────────────────────────────────────────────────────────────

    public static int RunChild(string[] args)
    {
        // Handshake: the parent assigns the job object before generation starts.
        _ = Console.In.ReadLine();
        if (args.Length >= 4 && args[1] == "census") return RunCensus(args[2], ParseSize(args[3]));
        if (args.Length >= 5 && args[1] == "faithful") return RunFaithful(args[2], args[3], ParseSize(args[4]));
        Console.Error.WriteLine("fe-mem-child faithful ROUTE SHAPE CHARS | fe-mem-child census SHAPE CHARS");
        return 2;
    }

    private static void FullCollect()
    {
        for (var i = 0; i < 3; i++)
        {
            GCSettings.LargeObjectHeapCompactionMode = GCLargeObjectHeapCompactionMode.CompactOnce;
            GC.Collect(2, GCCollectionMode.Forced, blocking: true, compacting: true);
            GC.WaitForPendingFinalizers();
        }
    }

    private static string SourceFacts(string source)
        => $"srcLen={source.Length} utf8Bytes={Encoding.UTF8.GetByteCount(source)} sourceSha256={Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(Encoding.UTF8.GetBytes(source)))}";

    /// <summary>One public operation. Returns the operation's result object (kept alive by the caller).</summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static string OperateInto(string route, string source, System.Runtime.CompilerServices.StrongBox<object?> result, bool requireClean)
    {
        result.Value = Operate(route, source, out var facts, requireClean);
        return facts;
    }
    private static object Operate(string route, string source, out string facts, bool requireClean = false)
    {
        switch (route)
        {
            case "lex":
            {
                var (tokens, diagnostics) = Lexer.Tokenize(source);
                RequireClean(diagnostics, requireClean);
                facts = $"tokens={tokens.Count} diags={diagnostics.Count}";
                return tokens;
            }
            case "parse":
            {
                var result = Parser.Parse(source);
                RequireClean(result.Diagnostics, requireClean);
                facts = $"diags={result.Diagnostics.Count} errors={result.HasErrors}";
                return result;
            }
            case "parse-async":
            {
                var task = Parser.ParseAsync(source);
                var completedSynchronously = task.IsCompleted;
                var result = task.GetAwaiter().GetResult();
                RequireClean(result.Diagnostics, requireClean);
                facts = $"diags={result.Diagnostics.Count} errors={result.HasErrors} syncCompleted={completedSynchronously}";
                return result;
            }
            case "parse-async-dl":
            {
                // The shape is a MODULE the main program loads; the in-memory downloader yields
                // before answering, so module acquisition genuinely suspends. No network.
                var module = source;
                var suspended = false;
                var options = new RunOptions
                {
                    DownloadCode = async (url, _) =>
                    {
                        await Task.Yield();
                        suspended = true;
                        return module;
                    },
                };
                var task = Parser.ParseAsync("public M = load('https://katlang.org/gen/module')\n1", options);
                var completedSynchronously = task.IsCompleted;
                var result = task.GetAwaiter().GetResult();
                RequireClean(result.Diagnostics, requireClean);
                facts = $"diags={result.Diagnostics.Count} errors={result.HasErrors} syncCompleted={completedSynchronously} downloaderSuspended={suspended}";
                return result;
            }
            case var cancel when cancel.StartsWith("parse-cancel-", StringComparison.Ordinal):
            {
                // Cancellation LATENCY (diagnostic): the source-processing token is cancelled
                // after N ms; the time from cancellation to OperationCanceledException is reported.
                var afterMs = int.Parse(cancel["parse-cancel-".Length..], CultureInfo.InvariantCulture);
                using var cts = new CancellationTokenSource();
                long cancelledAt = 0;
                var clock = Stopwatch.StartNew();
                using var timer = new Timer(_ => { cancelledAt = clock.ElapsedTicks; cts.Cancel(); }, null, afterMs, Timeout.Infinite);
                try
                {
                    var result = Parser.Parse(source, new RunOptions { SourceProcessingCancellationToken = cts.Token });
                    RequireClean(result.Diagnostics, requireClean);
                    facts = $"completed-before-cancel totalMs={clock.Elapsed.TotalMilliseconds:F0} diags={result.Diagnostics.Count}";
                    return result;
                }
                catch (OperationCanceledException)
                {
                    var latencyMs = (clock.ElapsedTicks - Interlocked.Read(ref cancelledAt)) * 1000.0 / Stopwatch.Frequency;
                    facts = $"cancelled latencyMs={latencyMs:F0} totalMs={clock.Elapsed.TotalMilliseconds:F0}";
                    return facts;
                }
            }
            case "run":
            {
                var result = KatLangEngine.Run(source);
                RequireSuccess(result, requireClean);
                facts = $"run={Describe(result)}";
                return result;
            }
            case "run-async":
            {
                var task = KatLangEngine.RunAsync(source);
                var completedSynchronously = task.IsCompleted;
                var result = task.GetAwaiter().GetResult();
                RequireSuccess(result, requireClean);
                facts = $"run={Describe(result)} syncCompleted={completedSynchronously}";
                return result;
            }
            default:
                throw new ArgumentException($"unknown route {route}");
        }
    }

    internal static void RequireClean(IReadOnlyList<Diagnostic> diagnostics, bool required)
    {
        if (required && diagnostics.Count != 0)
            throw new InvalidOperationException($"Expected valid probe source; received {diagnostics.Count} diagnostic(s).");
    }

    private static void RequireSuccess(RunResult result, bool required)
    {
        if (required && result is not RunResult.Success)
            throw new InvalidOperationException($"Expected successful probe run; received {result.GetType().Name}.");
    }

    private static string Describe(RunResult result) => result switch
    {
        RunResult.Success s => "success:" + Trunc(s.Value.ToString() ?? "", 24).Replace(' ', '_'),
        _ => result.GetType().Name,
    };

    private static int RunFaithful(string route, string shapeId, int targetChars)
    {
        var shape = Find(shapeId);
        if (shape is null) { Console.Error.WriteLine($"unknown shape {shapeId}"); return 2; }

        // Warm the SAME route on a small instance of the same shape (JIT, static caches).
        for (var i = 0; i < 3; i++) GC.KeepAlive(Operate(route, Generate(shape, 1024), out _));

        var source = Generate(shape, targetChars);
        FullCollect();
        var process = Process.GetCurrentProcess();
        process.Refresh();
        var privateBefore = process.PrivateMemorySize64;
        var heapBefore = GC.GetTotalMemory(forceFullCollection: false);
        var gen2Before = GC.CollectionCount(2);
        var sampler = new HeapSampler();
        var allocBefore = GC.GetTotalAllocatedBytes(precise: true);
        var sw = Stopwatch.StartNew();
        // The result lives in a box filled by a non-inlined call, never in this frame: an
        // unoptimized frame would keep a returned reference in a spilled temporary until the
        // method exits, and the release measurement below would then report the result as leaked.
        var result = new System.Runtime.CompilerServices.StrongBox<object?>();
        var facts = OperateInto(route, source, result, requireClean: shape.Kind != "malformed");
        sw.Stop();
        var allocAfter = GC.GetTotalAllocatedBytes(precise: true);
        var heapPeak = sampler.Stop();
        var gen2 = GC.CollectionCount(2) - gen2Before;
        process.Refresh();
        var peakWs = process.PeakWorkingSet64;
        var peakPrivate = process.PeakPagedMemorySize64;

        FullCollect();
        var retained = GC.GetTotalMemory(false) - heapBefore;
        GC.KeepAlive(result.Value);
        result.Value = null;
        FullCollect();
        var afterRelease = GC.GetTotalMemory(false) - heapBefore;
        if (Environment.GetEnvironmentVariable("FE_MEM_DUMP_AFTER_RELEASE") is { Length: > 0 } releaseDump)
        {
            using var dump = Process.Start(new ProcessStartInfo(Environment.GetEnvironmentVariable("FE_MEM_DUMP_TOOL") ?? "dotnet-dump", $"collect -p {Environment.ProcessId} --type Heap -o \"{releaseDump}\"") { UseShellExecute = false });
            dump?.WaitForExit();
        }
        GC.KeepAlive(source);

        Console.Out.WriteLine(
            $"RESULT {SourceFacts(source)} {facts} allocKb={(allocAfter - allocBefore) / 1024} " +
            (HeapSampler.LiveSampleMs > 0 ? $"liveSampledPeakKb={(sampler.LiveMax - heapBefore) / 1024} " : "") +
            $"heapPeakKb={(heapPeak - heapBefore) / 1024} retainedKb={retained / 1024} afterReleaseKb={afterRelease / 1024} " +
            $"peakWsKb={peakWs / 1024} peakPrivateKb={peakPrivate / 1024} privateBeforeKb={privateBefore / 1024} " +
            $"gen2={gen2} ms={sw.Elapsed.TotalMilliseconds:F1}");
        return 0;
    }

    /// <summary>
    /// Samples the managed heap size (live + not-yet-collected) on a dedicated thread without
    /// allocating, so the main thread's allocation counter and the measured heap stay the operation's.
    /// </summary>
    private sealed class HeapSampler
    {
        private volatile bool _stop;
        public static readonly int LiveSampleMs = int.TryParse(Environment.GetEnvironmentVariable("FE_MEM_LIVE_SAMPLE_MS"), out var ms) ? ms : 0;
        public long LiveMax;
        private long _max;
        private readonly Thread _thread;

        public HeapSampler()
        {
            _max = GC.GetTotalMemory(false);
            if (OperatingSystem.IsWindows()) MainThreadId = GetCurrentThreadId();
            _thread = new Thread(Loop) { IsBackground = true, Priority = ThreadPriority.AboveNormal };
            _thread.Start();
        }

        private void Loop()
        {
            // Diagnostic-only (never set by the parent's measurement runs): dump the heap once the
            // managed heap first exceeds FE_MEM_DUMP_AT_MB, to see what is live near the peak.
            var dumpAt = long.TryParse(Environment.GetEnvironmentVariable("FE_MEM_DUMP_AT_MB"), out var mb) ? mb * 1024 * 1024 : long.MaxValue;
            while (!_stop)
            {
                var v = GC.GetTotalMemory(false);
                if (v > _max) _max = v;
                if (LiveSampleMs == 0 && v > dumpAt) DumpNow(ref dumpAt);
                // Diagnostic-only LIVE-SET sampling (mode B semantics inside a faithful child; never
                // set by default): a forced full blocking collection every FE_MEM_LIVE_SAMPLE_MS
                // measures what is actually reachable during the operation, separating transient
                // live state from uncollected garbage. It perturbs time and GC behavior on purpose.
                if (LiveSampleMs > 0)
                {
                    GC.Collect(2, GCCollectionMode.Forced, blocking: true, compacting: false);
                    var live = GC.GetTotalMemory(false);
                    if (live > LiveMax) LiveMax = live;
                    if (live > dumpAt) DumpNow(ref dumpAt);
                    Thread.Sleep(LiveSampleMs);
                    continue;
                }

                Thread.Sleep(1);
            }
        }

        private static void DumpNow(ref long dumpAt)
        {
            dumpAt = long.MaxValue;
            var path = Environment.GetEnvironmentVariable("FE_MEM_DUMP_PATH") ?? "fe-mem.dmp";
            var tool = Environment.GetEnvironmentVariable("FE_MEM_DUMP_TOOL") ?? "dotnet-dump";
            var psi = new ProcessStartInfo(tool, $"collect -p {Environment.ProcessId} --type Heap -o \"{path}\"") { UseShellExecute = false };
            // Freeze the measured operation where it is, so the dump shows its live state rather
            // than whatever the main thread reached while the dump tool started.
            var thread = OpenThread(0x0002 /* THREAD_SUSPEND_RESUME */, false, MainThreadId);
            if (thread != IntPtr.Zero) SuspendThread(thread);
            try
            {
                using var dump = Process.Start(psi);
                dump?.WaitForExit();
            }
            finally
            {
                if (thread != IntPtr.Zero) { ResumeThread(thread); CloseThreadHandle(thread); }
            }
        }

        public static uint MainThreadId;

        [DllImport("kernel32.dll")] public static extern uint GetCurrentThreadId();
        [DllImport("kernel32.dll")] private static extern IntPtr OpenThread(uint access, bool inherit, uint threadId);
        [DllImport("kernel32.dll")] private static extern uint SuspendThread(IntPtr thread);
        [DllImport("kernel32.dll")] private static extern uint ResumeThread(IntPtr thread);
        [DllImport("kernel32.dll", EntryPoint = "CloseHandle")] private static extern bool CloseThreadHandle(IntPtr handle);

        public long Stop()
        {
            _stop = true;
            _thread.Join();
            return Math.Max(_max, GC.GetTotalMemory(false));
        }
    }

    // ── census (attribution; explicit retention) ──────────────────────────────

    private static long RetainedBytes(Func<object> build, out object kept)
    {
        FullCollect();
        var before = GC.GetTotalMemory(false);
        kept = build();
        FullCollect();
        return GC.GetTotalMemory(false) - before;
    }

    private static int RunCensus(string shapeId, int targetChars)
    {
        var shape = Find(shapeId);
        if (shape is null) { Console.Error.WriteLine($"unknown shape {shapeId}"); return 2; }
        for (var i = 0; i < 3; i++) { GC.KeepAlive(Parser.Parse(Generate(shape, 1024))); GC.KeepAlive(Lexer.Tokenize(Generate(shape, 1024))); }

        var source = Generate(shape, targetChars);
        var sb = new StringBuilder($"RESULT census {SourceFacts(source)}");

        // Stage 1: tokens alone.
        var tokenBytes = RetainedBytes(() => Lexer.Tokenize(source).Tokens, out var tokensObj);
        var tokens = (IReadOnlyList<Token>)tokensObj;
        var kinds = tokens.GroupBy(t => t.Kind).OrderByDescending(g => g.Count()).Take(6).Select(g => $"{g.Key}:{g.Count()}");
        var textTokens = tokens.Where(t => t.StringValue is not null).ToList();
        var distinctText = textTokens.Select(t => t.StringValue!).Distinct(StringComparer.Ordinal).Count();
        var distinctTextObjects = textTokens.Select(t => (object)t.StringValue!).Distinct(ReferenceEqualityComparer.Instance).Count();
        // Tokenize returns a read-only wrapper; its backing list capacity is still a physical
        // cost. Count the reachable Token[] storage, without relying on the wrapper's CLR type.
        var tokenCensus = GraphCensus.Of(tokens);
        var listCapacity = tokenCensus.Nodes.OfType<Token[]>().Sum(array => array.Length);
        sb.Append($" tokens={tokens.Count} tokenCapacity={listCapacity} tokenRetainedKb={tokenBytes / 1024} " +
                  $"bytesPerToken={(tokens.Count == 0 ? 0 : tokenBytes / tokens.Count)} textTokens={textTokens.Count} " +
                  $"distinctText={distinctText} distinctTextObjects={distinctTextObjects} kinds={string.Join(',', kinds)}");
        textTokens = null;
        tokenCensus = null!;
        tokens = null;
        tokensObj = null!;

        // Stage 2: raw syntax alone.
        var rawBytes = RetainedBytes(() => Parser.ParseSyntax(source), out var rawObj);
        var raw = (SyntaxParseResult)rawObj;
        RequireClean(raw.Diagnostics, shape.Kind != "malformed");
        var rawCensus = GraphCensus.Of(raw.Root);
        sb.Append($" rawRetainedKb={rawBytes / 1024} rawDiags={raw.Diagnostics.Count} rawObjects={rawCensus.Distinct} rawAst={rawCensus.AstNodes} " +
                  $"rawRefs={rawCensus.Edges} rawArraySlots={rawCensus.ArraySlots} rawStringChars={rawCensus.StringChars} rawTop={rawCensus.Top(10)}");

        // Stage 3: elaborated result alone (raw released).
        rawCensus = null!;
        raw = null;
        rawObj = null!;
        var elaboratedBytes = RetainedBytes(() => Parser.Parse(source), out var parsedObj);
        var parsed = (ParseResult)parsedObj;
        RequireClean(parsed.Diagnostics, shape.Kind != "malformed");
        var elaborated = GraphCensus.Of(parsed.Root);
        sb.Append($" parseRetainedKb={elaboratedBytes / 1024} parseDiags={parsed.Diagnostics.Count} errors={parsed.HasErrors} " +
                  $"elabObjects={elaborated.Distinct} elabAst={elaborated.AstNodes} elabRefs={elaborated.Edges} elabArraySlots={elaborated.ArraySlots} " +
                  $"elabStringChars={elaborated.StringChars} elabTop={elaborated.Top(16)}");
        elaborated = null!;

        // Physical sharing between a fresh raw tree and the elaborated tree built from IT.
        var raw2 = Parser.ParseSyntax(source);
        var rawSet = GraphCensus.Of(raw2.Root).Nodes;
        var syntaxBag = raw2.Diagnostics;
        var elaboratedFromRaw = ElaborateLikePipeline(raw2.Root, syntaxBag);
        var elaboratedNodes = GraphCensus.Of(elaboratedFromRaw).Nodes;
        var shared = elaboratedNodes.Count(rawSet.Contains);
        sb.Append($" elabNodesSharedWithRaw={shared}");
        rawSet = null!;
        elaboratedNodes = null!;
        elaboratedFromRaw = null!;
        raw2 = null!;

        // Stage 4: per-pass allocation (each pass's allocated bytes, process-wide counter).
        sb.Append(' ').Append(PassAllocations(source));

        // Stage 5: sampled allocation-by-type for one Parser.Parse.
        parsed = null!;
        parsedObj = null!;
        FullCollect();
        using (var listener = new AllocationListener())
        {
            GC.KeepAlive(Parser.Parse(source));
            Thread.Sleep(200);
            sb.Append(" allocTop=").Append(listener.Top(12));
        }

        Console.Out.WriteLine(sb.ToString());
        return 0;
    }

    private static Algorithm ElaborateLikePipeline(Algorithm root, DiagnosticBag bag)
    {
        var modules = new ModuleUnits();
        var (detected, _) = ParameterDetector.DetectPrevalidated(root, null, diagnostics: bag, modules: modules);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, null, bag, null, modules);
        return PropertyExposureResolver.Resolve(resolved, null, null, modules);
    }

    private static string PassAllocations(string source)
    {
        FullCollect();
        long Now() => GC.GetTotalAllocatedBytes(precise: true);
        var t0 = Now();
        var (tokens, _) = Lexer.Tokenize(source);
        var t1 = Now();
        GC.KeepAlive(tokens);
        tokens = null;
        var syntax = Parser.ParseSyntax(source);
        var t2 = Now();
        var bag = syntax.Diagnostics;
        var modules = new ModuleUnits();
        var (detected, _) = ParameterDetector.DetectPrevalidated(syntax.Root, null, diagnostics: bag, modules: modules);
        var t3 = Now();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, null, bag, null, modules);
        var t4 = Now();
        new ParameterPropertyCollisionValidator(bag, programRoot: resolved).VisitAlgorithm(resolved);
        OpenProviderValidator.Validate(resolved, bag, (HostOperations?)null);
        InferredParameterOutputValidator.ValidateProgram(resolved, bag);
        var t5 = Now();
        var exposed = PropertyExposureResolver.Resolve(resolved, null, null, modules);
        var t6 = Now();
        GC.KeepAlive(exposed);
        return $"allocKb[lex={(t1 - t0) / 1024},syntaxInclLex={(t2 - t1) / 1024},detect={(t3 - t2) / 1024}," +
               $"resolve={(t4 - t3) / 1024},validate={(t5 - t4) / 1024},exposure={(t6 - t5) / 1024}]";
    }

    /// <summary>
    /// Distinct-reference census of the object graph reachable from a root: every KatLang object,
    /// array, and generic collection is descended through its instance FIELDS (so annotation
    /// backings, name sets, and collection storage are counted, not just AST children); other
    /// framework objects (strings, delegates, reflection) are counted as leaves. Physical objects,
    /// not logical occurrences: a shared subtree counts once.
    /// </summary>
    internal sealed class GraphCensus
    {
        public int Distinct => Nodes.Count;
        public long Edges;
        public long ArraySlots;
        public int AstNodes;
        public long StringChars;
        public HashSet<object> Nodes { get; } = new(ReferenceEqualityComparer.Instance);
        public Dictionary<string, int> ByType { get; } = new();

        public string Top(int n) => string.Join(',', ByType.OrderByDescending(kv => kv.Value).Take(n).Select(kv => $"{kv.Key}:{kv.Value}"));

        public static GraphCensus Of(object root)
        {
            var census = new GraphCensus();
            var stack = new Stack<object>();
            stack.Push(root);
            while (stack.Count > 0)
            {
                var node = stack.Pop();
                if (!census.Nodes.Add(node)) continue;
                var type = node.GetType();
                var name = TypeName(type);
                census.ByType[name] = census.ByType.GetValueOrDefault(name) + 1;
                if (node is Algorithm or Property or Expr or CondBranch) census.AstNodes++;
                if (node is string s) { census.StringChars += s.Length; continue; }
                if (!Descend(type)) continue;
                if (node is Array array)
                {
                    census.ArraySlots += array.LongLength;
                    foreach (var item in array)
                        References(item);
                    continue;
                }

                Fields(node, type);
            }

            return census;

            // Structs carry inline references too (Dictionary entries, ImmutableArray, ...).
            // Walk their fields without counting reflection's temporary boxes as heap owners.
            void References(object? value)
            {
                if (value is null) return;
                var type = value.GetType();
                if (type.IsPrimitive || type.IsEnum || type.IsPointer) return;
                if (type.IsValueType) { Fields(value, type); return; }
                census.Edges++;
                stack.Push(value);
            }

            void Fields(object node, Type type)
            {
                foreach (var field in FieldsOf(type)) References(field.GetValue(node));
            }
        }

        private static string TypeName(Type t)
        {
            var n = t.IsGenericType ? t.Name + "<" + string.Join("|", t.GetGenericArguments().Select(a => a.Name)) + ">" : t.Name;
            return t.DeclaringType is { } d && t.Namespace == "KatLang" ? d.Name + "." + n : n;
        }

        private static bool Descend(Type t)
        {
            if (t == typeof(string) || typeof(Delegate).IsAssignableFrom(t) || typeof(MemberInfo).IsAssignableFrom(t)) return false;
            if (t.IsArray) return true;
            var ns = t.Namespace ?? "";
            return ns.StartsWith("KatLang", StringComparison.Ordinal) || ns.StartsWith("System.Collections", StringComparison.Ordinal);
        }

        private static readonly Dictionary<Type, FieldInfo[]> Cache = new();

        // Include nonprimitive structs: their inline fields can keep heap objects reachable.
        private static FieldInfo[] FieldsOf(Type type)
        {
            if (Cache.TryGetValue(type, out var cached)) return cached;
            var fields = new List<FieldInfo>();
            for (var t = type; t is not null && t != typeof(object); t = t.BaseType)
                fields.AddRange(t.GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly)
                    .Where(f => !f.FieldType.IsPrimitive && !f.FieldType.IsEnum && !f.FieldType.IsPointer));
            var result = fields.ToArray();
            Cache[type] = result;
            return result;
        }
    }

    /// <summary>Sampled allocation-by-type profile (runtime GCAllocationTick, ~100 KB granularity).</summary>
    private sealed class AllocationListener : EventListener
    {
        private readonly Dictionary<string, long> _bytes = new();
        private readonly object _gate = new();

        protected override void OnEventSourceCreated(EventSource source)
        {
            if (source.Name == "Microsoft-Windows-DotNETRuntime")
                EnableEvents(source, EventLevel.Verbose, (EventKeywords)0x1);
        }

        protected override void OnEventWritten(EventWrittenEventArgs e)
        {
            if (e.EventName is null || !e.EventName.StartsWith("GCAllocationTick", StringComparison.Ordinal) || e.Payload is null) return;
            var typeIndex = e.PayloadNames?.IndexOf("TypeName") ?? -1;
            var amountIndex = e.PayloadNames?.IndexOf("AllocationAmount64") ?? -1;
            if (typeIndex < 0) return;
            var type = e.Payload[typeIndex] as string ?? "?";
            var amount = amountIndex >= 0 ? Convert.ToInt64(e.Payload[amountIndex], CultureInfo.InvariantCulture) : 100_000;
            lock (_gate) _bytes[type] = _bytes.GetValueOrDefault(type) + amount;
        }

        public string Top(int n)
        {
            lock (_gate)
            {
                var total = _bytes.Values.Sum();
                return $"totalSampledKb:{total / 1024};" + string.Join(';', _bytes.OrderByDescending(kv => kv.Value).Take(n)
                    .Select(kv => $"{ShortType(kv.Key)}:{kv.Value / 1024}"));
            }
        }

        private static string ShortType(string name)
        {
            var s = name.Replace("KatLang.", "").Replace("System.Collections.Generic.", "").Replace("System.", "");
            return s.Length > 70 ? s[..70] : s;
        }
    }

    // ── Windows job object: commit limit + exact peak ─────────────────────────

    private sealed class JobLimit : IDisposable
    {
        private readonly IntPtr _handle;

        private JobLimit(IntPtr handle) => _handle = handle;

        public static JobLimit? TryCreate(Process process, long limitBytes)
        {
            var handle = CreateJobObject(IntPtr.Zero, null);
            if (handle == IntPtr.Zero) return null;
            var info = new JOBOBJECT_EXTENDED_LIMIT_INFORMATION
            {
                BasicLimitInformation = new JOBOBJECT_BASIC_LIMIT_INFORMATION
                {
                    LimitFlags = JOB_OBJECT_LIMIT_PROCESS_MEMORY | JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE,
                },
                ProcessMemoryLimit = (UIntPtr)(ulong)limitBytes,
            };
            var size = Marshal.SizeOf<JOBOBJECT_EXTENDED_LIMIT_INFORMATION>();
            var ptr = Marshal.AllocHGlobal(size);
            try
            {
                Marshal.StructureToPtr(info, ptr, false);
                if (!SetInformationJobObject(handle, 9, ptr, (uint)size) || !AssignProcessToJobObject(handle, process.Handle))
                {
                    CloseHandle(handle);
                    return null;
                }
            }
            finally { Marshal.FreeHGlobal(ptr); }

            return new JobLimit(handle);
        }

        public long PeakProcessMemoryUsed()
        {
            var size = Marshal.SizeOf<JOBOBJECT_EXTENDED_LIMIT_INFORMATION>();
            var ptr = Marshal.AllocHGlobal(size);
            try
            {
                if (!QueryInformationJobObject(_handle, 9, ptr, (uint)size, out _)) return -1;
                var info = Marshal.PtrToStructure<JOBOBJECT_EXTENDED_LIMIT_INFORMATION>(ptr);
                return (long)(ulong)info.PeakProcessMemoryUsed;
            }
            finally { Marshal.FreeHGlobal(ptr); }
        }

        public void Dispose() => CloseHandle(_handle);

        private const uint JOB_OBJECT_LIMIT_PROCESS_MEMORY = 0x100;
        private const uint JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x2000;

        [StructLayout(LayoutKind.Sequential)]
        private struct JOBOBJECT_BASIC_LIMIT_INFORMATION
        {
            public long PerProcessUserTimeLimit;
            public long PerJobUserTimeLimit;
            public uint LimitFlags;
            public UIntPtr MinimumWorkingSetSize;
            public UIntPtr MaximumWorkingSetSize;
            public uint ActiveProcessLimit;
            public UIntPtr Affinity;
            public uint PriorityClass;
            public uint SchedulingClass;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct IO_COUNTERS
        {
            public ulong ReadOperationCount, WriteOperationCount, OtherOperationCount, ReadTransferCount, WriteTransferCount, OtherTransferCount;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct JOBOBJECT_EXTENDED_LIMIT_INFORMATION
        {
            public JOBOBJECT_BASIC_LIMIT_INFORMATION BasicLimitInformation;
            public IO_COUNTERS IoInfo;
            public UIntPtr ProcessMemoryLimit;
            public UIntPtr JobMemoryLimit;
            public UIntPtr PeakProcessMemoryUsed;
            public UIntPtr PeakJobMemoryUsed;
        }

        [DllImport("kernel32.dll", CharSet = CharSet.Unicode, SetLastError = true)]
        private static extern IntPtr CreateJobObject(IntPtr attributes, string? name);

        [DllImport("kernel32.dll", SetLastError = true)]
        private static extern bool SetInformationJobObject(IntPtr job, int infoClass, IntPtr info, uint length);

        [DllImport("kernel32.dll", SetLastError = true)]
        private static extern bool QueryInformationJobObject(IntPtr job, int infoClass, IntPtr info, uint length, out uint returned);

        [DllImport("kernel32.dll", SetLastError = true)]
        private static extern bool AssignProcessToJobObject(IntPtr job, IntPtr process);

        [DllImport("kernel32.dll", SetLastError = true)]
        private static extern bool CloseHandle(IntPtr handle);
    }
}
