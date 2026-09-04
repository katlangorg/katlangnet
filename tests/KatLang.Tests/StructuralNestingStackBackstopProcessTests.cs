using System.Diagnostics;
using System.Numerics;
using System.Text;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Process-isolated regression for audit finding K2-R1 (September 2026): STATIC brace/group
/// nesting MULTIPLIED by DYNAMIC recursion overflowed the process stack on the synchronous
/// output-row path. Structural nesting charges no dynamic depth, so each recursion level
/// crossed exactly one charged, probing chokepoint (<c>EvaluationBudget.TryEnterInvocation</c>)
/// and then descended its whole written nesting UNCHARGED; once that descent exceeded the
/// probe's fixed reserve, the next chokepoint noticed exhaustion with no stack left to build
/// the structured error, and the 90-byte legal program in <see cref="AuditMinimalRepro"/>
/// killed the embedding process with an uncatchable <see cref="StackOverflowException"/>
/// (exit 127 "Stack overflow." or a SIGSEGV) on the documented minimum 1 MiB thread and on
/// the shipped CLI's own main thread. The async twins already probed the host stack once per
/// row loop; the synchronous funnels (<c>EvalOutputRowsPreparedCore</c> for algorithm and
/// capture bodies, <c>EvalExplicitSequenceValueRowSlots</c> for written groups inside list
/// literals and patterned arguments) now mirror them.
///
/// <para>An in-process test cannot observe a process death safely, so a child process runs
/// the shapes on dedicated 1 MiB and 384 KiB threads, asserts structured outcomes, writes a
/// success marker, and exits normally (the subprocess convention of
/// <see cref="EvaluationLimitsProcessTests"/>). The crash frontier is sharp, machine-dependent
/// and NON-monotonic in the nesting width — before the fix a Release 1 MiB thread crashed the
/// brace family at widths 30, 40, 45, 55, 60, ... but returned the structured error at 35, 50
/// and 65, and Debug crashed a different set — so the child sweeps a family of widths instead
/// of pinning one point. Before the fix, every configuration measured had several crashing
/// members in each (kind, stack size) family, so the pre-fix child died in every
/// configuration.</para>
/// </summary>
public class StructuralNestingStackBackstopProcessTests
{
    private const string ProbeChildEnvironment = "KATLANG_STRUCTURAL_NESTING_STACK_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_STRUCTURAL_NESTING_STACK_PROBE_MARKER_FILE";
    private const string ProbeSuccessMarker = "katlang-structural-nesting-stack-backstop-ok";

    /// <summary>
    /// The audit's minimal reproduction (<c>docs/audit/repro-K2-R1.kat</c>), byte for byte:
    /// thirty nested zero-declaration brace blocks per recursion level, nine levels. Before
    /// the fix it terminated the process on a 1 MiB thread (Release) while the same program
    /// through the async twin path returned <see cref="EvalError.EvaluationStackExhausted"/>.
    /// </summary>
    internal const string AuditMinimalRepro =
        "F(0) = 0\n"
        + "F(n) = {{{{{{{{{{{{{{{{{{{{{{{{{{{{{{F(n - 1)}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}\n"
        + "F(9)\n";

    /// <summary>The four surface syntaxes that reach the two row-loop funnels.</summary>
    internal static readonly string[] Kinds = ["brace", "capture", "list-group", "list-alternation"];

    /// <summary>
    /// Widths swept by the child. The parser admits 95 group/block levels and the pre-fix
    /// crash frontier lay between 25 and 90 in every measured configuration; the
    /// alternating shape composes two mechanisms, so the structural preflight admits at most
    /// 25 alternation pairs (30 is rejected with <c>AstDepthLimitExceeded</c>), and with only
    /// the algorithm/capture funnel guarded, 25 pairs still killed the process in every
    /// measured configuration — the explicit-slot funnel's guard is what closes that route.
    /// </summary>
    internal static int[] SweepWidths(string kind)
        => kind == "list-alternation"
            ? [10, 15, 20, 25]
            : [20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90];

    /// <summary>
    /// <c>F(0) = 0</c>, a clause <c>F(n)</c> whose body nests the recursive call
    /// <c>F(n - 1)</c> <paramref name="width"/> levels deep in the requested syntax, and the
    /// output row <c>F(depth)</c>. Every recursion level therefore descends
    /// <paramref name="width"/> uncharged structural levels between two invocation chokepoints.
    /// </summary>
    internal static string Program(string kind, int width, int depth)
    {
        var body = new StringBuilder();
        switch (kind)
        {
            case "brace":
                // Zero-declaration brace blocks: Expr.AlgorithmExpr rows through
                // EvalOutputRowsPreparedCore (after pushing each block's scope).
                body.Append('{', width).Append("F(n - 1)").Append('}', width);
                break;

            case "capture":
                // Parenthesized groups: Expr.Capture rows through the SAME funnel,
                // without a scope push.
                AppendGroup(body, width);
                break;

            case "list-group":
                // A written group as a list-literal element: the element and every
                // nested group below it recurse through EvalExplicitSequenceValueRowSlots
                // (the explicit written-slot funnel), never through EvalOutputRowsPreparedCore.
                body.Append('[');
                AppendGroup(body, width);
                body.Append("]:0");
                break;

            case "list-alternation":
                // Alternating list literal / written group, `[([(F(n - 1), 1)], 1)]`: every
                // pair re-enters the iterative expression-spine machine from the explicit
                // written-slot funnel, the most frames per level any route through that
                // funnel can accumulate between two chokepoints.
                for (var i = 0; i < width; i++)
                    body.Append("[(");
                body.Append("F(n - 1)");
                for (var i = 0; i < width; i++)
                    body.Append(", 1)]");
                break;

            default:
                throw new ArgumentOutOfRangeException(nameof(kind), kind, "unknown shape kind");
        }

        return $"F(0) = 0\nF(n) = {body}\nF({depth})\n";

        static void AppendGroup(StringBuilder sb, int width)
        {
            sb.Append('(', width).Append("F(n - 1)");
            for (var i = 0; i < width; i++)
                sb.Append(", 1)");
        }
    }

    /// <summary>
    /// Host atoms of a COMPLETING program of the family: <c>0</c> from the base clause, then
    /// one <c>1</c> per written <c>, 1</c> slot (<c>width</c> per recursion level).
    /// </summary>
    internal static Decimal128[] ExpectedAtoms(string kind, int width, int depth)
        => kind == "brace"
            ? [0m]
            : [0m, .. Enumerable.Repeat<Decimal128>(1m, width * depth)];

    [Fact]
    public void AuditMinimalRepro_IsTheWidthThirtyDepthNineBraceProgram()
    {
        // Ties the generator to the audit's exact 90-byte reproduction file.
        Assert.Equal(AuditMinimalRepro, Program("brace", 30, 9));
        Assert.Equal(90, Encoding.UTF8.GetByteCount(AuditMinimalRepro));
        Assert.False(Parser.Parse(AuditMinimalRepro).HasErrors);
    }

    [Fact]
    public async Task StaticNestingTimesRecursion_IsStructurallyBounded_InSubprocess()
        => await RunProbeChild("StaticNestingTimesRecursion_ProbeChild");

    /// <summary>
    /// The child. Parsing and elaboration happen on the child's ordinary thread first: the
    /// front end is calibrated for the documented 1 MiB minimum only, and the 384 KiB thread
    /// pins the EVALUATOR (the K2-R1 subject) exactly like the iterative-spine pin in
    /// <see cref="AstStructuralDepthProcessTests"/>. The 1 MiB thread additionally runs the
    /// complete public engine path, front end included.
    /// </summary>
    [Fact]
    public void StaticNestingTimesRecursion_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // Parse and elaborate on a dedicated 1 MiB thread — the documented minimum the front
        // end is calibrated for — never on whatever stack the test host gives its worker
        // threads (the widest members overflow the PARSER on a smaller test-host thread,
        // which is a different, out-of-scope regime).
        Expr auditAst = null!;
        List<(string Kind, int Width, int Depth, string Source, Expr Ast)> sweep = null!;
        List<(string Kind, int Width, Expr Ast)> widestAtDepth60 = null!;
        List<(string Kind, Expr Ast)> smallControls = null!;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
        {
            auditAst = Ast(AuditMinimalRepro);
            sweep = (
                from kind in Kinds
                from depth in new[] { 9, 20 }
                from width in SweepWidths(kind)
                select (Kind: kind, Width: width, Depth: depth, Source: Program(kind, width, depth)))
                .Select(static shape => (shape.Kind, shape.Width, shape.Depth, shape.Source, Ast: Ast(shape.Source)))
                .ToList();
            widestAtDepth60 = Kinds
                .Select(static kind => (Kind: kind, Width: SweepWidths(kind).Max()))
                .Select(static shape => (shape.Kind, shape.Width, Ast: Ast(Program(shape.Kind, shape.Width, 60))))
                .ToList();
            smallControls = Kinds
                .Select(static kind => (Kind: kind, Ast: Ast(Program(kind, 3, 3))))
                .ToList();
        });

        // ── 1 MiB: the documented minimum supported environment ─────────────────
        AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
        {
            // The audit's exact reproduction, through every entry point it was proven on:
            // the public engine (front end + evaluation on this thread), the direct
            // evaluator, the generic strategies (a configured step budget), and the twin.
            // On Windows — the audit's measured environment, both build configurations —
            // the program needs more than the whole thread, so the ONLY correct outcome is
            // the structured stack error. Other platforms' frame sizes are not calibrated
            // here: a smaller-framed runtime may legitimately complete it, which is equally
            // a non-crash outcome; it must never be a depth or step verdict.
            var strict = OperatingSystem.IsWindows();
            AssertEngine(AuditMinimalRepro, [0m], strictStackError: strict);
            AssertDirect(auditAst, [0m], strictStackError: strict);
            AssertDirect(auditAst, [0m], strictStackError: strict, new EvaluationLimits { MaxSteps = 1_000_000 });
            AssertTwin(auditAst, [0m], strictStackError: strict);

            // Shapes that cannot fit any 1 MiB stack (thousands of frames per chain): the
            // backstop MUST fire, identically on both families, through both entry points.
            foreach (var kind in new[] { "brace", "capture" })
            {
                var source = Program(kind, 90, 20);
                var ast = Ast(source);
                AssertEngine(source, ExpectedAtoms(kind, 90, 20), strictStackError: true);
                AssertDirect(ast, ExpectedAtoms(kind, 90, 20), strictStackError: true);
                AssertTwin(ast, ExpectedAtoms(kind, 90, 20), strictStackError: true);
            }

            // The whole family: a structured outcome for every member — never a crash
            // (a crash kills this process before the marker is written) and never the
            // deterministic depth or step verdict.
            var stackErrors = 0;
            foreach (var shape in sweep)
            {
                if (AssertEngine(shape.Source, ExpectedAtoms(shape.Kind, shape.Width, shape.Depth), strictStackError: false))
                    stackErrors++;
            }

            Assert.True(stackErrors > 0, "The backstop never fired on the 1 MiB thread; the family no longer exercises it.");

            // Safe controls: ordinary nesting keeps completing with the right value.
            foreach (var kind in Kinds)
            {
                AssertEngine(Program(kind, 5, 9), ExpectedAtoms(kind, 5, 9), strictStackError: false, mustComplete: true);
                AssertDirect(Ast(Program(kind, 5, 9)), ExpectedAtoms(kind, 5, 9), strictStackError: false, mustComplete: true);
            }
        });

        // ── 384 KiB: a hostile stack far below the supported minimum ───────────────
        // Evaluator only, on pre-elaborated ASTs. A guard placed one frame too late,
        // or a route around it, overflows this thread long before the 1 MiB one.
        AstStructuralDepthProcessTests.RunOnThreadWithStack(393_216, () =>
        {
            // The exact reproduction needs roughly a whole 1 MiB thread, so on 384 KiB the
            // structured stack error is the only correct outcome on every platform.
            AssertDirect(auditAst, [0m], strictStackError: true);
            AssertDirect(auditAst, [0m], strictStackError: true, new EvaluationLimits { MaxSteps = 1_000_000 });
            AssertTwin(auditAst, [0m], strictStackError: true);

            // The widest preflight-admitted member of every kind at recursion depth 60
            // (thousands of frames per chain): the backstop must fire on both families.
            foreach (var (kind, width, ast) in widestAtDepth60)
            {
                AssertDirect(ast, ExpectedAtoms(kind, width, 60), strictStackError: true);
                AssertTwin(ast, ExpectedAtoms(kind, width, 60), strictStackError: true);
            }

            foreach (var shape in sweep)
                AssertDirect(shape.Ast, ExpectedAtoms(shape.Kind, shape.Width, shape.Depth), strictStackError: false);

            foreach (var (kind, ast) in smallControls)
                AssertDirect(ast, ExpectedAtoms(kind, 3, 3), strictStackError: false, mustComplete: true);
        });

        WriteProbeMarker();
    }

    private static Expr Ast(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    /// <summary>
    /// Runs the public engine path and classifies the outcome: a completing run must produce
    /// <paramref name="expectedAtoms"/>; a failing run must be exactly ONE structured
    /// <see cref="KatLangErrorCode.EvaluationStackExhausted"/> error carrying a source
    /// position. Returns whether the backstop fired.
    /// </summary>
    private static bool AssertEngine(
        string source,
        Decimal128[] expectedAtoms,
        bool strictStackError,
        bool mustComplete = false)
    {
        var result = KatLangEngine.Run(source);
        switch (result)
        {
            case RunResult.Success success:
                Assert.False(strictStackError, $"expected the structured stack error but the program completed:\n{source}");
                Assert.Equal(expectedAtoms, success.Atoms);
                return false;

            case RunResult.EvalFailure failure:
                Assert.False(mustComplete, $"expected completion but got {failure.Errors[0].Message}:\n{source}");
                var error = Assert.Single(failure.Errors);
                Assert.True(
                    error.Code == KatLangErrorCode.EvaluationStackExhausted,
                    $"expected EvaluationStackExhausted, got {error.Code}: {error.Message}\n{source}");
                Assert.True(error.IsResourceLimit);
                Assert.IsType<EvalError.EvaluationStackExhausted>(error.Source);
                Assert.NotNull(error.StartLine);
                return true;

            default:
                Assert.Fail($"unexpected run result {result.GetType().Name}:\n{source}");
                return false;
        }
    }

    private static bool AssertDirect(
        Expr ast,
        Decimal128[] expectedAtoms,
        bool strictStackError,
        EvaluationLimits? limits = null,
        bool mustComplete = false)
    {
        var flat = Evaluator.RunFlat(ast, limits);
        if (flat.IsOk)
        {
            Assert.False(strictStackError, "expected the structured stack error but the program completed");
            Assert.Equal(expectedAtoms, flat.Value);
            return false;
        }

        Assert.False(mustComplete, $"expected completion but got {flat.Error}");
        Assert.True(
            flat.Error is EvalError.EvaluationStackExhausted,
            $"expected EvaluationStackExhausted, got {flat.Error}");
        Assert.True(flat.Error.IsResourceLimit);
        Assert.NotNull(flat.Error.Span);
        return true;
    }

    /// <summary>
    /// The async twin family on the SAME thread (pass-through async cache: the twin path
    /// completes synchronously, so the whole spine consumed this thread's stack). The twin's
    /// larger frames may stop a chain earlier than the synchronous family, never later than
    /// a structured outcome.
    /// </summary>
    private static bool AssertTwin(Expr ast, Decimal128[] expectedAtoms, bool strictStackError)
    {
        var pending = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache());
        Assert.True(pending.IsCompleted, "the pass-through twin path must complete synchronously");
        var result = pending.GetAwaiter().GetResult();
        if (result.IsOk)
        {
            Assert.False(strictStackError, "expected the structured stack error but the twin path completed");
            Assert.True(result.Value.Value.TryToHostAtoms(int.MaxValue, out var atoms));
            Assert.Equal(expectedAtoms, atoms);
            return false;
        }

        Assert.Equal("evaluationStackExhausted", SemanticExplorerHarness.ErrorCategory(result.Error));
        return true;
    }

    private static async Task RunProbeChild(string childTestName)
    {
        var assemblyPath = typeof(StructuralNestingStackBackstopProcessTests).Assembly.Location;
        var testName = typeof(StructuralNestingStackBackstopProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(
            Path.GetTempPath(),
            $"katlang-structural-nesting-stack-probe-{Guid.NewGuid():N}.txt");

        var startInfo = new ProcessStartInfo("dotnet")
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true,
        };
        startInfo.ArgumentList.Add("vstest");
        startInfo.ArgumentList.Add(assemblyPath);
        startInfo.ArgumentList.Add("--Tests:" + testName);
        startInfo.Environment[ProbeChildEnvironment] = "1";
        startInfo.Environment[ProbeMarkerFileEnvironment] = markerFile;
        startInfo.Environment["DOTNET_NOLOGO"] = "1";

        try
        {
            using var process = new Process { StartInfo = startInfo };
            process.Start();
            var stdoutTask = process.StandardOutput.ReadToEndAsync();
            var stderrTask = process.StandardError.ReadToEndAsync();

            var exited = true;
            using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(120));
            try
            {
                await process.WaitForExitAsync(timeout.Token);
            }
            catch (OperationCanceledException)
            {
                exited = false;
                try { process.Kill(entireProcessTree: true); }
                catch { /* process already exited */ }
                await process.WaitForExitAsync();
            }

            var stdout = await stdoutTask;
            var stderr = await stderrTask;
            var combined = stdout + Environment.NewLine + stderr;

            Assert.True(exited, $"Probe subprocess '{childTestName}' did not exit within 120 seconds."
                + Environment.NewLine + combined);
            Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
            Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
            Assert.True(
                process.ExitCode == 0,
                $"Probe subprocess '{childTestName}' exited with {process.ExitCode}.{Environment.NewLine}{combined}");
            Assert.True(
                File.Exists(markerFile),
                $"Probe child '{childTestName}' did not write its success marker.{Environment.NewLine}{combined}");
            Assert.Equal(ProbeSuccessMarker, (await File.ReadAllTextAsync(markerFile)).Trim());
        }
        finally
        {
            try { File.Delete(markerFile); }
            catch { /* best-effort cleanup */ }
        }
    }

    private static void WriteProbeMarker()
    {
        var markerFile = Environment.GetEnvironmentVariable(ProbeMarkerFileEnvironment);
        Assert.False(string.IsNullOrWhiteSpace(markerFile));
        File.WriteAllText(markerFile!, ProbeSuccessMarker);
    }
}
