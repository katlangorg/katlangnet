using System.Collections.Immutable;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// OPEN TARGETS OF A DEFERRED UNIT (constitution PV-11 and MOD-10). Every written open target must resolve,
/// whatever its head, and a load-bearing clause branch is one deferred compilation unit, elaborated and
/// validated as a whole when it is selected, open targets included. So a materialization must report
/// exactly what the same text reports at parse when nothing is deferred.
///
/// <para>It did not for a path headed by an INLINE BLOCK. The chain a unit is validated under is the one
/// recorded at its branch, whose root level carries the EAGER program's completed facts; those hold the
/// block of the unit's placeholder (the same declaration, with no body). The description of an unresolved
/// target read the block there, found it unavailable and stayed silent: <c>open { public X = 1 }.Nope</c>
/// was dropped, <c>X</c> became an inferred parameter and the branch ran. A block head is now read from
/// the facts that decided its resolution, the unit's own
/// (<c>ElaboratedScopeLookup.OpenBlockHeadFacts</c> / <c>OpenBlockHeadLevel</c>), and open-provider
/// validation enters an inline open target at the same level, so the open list of a block that is itself
/// an open target is validated too.</para>
///
/// <para>One position needed more: a block written under a clause family NESTED in the unit. The module
/// loader keeps a load-free clause branch by reference, so below such a branch the loaded body is the very
/// object graph the eager operation admitted below the placeholder, and a block there, keyed at the
/// prelude, has ONE static key in the eager publication and in the unit. The eager publication holds the
/// placeholder's entry for that key, with no body, and the unit used to keep it instead of building its
/// own. A UNIT NOW COMPLETES THE FACTS OF EVERY CONTEXT IT PUBLISHED ITSELF
/// (<c>StaticStructureOperation.CompleteLookups</c>): the rows named "nested family" below, the provider
/// verdicts and valid targets below a nested branch, and the facts read directly in the last section.</para>
///
/// <para><b>The oracle is a twin in which nothing is deferred.</b> The PLAIN twin is the same text with
/// the load removed (the construction of <see cref="DeferredProvisionalParitySweepTests"/>): the holder
/// <c>H = load('…/unused.kat')</c> becomes <c>H = 0</c>, and the minimal program's <c>open '…'</c>
/// directive is dropped. Where the load cannot be removed (an inline <c>load('url')</c> head, a module
/// holder, a target written in module text) the twin makes the family ONE clause instead
/// (<c>F(0) = 0</c> becomes <c>F0 = 0</c>), which is elaborated eagerly. Either way every other token keeps
/// its position, so the twin's diagnostic is compared with the materialization's by code, message AND
/// span.</para>
///
/// <para>Every program runs through <see cref="KatLangEngine.RunAsync"/> with an in-memory downloader
/// that counts its calls, <c>AllowedHosts = ["modules.example"]</c>; every deferred source is checked for
/// a clean parse first, and the materialization's own diagnostic list is read through
/// <see cref="Evaluator.RunFlatAsync(Expr, EvaluationLimits?, CancellationToken)"/> over the parsed tree.</para>
/// </summary>
public class DeferredOpenTargetValidationTests
{
    private const string Host = "modules.example";

    private static string Url(string name) => $"https://{Host}/{name}.kat";

    private static readonly Dictionary<string, string> Library = new(StringComparer.Ordinal)
    {
        // Supplies no name any program reads.
        ["unused"] = "public ZzUnused = 0\n",
        // A public and a private member, for module heads.
        ["lib"] = "public Sub = { public X = 1 }\nPriv = { public X = 2 }\n",
        // An unresolvable target in the module's own open list, and in a nested body of the module.
        ["badroot"] = "open { public X = 1 }.Nope\npublic Q = 1\n",
        ["badnested"] = "public Q = { open { public X = 1 }.Nope\n  7 }\n",
    };

    private static readonly string LoadUnused = "load('" + Url("unused") + "')";
    private static readonly string OpenUnused = "open '" + Url("unused") + "'";
    private static readonly string LoadLib = "load('" + Url("lib") + "')";

    /// <summary>The in-memory host of one run: download counts per module.</summary>
    private sealed class RunHost
    {
        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int this[string module] => Fetches.GetValueOrDefault(Url(module));

        public int TotalFetches => Fetches.Values.Sum();

        public RunOptions Options => new()
        {
            AllowedHosts = [Host],
            DownloadCode = (url, _) =>
            {
                lock (Fetches)
                    Fetches[url] = Fetches.GetValueOrDefault(url) + 1;
                var name = url[$"https://{Host}/".Length..^".kat".Length];
                return Library.TryGetValue(name, out var source)
                    ? ValueTask.FromResult(source)
                    : throw new InvalidOperationException($"404: {url}");
            },
        };
    }

    public enum Twin
    {
        /// <summary>The same text with the load removed.</summary>
        Plain,

        /// <summary>The same text with the family made one clause (the load cannot be removed).</summary>
        SingleClause,
    }

    /// <summary>The twin of <paramref name="deferred"/> in which nothing is deferred; every other token keeps its position.</summary>
    private static string TwinOf(string deferred, Twin kind)
    {
        var twin = kind == Twin.Plain
            ? deferred.Replace(LoadUnused, "0", StringComparison.Ordinal).Replace("{ " + OpenUnused + "\n", "{\n", StringComparison.Ordinal)
            : deferred.Replace("F(0) = 0\n", "F0 = 0\n", StringComparison.Ordinal);
        Assert.NotEqual(deferred, twin);
        if (kind == Twin.Plain)
            Assert.DoesNotContain("load(", twin, StringComparison.Ordinal);
        return twin;
    }

    /// <summary>
    /// The position of the ONE occurrence of <paramref name="text"/> in <paramref name="source"/>, as a
    /// diagnostic spans it: its first character, and the column after its last one.
    /// </summary>
    private static SourceSpan SpanOf(string source, string text)
    {
        var start = source.IndexOf(text, StringComparison.Ordinal);
        Assert.True(start >= 0, $"'{text}' is not in the source");
        Assert.Equal(-1, source.IndexOf(text, start + 1, StringComparison.Ordinal));
        var (startLine, startColumn) = LineAndColumn(source, start);
        var (endLine, endColumn) = LineAndColumn(source, start + text.Length - 1);
        return new SourceSpan(startLine, startColumn, endLine, endColumn + 1);
    }

    private static (int Line, int Column) LineAndColumn(string source, int offset)
    {
        var line = 1;
        var lineStart = 0;
        for (var index = 0; index < offset; index++)
        {
            if (source[index] != '\n')
                continue;
            line++;
            lineStart = index + 1;
        }

        return (line, offset - lineStart + 1);
    }

    /// <summary>
    /// The whole front end over a deferred program: every module text parses cleanly as raw syntax, and the
    /// program's parse is clean, holds a region and downloads nothing.
    /// </summary>
    private static async Task<SourceProvenance> ParseDeferred(string source, RunHost host)
    {
        foreach (var module in Library.Values)
            SourceProvenance.ParseSyntaxValidRoot(module);
        var parsed = await SourceProvenance.ParseValidAsync(source, host.Options);
        Assert.Empty(parsed.Diagnostics);
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(parsed.Root)), "the program holds no deferred region");
        Assert.Equal(0, host.TotalFetches);
        return parsed;
    }

    /// <summary>The twin's parse: nothing deferred, and its error diagnostics in reported order.</summary>
    private static async Task<IReadOnlyList<Diagnostic>> ParseTwin(string twin)
    {
        var parsed = await Parser.ParseAsync(twin, new RunHost().Options);
        Assert.False(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(parsed.Root)), "the twin holds a deferred region");
        return [.. parsed.Diagnostics.Where(static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error)];
    }

    /// <summary>The diagnostic list of the materialization a run of <paramref name="root"/> refused.</summary>
    private static async Task<IReadOnlyList<Diagnostic>> RefusedMaterialization(Algorithm.User root)
    {
        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), null, CancellationToken.None);
        Assert.True(result.IsError, "the selection produced a value");
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var failure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
        Assert.False(result.Error.IsResourceLimit);
        return failure.Diagnostics;
    }

    private static (DiagnosticCode Code, string Message, SourceSpan? Span) Facts(Diagnostic diagnostic)
        => (diagnostic.Code, diagnostic.Message, diagnostic.Span);

    /// <summary>
    /// What every refused program asserts: the deferred twin parses cleanly, its run is ONE evaluation
    /// error with <paramref name="code"/>, and the materialization's list is the twin's parse errors, by
    /// code, message and span, the first of them at <paramref name="span"/>.
    /// </summary>
    private static async Task<IReadOnlyList<Diagnostic>> AssertRefusedLikeItsTwin(
        string deferred, Twin kind, KatLangErrorCode code, SourceSpan span, int expectedDiagnostics = 1)
    {
        var twinErrors = await ParseTwin(TwinOf(deferred, kind));
        Assert.Equal(expectedDiagnostics, twinErrors.Count);
        var twinRun = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(TwinOf(deferred, kind), new RunHost().Options));
        Assert.Equal(code, twinRun.Errors[0].Code);

        var host = new RunHost();
        var parsed = await ParseDeferred(deferred, host);
        var materialization = await RefusedMaterialization(parsed.Root);
        Assert.Equal(twinErrors.Select(Facts), materialization.Select(Facts));
        Assert.Equal(span, materialization[0].Span);

        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(deferred, new RunHost().Options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(code, error.Code);
        Assert.False(error.IsResourceLimit);
        Assert.Equal(span, Assert.NotNull(error.Span));
        Assert.Contains(twinErrors[0].Message, error.Message, StringComparison.Ordinal);
        return materialization;
    }

    private static async Task<string> Display(string source)
        => Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, new RunHost().Options)).ToDisplayString();

    // ── The programs ────────────────────────────────────────────────────────

    /// <summary>The minimal program of the defect: the path sits in a nested body that infers its parameters.</summary>
    private static readonly string Minimal =
        "F(0) = 0\n" +
        "F(n) = { " + OpenUnused + "\n" +
        "  A = { open { public X = 1 }.Nope\n" +
        "    X }\n" +
        "  A(5) }\n" +
        "F(1)\n";

    /// <summary>A load-bearing branch whose rows follow the holder of the unused module.</summary>
    private static string Unit(string rows, string call = "F(1)")
        => "F(0) = 0\n" +
           "F(n) = { H = " + LoadUnused + "\n" +
           rows +
           " }\n" +
           call + "\n";

    /// <summary>The path <paramref name="target"/> opened by a nested body that infers its parameters.</summary>
    private static string InNestedBody(string target)
        => Unit("  A = { open " + target + "\n" +
                "    X }\n" +
                "  A(5)");

    /// <summary>
    /// The path <paramref name="target"/> opened by the second clause of a clause family NESTED in the unit: a
    /// load-free branch, which the module loader keeps by reference.
    /// </summary>
    private static string InNestedBranch(string target, string result = "m")
        => Unit("  G(0) = 0\n" +
                "  G(m) = { open " + target + "\n" +
                "    " + result + " }\n" +
                "  G(5)");

    /// <summary>The minimal program of the nested position: the path sits in the open list of a nested clause branch.</summary>
    private static readonly string MinimalNested = InNestedBranch(MissingStep);

    public sealed record RefusedCase(string Name, string Deferred, Twin Twin, string Target)
    {
        public override string ToString() => Name;
    }

    private const string MissingStep = "{ public X = 1 }.Nope";

    private const string BranchOnlyStep =
        "{ public G(0) = {\n" +
        "        public X = 1\n" +
        "        0\n" +
        "      }\n" +
        "      public G(k) = k }.G.X";

    private static readonly RefusedCase[] RefusedCases =
    [
        // ── Position in the unit (inline block head, missing step) ──
        new("position: a nested body that infers its parameters (the minimal program)", Minimal, Twin.Plain, MissingStep),
        new("position: the branch body's own open list",
            "F(0) = 0\n" +
            "F(n) = { open " + MissingStep + "\n" +
            "  H = " + LoadUnused + "\n" +
            "  n }\n" +
            "F(1)\n",
            Twin.Plain, MissingStep),
        new("position: a nested closed body",
            Unit("  A(p) = { open " + MissingStep + "\n" +
                 "    p }\n" +
                 "  A(5)"),
            Twin.Plain, MissingStep),
        new("position: a block in expression position",
            Unit("  K = 1 + { open " + MissingStep + "\n" +
                 "    7 }\n" +
                 "  K"),
            Twin.Plain, MissingStep),
        new("position: the open list of a block that is itself an open target (of the branch)",
            "F(0) = 0\n" +
            "F(n) = { open { open " + MissingStep + "\n" +
            "      public Y = 2 }\n" +
            "  H = " + LoadUnused + "\n" +
            "  Y + n }\n" +
            "F(1)\n",
            Twin.Plain, MissingStep),
        new("position: the open list of a block that is itself an open target (of a nested body)",
            Unit("  A = { open { open " + MissingStep + "\n" +
                 "        public Y = 2 }\n" +
                 "    Y }\n" +
                 "  A"),
            Twin.Plain, MissingStep),
        new("position: a nested region (a load-bearing clause inside the unit, selected)",
            Unit("  G(0) = 0\n" +
                 "  G(m) = { H2 = " + LoadUnused + "\n" +
                 "    A = { open " + MissingStep + "\n" +
                 "      X }\n" +
                 "    A(5) }\n" +
                 "  G(1)"),
            Twin.Plain, MissingStep),

        // ── Failure (inline block head, in a nested body) ──
        new("failure: a private step", InNestedBody("{ S = { public X = 1 } }.S"), Twin.Plain, "{ S = { public X = 1 } }.S"),
        new("failure: a step declared only inside a conditional branch", InNestedBody(BranchOnlyStep), Twin.Plain, BranchOnlyStep),
        new("failure: a later step of a longer path",
            InNestedBody("{ public S = { public X = 1 } }.S.Nope"), Twin.Plain, "{ public S = { public X = 1 } }.S.Nope"),

        // ── A clause family nested in the unit: below its load-free branches the loaded body is the object graph
        //    the eager operation admitted, so the block has one key in the eager publication and in the unit ──
        new("nested family: the branch's own open list (the minimal program of the position)", MinimalNested, Twin.Plain, MissingStep),
        new("nested family: the first clause of the family",
            Unit("  G(0) = { open " + MissingStep + "\n" +
                 "    0 }\n" +
                 "  G(m) = m\n" +
                 "  G(5)"),
            Twin.Plain, MissingStep),
        new("nested family: a body inside the nested branch",
            Unit("  G(0) = 0\n" +
                 "  G(m) = { A = { open " + MissingStep + "\n" +
                 "      X }\n" +
                 "    A(5) + m }\n" +
                 "  G(5)"),
            Twin.Plain, MissingStep),
        new("nested family: a private step", InNestedBranch("{ S = { public X = 1 } }.S"), Twin.Plain, "{ S = { public X = 1 } }.S"),
        new("nested family: a step declared only inside a conditional branch", InNestedBranch(BranchOnlyStep), Twin.Plain, BranchOnlyStep),
        new("nested family: a later step of a longer path",
            InNestedBranch("{ public S = { public X = 1 } }.S.Nope"), Twin.Plain, "{ public S = { public X = 1 } }.S.Nope"),
        new("nested family: a family two levels deep",
            Unit("  G(0) = 0\n" +
                 "  G(m) = { K(0) = 0\n" +
                 "    K(j) = { open " + MissingStep + "\n" +
                 "      j }\n" +
                 "    K(m) }\n" +
                 "  G(5)"),
            Twin.Plain, MissingStep),
        new("nested family: a nested region below a nested family (a load-bearing clause inside, selected)",
            Unit("  G(0) = 0\n" +
                 "  G(m) = { H2 = " + LoadUnused + "\n" +
                 "    K(0) = 0\n" +
                 "    K(j) = { open " + MissingStep + "\n" +
                 "      j }\n" +
                 "    K(5) }\n" +
                 "  G(1)"),
            Twin.Plain, MissingStep),
        new("nested family: the open list of a block that is itself an open target",
            InNestedBranch("{ open " + MissingStep + "\n" +
                           "        public Y = 2 }", "m + Y"),
            Twin.Plain, MissingStep),

        // ── Head: an inline load ──
        new("head: an inline load, missing step, in a nested body",
            "F(0) = 0\n" +
            "F(n) = { A = { open " + LoadLib + ".Nope\n" +
            "    X }\n" +
            "  A(5) }\n" +
            "F(1)\n",
            Twin.SingleClause, LoadLib + ".Nope"),
        new("head: an inline load, private step, in a nested body",
            "F(0) = 0\n" +
            "F(n) = { A = { open " + LoadLib + ".Priv\n" +
            "    X }\n" +
            "  A(5) }\n" +
            "F(1)\n",
            Twin.SingleClause, LoadLib + ".Priv"),
        new("head: an inline load, missing step, in the branch body's own open list",
            "F(0) = 0\n" +
            "F(n) = { open " + LoadLib + ".Nope\n" +
            "  n }\n" +
            "F(1)\n",
            Twin.SingleClause, LoadLib + ".Nope"),

        // ── Head: the controls that were reported before ──
        new("control head: a name declared in the unit",
            Unit("  L = { public X = 1 }\n" +
                 "  A = { open L.Nope\n" +
                 "    X }\n" +
                 "  A(5)"),
            Twin.Plain, "L.Nope"),
        new("control head: a name declared outside the unit",
            "L = { public X = 1 }\n" +
            Unit("  A = { open L.Nope\n" +
                 "    X }\n" +
                 "  A(5)"),
            Twin.Plain, "L.Nope"),
        new("control head: a module holder",
            "F(0) = 0\n" +
            "F(n) = { M = " + LoadLib + "\n" +
            "  A = { open M.Nope\n" +
            "    X }\n" +
            "  A(5) }\n" +
            "F(1)\n",
            Twin.SingleClause, "M.Nope"),

        // ── A target written in module text: reported at the import site (ONE COORDINATE SPACE PER RESULT) ──
        new("module text: the module's own open list",
            "F(0) = 0\n" +
            "F(n) = { open '" + Url("badroot") + "'\n" +
            "  Q }\n" +
            "F(1)\n",
            Twin.SingleClause, "'" + Url("badroot") + "'"),
        new("module text: a nested body of the module",
            "F(0) = 0\n" +
            "F(n) = { open '" + Url("badnested") + "'\n" +
            "  Q }\n" +
            "F(1)\n",
            Twin.SingleClause, "'" + Url("badnested") + "'"),
    ];

    public static TheoryData<RefusedCase> Refused()
    {
        var data = new TheoryData<RefusedCase>();
        foreach (var item in RefusedCases)
            data.Add(item);
        return data;
    }

    // ── Refused: what the twin's parse reports ──────────────────────────────

    [Theory]
    [MemberData(nameof(Refused))]
    public async Task UnresolvableTarget_IsReportedAtMaterialization_ExactlyAsItsTwinReportsItAtParse(RefusedCase program)
    {
        var materialization = await AssertRefusedLikeItsTwin(
            program.Deferred, program.Twin, KatLangErrorCode.UnresolvedOpenTarget, SpanOf(program.Deferred, program.Target));
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, Assert.Single(materialization).Code);
    }

    [Fact]
    public async Task MinimalProgram_IsRefusedWithThePinnedMessage_WhereItUsedToRunAsFive()
    {
        const string message = "'{...}.Nope' cannot be opened because '{...}' has no property named 'Nope'.";
        var span = new SourceSpan(3, 14, 3, 35);
        Assert.Equal(span, SpanOf(Minimal, MissingStep));

        // The plain twin: the same text without the load.
        var twin = TwinOf(Minimal, Twin.Plain);
        Assert.Equal(
            "F(0) = 0\n" +
            "F(n) = {\n" +
            "  A = { open { public X = 1 }.Nope\n" +
            "    X }\n" +
            "  A(5) }\n" +
            "F(1)\n",
            twin);
        var twinError = Assert.Single(await ParseTwin(twin));
        Assert.Equal((DiagnosticCode.UnresolvedOpenTarget, message, span), Facts(twinError));

        var host = new RunHost();
        var parsed = await ParseDeferred(Minimal, host);
        var diagnostic = Assert.Single(await RefusedMaterialization(parsed.Root));
        Assert.Equal((DiagnosticCode.UnresolvedOpenTarget, message, span), Facts(diagnostic));
        // The module was loaded for the unit: the unit is judged whole, after its load.
        Assert.Equal(1, host["unused"]);

        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(Minimal, new RunHost().Options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UnresolvedOpenTarget, error.Code);
        Assert.Equal(span, Assert.NotNull(error.Span));
        Assert.EndsWith(message, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task NestedFamilyMinimalProgram_IsRefusedWithThePinnedMessage_WhereItUsedToRunAsFive()
    {
        const string message = "'{...}.Nope' cannot be opened because '{...}' has no property named 'Nope'.";
        var span = new SourceSpan(4, 17, 4, 38);
        Assert.Equal(span, SpanOf(MinimalNested, MissingStep));
        Assert.Equal(
            "F(0) = 0\n" +
            "F(n) = { H = load('https://modules.example/unused.kat')\n" +
            "  G(0) = 0\n" +
            "  G(m) = { open { public X = 1 }.Nope\n" +
            "    m }\n" +
            "  G(5) }\n" +
            "F(1)\n",
            MinimalNested);

        // The plain twin: the same text with the holder's load removed.
        var twin = TwinOf(MinimalNested, Twin.Plain);
        Assert.Equal(MinimalNested.Replace(LoadUnused, "0", StringComparison.Ordinal), twin);
        var twinError = Assert.Single(await ParseTwin(twin));
        Assert.Equal((DiagnosticCode.UnresolvedOpenTarget, message, span), Facts(twinError));

        var host = new RunHost();
        var parsed = await ParseDeferred(MinimalNested, host);
        var diagnostic = Assert.Single(await RefusedMaterialization(parsed.Root));
        Assert.Equal((DiagnosticCode.UnresolvedOpenTarget, message, span), Facts(diagnostic));
        // The module was loaded for the unit: the unit is judged whole, after its load.
        Assert.Equal(1, host["unused"]);

        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(MinimalNested, new RunHost().Options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UnresolvedOpenTarget, error.Code);
        Assert.Equal(span, Assert.NotNull(error.Span));
        Assert.EndsWith(message, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RefusedCases_CoverEveryPositionHeadAndFailure()
    {
        Assert.Equal(RefusedCases.Length, RefusedCases.Select(static program => program.Name).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(7, RefusedCases.Count(static program => program.Name.StartsWith("position: ", StringComparison.Ordinal)));
        Assert.Equal(3, RefusedCases.Count(static program => program.Name.StartsWith("failure: ", StringComparison.Ordinal)));
        Assert.Equal(9, RefusedCases.Count(static program => program.Name.StartsWith("nested family: ", StringComparison.Ordinal)));
        Assert.Equal(3, RefusedCases.Count(static program => program.Name.StartsWith("head: ", StringComparison.Ordinal)));
        Assert.Equal(3, RefusedCases.Count(static program => program.Name.StartsWith("control head: ", StringComparison.Ordinal)));
        Assert.Equal(2, RefusedCases.Count(static program => program.Name.StartsWith("module text: ", StringComparison.Ordinal)));
    }

    // ── Valid targets keep their value ──────────────────────────────────────

    public static TheoryData<string, string, Twin, string> ValidControls() => new()
    {
        {
            "a block-headed path",
            Unit("  A = { open { public S = { public X = 1 } }.S\n" +
                 "    X }\n" +
                 "  A"),
            Twin.Plain, "1"
        },
        {
            "a bare block",
            Unit("  A = { open { public X = 1 }\n" +
                 "    X }\n" +
                 "  A"),
            Twin.Plain, "1"
        },
        {
            "a block that opens a block-headed path of its own",
            Unit("  A = { open { open { public S = { public Y = 3 } }.S\n" +
                 "        public X = Y + 1 }\n" +
                 "    X }\n" +
                 "  A"),
            Twin.Plain, "4"
        },
        {
            "an inline load path",
            "F(0) = 0\n" +
            "F(n) = { A = { open " + LoadLib + ".Sub\n" +
            "    X }\n" +
            "  A }\n" +
            "F(1)\n",
            Twin.SingleClause, "1"
        },
        { "below a nested clause branch: a block-headed path", ValidNestedPath, Twin.Plain, "6" },
        { "below a nested clause branch: a bare block", ValidNestedBlock, Twin.Plain, "6" },
        { "below a nested clause branch: a block that opens a block-headed path of its own", ValidNestedBlockOfBlock, Twin.Plain, "9" },
    };

    private static readonly string ValidNestedPath = InNestedBranch("{ public S = { public X = 1 } }.S", "m + X");

    private static readonly string ValidNestedBlock = InNestedBranch("{ public X = 1 }", "m + X");

    private static readonly string ValidNestedBlockOfBlock = InNestedBranch(
        "{ open { public S = { public Y = 3 } }.S\n" +
        "        public X = Y + 1 }",
        "m + X");

    [Theory]
    [MemberData(nameof(ValidControls))]
    public async Task ValidTarget_KeepsItsValue_AndTheValueOfItsTwin(string name, string deferred, Twin kind, string expected)
    {
        Assert.NotEmpty(name);
        var twin = TwinOf(deferred, kind);
        Assert.Empty(await ParseTwin(twin));
        await ParseDeferred(deferred, new RunHost());
        Assert.Equal(expected, await Display(twin));
        Assert.Equal(expected, await Display(deferred));
    }

    // ── Other verdicts on a block head ──────────────────────────────────────

    public static TheoryData<string, string, string> OtherVerdicts() => new()
    {
        {
            "a parameterized block provider",
            Unit("  A = { open { public X = 1\n" +
                 "      p + 1 }\n" +
                 "    X }\n" +
                 "  A"),
            "{ public X = 1\n" +
            "      p + 1 }"
        },
        {
            "a block-headed path to a member that requires arguments",
            Unit("  A = { open { public S(q) = { public X = 1\n" +
                 "        q } }.S\n" +
                 "    X }\n" +
                 "  A"),
            "{ public S(q) = { public X = 1\n" +
            "        q } }.S"
        },
        {
            "below a nested clause branch: a parameterized block provider",
            InNestedBranch("{ public X = 1\n" +
                           "      p + 1 }"),
            "{ public X = 1\n" +
            "      p + 1 }"
        },
        {
            "below a nested clause branch: a block-headed path to a member that requires arguments",
            InNestedBranch("{ public S(q) = { public X = 1\n" +
                           "        q } }.S"),
            "{ public S(q) = { public X = 1\n" +
            "        q } }.S"
        },
    };

    [Theory]
    [MemberData(nameof(OtherVerdicts))]
    public async Task ProviderThatRequiresArguments_IsRefusedAtMaterialization_ExactlyAsItsTwinRefusesItAtParse(
        string name, string deferred, string target)
    {
        Assert.NotEmpty(name);
        var materialization = await AssertRefusedLikeItsTwin(deferred, Twin.Plain, KatLangErrorCode.IllegalInOpen, SpanOf(deferred, target));
        Assert.Equal(DiagnosticCode.IllegalInOpen, Assert.Single(materialization).Code);
    }

    // ── Several targets, selection, caching ─────────────────────────────────

    [Fact]
    public async Task TwoUnresolvableTargetsOfOneUnit_AreBothListed_InWrittenOrder_AndTheEngineReportsTheFirst()
    {
        var deferred = Unit(
            "  A = { open { public X = 1 }.Nope, { public Y = 1 }.Nada\n" +
            "    7 }\n" +
            "  A");
        var first = SpanOf(deferred, "{ public X = 1 }.Nope");
        var second = SpanOf(deferred, "{ public Y = 1 }.Nada");

        var materialization = await AssertRefusedLikeItsTwin(deferred, Twin.Plain, KatLangErrorCode.UnresolvedOpenTarget, first, expectedDiagnostics: 2);
        Assert.Equal([first, second], materialization.Select(static diagnostic => diagnostic.Span));
        Assert.Equal(
            [
                "'{...}.Nope' cannot be opened because '{...}' has no property named 'Nope'.",
                "'{...}.Nada' cannot be opened because '{...}' has no property named 'Nada'.",
            ],
            materialization.Select(static diagnostic => diagnostic.Message));
    }

    [Fact]
    public async Task UnselectedBranch_IsNeverJudged_AndNothingIsDownloaded()
    {
        var source = Minimal.Replace("F(1)\n", "F(0)\n", StringComparison.Ordinal);
        Assert.NotEqual(Minimal, source);
        var host = new RunHost();
        var parsed = await ParseDeferred(source, host);

        var flat = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), null, CancellationToken.None);
        Assert.False(flat.IsError);
        Assert.Equal([(System.Numerics.Decimal128)0], flat.Value);
        Assert.Equal(0, host.TotalFetches);

        var engineHost = new RunHost();
        Assert.Equal("0", Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, engineHost.Options)).ToDisplayString());
        Assert.Equal(0, engineHost.TotalFetches);
    }

    private static DeferredModuleRegion SingleRegion(object root)
    {
        var regions = new List<DeferredModuleRegion>();
        var visited = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!visited.Add(node))
                continue;
            if (node is Algorithm { DeferredRegion: { } region } && !regions.Contains(region))
                regions.Add(region);
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return Assert.Single(regions);
    }

    [Fact]
    public async Task Refusal_IsNotCached_ASecondSelectionOnTheSameTreeIsRefusedAgain()
    {
        var host = new RunHost();
        var parsed = await ParseDeferred(Minimal, host);
        var region = SingleRegion(parsed.Root);

        for (var attempt = 1; attempt <= 3; attempt++)
        {
            var diagnostic = Assert.Single(await RefusedMaterialization(parsed.Root));
            Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, diagnostic.Code);
            Assert.Equal(attempt, region.MaterializationAttempts);
            Assert.False(region.IsMaterialized);
            // The download stays charged, and the cached module is not fetched again.
            Assert.Equal(1, host["unused"]);
            Assert.Equal(1, host.TotalFetches);
        }
    }

    // ── Two units of one program ────────────────────────────────────────────

    /// <summary>
    /// Two load-bearing families that share nothing. F's unit holds the unresolvable path below a nested clause
    /// branch; P's holds a valid block in the same position.
    /// </summary>
    private static string TwoUnits(string output)
        => "F(0) = 0\n" +
           "F(n) = { H = " + LoadUnused + "\n" +
           "  G(0) = 0\n" +
           "  G(m) = { open " + MissingStep + "\n" +
           "    m }\n" +
           "  G(5) }\n" +
           "P(0) = 0\n" +
           "P(n) = { H = " + LoadUnused + "\n" +
           "  G(0) = 0\n" +
           "  G(m) = { open { public Y = 1 }\n" +
           "    m + Y }\n" +
           "  G(5) }\n" +
           output + "\n";

    /// <summary>A reference that must be present, returned for further assertions.</summary>
    private static T Present<T>(T? value) where T : class
    {
        Assert.NotNull(value);
        return value;
    }

    /// <summary>The second clause of the clause family <paramref name="family"/> declared by <paramref name="owner"/>.</summary>
    private static CondBranch SecondClause(Algorithm owner, string family)
        => Assert.IsType<Algorithm.Conditional>(owner.Properties.Single(property => property.Name == family).Value).Branches[1];

    private static DeferredModuleRegion RegionOfFamily(Algorithm owner, string family)
        => Present(SecondClause(owner, family).Body.DeferredRegion);

    [Fact]
    public async Task TwoUnitsOfOneProgram_AreEachJudgedOnTheirOwn_AndARefusalIsNotCached()
    {
        var deferred = TwoUnits("P(1) + F(1)");
        var span = SpanOf(deferred, MissingStep);
        Assert.Single(await AssertRefusedLikeItsTwin(deferred, Twin.Plain, KatLangErrorCode.UnresolvedOpenTarget, span));

        // On ONE tree: the valid unit materializes once and stays; the refused one is judged again at every selection.
        var host = new RunHost();
        var parsed = await ParseDeferred(deferred, host);
        var refused = RegionOfFamily(parsed.Root, "F");
        var valid = RegionOfFamily(parsed.Root, "P");
        Assert.NotSame(refused, valid);
        for (var attempt = 1; attempt <= 3; attempt++)
        {
            var diagnostic = Assert.Single(await RefusedMaterialization(parsed.Root));
            Assert.Equal((DiagnosticCode.UnresolvedOpenTarget, span), (diagnostic.Code, diagnostic.Span));
            Assert.True(valid.IsMaterialized);
            Assert.Equal(1, valid.MaterializationAttempts);
            Assert.False(refused.IsMaterialized);
            Assert.Equal(attempt, refused.MaterializationAttempts);
            // One download serves both units and every attempt.
            Assert.Equal(1, host["unused"]);
            Assert.Equal(1, host.TotalFetches);
        }

        // Only the valid unit is selected: it has its value, and the other unit is never judged.
        var only = TwoUnits("P(1) + F(0)");
        var onlyParsed = await ParseDeferred(only, new RunHost());
        var flat = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(onlyParsed.Root), null, CancellationToken.None);
        Assert.False(flat.IsError);
        Assert.Equal([(System.Numerics.Decimal128)6], flat.Value);
        Assert.True(RegionOfFamily(onlyParsed.Root, "P").IsMaterialized);
        Assert.Equal(0, RegionOfFamily(onlyParsed.Root, "F").MaterializationAttempts);
        Assert.Equal("6", await Display(only));
    }

    // ── The unit's own facts ────────────────────────────────────────────────

    /// <summary>
    /// The first open target of <paramref name="owner"/>: the block that heads it, and the provider its steps
    /// select in that block.
    /// </summary>
    private static (Expr Target, Algorithm Block, Algorithm Provider) FirstOpenTarget(Algorithm owner)
    {
        var target = owner.Opens[0];
        var block = Assert.IsType<Expr.AlgorithmExpr>(target.OpenTargetHead(out var steps)).Algorithm;
        var provider = block;
        foreach (var step in steps)
            provider = provider.Properties.Single(property => property.Name == step).Value;
        return (target, block, provider);
    }

    public static TheoryData<string, string, int> ValidBelowANestedBranch() => new()
    {
        { "a block-headed path", ValidNestedPath, 6 },
        { "a bare block", ValidNestedBlock, 6 },
        { "a block that opens a block-headed path of its own", ValidNestedBlockOfBlock, 9 },
    };

    [Theory]
    [MemberData(nameof(ValidBelowANestedBranch))]
    public async Task ValidTargetBelowANestedBranch_HasAStaticProviderInTheUnitsOwnFacts_AndTheEagerPublicationIsUntouched(
        string name, string deferred, int expected)
    {
        Assert.NotEmpty(name);
        var parsed = await ParseDeferred(deferred, new RunHost());
        var region = SingleRegion(parsed.Root);
        var eager = Present(parsed.Root.CompletedStructure).Facts;
        Assert.True(eager.IsSealed);

        // Before the unit exists the eager publication holds the block of the PLACEHOLDER: an entry with no body.
        var rawBlock = FirstOpenTarget(SecondClause(region.RawBody, "G").Body).Block;
        var key = Present(eager.Child(eager.PreludeKey, rawBlock));
        Assert.Same(eager.PreludeKey, key.Parent);
        var inherited = Present(eager.Facts(key));
        Assert.Null(inherited.Body);
        Assert.Equal(StaticFactKind.Unknown, inherited.Open.Kind);
        Assert.False(inherited.IsProvisional);
        var eagerStorage = eager.RetainedStorageUnits;
        var eagerCount = eager.Count;

        var flat = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), null, CancellationToken.None);
        Assert.False(flat.IsError);
        Assert.Equal([(System.Numerics.Decimal128)expected], flat.Value);
        Assert.True(region.TryGetMaterialized(out var unit));
        var facts = Present(unit.CompletedStructure).Facts;
        Assert.NotSame(eager, facts);
        Assert.True(facts.IsSealed);

        // ONE key names the block in both publications, and the unit's own facts hold it WITH its body: the view the
        // unit's tree holds, published by the unit.
        var clause = SecondClause(unit, "G");
        var (target, block, provider) = FirstOpenTarget(clause.Body);
        Assert.Same(key, facts.Child(facts.PreludeKey, block));
        var own = Present(facts.Facts(key));
        Assert.Same(block, own.Body);
        Assert.Equal(StaticFactKind.Structure, own.Open.Kind);
        Assert.Same(facts, Present(block.CompletedStructure).Facts);

        // So the target has a STATIC provider, read as open-provider validation reads it: under the chain recorded at
        // the branch, at the level of the clause that wrote the open.
        var chain = region.Exposure!.Scope.PropertyScope;
        var unitLevel = ElaboratedScopeLookup.CreateScope(unit, chain, completedContext: CompletedStructureContext.For(unit, chain));
        var clauseLevel = ElaboratedScopeLookup.CreateScope(clause.Body, unitLevel,
            completedContext: CompletedStructureContext.For(clause.Body, unitLevel, clause.Pattern));
        Assert.Same(facts, Present(clauseLevel.CompletedContext).Facts);
        Assert.Same(provider, ElaboratedScopeLookup.ResolveOpenTarget(clauseLevel, target));
        Assert.Null(ElaboratedScopeLookup.DescribeUnresolvedOpenTarget(clauseLevel, target));

        // The eager publication keeps saying what it knows: the same entry, the same count, the same storage.
        Assert.Same(inherited, eager.Facts(key));
        Assert.Equal(eagerCount, eager.Count);
        Assert.Equal(eagerStorage, eager.RetainedStorageUnits);
        // And the unit replaced nothing it inherited with a body: it completed the block and what lies below it.
        Assert.True(AssertEveryInheritedEntryWithABodyStands(eager, facts) > 10);
    }

    [Fact]
    public async Task NestedRegion_OnlyTheUnitThatResolvedTheBlockCompletesItsFacts()
    {
        // The block sits below a load-free branch of a family nested in the INNER unit. The outer unit holds only the
        // inner unit's placeholder: it resolved that body provisionally and took the resolution back, so it published
        // no resolved view of the block and keeps the entry it inherited. The inner unit resolved the block itself.
        // The block has an open list of its own, so that an entry rebuilt for it would not be the inherited one.
        var deferred = Unit(
            "  G(0) = 0\n" +
            "  G(m) = { H2 = " + LoadUnused + "\n" +
            "    K(0) = 0\n" +
            "    K(j) = { open { open { public S = { public Y = 3 } }.S\n" +
            "          public X = Y + 1 }\n" +
            "      j + X }\n" +
            "    K(5) }\n" +
            "  G(1)");
        Assert.Equal("9", await Display(TwinOf(deferred, Twin.Plain)));
        Assert.Equal("9", await Display(deferred));

        var parsed = await ParseDeferred(deferred, new RunHost());
        var outerRegion = SingleRegion(parsed.Root);
        var eager = Present(parsed.Root.CompletedStructure).Facts;
        var flat = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), null, CancellationToken.None);
        Assert.False(flat.IsError);
        Assert.True(outerRegion.TryGetMaterialized(out var outer));
        Assert.True(RegionOfFamily(outer, "G").TryGetMaterialized(out var inner));
        var outerFacts = Present(outer.CompletedStructure).Facts;
        var innerFacts = Present(inner.CompletedStructure).Facts;
        Assert.NotSame(outerFacts, innerFacts);

        var block = FirstOpenTarget(SecondClause(inner, "K").Body).Block;
        var key = Present(innerFacts.Child(innerFacts.PreludeKey, block));
        Assert.Same(block, Present(innerFacts.Facts(key)).Body);
        // The outer unit did not rebuild it: it answers with the very entry the eager publication holds.
        var inherited = Present(eager.Facts(key));
        Assert.Null(inherited.Body);
        Assert.Same(inherited, outerFacts.Facts(key));
    }

    /// <summary>
    /// NOTHING INHERITED THAT HAS A BODY IS REBUILT: for every context the inherited publication holds with a body,
    /// the unit answers with the very entry it inherited. Returns how many such contexts there are.
    /// </summary>
    private static int AssertEveryInheritedEntryWithABodyStands(CompletedStaticStructures inherited, CompletedStaticStructures unit)
    {
        var standing = 0;
        foreach (var key in inherited.Scopes)
        {
            if (inherited.Facts(key) is not { Body: not null } entry)
                continue;
            Assert.Same(entry, unit.Facts(key));
            standing++;
        }

        return standing;
    }

    [Fact]
    public async Task InheritedEntryThatHasABody_Stands_WhereTheUnitPublishesAViewOfTheSameContext()
    {
        // An alias of a prelude member publishes that member as its target's resolved view, in a unit too (measured
        // 2026-11-17: the unit's operation holds its own resolved view at the key of `Math`, which the inherited
        // publication holds WITH its body and its members). A unit never rebuilds such an entry: it would replace
        // the inherited one and attach this program's publication to a prelude object.
        var deferred = Unit("  M = Math\n" +
                            "  M.Abs(0 - 3)");
        Assert.Equal("3", await Display(TwinOf(deferred, Twin.Plain)));
        Assert.Equal("3", await Display(deferred));

        var parsed = await ParseDeferred(deferred, new RunHost());
        var region = SingleRegion(parsed.Root);
        var eager = Present(parsed.Root.CompletedStructure).Facts;
        var math = Present(eager.Facts(Present(eager.Member(eager.PreludeKey, "Math"))));
        Assert.NotEmpty(math.Members);
        var flat = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), null, CancellationToken.None);
        Assert.False(flat.IsError);
        Assert.True(region.TryGetMaterialized(out var unit));
        var facts = Present(unit.CompletedStructure).Facts;
        Assert.NotSame(eager, facts);

        // The prelude, its members and the program's own eager declarations.
        Assert.True(AssertEveryInheritedEntryWithABodyStands(eager, facts) > 10);
        Assert.Same(math, facts.Facts(Present(facts.Member(facts.PreludeKey, "Math"))));
        Assert.Null(Present(math.Body).CompletedStructure);
        // The unit added its own contexts and replaced none.
        Assert.True(facts.Count > eager.Count);
    }

    [Fact]
    public async Task UnitWithSeveralOpenTargetBlocks_EntersThemAtOnePreludeLevelOverItsOwnFacts()
    {
        // Three bodies of one unit, each opening a block of its own.
        string[] bodies = ["A", "B", "C"];
        var deferred = Unit(
            "  A = { open { public X = 1 }\n" +
            "    X }\n" +
            "  B = { open { public Y = 2 }\n" +
            "    Y }\n" +
            "  C = { open { public Z = 3 }\n" +
            "    Z }\n" +
            "  A + B + C");
        Assert.Equal("6", await Display(TwinOf(deferred, Twin.Plain)));

        var parsed = await ParseDeferred(deferred, new RunHost());
        var region = SingleRegion(parsed.Root);
        var flat = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), null, CancellationToken.None);
        Assert.False(flat.IsError);
        Assert.Equal([(System.Numerics.Decimal128)6], flat.Value);
        Assert.True(region.TryGetMaterialized(out var unit));
        var facts = Present(unit.CompletedStructure).Facts;

        // The chain the unit is validated under: its root level carries the EAGER program's facts, so an eager level
        // enters an inline open target at that root.
        var chain = region.Exposure!.Scope.PropertyScope;
        var cache = Present(chain.MemberIndexes);
        Assert.NotSame(facts, Present(chain.Root.CompletedContext).Facts);
        Assert.Same(chain.Root, ElaboratedScopeLookup.OpenBlockHeadLevel(chain));

        var unitLevel = ElaboratedScopeLookup.CreateScope(unit, chain, completedContext: CompletedStructureContext.For(unit, chain));
        var entered = new HashSet<ElaboratedPropertyScope>(ReferenceEqualityComparer.Instance);
        foreach (var name in bodies)
        {
            var body = unit.Properties.Single(property => property.Name == name).Value;
            var bodyLevel = ElaboratedScopeLookup.CreateScope(body, unitLevel, completedContext: CompletedStructureContext.For(body, unitLevel));
            // Validation resolves the target first. Its provider is declared at the prelude, and reading that level
            // records the chain's physical root, the eager one, under the unit's facts and the prelude key.
            var (target, block, _) = FirstOpenTarget(body);
            Assert.Same(block, ElaboratedScopeLookup.ResolveOpenTarget(bodyLevel, target));
            Assert.Same(chain.Root, cache.CompletedLevels[(facts, facts.PreludeKey)]);

            // The level the block is entered at carries the unit's facts: never that recorded eager root.
            var level = ElaboratedScopeLookup.OpenBlockHeadLevel(bodyLevel);
            Assert.NotSame(chain.Root, level);
            Assert.Same(facts, Present(level.CompletedContext).Facts);
            Assert.Same(facts.PreludeKey, level.CompletedContext!.Key);
            Assert.Same(level, level.Root);
            // A level below it is entered at it again (a block that is itself an open target's opener).
            var inside = ElaboratedScopeLookup.CreateScope(block, level, completedContext: CompletedStructureContext.For(block, level));
            Assert.Same(level, ElaboratedScopeLookup.OpenBlockHeadLevel(inside));
            entered.Add(level);
        }

        // K = 3 open-target blocks, ONE prelude level over the unit's facts (measured 2026-11-17 without the sharing:
        // three, one per read).
        Assert.True(entered.Count == 1, $"{bodies.Length} open-target blocks were entered at {entered.Count} prelude levels");
        var shared = entered.Single();
        Assert.Same(shared, cache.OpenBlockHeadLevels[facts]);
        Assert.True(cache.OpenBlockHeadLevels.Count == 1, $"the chain's cache holds {cache.OpenBlockHeadLevels.Count} block-head levels");

        // The validation itself, over the materialized body: clean, and it enters every block at that same level.
        var diagnostics = new DiagnosticBag();
        OpenProviderValidator.Validate(unit, diagnostics, chain, region.ImportSite);
        Assert.Empty(diagnostics);
        Assert.True(cache.OpenBlockHeadLevels.Count == 1, $"validation left {cache.OpenBlockHeadLevels.Count} block-head levels");
        Assert.Same(shared, cache.OpenBlockHeadLevels[facts]);
    }

    [Fact]
    public void CompletingAnInheritedEntry_ExchangesItsStorageExactly_AndLeavesTheInheritedTableAsItWas()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot("B = { public X = 1 }\n0\n");
        var block = root.Properties.Single().Value;
        var member = block.Properties.Single().Value;
        var prelude = new StaticScopeKey(null, OpenProviderIdentity.RootLevelDeclaration);
        var blockKey = new StaticScopeKey(prelude, OpenProviderIdentity.DeclarationOf(block));
        var memberKey = new StaticScopeKey(blockKey, OpenProviderIdentity.DeclarationOf(member));
        static CompletedStaticStructures.Selection Self(StaticScopeKey key) => new(StaticFactKind.Structure, key);
        var unavailable = new CompletedStaticStructures.BodyFacts(null, CompletedStaticStructures.Selection.Unavailable,
            CompletedStaticStructures.Selection.Unavailable, new Dictionary<string, StaticScopeKey>(), new HashSet<string>(), []);
        var blockFacts = new CompletedStaticStructures.BodyFacts(block, Self(blockKey), Self(blockKey),
            new Dictionary<string, StaticScopeKey> { ["X"] = memberKey }, new HashSet<string> { "p", "q" }, [Self(memberKey)]);
        var memberFacts = new CompletedStaticStructures.BodyFacts(member, Self(memberKey), Self(memberKey),
            new Dictionary<string, StaticScopeKey>(), new HashSet<string>(), []);

        // The inherited publication: the placeholder's two entries, with no body. 12 units each.
        var inherited = new CompletedStaticStructures(prelude);
        inherited.Add(blockKey, unavailable);
        inherited.Add(memberKey, unavailable);
        inherited.Seal();
        Assert.Equal(24, inherited.RetainedStorageUnits);

        var unit = new CompletedStaticStructures(prelude, inherited);
        Assert.Equal(24, unit.RetainedStorageUnits);
        // One member (2), two parameters (4 each) and one provider (2) more than the entry it replaces.
        unit.Add(blockKey, blockFacts);
        Assert.Equal(36, unit.RetainedStorageUnits);
        // An entry of the same size as the one it replaces.
        unit.Add(memberKey, memberFacts);
        Assert.Equal(36, unit.RetainedStorageUnits);
        // The completion pass exchanges the unit's own entry once more, for its open names: 2 units per name.
        unit.Add(blockKey, blockFacts with
        {
            UnavailableOpenNames = ImmutableHashSet.Create("a", "b"),
            AmbiguousOpenNames = ImmutableHashSet.Create("c"),
        });
        Assert.Equal(42, unit.RetainedStorageUnits);
        unit.Add(blockKey, blockFacts);
        Assert.Equal(36, unit.RetainedStorageUnits);
        unit.Seal();

        // Exactly what a table that never inherited those keys retains for the same two entries.
        var fresh = new CompletedStaticStructures(prelude);
        fresh.Add(blockKey, blockFacts);
        fresh.Add(memberKey, memberFacts);
        Assert.Equal(fresh.RetainedStorageUnits, unit.RetainedStorageUnits);
        Assert.Equal(2, unit.Count);
        Assert.Same(blockFacts, unit.Facts(blockKey));
        Assert.Same(blockKey, unit.Child(prelude, block));
        Assert.Same(memberKey, unit.Member(blockKey, "X"));

        // The inherited table is as it was: its entries, its count and its storage.
        Assert.Same(unavailable, inherited.Facts(blockKey));
        Assert.Same(unavailable, inherited.Facts(memberKey));
        Assert.Equal(2, inherited.Count);
        Assert.Equal(24, inherited.RetainedStorageUnits);
    }

    // ── The analysis states stay silent ─────────────────────────────────────

    [Fact]
    public void DocumentElaboratedWithoutItsModules_ReportsOnlyThatTheLoadIsUnavailable_AndIsModelled()
    {
        // No downloader: the branch's module cannot be elaborated, so its targets may still resolve. Nothing is
        // reported for them.
        var parsed = Parser.Parse(Minimal);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, diagnostic.Code);

        var model = SemanticModelBuilder.Build(parsed);
        Assert.NotEmpty(model.FindResolutions("A"));
    }

    [Fact]
    public async Task DeferredProgram_ReportsNothingAtParse_TheUnitIsJudgedWhenItIsSelected()
    {
        foreach (var program in RefusedCases)
        {
            var parsed = await Parser.ParseAsync(program.Deferred, new RunHost().Options);
            Assert.True(parsed.Diagnostics.Count == 0, $"{program.Name}: the parse reports {string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message))}");
        }

        // The placeholder is modelled without its module: no diagnostic, and the unit's names stay in the model.
        var minimal = await SourceProvenance.ParseValidAsync(Minimal, new RunHost().Options);
        var model = SemanticModelBuilder.Build(minimal.Parsed);
        Assert.NotEmpty(model.FindResolutions("A"));
    }
}
