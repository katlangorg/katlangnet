using System.Numerics;
using KatLang.Semantics;
using Requirement = KatLang.PropertyExposureResolver.Requirement;

namespace KatLang.Tests;

/// <summary>
/// DEFERRED BRANCHES AND ENCLOSING PARAMETERS (audit of 2026-11-14 § 1.2, "deferred-branch exposure";
/// owner decisions 2026-11-15, option (C) "refuse at load", and 2026-11-16, "resolve the provisional
/// body"). A clause branch that loads a module is a deferred compilation unit (MOD-10, B2c): exposure
/// classifies its family, and every zero-argument property that reads the family, from the branch's
/// PROVISIONAL body, before the module exists.
///
/// <para>The provisional body is elaborated as if the modules it loads on demand were EMPTY: detection
/// decides its written names, and implicit-argument resolution lifts and forwards in it exactly as in
/// an eager branch (<c>ImplicitArgumentResolver.ResolveProvisionalBranch</c>), with nothing reported.
/// So forwarding to a callable the program declares itself (at the root, in the branch, in a block an
/// enclosing algorithm opens) is charged to the enclosing declarations and keeps exact eager parity.
/// Before, the eager front end lifted nothing in such a body: a cached reader gave <c>(7, 7)</c> where
/// the eager twin gives <c>(7, 8)</c>.</para>
///
/// <para>When the unit materializes, what its body requires from outside its family is compared, by
/// owner-qualified identity, with what the family charged
/// (<c>PropertyExposureResolver.ProvisionalFamilyContribution</c> / <c>UnchargedByFamily</c>). A
/// requirement the family never charged can only be one the loaded module decided (a member of it
/// receiving an enclosing parameter, directly or through a declaration of the branch): the
/// materialization then fails with <see cref="DiagnosticCode.DeferredBranchForwardsEnclosingParameter"/>,
/// publishes nothing, caches no failure, and is never a clause non-match. The comparison is the whole
/// decision: nothing asks which callee received the binding.</para>
///
/// <para>Each deferred program is paired with its EAGER TWIN (the holder declared at the root and
/// opened in the branch, so the branch is not deferred), which is the oracle. Every program runs
/// through <see cref="KatLangEngine.RunAsync"/> with an in-memory downloader that counts its calls and
/// a recording host operation <c>trace(x) = x</c>; every source is checked for a clean parse first.</para>
/// </summary>
public class DeferredBranchForwardingRefusalTests
{
    private const string Host = "modules.example";

    private static string Url(string name) => $"https://{Host}/{name}.kat";

    private static readonly Dictionary<string, string> Library = new(StringComparer.Ordinal)
    {
        ["m"] = "public X = y * 10\n",
        ["a"] = "public A0 = 1\n",
        ["s"] = "public Z = 5\n",
        // A member that needs two enclosing parameters.
        ["m2"] = "public X2 = y * 10 + z\n",
        // A self-contained member named like one an enclosing open provides (the known limitation).
        ["m3"] = "public X = 3\n",
        // Self-contained members named like two callables an enclosing open provides.
        ["xy"] = "public X = 1\npublic Y = 2\n",
        // Callables named like those members, each with a written parameter.
        ["cb"] = "public X(x) = x\npublic Y(y) = y\n",
        // A load-bearing family written inside module text: its references carry no location.
        ["outer"] = "public Outer(y) = {\n  F(0) = 0\n  F(n) = { open '" + Url("m") + "'\n    X }\n  F(1)\n}\n",
    };

    /// <summary>The in-memory host of one run: download counts per module and the recorded <c>trace</c> arguments.</summary>
    private sealed class RunHost
    {
        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public List<Decimal128> Trace { get; } = [];

        public int this[string module] => Fetches.GetValueOrDefault(Url(module));

        public int TotalFetches => Fetches.Values.Sum();

        public HostOperations Operations => HostOperations.Create(HostOperation.Create("trace", (arguments, _) =>
        {
            lock (Trace)
                Trace.Add(Assert.IsType<Result.Atom>(arguments[0]).Value);
            return arguments[0];
        }, "x"));

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
            HostOperations = Operations,
        };
    }

    /// <summary>
    /// The EAGER TWIN of a deferred program: every module the program opens by URL is declared by a
    /// holder at the root (<c>Hm = load('…/m.kat')</c>) and opened through it, so no branch is deferred.
    /// </summary>
    private static string EagerTwin(string deferred)
    {
        var holders = new List<string>();
        var twin = deferred;
        foreach (var name in Library.Keys)
        {
            var directive = $"open '{Url(name)}'";
            if (!twin.Contains(directive, StringComparison.Ordinal))
                continue;
            twin = twin.Replace(directive, $"open H{name}", StringComparison.Ordinal);
            holders.Add($"H{name} = load('{Url(name)}')\n");
        }

        Assert.NotEmpty(holders);
        return string.Concat(holders) + twin;
    }

    /// <summary>
    /// The source check every test makes first: each module text parses cleanly as raw syntax, and
    /// the program passes the whole front end (a deferred branch is never judged by the parse).
    /// </summary>
    private static async Task AssertCleanSource(string source)
    {
        foreach (var module in Library.Values)
            SourceProvenance.ParseSyntaxValidRoot(module);
        var parsed = await SourceProvenance.ParseValidAsync(source, new RunHost().Options);
        Assert.DoesNotContain(parsed.Diagnostics, diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
    }

    private static async Task<(RunResult Result, RunHost Host)> Run(string source)
    {
        await AssertCleanSource(source);
        var host = new RunHost();
        return (await KatLangEngine.RunAsync(source, host.Options), host);
    }

    private static Decimal128[] Atoms(params int[] values) => [.. values.Select(value => (Decimal128)value)];

    private static void AssertValue(RunResult result, params int[] expected)
    {
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(Atoms(expected), success.Atoms);
    }

    /// <summary>The position of <paramref name="reference"/> on the one line of <paramref name="source"/> that is exactly <paramref name="line"/>.</summary>
    private static SourceSpan SpanOf(string source, string line, string reference)
    {
        var lines = source.Split('\n');
        var index = Assert.Single(Enumerable.Range(0, lines.Length), candidate => lines[candidate] == line);
        var column = line.IndexOf(reference, StringComparison.Ordinal);
        Assert.True(column >= 0, $"'{reference}' is not on the line '{line}'");
        return new SourceSpan(index + 1, column + 1, index + 1, column + 1 + reference.Length);
    }

    /// <summary>
    /// The public outcome of a refused materialization: ONE <see cref="RunResult.EvalFailure"/> error
    /// with the new code, outside <see cref="KatLangError.IsResourceLimit"/>, worded as
    /// <paramref name="message"/> and positioned at <paramref name="expectedSpan"/>.
    /// </summary>
    private static KatLangError AssertRefusedWith(RunResult result, string message, SourceSpan expectedSpan)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.DeferredBranchForwardsEnclosingParameter, error.Code);
        Assert.False(error.IsResourceLimit);
        Assert.Contains(message, error.Message, StringComparison.Ordinal);
        Assert.Equal(expectedSpan, Assert.NotNull(error.Span));
        return error;
    }

    /// <summary>A refusal that names the reference, the enclosing parameter and the repair, the explicit call.</summary>
    private static KatLangError AssertRefused(RunResult result, string callee, string parameter, string repair, SourceSpan expectedSpan)
    {
        var error = AssertRefusedWith(result, DeferredModuleRegion.ForwardedEnclosingParameterMessage(parameter, callee, repair), expectedSpan);
        Assert.Contains($"write {repair}.", error.Message, StringComparison.Ordinal);
        return error;
    }

    /// <summary>A run's observable outcome: its display, or its error codes.</summary>
    private static string Outcome(RunResult result) => result switch
    {
        RunResult.Success success => "ok " + success.ToDisplayString(),
        RunResult.EvalFailure failure => "error " + string.Join(",", failure.Errors.Select(error => error.Code)),
        _ => result.GetType().Name,
    };

    private static TheoryData<TCase> Rows<TCase>(IEnumerable<TCase> cases)
    {
        var data = new TheoryData<TCase>();
        foreach (var item in cases)
            data.Add(item);
        return data;
    }

    // ── Refused: the loaded module decides the requirement ──────────────────

    private const string LoadM = "load('https://modules.example/m.kat')";
    private const string OpenM = "open 'https://modules.example/m.kat'";
    private const string OpenS = "open 'https://modules.example/s.kat'";
    private const string OpenA = "open 'https://modules.example/a.kat'";
    private const string OpenM3 = "open 'https://modules.example/m3.kat'";
    private const string OpenXy = "open 'https://modules.example/xy.kat'";

    /// <summary>p41: the audit's defect program, without its root rows.</summary>
    private const string P41 =
        "G(y) = {\n" +
        "  F(0) = 0\n" +
        "  F(n) = { " + OpenM + "\n" +
        "    X }\n" +
        "  R = F(1)\n" +
        "  R\n" +
        "}\n";

    /// <summary>
    /// Reviewer finding F1, without its root rows: the module is opened through an in-branch ALIAS of an
    /// in-branch holder. Nothing decides what the branch's opens provide before the module exists, so
    /// no spelling of the route can hide the member.
    /// </summary>
    private const string F1 =
        "G(y) = {\n" +
        "  F(0) = 0\n" +
        "  F(n) = { open P\n" +
        "    M = " + LoadM + "\n" +
        "    P = M\n" +
        "    X }\n" +
        "  R = F(1)\n" +
        "  R\n" +
        "}\n";

    /// <summary>F1's eager twin: the holder declared at the root.</summary>
    private static string F1Twin(string program)
        => "M = " + LoadM + "\n" + program.Replace("    M = " + LoadM + "\n", "", StringComparison.Ordinal);

    public sealed record RefusedCase(
        string Name, string Deferred, string? EagerTwin, int[] EagerValue,
        string ReferenceLine, string Reference, string Repair, string[] Downloads)
    {
        public string Twin => EagerTwin ?? DeferredBranchForwardingRefusalTests.EagerTwin(Deferred);

        public override string ToString() => Name;
    }

    private static string Branch(string header, string branchRows)
        => header + " = {\n" +
           "  F(0) = 0\n" +
           "  F(n) = { " + branchRows + " }\n" +
           "  F(1)\n" +
           "}\n";

    private static readonly RefusedCase[] RefusedCases =
    [
        // p41: before (10, 10); the eager twin (10, 20).
        new RefusedCase("p41", P41 + "G(1), G(2)\n", null, [10, 20], "    X }", "X", "X(y)", ["m"]),
        // A single activation gave the right value by luck (20) and is refused as decided.
        new RefusedCase("p41-single-activation", P41 + "G(2)\n", null, [20], "    X }", "X", "X(y)", ["m"]),
        // v01: the load holder is written in the branch.
        new RefusedCase(
            "v01-holder-in-branch",
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { M = " + LoadM + "\n" +
            "    M.X }\n" +
            "  R = F(1)\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2)\n",
            "M = " + LoadM + "\n" +
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { M.X }\n" +
            "  R = F(1)\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2)\n",
            [10, 20], "    M.X }", "M.X", "M.X(y)", ["m"]),
        // v15: the enclosing binding is a clause binder of a root family.
        new RefusedCase(
            "v15-enclosing-clause-binder",
            "H(0) = 0\n" +
            "H(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { " + OpenM + "\n" +
            "    X }\n" +
            "  R = F(1)\n" +
            "  R\n" +
            "}\n" +
            "H(1), H(2)\n",
            null, [10, 20], "    X }", "X", "X(y)", ["m"]),
        // v18: an outer open provides the name until the module shadows it.
        new RefusedCase(
            "v18-outer-open-shadowed",
            "L = { public X = 7 }\n" +
            "G(y) = {\n" +
            "  open L\n" +
            "  F(0) = 0\n" +
            "  F(n) = { " + OpenM + "\n" +
            "    X }\n" +
            "  R = F(1)\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2)\n",
            null, [10, 20], "    X }", "X", "X(y)", ["m"]),
        // v06: a deferred region nested inside a materialized body: the outer one loads, the inner one is refused.
        new RefusedCase(
            "v06-nested-region",
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { " + OpenA + "\n" +
            "    H(0) = 0\n" +
            "    H(k) = { " + OpenM + "\n" +
            "      X }\n" +
            "    Q = H(A0)\n" +
            "    Q }\n" +
            "  F(1)\n" +
            "}\n" +
            "G(1), G(2)\n",
            null, [10, 20], "      X }", "X", "X(y)", ["a", "m"]),
        // v13: forwarding through an inner property was accepted with the right value by luck, and is refused as decided.
        new RefusedCase(
            "v13-through-an-inner-property",
            Branch("G(y)", OpenM + "\n    P = X\n    P") + "G(1), G(2)\n",
            null, [10, 20], "    P }", "P", "P(y)", ["m"]),
        // The map form: before [11, 11, 11]; the eager twin [11, 21, 31].
        new RefusedCase(
            "map",
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { " + OpenM + "\n" +
            "    X + n }\n" +
            "  R = F(1) + 0\n" +
            "  R\n" +
            "}\n" +
            "map([1, 2, 3], G)\n",
            null, [11, 21, 31], "    X + n }", "X", "X(y)", ["m"]),
        // Reviewer finding F1: before (10, 10), since the route through the alias was not recognized.
        new RefusedCase("F1-open-of-an-alias-of-the-holder", F1 + "G(1), G(2)\n", F1Twin(F1 + "G(1), G(2)\n"),
            [10, 20], "    X }", "X", "X(y)", ["m"]),
        // The module opened through a holder the branch declares.
        new RefusedCase(
            "open-of-an-in-branch-holder",
            Branch("G(y)", "open M\n    M = " + LoadM + "\n    X + n") + "G(1), G(2)\n",
            F1Twin(Branch("G(y)", "open M\n    M = " + LoadM + "\n    X + n") + "G(1), G(2)\n"),
            [11, 21], "    X + n }", "X", "X(y)", ["m"]),
        // An in-branch alias of an in-branch alias of the member: reported at the reference that forwards.
        new RefusedCase(
            "alias-chain-to-the-member",
            Branch("G(y)", OpenM + "\n    P = X\n    Q = P\n    Q + n") + "G(1), G(2)\n",
            null, [11, 21], "    Q + n }", "Q", "Q(y)", ["m"]),
        // The member read by a formula of the branch: reported where it is read.
        new RefusedCase(
            "member-in-an-inner-formula",
            Branch("G(y)", OpenM + "\n    P = X + 1\n    P") + "G(1), G(2)\n",
            null, [11, 21], "    P = X + 1", "X", "X(y)", ["m"]),
        // The member read inside a block the branch writes: reported where it is read.
        new RefusedCase(
            "member-inside-a-nested-block",
            Branch("G(y)", OpenM + "\n    B = { T = X + 1\n      T }\n    B + n") + "G(1), G(2)\n",
            null, [12, 22], "    B = { T = X + 1", "X", "X(y)", ["m"]),
    ];

    public static TheoryData<RefusedCase> RefusedPrograms => Rows(RefusedCases);

    [Theory]
    [MemberData(nameof(RefusedPrograms))]
    public async Task BranchWhoseLoadedMemberWouldReceiveAnEnclosingParameter_IsRefused_AndItsEagerTwinKeepsItsValue(RefusedCase program)
    {
        var (deferred, host) = await Run(program.Deferred);
        AssertRefused(deferred, program.Reference, "y", program.Repair, SpanOf(program.Deferred, program.ReferenceLine, program.Reference));
        // The body never ran, and the downloads the attempt made stay charged: one per module.
        Assert.Empty(host.Trace);
        Assert.Equal(program.Downloads.Length, host.TotalFetches);
        Assert.All(program.Downloads, module => Assert.Equal(1, host[module]));

        var (eager, _) = await Run(program.Twin);
        AssertValue(eager, program.EagerValue);
    }

    // ── Escapes ─────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("G.R\n")]
    [InlineData("G.F(1)\n")]
    [InlineData("H(y) = G.F(1)\nH(3)\n")]
    public async Task EscapeOfTheDefectProgram_IsTheNewRefusal_NeverUnknownName_AndNeverAValue(string rows)
    {
        var source = P41 + rows;
        var (deferred, _) = await Run(source);
        // Before: UnknownName for the two paths, and 30 for H(3), which read the caller's y.
        AssertRefused(deferred, "X", "y", "X(y)", SpanOf(source, "    X }", "X"));

        // The eager twin refuses the escape as an ordinary accessibility error.
        var (eager, _) = await Run(EagerTwin(source));
        var failure = Assert.IsType<RunResult.EvalFailure>(eager);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, Assert.Single(failure.Errors).Code);
    }

    [Fact]
    public async Task EscapeThroughAnAliasOfTheHolder_IsTheNewRefusal_NeverUnknownName()
    {
        // Reviewer finding F1 with the escape as its row: before, UnknownName at X.
        var source = F1 + "G.R\n";
        var (deferred, _) = await Run(source);
        AssertRefused(deferred, "X", "y", "X(y)", SpanOf(source, "    X }", "X"));

        var (eager, _) = await Run(F1Twin(source));
        var failure = Assert.IsType<RunResult.EvalFailure>(eager);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, Assert.Single(failure.Errors).Code);
    }

    // ── Accepted programs: exactly the eager twin's value, trace and escape ──

    public sealed record AdmittedCase(string Name, string Deferred, int[] Value, int[] Trace, string? EagerTwin = null)
    {
        public string Twin => EagerTwin ?? DeferredBranchForwardingRefusalTests.EagerTwin(Deferred);

        public override string ToString() => Name;
    }

    private static string Family(string firstClause, string open, string output, string reader)
        => "G(y) = {\n" +
           "  " + firstClause + "\n" +
           "  F(n) = { " + open + "\n" +
           "    " + output + " }\n" +
           "  R = " + reader + "\n" +
           "  R\n" +
           "}\n";

    private const string ReaderSlot = "@READER@";

    /// <summary>
    /// One program in its two reader forms: the cached read <c>R = reader</c>, and the counted one
    /// <c>R = trace(reader)</c>, whose trace is one entry per evaluation of the reader.
    /// </summary>
    private static AdmittedCase[] BothReaders(string name, string template, string reader, int[] value, string? twinTemplate = null)
    {
        Assert.Contains(ReaderSlot, template, StringComparison.Ordinal);
        var counted = $"trace({reader})";
        return
        [
            new AdmittedCase(name, template.Replace(ReaderSlot, reader, StringComparison.Ordinal), value, [],
                twinTemplate?.Replace(ReaderSlot, reader, StringComparison.Ordinal)),
            new AdmittedCase(name + "-counted", template.Replace(ReaderSlot, counted, StringComparison.Ordinal), value, value,
                twinTemplate?.Replace(ReaderSlot, counted, StringComparison.Ordinal)),
        ];
    }

    private const string RootW = "W = y + 1\n";

    /// <summary>
    /// THE NEWLY ACCEPTED CLASS (owner decision 2026-11-16): a load-bearing branch forwards an enclosing
    /// parameter to a callable its modules do not decide. The provisional body holds that forwarding, so
    /// the family charges the parameter and the reader <c>R</c> is evaluated once per activation of
    /// <c>G</c>, as in the eager twin. Before, each gave its first activation's value twice.
    /// </summary>
    private static readonly AdmittedCase[] ForwardingCases =
    [
        // A1: a root callable in a formula. Before (7, 7).
        .. BothReaders("A1-root-callable-in-a-formula",
            RootW + Family("F(0) = 0", OpenS, "W + Z", ReaderSlot) + "G(1), G(2)\n", "F(1)", [7, 8]),
        // A2: bare forwarding of a lone row. Before (2, 2).
        .. BothReaders("A2-root-callable-as-a-lone-row",
            RootW + Family("F(0) = 0", OpenS, "W", ReaderSlot) + "G(1), G(2)\n", "F(1)", [2, 3]),
        // A3: a callable the branch declares, with a written parameter. Before (7, 7).
        .. BothReaders("A3-callable-declared-in-the-branch",
            Family("F(0) = 0", OpenS, "K(y) = y * 2\n    K + Z", ReaderSlot) + "G(1), G(2)\n", "F(1)", [7, 9]),
        // A4: a member of a block the enclosing algorithm opens. Before (8, 8).
        .. BothReaders("A4-member-of-an-enclosing-open",
            "L = { public Q = t * 3 }\n" +
            "G(t) = {\n" +
            "  open L\n" +
            "  F(0) = 0\n" +
            "  F(n) = { " + OpenS + "\n" +
            "    Q + Z }\n" +
            "  R = " + ReaderSlot + "\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2)\n", "F(1)", [8, 11]),
        // A5: an in-branch alias of a root callable. Before (7, 7).
        .. BothReaders("A5-in-branch-alias-of-a-root-callable",
            RootW + Family("F(0) = 0", OpenS, "P = W\n    P + Z", ReaderSlot) + "G(1), G(2)\n", "F(1)", [7, 8]),
        // A6: the module's X receives y too, but W already charged y. The narrowed rule refused it.
        .. BothReaders("A6-root-callable-beside-a-module-member",
            RootW + Family("F(0) = 0", OpenM, "W + X", ReaderSlot) + "G(1), G(2)\n", "F(1)", [12, 23]),
        // A7 (reviewer finding F2): an inner open of a declared block provides X; the module's X is shadowed.
        // Before (100, 100); the narrowed rule refused it and blamed the module.
        .. BothReaders("A7-inner-open-of-a-declared-block",
            "L = { public X = y * 100 }\n" + Family("F(0) = 0", OpenM, "B = { open L\n      X + 0 }\n    B", ReaderSlot) + "G(1), G(2)\n",
            "F(1)", [100, 200]),
        // A8 (reviewer finding F2, carrier): the same through a forwarding carrier.
        .. BothReaders("A8-inner-open-through-a-carrier",
            "L = { public X = y * 100 }\n" + Family("F(0) = 0", OpenM, "B = { open L\n      X }\n    B", ReaderSlot) + "G(1), G(2)\n",
            "F(1)", [100, 200]),
        // Two load-bearing clauses of one family, each forwarding to the root callable.
        .. BothReaders("two-load-bearing-clauses",
            RootW +
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(1) = { " + OpenS + "\n" +
            "    W + Z }\n" +
            "  F(n) = { " + OpenA + "\n" +
            "    W + A0 }\n" +
            "  R = " + ReaderSlot + "\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2)\n", "F(1) + F(2)", [10, 12]),
        // The module held by a holder the branch declares, read by a member path beside the root callable.
        .. BothReaders("holder-in-the-branch-beside-a-root-callable",
            RootW +
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { M = load('https://modules.example/s.kat')\n" +
            "    W + M.Z }\n" +
            "  R = " + ReaderSlot + "\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2)\n", "F(1)", [7, 8],
            "M = load('https://modules.example/s.kat')\n" + RootW +
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { W + M.Z }\n" +
            "  R = " + ReaderSlot + "\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2)\n"),
        // A clause family the branch declares, forwarding in both of its clauses.
        .. BothReaders("family-declared-in-the-branch",
            RootW + Family("F(0) = 0", OpenS, "H(0) = W\n    H(k) = W + k + Z\n    H(n)", ReaderSlot) + "G(1), G(2)\n", "F(1)", [8, 9]),
        // A load-bearing branch nested in a load-bearing branch: the inner unit is judged when it loads.
        .. BothReaders("nested-load-bearing-branch",
            RootW +
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { " + OpenA + "\n" +
            "    H(0) = 0\n" +
            "    H(k) = { " + OpenS + "\n" +
            "      W + Z }\n" +
            "    Q = H(A0)\n" +
            "    Q }\n" +
            "  R = " + ReaderSlot + "\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2)\n", "F(1)", [7, 8]),
        // A member of a block written in the branch's row.
        .. BothReaders("block-written-in-the-row",
            RootW + Family("F(0) = 0", OpenS, "{ K = W + Z\n      K }.K + 0", ReaderSlot) + "G(1), G(2)\n", "F(1)", [7, 8]),
        // A block written as an OPEN TARGET inside the branch. Such a block is rooted at the prelude, so its static
        // context is the same in the placeholder and in the materialized body: the materialization must elaborate its
        // own, never meet the provisional resolution's.
        .. BothReaders("open-target-block-in-the-branch",
            RootW + Family("F(0) = 0", OpenS, "K = { open { public V = 40 }\n      V + W }\n    K + Z", ReaderSlot) + "G(1), G(2)\n",
            "F(1)", [47, 48]),
    ];

    private static readonly AdmittedCase[] UnchangedCases =
    [
        // v08: self-contained. R stays exported: one evaluation for the whole run, and G.R is accessible.
        new AdmittedCase("v08-self-contained", Family("F(0) = 0", OpenS, "Z", "trace(F(1))") + "G(1), G(2), G.R\n", [5, 5, 5], [5]),
        // v21: the same with the run's tick counter: one tick.
        new AdmittedCase("v21-self-contained-tick", Family("F(0) = 0", OpenS, "Z", "F(1) + tick() * 1000") + "G(1), G(2), G.R\n", [1005, 1005, 1005], []),
        // v14: the enclosing parameter is passed explicitly.
        new AdmittedCase("v14-explicit-argument", Family("F(0) = 0", OpenM, "X(y)", "F(1)") + "G(1), G(2)\n", [10, 20], []),
        new AdmittedCase("v14-explicit-argument-counted", Family("F(0) = 0", OpenM, "X(y)", "trace(F(1))") + "G(1), G(2)\n", [10, 20], [10, 20]),
        // v17: the branch reads the parameter itself, so the family charged it.
        new AdmittedCase("v17-written-read-in-the-branch", Family("F(0) = 0", OpenM, "X + y * 0", "F(1)") + "G(1), G(2)\n", [10, 20], []),
        new AdmittedCase("v17-written-read-in-the-branch-counted", Family("F(0) = 0", OpenM, "X + y * 0", "trace(F(1))") + "G(1), G(2)\n", [10, 20], [10, 20]),
        // v20: another clause of the family reads the parameter: the FAMILY's contribution holds it.
        new AdmittedCase("v20-other-clause-reads-it", Family("F(0) = y * 0", OpenM, "X", "F(1)") + "G(1), G(2)\n", [10, 20], []),
        new AdmittedCase("v20-other-clause-reads-it-counted", Family("F(0) = y * 0", OpenM, "X", "trace(F(1))") + "G(1), G(2)\n", [10, 20], [10, 20]),
        // A parameter of an owner INSIDE the branch is the member's argument: nothing escapes the family.
        new AdmittedCase(
            "inner-owner-binds-the-name",
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { " + OpenM + "\n" +
            "    K(y) = X + 0\n" +
            "    K(n) }\n" +
            "  R = trace(F(1))\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2), G.R\n",
            [10, 10, 10], [10]),
        // The branch's own binder is the member's argument.
        new AdmittedCase(
            "branch-binder-binds-the-name",
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(y) = { " + OpenM + "\n" +
            "    X }\n" +
            "  R = trace(F(7))\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2), G.R\n",
            [70, 70, 70], [70]),
        // An enclosing property that reads the parameter was charged by the provisional body already.
        new AdmittedCase(
            "enclosing-property-reads-it",
            "G(y) = {\n" +
            "  W = y * 3\n" +
            "  F(0) = 0\n" +
            "  F(n) = { " + OpenS + "\n" +
            "    W + Z }\n" +
            "  R = trace(F(1))\n" +
            "  R\n" +
            "}\n" +
            "G(1), G(2)\n",
            [8, 11], [8, 11]),
    ];

    private static IEnumerable<AdmittedCase> AdmittedCases => UnchangedCases.Concat(ForwardingCases);

    public static TheoryData<AdmittedCase> AdmittedPrograms => Rows(AdmittedCases);

    [Theory]
    [MemberData(nameof(AdmittedPrograms))]
    public async Task AdmittedProgram_HasExactlyItsEagerTwinsValueAndEvaluationCount(AdmittedCase program)
    {
        var (deferred, deferredHost) = await Run(program.Deferred);
        AssertValue(deferred, program.Value);
        Assert.Equal(Atoms(program.Trace), deferredHost.Trace);

        var (eager, eagerHost) = await Run(program.Twin);
        AssertValue(eager, program.Value);
        Assert.Equal(deferredHost.Trace, eagerHost.Trace);
        Assert.Equal(eager.ToDisplayString(), deferred.ToDisplayString());
    }

    /// <summary>A program's declarations, without its root rows: everything through the last closing brace line.</summary>
    private static string Declarations(string program)
        => program[..(program.LastIndexOf("}\n", StringComparison.Ordinal) + 2)];

    [Theory]
    [MemberData(nameof(AdmittedPrograms))]
    public async Task AdmittedProgram_HasExactlyItsEagerTwinsEscapeOutcome_AndNeverUnknownName(AdmittedCase program)
    {
        // The declarations with the escape as the program's only row: G.R and G.F(1) from the root,
        // and G.F(1) from another owner's activation.
        foreach (var rows in new[] { "G.R\n", "G.F(1)\n", "Other(y) = G.F(1)\nOther(3)\n" })
        {
            var (deferred, deferredHost) = await Run(Declarations(program.Deferred) + rows);
            var (eager, eagerHost) = await Run(Declarations(program.Twin) + rows);
            Assert.Equal(Outcome(eager), Outcome(deferred));
            Assert.Equal(eagerHost.Trace, deferredHost.Trace);
            Assert.DoesNotContain(nameof(KatLangErrorCode.UnknownName), Outcome(deferred), StringComparison.Ordinal);
        }
    }

    [Theory]
    [InlineData("A1-root-callable-in-a-formula")]
    [InlineData("A3-callable-declared-in-the-branch")]
    [InlineData("A4-member-of-an-enclosing-open")]
    public async Task EscapeOfAReaderThatForwards_IsTheEagerTwinsAccessibilityError_NeverUnknownName_AndNeverAValue(string name)
    {
        // Before: UnknownName at the forwarded parameter, since R was classified exported.
        var program = Assert.Single(ForwardingCases, candidate => candidate.Name == name);
        var (deferred, deferredHost) = await Run(Declarations(program.Deferred) + "G.R\n");
        var failure = Assert.IsType<RunResult.EvalFailure>(deferred);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, Assert.Single(failure.Errors).Code);
        // The escape is refused by the classification, before anything is loaded.
        Assert.Equal(0, deferredHost.TotalFetches);

        var (eager, _) = await Run(Declarations(program.Twin) + "G.R\n");
        Assert.Equal(Outcome(eager), Outcome(deferred));
    }

    // ── The known limitation ────────────────────────────────────────────────

    public sealed record LimitationCase(string Name, string Deferred)
    {
        public override string ToString() => Name;
    }

    /// <summary>
    /// KNOWN LIMITATION (kept by the owner's decision of 2026-11-16): the provisional body is elaborated as
    /// if the branch's modules were empty, so a name the module provides AND an enclosing level's open
    /// provides is read, provisionally, as the enclosing provider's, and the family is charged what
    /// that provider needs. Here it needs the enclosing parameter and the module's member needs nothing:
    /// the reader is classified local-only although the materialized branch is self-contained.
    /// </summary>
    private static readonly LimitationCase[] LimitationCases =
    [
        // A direct read: the enclosing provider reads the parameter (identical before the decision).
        new LimitationCase("enclosing-provider-reads-the-parameter",
            "G(y) = {\n" +
            "  open L\n" +
            "  L = { public X = y * 7 }\n" +
            "  F(0) = 0\n" +
            "  F(n) = { " + OpenM3 + "\n" +
            "    X }\n" +
            "  R = trace(F(1))\n" +
            "  R\n" +
            "}\n"),
        // Forwarding: the enclosing provider would receive the parameter (the same over-charge, since the decision).
        new LimitationCase("enclosing-provider-would-receive-the-parameter",
            "L = { public X = t * 7 }\n" +
            "G(t) = {\n" +
            "  open L\n" +
            "  F(0) = 0\n" +
            "  F(n) = { " + OpenM3 + "\n" +
            "    X + 0 }\n" +
            "  R = trace(F(1))\n" +
            "  R\n" +
            "}\n"),
    ];

    public static TheoryData<LimitationCase> LimitationPrograms => Rows(LimitationCases);

    [Theory]
    [MemberData(nameof(LimitationPrograms))]
    public async Task KnownLimitation_ModuleShadowsANameAnEnclosingOpenProvides_ValueParity_WithOneEvaluationPerActivation(LimitationCase program)
    {
        var (deferred, deferredHost) = await Run(program.Deferred + "G(1), G(2)\n");
        var (eager, eagerHost) = await Run(EagerTwin(program.Deferred + "G(1), G(2)\n"));

        // Values are right.
        AssertValue(deferred, 3, 3);
        AssertValue(eager, 3, 3);
        // THE LIMITATION, pinned so that removing it is a visible change of this test: the deferred
        // reader is evaluated once per activation of G, the eager twin's once per run.
        Assert.Equal(Atoms(3, 3), deferredHost.Trace);
        Assert.Equal(Atoms(3), eagerHost.Trace);

        // And its escape is refused where the eager twin's is accessible. Never UnknownName.
        var (deferredEscape, _) = await Run(program.Deferred + "G.R\n");
        var failure = Assert.IsType<RunResult.EvalFailure>(deferredEscape);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, Assert.Single(failure.Errors).Code);
        var (eagerEscape, _) = await Run(EagerTwin(program.Deferred + "G.R\n"));
        AssertValue(eagerEscape, 3);
    }

    // ── The guard over the whole class ──────────────────────────────────────

    public sealed record ClassProgram(string Name, string Deferred, string Twin, bool EvaluationCountParity)
    {
        public override string ToString() => Name;
    }

    public static TheoryData<ClassProgram> EveryProgramOfTheClass()
    {
        var programs = new List<ClassProgram>();
        foreach (var program in RefusedCases)
            programs.Add(new(program.Name, program.Deferred, program.Twin, true));
        foreach (var program in AdmittedCases)
        {
            programs.Add(new(program.Name, program.Deferred, program.Twin, true));
            foreach (var (escape, rows) in new[] { ("R", "G.R\n"), ("F", "G.F(1)\n") })
                programs.Add(new($"{program.Name}-escape-{escape}", Declarations(program.Deferred) + rows, Declarations(program.Twin) + rows, true));
        }

        foreach (var rows in new[] { "G.R\n", "G.F(1)\n", "H(y) = G.F(1)\nH(3)\n", "H(y) = G.R\nH(3)\n", "G(1), G.R\n" })
        {
            programs.Add(new("p41 with " + rows.TrimEnd().Replace("\n", "; ", StringComparison.Ordinal), P41 + rows, EagerTwin(P41 + rows), true));
            programs.Add(new("F1 with " + rows.TrimEnd().Replace("\n", "; ", StringComparison.Ordinal), F1 + rows, F1Twin(F1 + rows), true));
        }

        // The known limitation: value parity only.
        foreach (var program in LimitationCases)
        {
            foreach (var rows in new[] { "G(1), G(2)\n", "G.R\n" })
                programs.Add(new(program.Name + " with " + rows.TrimEnd(), program.Deferred + rows, EagerTwin(program.Deferred + rows), false));
        }

        programs.Add(new("two-missing-bindings", TwoMissingBindings, EagerTwin(TwoMissingBindings), true));
        programs.Add(new("block-headed-lone-row", BlockHeadedLoneRow, EagerTwin(BlockHeadedLoneRow), true));
        programs.Add(new("block-headed-formula", BlockHeadedFormula, EagerTwin(BlockHeadedFormula), true));
        programs.Add(new("refused-provisional-group", RefusedProvisionalGroup("7"), EagerTwin(RefusedProvisionalGroup("7")), true));
        programs.Add(new("refused-provisional-group-that-forwards", RefusedProvisionalGroup("W"), EagerTwin(RefusedProvisionalGroup("W")), true));
        programs.Add(new("refused-nested-provisional-group", NestedRefusedProvisionalGroup, EagerTwin(NestedRefusedProvisionalGroup), true));
        return Rows(programs);
    }

    /// <summary>
    /// THE GUARD: no program of this class reaches the evaluation error <c>UnknownName</c> (a captured
    /// read whose owner has no activation), and every deferred program that is ACCEPTED equals its
    /// eager twin in value and in evaluation count; the known limitation keeps value parity only. A
    /// deferred program may be refused where its twin has a value, never the reverse with another value.
    /// </summary>
    [Theory]
    [MemberData(nameof(EveryProgramOfTheClass))]
    public async Task NoProgramOfTheClass_ReachesUnknownName_AndEveryAcceptedOneEqualsItsEagerTwin(ClassProgram program)
    {
        var (deferred, deferredHost) = await Run(program.Deferred);
        if (deferred is RunResult.EvalFailure failure)
        {
            Assert.DoesNotContain(failure.Errors, error => error.Code == KatLangErrorCode.UnknownName);
            return;
        }

        var accepted = Assert.IsType<RunResult.Success>(deferred);
        var (eager, eagerHost) = await Run(program.Twin);
        Assert.Equal(Assert.IsType<RunResult.Success>(eager).Atoms, accepted.Atoms);
        Assert.Equal(eager.ToDisplayString(), deferred.ToDisplayString());
        if (program.EvaluationCountParity)
            Assert.Equal(eagerHost.Trace, deferredHost.Trace);
    }

    // ── The refusal is a materialization failure: unpublished, uncached, never a non-match ─

    /// <summary>Every placeholder body reachable from <paramref name="root"/> with its region, by reference, in first-reach order.</summary>
    private static List<(Algorithm Placeholder, DeferredModuleRegion Region)> Placeholders(object root)
    {
        var placeholders = new List<(Algorithm, DeferredModuleRegion)>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var visited = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!visited.Add(node))
                continue;
            if (node is Algorithm { DeferredRegion: { } region } placeholder && seen.Add(region))
                placeholders.Add((placeholder, region));
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return placeholders;
    }

    /// <summary>Every deferred region reachable from <paramref name="root"/>, by reference, in first-reach order.</summary>
    private static List<DeferredModuleRegion> Regions(object root) => [.. Placeholders(root).Select(static item => item.Region)];

    private static (PropertyExposure F, PropertyExposure R) Exposures(Algorithm.User root)
    {
        var g = Assert.Single(root.Properties, property => property.Name == "G").Value;
        return (Assert.Single(g.Properties, property => property.Name == "F").Exposure,
            Assert.Single(g.Properties, property => property.Name == "R").Exposure);
    }

    private static EvalError.ModuleRegionMaterializationFailed AssertMaterializationRefused<T>(EvalResult<T> result)
    {
        Assert.True(result.IsError, "the refused selection produced a value");
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var failure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
        Assert.All(failure.Diagnostics, diagnostic => Assert.Equal(DiagnosticCode.DeferredBranchForwardsEnclosingParameter, diagnostic.Code));
        Assert.Equal(KatLangErrorCode.DeferredBranchForwardsEnclosingParameter, KatLangError.FromEvalError(result.Error).Code);
        Assert.False(result.Error.IsResourceLimit);
        return failure;
    }

    [Fact]
    public async Task RefusedRegion_ReselectedOnOneTree_IsRefusedAgain_WithoutCachingTheFailureOrDownloadingAgain()
    {
        var host = new RunHost();
        var parsed = await SourceProvenance.ParseValidAsync(P41 + "G(1), G(2)\n", host.Options);
        Assert.Equal(0, host.TotalFetches);
        var region = Assert.Single(Regions(parsed.Root));

        for (var attempt = 1; attempt <= 3; attempt++)
        {
            var failure = AssertMaterializationRefused(
                await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), host.Operations, null, null, CancellationToken.None));
            Assert.Single(failure.Diagnostics);
            Assert.Equal(attempt, region.MaterializationAttempts);
            Assert.False(region.IsMaterialized);
            // The download stays charged, and the cached module is not fetched again.
            Assert.Equal(1, host["m"]);
            Assert.Equal(1, host.TotalFetches);
        }
    }

    [Fact]
    public async Task NestedRegion_IsRefusedOnEverySelection_WhileTheOuterRegionStaysMaterialized()
    {
        var nested = Assert.Single(RefusedCases, program => program.Name == "v06-nested-region");
        var host = new RunHost();
        var parsed = await SourceProvenance.ParseValidAsync(nested.Deferred, host.Options);
        var outer = Assert.Single(Regions(parsed.Root));

        for (var attempt = 1; attempt <= 2; attempt++)
        {
            AssertMaterializationRefused(
                await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), host.Operations, null, null, CancellationToken.None));
            // The outer unit is self-contained: it materialized once and stays published.
            Assert.True(outer.TryGetMaterialized(out var outerBody));
            Assert.Equal(1, outer.MaterializationAttempts);
            // The inner region lives in the outer unit's materialized body, and is judged at every selection.
            var inner = Assert.Single(Regions(outerBody));
            Assert.Equal(attempt, inner.MaterializationAttempts);
            Assert.False(inner.IsMaterialized);
            Assert.Equal(1, host["a"]);
            Assert.Equal(1, host["m"]);
        }
    }

    [Fact]
    public async Task RefusedBranch_IsNeverAClauseNonMatch()
    {
        // The load-bearing clause is selected; a later clause that would match must not be tried (Q-71).
        var source =
            "G(y) = {\n" +
            "  F(1) = { " + OpenM + "\n" +
            "    X }\n" +
            "  F(n) = 99\n" +
            "  F(1)\n" +
            "}\n" +
            "G(1)\n";
        var (result, _) = await Run(source);
        AssertRefused(result, "X", "y", "X(y)", SpanOf(source, "    X }", "X"));
    }

    [Theory]
    [InlineData(OpenM, "X")]
    // A branch whose provisional body forwards: resolving it eagerly loads nothing either.
    [InlineData(OpenS, "W + Z")]
    public async Task UnselectedBranch_DoesNoModuleWork_AndIsNeverJudged(string open, string output)
    {
        var source = RootW + Family("F(0) = 0", open, output, "trace(F(0))") + "G(1), G(2)\n";
        var (result, host) = await Run(source);
        AssertValue(result, 0, 0);
        Assert.Equal(0, host.TotalFetches);
        // The classification is static: it reads the family, whichever clause a run selects.
        Assert.Equal(output == "X" ? Atoms(0) : Atoms(0, 0), host.Trace);
    }

    [Fact]
    public async Task Refusal_NeverRevisesTheEagerClassification()
    {
        // Exposure is static: decided before evaluation, and independent of what a run selected.
        var host = new RunHost();
        var parsed = await SourceProvenance.ParseValidAsync(P41 + "G(1), G(2)\n", host.Options);
        var before = Exposures(parsed.Root);
        Assert.Equal((PropertyExposure.Exported, PropertyExposure.Exported), before);
        AssertMaterializationRefused(
            await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), host.Operations, null, null, CancellationToken.None));
        Assert.Equal(before, Exposures(parsed.Root));
    }

    // ── The provisional body ────────────────────────────────────────────────

    [Fact]
    public async Task ProvisionalBody_HoldsTheForwardingsItsModulesDoNotDecide_AndLeavesWhatTheyDecideAsWritten()
    {
        var source = RootW + Family("F(0) = 0", OpenS, "W + Z", "F(1)") + "G(1), G(2)\n";
        var host = new RunHost();
        var parsed = await SourceProvenance.ParseValidAsync(source, host.Options);
        // Nothing is reported for the provisional body, and nothing is loaded for it.
        Assert.Empty(parsed.Diagnostics);
        Assert.Equal(0, host.TotalFetches);

        var (placeholder, region) = Assert.Single(Placeholders(parsed.Root));
        var sum = Assert.IsType<Expr.Binary>(Assert.Single(Assert.IsType<Algorithm.User>(placeholder).Output));
        // The root callable is lifted exactly as in an eager branch: the call W(y) over the enclosing binding.
        var lifted = Assert.IsType<Expr.Call>(sum.Left);
        Assert.Equal("W", Assert.IsType<Expr.Resolve>(lifted.Function).Name);
        Assert.Equal("y", Assert.IsType<Expr.Param>(Assert.Single(lifted.Args)).Name);
        // The synthesized call takes the reference's own span: nothing invents a location.
        Assert.Equal(SpanOf(source, "    W + Z }", "W"), lifted.Span);
        // What only the module could bind stays the name detection left, and the load directive the opaque source construct it is.
        Assert.Equal("Z", Assert.IsType<Expr.Resolve>(sum.Right).Name);
        Assert.True(LoadElaborationGuard.TryFindFirstUnresolvedLoad(placeholder, out _));
        Assert.False(region.IsMaterialized);

        // So the enclosing classification charges the parameter: the family and its reader are local-only.
        Assert.Equal(
            (PropertyExposure.LocalOnlyCapturedAncestorParameters, PropertyExposure.LocalOnlyCapturedAncestorParameters),
            Exposures(parsed.Root));
    }

    [Fact]
    public async Task SemanticModel_OfAProvisionalBodyThatForwards_KeepsEverySiteSourceBacked_AndModuleNamesIndeterminate()
    {
        var source = RootW + Family("F(0) = 0", OpenS, "W + Z", "F(1)") + "G(1), G(2)\n";
        var host = new RunHost();
        var parsed = await SourceProvenance.ParseValidAsync(source, host.Options);
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        Assert.Equal(0, host.TotalFetches);

        // The name only the module could bind is indeterminate: never unresolved, never an inferred parameter.
        var z = Assert.Single(model.FindResolutions("Z"));
        Assert.Equal(IdentifierClassification.DeferredModuleReference, z.Classification);
        Assert.Null(z.ResolvedDeclaration);
        // The lifted reference is ONE site, the name as written: the call the front end synthesized adds none,
        // and the binding it forwards is no site either.
        var w = Assert.Single(model.FindResolutions("W"), resolution => resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
        Assert.Equal(IdentifierClassification.PropertyReference, w.Classification);
        Assert.Equal(SpanOf(source, "    W + Z }", "W"), w.Occurrence.Span);
        Assert.DoesNotContain(model.IdentifierResolutions, resolution => resolution.Classification == IdentifierClassification.Unresolved);
        // Every site slices the document to the identifier written there.
        var lines = source.Split('\n');
        Assert.All(model.IdentifierResolutions, resolution =>
        {
            var span = resolution.Occurrence.Span;
            Assert.Equal(span.Start.Line, span.End.Line);
            Assert.Equal(resolution.Occurrence.Name, lines[span.Start.Line - 1][(span.Start.Column - 1)..(span.End.Column - 1)]);
        });
    }

    [Fact]
    public async Task AcceptedRegion_IsMaterializedOnceFromTheLoadedSource_NeverFromItsProvisionalView()
    {
        var source = RootW + Family("F(0) = 0", OpenS, "W + Z", "F(1)") + "G(1), G(2)\n";
        var host = new RunHost();
        var parsed = await SourceProvenance.ParseValidAsync(source, host.Options);
        var (placeholder, region) = Assert.Single(Placeholders(parsed.Root));

        for (var run = 1; run <= 2; run++)
        {
            var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), host.Operations, null, null, CancellationToken.None);
            Assert.False(result.IsError);
            Assert.Equal(1, region.MaterializationAttempts);
            Assert.Equal(1, host["s"]);
        }

        // The materialized body is its own elaboration of the loaded source: another object than the
        // placeholder's provisional view, a placeholder for nothing, and with the module member bound.
        Assert.True(region.TryGetMaterialized(out var materialized));
        Assert.NotSame(placeholder, materialized);
        Assert.Null(materialized.DeferredRegion);
        Assert.False(LoadElaborationGuard.TryFindFirstUnresolvedLoad(materialized, out _));
        // The provisional view is what it was.
        Assert.True(LoadElaborationGuard.TryFindFirstUnresolvedLoad(placeholder, out _));
    }

    [Fact]
    public async Task OpenTargetBlockInALoadBearingBranch_IsElaboratedByTheMaterializationItself()
    {
        // A block written as an open target is rooted at the prelude: its static context is ONE context, whether the
        // block is read in the placeholder or in the materialized body. The provisional resolution's views of it are
        // retracted when the eager run ends, so the materialization publishes its own; a module member the block
        // reads is bound there, and unresolved in the provisional view.
        var source =
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { K = { open { public V = { " + OpenS + "\n" +
            "          Z + 1 } }\n" +
            "      V }\n" +
            "    K }\n" +
            "  F(1)\n" +
            "}\n" +
            "G(1), G(2)\n";
        var (deferred, host) = await Run(source);
        AssertValue(deferred, 6, 6);
        Assert.Equal(1, host["s"]);
        // (No eager twin exists: a block rooted at the prelude cannot name a holder the program declares.)
    }

    [Fact]
    public async Task ProvisionalResolution_ReportsNothing_AndTheBodyIsJudgedOnlyWhenItLoads()
    {
        // K(a) = W2 is bare forwarding that cannot be supplied: a front-end error of the branch, which belongs to
        // its materialization (the module might have bound zz). The parse reports nothing.
        static string Program(string selected)
            => "W2 = zz + 1\n" +
               "G(y) = {\n" +
               "  F(0) = 0\n" +
               "  F(n) = { " + OpenS + "\n" +
               "    K(a) = W2\n" +
               "    K(1) + Z }\n" +
               "  " + selected + "\n" +
               "}\n" +
               "G(1)\n";
        var host = new RunHost();
        var parsed = await SourceProvenance.ParseValidAsync(Program("F(1)"), host.Options);
        Assert.Empty(parsed.Diagnostics);

        var (unselected, unselectedHost) = await Run(Program("F(0)"));
        AssertValue(unselected, 0);
        Assert.Equal(0, unselectedHost.TotalFetches);

        var (selected, _) = await Run(Program("F(1)"));
        var failure = Assert.IsType<RunResult.EvalFailure>(selected);
        Assert.Equal(KatLangErrorCode.UnforwardableParameter, Assert.Single(failure.Errors).Code);
    }

    /// <summary>
    /// A group the selector refuses inside a PROVISIONAL body: <c>A</c> and <c>B</c> use one another, and,
    /// with the module treated as empty, read the callables <c>X(x)</c> and <c>Y(y)</c> of the block
    /// the enclosing algorithm opens, which do not settle. The module's own <c>X</c> and <c>Y</c> take
    /// no parameters, so the materialized body is well formed.
    /// </summary>
    private static string RefusedProvisionalGroup(string row)
        => "L = { public X(x) = x\n" +
           "  public Y(y) = y }\n" +
           "W = q + 1\n" +
           "G(q) = {\n" +
           "  open L\n" +
           "  F(0) = 0\n" +
           "  F(n) = { " + OpenXy + "\n" +
           "    A = B + X\n" +
           "    B = A + Y\n" +
           "    " + row + " }\n" +
           "  R = F(1)\n" +
           "  R\n" +
           "}\n" +
           "G(1), G(2)\n";

    [Fact]
    public async Task GroupRefusedInsideAProvisionalBody_IsNotAProgramError()
    {
        // The refusal is the provisional body's alone: the program parses cleanly, and the branch, once
        // loaded, is the eager twin's.
        var selfContained = RefusedProvisionalGroup("7");
        Assert.Empty((await SourceProvenance.ParseValidAsync(selfContained, new RunHost().Options)).Diagnostics);
        var (deferred, _) = await Run(selfContained);
        AssertValue(deferred, 7, 7);
        var (eager, _) = await Run(EagerTwin(selfContained));
        AssertValue(eager, 7, 7);

        // CONSERVATIVE, never wrong: the provisional body stays the detected one, so a forwarding it
        // writes beside the refused group is not charged, and the materialization is refused where the
        // eager twin has a value. Before, the cached reader gave (2, 2).
        var forwards = RefusedProvisionalGroup("W");
        var parsed = await SourceProvenance.ParseValidAsync(forwards, new RunHost().Options);
        Assert.Empty(parsed.Diagnostics);
        // The fact is recorded where it is decided, on the region the tree holds (after every later fork): the
        // names of the refused bodies, in first-occurrence order.
        Assert.Equal(["A", "B"], Assert.Single(Regions(parsed.Root)).Structure!.UnresolvedProvisionalBodies);
        var (refused, _) = await Run(forwards);
        // W is a ROOT property: the module has nothing to do with it, and the report must not say it has. It says
        // why the forwarding was not decided before the load, and keeps the reference, the parameter and the repair.
        var error = AssertRefusedWith(refused,
            "'W' would receive the enclosing parameter 'q' implicitly. This branch's implicit arguments could not be "
            + "resolved before its module was loaded (the parameters of 'A' and 'B' cannot be decided without it), so it "
            + "passes enclosing parameters only explicitly: write W(q).",
            SpanOf(forwards, "    W }", "W"));
        Assert.DoesNotContain("through a module", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("module provides", error.Message, StringComparison.Ordinal);
        var (twin, _) = await Run(EagerTwin(forwards));
        AssertValue(twin, 2, 3);
    }

    [Fact]
    public async Task OrdinaryRefusal_KeepsTheModuleWording_AndItsRegionRecordsNoUnresolvedProvisionalBody()
    {
        // The negative control of the wording: p41's provisional body WAS resolved, so the uncharged requirement is
        // one its module decided, and the report says so.
        var source = P41 + "G(1), G(2)\n";
        var parsed = await SourceProvenance.ParseValidAsync(source, new RunHost().Options);
        Assert.Null(Assert.Single(Regions(parsed.Root)).Structure!.UnresolvedProvisionalBodies);
        var (refused, _) = await Run(source);
        var error = AssertRefused(refused, "X", "y", "X(y)", SpanOf(source, "    X }", "X"));
        Assert.Contains("implicitly through a module this branch loads on demand", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("could not be resolved before its module was loaded", error.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// The refused group inside a NESTED region. The outer branch loads the callables <c>X(x)</c> and
    /// <c>Y(y)</c> (<c>cb.kat</c>); the inner branch, which its materialization defers again, loads
    /// self-contained members of the same names (<c>xy.kat</c>). The inner placeholder is resolved
    /// provisionally inside the OUTER MATERIALIZATION's run, where the outer module's callables are real
    /// and the inner module is empty: there <c>A</c> and <c>B</c> do not settle.
    /// </summary>
    private const string NestedRefusedProvisionalGroup =
        "W = q + 1\n" +
        "G(q) = {\n" +
        "  F(0) = 0\n" +
        "  F(n) = { open 'https://modules.example/cb.kat'\n" +
        "    H(0) = 0\n" +
        "    H(k) = { " + OpenXy + "\n" +
        "      A = B + X\n" +
        "      B = A + Y\n" +
        "      W }\n" +
        "    Q = H(n)\n" +
        "    Q }\n" +
        "  R = F(1)\n" +
        "  R\n" +
        "}\n" +
        "G(1), G(2)\n";

    [Fact]
    public async Task GroupRefusedInsideANestedProvisionalBody_IsRecordedByTheMaterializationsRun_AndWordsItsRefusalTheSameWay()
    {
        var source = NestedRefusedProvisionalGroup;
        var host = new RunHost();
        var parsed = await SourceProvenance.ParseValidAsync(source, host.Options);
        Assert.Empty(parsed.Diagnostics);
        var outer = Assert.Single(Regions(parsed.Root));
        // With both modules empty nothing in the outer provisional body is refused: X and Y are names only a
        // module could bind.
        Assert.Null(outer.Structure!.UnresolvedProvisionalBodies);

        var failure = AssertMaterializationRefused(
            await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), host.Operations, null, null, CancellationToken.None));
        // The outer unit materialized; the region its body defers again was resolved provisionally in that run,
        // and its refused selection is recorded on the region the materialized tree holds.
        Assert.True(outer.TryGetMaterialized(out var outerBody));
        var inner = Assert.Single(Regions(outerBody));
        Assert.False(inner.IsMaterialized);
        Assert.Equal(["A", "B"], inner.Structure!.UnresolvedProvisionalBodies);
        var diagnostic = Assert.Single(failure.Diagnostics);
        Assert.Equal(
            DeferredModuleRegion.UnresolvedBranchForwardedEnclosingParameterMessage("q", "W", "W(q)", ["A", "B"]),
            diagnostic.Message);
        Assert.DoesNotContain("through a module", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(SpanOf(source, "      W }", "W"), diagnostic.Span);

        // The eager twin has the value.
        var (twin, _) = await Run(EagerTwin(source));
        AssertValue(twin, 2, 3);
    }

    // ── Position, and one report per binding ────────────────────────────────

    [Fact]
    public async Task FamilyWrittenInsideModuleText_IsReportedAtTheCurrentDocumentsImportSite()
    {
        // ONE COORDINATE SPACE PER RESULT: the reference `X` lies in module text, which has no location here.
        var source = $"open '{Url("outer")}'\nOuter(1), Outer(2)\n";
        var (result, host) = await Run(source);
        var quoted = $"'{Url("outer")}'";
        AssertRefused(result, "X", "y", "X(y)", SpanOf(source, $"open {quoted}", quoted));
        Assert.Equal(1, host["outer"]);
        Assert.Equal(1, host["m"]);
    }

    private const string TwoMissingBindings =
        "G(y, z) = {\n" +
        "  F(0) = 0\n" +
        "  F(n) = { open 'https://modules.example/m2.kat'\n" +
        "    T = X2 + 1\n" +
        "    X2 + T }\n" +
        "  F(1)\n" +
        "}\n" +
        "G(1, 2), G(2, 3)\n";

    [Fact]
    public async Task EveryMissingBinding_IsReportedOnce_AtTheFirstReferenceThatReceivesIt()
    {
        var source = TwoMissingBindings;
        var host = new RunHost();
        var parsed = await SourceProvenance.ParseValidAsync(source, host.Options);
        var failure = AssertMaterializationRefused(
            await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), host.Operations, null, null, CancellationToken.None));

        // One diagnostic per enclosing binding, in name order, each at the FIRST reference in source order
        // (the `X2` of `T = X2 + 1`), with the complete explicit call as the repair.
        var first = SpanOf(source, "    T = X2 + 1", "X2");
        Assert.Equal(2, failure.Diagnostics.Count);
        Assert.Equal(
            [DeferredModuleRegion.ForwardedEnclosingParameterMessage("y", "X2", "X2(y, z)"),
             DeferredModuleRegion.ForwardedEnclosingParameterMessage("z", "X2", "X2(y, z)")],
            failure.Diagnostics.Select(diagnostic => diagnostic.Message));
        Assert.All(failure.Diagnostics, diagnostic => Assert.Equal(first, diagnostic.Span));

        // The eager twin is correct, and writing the call explicitly admits the deferred program with the same value.
        var (eager, _) = await Run(EagerTwin(source));
        AssertValue(eager, 12 + 12 + 1, 23 + 23 + 1);
        var (repaired, _) = await Run(source.Replace("X2 +", "X2(y, z) +", StringComparison.Ordinal));
        AssertValue(repaired, 12 + 12 + 1, 23 + 23 + 1);
    }

    private const string BlockHeadedLoneRow =
        "G(y) = {\n" +
        "  F(0) = 0\n" +
        "  F(n) = { " + OpenM + "\n" +
        "    { public K = X }.K }\n" +
        "  F(1)\n" +
        "}\n" +
        "G(1), G(2)\n";

    private const string BlockHeadedFormula =
        "G(y) = {\n" +
        "  F(0) = 0\n" +
        "  F(n) = { " + OpenM + "\n" +
        "    { public K = X }.K + 0 }\n" +
        "  F(1)\n" +
        "}\n" +
        "G(1), G(2)\n";

    [Theory]
    [InlineData(BlockHeadedLoneRow, "    { public K = X }.K }")]
    [InlineData(BlockHeadedFormula, "    { public K = X }.K + 0 }")]
    public async Task ReferenceWithNoSpellingAsANamePath_IsRefusedAtItsOwnPosition_WithoutBeingNamed(string source, string line)
    {
        // The reference that receives the binding is headed by a block: it keeps its position, and the
        // wording names the parameter and the repair only. A position is never a condition of the refusal.
        var (deferred, _) = await Run(source);
        AssertRefusedWith(deferred, DeferredModuleRegion.UnchargedEnclosingParameterMessage("y"), SpanOf(source, line, "{ public K = X }.K"));

        var (eager, _) = await Run(EagerTwin(source));
        AssertValue(eager, 10, 20);
    }

    [Fact]
    public void RefusedBareForwardingOverABlockHead_IsItsFrontEndError_WithItsBlockElaborated()
    {
        // The row of a closed body is headed by a block and forwards to a callee that cannot be supplied
        // (Q-77): the row is left as written, and its block is still elaborated, in a reporting resolution
        // and in a provisional one alike. Before, the unprocessed block failed the resolver's reach
        // invariant with an internal error instead of leaving the report standing; a deferred branch's
        // provisional body reaches the same verdict whenever the missing parameter is a name its module binds.
        var eager = SourceProvenance.ParseAllowingDiagnostics(
            "G(y) = {\n" +
            "  F(0) = 0\n" +
            "  F(n) = { { public K = Q9 }.K }\n" +
            "  F(1)\n" +
            "}\n" +
            "G(1)\n");
        Assert.Equal(DiagnosticCode.UnforwardableParameter, Assert.Single(eager.Diagnostics).Code);

        var family = SourceProvenance.ParseAllowingDiagnostics(
            "Fam(a, 0) = a\n" +
            "Fam(0, a) = a\n" +
            "G(y) = {\n" +
            "  F(n) = { { public K = Fam }.K }\n" +
            "  F(1)\n" +
            "}\n" +
            "G(1)\n");
        Assert.Equal(DiagnosticCode.UnforwardableCallable, Assert.Single(family.Diagnostics).Code);

        // The whole-document form of the provisional state: a parse without a downloader models the program.
        var withoutModules = SourceProvenance.ParseAllowingDiagnostics(BlockHeadedLoneRow);
        Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, Assert.Single(withoutModules.Diagnostics).Code);
    }

    [Fact]
    public void Message_NamesTheReferenceTheParameterAndTheRepair()
    {
        Assert.Equal(
            "'X' would receive the enclosing parameter 'y' implicitly through a module this branch loads on demand. "
            + "A branch that loads its module on demand passes enclosing parameters to what its module provides only explicitly: write X(y).",
            DeferredModuleRegion.ForwardedEnclosingParameterMessage("y", "X", "X(y)"));
        // An argument with no simple spelling keeps the rule and names what to pass to what.
        Assert.Equal(
            "'X' would receive the enclosing parameter 'y' implicitly through a module this branch loads on demand. "
            + "A branch that loads its module on demand passes enclosing parameters to what its module provides only explicitly: "
            + "pass 'y' to 'X' as a written argument.",
            DeferredModuleRegion.ForwardedEnclosingParameterMessage("y", "X", explicitCall: null));
        // Without a reference to name, the parameter and the repair remain.
        Assert.Equal(
            "This branch would depend on the enclosing parameter 'y' implicitly through a module it loads on demand. "
            + "A branch that loads its module on demand passes enclosing parameters to what its module provides only explicitly: "
            + "pass 'y' as a written argument where the branch uses what its module provides.",
            DeferredModuleRegion.UnchargedEnclosingParameterMessage("y"));

        // A BRANCH WHOSE PROVISIONAL BODY WAS LEFT UNRESOLVED: the reference may be the program's own callable, so
        // neither form says who provides it. Each says why the forwarding was not decided before the load, naming
        // the refused bodies, and keeps the reference as written, the parameter and the repair.
        Assert.Equal(
            "'W' would receive the enclosing parameter 'q' implicitly. This branch's implicit arguments could not be resolved "
            + "before its module was loaded (the parameters of 'A' and 'B' cannot be decided without it), so it passes enclosing "
            + "parameters only explicitly: write W(q).",
            DeferredModuleRegion.UnresolvedBranchForwardedEnclosingParameterMessage("q", "W", "W(q)", ["A", "B"]));
        Assert.Equal(
            "'W' would receive the enclosing parameter 'q' implicitly. This branch's implicit arguments could not be resolved "
            + "before its module was loaded (the parameters of 'A' cannot be decided without it), so it passes enclosing "
            + "parameters only explicitly: pass 'q' to 'W' as a written argument.",
            DeferredModuleRegion.UnresolvedBranchForwardedEnclosingParameterMessage("q", "W", explicitCall: null, ["A"]));
        Assert.Equal(
            "This branch would depend on the enclosing parameter 'q' implicitly. This branch's implicit arguments could not be "
            + "resolved before its module was loaded (the parameters of 'A', 'B', and 'C' cannot be decided without it), so it "
            + "passes enclosing parameters only explicitly: pass 'q' as a written argument where the branch needs it.",
            DeferredModuleRegion.UnresolvedBranchUnchargedEnclosingParameterMessage("q", ["A", "B", "C"]));
        // The list of refused bodies is bounded like every rendered name: a long one is cut, and the repair still follows.
        var many = Enumerable.Range(0, 400).Select(index => $"Body{index}").ToArray();
        var bounded = DeferredModuleRegion.UnresolvedBranchForwardedEnclosingParameterMessage("q", "W", "W(q)", many);
        Assert.Contains("'Body0', 'Body1', ", bounded, StringComparison.Ordinal);
        Assert.DoesNotContain("'Body399'", bounded, StringComparison.Ordinal);
        Assert.EndsWith("so it passes enclosing parameters only explicitly: write W(q).", bounded, StringComparison.Ordinal);
        Assert.True(bounded.Length < ExprNameRenderer.MaxRenderedNameLength + 400);
        foreach (var message in new[]
        {
            bounded,
            DeferredModuleRegion.UnresolvedBranchForwardedEnclosingParameterMessage("q", "W", explicitCall: null, ["A"]),
            DeferredModuleRegion.UnresolvedBranchUnchargedEnclosingParameterMessage("q", ["A", "B", "C"]),
        })
        {
            Assert.DoesNotContain("through a module", message, StringComparison.Ordinal);
            Assert.DoesNotContain("module provides", message, StringComparison.Ordinal);
        }
    }

    // ── The family's provisional contribution ───────────────────────────────

    [Fact]
    public async Task FamilysProvisionalContribution_IsOneCanonicalSet_SharedByEveryDeferredBranchOfTheFamily()
    {
        var source =
            "G(y) = {\n" +
            "  F(0) = y * 0\n" +
            "  F(1) = { " + OpenM + "\n" +
            "    X }\n" +
            "  F(n) = { " + OpenS + "\n" +
            "    Z }\n" +
            "  F(1) + F(2)\n" +
            "}\n" +
            "G(1), G(2)\n";
        var host = new RunHost();
        var parsed = await SourceProvenance.ParseValidAsync(source, host.Options);
        var regions = Regions(parsed.Root);
        Assert.Equal(2, regions.Count);

        // One set for the family: the union over ALL its clauses, so the first clause's read of y is in it.
        var contribution = regions[0].Exposure!.FamilyContribution;
        Assert.True(contribution.Equals(regions[1].Exposure!.FamilyContribution));
        Assert.Same(contribution.Root, regions[1].Exposure!.FamilyContribution.Root);
        var requirement = Assert.Single(contribution.Elements);
        Assert.Equal("y", requirement.Name);
        // The owner is the scope of G's body: the level the family is written in.
        Assert.Same(regions[0].Exposure!.Scope.Parent!.PropertyScope, requirement.Owner);

        // Both branches are admitted against it.
        AssertValue(await KatLangEngine.RunAsync(source, host.Options), 15, 25);

        // A self-contained family charged nothing.
        var selfContained = await SourceProvenance.ParseValidAsync(P41 + "G(1)\n", new RunHost().Options);
        Assert.True(Assert.Single(Regions(selfContained.Root)).Exposure!.FamilyContribution.IsEmpty);
    }

    [Fact]
    public async Task FamilysProvisionalContribution_HoldsWhatTheProvisionalBodyForwards()
    {
        // No clause WRITES a read of y: the load-bearing clause forwards it to the root callable W, and
        // the provisional body holds that call, so the family charges y of the level it is written in.
        var source = RootW + Family("F(0) = 0", OpenS, "W + Z", "F(1)") + "G(1), G(2)\n";
        var parsed = await SourceProvenance.ParseValidAsync(source, new RunHost().Options);
        var region = Assert.Single(Regions(parsed.Root));
        var requirement = Assert.Single(region.Exposure!.FamilyContribution.Elements);
        Assert.Equal("y", requirement.Name);
        Assert.Same(region.Exposure!.Scope.Parent!.PropertyScope, requirement.Owner);
    }

    // ── The subset predicate, directly ──────────────────────────────────────

    [Fact]
    public void SubsetPredicate_ComparesOwnerQualifiedRequirements_NeverSpellings()
    {
        // `y` is bound at two levels: Outer's body and, shadowing it, Inner's.
        var root = SourceProvenance.ParseValid("Outer(y) = {\n  Inner(y) = y + 1\n  Inner(y)\n}\nOuter(1)").Root;
        var prelude = ElaboratedScopeLookup.CreateScope(root);
        var outerBody = Assert.Single(root.Properties, property => property.Name == "Outer").Value;
        var outer = ElaboratedScopeLookup.CreateScope(outerBody, prelude);
        var inner = ElaboratedScopeLookup.CreateScope(Assert.Single(outerBody.Properties, property => property.Name == "Inner").Value, outer);
        Assert.NotSame(outer, inner);

        var sets = new RequirementSetInterner(observations: null);
        var outerY = new Requirement("y", outer);
        var innerY = new Requirement("y", inner);
        var outerZ = new Requirement("z", outer);
        static Requirement[] Uncharged(RequirementSetInterner sets, Requirement[] contribution, Requirement[] charged)
            => [.. PropertyDependencyGraphBuilder.UnchargedRequirements(sets.From(contribution), sets.From(charged), sets).Elements];

        // The same spelling under another owner is NOT charged: a spelling-only comparison would call both subsets.
        Assert.Equal([innerY], Uncharged(sets, [innerY], [outerY]));
        Assert.Equal([outerY], Uncharged(sets, [outerY], [innerY]));
        Assert.Equal([innerY], Uncharged(sets, [innerY, outerY], [outerY, outerZ]));

        // Subsets by identity, the empty contribution included.
        Assert.Empty(Uncharged(sets, [outerY], [outerY]));
        Assert.Empty(Uncharged(sets, [innerY], [innerY, outerY]));
        Assert.Empty(Uncharged(sets, [], [outerY]));
        Assert.Empty(Uncharged(sets, [], []));
        Assert.Equal([outerY], Uncharged(sets, [outerY], []));

        // The charged set may belong to ANOTHER run's interner (the eager run's): it is adopted by its
        // elements, whose owner scopes are unchanged.
        var eager = new RequirementSetInterner(observations: null);
        Assert.Empty(PropertyDependencyGraphBuilder.UnchargedRequirements(sets.From([outerY]), eager.From([outerY, outerZ]), sets).Elements);
        Assert.Equal([innerY],
            PropertyDependencyGraphBuilder.UnchargedRequirements(sets.From([innerY]), eager.From([outerY, outerZ]), sets).Elements);
    }
}
