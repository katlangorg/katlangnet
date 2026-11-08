namespace KatLang.Tests;

/// <summary>
/// THE ROOT CLAUSE preserves a bare root ROW, never its BLOCK (S-10, F1). A block written in a preserved root row such as
/// <c>{ public K = … ⏎ 0 }.K</c> is a body of its own and is elaborated like every other body; only the row stays unlifted,
/// as <c>K</c>'s own zero-argument demand. Before the fix the signature analysis recorded the block's bodies while the
/// rewrite returned the whole row unchanged, so the evaluator ran <c>K</c>'s raw body: a wrong value, the wrong callable
/// blamed, or a lost front-end error. The reach invariant (<c>RequireEveryAnalyzedBodyRewritten</c>) now fails loudly on
/// any body the analysis records and the rewrite skips; the affected cases here would throw it if F1 came back.
/// <para>THE NAMED-HOLDER LAW: <c>{ M }.K</c> at the root behaves exactly like <c>Lib = { M }</c> followed by
/// <c>Lib.K</c> — the same front-end codes, the same evaluation outcome, the same callable blamed.</para>
/// </summary>
public class RootRowBlockHeadTests
{
    private const string Inc = "Inc(x) = x + 1\n";
    private const string Module = "https://katlang.org/s10/a.kat";

    // ── The observer ──────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// One program's outcome on the engine: <c>front &lt;sorted codes&gt;</c> for a front-end rejection, otherwise the
    /// six-route observation (<see cref="RepeatedNameConstraintTests.OnEveryRouteAsync"/>, which also requires every
    /// evaluation route to agree, host-call log included) rendered as <c>ok &lt;value&gt;</c> or
    /// <c>err &lt;code&gt;: &lt;message&gt;</c>, with the host calls (<c>tock()</c>) in brackets.
    /// </summary>
    private static async Task<string> Outcome(string source)
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("tock", static (_, _) => new Result.Atom(0))),
        };
        if (KatLangEngine.Run(source, options) is RunResult.ParseFailure failure)
            return "front " + string.Join(",", failure.Errors.Select(static error => error.Code.ToString()).Distinct().Order(StringComparer.Ordinal));
        return RepeatedNameConstraintTests.Rendered(await RepeatedNameConstraintTests.OnEveryRouteAsync(source));
    }

    /// <summary>The outcome CLASS the named-holder law compares: the kind, the codes or the value — never the receiver's display.</summary>
    private static string Class(string outcome)
        => outcome.StartsWith("err ", StringComparison.Ordinal) ? "eval " + outcome[4..outcome.IndexOf(':', StringComparison.Ordinal)]
            : outcome;

    /// <summary>The callable an arity rejection blames (<c>Property 'K'</c>), or null.</summary>
    private static string? Blamed(string outcome)
    {
        const string Marker = "Property '";
        var at = outcome.LastIndexOf(Marker, StringComparison.Ordinal);
        return at < 0 ? null : outcome[(at + Marker.Length)..outcome.IndexOf('\'', at + Marker.Length)];
    }

    // ── Appendix A: the F1 cases, each beside its named-holder control ─────────────────────────────

    /// <summary>
    /// (id, program, its named-holder control or null, the pinned outcome class or null for a control, the callable the
    /// arity rejection must blame or null). Blocks are written with one-space indentation, as in the S-10 report.
    /// </summary>
    public static TheoryData<string, string, string?, string?, string?> Cases => new()
    {
        // P01 lifted unselected branch (printed 5 before the fix); P02 is its named-holder control.
        { "P01", Inc + "{ public K = if(true, 5, Inc)\n 0 }.K", Inc + "Lib = { public K = if(true, 5, Inc)\n 0 }\nLib.K", "eval ArityMismatch", "K" },
        // P03 control: the same block in a formula row is not preserved; the root gains x.
        { "P03", Inc + "{ public K = if(true, 5, Inc)\n 0 }.K + 0", Inc + "Lib = { public K = if(true, 5, Inc)\n 0 }\nLib.K + 0", null, null },
        // P04 lone-row alias of the member, read at the root: the alias A is blamed.
        { "P04", Inc + "A = { public K = if(true, 5, Inc)\n 0 }.K\nA", Inc + "Lib = { public K = if(true, 5, Inc)\n 0 }\nA = Lib.K\nA", "eval ArityMismatch", "A" },
        // P06 chain: the block head two edges deep (printed 5); P07 is its named-holder control.
        { "P06", Inc + "{ public S = { public K = if(true, 5, Inc)\n  0 }\n 0 }.S.K", Inc + "Lib = { public S = { public K = if(true, 5, Inc)\n  0 }\n 0 }\nLib.S.K", "eval ArityMismatch", "K" },
        // P08 alias member inside the block (printed 5).
        { "P08", Inc + "{ public A = Inc\n public K = if(true, 5, A)\n 0 }.K", Inc + "Lib = { public A = Inc\n public K = if(true, 5, A)\n 0 }\nLib.K", "eval ArityMismatch", "K" },
        // P09 own inferred input inside the block (right outcome before the fix, but its block went unprocessed).
        { "P09", "{ public K = if(true, 5, y)\n 0 }.K", "Lib = { public K = if(true, 5, y)\n 0 }\nLib.K", "eval ArityMismatch", "K" },
        // P10 closed bare forwarding inside the block (blamed Q, then Inc, before the fix).
        { "P10", Inc + "{ public Q(x) = Inc\n public K = if(true, Q(3), Inc)\n 0 }.K", Inc + "Lib = { public Q(x) = Inc\n public K = if(true, Q(3), Inc)\n 0 }\nLib.K", "eval ArityMismatch", "K" },
        // P12 a second root row after the preserved one (printed 5, 7).
        { "P12", Inc + "{ public K = if(true, 5, Inc)\n 0 }.K, 7", Inc + "Lib = { public K = if(true, 5, Inc)\n 0 }\nLib.K, 7", "eval ArityMismatch", "K" },
        // P13 a sibling with a written parameter; the selected member lifts (printed 5).
        { "P13", Inc + "{ public K(y) = y\n public L = if(true, 5, Inc)\n 0 }.L", Inc + "Lib = { public K(y) = y\n public L = if(true, 5, Inc)\n 0 }\nLib.L", "eval ArityMismatch", "L" },
        // H03 lifted formula member (blamed Inc before the fix).
        { "H03", Inc + "{ public K = Inc + 0\n 0 }.K", Inc + "Lib = { public K = Inc + 0\n 0 }\nLib.K", "eval ArityMismatch", "K" },
        // H04 two collectors inside the block (lost InvalidCollectingBinding); H05 is the ordinary-definition control.
        { "H04", "C1(a, *p) = a\nC2(b, *q) = b\n{ public K = C1 + C2\n 0 }.K", "C1(a, *p) = a\nC2(b, *q) = b\nLib = { public K = C1 + C2\n 0 }\nLib.K", "front InvalidCollectingBinding", null },
        { "H05", "C1(a, *p) = a\nC2(b, *q) = b\nG = { public K = C1 + C2\n 0 }.K\nG(1, 2)", null, "front InvalidCollectingBinding", null },
        // H06 unnameable family inside the block (lost UnliftableClauseFamily); H07 is the ordinary-definition control.
        { "H06", "S(1) = 1\nS(-1) = -1\n{ public K = S + 0\n public L(x) = x\n 0 }.L", "S(1) = 1\nS(-1) = -1\nLib = { public K = S + 0\n public L(x) = x\n 0 }\nLib.L", "front UnliftableClauseFamily", null },
        { "H07", "S(1) = 1\nS(-1) = -1\nG = { public K = S + 0\n public L(x) = x\n 0 }.L\nG(1)", null, "front UnliftableClauseFamily", null },
        // H08 a sibling reads the lifted member (right outcome before the fix, but its block went unprocessed).
        { "H08", Inc + "{ public K = Inc + 0\n public L(y) = K(y) + 1\n 0 }.L", Inc + "Lib = { public K = Inc + 0\n public L(y) = K(y) + 1\n 0 }\nLib.L", "eval ArityMismatch", "L" },
        // H09 control: a member that accepts zero arguments is not preserved, so its block was always processed.
        { "H09", Inc + "{ public K = Inc + 0\n public L = K(4)\n 0 }.L", Inc + "Lib = { public K = Inc + 0\n public L = K(4)\n 0 }\nLib.L", "ok 5", null },
        // H10 unforwardable parameter inside the block (lost UnforwardableParameter).
        { "H10", Inc + "{ public K(y) = Inc\n public L(z) = z\n 0 }.L", Inc + "Lib = { public K(y) = Inc\n public L(z) = z\n 0 }\nLib.L", "front UnforwardableParameter", null },
        // H11 alias member read through a parameterized sibling (right outcome before the fix, block unprocessed).
        { "H11", Inc + "{ public A = Inc\n public L(z) = A(z) + 1\n 0 }.L", Inc + "Lib = { public A = Inc\n public L(z) = A(z) + 1\n 0 }\nLib.L", "eval ArityMismatch", "L" },
        // N01 control: a .string edge after the member is no preserved row.
        { "N01", Inc + "{ public K = Inc + 0\n 0 }.K.string", Inc + "Lib = { public K = Inc + 0\n 0 }\nLib.K.string", null, null },
        // N03 inline carrier member (blamed Inc before the fix).
        { "N03", Inc + "{ public K = { Inc + 0 }\n 0 }.K", Inc + "Lib = { public K = { Inc + 0 }\n 0 }\nLib.K", "eval ArityMismatch", "K" },
        // N04 control: a bare block row is no dot path, always rewritten.
        { "N04", Inc + "{ public K = Inc + 0\n K(2) }", null, "ok 3", null },
        // N05 control: a member that needs nothing.
        { "N05", "{ public K = 5\n 0 }.K", "Lib = { public K = 5\n 0 }\nLib.K", "ok 5", null },
        // N06 the block's own row lifts too (blamed Inc before the fix).
        { "N06", Inc + "{ public K = Inc + 0\n Inc + 0 }.K", Inc + "Lib = { public K = Inc + 0\n Inc + 0 }\nLib.K", "eval ArityMismatch", "K" },
        // N07 a family member selected through the row (NoMatchingBranch before and after; the block went unprocessed).
        { "N07", "{ public F(0) = 0\n public F(n) = n + 1\n 0 }.F", "Lib = { public F(0) = 0\n public F(n) = n + 1\n 0 }\nLib.F", null, null },
        // N08 control: two preserved rows through a named holder.
        { "N08", Inc + "B = { public K = Inc + 0\n 0 }\nB.K, B.K", null, "eval ArityMismatch", "K" },
    };

    [Theory]
    [MemberData(nameof(Cases))]
    public async Task ABlockInAPreservedRootRow_IsElaborated_LikeItsNamedHolder(string id, string source, string? holder, string? expected, string? blamed)
    {
        var outcome = await Outcome(source);
        if (expected is not null)
            Assert.True(expected == Class(outcome), $"{id}\nexpected: {expected}\nactual:   {outcome}");
        if (blamed is not null)
            Assert.True(blamed == Blamed(outcome), $"{id}: blames '{Blamed(outcome)}', expected '{blamed}'\n{outcome}");
        if (holder is not null)
        {
            var held = await Outcome(holder);
            Assert.True(Class(held) == Class(outcome), $"{id}: the named-holder law\nroot row: {outcome}\nholder:   {held}");
            Assert.True(Blamed(held) == Blamed(outcome), $"{id}: blame differs\nroot row: {outcome}\nholder:   {held}");
        }
    }

    /// <summary>
    /// The pinned arity rejection names the member the root row selects on the block, exactly as the evaluator words a
    /// receiver it renders as <c>{...}</c> (<c>{...}.S</c> for the two-edge chain).
    /// </summary>
    [Theory]
    [InlineData(Inc + "{ public K = if(true, 5, Inc)\n 0 }.K", "Property 'K' on `{...}` expects 1 parameter, but was called with 0 arguments.")]
    [InlineData(Inc + "{ public S = { public K = if(true, 5, Inc)\n  0 }\n 0 }.S.K", "Property 'K' on `{...}.S` expects 1 parameter, but was called with 0 arguments.")]
    public async Task TheArityRejection_NamesTheSelectedMember(string source, string message)
    {
        var outcome = await Outcome(source);
        Assert.True(outcome.EndsWith(message, StringComparison.Ordinal), outcome);
    }

    /// <summary>
    /// P05: nothing runs before the rejection. The raw body used to call the host operation first and then blame
    /// <c>Inc</c>; the elaborated <c>K(x)</c> is rejected at the row's zero-argument demand, so <c>tock()</c> is never
    /// called (the six-route observer pins the empty host-call log on every route).
    /// </summary>
    [Fact]
    public async Task P05_TheRejectionPrecedesEveryEffect()
    {
        var root = await RepeatedNameConstraintTests.OnEveryRouteAsync(Inc + "T = tock()\n{ public K = tock() + (Inc + 0)\n 0 }.K");
        var holder = await RepeatedNameConstraintTests.OnEveryRouteAsync(Inc + "T = tock()\nLib = { public K = tock() + (Inc + 0)\n 0 }\nLib.K");
        foreach (var observation in new[] { root, holder })
        {
            Assert.Empty(observation.HostCalls);
            Assert.Equal("eval ArityMismatch", Class(observation.Outcome));
            Assert.Equal("K", Blamed(observation.Outcome));
        }
    }

    /// <summary>N02: an <c>open</c> inside the block, in every declaration order (blamed <c>Inc</c> before the fix).</summary>
    [Fact]
    public async Task N02_AnOpenInsideTheBlock_InEveryDeclarationOrder()
    {
        string[] chunks = ["Lib = { public Member = 5 }", "Inc(x) = x + 1", "{ open Lib\n public K = Member + Inc\n 0 }.K"];
        int[][] orders = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
        foreach (var order in orders)
        {
            var source = string.Join("\n", order.Select(index => chunks[index]));
            var outcome = await Outcome(source);
            Assert.True(Class(outcome) == "eval ArityMismatch" && Blamed(outcome) == "K", $"{source}\n{outcome}");
        }
    }

    /// <summary>
    /// P11 control: the same shape as a MODULE's root row is not the program's root row, so the module's row is an
    /// ordinary formula row and the module is called with the lifted input (prints 5 before and after the fix).
    /// </summary>
    [Fact]
    public async Task P11_AModuleRootRow_IsNoProgramRootRow()
    {
        var options = new RunOptions
        {
            DownloadCode = static (url, _) => url == Module
                ? ValueTask.FromResult(Inc + "{ public K = if(true, 5, Inc)\n 0 }.K")
                : throw new InvalidOperationException(url),
        };
        var result = await KatLangEngine.RunAsync($"M = load('{Module}')\nM(1)", options);
        Assert.True(result is RunResult.Success, result is RunResult.ParseFailure failure
            ? string.Join("; ", failure.Errors.Select(static error => $"{error.Code}: {error.Message}"))
            : result.ToString());
        Assert.Equal("5", ((RunResult.Success)result).ToDisplayString().ReplaceLineEndings("\n"));
    }

    // ── Appendix B: the named-holder law, swept ──────────────────────────────────────────────────

    private const string Prelude = "Inc(x) = x + 1\nC1(a, *p) = a\nC2(b, *q) = b\nS(1) = 1\nS(-1) = -1\nTwice(f) = f(f(1))\n";

    private static readonly string[] MemberSets =
    [
        "public K = Inc + 0",
        "public K = if(true, 5, Inc)",
        "public K = C1 + C2",
        "public K = S + 0",
        "public K = y + 1",
        "public A = Inc\n public K = if(true, 5, A)",
        "public Q(x) = Inc\n public K = if(true, Q(3), Inc)",
        "public K(y) = Inc",
        "public K = 5",
        "public K = tock() + (Inc + 0)",
        "public K = Twice(Inc)",
        "public K(y) = y + 1",
    ];

    /// <summary>(the selected member, its declaration or null for <c>K</c> itself).</summary>
    private static readonly (string Member, string? Declaration)[] Selections =
    [
        ("K", null),
        ("L", "public L = 7"),
        ("L", "public L(z) = z"),
        ("L", "public L(y) = K(y) + 1"),
        ("L", "public L = K(4)"),
    ];

    /// <summary>(the root-row program's rows after the block <c>B</c>, the named holder's) for a selected member <c>P</c>.</summary>
    private static readonly (string Name, Func<string, string, string> Root, Func<string, string, string> Holder)[] Holders =
    [
        ("root row", static (block, p) => $"{block}.{p}", static (block, p) => $"Lib = {block}\nLib.{p}"),
        ("two edges", static (block, p) => $"{{ public T = {block}\n 0 }}.T.{p}", static (block, p) => $"Lib = {{ public T = {block}\n 0 }}\nLib.T.{p}"),
        ("second row", static (block, p) => $"{block}.{p}, 7", static (block, p) => $"Lib = {block}\nLib.{p}, 7"),
        ("not preserved", static (block, p) => $"{block}.{p}.string", static (block, p) => $"Lib = {block}\nLib.{p}.string"),
    ];

    /// <summary>
    /// 12 member sets × 5 selections × 4 holders = 240 pairs: every root-row program has the outcome class of its named
    /// holder, and an arity rejection blames the same callable. Non-vacuous: at least one pair per outcome class (an arity
    /// error, each of the three front-end codes, a value).
    /// </summary>
    [Fact]
    public async Task TheNamedHolderLaw_HoldsOverTheSweep()
    {
        var pairs = 0;
        var classes = new Dictionary<string, int>(StringComparer.Ordinal);
        var disagreements = new List<string>();
        foreach (var members in MemberSets)
        foreach (var (member, declaration) in Selections)
        foreach (var (name, root, holder) in Holders)
        {
            var block = "{ " + members + (declaration is null ? "" : "\n " + declaration) + "\n 0 }";
            var (rootOutcome, holderOutcome) = (await Outcome(Prelude + root(block, member)), await Outcome(Prelude + holder(block, member)));
            pairs++;
            var outcomeClass = Class(rootOutcome);
            classes[outcomeClass.StartsWith("ok ", StringComparison.Ordinal) ? "ok" : outcomeClass] =
                classes.GetValueOrDefault(outcomeClass.StartsWith("ok ", StringComparison.Ordinal) ? "ok" : outcomeClass) + 1;
            if (outcomeClass != Class(holderOutcome) || Blamed(rootOutcome) != Blamed(holderOutcome))
                disagreements.Add($"{name} / {members.ReplaceLineEndings(" ")} / {member}:\n  root row: {rootOutcome}\n  holder:   {holderOutcome}");
        }

        Assert.Equal(240, pairs);
        Assert.True(disagreements.Count == 0, string.Join("\n", disagreements));
        foreach (var required in new[] { "eval ArityMismatch", "front InvalidCollectingBinding", "front UnliftableClauseFamily", "front UnforwardableParameter", "ok" })
            Assert.True(classes.GetValueOrDefault(required) > 0, $"no pair of class '{required}': {string.Join(", ", classes)}");
    }
}
