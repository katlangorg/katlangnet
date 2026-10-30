namespace KatLang.Tests;

/// <summary>
/// Historical M4/OD-D review identities. The same value, signature, provider and diagnostic witnesses now observe authoritative Q1-Q7 equations and final closure reuse. No deleted decider, tentative-chase or repetition counter is an acceptance observation.
/// </summary>
public sealed class AliasUnifySeventhReviewRegressionTests
{
    private static async Task OkAsync(string source, string value)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(value, outcome.Value);
    }

    private static FrontEndTraversalObservations Detect(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var (_, diagnostics) = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source), observations: observations);
        Assert.Empty(diagnostics);
        return observations;
    }

    private static (Algorithm.User Body, FrontEndTraversalObservations Observations) DetectBody(string source, string name)
    {
        var observations = new FrontEndTraversalObservations();
        var detectedInput = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source), observations: observations);
        var (detected, diagnostics) = detectedInput;
        Assert.Empty(diagnostics);
        var body = Assert.IsType<Algorithm.User>(Assert.Single(detected.Properties, property => property.Name == name).Value);
        HistoricalContractAssertions.FinalInputs(detectedInput, body);
        return (body, observations);
    }

    // ── Open providers follow a written reference exactly where it becomes an alias ──

    // A = B ⏎ B = { … A } is cyclic in OD-D's lower reading, so G's `open A` provides nothing; R = C's target chase then
    // reaches C's head N through the root's `open Back` — Back.N = G.R — and returns to R: a cycle only the final reading
    // closes, so R is no alias and opens its own (empty) namespace.
    private const string FinalReadingCycleOpenedByPath = "open Back\nA = B\nB = {\n    public N = 5\n    A\n}\nBack = { public N = G.R }\n"
        + "G = {\n    open A\n    public R = C\n    C = {\n        public X = 2\n        N\n    }\n    0\n}\n";

    [Fact]
    public async Task AReferenceOnlyTheFinalReadingFindsCyclic_ProvidesNothingWhenOpened()
    {
        const string F = "F = {\n    open G.R\n    X + 0\n}\n";
        await OkAsync(FinalReadingCycleOpenedByPath + F + "F(7)", "7");
        Assert.Equal(new[] { "X" }, DetectBody(FinalReadingCycleOpenedByPath + F + "5", "F").Body.Params);
    }

    [Fact]
    public async Task AReferenceOnlyTheFinalReadingFindsCyclic_IsNoSecondProviderOfAnOpenedName()
    {
        // Other alone provides X: R's target C, which declares an X too, is no provider — no AmbiguousOpen.
        const string F = "Other = { public X = 40 }\nF = {\n    open G.R, Other\n    X + 2\n}\n";
        await OkAsync(FinalReadingCycleOpenedByPath + F + "F", "42");
        Assert.Empty(DetectBody(FinalReadingCycleOpenedByPath + F + "5", "F").Body.Params);
    }

    [Fact]
    public async Task AnAliasFormedThroughAnOpen_ReadsAReferenceOnlyTheFinalReadingFindsCyclic_AsNoProvider()
    {
        // F and G form a sibling cycle (C's Y = F), so implicit-argument resolution forms F's alias Z = X reading G's R
        // as written: R is no provider, Other alone provides X, and Z is a reference to Other.X — one identity.
        const string source = "open Back\nA = B\nB = {\n    public N = 5\n    A\n}\nBack = { public N = G.R }\n"
            + "Other = { public X = { public K = 2 } }\nSame(x, x) = 0\nF = {\n    open G.R, Other\n    Z = X\n    Same(Z, Other.X) + Z.K\n}\n"
            + "G = {\n    open A\n    public R = C\n    C = {\n        public X = { public K = 1 }\n        public Y = F\n        N\n    }\n    0\n}\nF";
        await OkAsync(source, "2");
    }

    // ── A result read from a tentative result is tentative too ──

    // `W.h` asks P's decider about A's head h, which reads h itself (W.h is h's only edge): while h is answered no, W's
    // lower verdict records the stretch A -> X.h's block, tentative. `Z.tv`'s lower verdict then follows that stretch
    // (K = P.Z returns to Z: cyclic) without reading any answer itself, so only reading the stretch makes Z's verdict
    // tentative; forgotten at the repeat, it is recomputed with h an input — Z is C's reference, C declares tv — and P
    // is P(h).
    private const string TentativeStretchReadByALowerVerdict = "X = {\n    public h = {\n        public K = P.Z\n        public K2 = 7\n    }\n}\n"
        + "P = {\n    N = {\n        open X\n        public A = h\n        0\n    }\n    W = N.A.K2\n    Z = C\n    C = {\n        public tv = 1\n        N.A.K\n    }\n    W.h + Z.tv\n}\n5";

    [Fact]
    public async Task AVerdictReadFromATentativeStretch_IsForgottenWithIt()
    {
        await OkAsync(TentativeStretchReadByALowerVerdict, "5");
        var (p, observations) = DetectBody(TentativeStretchReadByALowerVerdict, "P");
        Assert.Equal(new[] { "h" }, p.Params);
        HistoricalContractAssertions.InputWork(observations);
    }

    // ── An answer about a name the rows never use is not tentative ──

    [Fact]
    public async Task AnAnswerAboutANameTheRowsNeverUse_IsNoTentativeAnswer()
    {
        // A's head Z is asked of P's collection, whose rows never use Z: it is no input in any pass, so nothing a chase
        // records from that answer is tentative.
        const string source = "Lib = { public Z = { public K = 1 } }\nP = {\n    open Lib\n    A = Z\n    A.K + 0\n}\nP";
        await OkAsync(source, "1");
        var (p, observations) = DetectBody(source, "P");
        Assert.Empty(p.Params);
        HistoricalContractAssertions.InputWork(observations);
    }

    // ── A collection that agrees keeps its results ──

    [Fact]
    public void ACollectionThatAgrees_SettlesWhatItsChasesRead()
    {
        // S's first pass reads h itself (through R2's provider) and repeats once; the repeated pass agrees, and the
        // results its chases recorded from its answers are kept as established — never dropped by a later repeat.
        const string source = "R = B\nB = {\n    public h = S.R2\n    R\n}\nS = {\n    open R, R2\n    public R2 = C2\n    C2 = {\n        public g = 7\n        h\n    }\n    h + g\n}\nS";
        var (s, observations) = DetectBody(source, "S");
        Assert.Equal(new[] { "h" }, s.Params);
        HistoricalContractAssertions.InputWork(observations);
        Assert.True(observations.StaticQueryEvaluations.Values.Any(count => count > 1), "No dependency refinement was measured.");
    }

    // ── Detection stays linear ──

    /// <summary>W fillers and K bodies, each repeating its collection once (`open Q` with `Q = h` reads h itself).</summary>
    private static string WideRootRepeats(int bodies, int fillers, string rows = "5")
        => string.Concat(Enumerable.Range(1, fillers).Select(i => $"F{i} = 1\n"))
            + string.Concat(Enumerable.Range(1, bodies).Select(j => $"R{j} = {{\n    open Q\n    Q = h\n    h\n}}\n"))
            + rows;

    /// <summary>
    /// One body with W fillers that repeats its collection once, holding K nested bodies that each repeat theirs: the
    /// outer body's names, derived while its collection read its own answers, stay tentative after it agreed, so the
    /// first nested repeat derives them once more — from established providers, never tentative again — and no later
    /// nested repeat derives them at all.
    /// </summary>
    private static string NestedRepeatsUnderAWideRepeatingBody(int nested, int fillers, string rows = "5")
        => "R = {\n    open Q\n    Q = h\n"
            + string.Concat(Enumerable.Range(1, fillers).Select(i => $"    F{i} = 1\n"))
            + string.Concat(Enumerable.Range(1, nested).Select(j => $"    N{j} = {{\n        open Qn\n        Qn = g\n        g\n    }}\n"))
            + "    h\n}\n" + rows;

    /// <summary>
    /// K repeating bodies, each reaching one L-long root chain through a reference whose head (`Z`, opened from Lib) is
    /// first asked of the body's collection.
    /// </summary>
    private static string ChainAfterADeciderRead(int size, string rows = "5")
        => "Lib = { public Z = X1 }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"X{i} = X{i + 1}\n" : $"X{i} = {{ public K = 1 }}\n"))
            + string.Concat(Enumerable.Range(1, size).Select(j => $"R{j} = {{\n    open Q, Lib\n    Q = h\n    A = Z\n    h + A.K\n}}\n"))
            + rows;

    /// <summary>K repeating bodies, each entering one L-long root chain from inside its own decision of h.</summary>
    private static string SharedChainEnteredFromADecision(int size)
        => "Lib = { public x = 1 }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"A{i} = A{i + 1}\n" : $"A{i} = Lib\n"))
            + "X = { public h = A1 }\n"
            + string.Concat(Enumerable.Range(1, size).Select(j => $"P{j} = {{\n    N = {{\n        open X\n        public S = h\n        0\n    }}\n    N.S.h\n}}\n"))
            + "5";

    /// <summary>
    /// One decision (z, asked through `M.B.w`) whose OD-D walk reads K undecided inputs n1 … nK one after another
    /// (through `Ni = { open Xi ⏎ public A = ni ⏎ 0 }`, `Xi = { public ni = N(i+1).A }`); each ni is decided no (`Q.ni`).
    /// </summary>
    private static string DecisionReadingUndecidedInputsInTurn(int size)
        => "Y = { public z = { public w = 1 } }\nP = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"    X{i} = {{ public n{i} = N{i + 1}.A }}\n" : $"    X{i} = {{ public n{i} = {{ public z = 1 }} }}\n"))
            + "    M = {\n        open Y\n        public B = z\n        0\n    }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    N{i} = {{\n        open X{i}\n        public A = n{i}\n        0\n    }}\n"))
            + "    Q = {\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"        public n{i} = 0\n")) + "    }\n"
            + "    M.B.w\n    N1.A.z\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    Q.n{i}\n")) + "}\nP";

    [Theory]
    [InlineData("suggestion-names")]
    [InlineData("suggestion-names-under-a-repeating-body")]
    [InlineData("chain-after-a-decider-read")]
    [InlineData("shared-chain-entered-from-a-decision")]
    [InlineData("decision-reading-undecided-inputs-in-turn")]
    public async Task DetectionWork_GrowsLinearly(string shape)
    {
        // The values first (small instances), then the work at two sizes: doubling the size about doubles the work.
        (Func<int, string> Generate, Func<FrontEndTraversalObservations, long> Work, double Bound) measure;
        switch (shape)
        {
            case "suggestion-names":
                // Each repeat re-derives only its own level's names, never the W-wide root's: K doubles, W stays.
                await OkAsync(WideRootRepeats(3, 3, "R1(5) + R3(7)"), "12");
                measure = (k => WideRootRepeats(k, 1000), o => o.ContextNamesCanonicalized, 1.6);
                break;
            case "suggestion-names-under-a-repeating-body":
                await OkAsync(NestedRepeatsUnderAWideRepeatingBody(3, 3, "R(5)"), "5");
                measure = (k => NestedRepeatsUnderAWideRepeatingBody(k, 1000), o => o.ContextNamesCanonicalized, 1.6);
                break;
            case "chain-after-a-decider-read":
                await OkAsync(ChainAfterADeciderRead(3, "R1(5) + R3(7)"), "14");
                measure = (k => ChainAfterADeciderRead(k), o => o.StaticQueryEvaluationCount, 2.6);
                break;
            case "shared-chain-entered-from-a-decision":
                await OkAsync(SharedChainEnteredFromADecision(3), "5");
                measure = (SharedChainEnteredFromADecision, o => o.StaticQueryEvaluationCount, 2.6);
                break;
            default:
                await OkAsync(DecisionReadingUndecidedInputsInTurn(3), "S[1, 1, 0, 0, 0]");
                measure = (DecisionReadingUndecidedInputsInTurn, o => o.StaticQueryEvaluationCount, 2.6);
                break;
        }

        var small = measure.Work(Detect(measure.Generate(100)));
        var large = measure.Work(Detect(measure.Generate(200)));
        var ratio = (double)large / small;
        Assert.True(ratio < measure.Bound, $"Doubling the size grew the detection work {ratio:F2}x ({small} -> {large}).");
    }
}
