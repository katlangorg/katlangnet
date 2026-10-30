namespace KatLang.Tests;

/// <summary>
/// Historical M4 review identities, now observing the unified compiler. Source cases retain six-route value, identity and diagnostic controls. Inference cases inspect Q6/Q7 and prove that final reads add no evaluations. Complexity cases measure actual query computations, contextual admission and immutable index builds. Inconsistent inference is the approved static A1 rejection.
/// </summary>
public sealed class AliasUnifyThirdReviewRegressionTests
{
    private static async Task<SixRouteAgreement.Observation> OkAsync(string source, string value)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(value, outcome.Value);
        return outcome;
    }

    private static IReadOnlyDictionary<string, Algorithm> Kinds(string source)
        => SourceProvenance.ParseValid(source).Root.Properties.ToDictionary(static p => p.Name, static p => p.Value);

    private static Algorithm MemberOf(Algorithm owner, string name)
        => Assert.Single(owner.Properties, property => property.Name == name).Value;

    // ── A reference's head is answered by each level's own parameter bindings ──

    [Theory]
    [InlineData("G(x)")]
    [InlineData("G(y)")]
    public async Task AReferencesHead_IsTheParameterOfItsOwnScope_WhateverTheSiteShadows(string site)
    {
        // A = x is a runtime reference to F's x, so `A.W` is a MAY fallback: G's closed list checks nothing.
        var source = $"F(x) = {{\n    A = x\n    {site} = A.W + 0\n    G(5)\n}}\nF({{ public W = 9 }})";
        await OkAsync(source, "9");
        Assert.True(Assert.IsType<Algorithm.Alias>(MemberOf(Kinds(source)["F"], "A")).HasRuntimeTarget);
    }

    [Theory]
    [InlineData("    S(q) = N.A.Y + q\n    N.A.X + h + S(0)\n", "112")]
    [InlineData("    S(q) = N.A.Y + q\n    h + S(0)\n", "107")]
    public async Task ABodysOwnInferredInput_DecidesItsNestedReferences_BeforeAndAfterItsCollectionPass(string rows, string value)
    {
        // A's head h is P's inferred input (the owner walk precedes N's open), so A is a runtime reference and `.Y`
        // is a MAY fallback; what P's collection pass read before h existed is never reused.
        var source = "X(v) = 1000\nV = {\n    public X = 5\n    public Y = 7\n    100\n}\nLib = { public h = { public X = 1 } }\n"
            + "P = {\n    N = {\n        open Lib\n        public A = h\n        0\n    }\n" + rows + "}\nP(V)";
        await OkAsync(source, value);
    }

    [Theory]
    [InlineData("U = {\n    open Q.Sub\n    R.K\n}\nV(z) = Q.Sub.R.W\n")]
    [InlineData("V(z) = Q.Sub.R.W\nU = {\n    open Q.Sub\n    R.K\n}\n")]
    public async Task ABodyReachedThroughAnOpenOrAMemberPath_AnswersItsOwnersParameters_InEveryOrder(string readers)
        => await OkAsync("p = { public K = 1 }\nQ(p) = {\n    public Sub = {\n        public R = p\n        0\n    }\n    0\n}\n" + readers + "5", "5");

    [Theory]
    [InlineData("    G(x) = A.K + 0\n    H(y) = A.W + 0\n")]
    [InlineData("    H(y) = A.W + 0\n    G(x) = A.K + 0\n")]
    public async Task ASiteShadowingAParameter_LeavesNoVerdictForOtherSites_InEveryOrder(string sites)
        => await OkAsync("x = { public K = 1 }\nArg = {\n    public K = 2\n    public W = 9\n}\nF(x) = {\n    A = x\n" + sites + "    G(5) + H(6)\n}\nF(Arg)", "11");

    [Fact]
    public async Task AnOpenPathIntoAParameterizedBody_OpensItsRuntimeReferenceAsItsOwnNamespace()
    {
        // M is a runtime reference to Q's parameter p, its own (empty) namespace (OD-C): the closed F declares no K.
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("p = { public K = 1 }\nQ(p) = {\n    public M = p\n    0\n}\nF(z) = {\n    open Q.M\n    K\n}\nF(1)");
        Assert.Equal("parse", outcome.Kind);
        Assert.StartsWith("UndeclaredIdentifier: Identifier 'K'", outcome.Errors[0], StringComparison.Ordinal);

        // A static member of the same body still opens its target.
        await OkAsync("Lib = { public K = 1 }\nQ(p) = {\n    public M = Lib\n    0\n}\nF(z) = {\n    open Q.M\n    K\n}\nF(1)", "1");
    }

    // ── A chase during detection sees the inputs an enclosing body infers before they are recorded ──

    private const string OpenedH = "X = {\n    public h = {\n        public K = 1\n        public Z = 2\n    }\n}\n";
    private const string LibInferringH = "Lib = {\n    public N = {\n        open X\n        public R = h\n        0\n    }\n    h + 0\n}\n";

    [Theory]
    [InlineData(OpenedH + LibInferringH + "F(z) = Lib.N.R.W\n5")]
    [InlineData(OpenedH + "F(z) = Lib.N.R.W\n" + LibInferringH + "5")]
    [InlineData("Lib = {\n    public N = {\n        public R = h\n        0\n    }\n    h + 0\n}\nF(z) = Lib.N.R.W\n5")]
    public async Task AnInputANavigatedBodyInfers_IsTheParameterItsNestedReferenceNames(string source)
    {
        // Lib's row uses h, which nothing Lib sees declares or opens, so Lib infers h, and R = h names that input (the
        // owner walk precedes N's open): a runtime reference, so the closed F's `.W` is a MAY fallback.
        await OkAsync(source, "5");
    }

    [Fact]
    public async Task ANameTheBodyDoesNotInfer_IsProvidedByTheNearerOpen()
    {
        // Lib's rows do not use h, so R names the h `open X` provides: X.h has no W, and the closed F reports it.
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(
            OpenedH + "Lib = {\n    public N = {\n        open X\n        public R = h\n        0\n    }\n    0\n}\nF(z) = Lib.N.R.W\n5");
        Assert.Equal("parse", outcome.Kind);
        Assert.StartsWith("UndeclaredIdentifier: Property 'W' was not found on `Lib.N.R`", outcome.Errors[0], StringComparison.Ordinal);

        // A member name the rows reach structurally (`Q.h`) is no inferred input either, so A is X's h.
        await OkAsync(OpenedH + "P = {\n    N = {\n        open X\n        public A = h\n        0\n    }\n    Q = { public h = 5 }\n    N.A.Z + Q.h\n}\nP", "7");
    }

    // The detector-only cases below read the collected body's signature and the collection's own observations.
    private static (Algorithm.User Body, FrontEndTraversalObservations Observations) DetectBody(string source, string name)
    {
        var observations = new FrontEndTraversalObservations();
        var detectedInput = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source), observations: observations);
        var (detected, diagnostics) = detectedInput;
        Assert.Empty(diagnostics);
        var body = Assert.IsType<Algorithm.User>(MemberOf(detected, name));
        HistoricalContractAssertions.FinalInputs(detectedInput, body);
        return (body, observations);
    }

    [Fact]
    public void ABodysCollection_DecidesAnInputItsRowsUseBareLater_WhenAChaseAsks()
    {
        // While P collects its inputs, A = h names P's input h (P's row uses it bare after `N.A.Z`, and nothing P sees
        // declares or opens it), so `N.A.Z` is a MAY fallback and P infers Z too — one decision, no repeated pass.
        var (p, observations) = DetectBody(OpenedH + "P = {\n    N = {\n        open X\n        public A = h\n        0\n    }\n    N.A.Z + h\n}\nP", "P");
        Assert.Equal(new[] { "Z", "h" }, p.Params);
        HistoricalContractAssertions.InputWork(observations);
    }

    private const string FallbackInputsLib = "X = {\n    public h = { public Z = 2 }\n    public Z = { public Q = 3 }\n}\n";

    private static string FallbackInputsBody(string rows)
        => FallbackInputsLib + "P = {\n    N = {\n        open X\n        public A = h\n        public B = Z\n        0\n    }\n" + rows + "}\nP";

    [Theory]
    [InlineData("    5.h + N.A.Z\n", new[] { "h", "Z" }, 0L)]
    [InlineData("    5.h + N.A.Z + N.B.Q\n", new[] { "h", "Z", "Q" }, 0L)]
    [InlineData("    N.B.Q + N.A.Z + 5.h\n", new[] { "Q", "Z", "h" }, 3L)]
    [InlineData("    N.A.Z\n    5.h\n", new[] { "Z", "h" }, 1L)]
    [InlineData("    5.h\n", new[] { "h" }, 0L)]
    public void AnInputABodyInfersOnlyAsAFallbackName_IsKnownToItsChases_InEveryRowOrder(string rows, string[] inputs, long decisions)
    {
        // `5.h` makes h P's input, so A = h names it and A's `.Z` is a MAY fallback, which makes Z an input and B's `.Q`
        // one too: a name the pass collected before a chase asks is known, and one it collects later is decided when
        // asked (`N.B.Q` first decides Z, which first decides h) — never a pass that read a wrong answer.
        var (p, observations) = DetectBody(FallbackInputsBody(rows), "P");
        Assert.Equal(inputs, p.Params);
        // `decisions` preserves the historical theory identity; the old decider no longer runs.
        _ = decisions;
        HistoricalContractAssertions.InputWork(observations);
    }

    // `h` is P's input (`5.h`), so C's head h is P's parameter and R = C is a reference to the carrier C, which declares W:
    // `R.W` reads C's W and W is no input, so N's Z is L2's W and `N.Z.V` reads its V. Read without h, R's chase passed
    // L.h back to R (OD-D), which made W an input; and W known as an input made V one.
    private const string InputThatBreaksACycle =
        "Inc(n) = n + 1\nL = { public h = P.R }\nL2 = { public W = { public V = 2 } }\nP = {\n    public R = C\n    C = {\n        open L\n        public W = 1\n        h\n    }\n"
        + "    N = {\n        open L2\n        public Z = W\n        0\n    }\n";

    [Theory]
    [InlineData("    5.h + R.W + N.Z.V\n")]
    [InlineData("    R.W + N.Z.V + 5.h\n")]
    public async Task AnInputThatDecidesWhetherAReferenceCycles_GivesTheOneSignatureItsCollectionAgreesWith(string rows)
    {
        await OkAsync(InputThatBreaksACycle + rows + "}\nP(Inc)", "9");
        var (p, observations) = DetectBody(InputThatBreaksACycle + rows + "}\nP", "P");
        Assert.Equal(new[] { "h" }, p.Params);
        HistoricalContractAssertions.InputWork(observations);
    }

    [Fact]
    public async Task ABodyWhoseOpenReadsItsOwnInput_IsRepeatedUntilItsCollectionAgrees()
    {
        // S's `open R2` provides what R2 = C2 is, and C2's head h is S's own input — decided by S's rule, final open
        // providers included: `open R` is OD-D cyclic (R -> B -> R) and provides nothing, so S infers h, C2 is a carrier
        // and R2 provides its g. Deciding h read itself (through R2's provider) and was answered no until decided, so
        // one repeated pass, seeded with h, confirms S(h).
        const string source = "R = B\nB = {\n    public h = S.R2\n    R\n}\nS = {\n    open R, R2\n    public R2 = C2\n    C2 = {\n        public g = 7\n        h\n    }\n    h + g\n}\n";
        await OkAsync(source + "S(10)", "17");
        var (s, observations) = DetectBody(source + "S", "S");
        Assert.Equal(new[] { "h" }, s.Params);
        HistoricalContractAssertions.InputWork(observations);
    }

    /// <summary>
    /// K references, each naming an input of P that only the previous one's fallback reveals, in REVERSE row order: the
    /// rows that reveal an input come after the chases that ask for it.
    /// </summary>
    private static string RevealedInputChain(int size)
        => "X = {\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    public h{i} = {{ public h{i + 1} = 1 }}\n")) + "}\nP = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    N{i} = {{\n        open X\n        public A = h{i}\n        0\n    }}\n"))
            + string.Concat(Enumerable.Range(1, size).Reverse().Select(i => $"    N{i}.A.h{i + 1}\n"))
            + "    5.h1\n}\nP";

    [Fact]
    public void AChainOfInputsEachRevealingTheNext_IsDecidedInLinearWork()
    {
        // Every h{i} is an input; deciding the first asked decides each earlier one first, once, so the collection
        // walks the rows once and decides each input at most twice (once abandoned, once made) — no repeated pass.
        static (FrontEndTraversalObservations Observations, int Inputs) Detect(int size)
        {
            var (p, observations) = DetectBody(RevealedInputChain(size), "P");
            return (observations, p.Params.Count);
        }

        var (small, smallInputs) = Detect(200);
        var (large, largeInputs) = Detect(400);
        Assert.Equal(201, smallInputs);
        Assert.Equal(401, largeInputs);
        HistoricalContractAssertions.InputWork(small);
        HistoricalContractAssertions.InputWork(large);
        var ratio = (double)large.StaticQueryEvaluationCount / small.StaticQueryEvaluationCount;
        Assert.True(ratio < 2.2, $"Doubling the chain grew authoritative query work {ratio:F2}x ({small.StaticQueryEvaluationCount} -> {large.StaticQueryEvaluationCount}).");
    }

    [Fact]
    public async Task ABodyWhoseInputsHaveNoConsistentAnswer_EndsItsRepetition_WithinItsBound()
    {
        // m iff n, and n iff not m: approved A1 rejects the unresolved equations statically.
        const string libraries = "L = { public m = P.R }\nL2 = { public n = { public m = 1 } }\n";
        const string body = "P = {\n    public R = C\n    C = {\n        open L\n        public n = 1\n        m\n    }\n"
            + "    N = {\n        open L2\n        public S = n\n        0\n    }\n    R.n + N.S.m\n}\n";
        foreach (var declarations in new[] { libraries + body, body + libraries,
            "L2 = { public n = { public m = 1 } }\n" + body + "L = { public m = P.R }\n" })
        {
            var source = declarations + "5";
            var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
            var observations = new FrontEndTraversalObservations();
            var detected = ParameterDetector.DetectPrevalidated(syntax, observations: observations);
            var diagnostic = Assert.Single(detected.Diagnostics);
            Assert.Equal(DiagnosticCode.SelfDependentInferredParameters, diagnostic.Code);
            Assert.Contains("classification is circular (n, m)", diagnostic.Message, StringComparison.Ordinal);
            Assert.Equal(syntax.Properties.Single(property => property.Name == "P").FirstDeclarationSpan, diagnostic.Span);
            Assert.InRange(observations.StaticQueryEvaluationCount, 1, 2_000);
            Assert.Contains(observations.StaticQueryAnswers, pair => pair.Key.Kind == StaticQueryKind.Inputs
                && pair.Value == StaticFactKind.Unknown);
            var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.Equal("parse", outcome.Kind);
            Assert.StartsWith("SelfDependentInferredParameters:", Assert.Single(outcome.Errors), StringComparison.Ordinal);
            Assert.Empty(outcome.HostCalls);
        }
        // Explicit m breaks the dependency without declaring a colliding n in the enclosing owner.
        await OkAsync(libraries + body.Replace("P =", "P(m) =", StringComparison.Ordinal) + "P(8)", "2");
        await OkAsync("P = x + 1\nP(4)", "5"); // ordinary inferred input
        await OkAsync("A = B\nB = A\n5", "5"); // benign target cycle, no unresolved inference
    }

    // Fifth review: X.h names P.N.A, whose head h is P's own input (P's row uses it bare), so X.h is a runtime
    // reference and the closed G's `X.h.W` is a MAY fallback. Deciding h reads h itself (through P's `open N.A`), and
    // the chase run under that first answer passed X.h, declared outside P: the repeat forgets that verdict too, so
    // G's check sees X.h's own chase in every order.
    private const string OutsideVerdictX = "X = {\n    public h = P.N.A\n}\n";
    private const string OutsideVerdictP = "P = {\n    open N.A\n    public N = {\n        open X\n        public A = h\n        0\n    }\n";

    [Theory]
    [InlineData(OutsideVerdictX + OutsideVerdictP + "    G(z) = X.h.W + 0\n    h + 0\n}\n5")]
    [InlineData(OutsideVerdictX + OutsideVerdictP + "    h + 0\n}\nG(z) = X.h.W + 0\n5")]
    [InlineData(OutsideVerdictX + "G(z) = X.h.W + 0\n" + OutsideVerdictP + "    h + 0\n}\n5")]
    public async Task AnAnswerReadOutsideTheCollectedBody_IsForgottenBeforeItsCollectionRepeats(string source)
        => await OkAsync(source, "5");

    /// <summary>
    /// S opens R1 = h and RK = zK, and N0..N(K-1) chain the inputs h -> z1 -> ... -> zK, written in REVERSE row order:
    /// deciding h reads h itself (through `open R1`), and RK's verdict decides the chain under that first answer.
    /// </summary>
    private static string SelfReadBeforeAReverseChain(int size)
        => "X = {\n    public h = { public z1 = 1 }\n" + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"    public z{i} = {{ public z{i + 1} = 1 }}\n")) + "}\n"
            + $"S = {{\n    open R1, R{size}\n    R1 = h\n    R{size} = z{size}\n"
            + "    N0 = {\n        open X\n        public A = h\n        0\n    }\n"
            + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"    N{i} = {{\n        open X\n        public A = z{i}\n        0\n    }}\n"))
            + "    h + 0\n"
            + string.Concat(Enumerable.Range(1, size).Reverse().Select(i => $"    N{i - 1}.A.z{i}\n"))
            + "}\n5";

    [Theory]
    [InlineData(3)]
    [InlineData(12)]
    public async Task ARepeatedPass_DecidesEveryOtherInputOnDemand_AfterAWrongSelfRead(int size)
    {
        // The first pass keeps h and LOSES the chain decided under h's first answer. The repeated pass is seeded with h
        // and decides z1 ... zK on demand again (deciding zK then reads zK itself through `open RK`, so one more pass,
        // seeded with every input, confirms): a chain lost this way, each link reading only the one before it, costs
        // repetitions that never grow with the chain — a pass that kept its first answers would have S(h), one that
        // answered only by its seeds one more link per pass. (A chain COLLECTED wrongly under a wrong self-read loses one
        // link per pass whatever its links read, its seeds never decided again, and a lost one whose links read their
        // successors first is regained one link per pass: the recorded limit of SEMANTIC-ALIGNMENT (12).)
        var source = SelfReadBeforeAReverseChain(size);
        await OkAsync(source, "5");
        var (s, observations) = DetectBody(source, "S");
        Assert.Equal(new[] { "h" }.Concat(Enumerable.Range(1, size).Reverse().Select(i => $"z{i}")), s.Params);
        HistoricalContractAssertions.InputWork(observations);
    }

    /// <summary>K opens of references to the body's own bare inputs: <c>open R1, …, RK</c>, <c>Ri = hi</c>, rows <c>hi</c>.</summary>
    private static string OpensOfOwnInputs(int size)
        => "P = {\n    open " + string.Join(", ", Enumerable.Range(1, size).Select(i => $"R{i}")) + "\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    R{i} = h{i}\n"))
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    h{i}\n"))
            + "}\nP";

    [Fact]
    public void OpensOfReferencesToTheBodysOwnInputs_ResolveEachTargetABoundedNumberOfTimes()
    {
        // Each hi's decision reads the body's whole provider list while it is being resolved; an abandoned resolution
        // resumes at the next target it had not committed, so each target is resolved a bounded number of times in
        // each of the three provider strata (one repeated pass, seeded with every hi, settles the providers).
        static (FrontEndTraversalObservations Observations, int Inputs) Detect(int size)
        {
            var (p, observations) = DetectBody(OpensOfOwnInputs(size), "P");
            return (observations, p.Params.Count);
        }

        var (small, smallInputs) = Detect(100);
        var (large, largeInputs) = Detect(200);
        Assert.Equal(100, smallInputs);
        Assert.Equal(200, largeInputs);
        HistoricalContractAssertions.InputWork(small);
        HistoricalContractAssertions.InputWork(large);
        Assert.InRange(small.StaticOpenTargetEvaluations, 100, 9 * 100);
        Assert.InRange(large.StaticOpenTargetEvaluations, 200, 9 * 200);
    }

    /// <summary>
    /// One name n with K fallback edges <c>Ni.A.n</c>, each receiver headed by a different name mi that P does not infer
    /// (it is used only as <c>Q.mi</c>, a member Q declares), asked first by <c>N0.B.z</c> (B = n).
    /// </summary>
    private static string EdgesReadingUndecidedInputs(int size)
        => "X = {\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    public m{i} = {{ public n = 1 }}\n")) + "}\n"
            + "Q = {\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    public m{i} = 0\n")) + "}\n"
            + "P = {\n    N0 = {\n        open X\n        public B = n\n        0\n    }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    N{i} = {{\n        open X\n        public A = m{i}\n        0\n    }}\n"))
            + "    N0.B.z\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    N{i}.A.n\n"))
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    Q.m{i}\n"))
            + "}\nP";

    [Fact]
    public void FallbackEdgesEachReadingAnUndecidedInput_AreEachExaminedABoundedNumberOfTimes()
    {
        // Deciding n examines its K edges; each edge's receiver reads an undecided mi, which is decided first, and the
        // decision resumes AT that edge, never at the first: every edge is examined at most twice.
        static (FrontEndTraversalObservations Observations, IReadOnlyList<string> Inputs) Detect(int size)
        {
            var (p, observations) = DetectBody(EdgesReadingUndecidedInputs(size), "P");
            return (observations, p.Params);
        }

        var (small, smallInputs) = Detect(100);
        var (large, largeInputs) = Detect(200);
        Assert.Equal(new[] { "z" }, smallInputs);
        Assert.Equal(new[] { "z" }, largeInputs);
        HistoricalContractAssertions.InputWork(small);
        HistoricalContractAssertions.InputWork(large);
        Assert.True((double)large.StaticQueryEvaluationCount / small.StaticQueryEvaluationCount < 2.6);
    }

    // Sixth review: Y = X.h is chased while P collects, from X.h's verdict recorded under P's first answer for h; reading
    // that verdict makes Y's own verdict tentative too, so the repeat forgets both and G's check sees Y's own chase.
    private const string ReadFromATentativeVerdictX = "X = {\n    public h = P.N.A\n}\n";
    private const string ReadFromATentativeVerdictP = "P = {\n    open N.A\n    public N = {\n        open X\n        public A = h\n        0\n    }\n";

    [Theory]
    [InlineData(ReadFromATentativeVerdictX + "Y = X.h\n" + ReadFromATentativeVerdictP + "    h + Y.Q\n}\nG(z) = Y.W + 0\n5")]
    [InlineData(ReadFromATentativeVerdictX + "Y = X.h\n" + ReadFromATentativeVerdictP + "    G(z) = Y.W + 0\n    h + Y.Q\n}\n5")]
    [InlineData(ReadFromATentativeVerdictX + ReadFromATentativeVerdictP + "    h + Y.Q\n}\nY = X.h\nG(z) = Y.W + 0\n5")]
    public async Task AChaseResultReadFromATentativeOne_IsForgottenWithIt_InEveryOrder(string source)
        => await OkAsync(source, "5");

    // Sixth review: the root's h is decided through a read of itself (R2's chase), so under its first answer R2 opens its
    // own empty namespace; the repeated pass, seeded with h, opens C2, which provides `tally`.
    private const string SuggestionAfterARepeat = "open R, R2\nR = B\nB = {\n    public h = R2\n    R\n}\nR2 = C2\nC2 = {\n    public tally = 7\n    h\n}\nh + Tally";

    [Fact]
    public void ARepeatedPass_SuggestsFromTheProvidersItResolves()
    {
        var observations = new FrontEndTraversalObservations();
        var (_, diagnostics) = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(SuggestionAfterARepeat), observations: observations);
        Assert.Empty(diagnostics);
        HistoricalContractAssertions.InputWork(observations);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(SuggestionAfterARepeat));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UnresolvedImplicitParams, error.Code);
        Assert.Contains("Did you mean 'tally' instead of 'Tally'?", error.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// K bodies, each reading its own input h through <c>open Q</c> with <c>Q = h</c>, and each reading one L-long root
    /// chain <c>A1 = A2</c> … <c>AL = Lib</c>; <paramref name="rows"/> are the root's rows.
    /// </summary>
    private static string RepeatingBodiesReadingOneChain(int size, string rows = "5")
        => "Lib = { public x = 1 }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"A{i} = A{i + 1}\n" : $"A{i} = Lib\n"))
            + string.Concat(Enumerable.Range(1, size).Select(i => $"R{i} = {{\n    open Q\n    Q = h\n    h + A1.x\n}}\n"))
            + rows;

    [Fact]
    public async Task BodiesThatRepeatTheirCollection_KeepTheChaseResultsReadFromDeclarationsAlone()
    {
        // Each Ri repeats its collection once (deciding h reads h itself through `open Q`) and forgets only what read its
        // answers — Q's verdict, its own providers — so the chain A1 … AL every Ri reads is chased once, not once per Ri.
        await OkAsync(RepeatingBodiesReadingOneChain(3, "R1(5) + R3(7)"), "14");
        Assert.Equal(new[] { "h" }, DetectBody(RepeatingBodiesReadingOneChain(3), "R2").Body.Params);

        static FrontEndTraversalObservations Detect(int size)
        {
            var observations = new FrontEndTraversalObservations();
            var (_, diagnostics) = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(RepeatingBodiesReadingOneChain(size)), observations: observations);
            Assert.Empty(diagnostics);
            return observations;
        }

        var small = Detect(100);
        var large = Detect(200);
        HistoricalContractAssertions.InputWork(small);
        HistoricalContractAssertions.InputWork(large);
        var ratio = (double)large.StaticQueryEvaluationCount / small.StaticQueryEvaluationCount;
        Assert.True(ratio < 2.6, $"Doubling the bodies and the chain grew the lookup work {ratio:F2}x ({small.StaticQueryEvaluationCount} -> {large.StaticQueryEvaluationCount}).");
    }

    // ── OD-D: a body whose target chase returns in either reading is no alias ──

    private const string FinalReadingCycleDeclarations = "Back = { public N = G.Z }\nG = {\n    open A\n    public Z = N\n    0\n}\n";
    private const string LowerCyclicReference = "A = B\nB = {\n    public N = 5\n    A\n}\n";

    [Theory]
    [InlineData("open Back\n" + LowerCyclicReference + FinalReadingCycleDeclarations)]
    [InlineData("open Back\n" + FinalReadingCycleDeclarations + LowerCyclicReference)]
    public async Task ACycleOnlyTheFinalProvidersClose_FormsNoAlias_InEveryOrder(string declarations)
    {
        // A is OD-D cyclic, so `open A` provides nothing and Z's N is Back.N, whose row reads Z back: neither forms
        // an alias, so no static alias cycle reaches evaluation, and two reads of Z share Z's own identity.
        var source = declarations + "Same(x, x) = 0\nSame(G.Z, G.Z)";
        await OkAsync(source, "0");
        var kinds = Kinds(source);
        Assert.IsNotType<Algorithm.Alias>(MemberOf(kinds["G"], "Z"));
        Assert.IsNotType<Algorithm.Alias>(MemberOf(kinds["Back"], "N"));

        // A reference entering that cycle is no alias either: its identity is its own.
        var entering = await SixRouteAgreement.OnEveryRouteAsync(declarations + "W = G.Z\nSame(x, x) = 0\nSame(W, G.Z)");
        Assert.Equal("err", entering.Kind);
        Assert.Contains("Repeated bind equality requires the same callable identity", entering.Errors[0], StringComparison.Ordinal);
    }

    private const string MemberPathThroughACyclicReceiver = "A = B\nB = {\n    public X = D\n    A\n}\nD = {\n    public Q = 7\n    A.X\n}\nE = D\n";

    [Fact]
    public async Task AMemberPathThroughAReceiverTheLowerReadingFollows_ClassifiesAlikeInBothTwins()
    {
        // The lower reading follows A to B, whose X is D: E's target chase E -> D -> A.X -> D returns, so E is no
        // alias: each E() reads D's one cached value, and E and D are distinct identities.
        var calls = await OkAsync("X(v) = tick()\n" + MemberPathThroughACyclicReceiver + "E(), E()", "S[1, 1]");
        Assert.Equal(new[] { "tick#1" }, calls.HostCalls);
        Assert.IsType<Algorithm.User>(Kinds("X(v) = 0\n" + MemberPathThroughACyclicReceiver + "E")["E"]);

        var identity = await SixRouteAgreement.OnEveryRouteAsync("X(v) = 0\n" + MemberPathThroughACyclicReceiver + "Same(x, x) = 0\nSame(E, D)");
        Assert.Equal("err", identity.Kind);
        Assert.Contains("Repeated bind equality requires the same callable identity", identity.Errors[0], StringComparison.Ordinal);
    }

    // ── The resolver's chases share one level per navigated body and one provider per open target ──

    private static (Algorithm Root, FrontEndTraversalObservations Observations, int Contexts) ObserveResolution(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var detectedInput = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source), observations: observations);
        var (detected, detectionDiagnostics) = detectedInput;
        Assert.Empty(detectionDiagnostics);
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detectedInput, observations, diagnostics);
        Assert.Empty(diagnostics);
        return (resolved, observations, detectedInput.Operation!.Queries.LocalContextCount);
    }

    /// <summary>An L-long reference chain declared inside <c>Lib</c>, reached by K aliases <c>B{j} = Lib.A1</c> (or K blocks opening it).</summary>
    private static string NavigatedChain(int size, bool opens)
        => "Lib = {\n" + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"    public A{i} = A{i + 1}\n")) + $"    public A{size} = {{ public x = 1 }}\n}}\n"
            + string.Concat(Enumerable.Range(0, size).Select(j => opens ? $"R{j} = {{\n    open Lib.A1\n    x + 0\n}}\n" : $"B{j} = Lib.A1\n"))
            + (opens ? "R0" : "B0.x");

    /// <summary>W opened block members and K = W aliases <c>R{j} = M{j}</c> of them.</summary>
    private static string OpenedMemberAliases(int size)
        => "open Lib\nLib = {\n" + string.Concat(Enumerable.Range(0, size).Select(i => $"    public M{i} = {{ public x = {i} }}\n")) + "}\n"
            + string.Concat(Enumerable.Range(0, size).Select(j => $"R{j} = M{j}\n"))
            + "R0.x";

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AChainInsideANavigatedBody_BuildsItsLevelsOnce_HoweverManyChasesReachIt(bool opens)
    {
        var small = ObserveResolution(NavigatedChain(50, opens));
        var large = ObserveResolution(NavigatedChain(100, opens));
        Assert.InRange(small.Contexts, 1, 6 * 50);
        Assert.InRange(large.Contexts, 1, 6 * 100);
        Assert.InRange(small.Observations.StaticSyntaxIndexBuilds, 1, 6 * 50);
        Assert.InRange(large.Observations.StaticSyntaxIndexBuilds, 1, 6 * 100);
    }

    [Fact]
    public void AnOpenedProvider_IsResolvedOnce_HoweverManyAliasesReadItsMembers()
    {
        foreach (var size in new[] { 50, 200 })
        {
            var measured = ObserveResolution(OpenedMemberAliases(size));
            var observations = measured.Observations;
            Assert.Equal(3, observations.StaticOpenTargetComputations); // one written target, three OD-D strata
            Assert.Equal(6, observations.StaticOpenTargetEvaluations); // Unknown then conclusive in each stratum
            Assert.Equal(1, observations.StaticOpenIndexBuilds); // identical ordered providers share across strata
            Assert.Equal(size, observations.StaticOpenIndexMemberVisits);
            var lib = MemberOf(measured.Root, "Lib");
            for (var i = 0; i < size; i++)
            {
                var alias = Assert.IsType<Algorithm.Alias>(MemberOf(measured.Root, $"R{i}"));
                var target = Assert.IsType<ImplicitArgumentResolver.AliasTarget>(alias.ResolvedTarget);
                Assert.Same(MemberOf(lib, $"M{i}"), target.Algorithm);
            }
        }
    }

    [Theory]
    [InlineData("navigated-chain-aliases")]
    [InlineData("navigated-chain-opens")]
    [InlineData("opened-member-aliases")]
    public void ResolverChases_AllocationGrowsLinearly(string shape)
    {
        string Source(int size) => shape switch
        {
            "navigated-chain-aliases" => NavigatedChain(size, opens: false),
            "navigated-chain-opens" => NavigatedChain(size, opens: true),
            _ => OpenedMemberAliases(size),
        };

        static long Allocation(string source)
        {
            Assert.False(Parser.Parse(source).HasErrors);
            var before = GC.GetAllocatedBytesForCurrentThread();
            _ = Parser.Parse(source);
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        var small = Allocation(Source(400));
        var large = Allocation(Source(800));
        var ratio = (double)large / small;
        Assert.True(ratio < 2.5, $"Doubling {shape} grew the parse allocation {ratio:F2}x ({small} -> {large} bytes).");
    }
}
