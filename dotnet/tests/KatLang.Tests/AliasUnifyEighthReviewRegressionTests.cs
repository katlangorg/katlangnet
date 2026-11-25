using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// ALIAS-UNIFY-1 (M4★) eighth independent-review regressions. Source cases run on the six routes of
/// <see cref="SixRouteAgreement"/>; the scaling facts compare the detection's own observations
/// (<see cref="FrontEndTraversalObservations"/>) at two sizes. Front end: a dot receiver that is a calculation written as
/// a member path from a head that is no name or block (<c>A = 5.size</c>) is its own structure, and so is a body reached
/// through a member path or an open whose head names nothing — unless a navigated body enclosing it gives a dot edge
/// that name, which it may then infer as a fallback name — exactly as at HEAD: a certain miss on such a receiver lifts
/// it into the fallback's value slot and is checked in a closed list. A receiver chase abandoned on an undecided input
/// records the stretch it passed, so the chase taken again once the input is decided resumes where it stopped.
/// </summary>
public sealed class AliasUnifyEighthReviewRegressionTests
{
    private static async Task OkAsync(string source, string value)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(value, outcome.Value);
    }

    private static async Task CheckedMissAsync(string source, string member, string receiver)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", outcome.Kind);
        Assert.StartsWith($"UndeclaredIdentifier: Property '{member}' was not found on `{receiver}`", outcome.Errors[0], StringComparison.Ordinal);
    }

    private static FrontEndTraversalObservations Detect(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var (_, diagnostics) = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source), observations: observations);
        Assert.Empty(diagnostics);
        return observations;
    }

    // ── A calculation written as a member path is its own structure ──

    [Theory]
    [InlineData("A = 5.size\nF = A.abs + 0\nF(count)", "1")]
    [InlineData("A = x~.abs\nF = A.abs + 0\nF(-3)", "3")]
    public async Task ACalculationReceiver_IsLiftedIntoItsCertainFallback(string source, string value)
    {
        // A requires its input (`size`, `x`), and `A.abs` is the certain fallback abs(A), whose value slot lifts A: F is
        // F(size) / F(x), as at HEAD.
        await OkAsync(source, value);
    }

    [Theory]
    [InlineData("A = 6.abs\nG(p) = A.bar + p\nG(1)")]
    [InlineData("Mk(n) = n + 1\nA = Mk(1).abs\nG(p) = A.bar + p\nG(1)")]
    [InlineData("A = (1, 2).count\nG(p) = A.bar + p\nG(1)")]
    public async Task ACalculationReceiver_HasACertainMiss_ThatAClosedListChecks(string source)
    {
        // A literal, a call or a capture heads no reference: A is its own structure, which declares no `bar`.
        await CheckedMissAsync(source, "bar", "A");
    }

    [Fact]
    public async Task ARuntimeAlgorithmLinkReceiver_IsNoKnownStructure()
    {
        // An argumentless `.Algorithm` link is a runtime row: A is a runtime reference whose members are its target's,
        // which only the run knows, so `A.bar` may take its fallback and the closed list checks nothing.
        await OkAsync("Cap(meta op) = op\nInc(x) = x + 1\nA = Cap(Inc(1)).Algorithm\nG(p) = A.bar + p\n5", "5");
    }

    [Fact]
    public async Task ALinkFromTheBodysOwnGracedInput_IsItsOwnStructure()
    {
        // x is A's own input (Grace marks it), so A has a parameter and is no reference: its own structure, as at HEAD.
        await CheckedMissAsync("A = x~.Algorithm\nG(p) = A.bar + p\n5", "bar", "A");
    }

    [Fact]
    public void TheEditor_ReadsACalculationMemberAsItsOwnStructure_InsideAChain()
    {
        // `B.A.C.D`: the editor's chain reads B's member A through its scope-free structure view — A, a calculation,
        // declares no C, so `B.A.C` is the certain fallback C(B.A), a value, and `.D` is the certain fallback D(…): the
        // site resolves to D's declaration.
        var parsed = SourceProvenance.ParseValid("B = {\n    public A = 6.abs\n}\nC(x) = x\nD(x) = x\nB.A.C.D");
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(6, 7)));
        Assert.Equal("D", resolution.Occurrence.Name);
        Assert.NotNull(resolution.ResolvedDeclaration);
        Assert.Equal(5, resolution.ResolvedDeclaration!.Span.Start.Line);
    }

    // ── A body reached through a member path or an open, whose head names nothing, infers it ──

    [Theory]
    [InlineData("Lib = {\n    public A = x\n    0\n}\nF = Lib.A.abs + 0\nF(-3)", "3")]
    [InlineData("Lib = {\n    public Sub = {\n        public A = x\n        0\n    }\n    0\n}\nF = Lib.Sub.A.abs + 0\nF(-4)", "4")]
    public async Task ANavigatedInferredInputBody_IsLiftedIntoItsCertainFallback(string source, string value)
    {
        // Nothing declares x and no body enclosing A uses it: A is A(x), its own structure, so `.abs` is the certain
        // fallback and F is F(x), as at HEAD.
        await OkAsync(source, value);
    }

    [Fact]
    public async Task AnOpenedInferredInputBody_HasACertainMiss_ThatAClosedListChecks()
        => await CheckedMissAsync("open Lib\nLib = {\n    public A = x\n    0\n}\nG(p) = A.bar + p\nG(1)", "bar", "A");

    [Fact]
    public async Task ABodyEnclosedByOneThatMayInferItsHeadAsAFallbackName_IsNoKnownStructure()
    {
        // Lib's row `5.x` gives a dot edge the member x: Lib may infer x as a fallback name (here it does: 5 has no x), so
        // A = x may read Lib's parameter — a runtime reference whose members only the run knows. `Lib.A.bar` may take
        // its fallback, so the closed list checks nothing.
        await OkAsync("Lib = {\n    public A = x\n    5.x\n}\nG(p) = Lib.A.bar + p\n5", "5");
    }

    // ── An abandoned receiver chase resumes where it stopped ──

    /// <summary>
    /// One decision (z, asked through `M.B.w`) whose OD-D walk passes the hop `X = C1.w`: the hop's receiver chain C1 → m1
    /// → U.m1 = C2 → … reads the undecided inputs m1 … mK one after another; each is decided no (`Q.mi`).
    /// </summary>
    private static string InnerReceiverChainReadingUndecidedInputsInTurn(int size)
        => "Y = { public z = { public w = 1 } }\nP = {\n    open U\n    U = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"        public m{i} = C{i + 1}\n" : $"        public m{i} = {{ public w = {{ public z = 1 }} }}\n"))
            + "    }\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    C{i} = m{i}\n"))
            + "    X = C1.w\n    M = {\n        open Y\n        public B = z\n        0\n    }\n    Q = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"        public m{i} = 0\n")) + "    }\n"
            + "    M.B.w\n    X.z\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    Q.m{i}\n")) + "}\nP";

    /// <summary>
    /// One decision (z) whose OD-D walk passes the member-path hop `T = N1.A.Out`, whose receiver chase reads the undecided
    /// inputs n1 … nK one after another (`Ni = { open Xi ⏎ public A = ni ⏎ 0 }`, `Xi = { public ni = N(i+1).A }`).
    /// </summary>
    private static string MemberPathHopReadingUndecidedInputsInTurn(int size)
        => "Y = { public z = { public w = 1 } }\nP = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"    X{i} = {{ public n{i} = N{i + 1}.A }}\n" : $"    X{i} = {{ public n{i} = {{ public Out = {{ public z = 1 }} }} }}\n"))
            + "    M = {\n        open Y\n        public B = z\n        0\n    }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    N{i} = {{\n        open X{i}\n        public A = n{i}\n        0\n    }}\n"))
            + "    T = N1.A.Out\n    Q = {\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"        public n{i} = 0\n")) + "    }\n"
            + "    M.B.w\n    T.z\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    Q.n{i}\n")) + "}\nP";

    [Theory]
    [InlineData("inner-receiver-chain")]
    [InlineData("member-path-hop")]
    public async Task AnAbandonedReceiverChase_ResumesWhereItStopped(string shape)
    {
        // No decision reads itself and no pass repeats, so detection is linear: each undecided read abandons the
        // receiver chase once, and the chase taken again follows the stretch it recorded to the body it stopped at.
        Func<int, string> generate = shape == "inner-receiver-chain"
            ? InnerReceiverChainReadingUndecidedInputsInTurn
            : MemberPathHopReadingUndecidedInputsInTurn;
        await OkAsync(generate(3), "S[1, 1, 0, 0, 0]");
        var small = Detect(generate(100));
        var large = Detect(generate(200));
        HistoricalContractAssertions.InputWork(small);
        HistoricalContractAssertions.InputWork(large);
        var ratio = (double)large.StaticQueryEvaluationCount / small.StaticQueryEvaluationCount;
        Assert.True(ratio < 2.6, $"Doubling the size grew the detection work {ratio:F2}x ({small.StaticQueryEvaluationCount} -> {large.StaticQueryEvaluationCount}).");
    }
}
