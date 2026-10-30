using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// ALIAS-UNIFY-1 (M4★) ninth independent-review regressions. Source cases run on the six routes of
/// <see cref="SixRouteAgreement"/>; the editor cases read the semantic model; the scaling facts compare the detection's
/// own observations (<see cref="FrontEndTraversalObservations"/>) at two sizes. Front end: a body whose row is a member
/// path that names no static algorithm — a step's receiver not statically known, or an <c>.Algorithm</c> step before the
/// last — is no reference and so its own structure, and a body whose row ends in an <c>.Algorithm</c> link is a runtime
/// reference only when it has no input of its own (inferred, graced or lifted); a navigated body is its own input when
/// no body enclosing it infers its head — decided since the tenth review by implicit-argument resolution, from the
/// bodies it processed (detection leaves a link body, and a navigated body whose head an enclosing body's dot edge
/// names, to it). Outcomes are HEAD's except where M4★ changes them (a runtime reference's members are its
/// target's). Editor: a receiver after resolution is read as its elaborated structure, so a body alias
/// formation left a lone row (a member miss, an OD-D cycle) is its own structure and a transparent reference reached as a
/// member shows its target's members. A chase parameter detection abandons on an undecided input resumes where it
/// stopped, so a decision whose chase reads K undecided inputs in turn — however its member paths nest — is linear.
/// </summary>
public sealed class AliasUnifyNinthReviewRegressionTests
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

    private static void AssertResolvesTo(string source, int line, int column, string name, int declarationLine)
    {
        var parsed = SourceProvenance.ParseValid(source);
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(line, column)));
        Assert.Equal(name, resolution.Occurrence.Name);
        Assert.NotNull(resolution.ResolvedDeclaration);
        Assert.Equal(declarationLine, resolution.ResolvedDeclaration!.Span.Start.Line);
    }

    // ── A member path that names no static algorithm makes its body its own structure ──

    [Theory]
    // `X.Algorithm` misses on the block X, so `.abs` is the certain fallback abs(X.Algorithm): A is a calculation.
    [InlineData("X = {\n    public Y = 1\n}\nA = X.Algorithm.abs\nG(p) = A.bar + p\n5", "bar", "A")]
    // x reads F's parameter, so `x.y` is undecided and no runtime row: A is no alias, a body with no members.
    [InlineData("y(v) = v\nF(p) = {\n    x = p\n    A = x.y\n    G(q) = A.foo + q\n    0\n}\nF(1)", "foo", "A")]
    public async Task APathWhoseReceiverIsNotKnown_MakesItsBodyItsOwnStructure(string source, string member, string receiver)
        => await CheckedMissAsync(source, member, receiver);

    [Fact]
    public async Task ALinkPathThroughAnUnknownReceiver_WhoseMemberIsTheBodysInput_IsItsOwnStructure()
    {
        // `x.y` may take its fallback, so A infers y: A(y) is a calculation, its own structure, although its path ends in
        // a link — `A.foo` is a certain miss, as at HEAD.
        await CheckedMissAsync("F(p) = {\n    x = p\n    A = x.y.Algorithm\n    G(q) = A.foo + q\n    0\n}\nF(1)", "foo", "A");
    }

    [Fact]
    public async Task APathThroughARuntimeReceiver_IsLiftedIntoItsCertainFallback()
    {
        // A infers y, so A(y) is its own structure: `A.abs` is the certain fallback abs(A), whose value slot lifts A, so
        // H is H(y) and A(Pick) is x.Pick = Pick(5) = 7, as at HEAD.
        await OkAsync("Pick(v) = 7\nF(p) = {\n    x = p\n    A = x.y\n    H = A.abs + 0\n    H(Pick)\n}\nF(5)", "7");
    }

    // ── A link row is a runtime reference only when its body has no input of its own ──

    [Theory]
    // x is A's inferred input: an argument of the call the link projects.
    [InlineData("Mk(n) = n + 1\nA = Mk(x).Algorithm\nG(p) = A.bar + p\n5")]
    // Grace marks the input inside the call.
    [InlineData("Mk(n) = n + 1\nA = Mk(x~).Algorithm\nG(p) = A.bar + p\n5")]
    // The receiver Mk requires an argument, so lifting gives A the parameter t.
    [InlineData("Mk(t) = t + 1\nA = Mk.Algorithm\nG(p) = A.bar + p\n5")]
    // y is A's inferred input, an argument nested in the captured call.
    [InlineData("Cap(meta op) = op\nInc(x) = x + 1\nA = Cap(Inc(y)).Algorithm\nG(p) = A.bar + p\n5")]
    // `size` is A's inferred input: the certain fallback name of `5.size`.
    [InlineData("A = 5.size.Algorithm\nG(p) = A.bar + p\n5")]
    // The head x itself is A's inferred input.
    [InlineData("A = x.Algorithm\nG(p) = A.bar + p\n5")]
    public async Task ALinkFromABodyWithAnInputOfItsOwn_IsItsOwnStructure(string source)
    {
        // A has a parameter, so it is no runtime alias but its own structure, which declares no `bar`.
        await CheckedMissAsync(source, "bar", "A");
    }

    [Fact]
    public async Task ALinkFromABodyWithAnInputOfItsOwn_IsLiftedIntoItsCertainFallback()
    {
        // A(x) is its own structure, so `A.abs` is the certain fallback abs(A), whose value slot lifts A: H(x). A(3) is the
        // bare VALUE of the projected callee Only, 5.
        await OkAsync("Cap(meta op) = op\nOnly(*xs) = 5\nA = Cap(Only(x)).Algorithm\nH = A.abs + 0\nH(3)", "5");
    }

    [Fact]
    public async Task ALinkFromABodyWithAnInputOfItsOwn_IsCalledAsItsOwnCalculation()
    {
        // F(y) = abs(A(y)) + 0, as at HEAD: A(1) projects `.Algorithm` from Mk(1) = 2, a number, not a call reference.
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("Mk(n) = n + 1\nA = Mk(y).Algorithm\nF = A.abs + 0\nF(1)");
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith("TypeMismatch:", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Contains("`Algorithm` requires a call reference", outcome.Errors[0], StringComparison.Ordinal);
    }

    // ── A navigated body's head that no enclosing body infers is its own input ──

    [Theory]
    // `Cfg.x` is a structural hit, so Lib infers no x: A is A(x), its own structure, and F is F(x).
    [InlineData("Lib = {\n    Cfg = {\n        public x = 1\n    }\n    public A = x\n    Cfg.x + 0\n}\nF = Lib.A.abs + 0\nF(-3)", "3")]
    // `Q.h` selects Q's member h whatever Lib infers.
    [InlineData("Lib = {\n    public A = h\n    Q.h\n    Q = { public h = 1 }\n}\nF = Lib.A.abs + 0\nF(-3)", "3")]
    public async Task ANavigatedBodyWhoseHeadNoEnclosingBodyMayInfer_IsLiftedIntoItsCertainFallback(string source, string value)
        => await OkAsync(source, value);

    [Theory]
    [InlineData("Lib = {\n    public A = h\n    Q.h\n    Q = { public h = 1 }\n}\nG(p) = Lib.A.bar + p\n5", "bar", "Lib.A")]
    // One verdict wherever the chase starts: through the navigated P, as from inside P below.
    [InlineData("P = {\n    Cfg = {\n        public h = 1\n    }\n    N = {\n        public A = h\n        0\n    }\n    Cfg.h + 0\n}\nF(z) = P.N.A.W + z\n5", "W", "P.N.A")]
    [InlineData("P = {\n    Cfg = {\n        public h = 1\n    }\n    N = {\n        public A = h\n        0\n    }\n    G(z) = N.A.W + z\n    Cfg.h + 0\n}\n5", "W", "N.A")]
    public async Task ANavigatedBodyWhoseHeadNoEnclosingBodyMayInfer_HasACertainMiss_ThatAClosedListChecks(string source, string member, string receiver)
        => await CheckedMissAsync(source, member, receiver);

    // ── The editor reads a receiver after resolution as its elaborated structure ──

    [Fact]
    public void TheEditor_ReadsABodyLeftALoneRowByAMemberMiss_AsItsOwnStructure()
    {
        // `A = B.Wrap` misses on B, so A is the calculation Wrap(B), no alias: `A.Inc` is the certain fallback, a value,
        // and `.Dbl` is the certain fallback Dbl(…).
        AssertResolvesTo("B = {\n    public Y = 1\n}\nWrap(v) = 10\nA = B.Wrap\nInc(v) = v + 1\nDbl(v) = v * 2\nA.Inc.Dbl", 8, 7, "Dbl", 7);
        AssertResolvesTo("Lib = {\n    public Q = 1\n}\nfoo(x) = 7\nA = Lib.foo\nC(x) = x\nD(x) = x\nA.C.D", 8, 5, "D", 7);
    }

    [Fact]
    public void TheEditor_ReadsABodyLeftALoneRowByAStaticCycle_AsItsOwnStructure()
    {
        // OD-D: A's target chase returns, so A is no alias but its own structure, which declares no X.
        AssertResolvesTo("A = B\nB = {\n    public Y = 1\n    A\n}\nX(v) = 5\nShow(v) = v\nA.X.Show", 8, 5, "Show", 7);
        AssertResolvesTo("B = {\n    public A = A\n}\nC(x) = x\nD(x) = x\nB.A.C.D", 6, 7, "D", 5);
    }

    [Fact]
    public async Task ABlockReceiversMember_IsItsElaboratedStructure_InTheEditorAndTheDiagnostics()
    {
        // The block's A = B.Wrap misses on B, so A is the calculation Wrap(B), its own structure: `.Inc` is a certain
        // fallback, `.Dbl` resolves, and the root's inferred X is reported as the certain fallback of A's miss, as at HEAD.
        const string Declarations = "B = { public Y = 1 }\nWrap(v) = 10\n";
        AssertResolvesTo(Declarations + "Inc(v) = v + 1\nDbl(v) = v * 2\n{ public A = B.Wrap }.A.Inc.Dbl", 5, 29, "Dbl", 4);
        var root = await SixRouteAgreement.OnEveryRouteAsync(Declarations + "{ public A = B.Wrap }.A.X");
        Assert.Equal("err", root.Kind);
        Assert.StartsWith("UnresolvedImplicitParams: Property 'X' was not found on `{...}.A`", root.Errors[0], StringComparison.Ordinal);
    }

    [Fact]
    public void TheEditor_ReadsATransparentReferenceMember_AsItsTarget()
    {
        // `Lib.A` / `B.A` is a transparent reference: its members are its target's.
        AssertResolvesTo("B = {\n    public Q = 1\n}\nLib = {\n    public A = B\n}\nLib.A.Q", 7, 7, "Q", 2);
        AssertResolvesTo("Lib = {\n    public C = 5\n}\nB = {\n    public A = Lib\n}\nC(x) = x + 100\nB.A.C", 8, 5, "C", 2);
    }

    // ── A reference elaborated while the body it reaches is in progress records that body once it is processed ──

    private const string SelfReferencingBlock = "R = {\n    public a = R\n    public w = { public z = 1 }\n    0\n}\n";

    [Theory]
    // R's member a is elaborated while R is in progress: its recorded structure is R's processed body, so O2 = R.a,
    // O1 = O2.a and X = O1.w navigate it — each of them a reference — whatever the nesting.
    [InlineData(SelfReferencingBlock + "O2 = R.a\nO1 = O2.a\nX = O1.w\nX.z", "1")]
    [InlineData(SelfReferencingBlock + "C1 = R\nO1 = O2.a\nO2 = C1.a\nX = O1.w\nX.z", "1")]
    [InlineData(SelfReferencingBlock + "O3 = R.a\nO2 = O3.a\nO1 = O2.a\nX = O1.w\nX.z", "1")]
    // Inside R, a reference through the in-progress a is read statically.
    [InlineData("R = {\n    public a = R\n    public b = a.a.w\n    public w = { public z = 1 }\n    0\n}\nR.b.z", "1")]
    // b reaches R's member w, which R processed before b: its processed body, whose z is a reference to Q.
    [InlineData("R = {\n    public w = { public z = Q }\n    public b = R.w\n    0\n}\nQ = { public y = 5 }\nR.b.z.y", "5")]
    // A sibling cycle: A reaches B's member C before B is processed, in either order.
    [InlineData("A = B.C\nB = {\n    public C = { public X = Y }\n    public D = A\n    0\n}\nY = { public Q = 3 }\nA.X.Q", "3")]
    [InlineData("B = {\n    public C = { public X = Y }\n    public D = A\n    0\n}\nA = B.C\nY = { public Q = 3 }\nA.X.Q", "3")]
    public async Task AReferenceElaboratedWhileItsStructureIsInProgress_NavigatesItsProcessedBody(string source, string value)
    {
        await OkAsync(source, value);
        Assert.All(
            SourceProvenance.ParseValid(source).Root.Properties.Where(static p => p.Name is "A" or "X" or "O1" or "O2" or "O3"),
            static p => Assert.IsType<Algorithm.Alias>(p.Value));
    }

    [Fact]
    public async Task AReferenceThroughAnInProgressStructure_HasACertainMiss_ThatAClosedListChecks()
        => await CheckedMissAsync(SelfReferencingBlock + "O2 = R.a\nO1 = O2.a\nX = O1.w\nG(p) = X.bar + p\n5", "bar", "X");

    [Fact]
    public void TheEditor_NavigatesAReferenceElaboratedWhileItsStructureWasInProgress()
    {
        // R.a's recorded structure is R's processed body, so `R.a.a.w.z` reads R's members at every step.
        AssertResolvesTo(SelfReferencingBlock + "R.a.a.w.z", 6, 9, "z", 3);
        // c = a records a's structure, which R completes after c is elaborated: the two share it.
        AssertResolvesTo("R = {\n    public a = R\n    public c = a\n    public w = { public z = 1 }\n    0\n}\nR.c.a.w.z", 7, 9, "z", 4);
        // b = R.w reaches R's member w, which R processed before b: b's structure is w's processed body, whose z is a
        // reference to Q.
        AssertResolvesTo("R = {\n    public w = { public z = Q }\n    public b = R.w\n    0\n}\nQ = { public y = 5 }\nR.b.z.y", 7, 7, "y", 6);
    }

    // ── An abandoned chase resumes where it stopped ──

    /// <summary>
    /// One decision (z, asked through `M.B.w`) whose OD-D walk passes the hop `X = O1.w`, whose receiver chase nests the
    /// owners O1 → U.h1 = O2 → … (`Oi = hi.a`): each owner's head hi is undecided in turn and decided no (`Q.hi`).
    /// </summary>
    private static string NestedOwnersReadingUndecidedInputsInTurn(int size)
        => "Y = { public z = { public w = 1 } }\nP = {\n    open U\n    U = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"        public h{i} = O{i + 1}\n" : $"        public h{i} = R\n"))
            + "    }\n    R = {\n        public a = R\n        public w = { public z = 1 }\n        0\n    }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    O{i} = h{i}.a\n"))
            + "    X = O1.w\n    M = {\n        open Y\n        public B = z\n        0\n    }\n    Q = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"        public h{i} = 0\n")) + "    }\n"
            + "    M.B.w\n    X.z\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    Q.h{i}\n")) + "}\nP";

    /// <summary>
    /// One decision (z) whose OD-D walk passes the hop `X = B1.w`: each Bi = Si.k waits on its member path while Si = mi
    /// reads the undecided input mi, so the chase abandons with the paths of B1 … B(i-1) waiting.
    /// </summary>
    private static string WaitingPathsReadingUndecidedInputsInTurn(int size)
        => "Y = { public z = { public w = 1 } }\nP = {\n    open U\n    U = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"        public m{i} = {{ public k = B{i + 1} }}\n" : $"        public m{i} = {{ public k = {{ public w = {{ public z = 1 }} }} }}\n"))
            + "    }\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    S{i} = m{i}\n    B{i} = S{i}.k\n"))
            + "    X = B1.w\n    M = {\n        open Y\n        public B = z\n        0\n    }\n    Q = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"        public m{i} = 0\n")) + "    }\n"
            + "    M.B.w\n    X.z\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    Q.m{i}\n")) + "}\nP";

    /// <summary>
    /// The owners O1 → O2 → … → OD (`Oi = O(i+1).a`, `OD = C1.a`) wait on an inner receiver chain C1 → U.m1 = C2 → … that
    /// reads the undecided inputs m1 … mK in turn (D = K = the size).
    /// </summary>
    private static string OwnersOverAnInnerChainReadingUndecidedInputsInTurn(int size)
        => "Y = { public z = { public w = 1 } }\nP = {\n    open U\n    U = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"        public m{i} = C{i + 1}\n" : $"        public m{i} = R\n"))
            + "    }\n    R = {\n        public a = R\n        public w = { public z = 1 }\n        0\n    }\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"    C{i} = m{i}\n"))
            + string.Concat(Enumerable.Range(1, size).Select(i => i < size ? $"    O{i} = O{i + 1}.a\n" : $"    O{i} = C1.a\n"))
            + "    X = O1.w\n    M = {\n        open Y\n        public B = z\n        0\n    }\n    Q = {\n"
            + string.Concat(Enumerable.Range(1, size).Select(i => $"        public m{i} = 0\n")) + "    }\n"
            + "    M.B.w\n    X.z\n" + string.Concat(Enumerable.Range(1, size).Select(i => $"    Q.m{i}\n")) + "}\nP";

    [Theory]
    [InlineData("nested-owners")]
    [InlineData("waiting-paths")]
    [InlineData("owners-over-an-inner-chain")]
    public async Task AnAbandonedChase_ResumesWhereItStopped(string shape)
    {
        // P infers nothing (Q declares every input, and X's structure declares z), no decision reads itself and no pass
        // repeats, so detection is linear: each undecided read abandons the chase once, and the chase taken again resumes
        // at the hop it abandoned, with its waiting member paths.
        Func<int, string> generate = shape switch
        {
            "nested-owners" => NestedOwnersReadingUndecidedInputsInTurn,
            "waiting-paths" => WaitingPathsReadingUndecidedInputsInTurn,
            _ => OwnersOverAnInnerChainReadingUndecidedInputsInTurn,
        };
        await OkAsync(generate(3), "S[1, 1, 0, 0, 0]");
        var small = Detect(generate(100));
        var large = Detect(generate(200));
        HistoricalContractAssertions.InputWork(small);
        HistoricalContractAssertions.InputWork(large);
        var ratio = (double)large.StaticQueryEvaluationCount / small.StaticQueryEvaluationCount;
        Assert.True(ratio < 2.6, $"Doubling the size grew the detection work {ratio:F2}x ({small.StaticQueryEvaluationCount} -> {large.StaticQueryEvaluationCount}).");
    }
}
