namespace KatLang.Tests;

/// <summary>
/// Exposure charges a reader exactly the access checks and value reads the evaluator performs on static
/// selections while it evaluates the reader's rows (owner decision 2026-11-13; ledger E-18, F1): every
/// member of a written path whatever its head (a name, an inline block, a redundant group), every
/// selection of a transparent reference's target walk (made in the reference's own scope, through
/// chains of references), and every open target's walk of every level the reader's lookup consults, up
/// to and including the deciding one. Never a lexically found head's or reference's VALUE, nor an
/// inline block head's VALUE when a member is selected.
///
/// <para>Each row is a source program inside <c>F(y)</c>, with the reader <c>A</c>; the row id names the
/// inventory row of the E-18 exposure access-check report. An under-charged reader was exported, so its
/// escaped read <c>F.A</c> failed naming an inner member and <c>F(5), F.A</c> reused the call's exported
/// cache entry; both engines now refuse both, naming <c>A</c>. The Lean evaluator agrees on every program
/// (<c>NavigationSourceDomainGuards.AccessChecks</c> holds one per class).</para>
/// </summary>
public sealed class ExposureAccessCheckTests
{
    public static TheoryData<string, string, string, int> LocalOnlyReaders => new()
    {
        { "openProvidedReferenceTargetHead", "I5-open-head", "F(y) = {\n  open Lib\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Sub\n  A = L.Q + 0\n  A\n}\n", 1 },
        // A dot path THROUGH a runtime reference reads the receiver at run time: its row is charged (I28 control).
        { "runtimeReferenceDotPath", "I28-dot", "F(y) = {\n  L = y\n  Q(r) = 1\n  A = L.Q + 0\n  A\n}\n", 1 },
        { "runtimeReferenceChainDotPath", "I28-dot-chain", "F(y) = {\n  L0 = y\n  L1 = L0\n  Q(r) = 1\n  A = L1.Q + 0\n  A\n}\n", 1 },
        { "referenceTargetWalk", "I5", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  A = L.Q + 0\n  A\n}\n", 1 },
        { "referenceChainWithMembers", "I6", "F(y) = {\n  Lib = {\n    public Sub = {\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  L0 = Lib.Sub\n  M = L0.T\n  A = M.Q + 0\n  A\n}\n", 1 },
        { "memberlessReferenceChain", "I7", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L0 = Lib.Sub\n  L1 = L0\n  L2 = L1\n  A = L2.Q + 0\n  A\n}\n", 1 },
        { "outerReferenceReadOneLevelDown", "I8", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  A = {\n    Inner = L.Q + 0\n    Inner\n  }\n  A\n}\n", 1 },
        { "outerReferenceReadTwoLevelsDown", "I8b", "F(y) = {\n  L = Lib.Sub\n  A = {\n    B = {\n      C = L.Q + 0\n      C\n    }\n    B\n  }\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1 },
        { "referenceCallee", "I9", "F(y) = {\n  Lib = {\n    public Sub = {\n      public G(x) = x\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  A = L.G(1) + 0\n  A\n}\n", 1 },
        { "memberlessChainCallee", "I9", "F(y) = {\n  L0 = Lib.Sub\n  L1 = L0\n  A = L1.G(1) + 0\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1 },
        { "referenceSpread", "I10", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  A = sum(L.Q*) + 0\n  A\n}\n", 1 },
        { "memberlessChainSpread", "I10", "F(y) = {\n  L0 = Lib.Sub\n  L1 = L0\n  A = sum(L1.Q*) + 0\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1 },
        { "groupedReferenceHead", "I10b", "F(y) = {\n  L = Lib.Sub\n  A = (L).Q + 0\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1 },
        { "referenceInsideReferenceTarget", "I10c", "F(y) = {\n  L = Lib.Sub\n  M = L.T\n  A = M + 0\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n        7\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 7 },
        { "referenceInClauseBranch", "I10d", "F(y) = {\n  L = Lib.Sub\n  G(0) = L.Q + 0\n  G(n) = n\n  A = G(0) + 0\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1 },
        { "openThroughReference", "I11", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  A = {\n    open L\n    Q + 0\n  }\n  A\n}\n", 1 },
        { "dottedOpenThroughReference", "I11b", "F(y) = {\n  L = Lib.Sub\n  A = {\n    open L.T\n    Q + 0\n  }\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1 },
        { "openThroughMemberlessChain", "I11c", "F(y) = {\n  L0 = Lib.Sub\n  L1 = L0\n  A = {\n    open L1\n    Q + 0\n  }\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1 },
        { "unusedOwnOpenThroughReference", "I12", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  Other = {\n    public Z = 3\n  }\n  A = {\n    open L, Other\n    Z + 0\n  }\n  A\n}\n", 3 },
        { "enclosingOpenUsed", "I13b", "F(y) = {\n  open Lib.Sub\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  A = Q + 0\n  A\n}\n", 1 },
        { "enclosingOpenUnused", "I13c", "F(y) = {\n  open Lib.Sub, Other\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  Other = {\n    public X = 2\n  }\n  A = X + 0\n  A\n}\n", 2 },
        { "enclosingOpenTwoLevelsDown", "I13d", "F(y) = {\n  open Lib.Sub\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A = {\n    B = Q + 0\n    B\n  }\n  A\n}\n", 1 },
        { "enclosingOpenThroughReference", "I13e", "F(y) = {\n  open L\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  A = Q + 0\n  A\n}\n", 1 },
        { "twoConsultedOpenLevels", "I13f", "F(y) = {\n  open Lib.Sub\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  Other = {\n    public Z = 3\n  }\n  A = {\n    open Other\n    Q + 0\n  }\n  A\n}\n", 1 },
        { "blockHead", "I19", "F(y) = {\n  A = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n  }.Sub.Q + 0\n  A\n}\n", 1 },
        { "blockHeadFromNamedLib", "I19", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  A = { public Sub = { public Q = 1\n y } }.Sub.Q + 0\n  A\n}\n", 1 },
        { "groupedBlockHead", "I19b", "F(y) = {\n  A = ({\n    public Sub = {\n      public Q = 1\n      y\n    }\n  }).Sub.Q + 0\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1 },
        { "blockHeadTwoLevelsDown", "I19c", "F(y) = {\n  A = {\n    B = {\n      C = {\n        public Sub = {\n          public Q = 1\n          y\n        }\n      }.Sub.Q + 0\n      C\n    }\n    B\n  }\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1 },
        { "blockHeadCallee", "I20", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      y\n    }\n    0\n  }\n  A = { public Sub = { public G(x) = x\n y } }.Sub.G(1) + 0\n  A\n}\n", 1 },
        { "blockHeadedReference", "I21", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = { public Sub = { public Q = 1\n y } }.Sub\n  A = L.Q + 0\n  A\n}\n", 1 },
        { "blockHeadedReferenceValue", "I21", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = { public Sub = { public Q = 1\n y } }.Sub\n  A = L + 0\n  A\n}\n", 5 },
        { "directPath", "I1", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  A = Lib.Sub.Q + 0\n  A\n}\n", 1 },
        { "directSpread", "I3", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      y\n    }\n    0\n  }\n  A = sum(Lib.Sub.Q*) + 0\n  A\n}\n", 1 },
        { "directGroup", "I4", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      y\n    }\n    0\n  }\n  A = (Lib.Sub).Q + 0\n  A\n}\n", 1 },
        { "ownDottedOpen", "I13", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  A = {\n    open Lib.Sub\n    Q + 0\n  }\n  A\n}\n", 1 },
        { "referenceSelectedAsMember", "I15", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  Box = {\n    public L = Lib.Sub\n  }\n  A = Box.L.Q + 0\n  A\n}\n", 1 },
        { "fallbackThroughReference", "I16", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = Lib.Sub\n  A = L.Missing + 0\n  Missing(r) = 2\n  A\n}\n", 2 },
        { "blockHeadFallback", "I24", "F(y) = {\n  A = {\n    public Q = 1\n    y + 0\n  }.Missing + 0\n  Missing(r) = 2\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 2 },
        { "eagerOwnOpenOverCharge", "I25", "F(y) = {\n  A = {\n    open Lib.Sub\n    1\n  }\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1 },
        { "eagerOwnOpenOwnerWalkOverCharge", "I25", "F(y) = {\n  A = {\n    open Lib.Sub\n    X = 2\n    X + 0\n  }\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 2 },
        { "namedHeadAllMembers", "I1", "F(y) = {\n  B = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n  }\n  A = B.Sub.Q + 0\n  A\n}\n", 1 },
    };

    public static TheoryData<string, string, string, int, int> ExportedReaders => new()
    {
        // Opening a RUNTIME reference charges nothing (owner decision 3, 2026-11-13): openStructure opens its own
        // namespace, never establishing its target or reading its row (OD-C). These restore HEAD a4b545e8.
        { "runtimeReferenceOpen", "I28", "F(y) = {\n  open L, Other\n  L = y\n  Other = { public Q = 1 }\n  A = Q + 0\n  A\n}\n", 1, 1 },
        { "runtimeReferenceOpenChain", "I28-chain", "F(y) = {\n  open L1, Other\n  L0 = y\n  L1 = L0\n  Other = { public Q = 1 }\n  A = Q + 0\n  A\n}\n", 1, 1 },
        { "runtimeReferenceOpenMemberPath", "I28-member-path", "F(y) = {\n  open L, Other\n  L = y.C\n  Other = { public Q = 1 }\n  A = Q + 0\n  A\n}\n", 1, 1 },
        { "runtimeReferenceOpenAlgorithmLink", "I28-link", "F(y) = {\n  open L, Other\n  L = y.Algorithm\n  Other = { public Q = 1 }\n  A = Q + 0\n  A\n}\n", 1, 1 },
        { "runtimeReferenceOpenCallee", "I28-callee", "F(y) = {\n  open L, Other\n  L = y\n  Other = { public G(r) = r }\n  A = G(1) + 0\n  A\n}\n", 1, 1 },
        { "unusedOpenValueOnlyReference", "I17-open", "F(y) = {\n  open L, Other\n  Lib = { public Q = 1\n    y }\n  L = Lib\n  Other = { public X = 2 }\n  A = X + 0\n  A\n}\n", 2, 2 },
        { "blockHeadRelaxation", "I23", "F(y) = {\n  A = {\n    public Q = 1\n    y + 0\n  }.Q + 0\n  A\n}\n", 1, 1 },
        { "blockHeadRelaxationOtherMember", "I23", "F(y) = {\n  A = {\n    public Q = 1\n    y + 0\n  }.Q + 0\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n", 1, 1 },
        { "namedMemberOnly", "I23c", "F(y) = {\n  B = {\n    public Q = 1\n    y + 0\n  }\n  A = B.Q + 0\n  A\n}\n", 1, 1 },
        { "valueOnlyReference", "I17", "F(y) = {\n  Lib = {\n    public Q = 1\n    y\n  }\n  L = Lib\n  A = L.Q + 0\n  A\n}\n", 1, 1 },
        { "innerLevelDecidesFirst", "I14b", "F(y) = {\n  open Lib.Sub\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  Other = {\n    public Z = 3\n  }\n  A = {\n    open Other\n    Z + 0\n  }\n  A\n}\n", 3, 3 },
        { "ownerWalkConsultsNoOpens", "I14c", "F(y) = {\n  open Lib.Sub\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  X = 2\n  A = X + 0\n  A\n}\n", 2, 2 },
        { "preludeConsultsNoOpens", "I14d", "F(y) = {\n  open Lib.Sub\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A = max([1, 2]) + 0\n  A\n}\n", 2, 2 },
        { "inlineOpenBlockTarget", "I18", "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      y\n    }\n    0\n  }\n  A = {\n    open { public Sub = { public Q = 1 } }.Sub\n    Q + 0\n  }\n  A\n}\n", 1, 1 },
    };

    private static Property Reader(string source, string reader = "A")
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var f = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == "F").Value);
        return Assert.Single(f.Properties, property => property.Name == reader);
    }

    private static async Task<RunResult[]> BothEngines(string source)
    {
        // RunAsync with a sync-only configuration delegates to the sync evaluator. Keep that API
        // route and also exercise the actual async twin by registering an unused async operation.
        var operations = HostOperations.Create(HostOperation.CreateAsync("UnusedExposureReview",
            static (_, _) => throw new InvalidOperationException("The route marker must never execute.")));
        Assert.True(operations.ContainsAsynchronousOperations);
        return [KatLangEngine.Run(source), await KatLangEngine.RunAsync(source),
            await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations })];
    }

    [Theory]
    [MemberData(nameof(LocalOnlyReaders))]
    public async Task UnderChargedReader_IsLocalOnly_AndRefusedOutsideTheCall(string name, string row, string body, int inside)
    {
        _ = (name, row);
        var a = Reader(body + "F(5)\n");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, a.Exposure);
        Assert.Equal(["y"], a.RequiredAncestorParameters);

        foreach (var result in await BothEngines(body + "F(5)\n"))
            Assert.Equal(new Result.Atom(inside), Assert.IsType<RunResult.Success>(result).Value);
        foreach (var tail in new[] { "F.A\n", "F(5), F.A\n" })
            foreach (var result in await BothEngines(body + tail))
            {
                var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
                Assert.Equal(KatLangErrorCode.LocalOnlyProperty, error.Code);
                Assert.Contains("Property 'A' on `F` is local-only", error.Message, StringComparison.Ordinal);
            }
    }

    [Theory]
    [MemberData(nameof(ExportedReaders))]
    public async Task SelectedMemberOnlyReader_IsExported_AndReadOutsideTheCall(string name, string row, string body, int inside, int escaped)
    {
        _ = (name, row);
        var a = Reader(body + "F(5)\n");
        Assert.Equal(PropertyExposure.Exported, a.Exposure);
        Assert.Empty(a.RequiredAncestorParameters);

        foreach (var result in await BothEngines(body + "F(5)\n"))
            Assert.Equal(new Result.Atom(inside), Assert.IsType<RunResult.Success>(result).Value);
        foreach (var result in await BothEngines(body + "F.A\n"))
            Assert.Equal(new Result.Atom(escaped), Assert.IsType<RunResult.Success>(result).Value);
        foreach (var result in await BothEngines(body + "F(5), F.A\n"))
            Assert.Equal([$"{inside}", $"{escaped}"], Assert.IsType<RunResult.Success>(result).Atoms.Select(atom => atom.ToString()));
    }

    // ── Each check where the evaluator makes it, and nothing for a check that can never pass (owner decisions Q1–Q3, 2026-11-14) ──

    private const string OnlyInsideF = "F(y) = {\n  A = y + 1\n  A\n}\n";

    // `Sub` requires `p` of the `Mid(p)` this literal declares, which nothing ever activates.
    private const string LiteralMid = "{\n    public Mid(p) = {\n      public Sub = {\n        public Q = 1\n        p\n      }\n      0\n    }\n  }.Mid.Sub";

    private const string LibMid = "  Lib = {\n    public Mid(p) = {\n      public Sub = {\n        public Q = 1\n        p\n      }\n";

    private const string RefInMid = "F(y) = {\n  L = Lib.Mid.Sub\n" + LibMid
        + "      A(z) = L.Q + 0\n      B(z) = {\n        open L\n        Q + 0\n      }\n      C(z) = Lib.Mid.Sub.Q + 0\n      D(z) = Sub.Q + 0\n"
        + "      if(p == 1, A(0), if(p == 2, B(0), if(p == 3, C(0), D(0))))\n    }\n    0\n  }\n  Lib.Mid(y)\n}\n";

    private const string BlockHeadedProvider = "F(y) = {\n  open L\n  L = {\n    public Sub = {\n      public Q = y\n      0\n    }\n  }.Sub\n  A = Q + 0\n  A\n}\n";

    private const string NamedProvider = "F(y) = {\n  open L\n  Lib = {\n    public Sub = {\n      public Q = y\n      0\n    }\n  }\n  L = Lib.Sub\n  A = Q + 0\n  A\n}\n";

    /// <summary>
    /// The decision probes (<c>artifacts/validation/e18-q1-decision-20261114/programs</c>): a program, a root row and
    /// its outcome, which is the atoms it returns or the member a <c>LocalOnlyProperty</c> refusal names.
    /// </summary>
    public static TheoryData<string, string, string, string> SiteAndImpossibleCheckPins => new()
    {
        // Q3: a name provided by opening a block-headed reference keeps the provider's requirement (census G1) ...
        { "g1-min", BlockHeadedProvider, "F(5)", "5" },
        { "g1-min", BlockHeadedProvider, "F(7)", "7" },
        { "g1-min", BlockHeadedProvider, "F(5), F(7)", "5, 7" },
        { "g1-min", BlockHeadedProvider, "F.A", "refused at A" },
        // ... exactly as its named twin does.
        { "g1-ref", NamedProvider, "F(5)", "5" },
        { "g1-ref", NamedProvider, "F(7)", "7" },
        { "g1-ref", NamedProvider, "F(5), F(7)", "5, 7" },
        { "g1-ref", NamedProvider, "F.A", "refused at A" },
        // Q2: an open crossing is checked from the consulted level, here inside Mid's activation ...
        { "openref-in-mid", "F(y) = {\n  L = Lib.Mid.Sub\n" + LibMid + "      B(z) = {\n        open L\n        Q + 0\n      }\n      B(0)\n    }\n    0\n  }\n  Lib.Mid(y)\n}\n", "F(5)", "1" },
        // ... and a value crossing in the reference's own scope, outside it: only the route that runs fails.
        { "ref-in-mid", RefInMid, "F(1)", "refused at Sub" },
        { "ref-in-mid", RefInMid, "F(2)", "1" },
        { "ref-in-mid", RefInMid, "F(3)", "1" },
        { "ref-in-mid", RefInMid, "F(4)", "1" },
        // An open walk consulted OUTSIDE Mid by a reader inside it can never pass: the path that runs fails at the check.
        { "open-in-mid", "F(y) = {\n  open Lib.Mid.Sub\n" + LibMid + "      A(z) = Q + 0\n      A(0)\n    }\n    0\n  }\n  Lib.Mid(y)\n}\n", "F(5)", "refused at Sub" },
        // Q1: an impossible path behaves like any error in a branch that does not run, for values ...
        { "l1-root-row", OnlyInsideF, "if(false, F.A, 0)", "0" },
        { "l2-property", OnlyInsideF + "R = if(false, F.A, 0)\n", "R", "0" },
        { "l3-selected", OnlyInsideF + "Box = {\n  public R = if(false, F.A, 0)\n}\n", "Box.R", "0" },
        { "l4-in-call", OnlyInsideF + "G(x) = {\n  Box = {\n    public R = if(x > 100, F.A, x)\n  }\n  Box.R\n}\n", "G(1)", "1" },
        { "l4-in-call", OnlyInsideF + "G(x) = {\n  Box = {\n    public R = if(x > 100, F.A, x)\n  }\n  Box.R\n}\n", "G(200)", "refused at A" },
        { "l5-nested", OnlyInsideF + "M = {\n  public G(x) = {\n    R = if(x > 100, F.A, x)\n    R\n  }\n}\n", "M.G(1)", "1" },
        { "l5-nested", OnlyInsideF + "M = {\n  public G(x) = {\n    R = if(x > 100, F.A, x)\n    R\n  }\n}\n", "M.G(200)", "refused at A" },
        // ... and for caching: the reader is cached once per run, as an untaken `1 / 0` is.
        { "t1-untaken-impossible", OnlyInsideF + "G(x) = {\n  R = if(false, F.A, tick())\n  R\n}\n", "G(1), G(2)", "1, 1" },
        { "t2-plain-control", "G(x) = {\n  R = tick()\n  R\n}\n", "G(1), G(2)", "1, 1" },
        { "t3-div-control", "G(x) = {\n  R = if(false, 1 / 0, tick())\n  R\n}\n", "G(1), G(2)", "1, 1" },
        // More readers of an impossible path that does not run: selected by a path, nested, read by name.
        { "untaken-selected-g8", "F(y) = {\n  L = Lib.Mid.Sub\n" + LibMid + "      0\n    }\n    0\n  }\n  Box = {\n    public A = if(false, L.Q + 0, 7)\n  }\n  Box.A\n}\n", "F(5)", "7" },
        { "untaken-nested-g8", "M = {\n  public F(y) = {\n    L = Lib.Mid.Sub\n  " + LibMid.Replace("\n", "\n  ") + "    0\n      }\n      0\n    }\n    A = if(false, L.Q + 0, 7)\n    A\n  }\n}\n", "M.F(5)", "7" },
        { "untaken-selected-g9", "F(y) = {\n  Box = {\n    public A = {\n      open " + LiteralMid + "\n      if(false, Q + 0, 7)\n    }\n  }\n  Box.A\n}\n", "F(5)", "7" },
        { "untaken-nested-g9", "M = {\n  public F(y) = {\n    open " + LiteralMid + "\n    A = if(false, Q + 0, 7)\n    A\n  }\n}\n", "M.F(5)", "7" },
        { "untaken-lexical-g9", "F(y) = {\n  open " + LiteralMid + "\n  A = if(false, Q + 0, 7)\n  A\n}\n", "F(5)", "7" },
        { "untaken-lexical-g9", "F(y) = {\n  open " + LiteralMid + "\n  A = if(false, Q + 0, 7)\n  A\n}\n", "F.A", "7" },
        // The accepted consequence: under `tick`, the reader of an impossible path is cached once, like an untaken `1 / 0`.
        { "d01-impossible-tick", "F(y) = {\n  open " + LiteralMid + "\n  A = if(tick() > 1, Q + 0, 0)\n  A\n}\n", "F(5), F(7)", "0, 0" },
        { "d01-impossible-tick", "F(y) = {\n  open " + LiteralMid + "\n  A = if(tick() > 1, Q + 0, 0)\n  A\n}\n", "F(5)", "0" },
        { "d01-impossible-tick", "F(y) = {\n  open " + LiteralMid + "\n  A = if(tick() > 1, Q + 0, 0)\n  A\n}\n", "F(7)", "0" },
        { "d02-live-tick", "F(y) = {\n  A = if(tick() > 1, y, 0)\n  A\n}\n", "F(5), F(7)", "0, 7" },
        // The impossible path, when it runs, fails at the member the evaluator checks.
        { "d03-impossible-direct", "F(y) = {\n  open " + LiteralMid + "\n  A = Q + 0\n  A\n}\n", "F(5), F(7)", "refused at Sub" },
    };

    private static string Outcome(RunResult result)
    {
        if (result is RunResult.Success success)
            return string.Join(", ", success.Atoms.Select(atom => atom.ToString()));
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, error.Code);
        var source = error.Source;
        while (source is EvalError.WithContext context) source = context.Inner;
        return "refused at " + Assert.IsType<EvalError.LocalOnlyProperty>(source).PropertyName;
    }

    [Theory]
    [MemberData(nameof(SiteAndImpossibleCheckPins))]
    public async Task EachCheckIsChargedAtItsSite_AndAnImpossibleOneChargesNothing(string name, string body, string row, string expected)
    {
        _ = name;
        var source = body + row + "\n";
        // No declaration publishes a requirement no level of its chain can supply (the fail-closed entry is retired).
        Assert.Empty(ExposureCensus.CensusRunner.UnsuppliedRequirements(SourceProvenance.ParseValid(source).Root));
        foreach (var result in await BothEngines(source))
            Assert.Equal(expected, Outcome(result));
    }

    /// <summary>
    /// Q3: an open target that names a missing member through a block-headed reference is unresolved, exactly as
    /// through a named reference, at the same position.
    /// </summary>
    [Fact]
    public void MissingMemberThroughABlockHeadedReference_IsUnresolved_LikeItsNamedTwin()
    {
        var blockHeaded = SourceProvenance.ParseAllowingDiagnostics(
            "F(y) = {\n  open L.Missing\n  L = {\n    public Sub = {\n      public Q = y\n      0\n    }\n  }.Sub\n  1\n}\nF(5)\n");
        var named = SourceProvenance.ParseAllowingDiagnostics(
            "F(y) = {\n  open L.Missing\n  Lib = {\n    public Sub = {\n      public Q = y\n      0\n    }\n  }\n  L = Lib.Sub\n  1\n}\nF(5)\n");
        var expected = Assert.Single(named.Diagnostics, diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
        var actual = Assert.Single(blockHeaded.Diagnostics, diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, expected.Code);
        Assert.Equal(expected.Code, actual.Code);
        Assert.Equal(expected.Span, actual.Span);
    }

    /// <summary>The intermediate readers of a chain are charged too: <c>M = L0.T</c> crosses <c>L0 = Lib.Sub</c>.</summary>
    [Fact]
    public void ChainLinkThatSelectsAMember_IsLocalOnly()
    {
        var source = "F(y) = {\n  Lib = {\n    public Sub = {\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  L0 = Lib.Sub\n  M = L0.T\n  A = M.Q + 0\n  A\n}\n" + "F(5)\n";
        var m = Reader(source, "M");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, m.Exposure);
        Assert.Equal(["y"], m.RequiredAncestorParameters);
    }

    /// <summary>A block-headed reference <c>L = { … }.Sub</c> selects <c>Sub</c>: <c>L</c> itself is local-only.</summary>
    [Fact]
    public void BlockHeadedReference_IsLocalOnly()
    {
        var source = "F(y) = {\n  Lib = {\n    public Sub = {\n      public Q = 1\n      y\n    }\n    0\n  }\n  L = { public Sub = { public Q = 1\n y } }.Sub\n  A = L.Q + 0\n  A\n}\n" + "F(5)\n";
        var l = Reader(source, "L");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, l.Exposure);
        Assert.Equal(["y"], l.RequiredAncestorParameters);
    }

    /// <summary>The clause family reading <c>L.Q</c> in a branch body is charged at the family.</summary>
    [Fact]
    public void ClauseBranchReader_IsLocalOnly()
    {
        var source = "F(y) = {\n  L = Lib.Sub\n  G(0) = L.Q + 0\n  G(n) = n\n  A = G(0) + 0\n  Lib = {\n    public Sub = {\n      public Q = 1\n      public G(x) = x\n      public T = {\n        public Q = 1\n      }\n      y\n    }\n    0\n  }\n  A\n}\n" + "F(5)\n";
        var g = Reader(source, "G");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, g.Exposure);
        Assert.Equal(["y"], g.RequiredAncestorParameters);
    }

    [Fact]
    public async Task HostFamilyOwnedOpens_ChargeAnUnusedTargetWalk()
    {
        static Algorithm.User Body(params Expr[] rows) => new(null, [], [], [], rows);
        var lib = Body(new Expr.Num(0)) with
        {
            Properties = [new Property("Sub", Body(new Expr.Param("y")), true)],
        };
        var other = Body() with { Properties = [new Property("Q", Body(new Expr.Num(1)), true)] };
        var family = new Algorithm.Conditional(null,
            [new Expr.DotCall(new Expr.Resolve("Lib"), "Sub", null), new Expr.Resolve("Other")],
            [new CondBranch(new Pattern.LitInt(0), Body(new Expr.Num(1))),
             new CondBranch(new Pattern.Bind("k"), Body(new Expr.Resolve("Q")))]);
        var f = (Algorithm.User)Body(new Expr.Call(new Expr.Resolve("G"), [new Expr.Num(1)])).WithParams(["y"]) with
        {
            Properties = [new Property("Lib", lib), new Property("Other", other), new Property("G", family)],
        };
        foreach (var escaped in new[] { false, true })
        {
            var root = Body(new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(5)])) with
            {
                Properties = [new Property("F", f)],
            };
            if (escaped) root = root with { Output = [.. root.Output, new Expr.DotCall(new Expr.Resolve("F"), "G", [new Expr.Num(1)])] };
            var exposed = PropertyExposureResolver.Resolve(root);
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(exposed, "F", "G"), ("y", 0));
            var expression = new Expr.AlgorithmExpr(exposed);
            foreach (var result in new[] { Evaluator.Run(expression),
                await Evaluator.RunAsync(expression, new AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache()) })
            {
                if (escaped)
                {
                    Assert.True(result.IsError);
                    var error = result.Error;
                    while (error is EvalError.WithContext context) error = context.Inner;
                    Assert.Equal("G", Assert.IsType<EvalError.LocalOnlyProperty>(error).PropertyName);
                }
                else
                {
                    Assert.False(result.IsError);
                    Assert.Equal(new Result.Atom(1), result.Value);
                }
            }
        }
    }
}
