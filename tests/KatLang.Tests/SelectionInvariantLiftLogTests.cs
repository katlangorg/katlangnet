namespace KatLang.Tests;

/// <summary>
/// THE SELECTION INVARIANT's rewrite-side record (B3-5★, ledger S-10): <see cref="ImplicitArgumentResolver.OpenBodyLiftLog"/>
/// keeps the callees an open body's rewrite lifted in role-walk order, and
/// <see cref="ImplicitArgumentResolver.OpenBodyLiftLog.Disagreement"/> compares them with the dependencies the selected
/// signature was composed from. A disagreement is an internal defect of implicit-argument resolution — no program can
/// produce one — so the negative cases drive the log directly, exactly as the rewrite calls it: a lift per lifting
/// reference, a dot edge's arguments before its receiver, the output rows before the hoisted deconstruction right-hand
/// sides, and a memo hit where a shared node is served. The positive end-to-end shapes (an edge's receiver and
/// arguments, a right-hand side before its row, two spellings of one callee) are in <c>UnifiedFormulaLiftingTests</c>.
/// </summary>
public class SelectionInvariantLiftLogTests
{
    /// <summary>A callee: one static identity, one composed signature object.</summary>
    private sealed class Callee(string name, params string[] parameters)
    {
        public object Identity { get; } = new();

        public string Name { get; } = name;

        public CallableSignature Signature { get; } = CallableSignature.FromInferredPatterns(
            name, parameters.Select(static parameter => (ParameterPattern)new CaptureParameterPattern(parameter)).ToArray());

        /// <summary>The same callee spelled another way (<c>pow</c> / <c>Math.Pow</c>): its own, equal signature object.</summary>
        public IReadOnlyList<ParameterPattern> OtherSpelling { get; } = parameters
            .Select(static parameter => (ParameterPattern)new CaptureParameterPattern(parameter)).ToArray();

        public ImplicitArgumentResolver.LiftedDependency Dependency
            => new(Name, Signature, new Expr.Resolve(Name), Identity);
    }

    private static readonly Callee A = new("A", "a");
    private static readonly Callee B = new("B", "b");
    private static readonly Callee C = new("C", "c");

    private static void Lift(ImplicitArgumentResolver.OpenBodyLiftLog log, Callee callee)
        => log.Record(callee.Identity, callee.Signature.ParameterPatterns, callee.Name);

    private static ImplicitArgumentResolver.OpenBodyLiftLog OneRow(params Callee[] lifted)
    {
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
        log.BeginRow();
        foreach (var callee in lifted)
            Lift(log, callee);
        log.EndRows();
        log.EndSources();
        return log;
    }

    private static ImplicitArgumentResolver.LiftedDependency[] Composed(params Callee[] callees)
        => callees.Select(static callee => callee.Dependency).ToArray();

    // ── Agreement ──────────────────────────────────────────────────────────────────────────

    [Fact]
    public void SameCalleesInTheSameOrder_Agree()
    {
        Assert.Null(OneRow(A, B, C).Disagreement(Composed(A, B, C)));
        Assert.Null(OneRow().Disagreement(Composed()));
    }

    [Fact]
    public void ALaterLiftOfALiftedCallee_AddsNothing_WhateverSpellingForwardsIt()
    {
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
        log.BeginRow();
        Lift(log, A);
        Lift(log, B);
        Lift(log, A);
        log.Record(A.Identity, A.OtherSpelling, "Math.A");
        log.EndRows();
        log.EndSources();
        Assert.Null(log.Disagreement(Composed(A, B)));
    }

    // ── Disagreement: order, membership, signature ─────────────────────────────────────────

    [Fact]
    public void FirstContributionsOfDistinctCallees_InAnotherOrder_Disagree()
    {
        var disagreement = OneRow(B, A).Disagreement(Composed(A, B));
        Assert.Equal("the lifted callee 'B' at position 1, where it was composed from 'A'", disagreement);
    }

    [Fact]
    public void AComposedCalleeNoRowLifts_Disagrees()
    {
        Assert.Equal("the lifted callee 'B', which no row lifts", OneRow(A).Disagreement(Composed(A, B)));
        Assert.Equal("the lifted callee 'A', which no row lifts", OneRow().Disagreement(Composed(A)));
    }

    [Fact]
    public void ALiftedCalleeTheCompositionLacks_Disagrees()
    {
        Assert.Equal("the callee 'C', which its rows lift after every composed one", OneRow(A, B, C).Disagreement(Composed(A, B)));
        Assert.Equal("the lifted callee 'C' at position 2, where it was composed from 'B'", OneRow(A, C, B).Disagreement(Composed(A, B)));
    }

    [Fact]
    public void AFirstLiftForwardingAnotherSignatureObject_Disagrees_EvenWithEqualContent()
    {
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
        log.BeginRow();
        log.Record(A.Identity, A.OtherSpelling, "Math.A");
        Lift(log, A);
        log.EndRows();
        log.EndSources();
        Assert.Equal(
            "the lifted callee 'A', whose first lift forwards another signature than it was composed with",
            log.Disagreement(Composed(A)));
    }

    // ── The rewrite's own order, read in role-walk order ───────────────────────────────────

    [Fact]
    public void ADotEdgesReceiverLifts_ReadBeforeItsArgumentLifts()
    {
        // `(A + 0).F(B + 0)`: the rewrite lifts B (the argument) before A (the receiver); the role walk reads A first.
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
        log.BeginRow();
        log.BeginEdgeArguments();
        Lift(log, B);
        log.BeginEdgeReceiver();
        Lift(log, A);
        log.EndEdgeReceiver();
        Lift(log, C);
        log.EndRows();
        log.EndSources();
        Assert.Null(log.Disagreement(Composed(A, B, C)));
        Assert.NotNull(log.Disagreement(Composed(B, A, C)));
    }

    [Fact]
    public void NestedDotEdges_ReadInRoleWalkOrder()
    {
        // `(A + 0).F(B + 0).F(C + 0)`: the rewrite lifts C, B, A; the role walk reads A, B, C.
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
        log.BeginRow();
        log.BeginEdgeArguments();
        Lift(log, C);
        log.BeginEdgeReceiver();
        log.BeginEdgeArguments();
        Lift(log, B);
        log.BeginEdgeReceiver();
        Lift(log, A);
        log.EndEdgeReceiver();
        log.EndEdgeReceiver();
        log.EndRows();
        log.EndSources();
        Assert.Null(log.Disagreement(Composed(A, B, C)));

        // An edge whose arguments lift nothing continues after its receiver's lifts.
        var noArguments = new ImplicitArgumentResolver.OpenBodyLiftLog();
        noArguments.BeginRow();
        noArguments.BeginEdgeArguments();
        noArguments.BeginEdgeReceiver();
        Lift(noArguments, A);
        noArguments.EndEdgeReceiver();
        Lift(noArguments, B);
        noArguments.EndRows();
        noArguments.EndSources();
        Assert.Null(noArguments.Disagreement(Composed(A, B)));
    }

    [Fact]
    public void HoistedRightHandSides_ReadBeforeTheRowTheyAreWrittenBefore_InPropertyOrder()
    {
        // Rows 0 and 1 lift A and C; the right-hand sides are rewritten afterwards: one before row 1 (B), one before row 0
        // (D, then E, in property order), one written after every row (F).
        var d = new Callee("D", "d");
        var e = new Callee("E", "e");
        var f = new Callee("F", "f");
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
        log.BeginRow();
        Lift(log, A);
        log.BeginRow();
        Lift(log, C);
        log.EndRows();
        log.EnterSource(1);
        Lift(log, B);
        log.EnterSource(0);
        Lift(log, d);
        log.EnterSource(0);
        Lift(log, e);
        log.EnterSource(2);
        Lift(log, f);
        log.EndSources();
        Assert.Null(log.Disagreement(Composed(d, e, A, B, C, f)));
        Assert.NotNull(log.Disagreement(Composed(A, B, C, d, e, f)));
    }

    [Fact]
    public void ARightHandSideBeforeARowThatLiftsNothing_StillPrecedesTheNextRowsRightHandSide()
    {
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
        log.BeginRow();
        log.BeginRow();
        Lift(log, C);
        log.EndRows();
        log.EnterSource(1);
        Lift(log, B);
        log.EnterSource(0);
        Lift(log, A);
        log.EndSources();
        Assert.Null(log.Disagreement(Composed(A, B, C)));
    }

    // ── Shared rewrite segments preserve order without expanding logical paths ─────────────

    [Fact]
    public void AMemoHitOutsideAReorderedStretch_KeepsTheOrder()
    {
        var node = new Expr.Resolve("A");
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
        log.BeginRow();
        log.BeginNode();
        Lift(log, A);
        log.EndNode(node, LiftingRole.Value);
        log.NoteMemoHit(node, LiftingRole.Value);
        log.BeginEdgeArguments();
        log.NoteMemoHit(node, LiftingRole.Value);
        Lift(log, B);
        log.BeginEdgeReceiver();
        log.EndEdgeReceiver();
        log.NoteMemoHit(node, LiftingRole.Value);
        log.EndRows();
        log.EndSources();
        Assert.Null(log.Disagreement(Composed(A, B)));
        Assert.NotNull(log.Disagreement(Composed(B, A)));
    }

    [Theory]
    [InlineData("receiver")]
    [InlineData("right-hand side")]
    public void AMemoHitInsideAReorderedStretch_PreservesTheWholeOrderedComparison(string stretch)
    {
        ImplicitArgumentResolver.OpenBodyLiftLog Log(params Callee[] lifted)
        {
            var node = new Expr.Resolve("shared");
            var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
            log.BeginRow();
            log.BeginNode();
            foreach (var callee in lifted)
                Lift(log, callee);
            log.EndNode(node, LiftingRole.Value);
            if (stretch == "receiver")
            {
                log.BeginEdgeArguments();
                log.BeginEdgeReceiver();
                log.NoteMemoHit(node, LiftingRole.Value);
                log.EndEdgeReceiver();
                log.EndRows();
            }
            else
            {
                log.EndRows();
                log.EnterSource(0);
                log.NoteMemoHit(node, LiftingRole.Value);
            }

            log.EndSources();
            return log;
        }

        Assert.Equal("the lifted callee 'B' at position 1, where it was composed from 'A'", Log(B, A).Disagreement(Composed(A, B)));
        Assert.Null(Log(A, B).Disagreement(Composed(A, B)));
        Assert.Equal("the lifted callee 'B', which no row lifts", Log(A).Disagreement(Composed(A, B)));
        Assert.Equal("the callee 'C', which its rows lift after every composed one", Log(A, C).Disagreement(Composed(A)));
        Assert.Equal("the callee 'A', which its rows lift after every composed one", Log(A).Disagreement(Composed()));

        var otherSignature = Log();
        otherSignature.Record(A.Identity, A.OtherSpelling, "Math.A");
        Assert.Equal(
            "the lifted callee 'A', whose first lift forwards another signature than it was composed with",
            otherSignature.Disagreement(Composed(A)));
    }

    [Fact]
    public void ASharedSegmentReachedFirstInAReceiver_KeepsTheFirstSignatureObject_AndCalleeOrder()
    {
        var shared = new Expr.Resolve("shared");
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
        log.BeginRow();
        log.BeginEdgeArguments();
        Lift(log, B);
        log.BeginNode();
        Lift(log, A);
        log.EndNode(shared, LiftingRole.Value);
        log.BeginEdgeReceiver();
        log.NoteMemoHit(shared, LiftingRole.Value);
        log.EndEdgeReceiver();
        log.Record(A.Identity, A.OtherSpelling, "Math.A");
        log.EndRows();
        log.EndSources();

        Assert.Null(log.Disagreement(Composed(A, B)));
        Assert.NotNull(log.Disagreement(Composed(B, A)));
        var wrongFirst = A.Dependency with { Signature = CallableSignature.FromInferredPatterns("Math.A", A.OtherSpelling) };
        Assert.Equal("the lifted callee 'A', whose first lift forwards another signature than it was composed with",
            log.Disagreement([wrongFirst, B.Dependency]));
        Assert.NotNull(log.Disagreement(Composed(A, A, B)));
    }

    [Theory]
    [InlineData(12)]
    [InlineData(20)]
    public void ASharedTraceDiamond_VisitsEachSegmentOnce(int depth)
    {
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog();
        log.BeginRow();
        RecordDiamond(depth);
        log.EndRows();
        log.EndSources();
        Assert.Null(log.DisagreementWithWork(Composed(A), out var compared));
        Assert.Equal(2 * depth + 4, compared);

        Expr RecordDiamond(int level)
        {
            var node = new Expr.Resolve("node" + level);
            log.BeginNode();
            if (level == 0)
                Lift(log, A);
            else
                log.NoteMemoHit(RecordDiamond(level - 1), LiftingRole.Value);
            log.EndNode(node, LiftingRole.Value);
            return node;
        }
    }

    [Fact]
    public void RecordingAndComparison_ChargeActualStorageAndWork_AndRefusalIsTerminal()
    {
        var resources = new StaticQueryResourceBudget(StaticQueryLimits.Default);
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog(resources);
        var start = resources.MetadataUnits;
        log.BeginRow();
        Lift(log, A);
        log.EndRows();
        Assert.True(resources.MetadataUnits > start);
        var before = resources.WorkCharged;
        Assert.Null(log.Disagreement(Composed(A)));
        Assert.True(resources.WorkCharged > before);

        var tight = new StaticQueryResourceBudget(StaticQueryLimits.Default with { MaxStorageUnits = 4 });
        var refused = new ImplicitArgumentResolver.OpenBodyLiftLog(tight);
        Assert.Throws<StaticQueryLimitExceededException>(() => Lift(refused, A));
        Assert.True(tight.IsFailed);
        Assert.Throws<InvalidOperationException>(() => Lift(refused, A));
    }

    [Fact]
    public void CancellationDuringComparison_KeepsTheToken_AndFailsTheLedger()
    {
        using var cancellation = new CancellationTokenSource();
        var resources = new StaticQueryResourceBudget(StaticQueryLimits.Default);
        var log = new ImplicitArgumentResolver.OpenBodyLiftLog(resources, cancellation.Token);
        log.BeginRow();
        Lift(log, A);
        log.EndRows();
        cancellation.Cancel();
        var error = Assert.Throws<OperationCanceledException>(() => log.Disagreement(Composed(A)));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.True(resources.IsFailed);
        Assert.Throws<InvalidOperationException>(() => log.Disagreement(Composed(A)));
    }

    [Theory]
    [InlineData("receiver")]
    [InlineData("right-hand side")]
    public void HostDagAcrossReorderedStretches_MatchesTheDuplicatedTree_AndKeepsSharing(string stretch)
    {
        var diagnostics = new DiagnosticBag();
        var dag = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(Root(shared: true), diagnostics: diagnostics);
        var tree = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(Root(shared: false));
        Assert.Empty(diagnostics);
        Assert.Equal(LeanAstEncoder.EncodeProgram(tree), LeanAstEncoder.EncodeProgram(dag));
        var f = Assert.IsType<Algorithm.User>(dag.Properties[^1].Value);
        Assert.Equal(new[] { "p", "q" }, f.Params);
        if (stretch == "receiver")
        {
            var edge = Assert.IsType<Expr.DotCall>(Assert.Single(f.Output));
            Assert.Same(edge.Target, Assert.IsType<Expr.Binary>(Assert.Single(edge.Args!)).Right);
        }
        else
            Assert.Same(f.Properties[0].Value.Output[0], Assert.IsType<Expr.Binary>(Assert.Single(f.Output)).Right);

        Algorithm.User Root(bool shared)
        {
            static Algorithm.User Body(params Expr[] rows) => new(null, [], [], [], rows);
            static Expr AReference() => new Expr.Binary(BinaryOp.Add, new Expr.Resolve("A"), new Expr.Num(0));
            var a = AReference();
            var b = new Expr.Binary(BinaryOp.Add, new Expr.Resolve("B"), shared ? a : AReference());
            var f = stretch == "receiver"
                ? Body(new Expr.DotCall(a, "pow", new OutputBundle([b])))
                : Body(b) with { Properties = [new Property("source", Body(a) with { AssignmentDeconstructionRowIndex = 0 })] };
            return Body(new Expr.Num(0)) with
            {
                Properties =
                [
                    new Property("A", Body(new Expr.Param("p")) with { ParameterPatterns = [new CaptureParameterPattern("p")], HasExplicitParameterList = true }),
                    new Property("B", Body(new Expr.Param("q")) with { ParameterPatterns = [new CaptureParameterPattern("q")], HasExplicitParameterList = true }),
                    new Property("F", f),
                ],
            };
        }
    }
}
