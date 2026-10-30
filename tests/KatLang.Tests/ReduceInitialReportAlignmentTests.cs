using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// A BUILTIN VALUE SLOT'S REJECTION REPORT JUDGES THE CALLABLE ITS ARGUMENT NAMES (Lean aligned
/// 2026-10-13). A builtin's arguments are the call's supplied cells, each with its WRITTEN source;
/// when a VALUE slot's demand fails, the call item records the cell's CALLABLE projection unless
/// the written slot is a parameter (<c>FinishNeedCallItemDemand</c>), so the slot reports the
/// zero-argument law's verdict keyed by the written source, and <c>reduce</c>'s initial
/// accumulator its dedicated report (<c>ReduceInitialRejection</c>; PV-05: the dedicated
/// accumulator hint stays as the value slot's rejection report). A written parameter keeps its
/// established failure (CALL-06), and a clause family the law's own
/// <see cref="EvalError.NoMatchingBranch"/>. C# kept this through Model C; Lean's call items lost
/// the written source and the projection there (2026-10-02), so until 2026-10-13 Lean reported
/// the cell's own failure — <c>reduce([1, 2], Add, Inc)</c> was the property-arity error,
/// <c>reduce(xs, Add, { x + 1 })</c> even <see cref="EvalError.UnresolvedImplicitParams"/>, and
/// <c>count(Lib.M)</c> kept the member's dot-call frame. The error categories mostly agreed, so
/// the category-comparing differential corpora could not see it.
///
/// <para>The cross-engine table (<see cref="Cases"/>) is pinned on both sides with the same
/// programs and the same expectations: <c>lean/CoreTests/ValueDemand.lean</c> § "Builtin
/// VALUE-slot rejection reports" holds, for every case, the <see cref="LeanAstEncoder"/>
/// encoding of the case's elaborated AST and a guard on the same neutral tree, and
/// <see cref="LeanTable_HoldsTheSameProgramAndExpectation"/> checks that it does. A program that
/// would otherwise lift its reference runs inside a closed list (<c>Probe(unused) = …</c>), so the
/// reference stays the runtime zero-argument demand.</para>
/// </summary>
public class ReduceInitialReportAlignmentTests
{
    private const string LeanTablePath = "lean/CoreTests/ValueDemand.lean";

    private sealed record TableCase(string Id, string Source, string Expected)
    {
        /// <summary>The Lean fixture's name: <c>rir</c> plus the id in PascalCase.</summary>
        public string LeanName
            => "rir" + string.Concat(Id.Split('-').Select(static word => char.ToUpperInvariant(word[0]) + word[1..]));
    }

    private static TableCase FromSource(string id, string source, string expected) => new(id, source, expected);

    private static readonly TableCase[] Cases =
    [
        // reduce's initial accumulator: a written callable that cannot supply a zero-argument value
        // gets reduce's dedicated report, whatever names or spells it.
        FromSource("reduce-initial-property",
            "Inc(x) = x + 1\nAdd(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, Inc)\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        FromSource("reduce-initial-ignored-parameter",
            "K(x) = 5\nAdd(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, K)\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        FromSource("reduce-initial-block",
            "Add(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, { x + 1 })\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        // M4★: a written `{ Inc }` is a structural forwarding carrier; its failed slot names the
        // carrier's VALUE terminal, Inc, so it reports exactly as the written `Inc` does (FA-OQ-1) —
        // and so does a named carrier, while `count(C)` keeps the law's report keyed by the written `C`.
        FromSource("reduce-initial-inline-alias",
            "Inc(x) = x + 1\nAdd(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, { Inc })\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        FromSource("reduce-initial-named-carrier",
            "C = { Inc }\nInc(x) = x + 1\nAdd(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, C)\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        FromSource("count-named-carrier",
            "C = { Inc }\nInc(x) = x + 1\nProbe(unused) = count(C)\nProbe(0)",
            "call Probe > call count > property C > arityMismatch 1 0"),
        // The same carriers in a run with runtime projections (Unused's `W = q` is a runtime-row alias, so the run
        // is pre-marked): the carrier cell stays an identity-only cell, and its failed slot still names the carrier's
        // VALUE terminal, by observing the chase the failed demand already ran (C#'s non-initiating PeekResolve).
        FromSource("reduce-initial-named-carrier-premarked",
            "C = { Inc }\nInc(x) = x + 1\nAdd(e, a) = e + a\nUnused(q) = {\n    W = q\n    W\n}\nProbe(unused) = reduce([1, 2], Add, C)\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        FromSource("reduce-initial-inline-alias-premarked",
            "Inc(x) = x + 1\nAdd(e, a) = e + a\nUnused(q) = {\n    W = q\n    W\n}\nProbe(unused) = reduce([1, 2], Add, { Inc })\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        FromSource("reduce-initial-alias",
            "Inc(x) = x + 1\nA = Inc\nAdd(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, A)\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        FromSource("reduce-initial-member",
            "Lib = { public M(a) = a }\nAdd(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, Lib.M)\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        FromSource("reduce-initial-structural-pattern",
            "P((p, q)) = p\nAdd(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, P)\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        FromSource("reduce-initial-dotted",
            "Inc(x) = x + 1\nAdd(e, a) = e + a\nProbe(unused) = [1, 2].reduce(Add, Inc)\nProbe(0)",
            "call Probe > dotCall .reduce > reduceInitial > badArity"),
        FromSource("reduce-initial-empty-collection",
            "Inc(x) = x + 1\nAdd(e, a) = e + a\nProbe(unused) = reduce([], Add, Inc)\nProbe(0)",
            "call Probe > call reduce > reduceInitial > badArity"),
        // A transported collector cell keeps its own written source (Inc), so it is judged too —
        // and keyed by that source in every other value slot (Inc's property frame).
        FromSource("reduce-initial-collector-transport",
            "Inc(x) = x + 1\nAdd(e, a) = e + a\nG(*xs) = reduce([1, 2], Add, xs*)\nG(Inc)",
            "call G > call reduce > reduceInitial > badArity"),
        FromSource("count-collector-transport",
            "Inc(x) = x + 1\nG(*xs) = count(xs*)\nG(Inc)",
            "call G > call count > property Inc > arityMismatch 1 0"),
        // Controls: the law's own report (a family), a written parameter's established failure
        // (CALL-06), and a value.
        FromSource("reduce-initial-family",
            "F(0) = 1\nF(n) = n\nAdd(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, F)\nProbe(0)",
            "call Probe > call reduce > noMatchingBranch F"),
        FromSource("reduce-initial-through-parameter",
            "Inc(x) = x + 1\nAdd(e, a) = e + a\nG(v) = reduce([1, 2], Add, v)\nG(Inc)",
            "call G > call reduce > property Inc > arityMismatch 1 0"),
        FromSource("reduce-initial-value",
            "Add(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, 7)\nProbe(0)",
            "ok 10"),
        // Every other builtin VALUE slot: the zero-argument law's report keyed by the WRITTEN
        // source — a navigated member reports the bare arity, without its value read's dot-call
        // frame; a property keeps its property frame; a written parameter keeps its cell's report.
        FromSource("count-member",
            "Lib = { public M(a) = a }\nProbe(unused) = count(Lib.M)\nProbe(0)",
            "call Probe > call count > arityMismatch 1 0"),
        FromSource("count-nested-member",
            "Deep = { public Sub = { public N(b) = b } }\nProbe(unused) = count(Deep.Sub.N)\nProbe(0)",
            "call Probe > call count > arityMismatch 1 0"),
        FromSource("take-member",
            "Lib = { public M(a) = a }\nProbe(unused) = take([1, 2], Lib.M)\nProbe(0)",
            "call Probe > call take > arityMismatch 1 0"),
        FromSource("count-property",
            "Inc(x) = x + 1\nProbe(unused) = count(Inc)\nProbe(0)",
            "call Probe > call count > property Inc > arityMismatch 1 0"),
        FromSource("count-member-through-parameter",
            "Lib = { public M(a) = a }\nG(v) = count(v)\nG(Lib.M)",
            "call G > call count > dotCall .M > arityMismatch 1 0"),
    ];

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var tableCase in Cases)
            data.Add(tableCase.Id);
        return data;
    }

    private static TableCase CaseById(string id) => Cases.Single(tableCase => tableCase.Id == id);

    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    [Theory]
    [MemberData(nameof(CaseIds))]
    public async Task EveryRoute_ReportsTheTableTree(string id)
    {
        var tableCase = CaseById(id);
        var ast = Program(tableCase.Source);

        var sync = Evaluator.Run(ast);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);

        // A pre-marked row reaches the observation branch only while its run is pre-marked for runtime projections.
        Assert.Equal(id.EndsWith("-premarked", StringComparison.Ordinal), genericBudget.HasRuntimeProjections);
        var passThrough = new PassThroughAsyncZeroArgPropertyResultCache();
        var (twin, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: passThrough));
        var suspending = new SuspendingAsyncZeroArgPropertyResultCache();
        var (suspended, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: suspending));

        Assert.Equal(tableCase.Expected, Observe(sync));
        Assert.Equal(tableCase.Expected, Observe(generic));
        Assert.Equal(tableCase.Expected, Observe(twin));
        Assert.Equal(tableCase.Expected, Observe(suspended));
        Assert.Equal(0, passThrough.SyncAccesses);
        Assert.Equal(0, suspending.SyncAccesses);

        // Beyond the neutral tree, the complete C# error — every context, payload and span —
        // is one tree on every route.
        if (sync.IsError)
        {
            var tree = DescribeErrorTree(sync.Error);
            Assert.Equal(tree, DescribeErrorTree(generic.Error));
            Assert.Equal(tree, DescribeErrorTree(twin.Error));
            Assert.Equal(tree, DescribeErrorTree(suspended.Error));
        }
    }

    [Theory]
    [MemberData(nameof(CaseIds))]
    public void LeanTable_HoldsTheSameProgramAndExpectation(string id)
    {
        var tableCase = CaseById(id);
        var leanText = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanTablePath)).ReplaceLineEndings("\n");
        var encoded = LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(tableCase.Source).Root);
        var fixture =
            $"def {tableCase.LeanName} : Expr :=\n" +
            $"  {encoded}\n" +
            $"#guard rirObserve {tableCase.LeanName} == {LeanAstEncoder.QuoteString(tableCase.Expected)}\n";

        Assert.True(
            leanText.Contains(fixture, StringComparison.Ordinal),
            $"{LeanTablePath} must hold the case '{id}' exactly as:\n{fixture}");
    }

    [Fact]
    public void LeanTable_HoldsNoCaseTheCSharpTableLacks()
    {
        var leanText = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanTablePath)).ReplaceLineEndings("\n");
        var leanNames = leanText.Split('\n')
            .Where(static line => line.StartsWith("#guard rirObserve ", StringComparison.Ordinal))
            .Select(static line => line["#guard rirObserve ".Length..].Split(' ')[0])
            .ToArray();

        Assert.Equal(Cases.Select(static tableCase => tableCase.LeanName), leanNames);
    }

    /// <summary>
    /// The public report of reduce's initial accumulator is the dedicated hint for every written
    /// spelling of a callable that cannot supply a zero-argument value — a property, a written
    /// block, a callable reference, an inline or named carrier (judged on its VALUE terminal,
    /// FA-OQ-1), a navigated member, a structural pattern — on the written and the dotted call alike.
    /// </summary>
    [Theory]
    [InlineData("Inc")]
    [InlineData("{ x + 1 }")]
    [InlineData("{ Inc }")]
    [InlineData("A")]
    [InlineData("C")]
    [InlineData("{ C }")]
    [InlineData("Lib.M")]
    [InlineData("P")]
    public void PublicReport_IsTheDedicatedInitialAccumulatorHint(string initial)
    {
        const string definitions =
            "Inc(x) = x + 1\nA = Inc\nC = { Inc }\nLib = { public M(a) = a }\nP((p, q)) = p\nAdd(e, a) = e + a\n";

        foreach (var call in new[] { $"reduce([1, 2], Add, {initial})", $"[1, 2].reduce(Add, {initial})" })
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(
                KatLangEngine.Run(definitions + "Probe(unused) = " + call + "\nProbe(0)"));
            var error = Assert.Single(failure.Errors);

            Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
            Assert.Contains("the last argument must be an initial accumulator value", error.Message);
        }
    }

    private static string Observe(EvalResult<Result> result)
        => result.IsError ? NeutralTree(result.Error) : "ok " + SemanticExplorerHarness.Neutral(result.Value);

    private static string Observe(EvalResult<Evaluator.CountedResult> result)
        => result.IsError ? NeutralTree(result.Error) : "ok " + SemanticExplorerHarness.Neutral(result.Value.Value);

    /// <summary>
    /// The neutral tree shared with the Lean table (<c>rirObserve</c>): the call, dot-call and
    /// property frames by kind — a dot-call frame without its receiver description, whose Lean
    /// <c>(kind)</c> spelling is a documented presentation difference — and reduce's
    /// initial-accumulator frame as <c>reduceInitial</c>; then the leaf with its payload. Omitted
    /// are the documented presentation differences: C#'s <see cref="ImplicitParameterContext"/> and
    /// output-less argument blame frames (<see cref="ArgumentEvaluationContext"/>,
    /// <see cref="ParameterEvaluationContext"/>), which have no Lean counterpart, and — on the
    /// Lean side only — Lean's builtin-arity description frame, which C# keeps on the
    /// <see cref="EvalError.ArityMismatch"/> leaf.
    /// </summary>
    private static string NeutralTree(EvalError error)
    {
        var parts = new List<string>();
        while (error is EvalError.WithContext context)
        {
            switch (context.ErrorContext)
            {
                case CallContext call:
                    parts.Add($"call {call.CalleeDescription}");
                    break;
                case DotCallContext dotCall:
                    parts.Add($"dotCall .{dotCall.PropertyName}");
                    break;
                case PropertyEvaluationContext property:
                    parts.Add($"property {property.PropertyName}");
                    break;
                case ReduceInitialAccumulatorContext:
                    parts.Add("reduceInitial");
                    break;
                case ImplicitParameterContext or ArgumentEvaluationContext or ParameterEvaluationContext:
                    break;
                default:
                    parts.Add(context.ErrorContext.ToString());
                    break;
            }

            error = context.Inner;
        }

        parts.Add(error switch
        {
            EvalError.ArityMismatch arity => $"arityMismatch {arity.Expected} {arity.Actual}",
            EvalError.BadArity => "badArity",
            EvalError.NoMatchingBranch branch => $"noMatchingBranch {branch.AlgorithmName}",
            EvalError.UnresolvedImplicitParams unresolved => $"unresolvedImplicitParams [{string.Join(", ", unresolved.ParamNames)}]",
            EvalError.NotAnAlgorithm notAnAlgorithm => $"notAnAlgorithm {notAnAlgorithm.Description}",
            EvalError.DivByZero => "divByZero",
            EvalError.MissingOutput => "missingOutput",
            _ => $"other {error.GetType().Name}",
        });
        return string.Join(" > ", parts);
    }
}
