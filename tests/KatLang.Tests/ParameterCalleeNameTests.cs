using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// A PARAMETER IS NAMED AS WRITTEN in every report that names a callee or a receiver (Lean
/// aligned 2026-10-13). A parameter is a reference, so the call frame of <c>f(x)</c>, a clause
/// family's <see cref="EvalError.NoMatchingBranch"/>, the receiver of a dot-call frame, the object
/// of a <see cref="EvalError.LocalOnlyProperty"/>, and the name inside a
/// <see cref="EvalError.BadOpenForm"/> or alias-target message all name the parameter — what the
/// programmer wrote, just as a call through a callable alias names the written alias. C# always
/// rendered <see cref="Expr.Param"/> as its name (<c>ExprNameRenderer</c>, the
/// <c>CallDiagnosticName</c> leaf); Lean's minimal <c>openExprName</c> had no parameter arm until
/// 2026-10-13 and wrote the <c>(param)</c> kind placeholder instead — in frame text and in
/// structured payloads alike (<c>Apply(f, x) = f(x)</c> / <c>Apply(F, 5)</c> was
/// <c>noMatchingBranch "(param)"</c>). The error categories always agreed, so the
/// category-comparing differential corpora could not see it.
///
/// <para>The cross-engine table (<see cref="Cases"/>) is pinned on both sides with the same
/// programs and the same expectations: <c>lean/CoreTests/HigherOrderCalls.lean</c> § "Parameter
/// callee and receiver names" holds, for every case, the <see cref="LeanAstEncoder"/> encoding of
/// the case's AST (elaborated from source, or host-built) and a guard on the same neutral tree,
/// and <see cref="LeanTable_HoldsTheSameProgramAndExpectation"/> checks that it does. The neutral
/// tree keeps every frame with its full description — receivers included — outermost first,
/// then the leaf with its payload (<see cref="NeutralTree"/>).</para>
/// </summary>
public class ParameterCalleeNameTests
{
    private const string LeanTablePath = "lean/CoreTests/HigherOrderCalls.lean";

    private sealed record NameCase(string Id, string? Source, Func<Algorithm.User>? HostRoot, string Expected)
    {
        /// <summary>The Lean fixture's name: <c>pcn</c> plus the id in PascalCase.</summary>
        public string LeanName
            => "pcn" + string.Concat(Id.Split('-').Select(static word => char.ToUpperInvariant(word[0]) + word[1..]));

        /// <summary>The program's root: the elaborated source, or the host-built tree.</summary>
        public Algorithm.User Root() => Source is { } source ? SourceProvenance.ParseValid(source).Root : HostRoot!();
    }

    private static NameCase FromSource(string id, string source, string expected) => new(id, source, null, expected);

    private static NameCase HostBuilt(string id, Func<Algorithm.User> root, string expected) => new(id, null, root, expected);

    private static readonly NameCase[] Cases =
    [
        FromSource("family-through-parameter-callee",
            "F(0) = 1\nF(1) = 2\nApply(f, x) = f(x)\nApply(F, 5)",
            "call Apply > call f > noMatchingBranch f"),
        FromSource("arity-through-parameter-callee",
            "Inc(z) = z + 1\nApply(f) = f(1, 2)\nApply(Inc)",
            "call Apply > call f > arityMismatch 1 2"),
        FromSource("value-through-parameter-callee",
            "Apply(f) = f(1)\nApply(5)",
            "call Apply > call f > notAnAlgorithm param(f)"),
        FromSource("branch-only-member-of-parameter-receiver",
            "C(0) = {\n    public Q = 1\n    0\n}\nC(1) = 2\nGet(obj) = obj.Q\nGet(C)",
            "call Get > dotCall .Q of obj > localOnlyProperty obj Q conditional"),
        FromSource("local-only-member-of-parameter-receiver",
            "G(x) = {\n    public Sub = {\n        public Q = 1\n        x\n    }\n    0\n}\nGet(obj) = obj.Sub\nGet(G)",
            "call Get > dotCall .Sub of obj > localOnlyProperty obj Sub captured [x]"),
        FromSource("callable-projection-of-parameter-receiver-path",
            "C(0) = {\n    public Q = 1\n    0\n}\nC(1) = 2\nApply(g) = g(1)\nGet(obj) = Apply(obj.Q)\nGet(C)",
            "call Get > call Apply > call g > localOnlyProperty obj Q conditional"),
        FromSource("member-read-through-parameter-receiver",
            "Lib = { public M(a) = a }\nGet(obj) = obj.M\nGet(Lib)",
            "call Get > dotCall .M of obj > arityMismatch 1 0"),
        FromSource("dot-fallback-through-parameter",
            "F(0) = 1\nF(1) = 2\nApply(f, x) = x.f\nApply(F, 5)",
            "call Apply > dotCall .f of x > noMatchingBranch f"),
        // OD-C (M4★): an open through a transparent reference navigates its target's path, and an
        // inaccessible member names that step's RECEIVER as written — `open A` with `A = G.Sub` reports
        // what `open G.Sub` reports, whether Sub is a runtime-target carrier or a static one.
        FromSource("open-reference-local-only-member",
            "G(x) = {\n    public Sub = {\n        public Q = 1\n        x\n    }\n    0\n}\nA = G.Sub\nP = {\n    open A\n    Q\n}\nP",
            "while resolving open: A > localOnlyProperty G Sub captured [x]"),
        FromSource("open-static-reference-local-only-member",
            "G(x) = {\n    public Sub = {\n        public Q = 1\n        x + 0\n    }\n    0\n}\nA = G.Sub\nP = {\n    open A\n    Q\n}\nP",
            "while resolving open: A > localOnlyProperty G Sub captured [x]"),
        FromSource("open-direct-local-only-member",
            "G(x) = {\n    public Sub = {\n        public Q = 1\n        x + 0\n    }\n    0\n}\nP = {\n    open G.Sub\n    Q\n}\nP",
            "while resolving open: G.Sub > localOnlyProperty G Sub captured [x]"),
        // A later step names its receiver path so far: Sub is accessible, its Inner is not.
        FromSource("open-reference-second-step-local-only-member",
            "G(x) = {\n    public Sub = {\n        public Inner = {\n            public Q = 1\n            x\n        }\n        0\n    }\n    0\n}\nA = G.Sub.Inner\nP = {\n    open A\n    Q\n}\nP",
            "while resolving open: A > localOnlyProperty G.Sub Inner captured [x]"),
        FromSource("open-direct-second-step-local-only-member",
            "G(x) = {\n    public Sub = {\n        public Inner = {\n            public Q = 1\n            x\n        }\n        0\n    }\n    0\n}\nP = {\n    open G.Sub.Inner\n    Q\n}\nP",
            "while resolving open: G.Sub.Inner > localOnlyProperty G.Sub Inner captured [x]"),
        // A loop step's cell keeps its WRITTEN source through parameter transport (LOOP-08), so
        // the step is named by the argument written for it, F — never by the parameter step.
        FromSource("loop-step-through-parameter",
            "F(0) = 1\nRun(step) = repeat(step(5), 1)\nRun(F)",
            "call Run > call repeat > call F > noMatchingBranch F"),
        // Host-built trees: the front end refuses a parameter-headed open target
        // (OpenTargetIsParameter). An alias over a parameter is a RUNTIME-TARGET alias (FWD-02,
        // META-S3-2), admitted before evaluation; here nothing binds `f`, so its bare read is the
        // parameter read's own unknown name.
        HostBuilt("host-open-target-parameter",
            static () => new Algorithm.User(null, [], [new Expr.Param("f")], [], [new Expr.Resolve("Zzz")]),
            "badOpenForm param: f"),
        HostBuilt("host-alias-target-parameter",
            static () => new Algorithm.User(null, [], [],
                [new Property("A", new Algorithm.Alias(null, [], [], new Expr.Param("f")))],
                [new Expr.Resolve("A")]),
            "unknownName f"),
    ];

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var nameCase in Cases)
            data.Add(nameCase.Id);
        return data;
    }

    private static NameCase CaseById(string id) => Cases.Single(nameCase => nameCase.Id == id);

    [Theory]
    [MemberData(nameof(CaseIds))]
    public async Task EveryRoute_ReportsTheTableTree(string id)
    {
        var nameCase = CaseById(id);
        var ast = new Expr.AlgorithmExpr(nameCase.Root());

        var sync = Evaluator.Run(ast);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var passThrough = new PassThroughAsyncZeroArgPropertyResultCache();
        var (twin, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: passThrough));
        var suspending = new SuspendingAsyncZeroArgPropertyResultCache();
        var (suspended, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: suspending));

        Assert.True(sync.IsError);
        Assert.Equal(nameCase.Expected, NeutralTree(sync.Error));
        Assert.Equal(nameCase.Expected, NeutralTree(generic.Error));
        Assert.Equal(nameCase.Expected, NeutralTree(twin.Error));
        Assert.Equal(nameCase.Expected, NeutralTree(suspended.Error));
        Assert.Equal(0, passThrough.SyncAccesses);
        Assert.Equal(0, suspending.SyncAccesses);

        // Beyond the neutral tree, the complete C# error — every context, payload and span —
        // is one tree on every route.
        var tree = DescribeErrorTree(sync.Error);
        Assert.Equal(tree, DescribeErrorTree(generic.Error));
        Assert.Equal(tree, DescribeErrorTree(twin.Error));
        Assert.Equal(tree, DescribeErrorTree(suspended.Error));
    }

    [Theory]
    [MemberData(nameof(CaseIds))]
    public void LeanTable_HoldsTheSameProgramAndExpectation(string id)
    {
        var nameCase = CaseById(id);
        var leanText = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanTablePath)).ReplaceLineEndings("\n");
        var encoded = LeanAstEncoder.EncodeProgram(nameCase.Root());
        var fixture =
            $"def {nameCase.LeanName} : Expr :=\n" +
            $"  {encoded}\n" +
            $"#guard pcnObserve {nameCase.LeanName} == {LeanAstEncoder.QuoteString(nameCase.Expected)}\n";

        Assert.True(
            leanText.Contains(fixture, StringComparison.Ordinal),
            $"{LeanTablePath} must hold the case '{id}' exactly as:\n{fixture}");
    }

    [Fact]
    public void LeanTable_HoldsNoCaseTheCSharpTableLacks()
    {
        var leanText = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanTablePath)).ReplaceLineEndings("\n");
        var leanNames = leanText.Split('\n')
            .Where(static line => line.StartsWith("#guard pcnObserve ", StringComparison.Ordinal))
            .Select(static line => line["#guard pcnObserve ".Length..].Split(' ')[0])
            .ToArray();

        Assert.Equal(Cases.Select(static nameCase => nameCase.LeanName), leanNames);
    }

    /// <summary>
    /// The C# half of the renderer mirror: a parameter, and a dotted path from one, render as
    /// written in the base diagnostic spelling and in every frame built from it (Lean:
    /// <c>openExprName</c>'s <c>.param</c> arm, pinned by the <c>#guard</c>s beside the table).
    /// </summary>
    [Fact]
    public void ParameterReference_RendersAsItsWrittenName()
    {
        var parameter = new Expr.Param("f");
        var path = new Expr.DotCall(new Expr.Param("obj"), "Q", null);

        Assert.Equal("f", Evaluator.OpenExprName(parameter));
        Assert.Equal("obj.Q", Evaluator.OpenExprName(path));
        Assert.Equal("while evaluating call to f", new CallContext(Evaluator.OpenExprName(parameter)).ToString());
    }

    /// <summary>
    /// The neutral tree shared with the Lean table: every frame with its full description,
    /// outermost first, then the leaf with its payload.
    /// </summary>
    private static string NeutralTree(EvalError error)
    {
        var parts = new List<string>();
        while (error is EvalError.WithContext context)
        {
            parts.Add(context.ErrorContext switch
            {
                CallContext call => $"call {call.CalleeDescription}",
                DotCallContext dotCall => $"dotCall .{dotCall.PropertyName} of {dotCall.ReceiverDescription}",
                PropertyEvaluationContext property => $"property {property.PropertyName}",
                var other => other.ToString(),
            });
            error = context.Inner;
        }

        parts.Add(error switch
        {
            EvalError.NoMatchingBranch branch => $"noMatchingBranch {branch.AlgorithmName}",
            EvalError.ArityMismatch arity => $"arityMismatch {arity.Expected} {arity.Actual}",
            EvalError.NotAnAlgorithm notAnAlgorithm => $"notAnAlgorithm {notAnAlgorithm.Description}",
            EvalError.LocalOnlyProperty localOnly =>
                $"localOnlyProperty {localOnly.ObjectDesc} {localOnly.PropertyName} {NeutralExposure(localOnly)}",
            EvalError.BadOpenForm badOpenForm => $"badOpenForm {badOpenForm.Reason}",
            EvalError.IllegalInEval illegal => $"illegalInEval {illegal.Reason}",
            EvalError.UnknownName unknown => $"unknownName {unknown.Name}",
            _ => $"other {error.GetType().Name}",
        });
        return string.Join(" > ", parts);
    }

    /// <summary>A local-only member's exposure, as the neutral tree spells it (Lean: <c>pcnExposure</c>).</summary>
    private static string NeutralExposure(EvalError.LocalOnlyProperty localOnly) => localOnly.Exposure switch
    {
        PropertyExposure.LocalOnlyConditionalAlgorithm => "conditional",
        PropertyExposure.LocalOnlyCapturedAncestorParameters =>
            $"captured [{string.Join(", ", localOnly.RequiredParameters ?? [])}]",
        var other => $"other {other}",
    };
}
