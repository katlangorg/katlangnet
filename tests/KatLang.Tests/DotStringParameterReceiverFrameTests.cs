using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// THE <c>.string</c> RECEIVER OF A PARAMETER REPORTS WHAT THE WRITTEN ARGUMENT RAISES (CALL-06;
/// Lean aligned 2026-10-13). A parameter bound to a supplied cell is a VALUE demand of that cell
/// wherever it is read — a value position, a builtin value slot, and the ordinary-dot
/// <c>.string</c> intrinsic's receiver alike — so its first demand evaluates the written
/// argument once, and a failure is reported exactly as that argument reports it, never
/// re-judged by the zero-argument law against the parameter's callable. With
/// <c>Show(v) = v.string</c>: <c>Show(Inc)</c> keeps Inc's property frame,
/// <c>Show({ x + 1 })</c> is the block's <see cref="EvalError.UnresolvedImplicitParams"/>, and a
/// clause family's <see cref="EvalError.NoMatchingBranch"/> names the family — what
/// <c>Plus(f, x) = f + x</c> reports for the same argument. C# always read the cell first
/// (<c>EvalDotStringReceiverAlgOutput</c> and its async twin); Lean's <c>string</c> arm of
/// <c>evalDotCallCounted</c> applied the law to the PARAMETER first until 2026-10-13, which
/// dropped the property frame, turned the block's report into the parameter-shaped
/// <c>ArityMismatch(1, 0)</c> and named the family's branch failure after the parameter
/// (<c>hasSuppliedParameterCell</c> now reads the cell first).
///
/// <para>The cross-engine table (<see cref="Cases"/>) is pinned on both sides with the same
/// programs and the same expectations: <c>lean/CoreTests/ArgumentValueOutcome.lean</c> § 10
/// holds, for every case, the <see cref="LeanAstEncoder"/> encoding of the source's elaborated
/// AST and a guard on the same neutral tree, and
/// <see cref="LeanTable_HoldsTheSameProgramAndExpectation"/> checks that it does. The neutral
/// tree lists every frame, outermost first — a dot-call frame with its receiver — then the leaf
/// with its payload; it omits only two documented presentation differences
/// (<see cref="NeutralTree"/>).</para>
/// </summary>
public class DotStringParameterReceiverFrameTests
{
    private const string LeanTablePath = "lean/CoreTests/ArgumentValueOutcome.lean";

    private sealed record FrameCase(string Id, string Source, string Expected)
    {
        /// <summary>The Lean fixture's name: <c>dsr</c> plus the id in PascalCase.</summary>
        public string LeanName
            => "dsr" + string.Concat(Id.Split('-').Select(static word => char.ToUpperInvariant(word[0]) + word[1..]));
    }

    private static readonly FrameCase[] Cases =
    [
        new("parameterized-property",
            "Inc(z) = z + 1\nShow(v) = v.string\nShow(Inc)",
            "call Show > dotCall .string of v > property Inc > arityMismatch 1 0"),
        new("parameterized-property-value-read",
            "Inc(z) = z + 1\nPlus(f, x) = f + x\nPlus(Inc, 5)",
            "call Plus > property Inc > arityMismatch 1 0"),
        new("written-block",
            "Show(v) = v.string\nShow({ x + 1 })",
            "call Show > dotCall .string of v > unresolvedImplicitParams [x]"),
        new("written-block-value-read",
            "Plus(f, x) = f + x\nPlus({ y + 1 }, 5)",
            "call Plus > unresolvedImplicitParams [y]"),
        new("inline-alias",
            "Inc(z) = z + 1\nShow(v) = v.string\nShow({ Inc })",
            "call Show > dotCall .string of v > property Inc > arityMismatch 1 0"),
        new("clause-family",
            "F(0) = 1\nF(n) = n\nShow(v) = v.string\nShow(F)",
            "call Show > dotCall .string of v > noMatchingBranch F"),
        new("clause-family-value-read",
            "F(0) = 1\nF(n) = n\nPlus(f, x) = f + x\nPlus(F, 5)",
            "call Plus > noMatchingBranch F"),
        new("callable-alias",
            "Inc(z) = z + 1\nA = Inc\nShow(v) = v.string\nShow(A)",
            "call Show > dotCall .string of v > property A > arityMismatch 1 0"),
        new("family-alias",
            "F(0) = 1\nF(n) = n\nA = F\nShow(v) = v.string\nShow(A)",
            "call Show > dotCall .string of v > noMatchingBranch A"),
        new("member-path",
            "Lib = { public F(x) = x }\nShow(v) = v.string\nShow(Lib.F)",
            "call Show > dotCall .string of v > dotCall .F of Lib > arityMismatch 1 0"),
        new("member-alias",
            "Inc(z) = z + 1\nLib = { public A = Inc }\nShow(v) = v.string\nShow(Lib.A)",
            "call Show > dotCall .string of v > dotCall .A of Lib > arityMismatch 1 0"),
        new("forwarded-parameter",
            "Inc(z) = z + 1\nShow(v) = v.string\nShow2(w) = Show(w)\nShow2(Inc)",
            "call Show2 > call Show > dotCall .string of v > property Inc > arityMismatch 1 0"),
        new("minimum-supply",
            "Head(x, *rest) = x\nShow(v) = v.string\nShow(Head)",
            "call Show > dotCall .string of v > property Head > arityMismatch 1 0"),
        new("builtin",
            "Show(v) = v.string\nShow(count)",
            "call Show > dotCall .string of v > arityMismatch 1 0"),
        new("collecting-only-callable",
            "Only(*xs) = xs\nShow(v) = v.string\nShow(Only)",
            "call Show > dotCall .string of v > typeMismatch builtin property `string` expects a numeric receiver"),
        new("zero-parameter-property",
            "Z = 5\nShow(v) = v.string\nShow(Z)",
            "ok '5'"),
        new("failing-property",
            "Bad = 1 / 0\nShow(v) = v.string\nShow(Bad)",
            "call Show > dotCall .string of v > divByZero"),
        new("failing-argument",
            "Show(v) = v.string\nShow(1 / 0)",
            "call Show > dotCall .string of v > divByZero"),
        new("read-then-string",
            "Z = 5\nShow(v) = v + 0, v.string\nShow(Z)",
            "ok S[5, '5']"),
        new("loop-step",
            "Inc(z) = z + 1\nShow(v) = v.string\nStep(x) = Show(Inc)\nrepeat(Step(0), 1)",
            "call repeat > call Show > dotCall .string of v > property Inc > arityMismatch 1 0"),
        new("collecting-parameter",
            "Inc(z) = z + 1\nShow(*vs) = vs.string\nShow(Inc)",
            "call Show > dotCall .string of vs > property Inc > arityMismatch 1 0"),
        new("intrinsic-arguments",
            "Inc(z) = z + 1\nShow(v) = v.string(1)\nShow(Inc)",
            "call Show > dotCall .string of v > arityMismatch 0 1"),
    ];

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var frameCase in Cases)
            data.Add(frameCase.Id);
        return data;
    }

    private static FrameCase CaseById(string id) => Cases.Single(frameCase => frameCase.Id == id);

    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    [Theory]
    [MemberData(nameof(CaseIds))]
    public async Task EveryRoute_ReportsTheTableTree(string id)
    {
        var frameCase = CaseById(id);
        var ast = Program(frameCase.Source);

        var sync = Evaluator.Run(ast);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var passThrough = new PassThroughAsyncZeroArgPropertyResultCache();
        var (twin, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: passThrough));
        var suspending = new SuspendingAsyncZeroArgPropertyResultCache();
        var (suspended, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: suspending));

        Assert.Equal(frameCase.Expected, Observe(sync));
        Assert.Equal(frameCase.Expected, Observe(generic));
        Assert.Equal(frameCase.Expected, Observe(twin));
        Assert.Equal(frameCase.Expected, Observe(suspended));
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
        var frameCase = CaseById(id);
        var leanText = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanTablePath)).ReplaceLineEndings("\n");
        var encoded = LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(frameCase.Source).Root);
        var fixture =
            $"def {frameCase.LeanName} : Expr :=\n" +
            $"  {encoded}\n" +
            $"#guard dsrObserve {frameCase.LeanName} == {LeanAstEncoder.QuoteString(frameCase.Expected)}\n";

        Assert.True(
            leanText.Contains(fixture, StringComparison.Ordinal),
            $"{LeanTablePath} must hold the case '{id}' exactly as:\n{fixture}");
    }

    [Fact]
    public void LeanTable_HoldsNoCaseTheCSharpTableLacks()
    {
        var leanText = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanTablePath)).ReplaceLineEndings("\n");
        var leanNames = leanText.Split('\n')
            .Where(static line => line.StartsWith("#guard dsrObserve ", StringComparison.Ordinal))
            .Select(static line => line["#guard dsrObserve ".Length..].Split(' ')[0])
            .ToArray();

        Assert.Equal(Cases.Select(static frameCase => frameCase.LeanName), leanNames);
    }

    /// <summary>
    /// The arguments of the reads-agree law: every one fails its zero-argument VALUE demand,
    /// in each of the shapes that report differently (a parameterized property, a written
    /// block, an inline alias, a clause family, a callable alias of each, a member path and a
    /// member alias, a minimum supply, builtins, Math members, a failing property and a failing
    /// computation, an output-less block).
    /// </summary>
    public static TheoryData<string> FailingArguments()
    {
        var data = new TheoryData<string>();
        foreach (var argument in new[]
                 {
                     "Inc", "{ x + 1 }", "{ Inc }", "F", "A", "FA", "Lib.M", "Lib.MA", "Head",
                     "count", "if", "abs", "Math.Abs", "Bad", "1 / 0", "{ Member = 1 }",
                 })
            data.Add(argument);
        return data;
    }

    private const string Definitions =
        "Inc(z) = z + 1\n" +
        "F(0) = 1\n" +
        "F(n) = n\n" +
        "A = Inc\n" +
        "FA = F\n" +
        "Lib = { public M(x) = x\n" +
        "  public MA = Inc }\n" +
        "Head(x, *rest) = x\n" +
        "Bad = 1 / 0\n" +
        "Show(v) = v.string\n" +
        "Plus(v, x) = v + x\n";

    /// <summary>
    /// The law itself: below the receiver's own frames, <c>Show(K)</c> reports exactly the
    /// error the value-position read <c>Plus(K, 5)</c> reports — every context, payload and
    /// span (the argument stands at the same line and column in both programs, and both
    /// callees name the parameter <c>v</c>, which an output-less block's blame frame names).
    /// </summary>
    [Theory]
    [MemberData(nameof(FailingArguments))]
    public void StringReceiver_ReportsWhatTheValueReadReports(string argument)
    {
        var show = Evaluator.Run(Program(Definitions + $"Show({argument})"));
        var plus = Evaluator.Run(Program(Definitions + $"Plus({argument}, 5)"));

        Assert.True(show.IsError);
        Assert.True(plus.IsError);
        var showCall = Assert.IsType<EvalError.WithContext>(show.Error);
        Assert.Equal("while evaluating call to Show", showCall.ErrorContext.ToString());
        var receiver = Assert.IsType<EvalError.WithContext>(showCall.Inner);
        Assert.Equal(new DotCallContext("v", "string"), receiver.ErrorContext);
        var plusCall = Assert.IsType<EvalError.WithContext>(plus.Error);
        Assert.Equal("while evaluating call to Plus", plusCall.ErrorContext.ToString());

        Assert.Equal(DescribeErrorTree(plusCall.Inner), DescribeErrorTree(receiver.Inner));
    }

    /// <summary>
    /// The report is located at the WRITTEN ARGUMENT <c>Inc</c> of <c>Show(Inc)</c> (the cell
    /// keeps its source's span; inner spans win), on every frame from the call down to Inc's
    /// property frame — never at the receiver <c>v</c> inside <c>Show</c>.
    /// </summary>
    [Fact]
    public void ParameterizedPropertyReceiver_IsLocatedAtTheWrittenArgument()
    {
        var result = Evaluator.Run(Program("Inc(z) = z + 1\nShow(v) = v.string\nShow(Inc)"));
        var writtenArgument = new SourceSpan(3, 6, 3, 9);

        Assert.True(result.IsError);
        var frames = new List<EvalError.WithContext>();
        for (var error = result.Error; error is EvalError.WithContext context; error = context.Inner)
            frames.Add(context);
        Assert.Equal(
            ["while evaluating call to Show", "while evaluating dotCall .string of v", "while evaluating property Inc"],
            frames.Select(static frame => frame.ErrorContext.ToString()));
        Assert.All(frames, frame => Assert.Equal(writtenArgument, frame.Span));
    }

    [Theory]
    [InlineData("Inc(z) = z + 1\nShow(v) = v.string\nShow(Inc)", KatLangErrorCode.ArityMismatch)]
    [InlineData("Show(v) = v.string\nShow({ x + 1 })", KatLangErrorCode.UnresolvedImplicitParams)]
    [InlineData("F(0) = 1\nF(n) = n\nShow(v) = v.string\nShow(F)", KatLangErrorCode.NoMatchingBranch)]
    public void PublicEngine_ClassifiesTheWrittenArgumentsReport(string source, KatLangErrorCode expected)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));

        Assert.Equal(expected, Assert.Single(failure.Errors).Code);
    }

    private static string Observe(EvalResult<Result> result)
        => result.IsError ? NeutralTree(result.Error) : "ok " + NeutralValue(result.Value);

    private static string Observe(EvalResult<Evaluator.CountedResult> result)
        => result.IsError ? NeutralTree(result.Error) : "ok " + NeutralValue(result.Value.Value);

    /// <summary>
    /// The neutral tree shared with the Lean table: every frame outermost first — a dot-call
    /// frame with its receiver description — then the leaf with its payload. Omitted are exactly
    /// the two documented presentation differences: C#'s <see cref="ImplicitParameterContext"/>
    /// around <see cref="EvalError.UnresolvedImplicitParams"/> (no Lean counterpart), and — on the
    /// Lean side only — Lean's builtin-arity description frame, which C# keeps on the
    /// <see cref="EvalError.ArityMismatch"/> leaf. (Until 2026-10-13 the receiver description was
    /// omitted too, because Lean's <c>openExprName</c> wrote a parameter receiver <c>(param)</c>;
    /// both engines now write the parameter's name — <see cref="ParameterCalleeNameTests"/>.)
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
                    parts.Add($"dotCall .{dotCall.PropertyName} of {dotCall.ReceiverDescription}");
                    break;
                case PropertyEvaluationContext property:
                    parts.Add($"property {property.PropertyName}");
                    break;
                case ImplicitParameterContext:
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
            EvalError.UnresolvedImplicitParams unresolved => $"unresolvedImplicitParams [{string.Join(", ", unresolved.ParamNames)}]",
            EvalError.NoMatchingBranch branch => $"noMatchingBranch {branch.AlgorithmName}",
            EvalError.TypeMismatch type => $"typeMismatch {type.Message}",
            EvalError.NotAnAlgorithm notAnAlgorithm => $"notAnAlgorithm {notAnAlgorithm.Description}",
            EvalError.DivByZero => "divByZero",
            EvalError.BadArity => "badArity",
            _ => $"other {error.GetType().Name}",
        });
        return string.Join(" > ", parts);
    }

    /// <summary>The language-spec corpus's neutral spelling of a value.</summary>
    private static string NeutralValue(Result value) => SemanticExplorerHarness.Neutral(value);
}
