using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// DOT-09 / SYN-06 at a VALUE-ONLY runtime member (constitution audit C-1): redundant parentheses never
/// change a call. <c>(Box.A)(args)</c> is the member call <c>Box.A(args)</c> whatever the member's target,
/// so a member whose runtime row projects no identity answers through its value view on both spellings,
/// while grouping creates no callable identity for a scalar, a computed dot result or a supplied
/// reference. Lean: <c>resolveCalleeAlgWith</c>; the executable counterpart is the
/// <c>grouped-runtime-member-*</c> spec cases.
/// </summary>
public class GroupedRuntimeMemberCallTests
{
    private const string Inc = "Inc(x) = x + 1\n";

    private static string Use(string row, string argument = "5", string member = "public A = v")
        => $"{Inc}Use(v) = {{ Box = {{ {member}\n0 }}\n{row} }}\nUse({argument})";

    /// <summary>The public outcome: the displayed value, or the error kind alone (never its wording).</summary>
    private static string Outcome(RunResult result) => result switch
    {
        RunResult.Success success => "ok " + success.ToDisplayString(),
        RunResult.EvalFailure failure => "err " + string.Join(", ", failure.Errors.Select(static error => error.Code)),
        RunResult.ParseFailure failure => "front " + string.Join(", ", failure.Errors.Select(static error => error.Code)),
        _ => result.GetType().Name,
    };

    private static RunOptions Suspending(List<string>? effects = null) => new()
    {
        HostOperations = HostOperations.Create(
            HostOperation.CreateAsync("later", async (arguments, _) =>
            {
                await Task.Yield();
                effects?.Add("later");
                return arguments[0];
            }, "x")),
    };

    public static TheoryData<string, string, string> GroupedAndMemberSpellings => new()
    {
        { "(Box.A)()", "Box.A()", "ok 5" },
        { "((Box.A))()", "Box.A()", "ok 5" },
        { "(((Box.A)))()", "Box.A()", "ok 5" },
        { "(Box.A)(1)", "Box.A(1)", "err ArityMismatch" },
        { "((Box.A))(1, 2)", "Box.A(1, 2)", "err ArityMismatch" },
    };

    [Theory]
    [MemberData(nameof(GroupedAndMemberSpellings))]
    public void ValueOnlyMember_GroupedCallIsTheMemberCall(string grouped, string member, string expected)
    {
        Assert.Equal(expected, Outcome(KatLangEngine.Run(Use(member))));
        Assert.Equal(expected, Outcome(KatLangEngine.Run(Use(grouped))));
    }

    [Theory]
    [MemberData(nameof(GroupedAndMemberSpellings))]
    public async Task ValueOnlyMember_SuspendedRunAgrees(string grouped, string member, string expected)
    {
        _ = member;
        Assert.Equal(expected, Outcome(await KatLangEngine.RunAsync(Use(grouped, "later(5)"), Suspending())));
    }

    [Theory]
    [MemberData(nameof(GroupedAndMemberSpellings))]
    public void ValueOnlyMember_GenericAndOptimizedStrategiesAgree(string grouped, string member, string expected)
    {
        _ = expected;
        var ast = AsyncEvaluationHarness.Ast(Use(grouped));
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (optimized, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: true);
        var (written, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(Use(member)), enableOptimizations: false);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(optimized));
        Assert.Equal(generic.IsOk, written.IsOk);
        if (generic.IsOk)
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(written), AsyncEvaluationHarness.NeutralOf(generic));
        else
            Assert.Equal(written.Error.GetType(), generic.Error.GetType());
    }

    [Theory]
    [InlineData("(Box.A)(2)", "Inc", "public A = v", "ok 3")]
    [InlineData("((Box.A))(2)", "Inc", "public A = v", "ok 3")]
    [InlineData("(Box.A)()", "Inc", "public A = v", "err ArityMismatch")]
    [InlineData("(Box.B)()", "5", "public A = v\npublic B = A", "ok 5")]
    [InlineData("(Box.B)(2)", "Inc", "public A = v\npublic B = A", "ok 3")]
    [InlineData("(Box.A)()", "5", "public A = { v }", "ok 5")]
    [InlineData("(Box.A)()", "1 / 0", "public A = v", "err DivisionByZero")]
    [InlineData("(C.A)()", "5", "public A = v", "ok 5")]
    [InlineData("(Box.A)()", "5", "A = v", "ok 5")]
    public void NearbyMemberShapes_KeepTheirMemberCallOutcome(string row, string argument, string member, string expected)
    {
        var withAlias = row.StartsWith("(C.", StringComparison.Ordinal) ? "C = Box\n" + row : row;
        var ungrouped = withAlias.Replace("((Box.A))", "Box.A").Replace("(Box.A)", "Box.A").Replace("(Box.B)", "Box.B").Replace("(C.A)", "C.A");
        Assert.Equal(expected, Outcome(KatLangEngine.Run(Use(withAlias, argument, member))));
        Assert.Equal(expected, Outcome(KatLangEngine.Run(Use(ungrouped, argument, member))));
    }

    [Fact]
    public void ValueOnlyMember_EveryCallReadsTheOneSuppliedValue()
    {
        var effects = new List<string>();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("trace", (arguments, _) =>
            {
                effects.Add("trace");
                return arguments[0];
            }, "x")),
        };
        var result = KatLangEngine.Run(Use("(Box.A)() + ((Box.A))() + Box.A() + Box.A", "trace(5)"), options);
        Assert.Equal("ok 20", Outcome(result));
        Assert.Equal(["trace"], effects);
    }

    [Fact]
    public async Task ValueOnlyMember_SuspendedRunDemandsTheSuppliedValueOnce()
    {
        var effects = new List<string>();
        var result = await KatLangEngine.RunAsync(Use("(Box.A)() + (Box.A)()", "later(5)"), Suspending(effects));
        Assert.Equal("ok 10", Outcome(result));
        Assert.Equal(["later"], effects);
    }

    [Fact]
    public void GroupedCall_IsAWrittenInvocationForMetaCapture()
        => Assert.Equal("ok 5", Outcome(KatLangEngine.Run(
            Use("Cap((Box.A)())").Replace("Inc(x)", "Cap(meta r) = r.Invoke()\nInc(x)"))));

    [Theory]
    [InlineData("Inc(x) = x + 1\n(5.Inc)()", "err NotAnAlgorithm")]
    [InlineData("Inc(x) = x + 1\n(5.Inc)(1)", "err NotAnAlgorithm")]
    [InlineData("Box = { public A = 5 }\n(Box.A)()", "ok 5")]
    [InlineData("Box = { public A = 5 }\n(Box.A)(1)", "err ArityMismatch")]
    public void GroupingCreatesNoCallableForAComputedValue(string source, string expected)
        => Assert.Equal(expected, Outcome(KatLangEngine.Run(source)));

    [Theory]
    [InlineData("Call(Box.A)")]
    [InlineData("Call((Box.A))")]
    public void AValueOnlyMemberPassedOnStaysNoCallable(string row)
        => Assert.Equal("err NotAnAlgorithm", Outcome(KatLangEngine.Run(
            Use(row).Replace("Inc(x) = x + 1", "Call(f) = f()"))));

    [Fact]
    public void ABraceCarrierKeepsItsOwnIdentity()
    {
        // `{ Box.A }` is a distinct carrier, not a transparent reference: the member's value view stays
        // inside the carrier's forwarding, so the carrier's non-empty supply is the same arity rejection,
        // and a declared carrier member is no target member.
        Assert.Equal("ok 5", Outcome(KatLangEngine.Run(Use("C = { Box.A }\nC()"))));
        Assert.Equal("err ArityMismatch", Outcome(KatLangEngine.Run(Use("C = { Box.A }\nC(1)"))));
    }
}
