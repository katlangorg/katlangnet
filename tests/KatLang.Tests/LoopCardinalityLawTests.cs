using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// THE LOOP CARDINALITY LAW (Q-24 + Q-26, decided October 2026): <b>patterns bind, rows produce,
/// <c>*</c> opens</b> — and none of the three changes the others.
/// <list type="bullet">
/// <item><b>Q-24.</b> A step's parameter patterns inspect and bind the INCOMING state only. After the
/// step runs, its emitted row supply is the next state: each non-spread row supplies one item, each
/// spread row its spread items. No pattern category (plain, repeated names, collectors, structural
/// sequence or list patterns, nested patterns) repacks that supply — the former LOOP-04 packing of a
/// pattern-bound step's top-level spread row is retired — so <c>Dup(x, x) = { x + 1, x + 1 }</c>
/// and <c>Dup(x, x) = { (x + 1, x + 1)* }</c> form the same two-slot state.</item>
/// <item><b>Q-26.</b> A completed <c>while</c>/<c>repeat</c> is an ordinary value boundary: ONE value,
/// the canonical capture of its final slots (<c>()</c>, the slot itself, or a sequence), with emitted
/// count <c>valueCount</c> like every builtin and call result. A non-spread loop expression is one
/// item at every receiver — the root, a body, a capture, a loop step, a callback body — and
/// <c>L*</c> explicitly opens it.</item>
/// </list>
/// The step's rows remain the loop's own protocol for the next state (<c>Fib(a, b) = b, a + b</c>
/// still produces two slots); Q-26 concerns only the completed loop handed to its consumer, and
/// <c>while</c> still reads its continuation flag from the last item of the row supply (LOOP-06).
/// Every program here runs on the six established routes — both engines, the engine's suspending
/// twin, the generic and the optimized evaluator, and the forced async twin — which must agree on
/// value, root emitted count, display rows, every error and the host-call log.
/// Lean: <c>CoreTests/LoopCardinality.lean</c>, laws <c>loop_result_*</c> in
/// <c>KatLangArityLaws.lean</c>.
/// </summary>
public class LoopCardinalityLawTests
{
    // ── Q-24: patterns bind, rows produce ──────────────────────────────────────

    [Theory]
    [InlineData("Dup(x, x) = { x + 1, x + 1 }")]
    [InlineData("Dup(x, x) = { (x + 1, x + 1)* }")]
    public async Task RepeatedNameStep_RowsAndTheirSpread_FormTheSameTwoSlotState(string step)
    {
        // Both forms supply two next-state slots, which Dup(x, x) re-binds on the second iteration.
        AssertOk(await OnEveryRouteAsync(step + "\nDup.repeat(2, 1, 1)"), "S[3, 3]", 1, "S[3, 3]");
        AssertOk(await OnEveryRouteAsync(step + "\nrepeat(Dup, 2, 1, 1)"), "S[3, 3]", 1, "S[3, 3]");
        AssertOk(await OnEveryRouteAsync(step + "\nDup.repeat(2, 1, 1)*"), "S[3, 3]", 2, "3", "3");
    }

    [Theory]
    [InlineData("Dup(x, x) = { x + 1, x + 2 }")]
    [InlineData("Dup(x, x) = { (x + 1, x + 2)* }")]
    public async Task RepeatedNameStep_DivergingRows_FailTheNextBindingWithTheOrdinaryRepeatedNameError(string step)
    {
        AssertOk(await OnEveryRouteAsync(step + "\nDup.repeat(1, 1, 1)"), "S[2, 3]", 1, "S[2, 3]");

        // The NEXT binding of Dup(x, x) compares 2 with 3: the ordinary repeated-name failure of
        // the one inspecting binder (NEED-04) — never the former packing-derived loop-state
        // cardinality failure ("expects 2 state values ... has 1 state value").
        var loop = await OnEveryRouteAsync(step + "\nDup.repeat(2, 1, 1)");
        var loopError = Assert.Single(loop.Errors);
        Assert.Equal("err", loop.Kind);
        Assert.StartsWith("ArityMismatch: ", loopError, StringComparison.Ordinal);
        Assert.DoesNotContain("state value", loopError, StringComparison.Ordinal);
        Assert.IsType<EvalError.BadArity>(Innermost(GenericError(step + "\nDup.repeat(2, 1, 1)")));

        // ... exactly the direct call's own failure on the same values.
        var call = await OnEveryRouteAsync(step + "\nDup(2, 3)");
        Assert.Equal("err", call.Kind);
        Assert.IsType<EvalError.BadArity>(Innermost(GenericError(step + "\nDup(2, 3)")));
    }

    [Fact]
    public async Task StructuralStep_CaptureRowIsOneSlot_SpreadRowSuppliesItsItems()
    {
        // One sequence value is ONE slot, re-bound by (a, b) every iteration.
        AssertOk(await OnEveryRouteAsync("Step((a, b)) = (b, a + b)\nStep.repeat(3, (0, 1))"), "S[2, 3]", 1, "S[2, 3]");

        // Its spread supplies TWO items — the ordinary spread, whatever the head — so one
        // iteration completes ...
        AssertOk(await OnEveryRouteAsync("Step2((a, b)) = { (b, a + b)* }\nStep2.repeat(1, (0, 1))"), "S[1, 1]", 1, "S[1, 1]");

        // ... and the one-pattern head cannot bind the two-slot state of the next iteration.
        AssertLoopStateArity(
            await OnEveryRouteAsync("Step2((a, b)) = { (b, a + b)* }\nStep2.repeat(3, (0, 1))"),
            "`repeat` step expects 1 state value for 1 parameter '(a, b)', but the current loop state has 2 state values.");
    }

    [Fact]
    public async Task HistorySteps_KeepStructureOnlyThroughAnExplicitCaptureOrList()
    {
        // The explicit capture keeps the history as ONE state slot ...
        AssertOk(await OnEveryRouteAsync("P((*h), n) = (h*), n + 1\nP.repeat(2, (1, 2), 0)"), "S[S[1, 2], 2]", 1, "S[S[1, 2], 2]");
        // ... as does the exact list, at every history length, the empty one included.
        AssertOk(await OnEveryRouteAsync("Grow([*h], n) = [h*, n], n + 1\nGrow.repeat(3, [], 0):0"), "L[0, 1, 2]", 1, "L[0, 1, 2]");
        AssertOk(await OnEveryRouteAsync("Grow([*h], n) = [h*, n], n + 1\nGrow.repeat(0, [], 0):0"), "L[]", 1, "L[]");

        // Without it, the spread row supplies the history's items as separate slots (no implicit
        // packing): one iteration equals the direct call, and the second binding sees three slots.
        AssertOk(await OnEveryRouteAsync("P((*h), n) = h*, n + 1\nrepeat(P, 1, (1, 2), 0), P((1, 2), 0)"),
            "S[S[1, 2, 1], S[1, 2, 1]]", 2, "S[1, 2, 1]", "S[1, 2, 1]");
        AssertLoopStateArity(
            await OnEveryRouteAsync("P((*h), n) = h*, n + 1\nP.repeat(2, (1, 2), 0)"),
            "`repeat` step expects 2 state values for 2 parameters '(*h)' and 'n', but the current loop state has 3 state values.");
    }

    [Fact]
    public async Task YellowstoneHistory_TheExplicitCaptureIdiom_Iterates()
    {
        // The canonical program behind the retired packing (#99, `EvaluatorLoopTests`'
        // Yellowstone case) keeps its history through the explicit capture `(history*, Next)`, so
        // it never depended on packing; its patterned head only BINDS the history slot.
        const string source = """
            GcdStep = b, ~a mod b, a mod b != 0
            Gcd = GcdStep.while(a, b):1

            FindNext(*history, pre1, pre2) = {
                IsYSCandidate(candidate) = not history.contains(candidate) and
                    Gcd(candidate, pre1) == 1 and
                    Gcd(candidate, pre2) != 1

                FindStep = candidate + 1, not IsYSCandidate(candidate)
                FindStep.while(1):0
            }

            YSStep((*history), pre2, pre1) = {
                Next = FindNext(history*, pre1, pre2)
                (history*, Next), pre1, Next
            }

            YSStep.repeat(7, (1, 2, 3), 2, 3):0
            """;
        AssertOk(await OnEveryRouteAsync(source),
            "S[1, 2, 3, 4, 9, 8, 15, 14, 5, 6]", 1, "S[1, 2, 3, 4, 9, 8, 15, 14, 5, 6]");
    }

    [Theory]
    [InlineData("()*", "0", "a step's zero-item spread row supplies no slot")]
    [InlineData("()", "S[S[], 0]", "a step's () row is one visible slot")]
    [InlineData("(()*)", "S[S[], 0]", "a captured zero-item spread is one () slot")]
    [InlineData("[]*", "0", "a step's empty-list spread row supplies no slot")]
    [InlineData("[]", "S[L[], 0]", "a step's [] row is one visible slot")]
    public async Task EmptyRows_KeepTheirMeaningUnderEveryHead(string row, string expected, string why)
    {
        foreach (var head in Heads)
        {
            var source = head.Definitions(row) + $"\nrepeat(S, 1, {head.Init}), S({head.Init})";
            var observation = await OnEveryRouteAsync(source);
            Assert.True(observation.Kind == "ok", $"{head.Name}: {why}: {observation}");
            Assert.Equal($"S[{expected}, {expected}]", observation.Value);
        }
    }

    /// <summary>
    /// One step-head category: its definition of <c>S</c> (and any helper it needs) with the given
    /// output rows, and the initial state binding a = 1, b = 2 through that head.
    /// </summary>
    public sealed record StepHead(string Name, Func<string, string> Definitions, string Init);

    private static string Body(string rows, string locals = "")
        => locals.Length == 0 ? $"{{ {rows}, 0 }}" : $"{{\n  {locals}\n  {rows}, 0\n}}";

    /// <summary>
    /// Every step-head category the retired packing distinguished, plus the alias and the η-wrapper
    /// of a structural step. Each binds a = 1, b = 2 and adds the sentinel row <c>0</c>, so the
    /// captured final value reveals the exact next-state slot list.
    /// </summary>
    public static readonly IReadOnlyList<StepHead> Heads =
    [
        new("flat", rows => $"S(a, b) = {Body(rows)}", "1, 2"),
        new("repeated names", rows => $"S(a, a, b) = {Body(rows)}", "1, 1, 2"),
        new("collector", rows => $"S(a, *rest) = {Body(rows, "b = rest:0")}", "1, 2"),
        new("collector only", rows => $"S(*xs) = {Body(rows, "a = xs:0\n  b = xs:1")}", "1, 2"),
        new("sequence pattern", rows => $"S((a, b)) = {Body(rows)}", "(1, 2)"),
        new("list pattern", rows => $"S([a, b]) = {Body(rows)}", "[1, 2]"),
        new("nested pattern", rows => $"S(((a, b), c)) = {Body(rows)}", "((1, 2), 3)"),
        new("sequence pattern with collector", rows => $"S((a, *rest)) = {Body(rows, "b = rest:0")}", "(1, 2)"),
        new("list pattern with collector", rows => $"S([a, *rest]) = {Body(rows, "b = rest:0")}", "[1, 2]"),
        new("repeated structural leaf", rows => $"S((a, b), (a, c)) = {Body(rows)}", "(1, 2), (1, 3)"),
        new("alias of a structural step", rows => $"P((a, b)) = {Body(rows)}\nS = P", "(1, 2)"),
        new("wrapper of a structural step", rows => $"P((a, b)) = {Body(rows)}\nS(p) = {{ P(p)* }}", "(1, 2)"),
    ];

    /// <summary>
    /// Output forms over a = 1, b = 2 and the value their row supply plus the sentinel captures —
    /// the SAME for every head. Under the retired packing, every top-level spread row of two or
    /// more items became one packed slot under the pattern-bound heads only.
    /// </summary>
    public static readonly IReadOnlyList<(string Rows, string Expected)> Forms =
    [
        ("a, b", "S[1, 2, 0]"),
        ("(a, b)", "S[S[1, 2], 0]"),
        ("(a, b)*", "S[1, 2, 0]"),
        ("[a, b]", "S[L[1, 2], 0]"),
        ("[a, b]*", "S[1, 2, 0]"),
        ("()", "S[S[], 0]"),
        ("()*", "0"),
        ("(()*)", "S[S[], 0]"),
        ("[]", "S[L[], 0]"),
        ("[]*", "0"),
        ("(a, (a, b))*", "S[1, S[1, 2], 0]"),
        ("[(a, b)]*", "S[S[1, 2], 0]"),
        ("(a, b, ())*", "S[1, 2, S[], 0]"),
        ("Id((a, b))", "S[S[1, 2], 0]"),
        ("Id((a, b))*", "S[1, 2, 0]"),
        ("Only(a, b)", "S[L[1, 2], 0]"),
        ("Only(a, b)*", "S[1, 2, 0]"),
        ("if(a < b, (a, b), ())*", "S[1, 2, 0]"),
        ("repeat(Fib, 1, a, b)", "S[S[2, 3], 0]"),
        ("repeat(Fib, 1, a, b)*", "S[2, 3, 0]"),
        ("[a, b]:1", "S[2, 0]"),
        ("a, (b, a)*", "S[1, 2, 1, 0]"),
        ("[a, b], (a, b)*", "S[L[1, 2], 1, 2, 0]"),
        ("(a, b)**", "S[1, 2, 0]"),
    ];

    public static TheoryData<string, string> HeadsByForms()
    {
        var data = new TheoryData<string, string>();
        foreach (var head in Heads)
            foreach (var (rows, _) in Forms)
                data.Add(head.Name, rows);
        return data;
    }

    private const string Helpers = "Id(x) = x\nOnly(*xs) = xs\nFib(x, y) = y, x + y\n";

    /// <summary>
    /// For equal emitted rows, the next state does not depend on the step's parameter-pattern
    /// category: one iteration captures exactly the row supply the form defines under every head,
    /// and equals the direct call <c>S(init)</c> in value and emitted count.
    /// </summary>
    [Theory]
    [MemberData(nameof(HeadsByForms))]
    public async Task NextState_DoesNotDependOnTheStepsParameterPatterns(string headName, string rows)
    {
        var head = Heads.Single(candidate => candidate.Name == headName);
        var expected = Forms.Single(form => form.Rows == rows).Expected;
        var definitions = Helpers + head.Definitions(rows);

        var both = await OnEveryRouteAsync(definitions + $"\nrepeat(S, 1, {head.Init}), S({head.Init})");
        AssertOk(both, $"S[{expected}, {expected}]", 2, expected, expected);

        var loop = await OnEveryRouteAsync(definitions + $"\nrepeat(S, 1, {head.Init})");
        var call = await OnEveryRouteAsync(definitions + $"\nS({head.Init})");
        Assert.Equal(call.Value, loop.Value);
        Assert.Equal(call.Emitted, loop.Emitted);
    }

    // ── Q-26: a completed loop is one value ──────────────────────────────────

    private const string Fibonacci = "Fibonacci(a, b) = b, a + b\n";

    [Fact]
    public async Task Fibonacci_LoopIsOneValue_SpreadOpensIt_BesideAnotherRowItIsOneRow()
    {
        AssertOk(await OnEveryRouteAsync(Fibonacci + "Fibonacci.repeat(10, 0, 1)"), "S[55, 89]", 1, "S[55, 89]");
        AssertOk(await OnEveryRouteAsync(Fibonacci + "Fibonacci.repeat(10, 0, 1)*"), "S[55, 89]", 2, "55", "89");
        AssertOk(await OnEveryRouteAsync(Fibonacci + "Fibonacci.repeat(10, 0, 1), 7"), "S[S[55, 89], 7]", 2, "S[55, 89]", "7");

        Assert.Equal("(55, 89)", Display(Fibonacci + "Fibonacci.repeat(10, 0, 1)"));
        Assert.Equal("55\n89", Display(Fibonacci + "Fibonacci.repeat(10, 0, 1)*"));
        Assert.Equal("(55, 89)\n7", Display(Fibonacci + "Fibonacci.repeat(10, 0, 1), 7"));
    }

    /// <summary>
    /// For a successful source program, a non-spread loop row contributes exactly ONE emitted row,
    /// like every other non-spread expression, so the root's emitted count equals its display rows.
    /// </summary>
    [Theory]
    [InlineData("Fibonacci.repeat(10, 0, 1)", 1)]
    [InlineData("Fibonacci.repeat(10, 0, 1), 7", 2)]
    [InlineData("7, Fibonacci.repeat(10, 0, 1), Fibonacci.repeat(1, 0, 1)", 3)]
    [InlineData("Fibonacci.repeat(10, 0, 1)*, 7", 3)]
    [InlineData("while({a + 1, b + a, a < 2}, 0, 0)", 1)]
    [InlineData("while({a + 1, b + a, a < 2}, 0, 0), ()", 2)]
    [InlineData("repeat(Drop, 1, 5)", 1)]
    [InlineData("repeat(Drop, 1, 5)*", 0)]
    [InlineData("repeat(Drop, 1, 5), repeat(Drop, 1, 5)*, 9", 2)]
    [InlineData("repeat({x + 1}, 3, 0)", 1)]
    [InlineData("{ Fibonacci.repeat(10, 0, 1), 7 }", 1)]
    [InlineData("(Fibonacci.repeat(10, 0, 1), 7)", 1)]
    [InlineData("[Fibonacci.repeat(10, 0, 1), 7]", 1)]
    public async Task RootRows_EmittedCountEqualsDisplayRows(string rows, int expected)
    {
        var observation = await OnEveryRouteAsync(Fibonacci + "Drop(*xs) = { ()* }\n" + rows);
        Assert.Equal("ok", observation.Kind);
        Assert.Equal(expected, observation.Emitted);
        Assert.Equal(expected, observation.Rows.Count);
    }

    [Fact]
    public async Task LoopRowInBodiesCapturesAndLists_IsOneItem()
    {
        // A body, a capture and a list receive the loop as ONE item — the same structure.
        var body = await OnEveryRouteAsync(Fibonacci + "{ Fibonacci.repeat(10, 0, 1), 7 }");
        var capture = await OnEveryRouteAsync(Fibonacci + "(Fibonacci.repeat(10, 0, 1), 7)");
        var list = await OnEveryRouteAsync(Fibonacci + "[Fibonacci.repeat(10, 0, 1), 7]");
        Assert.Equal("S[S[55, 89], 7]", body.Value);
        Assert.Equal(body.Value, capture.Value);
        Assert.Equal("L[S[55, 89], 7]", list.Value);
        AssertOk(await OnEveryRouteAsync(Fibonacci + "{ Fibonacci.repeat(10, 0, 1), 7 }.count"), "2", 1, "2");
        AssertOk(await OnEveryRouteAsync(Fibonacci + "(Fibonacci.repeat(10, 0, 1)*, 7).count"), "3", 1, "3");
    }

    [Fact]
    public async Task NestedLoopStepRow_IsOneSlot_UnlessSpread()
    {
        // Two(a, b) = repeat(...) is ONE next-state slot (formerly SUP-01's exception spliced two),
        // so the two-parameter head cannot bind it on the next iteration ...
        AssertLoopStateArity(
            await OnEveryRouteAsync(Fibonacci + "Two(a, b) = repeat(Fibonacci, 2, a, b)\nTwo.repeat(3, 0, 1)"),
            "`repeat` step expects 2 state values for 2 parameters 'a' and 'b', but the current loop state has 1 state value.");

        // ... while the explicit spread supplies the inner loop's final items as the next state.
        AssertOk(await OnEveryRouteAsync(Fibonacci + "Two(a, b) = { repeat(Fibonacci, 2, a, b)* }\nTwo.repeat(3, 0, 1)"),
            "S[8, 13]", 1, "S[8, 13]");

        // A one-slot step consumes the nested loop's ONE value whole.
        AssertOk(await OnEveryRouteAsync(Fibonacci + "One((a, b)) = repeat(Fibonacci, 1, a, b)\nOne.repeat(3, (0, 1))"),
            "S[2, 3]", 1, "S[2, 3]");
    }

    [Fact]
    public async Task WrappedLoop_HasTheCardinalityOfTheDirectLoop()
    {
        // η-parity: a helper returning the loop and the loop itself are the same one value —
        // both non-spread forms are one slot, both spread forms supply the items.
        const string inner = "Inner(a, b) = repeat(Fibonacci, 2, a, b)\n";
        var direct = await OnEveryRouteAsync(Fibonacci + "Two(a, b) = repeat(Fibonacci, 2, a, b)\nTwo.repeat(3, 0, 1)");
        var wrapped = await OnEveryRouteAsync(Fibonacci + inner + "Two(a, b) = Inner(a, b)\nTwo.repeat(3, 0, 1)");
        Assert.Equal(MessagesOnly(direct), MessagesOnly(wrapped));

        var directSpread = await OnEveryRouteAsync(Fibonacci + "Two(a, b) = { repeat(Fibonacci, 2, a, b)* }\nTwo.repeat(3, 0, 1)");
        var wrappedSpread = await OnEveryRouteAsync(Fibonacci + inner + "Two(a, b) = { Inner(a, b)* }\nTwo.repeat(3, 0, 1)");
        AssertOk(directSpread, "S[8, 13]", 1, "S[8, 13]");
        Assert.Equal(directSpread with { HostCalls = [] }, wrappedSpread with { HostCalls = [] });

        // At the root and beside other rows, the helper and the loop agree in value and count.
        foreach (var rows in new[] { "{0}", "{0}, 7", "{0}*", "({0}, 7)" })
        {
            var loop = await OnEveryRouteAsync(Fibonacci + inner + string.Format(rows, "repeat(Fibonacci, 2, 0, 1)"));
            var helper = await OnEveryRouteAsync(Fibonacci + inner + string.Format(rows, "Inner(0, 1)"));
            Assert.Equal(loop, helper);
        }
    }

    [Fact]
    public async Task CallbackBodyLoop_IsOneValue_LikeAHelper()
    {
        const string defs = "Fib(x, y) = y, x + y\nH(x) = repeat(Fib, 2, x, 1)\n";
        // A callback whose body row is a multi-slot loop returns ONE value, exactly like a helper
        // returning it (formerly the loop's slot count leaked into the single-element contract).
        foreach (var call in new[] { "[0, 1].map(H)", "[0, 1].map({ repeat(Fib, 2, x, 1) })", "map([0, 1], { H(x) })" })
            AssertOk(await OnEveryRouteAsync(defs + call), "L[S[1, 2], S[2, 3]]", 1, "L[S[1, 2], S[2, 3]]");

        // The reducer step likewise receives and returns one value.
        const string reducer = "Step(x, acc) = acc:0 + x, acc:1 + 1\nR(x, acc) = repeat(Step, 1, x, acc)\n";
        foreach (var call in new[] { "[1, 2, 3].reduce(R, (0, 0))", "[1, 2, 3].reduce({ repeat(Step, 1, x, acc) }, (0, 0))" })
            AssertOk(await OnEveryRouteAsync(reducer + call), "S[6, 3]", 1, "S[6, 3]");

        // The single-element contract itself is unchanged: an explicit spread is still several outputs.
        var spread = await OnEveryRouteAsync(defs + "[0, 1].map({ repeat(Fib, 2, x, 1)* })");
        Assert.Equal("err", spread.Kind);
        Assert.Equal(
            MessagesOnly(await OnEveryRouteAsync("D(x) = x, x\n[0, 1].map({ D(x)* })")),
            MessagesOnly(spread));
    }

    [Fact]
    public async Task ZeroOneAndManySlotLoops_FollowValueCount()
    {
        // zero final slots: the result is () — a visible root row, and its spread supplies nothing
        const string drop = "Drop(*xs) = { ()* }\n";
        AssertOk(await OnEveryRouteAsync(drop + "repeat(Drop, 1, 1)"), "S[]", 1, "S[]");
        AssertOk(await OnEveryRouteAsync(drop + "repeat(Drop, 1, 1)*, 9"), "9", 1, "9");
        AssertOk(await OnEveryRouteAsync(drop + "(repeat(Drop, 1, 1), 9)"), "S[S[], 9]", 1, "S[S[], 9]");
        AssertOk(await OnEveryRouteAsync(drop + "Coll(*xs) = xs\nColl(repeat(Drop, 1, 1)), Coll(repeat(Drop, 1, 1)*)"),
            "S[L[S[]], L[]]", 2, "L[S[]]", "L[]");
        // ... and a zero-slot state is re-bound by a step that accepts an empty supply (a collector).
        AssertOk(await OnEveryRouteAsync(drop + "repeat(Drop, 3, 1)"), "S[]", 1, "S[]");

        // one final slot: unchanged
        AssertOk(await OnEveryRouteAsync("Inc(x) = x + 1\nrepeat(Inc, 3, 0)"), "3", 1, "3");
        AssertOk(await OnEveryRouteAsync("Inc(x) = x + 1\nrepeat(Inc, 3, 0)*"), "3", 1, "3");

        // several final slots: one value, opened only by the spread
        AssertOk(await OnEveryRouteAsync("G(*h) = h*, h.count\nrepeat(G, 3, 0)"), "S[0, 1, 2, 3]", 1, "S[0, 1, 2, 3]");
        AssertOk(await OnEveryRouteAsync("G(*h) = h*, h.count\nrepeat(G, 3, 0)*"), "S[0, 1, 2, 3]", 4, "0", "1", "2", "3");
    }

    [Fact]
    public async Task OneSlotPairAndTwoSlotState_CompleteToTheSameValue()
    {
        const string defs = "P1(p) = (p:0 + 10, p:1 + 10)\nP2(a, b) = a + 10, b + 10\n";
        var onePair = await OnEveryRouteAsync(defs + "repeat(P1, 1, (10, 20))");
        var twoSlots = await OnEveryRouteAsync(defs + "repeat(P2, 1, 10, 20)");
        AssertOk(onePair, "S[20, 30]", 1, "S[20, 30]");
        Assert.Equal(onePair, twoSlots);
        AssertOk(await OnEveryRouteAsync(defs + "repeat(P1, 1, (10, 20)) == repeat(P2, 1, 10, 20)"), "true", 1, "true");

        // The slot difference stays inside the loop: each state re-binds only its own head.
        AssertOk(await OnEveryRouteAsync(defs + "repeat(P1, 2, (10, 20)), repeat(P2, 2, 10, 20)"),
            "S[S[30, 40], S[30, 40]]", 2, "S[30, 40]", "S[30, 40]");
    }

    [Fact]
    public async Task StepRowsStillFormTheNextState_TheLoopProtocolIsUnchanged()
    {
        // Q-26 never collapses a step's rows into its call value: two rows are two slots ...
        AssertOk(await OnEveryRouteAsync("Fib(a, b) = b, a + b\nrepeat(Fib, 3, 0, 1)"), "S[2, 3]", 1, "S[2, 3]");
        // ... while one parenthesized row is ONE slot holding a sequence.
        AssertOk(await OnEveryRouteAsync("G(p) = (p:1, p:0 + p:1)\nrepeat(G, 3, (0, 1))"), "S[2, 3]", 1, "S[2, 3]");
        AssertLoopStateArity(
            await OnEveryRouteAsync("G(a, b) = (b, a + b)\nrepeat(G, 2, 0, 1)"),
            "`repeat` step expects 2 state values for 2 parameters 'a' and 'b', but the current loop state has 1 state value.");
    }

    [Fact]
    public async Task WhileFlag_IsStillTheLastItemOfTheStepsRowSupply()
    {
        // The flag position, the Boolean requirement and the state/flag split are unchanged.
        AssertOk(await OnEveryRouteAsync("Cd(n, acc) = n - 1, acc + n, n > 1\nwhile(Cd, 3, 0)"), "S[1, 5]", 1, "S[1, 5]");
        AssertOk(await OnEveryRouteAsync("Cd(n, acc) = { (n - 1, acc + n, n > 1)* }\nwhile(Cd, 3, 0)"), "S[1, 5]", 1, "S[1, 5]");
        var pairFlag = await OnEveryRouteAsync("S(x) = (x + 1, x < 3)\nwhile(S, 0)");
        Assert.Equal("err", pairFlag.Kind);
        Assert.StartsWith("TypeMismatch: ", Assert.Single(pairFlag.Errors), StringComparison.Ordinal);

        // A nested loop row is one item of the row supply: its final state — including a would-be
        // flag — arrives as ONE value, so as a lone row it is the flag itself and must be a Boolean;
        // the explicit spread supplies its items, the last of which is the flag.
        const string body = "Body(a) = a + 1, a < 3\n";
        var oneValue = await OnEveryRouteAsync(body + "W(a) = repeat(Body, 1, a)\nwhile(W, 0)");
        Assert.Equal("err", oneValue.Kind);
        Assert.StartsWith("TypeMismatch: ", Assert.Single(oneValue.Errors), StringComparison.Ordinal);
        AssertOk(await OnEveryRouteAsync(body + "W(a) = { repeat(Body, 1, a)* }\nwhile(W, 0)"), "3", 1, "3");
    }

    // ── The combined law: binding, production and opening are independent ───────

    /// <summary>
    /// Patterns bind, rows produce, <c>*</c> opens — varying ONE concern while the other two stay
    /// fixed changes only what that concern decides. BINDING (the head) decides which incoming
    /// states the step accepts, never what it produces; PRODUCTION (the rows) decides the next
    /// state's slots; OPENING (an explicit spread) decides where one value boundary opens — inside
    /// the step for the next state, at the consumer for the completed loop.
    /// </summary>
    [Fact]
    public async Task BindingProductionAndOpening_VaryOneConcernAtATime()
    {
        // BINDING varies; rows `b, a + b` (two slots) stay. Every head produces the same next
        // state, so one iteration completes to the same value under each ...
        var heads = new[] { ("S(a, b)", "0, 1"), ("S((a, b))", "(0, 1)"), ("S(a, b, b)", "0, 1, 1") };
        foreach (var (head, init) in heads)
            AssertOk(await OnEveryRouteAsync($"{head} = b, a + b\nrepeat(S, 1, {init})"), "S[1, 1]", 1, "S[1, 1]");

        // ... and only the next BINDING tells the heads apart: the flat head accepts the two slots,
        // the structural and the repeated-name heads reject them.
        AssertOk(await OnEveryRouteAsync("S(a, b) = b, a + b\nrepeat(S, 2, 0, 1)"), "S[1, 2]", 1, "S[1, 2]");
        AssertLoopStateArity(await OnEveryRouteAsync("S((a, b)) = b, a + b\nrepeat(S, 2, (0, 1))"),
            "but the current loop state has 2 state values.");
        AssertLoopStateArity(await OnEveryRouteAsync("S(a, b, b) = b, a + b\nrepeat(S, 2, 0, 1, 1)"),
            "but the current loop state has 2 state values.");

        // PRODUCTION varies; the flat head and the absence of a spread stay: the rows alone decide
        // the slots — two rows two, one sequence row one, three rows three.
        AssertOk(await OnEveryRouteAsync("S(a, b) = (b, a + b)\nrepeat(S, 1, 0, 1)"), "S[1, 1]", 1, "S[1, 1]");
        AssertLoopStateArity(await OnEveryRouteAsync("S(a, b) = (b, a + b)\nrepeat(S, 2, 0, 1)"),
            "but the current loop state has 1 state value.");
        AssertOk(await OnEveryRouteAsync("S(a, b) = b, a + b, a\nrepeat(S, 1, 0, 1)"), "S[1, 1, 0]", 1, "S[1, 1, 0]");
        AssertLoopStateArity(await OnEveryRouteAsync("S(a, b) = b, a + b, a\nrepeat(S, 2, 0, 1)"),
            "but the current loop state has 3 state values.");

        // OPENING varies; the flat head and the one written row stay: the spread opens the row's
        // value into two slots — exactly the two-row step — ...
        AssertOk(await OnEveryRouteAsync("S(a, b) = { (b, a + b)* }\nrepeat(S, 2, 0, 1)"), "S[1, 2]", 1, "S[1, 2]");
        // ... and at the consumer it opens the completed loop: one row, or its two items.
        AssertOk(await OnEveryRouteAsync("S(a, b) = b, a + b\nrepeat(S, 2, 0, 1)*"), "S[1, 2]", 2, "1", "2");
    }

    // ── One iteration equals the direct step call ──────────────────────────────

    /// <summary>
    /// LOOP-07, strengthened by Q-24 + Q-26: for a <c>repeat</c> step, one iteration equals the
    /// direct call on the same state in value AND root emitted count — for flat, patterned,
    /// repeated-name, collecting, list-pattern and nested-loop steps alike. (This is a statement
    /// about <c>repeat</c>: a <c>while</c> step's last row is its protocol flag, not state.)
    /// </summary>
    [Theory]
    [InlineData("Step(a, b) = b, a + b", "3, 4")]
    [InlineData("Step((*h), n) = h*, n + 1", "(1, 2), 0")]
    [InlineData("Step(x, x) = { (x + 1, x + 1)* }", "1, 1")]
    [InlineData("Step(*xs) = xs*, xs.count", "5, 6")]
    [InlineData("Step([a, b]) = [b, a]*, 9", "[1, 2]")]
    [InlineData("Step(a, b) = repeat({x + 1, y + x}, 1, a, b), a", "3, 4")]
    [InlineData("Step(a, b) = { repeat({x + 1, y + x}, 1, a, b)* }", "3, 4")]
    [InlineData("Step((a, b)) = (b, a + b)", "(0, 1)")]
    [InlineData("Step(a) = { ()* }", "7")]
    public async Task OneRepeatIteration_EqualsTheDirectCall_InValueAndEmittedCount(string step, string state)
    {
        var loop = await OnEveryRouteAsync(step + $"\nrepeat(Step, 1, {state})");
        var call = await OnEveryRouteAsync(step + $"\nStep({state})");
        Assert.Equal("ok", loop.Kind);
        Assert.Equal(call, loop);
        AssertOk(await OnEveryRouteAsync(step + $"\nrepeat(Step, 1, {state}) == Step({state})"), "true", 1, "true");
    }

    /// <summary>
    /// Iterating is not nesting calls: the next state is the step's row SUPPLY, while a call's result
    /// is ONE value. So <c>repeat(S, 2, s…)</c> equals <c>S(S(s…)*)</c> for a step whose rows each
    /// supply one item, and <c>S(S(s…))</c> for a step whose one row is a sequence value — and the
    /// mismatched nestings are arity errors.
    /// </summary>
    [Fact]
    public async Task IteratingIsNotNestingCalls()
    {
        const string defs = "Pair(x) = (x, x)\nFib(a, b) = b, a + b\n";
        AssertOk(await OnEveryRouteAsync(defs + "repeat(Pair, 2, 1) == Pair(Pair(1)), repeat(Fib, 2, 0, 1) == Fib(Fib(0, 1)*)"),
            "S[true, true]", 2, "true", "true");
        Assert.Equal("err", (await OnEveryRouteAsync(defs + "Pair(Pair(1)*)")).Kind);
        Assert.Equal("err", (await OnEveryRouteAsync(defs + "Fib(Fib(0, 1))")).Kind);
    }

    // ── Planned execution keeps the generic semantics ──────────────────────────

    /// <summary>
    /// A nested loop written as a step row now reports one value, so the planned loop frame can
    /// keep running where it formerly handed the iteration over to the generic loop. That is an
    /// optimizer-coverage change only: value, count, every budget counter and the host-call log
    /// equal the generic strategy's.
    /// </summary>
    [Fact]
    public void NestedLoopRow_StaysPlanned_AndChargesExactlyTheGenericBudgets()
    {
        const string source = "Fib(x, y) = y, x + y\nStepN(p, n) = repeat(Fib, 1, n, trace(n)), n + 1\nrepeat(StepN, 4, 0, 0)";
        var (genericResult, genericBudget, genericCalls, _) = RunWithTrace(source, optimize: false);
        var (plannedResult, plannedBudget, plannedCalls, loops) = RunWithTrace(source, optimize: true);

        Assert.True(genericResult.IsOk, genericResult.IsError ? genericResult.Error.ToString() : "");
        Assert.Equal(Neutral(genericResult.Value.Value), Neutral(plannedResult.Value.Value));
        Assert.Equal("S[S[3, 6], 4]", Neutral(plannedResult.Value.Value));
        Assert.Equal(1, plannedResult.Value.EmittedCount);
        Assert.Equal(genericResult.Value.EmittedCount, plannedResult.Value.EmittedCount);
        Assert.Equal(genericCalls, plannedCalls);
        Assert.Equal(["trace(0)", "trace(1)", "trace(2)", "trace(3)"], plannedCalls);

        Assert.Equal(genericBudget.ConsumedSteps, plannedBudget.ConsumedSteps);
        Assert.Equal(genericBudget.ConsumedExpressionCheckpoints, plannedBudget.ConsumedExpressionCheckpoints);
        Assert.Equal(genericBudget.MaterializedItems, plannedBudget.MaterializedItems);
        Assert.Equal(genericBudget.MaterializedStringChars, plannedBudget.MaterializedStringChars);
        Assert.Equal(genericBudget.PeakDepth, plannedBudget.PeakDepth);

        // The outer loop is planned and never hands over for its nested loop row.
        var outer = Assert.Single(loops.LoopPlans, plan => plan.Identity.StartsWith("StepN.", StringComparison.Ordinal));
        Assert.True(outer.Optimized);
        Assert.False(loops.FallbackReasons.ContainsKey("loop expression did not emit exactly one state value"));
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    /// <summary>
    /// One route's outcome: kind (<c>ok</c>, <c>err</c>, <c>parse</c>, <c>none</c>), the neutral value,
    /// the root emitted count, the display rows the count selects (the engine's
    /// <see cref="RunResult.Success.OutputRows"/>), every error as <c>Code: message @ span</c>, and
    /// the host-call log.
    /// </summary>
    public sealed record Observation(
        string Kind,
        string? Value,
        int? Emitted,
        IReadOnlyList<string> Rows,
        IReadOnlyList<string> Errors,
        IReadOnlyList<string> HostCalls)
    {
        public bool Equals(Observation? other)
            => other is not null
                && Kind == other.Kind
                && Value == other.Value
                && Emitted == other.Emitted
                && Rows.SequenceEqual(other.Rows)
                && Errors.SequenceEqual(other.Errors)
                && HostCalls.SequenceEqual(other.HostCalls);

        public override int GetHashCode() => HashCode.Combine(Kind, Value, Emitted);

        public override string ToString()
            => $"{Kind} {Value} n={Emitted} rows=[{string.Join(" | ", Rows)}] errors=[{string.Join(" | ", Errors)}] host=[{string.Join(",", HostCalls)}]";
    }

    private static async Task<Observation> OnEveryRouteAsync(string source)
    {
        var oracle = await ObserveAsync(SixRouteAgreement.Route.EngineSync, source);
        Assert.True(oracle.Kind != "parse", $"source must parse cleanly: {oracle}\nsource:\n{source}");
        foreach (var route in SixRouteAgreement.Routes.Skip(1))
        {
            var observation = await ObserveAsync(route, source);
            Assert.True(oracle.Equals(observation), $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
        }

        // Q-26 coherence: for a successful source program the root's emitted count IS its row count.
        if (oracle.Kind == "ok")
            Assert.True(oracle.Emitted == oracle.Rows.Count, $"emitted count {oracle.Emitted} != {oracle.Rows.Count} display rows\nsource:\n{source}");
        return oracle;
    }

    private static async Task<Observation> ObserveAsync(SixRouteAgreement.Route route, string source)
    {
        var log = new List<string>();
        var suspending = route is SixRouteAgreement.Route.EngineAsyncTwin or SixRouteAgreement.Route.ForcedTwin;
        var operations = HostOperationsFor(log, suspending);
        var options = new RunOptions { HostOperations = operations };

        switch (route)
        {
            case SixRouteAgreement.Route.EngineSync:
                return FromRunResult(KatLangEngine.Run(source, options), log);
            case SixRouteAgreement.Route.EngineAsync:
            case SixRouteAgreement.Route.EngineAsyncTwin:
                return FromRunResult(await KatLangEngine.RunAsync(source, options), log);
        }

        var parsed = Parser.Parse(source, options);
        if (parsed.HasErrors)
            return new Observation("parse", null, null, [], [.. parsed.Diagnostics.Select(static d => d.Message)], [.. log]);

        var program = new Expr.AlgorithmExpr(parsed.Root);
        var (result, _) = route switch
        {
            SixRouteAgreement.Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false, hostOperations: operations),
            SixRouteAgreement.Route.Optimized => Evaluator.RunCountedObserved(program, enableOptimizations: true, hostOperations: operations),
            SixRouteAgreement.Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: operations),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };

        if (result.IsError)
            return new Observation("err", null, null, [], [Describe(KatLangError.FromEvalError(result.Error))], [.. log]);

        var counted = result.Value;
        IReadOnlyList<Result> rows = counted.EmittedCount switch
        {
            0 => [],
            1 => [counted.Value],
            _ => counted.Value.ToItems(),
        };
        return new Observation("ok", Neutral(counted.Value), counted.EmittedCount, [.. rows.Select(Neutral)], [], [.. log]);
    }

    private static HostOperations HostOperationsFor(List<string> log, bool suspending)
    {
        Result Trace(Result value)
        {
            lock (log)
                log.Add($"trace({Neutral(value)})");
            return value;
        }

        return suspending
            ? HostOperations.Create(HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return Trace(args[0]); }, "x"))
            : HostOperations.Create(HostOperation.Create("trace", (args, _) => Trace(args[0]), "x"));
    }

    private static Observation FromRunResult(RunResult result, List<string> log) => result switch
    {
        RunResult.Success success => new Observation(
            "ok", Neutral(success.Value), success.EmittedCount, [.. success.OutputRows.Select(Neutral)], [], [.. log]),
        RunResult.EvalFailure failure => new Observation("err", null, null, [], [.. failure.Errors.Select(Describe)], [.. log]),
        RunResult.ParseFailure failure => new Observation("parse", null, null, [], [.. failure.Errors.Select(Describe)], [.. log]),
        RunResult.NoProgramOutput none => new Observation("none", null, null, [], [none.Diagnostic.Code.ToString()], [.. log]),
    };

    private static (EvalResult<Evaluator.CountedResult> Result, Evaluation.EvaluationBudget Budget, List<string> Calls, LoopOptimizationDiagnosticsSnapshot Loops)
        RunWithTrace(string source, bool optimize)
    {
        var log = new List<string>();
        var operations = HostOperationsFor(log, suspending: false);
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(static d => d.Message)));
        var root = parsed.Root;
        var loops = new LoopOptimizationDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(root), enableOptimizations: optimize, loopDiagnostics: loops, hostOperations: operations);
        return (result, budget, log, loops.GetSnapshot());
    }

    private static void AssertOk(Observation observation, string value, int emitted, params string[] rows)
    {
        Assert.True(observation.Kind == "ok", observation.ToString());
        Assert.Equal(value, observation.Value);
        Assert.Equal(emitted, observation.Emitted);
        Assert.Equal(rows, observation.Rows);
    }

    private static void AssertLoopStateArity(Observation observation, string sentence)
    {
        Assert.Equal("err", observation.Kind);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith("ArityMismatch: ", error, StringComparison.Ordinal);
        Assert.Contains(sentence, error, StringComparison.Ordinal);
    }

    private static IReadOnlyList<string> MessagesOnly(Observation observation)
        => [observation.Kind, .. observation.Errors.Select(static error => error.Split(" @ ")[0])];

    private static EvalError GenericError(string source)
    {
        var (result, _) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), enableOptimizations: false);
        Assert.True(result.IsError, source);
        return result.Error;
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static string Display(string source)
    {
        var run = KatLangEngine.Run(source);
        return Assert.IsType<RunResult.Success>(run).ToDisplayString().ReplaceLineEndings("\n");
    }

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";

    private static string Neutral(Result value) => SixRouteAgreement.Neutral(value);
}
