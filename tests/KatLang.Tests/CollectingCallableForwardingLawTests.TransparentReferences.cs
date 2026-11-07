using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// A TRANSPARENT REFERENCE KEEPS ITS COLLECTOR'S KNOWN SLICE (VAR-03 / FWD-03, audit finding A-2, owner
/// decision November 2026): <c>A = xs</c> followed by <c>A*</c> or <c>Box.A*</c> transports the cells
/// <c>xs*</c> transports, through any number of transparent hops, with the same order, shape, laziness,
/// effects, errors and charges. Selecting a member reads the receiver's declaration, never its output. Written
/// braces, calculations and any other spread operand stay arbitrary spreads. Every
/// expectation is written from the law and runs on the six routes (<see cref="AllRoutesAsync"/>), suspending
/// ones included. Lean: <c>EvalBody.transparentCollectorSlice?</c>, section 8 of
/// <c>CoreTests/CollectingCallableForwarding.lean</c> and <c>WholeAlgorithmTransport.lean</c>; spec cases
/// <c>collector-alias-*</c>.
/// </summary>
public sealed partial class CollectingCallableForwardingLawTests
{
    private const string Inline = "Inc(x) = x + 1\nApply(f) = f(9)\nT(x) = trace(x) + 1\n";

    private const string BoxA = "Box = {\npublic A = xs\n0\n}";

    /// <summary>The transparent spellings of the reference, one (declarations, operand) row each.</summary>
    public static TheoryData<string, string> ReferenceChains() => new()
    {
        { "A = xs", "A" },
        { "A0 = xs\nA = A0", "A" },
        { "A1 = xs\nA0 = A1\nA = A0", "A" },
        // A member path written at the spread, and the same path re-aliased.
        { BoxA, "Box.A" },
        { BoxA, "(Box.A)" },
        { BoxA + "\nY = Box.A", "Y" },
        { BoxA + "\nY = Box.A\nZ = Y", "Z" },
        // A hop inside the receiver, a hop before the member, a nested receiver and an aliased receiver.
        { "Box = {\npublic A = xs\npublic B = A\n0\n}", "Box.B" },
        { "T = xs\nBox = {\npublic A = T\n0\n}", "Box.A" },
        { "Box = {\npublic Inner = {\npublic A = xs\n0\n}\n0\n}", "Box.Inner.A" },
        { BoxA + "\nR = Box\nS = R", "S.A" },
        { BoxA + "\nOther = {\npublic Q = Box.A\n0\n}", "Other.Q" },
        // The output of the receiver is not the selected member, whatever it is.
        { "C = {\npublic A = xs\nxs\n}", "C.A" },
        { "C = {\npublic A = xs\n1 / 0\n}", "C.A" },
        { "C = {\npublic A = xs\n}", "C.A" },
        // An inline receiver block declaring the member.
        { "", "{\npublic A = xs\n0\n}.A" },
    };

    /// <summary>A callee block, a row written over the operand <c>@</c>, and the outer call.</summary>
    private static readonly (string Callees, string Row, string Call, string Expected, string[] Host)[] Witnesses =
    [
        ("Coll(*ys) = 0", "Coll(@*)", "F(1 / 0)", "ok 0 n=1", []),
        ("Coll(*ys) = ys.count", "Coll(@*)", "F()", "ok 0 n=1", []),
        ("Coll(*ys) = 0", "Coll(@*)", "F(trace(1), trace(2))", "ok 0 n=1", []),
        ("Coll(*ys) = ys", "Coll(@*)", "F(trace(1), trace(2), trace(3))", "ok L[1, 2, 3] n=1", ["trace(1)", "trace(2)", "trace(3)"]),
        ("Pick(a, b, c) = b", "Pick(@*)", "F(trace(1), trace(2), trace(3))", "ok 2 n=1", ["trace(2)"]),
        ("Use(*ys) = ys", "Use(@*), Use(@*)", "F(trace(5))", "ok S[L[5], L[5]] n=1", ["trace(5)"]),
        ("Two(a, b) = 0", "Two(@*)", "F(1 / 0, 2)", "ok 0 n=1", []),
        ("Rest(a, *r) = 0", "Rest(@*)", "F(1 / 0, 2)", "ok 0 n=1", []),
        ("Coll(*ys) = ys", "Coll(0, @*, 9)", "F(1, 2)", "ok L[0, 1, 2, 9] n=1", []),
        ("Coll(*ys) = 0\nG(*ws) = Coll(ws*)", "G(@*)", "F(1 / 0)", "ok 0 n=1", []),
        ("Coll(*ys) = ys", "Coll(@*)", "F((1, 2), (), [3])", "ok L[S[1, 2], S[], L[3]] n=1", []),
        ("Coll(*ys) = ys.count", "Coll(@*)", "F([1, 2])", "ok 1 n=1", []),
        ("", "[10, 20, 30][@*]", "F(0, 2)", "ok S[10, 30] n=1", []),
        (Inline, "Apply(@*)", "F(Inc)", "ok 10 n=1", []),
        (Inline, "Apply(@*) + Apply(@*)", "F(T)", "ok 20 n=1", ["trace(9)", "trace(9)"]),
    ];

    private static string Program(string declarations, string callees, string row, string call, string operand)
        => $"{callees}\nF(*xs) = {{\n{declarations}\n{row.Replace("@", operand, StringComparison.Ordinal)}\n}}\n{call}";

    [Theory]
    [MemberData(nameof(ReferenceChains))]
    public async Task TransparentReference_IsTheDirectKnownSlice_OnEveryRoute(string declarations, string operand)
    {
        foreach (var (callees, row, call, expected, host) in Witnesses)
        {
            var aliased = Program(declarations, callees, row, call, operand);
            var observation = await AllRoutesAsync(aliased);
            Assert.True(expected == observation.Outcome, $"expected {expected}, got {observation}\nsource:\n{aliased}");
            Assert.Equal(host, observation.HostCalls);
        }
    }

    [Theory]
    [MemberData(nameof(ReferenceChains))]
    public async Task TransparentReference_ChargesWhatTheDirectSliceCharges(string declarations, string operand)
    {
        foreach (var (callees, row, call, _, _) in Witnesses)
        {
            var (aliased, aliasedBudget) = await ObserveAsync(SixRouteAgreement.Route.Generic, Program(declarations, callees, row, call, operand));
            var (direct, directBudget) = await ObserveAsync(SixRouteAgreement.Route.Generic, Program(declarations, callees, row, call, "xs"));
            Assert.True(direct.Equals(aliased), $"expected {direct}, got {aliased}");
            Assert.Equal(directBudget, aliasedBudget);
        }
    }

    /// <summary>A demanded element raises its own error, once, at the demand; a check that precedes demand is unchanged.</summary>
    [Theory]
    [InlineData("Coll(*ys) = ys", "Coll(@*)", "F(1 / 0, 2)", "DivisionByZero/DivByZero")]
    [InlineData("Coll(*ys) = ys", "Coll(@*)", "F(1, 2 / 0, 3)", "DivisionByZero/DivByZero")]
    [InlineData("Two(a, b) = a", "Two(@*)", "F(1 / 0, 2)", "DivisionByZero/DivByZero")]
    [InlineData("Two(a, b) = 0", "Two(@*)", "F(1 / 0)", "ArityMismatch/ArityMismatch")]
    [InlineData("", "[10, 20][@*]", "F(99, 1 / 0)", "BadIndex/BadIndex")]
    [InlineData(Inline, "Apply(@*)", "F(5)", "NotAnAlgorithm/NotAnAlgorithm")]
    public async Task TransparentReference_FailsWhereTheDirectSliceFails(string callees, string row, string call, string cause)
    {
        var direct = await AllRoutesAsync(Program("A = xs\n" + BoxA, callees, row, call, "xs"));
        foreach (var operand in new[] { "A", "Box.A" })
        {
            var aliased = await AllRoutesAsync(Program("A = xs\n" + BoxA, callees, row, call, operand));
            Assert.Equal("err", aliased.Kind);
            Assert.Equal(cause, Assert.Single(aliased.Causes));
            Assert.Equal(direct.Causes, aliased.Causes);
            Assert.Equal(direct.HostCalls, aliased.HostCalls);
        }
    }

    [Fact]
    public async Task TransparentReference_DemandedCellCompletesOnce()
    {
        const string source = "Use(*ys) = ys\nF(*xs) = {\nA = xs\nB = A\nUse(A*), Use(B*), xs, A\n}\nF(trace(1), trace(2))";
        var observation = await AllRoutesAsync(source);
        Assert.Equal("ok S[L[1, 2], L[1, 2], L[1, 2], L[1, 2]] n=1", observation.Outcome);
        Assert.Equal(["trace(1)", "trace(2)"], observation.HostCalls);
    }

    [Fact]
    public async Task MemberPath_DemandedCellCompletesOnce()
    {
        var source = $"Use(*ys) = ys\nF(*xs) = {{\n{BoxA}\nY = Box.A\nUse(Box.A*), Use(Y*), xs, Box.A\n}}\nF(trace(1), trace(2))";
        var observation = await AllRoutesAsync(source);
        Assert.Equal("ok S[L[1, 2], L[1, 2], L[1, 2], L[1, 2]] n=1", observation.Outcome);
        Assert.Equal(["trace(1)", "trace(2)"], observation.HostCalls);
    }

    [Fact]
    public async Task MemberPath_MakesNoEffectAtFormation()
        => Assert.Equal("ok 1 n=1", (await AllRoutesAsync($"Coll(*ys) = 0\nF(t, *xs) = {{\n{BoxA}\nColl(Box.A*) + t + tick()\n}}\nF(0, tick())")).Outcome);

    /// <summary>An argument computation that really suspends stays suspended through the member path, and completes once at demand.</summary>
    [Theory]
    [InlineData("Coll(*ys) = 0", 0, "ok 0 n=1")]
    [InlineData("Coll(*ys) = ys", 2, "ok L[1, 2] n=1")]
    public async Task MemberPath_KeepsSuspendingArgumentsLazy(string collector, int calls, string expected)
    {
        var source = $"{collector}\nF(*xs) = {{\n{BoxA}\nColl(Box.A*)\n}}\nF(trace(1), trace(2))";
        var observation = await AllRoutesAsync(source);
        Assert.Equal(expected, observation.Outcome);
        Assert.Equal(calls, observation.HostCalls.Count);
    }

    [Fact]
    public async Task TransparentReference_MakesNoEffectAtFormation()
    {
        Assert.Equal("ok 1 n=1", (await AllRoutesAsync("Coll(*ys) = 0\nF(t, *xs) = {\nA = xs\nColl(A*) + t + tick()\n}\nF(0, tick())")).Outcome);
        Assert.Equal("ok 1 n=1", (await AllRoutesAsync("Coll(*ys) = 0\nF(t, *xs) = {\nA = xs\nColl(xs*) + t + tick()\n}\nF(0, tick())")).Outcome);
    }

    /// <summary>The row's cell is the one retained for the alias's own owner: everywhere the alias itself resolves.</summary>
    [Theory]
    // A collector of an enclosing body, read from a nested property.
    [InlineData("Coll(*ys) = 0\nF(*xs) = {\nA = xs\nInner = Coll(A*)\nInner\n}\nF(1 / 0)", "ok 0 n=1")]
    // A fixed parameter retaining a collector cell is the row's own cell.
    [InlineData("Coll(*ys) = 0\nPass(v) = {\nA = v\nColl(A*)\n}\nOuter(*fs) = Pass(fs)\nOuter(1 / 0)", "ok 0 n=1")]
    [InlineData(Inline + "Pass(v) = {\nA = v\nApply(A*)\n}\nOuter(*fs) = Pass(fs)\nOuter(Inc)", "ok 10 n=1")]
    // A static member hop and an open-provided reference are transparent chains too.
    [InlineData("Coll(*ys) = 0\nF(*xs) = {\nBox = {\npublic A = xs\n0\n}\nY = Box.A\nColl(Y*)\n}\nF(1 / 0)", "ok 0 n=1")]
    [InlineData("Coll(*ys) = 0\nF(*xs) = {\nopen Box\nBox = {\npublic A = xs\n0\n}\nColl(A*)\n}\nF(1 / 0)", "ok 0 n=1")]
    // A parameter of the spread site with the same name captures nothing: the alias's owner's cells move.
    [InlineData("Coll(*ys) = ys\nF(*xs) = {\nA = xs\nG(*xs) = Coll(A*)\nG(7, 8)\n}\nF(1, 2)", "ok L[1, 2] n=1")]
    [InlineData("Coll(*ys) = 0\nF(*xs) = {\nA = xs\nG(*xs) = Coll(A*)\nG(7)\n}\nF(1 / 0)", "ok 0 n=1")]
    // The same through a member: the member's own owner, never the spread site's parameter or a global of the name.
    [InlineData("Coll(*ys) = ys\nF(*xs) = {\n" + BoxA + "\nG(*xs) = Coll(Box.A*)\nG(7, 8)\n}\nF(1, 2)", "ok L[1, 2] n=1")]
    [InlineData("Coll(*ys) = 0\nF(*xs) = {\n" + BoxA + "\nG(*xs) = Coll(Box.A*)\nG(7)\n}\nF(1 / 0)", "ok 0 n=1")]
    [InlineData("Coll(*ys) = ys\nBox = {\npublic A = 5\n0\n}\nF(*xs) = {\n" + BoxA + "\nColl(Box.A*)\n}\nF(1, 2)", "ok L[1, 2] n=1")]
    // Each activation keeps its own cells, in a cached property of the body and in a recursive call.
    [InlineData("Coll(*ys) = ys\nF(*xs) = {\n" + BoxA + "\nP = Coll(Box.A*)\nP\n}\nF(1, 2), F(3)", "ok S[L[1, 2], L[3]] n=2")]
    [InlineData("Coll(*ys) = ys\nF(n, *xs) = {\n" + BoxA + "\nif(n > 0, F(n - 1, 7, 8), Coll(Box.A*))\n}\nF(1, 2)", "ok L[7, 8] n=1")]
    // An undecorated member readable from the site, and a fixed parameter retaining a collector cell, read through a member.
    [InlineData("Coll(*ys) = 0\nF(*xs) = {\nBox = {\nA = xs\n0\n}\nColl(Box.A*)\n}\nF(1 / 0)", "ok 0 n=1")]
    [InlineData("Coll(*ys) = 0\nPass(v) = {\nBox = {\npublic A = v\n0\n}\nColl(Box.A*)\n}\nOuter(*fs) = Pass(fs)\nOuter(1 / 0)", "ok 0 n=1")]
    // A loop's initial state keeps the callable through the reference.
    [InlineData("Zc(*xs) = 7\nAp(f) = f(1)\nS(n, *g) = {\nA = g\nAp(A*), g*\n}\nrepeat(S(0, Zc), 1)", "ok S[7, 7] n=1")]
    public async Task TransparentReference_FollowsTheRetainedCell(string source, string expected)
        => Assert.Equal(expected, (await AllRoutesAsync(source)).Outcome);

    /// <summary>The reference inaccessible where it is written stays refused by the ordinary read.</summary>
    [Theory]
    [InlineData("Coll(*ys) = ys\nBox(*xs) = {\npublic A = xs\n0\n}\nF(*xs) = {\nY = Box.A\nColl(Y*)\n}\nF(1, 2)", "LocalOnlyProperty")]
    // The member path itself: a same-named parameter of the site is not the member's owner.
    [InlineData("Coll(*ys) = ys\nBox(*xs) = {\npublic A = xs\n0\n}\nF(*xs) = Coll(Box.A*)\nF(1, 2)", "LocalOnlyProperty")]
    [InlineData("Coll(*ys) = 0\nBox(*xs) = {\npublic A = xs\n0\n}\nF(*xs) = Coll(Box.A*)\nF(1 / 0)", "LocalOnlyProperty")]
    // A receiver handed over as an argument leaves its owner's activation behind.
    [InlineData("Coll(*ys) = 0\nG(b) = Coll(b.A*)\nF(*xs) = {\n" + BoxA + "\nG(Box)\n}\nF(1 / 0)", "LocalOnlyProperty")]
    [InlineData("Coll(*ys) = 0\nG(b) = {\nY = b.A\nColl(Y*)\n}\nF(*xs) = {\n" + BoxA + "\nG(Box)\n}\nF(1 / 0)", "LocalOnlyProperty")]
    // A member declared only in a branch.
    [InlineData("Coll(*ys) = 0\nF(*xs) = {\nBox(0) = {\npublic A = xs\n0\n}\nBox(n) = 1\nColl(Box.A*)\n}\nF(1 / 0)", "LocalOnlyProperty")]
    public async Task TransparentReference_NeverWidensAccess(string source, string code)
    {
        var observation = await AllRoutesAsync(source);
        Assert.Equal("err", observation.Kind);
        Assert.StartsWith(code + "/", Assert.Single(observation.Causes), StringComparison.Ordinal);
    }

    /// <summary>
    /// Everything else stays an arbitrary spread: its operand is evaluated during supply formation, so an
    /// ignored failure is raised and every trace runs, however equal its eventual value.
    /// </summary>
    [Theory]
    [InlineData("A = { xs }", "A")]
    [InlineData("A = { xs }\nB = A", "B")]
    [InlineData("A = xs\nB = { A }", "B")]
    [InlineData("A = { Helper = 0\nxs }", "A")]
    [InlineData("A = xs + 0", "A")]
    [InlineData("A = [xs*]", "A")]
    [InlineData("A = Id(xs*)", "A")]
    [InlineData("A = xs", "(A, 1)")]
    [InlineData("A = xs", "Id(A)")]
    [InlineData("A = xs", "A*")]
    [InlineData("A = xs", "{ A }")]
    // A selected member that is itself no transparent reference to the cell.
    [InlineData("Box = {\npublic A = { xs }\n0\n}", "Box.A")]
    [InlineData("Box = {\npublic A = xs\npublic B = { A }\n0\n}", "Box.B")]
    [InlineData("Box = {\npublic A = { xs }\npublic B = A\n0\n}", "Box.B")]
    [InlineData("Box = {\npublic A = xs + 0\n0\n}", "Box.A")]
    [InlineData("Box = {\npublic A = [xs*]\n0\n}", "Box.A")]
    [InlineData("Box = {\npublic A = 1 / 0\n0\n}", "Box.A")]
    [InlineData("Box = {\npublic A = Id(xs*)\n0\n}", "Box.A")]
    // The receiver itself, whose rows a member selection never reads.
    [InlineData("C = {\npublic A = xs\nxs\n}", "C")]
    [InlineData("C = {\npublic A = xs\nxs\n}\nD = C", "D")]
    // Not the member reference itself: a stacked star, a call of the member, a group, a member's output row.
    [InlineData(BoxA, "Box.A*")]
    [InlineData(BoxA, "Box.A()")]
    [InlineData(BoxA, "(Box.A, 1)")]
    [InlineData(BoxA, "{ Box.A }")]
    [InlineData(BoxA + "\nA = { Box.A }", "A")]
    public async Task NonTransparentOperand_StaysAnArbitrarySpread(string declarations, string operand)
    {
        var source = $"Coll(*ys) = 0\nId(*zs) = zs\nF(*xs) = {{\n{declarations}\nColl({operand}*)\n}}\nF(1 / 0)";
        var observation = await AllRoutesAsync(source);
        Assert.Equal("err", observation.Kind);
        Assert.Equal("DivisionByZero/DivByZero", Assert.Single(observation.Causes));
    }

    [Theory]
    // A fixed parameter holding an ordinary computation or callable, aliased or not.
    [InlineData("Coll(*ys) = 0\nF(x) = {\nA = x\nColl(A*)\n}\nF(1 / 0)", "DivisionByZero/DivByZero")]
    [InlineData("Coll(*ys) = 0\nF(x) = Coll(x*)\nF(1 / 0)", "DivisionByZero/DivByZero")]
    [InlineData(Inline + "Coll(*ys) = 1\nPass(f) = {\nA = f\nColl(A*)\n}\nPass(Inc)", "ArityMismatch/ArityMismatch")]
    // A reference supplied as one argument is that argument's computation, not a retained collector cell.
    [InlineData("Coll(*ys) = 0\nPass(v) = Coll(v*)\nF(*xs) = {\nA = xs\nPass(A)\n}\nF(1 / 0)", "DivisionByZero/DivByZero")]
    [InlineData("Coll(*ys) = 0\nPass(v) = Coll(v*)\nF(*xs) = {\n" + BoxA + "\nPass(Box.A)\n}\nF(1 / 0)", "DivisionByZero/DivByZero")]
    // A member over a fixed parameter holding an ordinary computation, a structural collector and an ordinary property.
    [InlineData("Coll(*ys) = 0\nF(x) = {\nBox = {\npublic A = x\n0\n}\nColl(Box.A*)\n}\nF(1 / 0)", "DivisionByZero/DivByZero")]
    [InlineData("Coll(*ys) = 0\nF((x, *r)) = {\nBox = {\npublic A = r\n0\n}\nColl(Box.A*)\n}\nF((1, 1 / 0))", "DivisionByZero/DivByZero")]
    [InlineData("Coll(*ys) = 0\nBox = {\npublic A = 1 / 0\n0\n}\nColl(Box.A*)", "DivisionByZero/DivByZero")]
    [InlineData("Coll(*ys) = 0\nBox = {\npublic P = 1 / 0\npublic A = P\n0\n}\nColl(Box.A*)", "DivisionByZero/DivByZero")]
    // Ordinary scalar and property spreads, and a static reference to the property.
    [InlineData("Coll(*ys) = 0\nColl((1 / 0)*)", "DivisionByZero/DivByZero")]
    [InlineData("Coll(*ys) = 0\nP = 1 / 0\nColl(P*)", "DivisionByZero/DivByZero")]
    [InlineData("Coll(*ys) = 0\nP = 1 / 0\nA = P\nColl(A*)", "DivisionByZero/DivByZero")]
    // A structural collector's elements were demanded by their pattern.
    [InlineData("Coll(*ys) = 0\nF((x, *r)) = {\nA = r\nColl(A*)\n}\nF((1, 1 / 0))", "DivisionByZero/DivByZero")]
    public async Task OrdinarySpreadOperands_KeepTheirFormationFailure(string source, string cause)
    {
        var observation = await AllRoutesAsync(source);
        Assert.Equal("err", observation.Kind);
        Assert.Equal(cause, Assert.Single(observation.Causes));
    }

    [Theory]
    [InlineData("A = { xs }", "ok 0 n=1", null, "trace(1)", "trace(2)")]
    [InlineData("A = xs + xs", null, "TypeMismatch/TypeMismatch", "trace(1)", "trace(2)")]
    [InlineData("Box = {\npublic M = { xs }\n0\n}\nA = Box.M", "ok 0 n=1", null, "trace(1)", "trace(2)")]
    public async Task ArbitrarySpread_RunsItsEffectsAtFormation(string declarations, string? expected, string? cause, params string[] host)
    {
        var observation = await AllRoutesAsync($"Coll(*ys) = 0\nF(*xs) = {{\n{declarations}\nColl(A*)\n}}\nF(trace(1), trace(2))");
        if (cause is not null)
        {
            Assert.Equal("err", observation.Kind);
            Assert.Equal(cause, Assert.Single(observation.Causes));
        }
        else
            Assert.Equal(expected, observation.Outcome);
        Assert.Equal(host, observation.HostCalls);
    }

    /// <summary>Every other observation of the reference is what it was: only an explicit spread transports.</summary>
    [Theory]
    [InlineData("A", "ok L[1, 2] n=1")]
    [InlineData("A()", "ok L[1, 2] n=1")]
    [InlineData("A.count", "ok 2 n=1")]
    [InlineData("A[1]", "ok 2 n=1")]
    [InlineData("A*", "ok S[1, 2] n=1")]
    [InlineData("[A*]", "ok L[1, 2] n=1")]
    [InlineData("Box.A", "ok L[1, 2] n=1")]
    [InlineData("Box.A()", "ok L[1, 2] n=1")]
    [InlineData("Box.A.count", "ok 2 n=1")]
    [InlineData("Box.A[1]", "ok 2 n=1")]
    [InlineData("Box.A*", "ok S[1, 2] n=1")]
    [InlineData("[Box.A*]", "ok L[1, 2] n=1")]
    public async Task OtherReadsOfTheReference_AreUnchanged(string row, string expected)
        => Assert.Equal(expected, (await AllRoutesAsync($"F(*xs) = {{\nA = xs\n{BoxA}\n{row}\n}}\nF(1, 2)")).Outcome);

    /// <summary>A plan's one supply is formed by the same slot: META sees the cells, nothing demanded.</summary>
    [Theory]
    [InlineData("A")]
    [InlineData("Box.A")]
    [InlineData("xs")]
    public async Task PlannedCall_TransportsTheSameCells(string operand)
    {
        var source = $"Coll(*ys) = 0\nCapture(meta op) = op.Arguments.count\nF(*xs) = {{\nA = xs\n{BoxA}\nCapture(Coll({operand}*))\n}}\nF(1 / 0, trace(2))";
        Assert.Equal("ok 2 n=1", (await AllRoutesAsync(source)).Outcome);
        using (InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()))
            Assert.Equal("ok 2 n=1", (await AllRoutesAsync(source)).Outcome);
    }

    [Theory]
    [InlineData("B")]
    [InlineData("Box.A")]
    public async Task EveryPlannedRoute_AgreesOnTheSlice(string operand)
    {
        using var seam = InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam());
        foreach (var (callees, row, call, expected, host) in Witnesses)
        {
            var observation = await AllRoutesAsync(Program("A = xs\nB = A\n" + BoxA, callees, row, call, operand));
            Assert.Equal(expected, observation.Outcome);
            Assert.Equal(host, observation.HostCalls);
        }
    }

    /// <summary>A runtime row that is no parameter has no known slice: its <c>.Algorithm</c> route and VALUE read stay ordinary, on every route.</summary>
    [Fact]
    public async Task LinkMember_StaysAnArbitrarySpread()
    {
        var observation = await AllRoutesAsync("Mk(n) = n, n\nColl(*ys) = 0\nHold(meta op) = op\nR = Hold(Mk(trace(5)))\nBox = {\npublic A = R.Algorithm\n0\n}\nColl(Box.A*)");
        Assert.Equal("err", observation.Kind);
        Assert.Equal("ArityMismatch/ArityMismatch", Assert.Single(observation.Causes));
    }

    [Fact]
    public async Task LinkRow_StaysAnArbitrarySpread()
    {
        var observation = await AllRoutesAsync("Mk(n) = n, n\nColl(*ys) = 0\nHold(meta op) = op\nR = Hold(Mk(trace(5)))\nA = R.Algorithm\nColl(A*)");
        Assert.Equal("err", observation.Kind);
        Assert.Equal("ArityMismatch/ArityMismatch", Assert.Single(observation.Causes));
    }
}
