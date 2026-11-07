namespace KatLang.Tests;

/// <summary>
/// SELECTIVE OBSERVATION OF A RETAINED COLLECTOR (NEED-07, November 2026): <c>count</c>, <c>first</c>,
/// <c>last</c>, <c>take</c> and postfix selection read a collecting parameter's exact slice of need cells
/// and demand only the elements their result needs; a genuine whole VALUE, an ordinary list and every
/// computed carrier stay eager. Every expectation is written from the contract and runs on the six
/// routes (<see cref="SixRouteAgreement"/>), which compare values, the ordered host-call log and every
/// structured error. <c>trace</c> suspends on the twin routes, so a demanded element genuinely suspends
/// and an undemanded one is never entered. Lean: <c>retainedCollectorBuiltin</c>,
/// <c>EvalBody.retainedCellSlice?</c>, <c>CoreTests/SelectiveCollectorReads.lean</c> and
/// <c>KatLangArityLaws/SelectiveCollector.lean</c>; spec cases <c>selective-collector-*</c>.
/// </summary>
public sealed class SelectiveCollectorReadTests
{
    private static async Task<SixRouteAgreement.Observation> Ok(string source, string expected, params string[] host)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "ok" && observation.Value == expected, $"expected {expected}, got {observation}\nsource:\n{source}");
        Assert.Equal(host, observation.HostCalls);
        return observation;
    }

    private static async Task<SixRouteAgreement.Observation> Fails(string source, string code, params string[] host)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "err" && observation.Errors.Single().StartsWith(code + ":", StringComparison.Ordinal),
            $"expected {code}, got {observation}\nsource:\n{source}");
        Assert.Equal(host, observation.HostCalls);
        return observation;
    }

    private static string F(string body, string call) => $"F(*xs) = {body}\n{call}";

    // ── The primary witnesses and the acceptance table ──────────────────────────────────────────

    [Fact]
    public async Task PrimaryWitnesses_TogetherAndIndependently()
    {
        const string declarations = "CountItems(*xs) = xs.count\nFirstItem(*xs) = xs[0]\nPrefix(*xs) = xs.take(1)\n";
        await Ok(declarations + "CountItems(1 / 0)\nFirstItem(10, 1 / 0)\nPrefix(10, 1 / 0)", "S[1, 10, L[10]]");
        await Ok(declarations + "CountItems(1 / 0)", "1");
        await Ok(declarations + "FirstItem(10, 1 / 0)", "10");
        await Ok(declarations + "Prefix(10, 1 / 0)", "L[10]");
    }

    [Theory]
    [InlineData("xs.count", "F(1 / 0)", "1")]
    [InlineData("xs.count", "F()", "0")]
    [InlineData("xs.count", "F(())", "1")]
    [InlineData("xs.first", "F(10, 1 / 0)", "10")]
    [InlineData("xs.last", "F(1 / 0, 20)", "20")]
    [InlineData("xs[1]", "F(1 / 0, 20)", "20")]
    [InlineData("xs[]", "F(1 / 0)", "S[]")]
    [InlineData("xs[1, 0, 1]", "F(10, 20, 1 / 0)", "S[20, 10, 20]")]
    [InlineData("xs.take(1)", "F(10, 1 / 0)", "L[10]")]
    [InlineData("xs.take(0)", "F(1 / 0)", "L[]")]
    public Task AcceptanceTable_Values(string body, string call, string expected) => Ok(F(body, call), expected);

    [Theory]
    [InlineData("xs[99]", "F(1 / 0)", "BadIndex")]
    [InlineData("xs.take(2)", "F(10, 1 / 0)", "DivisionByZero")]
    public Task AcceptanceTable_Failures(string body, string call, string code) => Fails(F(body, call), code);

    // ── A whole VALUE, ordinary data and carriers stay eager ────────────────────────────────────

    [Theory]
    [InlineData("xs")]
    [InlineData("[xs*]")]
    [InlineData("(xs, 1)")]
    [InlineData("xs + 0")]
    [InlineData("[xs*][0]")]
    [InlineData("[xs*].count")]
    [InlineData("[xs*][]")]
    [InlineData("[xs*].take(0)")]
    [InlineData("(xs*)[0]")]
    [InlineData("(xs*).count")]
    [InlineData("xs.skip(1)")]
    [InlineData("xs.sum")]
    [InlineData("xs.contains(1)")]
    [InlineData("xs.distinct")]
    public Task WholeValueConsumers_StayEager(string body) => Fails(F(body, "F(1 / 0)"), "DivisionByZero");

    [Theory]
    [InlineData("[10, 1 / 0][0]")]
    [InlineData("[1 / 0].count")]
    [InlineData("(10, 1 / 0)[0]")]
    [InlineData("[10, 1 / 0].take(1)")]
    [InlineData("first([10, 1 / 0])")]
    public Task WrittenCollections_StayEager(string source) => Fails(source, "DivisionByZero");

    [Theory]
    [InlineData("A = { xs }\nA.count")]
    [InlineData("A = { xs }\nA[0]")]
    [InlineData("A = { xs }\nA.take(0)")]
    [InlineData("A = { Helper = 0\nxs }\nA.count")]
    [InlineData("A = [xs*]\nA.count")]
    [InlineData("A = [xs*]\nA[]")]
    [InlineData("Id(v) = v\nA = Id(xs)\nA.count")]
    [InlineData("Id(v) = v\nId(xs).count")]
    [InlineData("Mk(u) = xs\nMk(0).count")]
    [InlineData("Mk(u) = xs\nMk(0)[0]")]
    [InlineData("A = xs\nA().count")]
    [InlineData("Box = {\npublic A(u) = xs\n0\n}\nBox.A(0).count")]
    [InlineData("Box = {\npublic A = { xs }\n0\n}\nBox.A.count")]
    public Task CarriersAndCallResults_StayEager(string body)
        => Fails($"F(*xs) = {{\n{body}\n}}\nF(1 / 0)", "DivisionByZero");

    // ── One builtin identity, however it is reached ─────────────────────────────────────────────

    [Theory]
    [InlineData("count(xs)", "F(1 / 0)", "1")]
    [InlineData("first(xs)", "F(10, 1 / 0)", "10")]
    [InlineData("last(xs)", "F(1 / 0, 20)", "20")]
    [InlineData("take(xs, 1)", "F(10, 1 / 0)", "L[10]")]
    [InlineData("(xs).count", "F(1 / 0)", "1")]
    [InlineData("((xs))[0]", "F(10, 1 / 0)", "10")]
    public Task PlainAndGroupedSpellings_AgreeWithDot(string body, string call, string expected) => Ok(F(body, call), expected);

    [Theory]
    [InlineData("Size = count\nF(*xs) = Size(xs)\nF(1 / 0)", "1")]
    [InlineData("Head = first\nF(*xs) = xs.Head\nF(10, 1 / 0)", "10")]
    [InlineData("Pre = take\nF(*xs) = Pre(xs, 1)\nF(10, 1 / 0)", "L[10]")]
    public Task BuiltinAliases_AreTheBuiltin(string source, string expected) => Ok(source, expected);

    [Theory]
    [InlineData("count(v) = v\nF(*xs) = count(xs)\nF(1 / 0)")]
    [InlineData("first(v) = v + 1\nF(*xs) = xs.first\nF(1 / 0)")]
    [InlineData("take(v, n) = v\nF(*xs) = xs.take(1)\nF(1 / 0)")]
    public Task AUserBindingWithTheSpelling_KeepsItsOwnBehavior(string source) => Fails(source, "DivisionByZero");

    [Fact]
    public Task ADeclaredMember_WinsOverTheBuiltin()
        => Ok("Box = {\npublic count = 5\n0\n}\nBox.count", "5");

    [Theory]
    [InlineData("xs.take()")]
    [InlineData("take(xs, 1, 2)")]
    [InlineData("count(xs, 1)")]
    [InlineData("first(xs, 1)")]
    public Task WrongArity_RejectsBeforeAnyElement(string body) => Fails(F(body, "F(trace(1))"), "ArityMismatch");

    // ── Reference consistency: one retained-slice rule ──────────────────────────────────────────

    public static TheoryData<string, string> ReferenceChains() => CollectingCallableForwardingLawTests.ReferenceChains();

    [Theory]
    [MemberData(nameof(ReferenceChains))]
    public async Task EveryTransparentSpelling_ObservesTheDirectSlice(string declarations, string operand)
    {
        string Program(string row, string call) => $"F(*xs) = {{\n{declarations}\n{row.Replace("@", operand, StringComparison.Ordinal)}\n}}\n{call}";
        await Ok(Program("@.count", "F(trace(1), trace(2))"), "2");
        await Ok(Program("count(@)", "F(trace(1), trace(2))"), "2");
        await Ok(Program("@.first", "F(trace(1), trace(2))"), "1", "trace(1)");
        await Ok(Program("@.last", "F(trace(1), trace(2))"), "2", "trace(2)");
        await Ok(Program("@[1]", "F(trace(1), trace(2))"), "2", "trace(2)");
        await Ok(Program("@[]", "F(1 / 0)"), "S[]");
        await Ok(Program("@.take(1)", "F(trace(1), trace(2))"), "L[1]", "trace(1)");
    }

    [Theory]
    [InlineData("Size(v) = v.count\nF(*xs) = Size(xs)\nF(1 / 0)", "1")]
    [InlineData("Head(v) = v[0]\nF(*xs) = Head(xs)\nF(10, 1 / 0)", "10")]
    [InlineData("Pre(v) = v.take(1)\nF(*xs) = Pre(xs)\nF(10, 1 / 0)", "L[10]")]
    [InlineData("Size(v) = v.count\nF(*xs) = {\nA = xs\nSize(A)\n}\nF(1 / 0)", "1")]
    [InlineData("Head(v) = v[0]\nF(*xs) = {\nA = xs\nHead(A)\n}\nF(10, 1 / 0)", "10")]
    [InlineData("Size(v) = v.count\nF(*xs) = {\nBox = {\npublic A = xs\n0\n}\nSize(Box.A)\n}\nF(1 / 0)", "1")]
    [InlineData("Size(v) = v.count\nRelay(w) = {\nB = w\nSize(B)\n}\nF(*xs) = {\nA = xs\nRelay(A)\n}\nF(1 / 0)", "1")]
    [InlineData("Size(*ys) = ys.count\nF(*xs) = Size(xs*)\nF(1 / 0)", "1")]
    [InlineData("Head(*ys) = ys[0]\nF(*xs) = {\nA = xs\nHead(A*)\n}\nF(10, 1 / 0)", "10")]
    public Task HelperTransport_ReadsTheSameCells(string source, string expected) => Ok(source, expected);

    [Fact]
    public Task ALongChainOfReferenceArguments_IsOneLoop()
    {
        const string source = "Walk(w, n) = {\nB = w\nif(n == 0, B.count, Walk(B, n - 1))\n}\nF(*xs) = {\nA = xs\nWalk(A, 30)\n}\nF(1 / 0, 2)";
        return Ok(source, "2");
    }

    [Theory]
    [InlineData("Reader(b) = b.A.count\nF(*xs) = {\nBox = {\npublic A = xs\n0\n}\nReader(Box)\n}\nF(1 / 0)")]
    [InlineData("Box(*xs) = {\npublic A = xs\n0\n}\nF(*xs) = Box.A.count\nF(1 / 0)")]
    [InlineData("Box(*xs) = {\npublic A = xs\n0\n}\nF(*xs) = Box.A[0]\nF(1 / 0)")]
    public Task AnInaccessibleMember_KeepsItsRefusal(string source) => Fails(source, "LocalOnlyProperty");

    [Fact]
    public Task ReceiverRows_AreNeverExecuted()
        => Ok("F(*xs) = {\nBox = {\npublic A = xs\ntrace(9)\n}\nBox.A.count, Box.A[0]\n}\nF(5)", "S[1, 5]");

    [Fact]
    public Task AnOpenProvidedReference_IsObserved()
        => Ok("F(*xs) = {\nopen Box\nBox = {\npublic A = xs\n0\n}\nA.count\n}\nF(1 / 0)", "1");

    // ── Shape: positions, not atoms or emitted values ───────────────────────────────────────────

    [Theory]
    [InlineData("xs.count", "F([1, 2], (3, 4), (), [])", "4")]
    [InlineData("xs.first", "F((), 2)", "S[]")]
    [InlineData("xs.last", "F(2, [])", "L[]")]
    [InlineData("xs[0]", "F((1, 2), 1 / 0)", "S[1, 2]")]
    [InlineData("xs[0, 1]", "F((), [], 1 / 0)", "S[S[], L[]]")]
    [InlineData("xs.take(1)", "F((1, 2), 1 / 0)", "L[S[1, 2]]")]
    [InlineData("xs.take(2)", "F((), [])", "L[S[], L[]]")]
    [InlineData("xs.count, xs.take(1).count", "F(1, 2)", "S[2, 1]")]
    public Task Shape_IsTheSuppliedPositions(string body, string call, string expected) => Ok(F(body, call), expected);

    [Fact]
    public async Task AnEmptySlice_ReportsTheOrdinarySelectionFailure()
    {
        var first = await Fails(F("xs.first", "F()"), "BadIndex");
        var ordinary = await Fails("first([])", "BadIndex");
        Assert.Contains("first selects from an empty collection", first.Errors.Single(), StringComparison.Ordinal);
        Assert.Contains("first selects from an empty collection", ordinary.Errors.Single(), StringComparison.Ordinal);
        await Fails(F("xs.last", "F()"), "BadIndex");
        await Fails(F("xs[0]", "F()"), "BadIndex");
    }

    // ── Selective VALUE, selector order and formation ───────────────────────────────────────────

    [Theory]
    [InlineData("xs[1]", "2", new[] { "trace(2)" })]
    [InlineData("xs[2, 0]", "S[3, 1]", new[] { "trace(3)", "trace(1)" })]
    [InlineData("xs[1, 1, 1]", "S[2, 2, 2]", new[] { "trace(2)" })]
    [InlineData("xs[1, 0, 1]", "S[2, 1, 2]", new[] { "trace(2)", "trace(1)" })]
    public Task PositionOrder_IsFirstDemandOrder(string body, string expected, string[] host)
        => Ok(F(body, "F(trace(1), trace(2), trace(3))"), expected, host);

    [Theory]
    [InlineData("xs['a']", "TypeMismatch")]
    [InlineData("xs[true]", "TypeMismatch")]
    [InlineData("xs[-1]", "BadIndex")]
    [InlineData("xs[0.5]", "BadIndex")]
    [InlineData("xs[1 / 3]", "BadIndex")]
    [InlineData("xs[99999999999999]", "BadIndex")]
    [InlineData("xs[(0, 1)]", "TypeMismatch")]
    public Task AnInvalidSelector_DemandsNoElement(string body, string code) => Fails(F(body, "F(trace(1))"), code);

    [Fact]
    public async Task TheFirstFailureEndsTheSelection()
    {
        await Fails(F("xs[0, 99, 0]", "F(trace(1))"), "BadIndex", "trace(1)");
        await Fails(F("xs[99, trace(0)]", "F(trace(1))"), "BadIndex");
        await Fails(F("xs[0, 1, trace(0)]", "F(trace(1), 1 / 0)"), "DivisionByZero", "trace(1)");
    }

    [Fact]
    public async Task SelectorFormation_PrecedesValidation()
    {
        await Fails(F("xs[99, (1 / 0)*]", "F(trace(1))"), "DivisionByZero");
        await Fails(F("xs[99, 1 / 0]", "F(trace(1))"), "BadIndex");
        await Ok("F(*xs) = G(xs*)\nG(*ys) = [10, 20][ys*]\nF(1)", "20");
        // A known slice transported as selectors stays unforced until its turn.
        await Fails("Pick(*i) = [10, 20][99, i*]\nPick(1 / 0)", "BadIndex");
        await Ok("Pick(*i) = {\nA = i\n[10, 20][A*]\n}\nPick(0, 1)", "S[10, 20]");
        await Ok("F(*xs) = xs[xs*]\nF(1, 0)", "S[0, 1]");
    }

    // ── take controls ───────────────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData(-1, "L[]", new string[0])]
    [InlineData(0, "L[]", new string[0])]
    [InlineData(1, "L[1]", new[] { "trace(1)" })]
    [InlineData(2, "L[1, 2]", new[] { "trace(1)", "trace(2)" })]
    [InlineData(3, "L[1, 2]", new[] { "trace(1)", "trace(2)" })]
    public Task Take_DemandsExactlyItsPrefixInSourceOrder(int count, string expected, string[] host)
        => Ok(F($"xs.take({count})", "F(trace(1), trace(2))"), expected, host);

    [Fact]
    public async Task Take_ASaturatingCount_IsTheWholeSlice()
        => await Ok(F("xs.take(99999999999999999999)", "F(trace(1))"), "L[1]", "trace(1)");

    [Theory]
    [InlineData("xs.take('a')", "TypeMismatch")]
    [InlineData("xs.take(true)", "TypeMismatch")]
    [InlineData("xs.take([1])", "TypeMismatch")]
    [InlineData("xs.take(0.5)", "IllegalInEval")]
    [InlineData("xs.take(1 / 0)", "DivisionByZero")]
    public Task Take_ValidatesItsCountBeforeAnyElement(string body, string code) => Fails(F(body, "F(trace(1))"), code);

    [Fact]
    public async Task Take_CountEffects_PrecedeAKnownPrefix_OrdinaryInputsKeepTheirOrder()
    {
        await Ok(F("xs.take(trace(1))", "F(trace(5))"), "L[5]", "trace(1)", "trace(5)");
        await Ok("Id(v) = v\nId([trace(5)]).take(trace(1))", "L[5]", "trace(5)", "trace(1)");
        await Fails("[1 / 0].take('a')", "DivisionByZero");
    }

    // ── Effects and shared completion ───────────────────────────────────────────────────────────

    [Fact]
    public Task TheEffectWitness() => Ok("F(*xs) = xs[1], xs[0], xs[1]\nF(tick(), tick())", "S[1, 2, 1]");

    [Fact]
    public async Task ASkippedElement_DrawsNothing()
    {
        await Ok(F("xs.first, tick()", "F(tick(), tick())"), "S[1, 2]");
        await Ok(F("xs.count, tick()", "F(tick(), tick())"), "S[2, 1]");
        await Ok(F("xs.take(1), tick()", "F(tick(), tick())"), "S[L[1], 2]");
        var skipped = await SixRouteAgreement.OnEveryRouteAsync(F("xs.count, randomInt(1, 1000000)", "F(randomInt(1, 1000000), randomInt(1, 1000000))"), randomSeed: 7);
        var fresh = await SixRouteAgreement.OnEveryRouteAsync("2, randomInt(1, 1000000)", randomSeed: 7);
        Assert.Equal(fresh.Value, skipped.Value);
    }

    [Theory]
    [InlineData("xs[1], xs[1]", "S[1, 1]", new[] { "trace(1)" }, "F(2, trace(1))")]
    [InlineData("xs[1], xs", "S[2, L[1, 2]]", new[] { "trace(2)", "trace(1)" }, "F(trace(1), trace(2))")]
    [InlineData("xs.last, xs", "S[2, L[1, 2]]", new[] { "trace(2)", "trace(1)" }, "F(trace(1), trace(2))")]
    [InlineData("xs.first, xs", "S[1, L[1, 2]]", new[] { "trace(1)", "trace(2)" }, "F(trace(1), trace(2))")]
    [InlineData("xs.take(1), xs", "S[L[1], L[1, 2]]", new[] { "trace(1)", "trace(2)" }, "F(trace(1), trace(2))")]
    [InlineData("xs, xs[1]", "S[L[1, 2], 2]", new[] { "trace(1)", "trace(2)" }, "F(trace(1), trace(2))")]
    [InlineData("xs.first, xs.first, xs.take(1), xs[0]", "S[1, 1, L[1], 1]", new[] { "trace(1)" }, "F(trace(1), trace(2))")]
    public Task EachElementCompletesOnce_APartialReadPublishesNoPartialList(string body, string expected, string[] host, string call)
        => Ok(F(body, call), expected, host);

    [Fact]
    public async Task AnElementCompletesOnceThroughAliases_And_AWholeReadFinishesTheRemainder()
    {
        await Ok("F(*xs) = {\nA = xs\nB = A\nA[1], B[1], xs[1], A\n}\nF(trace(1), trace(2))", "S[2, 2, 2, L[1, 2]]", "trace(2)", "trace(1)");
        await Ok("F(*xs) = xs[2], xs\nF(trace(1), trace(2), trace(3))", "S[3, L[1, 2, 3]]", "trace(3)", "trace(1)", "trace(2)");
        await Fails(F("xs.first, xs", "F(1, 1 / 0)"), "DivisionByZero");
    }

    // ── Channels ────────────────────────────────────────────────────────────────────────────────

    private const string Inc = "Inc(x) = x + 1\nApply(f) = f(9)\n";

    [Fact]
    public async Task CountingACallableBearingCell_ProjectsAndInvokesNothing()
    {
        await Ok(Inc + "F(*xs) = xs.count\nF(Inc)", "1");
        await Ok(Inc + "F(*xs) = xs.count\nF(Inc, { 1 / 0 })", "2");
    }

    [Fact]
    public async Task SelectingOrTaking_RequestsVALUE_AndInventsNoCallable()
    {
        await Fails(Inc + "F(*xs) = xs.first\nF(Inc)", "ArityMismatch");
        await Fails(Inc + "F(*xs) = xs[0]\nF(Inc)", "ArityMismatch");
        await Fails(Inc + "F(*xs) = xs.take(1)\nF(Inc)", "ArityMismatch");
        await Fails(Inc + "F(*xs) = Apply(xs[0])\nF(7)", "NotAnAlgorithm");
        await Fails(Inc + "F(*xs) = Apply(xs.first)\nF(7)", "NotAnAlgorithm");
    }

    [Fact]
    public Task SpreadTransport_KeepsItsCallableChannel() => Ok(Inc + "F(*xs) = Apply(xs*), xs.count\nF(Inc)", "S[10, 1]");

    // ── Failure provenance ──────────────────────────────────────────────────────────────────────

    [Fact]
    public async Task ADemandedElement_KeepsItsOwnReport_WhatSkipsStaysDormant()
    {
        var direct = await Fails(F("xs.first", "F(1 / 0)"), "DivisionByZero");
        Assert.Contains("@ [2:3, 2:8)", direct.Errors.Single(), StringComparison.Ordinal);
        var selected = await Fails(F("xs[1]", "F(0, 1 / 0)"), "DivisionByZero");
        Assert.Contains("@ [2:6, 2:11)", selected.Errors.Single(), StringComparison.Ordinal);
        var taken = await Fails(F("xs.take(2)", "F(0, 1 / 0)"), "DivisionByZero");
        Assert.Contains("@ [2:6, 2:11)", taken.Errors.Single(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("xs[0]*")]
    [InlineData("xs.first*")]
    [InlineData("xs.take(1)*")]
    public Task ANestedMissingOutput_StaysNested(string body) => Fails(F(body, "F({ })"), "MissingOutput");

    [Theory]
    [InlineData("xs*")]
    public Task AWholeRead_KeepsItsOwnMissingOutputReport(string body) => Fails(F(body, "F({ })"), "MissingOutput");

    [Fact]
    public Task SelectionAndCount_LeaveAFailedElementDormantBesideASelectedOne()
        => Ok(F("xs.count, xs[0]", "F(1, 1 / 0)"), "S[2, 1]");

    // ── Ownership and isolation ─────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("Outer(*xs) = {\nInner(*xs) = xs.count\nInner(1, 2, 3)\n}\nOuter(1 / 0)", "3")]
    [InlineData("Size(xs) = xs.count\nOuter(*xs) = Size([1, 2, 3])\nOuter(1 / 0)", "3")]
    [InlineData("Outer(*xs) = {\nA = xs\nHelper(*ys) = A.count + ys.count\nHelper(1, 2)\n}\nOuter(1 / 0)", "3")]
    [InlineData("Size(*xs) = xs.count\nSize(1 / 0), Size(), Size(1 / 0, 2)", "S[1, 0, 2]")]
    [InlineData("Size(*xs) = xs.count\nA = Size(1 / 0)\nB = Size(1 / 0, 2)\nA + B", "3")]
    [InlineData("First(*xs) = xs.first\nFirst(1, 1 / 0), First(2, 1 / 0)", "S[1, 2]")]
    public Task ShadowedNamesAndSeparateActivations_NeverShareASlice(string source, string expected) => Ok(source, expected);

    [Fact]
    public async Task SeparateRuns_NeverShareAnOutcome()
    {
        const string source = "F(*xs) = xs.first\nF(tick())";
        await Ok(source, "1");
        await Ok(source, "1");
    }

    // ── Pre-existing contracts around the new path ──────────────────────────────────────────────

    [Theory]
    [InlineData("P([a, b]) = a\nF(*xs) = P(xs)\nF(1, 1 / 0)")]
    [InlineData("P(a, a) = 0\nF(*xs) = P(xs, xs)\nF(1 / 0)")]
    public Task StructuralPatternsAndRepeatedNames_InspectTheWholeValue(string source) => Fails(source, "DivisionByZero");

    [Theory]
    [InlineData("F(*xs) = {\nStep(n) = n + xs.count\nrepeat(Step(0), 3)\n}\nF(1, 2)", "6")]
    public Task LoopsRead_TheRetainedSliceThroughTheirCaptures(string source, string expected) => Ok(source, expected);

    [Theory]
    [InlineData("xs.count", "F(1 / 0)", "1")]
    [InlineData("xs[1]", "F(1 / 0, 20)", "20")]
    [InlineData("xs.take(1)", "F(10, 1 / 0)", "L[10]")]
    public Task AProgramRetainingInvocationPlans_ObservesTheSameSlice(string body, string call, string expected)
        => Ok("Hold(meta r) = r.Invoke()\nF(*xs) = Hold(Id(" + body + "))\nId(v) = v\n" + call, expected);

    [Fact]
    public Task ACapturedObserver_ReadsTheSliceOnEveryInvocation()
        => Ok("Twice(meta r) = r.Invoke(), r.Invoke()\nF(*xs) = Twice(count(xs))\nF(1 / 0)", "S[1, 1]");

    [Fact]
    public Task Callbacks_SeeTheOrdinaryValues()
        => Ok("F(*xs) = xs.map({ v * 2 })\nF(1, 2)", "L[2, 4]");

    private const string CapturePrelude = "Capture(meta r) = r\nFirst(*xs) = xs[0]\nCount(*xs) = xs.count\n";

    [Fact]
    public async Task ACycleThroughASelectedElement_IsTheDemandCycle_WhileCountingItsPositionIsNot()
    {
        await Fails(CapturePrelude + "R = Capture(First(R.Invoke()))\nR.Invoke()", "DemandCycle");
        await Ok(CapturePrelude + "R = Capture(Count(R.Invoke()))\nR.Invoke()", "1");
    }

    // ── Suspension, cancellation and terminality ────────────────────────────────────────────────

    private static HostOperations Gate(TaskCompletionSource release, List<string> entered) => HostOperations.Create(
        HostOperation.CreateAsync("wait", async (args, _) =>
        {
            lock (entered) entered.Add($"wait({args[0]})");
            await release.Task.ConfigureAwait(false);
            return args[0];
        }, "x"));

    [Fact]
    public async Task ASelectedElement_SuspendsAndCompletesOnce_AnUnselectedOneIsNeverEntered()
    {
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var entered = new List<string>();
        var run = KatLangEngine.RunAsync("F(*xs) = xs[1], xs[1]\nF(wait(1), wait(2))", new RunOptions { HostOperations = Gate(release, entered) });
        while (true)
        {
            lock (entered) if (entered.Count > 0) break;
            await Task.Yield();
        }
        Assert.False(run.IsCompleted);
        release.SetResult();
        var result = Assert.IsType<RunResult.Success>(await run);
        Assert.Equal("S[2, 2]", SixRouteAgreement.Neutral(result.Value));
        Assert.Single(entered);
    }

    [Fact]
    public async Task CancellationDuringARealSuspension_NeitherRestartsNorLeaksActiveState()
    {
        using var cancellation = new CancellationTokenSource();
        var entered = new List<string>();
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var run = KatLangEngine.RunAsync("F(*xs) = xs.take(2)\nF(wait(1), wait(2))", new RunOptions
        {
            HostOperations = Gate(release, entered),
            EvaluationCancellationToken = cancellation.Token,
        });
        while (true)
        {
            lock (entered) if (entered.Count > 0) break;
            await Task.Yield();
        }
        cancellation.Cancel();
        release.SetResult();
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run);
        Assert.Single(entered);
    }

    [Theory]
    [InlineData("F(*xs) = stop() + xs.count\nF(1)")]
    [InlineData("F(*xs) = (stop(), xs[])\nF(1)")]
    [InlineData("F(*xs) = (stop(), xs.take(0))\nF(1)")]
    public void AMetadataRead_ObservesCancellation(string source)
    {
        using var cancellation = new CancellationTokenSource();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("stop", (_, _) =>
            {
                cancellation.Cancel();
                return new Result.Atom(0);
            })),
            EvaluationCancellationToken = cancellation.Token,
        };
        Assert.ThrowsAny<OperationCanceledException>(() => KatLangEngine.Run(source, options));
    }

    // ── Resource accounting ─────────────────────────────────────────────────────────────────────

    /// <summary>The smallest materialization budget under which <paramref name="source"/> completes.</summary>
    private static int SmallestMaterialization(string source)
    {
        for (var limit = 1; limit < 64; limit++)
        {
            var run = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = new EvaluationLimits { MaxMaterializedItems = limit } });
            if (run is RunResult.Success) return limit;
        }
        throw new InvalidOperationException($"no budget below 64 completes:\n{source}");
    }

    [Fact]
    public void MetadataAndPositionReads_ReserveNoWholeList_TakeReservesOnlyItsPrefix()
    {
        const string call = "F(1, 2, 3, 4, 5, 6)";
        Assert.Equal(1, SmallestMaterialization(F("xs.count", call)));
        Assert.Equal(1, SmallestMaterialization(F("xs.first", call)));
        Assert.Equal(1, SmallestMaterialization(F("xs.last", call)));
        Assert.Equal(1, SmallestMaterialization(F("xs[3]", call)));
        Assert.Equal(2, SmallestMaterialization(F("xs[1, 2]", call)));
        Assert.Equal(2, SmallestMaterialization(F("xs.take(2)", call)));
        Assert.Equal(6, SmallestMaterialization(F("xs", call)));
        Assert.Equal(6, SmallestMaterialization(F("xs.take(99)", call)));
    }

    [Fact]
    public void NoBenefitEagerInputs_KeepTheirCharges()
    {
        const string data = "Data = [1, 2, 3, 4, 5, 6]\n";
        var whole = SmallestMaterialization(data + "Data");
        Assert.Equal(whole, SmallestMaterialization(data + "Data.count"));
        Assert.Equal(whole, SmallestMaterialization(data + "Data[3]"));
        Assert.Equal(whole + 2, SmallestMaterialization(data + "Data.take(2)"));
    }

    [Fact]
    public async Task ACollectionLimit_RefusesWhatWouldBeBuilt_NotWhatIsOnlyObserved()
    {
        var limits = new EvaluationLimits { MaxCollectionItems = 2 };
        const string call = "F(1, 2, 3)";
        var count = await SixRouteAgreement.OnEveryRouteAsync(F("xs.count", call), limits: limits);
        Assert.Equal("3", count.Value);
        var taken = await SixRouteAgreement.OnEveryRouteAsync(F("xs.take(2)", call), limits: limits);
        Assert.Equal("L[1, 2]", taken.Value);
        var whole = await SixRouteAgreement.OnEveryRouteAsync(F("xs", call), limits: limits);
        Assert.Equal("err", whole.Kind);
        var refused = await SixRouteAgreement.OnEveryRouteAsync(F("xs.take(3)", call), limits: limits);
        Assert.Equal("err", refused.Kind);
    }

    [Fact]
    public async Task ReachedStepLimits_StayReached_ForAMetadataRead()
    {
        const string source = "Use(n) = n\nF(*xs) = Use(1) + Use(2) + xs.count\nF(1 / 0)";
        var open = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("4", open.Value);
        var refused = await SixRouteAgreement.OnEveryRouteAsync(source, limits: new EvaluationLimits { MaxSteps = 2 });
        Assert.Equal("err", refused.Kind);
    }

    [Fact]
    public void ABigSlice_CountsAndSelectsWithoutItsWholeList()
    {
        // The source list is charged once by `range`; the two observers add nothing for the 40 cells.
        const string spread = "F(range(1, 40)*)";
        var baseline = SmallestMaterializationLarge(F("0", spread));
        Assert.Equal(baseline, SmallestMaterializationLarge(F("xs.count", spread)));
        Assert.Equal(baseline, SmallestMaterializationLarge(F("xs[39]", spread)));
        Assert.Equal(baseline + 1, SmallestMaterializationLarge(F("xs.take(1)", spread)));
    }

    private static int SmallestMaterializationLarge(string source)
    {
        for (var limit = 1; limit < 256; limit++)
        {
            var run = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = new EvaluationLimits { MaxMaterializedItems = limit } });
            if (run is RunResult.Success) return limit;
        }
        throw new InvalidOperationException($"no budget below 256 completes:\n{source}");
    }

    [Theory]
    [InlineData("xs.count")]
    [InlineData("xs.first")]
    [InlineData("xs.last")]
    [InlineData("xs[0]")]
    [InlineData("xs[xs.count - 1]")]
    [InlineData("xs.take(1)")]
    [InlineData("xs.take(16)")]
    public void ObservationAllocation_AfterSupplyFormation_DoesNotGrowWithTheSlice(string body)
    {
        static long Measure(string observer, int size)
        {
            long started = 0, allocated = -1;
            var operations = HostOperations.Create(
                HostOperation.Create("begin", (_, _) =>
                {
                    started = GC.GetAllocatedBytesForCurrentThread();
                    return new Result.Atom(0);
                }),
                HostOperation.Create("end", (_, _) =>
                {
                    allocated = GC.GetAllocatedBytesForCurrentThread() - started;
                    return new Result.Atom(0);
                }));
            var source = $"F(*xs) = {{\nbegin()\n{observer}\nend()\n}}\nF(range(1, {size})*)";
            // Parsing, range construction, cell allocation and collector binding all precede begin.
            var result = KatLangEngine.Run(source, new RunOptions { HostOperations = operations });
            Assert.IsType<RunResult.Success>(result);
            Assert.True(allocated > 0);
            return allocated;
        }

        // Warm up both routes. Coarse bounds tolerate background-GC allocation quanta; no exact
        // allocation assertion belongs in this in-process test. A whole-VALUE control proves the
        // window includes collector materialization (at least 128 KiB of references at this width).
        _ = Measure(body, 16_384);
        _ = Measure("xs", 16_384);
        var small = Measure(body, 16);
        var large = Measure(body, 16_384);
        Assert.True(large < small + 32_768, $"{body}: small={small}, large={large}");
        var whole = Measure("xs", 16_384);
        Assert.True(whole > large + 65_536, $"{body}: selective={large}, whole={whole}");
    }
}
