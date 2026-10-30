namespace KatLang.Tests;

/// <summary>
/// NEED-04, GROUP-AWARE (ALIAS-UNIFY-1, October 2026; Lean <c>NeedBinder.bindName</c>, C#
/// <c>Evaluator.BindAcceptedNeedPatterns</c>). At EVERY occurrence of a repeated parameter name the
/// binder projects the occurrence's CALLABLE first. A callable-bearing contribution is compared by
/// its structural identity with the group's first one and its VALUE is demanded only once the group
/// has a value-only contribution; a value-only contribution demands its own counted VALUE, the first
/// one anchoring the group and then checking every earlier pending callable contribution's own
/// counted VALUE in occurrence order. The binding is the first callable-bearing original cell, else
/// the first value-only one. So repeated REFERENCES match by identity without executing their
/// outputs, while a value-only contribution still constrains every contribution's own value.
/// <para>Every case runs on the six routes of <see cref="SixRouteAgreement"/>, which must agree on
/// the outcome, every error's code, message and position, and the exact host-call log — the
/// evaluation schedule.</para>
/// </summary>
public class GroupAwareRepeatedNameTests
{
    private static async Task<SixRouteAgreement.Observation> RunAsync(string source)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.NotEqual("parse", observation.Kind);
        return observation;
    }

    private static void AssertValue(SixRouteAgreement.Observation observation, string value, params string[] hostCalls)
    {
        Assert.True(observation.Kind == "ok", observation.ToString());
        Assert.Equal(value, observation.Value);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    private static void AssertError(SixRouteAgreement.Observation observation, string code, params string[] hostCalls)
    {
        Assert.True(observation.Kind == "err", observation.ToString());
        Assert.StartsWith(code + ":", observation.Errors[0]);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    private const string RepeatedValueMessage = "repeated parameter 'x' requires equal arguments";
    private const string IdentityMessage = "Repeated bind equality requires the same callable identity";

    // ── R5: the core outcomes ─────────────────────────────────────────────────────────

    [Fact]
    public async Task EqualValueOnlyArguments_Bind()
        => AssertValue(await RunAsync("Same(x, x) = 0\nSame(7, 7)"), "0");

    [Fact]
    public async Task UnequalValueOnlyArguments_AreTheRepeatedValueIncompatibility()
    {
        var observation = await RunAsync("Same(x, x) = 0\nSame(7, 8)");
        AssertError(observation, "ArityMismatch");
        Assert.Contains(RepeatedValueMessage, observation.Errors[0]);
    }

    [Theory]
    [InlineData("Same(A, 7)")]
    [InlineData("Same(7, A)")]
    public async Task ANumericPropertyAndAnEqualNumber_Bind(string call)
        => AssertValue(await RunAsync("A = 7\nSame(x, x) = 0\n" + call), "0");

    [Fact]
    public async Task TwoPropertiesWithEqualValues_AreDifferentIdentities()
    {
        var observation = await RunAsync("A = 7\nD = 7\nSame(x, x) = 0\nSame(A, D)");
        AssertError(observation, "TypeMismatch");
        Assert.Contains(IdentityMessage, observation.Errors[0]);
    }

    [Fact]
    public async Task CallResults_AreValueOnlyContributions()
        => AssertValue(await RunAsync("A = 7\nD = 7\nSame(x, x) = 0\nSame(A(), D())"), "0");

    [Fact]
    public async Task OneFailingReferenceTwice_MatchesWithoutDemandingItsOutput()
        => AssertValue(await RunAsync("Bad = trace(1) / 0\nSame(x, x) = 0\nSame(Bad, Bad)"), "0");

    [Fact]
    public async Task FailingCallResults_AreDemanded()
        => AssertError(await RunAsync("Bad = trace(1) / 0\nSame(x, x) = 0\nSame(Bad(), Bad())"), "DivisionByZero", "trace(1)");

    [Theory]
    [InlineData("Same(Bad, 7)")]
    [InlineData("Same(7, Bad)")]
    public async Task AValueOnlyContribution_DemandsTheReferencesOwnValue(string call)
        => AssertError(await RunAsync("Bad = trace(1) / 0\nSame(x, x) = 0\n" + call), "DivisionByZero", "trace(1)");

    [Fact]
    public async Task AMatchedReference_IsDemandedOnlyByItsLaterValueRead()
        // The repeated reference matches by identity; the body's own VALUE read then demands it.
        => AssertError(await RunAsync("Bad = trace(1) / 0\nUse(f, f) = f + 1\nUse(Bad, Bad)"), "DivisionByZero", "trace(1)");

    [Fact]
    public async Task AMatchedReference_KeepsItsCallable()
        => AssertValue(await RunAsync("Inc(y) = y + 1\nApplySame(f, f) = f(1)\nApplySame(Inc, Inc)"), "2");

    [Theory]
    // A transparent reference IS its target's identity (M4★), so the repeated reference matches
    // without demanding the failing output.
    [InlineData("Same(Alias, Bad)")]
    [InlineData("Same(Bad, Alias)")]
    public async Task AReferenceAndItsTarget_AreOneIdentity(string call)
        => AssertValue(await RunAsync("Bad = trace(1) / 0\nAlias = Bad\nSame(x, x) = 0\n" + call), "0");

    [Theory]
    // A braced carrier is a structure of its own (M4★): it never matches its forwarding target.
    [InlineData("Same(C, A)")]
    [InlineData("Same(A, C)")]
    public async Task ACarrierAndItsTarget_AreDifferentIdentities(string call)
    {
        var observation = await RunAsync("A = 7\nC = { A }\nSame(x, x) = 0\n" + call);
        AssertError(observation, "TypeMismatch");
        Assert.Contains(IdentityMessage, observation.Errors[0]);
    }

    [Fact]
    public async Task AWholeHolderMatched_FailsOnlyAtTheBodysLaterValueRead()
    {
        // R1's holder: matching B against B succeeds by identity; the body's own VALUE read of B is the
        // forwarded F's zero-supply arity rejection.
        var observation = await RunAsync("B = {\n    public F(x) = x * x\n    public Q = 99\n    F\n}\nUse(f, f) = f + 1\nUse(B, B)");
        AssertError(observation, "ArityMismatch");
    }

    [Theory]
    // One declaration in two activations is two identities; in one activation, one.
    [InlineData("if(k == 0, Same(g, G), F(k - 1, G))", "err")]
    [InlineData("if(k == 0, Same(G, G), F(k - 1, G))", "ok")]
    public async Task OneDeclarationInDifferentActivations_IsTwoIdentities(string row, string kind)
    {
        var observation = await RunAsync($"Same(x, x) = 0\nF(k, g) = {{\n    G(y) = y + k\n    {row}\n}}\nF(1, 0)");
        Assert.True(observation.Kind == kind, observation.ToString());
        if (kind == "err")
        {
            Assert.StartsWith("TypeMismatch:", observation.Errors[0]);
            Assert.Contains(IdentityMessage, observation.Errors[0]);
        }
        else
        {
            Assert.Equal("0", observation.Value);
        }
    }

    [Fact]
    public async Task DifferentIdentities_AreRejectedBeforeAnyValueDemand()
    {
        var observation = await RunAsync("Bad = trace(1) / 0\nMissing = [trace(2)][5]\nSame(x, x) = 0\nSame(Bad, Missing)");
        AssertError(observation, "TypeMismatch");
        Assert.Contains(IdentityMessage, observation.Errors[0]);
    }

    // ── R6: same identity, different completed VALUEs (Q-37 re-entrant reads) ──────────

    // Inside A's owning evaluation every read of A is RE-ENTRANT (Q-37): it evaluates afresh, so the
    // two cells p and q carry the SAME callable identity A but the completed values 3 and 5. A
    // value-only contribution 3 must check BOTH callable contributions' own values: a binder that only
    // compared the anchor with one retained representative would accept `Agree(p, q, p + 0)` and
    // reject the swapped order. Every one of the six orders rejects.
    [Theory]
    [InlineData("Agree(p, q, p + 0)")]
    [InlineData("Agree(q, p, p + 0)")]
    [InlineData("Agree(p, p + 0, q)")]
    [InlineData("Agree(q, p + 0, p)")]
    [InlineData("Agree(p + 0, p, q)")]
    [InlineData("Agree(p + 0, q, p)")]
    public async Task SameIdentityWithDifferentValues_NeverAgreesWithAValueAnchor(string agree)
    {
        var source = $"""
            Agree(x, x, x) = 0
            Probe(p, q) = p + 0, q + 0, {agree}
            A = if(tick() == 1, Probe(A, A), tick())
            A
            """;
        var observation = await RunAsync(source);
        AssertError(observation, "ArityMismatch", "tick#1", "tick#2", "tick#3", "tick#4", "tick#5");
        Assert.Contains(RepeatedValueMessage, observation.Errors[0]);
    }

    // The research's own host-fixture witness and its swapped variant, run in production: its premise —
    // two independent `tick` cells completing with DIFFERENT values — does not hold, because a bare
    // `tick` is a zero-argument read of the host operation's prelude property, cached per run (the
    // ordinary `A` vs `A()` rule; explicit `tick()` calls stay fresh). Both cells complete with 1, so the
    // value-only 1 agrees with each in either order. The policy is unchanged: the same-identity /
    // different-VALUE case is pinned above with Q-37 re-entrant reads, which do differ.
    [Theory]
    [InlineData("Agree(p, q, 1)")]
    [InlineData("Agree(q, p, 1)")]
    public async Task TheHostFixtureWitness_ReadsOneCachedHostValue_SoTheMixedAgreementHolds(string agree)
        => AssertValue(await RunAsync($"Agree(x, x, x) = 0\nProbe(p, q) = p + 0, q + 0, {agree}\nProbe(tick, tick)"), "S[1, 1, 0]", "tick#1");

    [Fact]
    public async Task SameIdentityWithDifferentValues_MatchesByIdentityAlone_AndKeepsTheFirstCell()
    {
        // Without a value-only contribution the group matches by identity: the binding is the FIRST
        // original cell, whose own completed VALUE (3) the body reads.
        var source = """
            Pick(x, x) = x
            Probe(p, q) = p + 0, q + 0, Pick(p, q), Pick(q, p)
            A = if(tick() == 1, Probe(A, A), tick())
            A
            """;
        AssertValue(await RunAsync(source), "S[3, 5, 3, 5]", "tick#1", "tick#2", "tick#3", "tick#4", "tick#5");
    }

    // ── R7: the mixed-demand schedule ─────────────────────────────────────────────────

    [Fact]
    public async Task TheValueAnchor_IsDemandedBeforeThePendingReference()
        => AssertValue(await RunAsync("A = trace(10) - 3\nSame(x, x) = 0\nSame(A, trace(7))"), "0", "trace(7)", "trace(10)");

    [Fact]
    public async Task PendingReferences_AreCheckedInOccurrenceOrder()
        => AssertValue(
            await RunAsync("A = trace(10) - 3\nSame3(x, x, x) = 0\nSame3(A, A, trace(7))"),
            "0", "trace(7)", "trace(10)");

    [Fact]
    public async Task ALaterIdentityConflict_FollowsTheAnchorCheck()
    {
        var observation = await RunAsync("A = trace(10) - 3\nD = 7\nSame3(x, x, x) = 0\nSame3(A, trace(7), D)");
        AssertError(observation, "TypeMismatch", "trace(7)", "trace(10)");
    }

    [Fact]
    public async Task InterleavedRepeatedNames_KeepTheirOwnGroups()
        => AssertValue(
            await RunAsync("A = trace(10) - 3\nB = trace(20) - 12\nTwo(x, y, x, y) = 0\nTwo(A, B, trace(7), trace(8))"),
            "0", "trace(7)", "trace(10)", "trace(8)", "trace(20)");

    [Fact]
    public async Task AnInterveningLiteral_RunsWhileTheReferenceStillWaits()
        => AssertValue(
            await RunAsync("A = trace(10) - 3\nLit(x, 0, x) = 1\nLit(A, trace(0), trace(7))"),
            "1", "trace(0)", "trace(7)", "trace(10)");

    [Fact]
    public async Task ANonMatchingLiteral_EndsTheAttemptBeforeTheWaitingReferenceIsDemanded()
    {
        var observation = await RunAsync("A = trace(10) - 3\nLit(x, 0, x) = 1\nLit(A, trace(1), trace(7))");
        AssertError(observation, "NoMatchingBranch", "trace(1)");
    }

    [Fact]
    public async Task TheFirstValueDisagreement_StopsTheBinding()
        => AssertError(
            await RunAsync("Same3(x, x, x) = 0\nSame3(trace(1), trace(2), trace(3))"),
            "ArityMismatch", "trace(1)", "trace(2)");

    // ── R8: nested patterns, families and representatives ───────────────────────────

    [Theory]
    [InlineData("Cross(A, (7, 9))", "9")]
    [InlineData("Cross((7, 9)[0], (7, 9))", "9")]
    public async Task AReferenceAndAnOpenedReadyChild_FormAMixedGroup(string call, string value)
        => AssertValue(await RunAsync("A = 7\nCross(x, (x, y)) = y\n" + call), value);

    [Fact]
    public async Task AReferenceAndAnUnequalOpenedChild_Disagree()
        => AssertError(await RunAsync("A = 7\nCross(x, (x, y)) = y\nCross(A, (8, 9))"), "ArityMismatch");

    [Theory]
    [InlineData("F(Bad, Bad)", "1")]
    [InlineData("F(A, D)", "2")]
    public async Task AFamilyAttempt_MatchesOrFallsThroughOnIdentity(string call, string value)
        => AssertValue(await RunAsync("Bad = trace(1) / 0\nA = 7\nD = 7\nF(x, x) = 1\nF(x, y) = 2\n" + call), value);

    [Fact]
    public async Task AFamilyAttempt_PropagatesAnExecutedValueFailure()
        // The value anchor demands the waiting reference's VALUE; its failure is the dispatch's
        // failure, never a non-match that would let the second clause run.
        => AssertError(await RunAsync("Bad = trace(1) / 0\nF(x, x) = 1\nF(x, y) = 2\nF(Bad, 7)"), "DivisionByZero", "trace(1)");

    [Fact]
    public async Task TheRepresentative_IsTheFirstCallableContribution()
        // `A`'s own cell (its representation 1.50) outranks the value-only 1.5 in either order.
        => AssertValue(await RunAsync("A = 1.50\nP(x, x) = x.string\nP(1.5, A), P(A, 1.5)"), "S['1.50', '1.50']");

    [Theory]
    [InlineData("W = 1, 2\nSame(x, x) = 0\nSame(W, (1, 2))")]
    [InlineData("Same(x, x) = 0\nSame({ 1, 2 }, (1, 2))")]
    [InlineData("E = ()\nSame(x, x) = 0\nSame(E, ())")]
    public async Task CountsAreNormalizedAtValueBoundaries_SoEqualValuesAgree(string source)
        // The comparison is of COUNTED values (value AND emitted count), but every source-level
        // contribution reaches the binder through a value boundary (`Result.valueCount`), so a
        // two-row property, a block and a capture of the same items agree. Unequal counts with equal
        // values exist only for hand-built cells: the Lean binder guards pin that case on the
        // production binder (`BinderGuards.differentCounts`, `RepeatedNameGuards`).
        => AssertValue(await RunAsync(source), "0");
}
