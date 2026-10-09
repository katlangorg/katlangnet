using static KatLang.Tests.SixRouteAgreement;

namespace KatLang.Tests;

/// <summary>
/// Model C (NEED-01..10) at the boundaries the Constitution's Phase A2 reconciliation (2026-10-09)
/// found stated wrongly and pinned nowhere else: every argument a call supplies — a dot-call
/// receiver included — is a suspended computation that runs only on its first VALUE demand, in the
/// callee's own demand order; a clause family demands only what its patterns inspect and its
/// binders keep the argument's callable identity; two written cells are two computations while one
/// transported cell is one; a deconstruction right-hand side runs when a target is first demanded;
/// and a forwarded callback is projected only when it is invoked. Each program runs on the six
/// routes, which must agree exactly (value, every error's code, message and span, host-call log);
/// the expected outcome and host log are written by hand from the adopted laws.
/// </summary>
public class ModelCPropagationTests
{
    // ── DOT-03 / DOT-08: the dot-call receiver is an ordinary supplied computation ──────────────

    [Theory]
    // The extension call's receiver is the first argument cell: demanded by the callee, never first.
    [InlineData("Second(a, b) = b\ntrace(1).Second(trace(2))", "ok 2", "trace(2)")]
    [InlineData("Second(a, b) = b\nSecond(trace(1), trace(2))", "ok 2", "trace(2)")]
    [InlineData("Flip(a, b) = b + a\ntrace(1).Flip(trace(2))", "ok 3", "trace(2) | trace(1)")]
    [InlineData("Flip(a, b) = b + a\nFlip(trace(1), trace(2))", "ok 3", "trace(2) | trace(1)")]
    // Demanded at most once, however often the callee reads it.
    [InlineData("Twice(a, b) = a + a + b\ntick().Twice(10)", "ok 12", "tick#1")]
    // Cardinality is checked before any demand, the receiver's included.
    [InlineData("Second(a, b) = b\ntrace(1).Second(trace(2), trace(3))", "err ArityMismatch", "")]
    // A spread receiver is an explicit spread: opened while the supply is formed.
    [InlineData("Third(a, b, c) = c\ntrace((1, 2))*.Third(trace(3))", "ok 3", "trace(S[1, 2]) | trace(3)")]
    // An unused property receiver performs no access: the root read is the property's first.
    [InlineData("B = tick()\nIgn(x, y) = y\nB.Ign(5), B", "ok S[5, 1]", "tick#1")]
    public async Task DotCallReceiver_IsDemandedLikeTheWrittenLeadingArgument(string source, string outcome, string hostCalls)
        => AssertOutcome(await OnEveryRouteAsync(source), outcome, hostCalls);

    [Theory]
    // The intrinsic's argument list is a supply: a non-spread argument and the receiver never run...
    [InlineData("trace(5).string(trace(6))", "err ArityMismatch", "")]
    // ...an explicit spread is opened before the cardinality check...
    [InlineData("trace(5).string([trace(6)]*)", "err ArityMismatch", "trace(6)")]
    // ...and a zero-item spread leaves the intrinsic, whose receiver is demanded after formation.
    [InlineData("trace(5).string(trace(())*)", "ok '5'", "trace(S[]) | trace(5)")]
    public async Task StringIntrinsicArguments_AreFormedAndRejectedBeforeAnyDemand(string source, string outcome, string hostCalls)
        => AssertOutcome(await OnEveryRouteAsync(source), outcome, hostCalls);

    // ── PAT-07: a family demands what its patterns inspect; its binders keep both channels ──────

    [Theory]
    // A binder retains the argument's callable identity (NEED-04; Q-21): the family receives a callable.
    [InlineData("Inc(x) = x + 1\nApp(f, 0) = 0\nApp(f, n) = f(n)\nR(z) = App(Inc, 5)\nR(0)", "ok 6", "")]
    [InlineData("Inc(x) = x + 10\nF(f, 0) = f(2)\nF(f, n) = n\nR(z) = F(Inc, 0)\nR(0)", "ok 12", "")]
    // A binder bound to a value shadows an outer callable of its name and is not callable.
    [InlineData("f(x) = x + 1\nF(f, 0) = f(2)\nF(f, n) = n\nF(7, 0)", "err NotAnAlgorithm", "")]
    // A binder demands nothing: an output-less block the selected clause never reads is no error.
    [InlineData("F(x, 0) = 1\nF(x, y) = 2\nF({ }, 0)", "ok 1", "")]
    [InlineData("F(0, y) = 'zero'\nF(x, y) = y\nF(trace(0), trace(1) / 0)", "ok 'zero'", "trace(0)")]
    public async Task ClauseFamily_DemandsOnlyWhatItsPatternsInspect_AndItsBindersKeepTheCallable(
        string source, string outcome, string hostCalls)
        => AssertOutcome(await OnEveryRouteAsync(source), outcome, hostCalls);

    // ── PAT-09: two written cells are two computations; one transported cell is one ─────────────

    [Theory]
    // Two cells naming one property: each demands it through the property cache — one tick.
    [InlineData("T = tick()\nQ(x, x) = x\nQ(T, T), T", "ok S[1, 1]", "tick#1")]
    // Two independent computations: two executions, and their values differ.
    [InlineData("Q(x, x) = x\nQ(tick(), tick())", "err ArityMismatch", "tick#1 | tick#2")]
    // One cell transported to both occurrences: one execution (NEED-04).
    [InlineData("Q(x, x) = x\nPass(g) = Q(g, g)\nPass(tick())", "ok 1", "tick#1")]
    // The first occurrence's failure ends the call before the second cell is demanded.
    [InlineData("Bad = trace(1) / 0\nQ(x, x) = x\nQ(Bad, Bad)", "err DivisionByZero", "trace(1)")]
    public async Task RepeatedName_DemandsEachOccurrencesOwnCell(string source, string outcome, string hostCalls)
        => AssertOutcome(await OnEveryRouteAsync(source), outcome, hostCalls);

    // ── VAR-06: the right-hand side runs on the first demand of a target ─────────────────────────

    [Theory]
    // Passing a target is no demand; q's first demand runs the right-hand side once.
    [InlineData("p, q = trace(1), trace(2)\nI(f) = 0\nI(p), q, p", "ok S[0, 2, 1]", "trace(1) | trace(2)")]
    [InlineData("p, q = trace(1) / 0, 2\nI(f) = 0\nI(p), I(q), I(p)", "ok S[0, 0, 0]", "")]
    // A demanded failing right-hand side fails at its first demand, and the run ends there.
    [InlineData("p, q = trace(1) / 0, 2\nI(f) = 0\nI(p), q, p", "err DivisionByZero", "trace(1)")]
    // One successful evaluation per activation; every target is a projection of it.
    [InlineData("p, q = tick(), 5\np, q, p, p + q", "ok S[1, 5, 1, 6]", "tick#1")]
    public async Task Deconstruction_RunsItsRightHandSideOnTheFirstTargetDemand(string source, string outcome, string hostCalls)
        => AssertOutcome(await OnEveryRouteAsync(source), outcome, hostCalls);

    // ── HO-04 / PROP-05: projection only at invocation; passing is not an access ─────────────────

    [Theory]
    // An empty collection never invokes, so the forwarded callback is never projected or demanded.
    [InlineData("Through(xs, f) = map(xs, f)\nThrough([], tick())", "ok L[]", "")]
    // Projecting a cell that has no callable identity demands no VALUE: the tick never runs.
    [InlineData("Through(xs, f) = map(xs, f)\nThrough([1], tick())", "err NotAnAlgorithm", "")]
    // The collection is demanded first; the callback is projected at its first invocation.
    [InlineData("map([trace(1), 2], 5)", "err NotAnAlgorithm", "trace(1)")]
    // Invoking is fresh and passing reads nothing; A's first property read is Apply's demand.
    [InlineData("A = tick()\nCall0(f) = f()\nApply(f) = f + 1\nCall0(A), Call0(A), Apply(A), A", "ok S[1, 2, 4, 3]",
        "tick#1 | tick#2 | tick#3")]
    public async Task CallbackAndInvokedArguments_AreProjectedOnlyWhenInvoked(string source, string outcome, string hostCalls)
        => AssertOutcome(await OnEveryRouteAsync(source), outcome, hostCalls);

    private static void AssertOutcome(Observation observation, string outcome, string hostCalls)
    {
        string[] expectedCalls = hostCalls.Length == 0 ? [] : hostCalls.Split(" | ");
        if (outcome.StartsWith("ok ", StringComparison.Ordinal))
        {
            Assert.True(observation.Kind == "ok", $"expected {outcome}, got {observation}");
            Assert.Equal(outcome["ok ".Length..], observation.Value);
        }
        else
        {
            var code = outcome["err ".Length..];
            Assert.True(observation.Kind == "err", $"expected {outcome}, got {observation}");
            Assert.StartsWith(code + ":", Assert.Single(observation.Errors), StringComparison.Ordinal);
        }

        Assert.Equal(expectedCalls, observation.HostCalls);
    }
}
