using static KatLang.Tests.SixRouteAgreement;

namespace KatLang.Tests;

/// <summary>Independent A2 review: intersections of ordered patterns, lazy supply, aliases,
/// collector slices, eager result construction, dot dispatch and property reads.</summary>
public class ModelCA2IndependentReviewTests
{
    [Theory]
    [InlineData("I01-attempts-demand-order", "F(0, x, 9) = 0\nF(1, x, 8) = x\nF(a, b, c) = 99\nF(trace(1), tick(), trace(8))", "ok 1", "trace(1) | trace(8) | tick#1")]
    [InlineData("I02-conflict-then-body", "F(x, x, 0) = 7\nF(a, b, c) = b + b\nF(tick(), tick(), 1 / 0)", "ok 4", "tick#1 | tick#2")]
    [InlineData("I03-list-boundary", "F([0, x], y) = 7\nF(a, b) = 'miss'\nF([trace(1), trace(2)], 1 / 0)", "ok 'miss'", "trace(1) | trace(2)")]
    [InlineData("I04-nested-conflict", "F([x, x], z) = 7\nF(a, b) = b\nF(trace([1, 2]), trace(9))", "ok 9", "trace(L[1, 2]) | trace(9)")]
    [InlineData("I05-pattern-collector-read", "P(x, x, *r, z, z) = r\nP(trace(0), trace(0), trace(3), trace(4), trace(9), trace(9))", "ok L[3, 4]", "trace(0) | trace(0) | trace(9) | trace(9) | trace(3) | trace(4)")]
    [InlineData("I06-pattern-collector-unread", "P(x, *r, x) = 1\nP(trace(0), 1 / 0, trace(0))", "ok 1", "trace(0) | trace(0)")]
    [InlineData("I07-nested-first-failure", "P((x, x), y, y) = 0\nP((trace(1), trace(2)), trace(3), 1 / 0)", "err ArityMismatch", "trace(1) | trace(2)")]
    [InlineData("I08-collector-first-failure", "P(x, *r, x) = r\nP(trace(1), 1 / 0, trace(2))", "err ArityMismatch", "trace(1) | trace(2)")]
    [InlineData("I09-suffix-before-slice", "P(x, *r, x) = r\nP(trace(1), trace(2) / 0, trace(1))", "err DivisionByZero", "trace(1) | trace(1) | trace(2)")]
    [InlineData("I10-wrong-cardinality-spread", "F(0, x) = 7\nF(a, b) = b\nF(trace(0), [trace(2), trace(3)]*)", "err ArityMismatch", "trace(2) | trace(3)")]
    [InlineData("I11-failed-spread", "F(0, x) = 7\nF(a, b) = b\nF(trace(0), [1 / 0]*)", "err DivisionByZero", "")]
    [InlineData("I12-empty-structural", "F([], x) = 7\nF([a, b], x) = a\nF([], 1 / 0)", "ok 7", "")]
    [InlineData("I13-outputless-inspection", "F(0, x) = 7\nF(a, b) = b\nF({}, trace(2))", "err MissingOutput", "")]
    [InlineData("I14-catchall-outputless", "F(x, 0) = 7\nF(a, b) = b\nF({}, trace(0))", "ok 7", "trace(0)")]
    [InlineData("I15-alias-independent", "P(x, x) = x\nA = P\nA(tick(), tick())", "err ArityMismatch", "tick#1 | tick#2")]
    [InlineData("I16-forwarding-one-cell", "P(x, x) = x\nA = P\nThrough(x) = A(x, x)\nThrough(tick())", "ok 1", "tick#1")]
    [InlineData("I17-richest-representation", "A = 1.50\nP(x, x) = x.string, x().string\nP(1.5, A), P(A, 1.5)", "ok S[S['1.50', '1.50'], S['1.50', '1.50']]", "")]
    [InlineData("I18-family-first-representation", "F(x, x, 0) = x.string\nF(a, b, c) = 'miss'\nF(1.50, 1.5, 0), F(1.5, 1.50, 0)", "ok S['1.50', '1.5']", "")]
    [InlineData("I19-family-callable-conflict", "A = 5\nB = 5\nF(x, x, 0) = 7\nF(a, b, c) = 9\nF(A, B, 1 / 0)", "ok 9", "")]
    [InlineData("I20-dot-known-slice", "Third(a, b, c) = c\nThrough(*xs) = xs*.Third(trace(9))\nThrough(1 / 0, 2 / 0)", "ok 9", "trace(9)")]
    [InlineData("I21-dot-family-receiver", "F(x, 0) = 7\nF(a, b) = b\n(1 / 0).F(trace(0))", "ok 7", "trace(0)")]
    [InlineData("I22-dot-family-repeat", "F(x, x) = 7\nF(a, b) = b\ntick().F(tick())", "ok 2", "tick#1 | tick#2")]
    [InlineData("I23-string-member", "Box = { public string(x) = x }\nBox.string(trace(7))", "ok 7", "trace(7)")]
    [InlineData("I24-string-spread-failure", "trace(5).string([1 / 0]*)", "err DivisionByZero", "")]
    [InlineData("I25-string-empty-then-cached", "A = tick()\nA.string(trace(())*), A", "ok S['1', 1]", "trace(S[]) | tick#1")]
    [InlineData("I26-empty-projection-wrapper", "F(f, 0) = reduce([], f, 7)\nF(f, n) = n\nF(tick(), 0)", "ok 7", "")]
    [InlineData("I27-one-item-reduce", "Through(f) = reduce([1], f, 7)\nThrough(tick())", "err NotAnAlgorithm", "")]
    // HO-03 (Q-25, Option B): the family callback's two rows are its ordinary call result, one sequence value.
    [InlineData("I28-family-callback-row-boundary", "F(0) = 1, 2\nF(x) = x, x\nmap([0], F)", "ok L[S[1, 2]]", "")]
    [InlineData("I29-property-invoke-read", "A = tick()\nUse(f) = f() + f + f() + f\nUse(A), A", "ok S[8, 2]", "tick#1 | tick#2 | tick#3")]
    [InlineData("I30-deconstruction-unused", "p, q = tick(), 7\nUse(f) = map([], f)\nUse(p), q, p", "ok S[L[], 7, 1]", "tick#1")]
    [InlineData("I31-ordinary-value-failure", "pow('a', 1 / 0)", "err TypeMismatch", "")]
    [InlineData("I34-undemanded-native", "Through(f) = map([], f)\nThrough(pow('a', 1 / 0))", "ok L[]", "")]
    public async Task SemanticIntersections_KeepDemandAndIdentitySeparate(
        string id, string source, string expected, string hostCalls)
    {
        var observed = await OnEveryRouteAsync(source);
        Assert.True(observed.Kind == expected.Split(' ')[0], $"{id}: {observed}");
        if (observed.Kind == "ok") Assert.Equal(expected[3..], observed.Value);
        else Assert.StartsWith(expected[4..] + ":", Assert.Single(observed.Errors), StringComparison.Ordinal);
        Assert.Equal(hostCalls.Length == 0 ? [] : hostCalls.Split(" | "), observed.HostCalls);
    }
}
