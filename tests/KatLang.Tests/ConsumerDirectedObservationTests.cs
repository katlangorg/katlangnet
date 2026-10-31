namespace KatLang.Tests;

/// <summary>
/// CDO-1 — consumer-directed observation (owner-approved 2026-10-31;
/// <c>docs/design/language-rules/ownership-and-lookup.md</c> § Consumer-directed observation).
/// A written name resolves ONE binding without evaluating it; the immediate consumer decides
/// whether the binding is transported, its CALLABLE projected, its VALUE demanded, or the
/// algorithm explicitly invoked. These witnesses make the routes observable through the run's
/// native <c>tick()</c> counter and the harness's <c>trace</c> host log rather than through a
/// common final number, on all six routes (<see cref="SixRouteAgreement"/>). Expectations are
/// handwritten from CDO-R1..R8 and the laws they consolidate (Model-C NEED-06, Q-03/Q-06,
/// M4★ OD-E, FWD-02, CACHE-PUB-1); the detailed contracts keep their own suites
/// (<see cref="TickBuiltinTests"/>, <see cref="ResultValueBoundaryTests"/>,
/// <see cref="WholeAlgorithmTransportTests"/>, <see cref="AliasAndBareForwardingTests"/>).
/// Repeated-name matching (NEED-04) is deliberately not exercised here.
/// </summary>
public class ConsumerDirectedObservationTests
{
    [Theory]
    // CDO-R3/R4/R8: the bare read publishes F's entry; `F()` is fresh and never replaces it;
    // arithmetic and value comparison read the same established entry.
    [InlineData("F = tick()\nF, F(), F + 0, F == 1, F", "S[1, 2, 1, true, 1]")]
    // CDO-R5: a collecting-only callable accepts the empty supply, so its bare read is the
    // cached zero-supply demand, while every explicit call — `Only()` included — is fresh.
    [InlineData("Only(*xs) = tick()\nOnly, Only(), Only, Only(9)", "S[1, 2, 1, 3]")]
    [InlineData("Only(*xs) = xs.count\nOnly, Only(), Only(1, 2)", "S[0, 0, 2]")]
    // CDO-R6: transport does not force VALUE — an unused parameter never evaluates its supply.
    [InlineData("Bad = tick() / 0\nIgnore(f) = 0\nIgnore(Bad), tick()", "S[0, 1]")]
    // CDO-R2/R6: CALLABLE projection does not demand the projected computation's VALUE, and each
    // invocation through it is fresh (1 + 2 * 10, then the counter's third tick).
    [InlineData("Z = tick()\nCallTwice(f) = f() + f() * 10\nCallTwice(Z), tick()", "S[21, 3]")]
    // CDO-R4/R8: a fresh call through a projected callable never replaces an established entry.
    [InlineData("Z = tick()\nApply0(f) = f()\nZ, Apply0(Z), Z", "S[1, 2, 1]")]
    // CDO-R6: a written reference keeps CALLABLE through transport, forwarding and a member path.
    [InlineData("Square(x) = x * x\nApply(f) = f(3)\nApply(Square)", "9")]
    [InlineData("Square(x) = x * x\nApply(f) = f(3)\nFwd(g) = Apply(g)\nFwd(Square)", "9")]
    [InlineData("Lib = {\n    public Sq(x) = x * x\n    0\n}\nApply(f) = f(3)\nApply(Lib.Sq)", "9")]
    // A zero-parameter property supplied by name is still a callable reference: invoked with no
    // supply it is its ordinary zero-supply call.
    [InlineData("Seven = 7\nApply0(f) = f()\nApply0(Seven)", "7")]
    // CDO-R7: transparent reference, structural carrier, formula. `A()` is the TARGET's fresh call
    // and establishes the target's empty entry (OD-E, CACHE-PUB-1); `B()` forwards freshly; the
    // formula `C` reads F's established entry.
    [InlineData("F = tick()\nA = F\nB = { F }\nC = F + 0\nA(), B(), C(), F", "S[1, 2, 1, 1]")]
    // CDO-R7: closed bare forwarding is by existing binding NAME; an explicit call maps written
    // arguments positionally.
    [InlineData("F(p) = p * 10\nD(p) = F\nE(q) = F(q)\nD(2), E(3)", "S[20, 30]")]
    [InlineData("Sub(y, x) = y - x\nG(x, y) = Sub\nH(x, y) = Sub(x, y)\nG(10, 3), H(10, 3)", "S[-7, 7]")]
    // CDO-R7/R8: a transparent reference's members are its target's; a carrier keeps its own
    // members and forwards invocation to its target.
    [InlineData("Lib = {\n    public Q = 3\n    0\n}\nA = Lib\nA.Q", "3")]
    [InlineData("F(x) = x + 1\nB = {\n    public M = 5\n    F\n}\nB.M, B(1)", "S[5, 2]")]
    public async Task EachConsumerObservesItsOwnRoute(string source, string expected)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(outcome.Kind == "ok", $"{outcome}\nsource:\n{source}");
        Assert.Equal(expected, outcome.Value);
    }

    [Theory]
    // CDO-R3: a VALUE consumer demands the transported supply, which fails with its own kind.
    [InlineData("Bad = trace(1) / 0\nRead(f) = f + 1\nRead(Bad)", "err", "DivisionByZero", new[] { "trace(1)" })]
    // CDO-R4: `Square()` is an explicit zero-supply invocation — an ordinary arity failure, never a
    // bare read and never a partial application.
    [InlineData("Square(x) = x * x\nRead(f) = f + 1\nRead(Square())", "err", "ArityMismatch", new string[0])]
    // CDO-R2/R6: a call result is data: it has no CALLABLE, and the invoking consumer's absence
    // report demands nothing (the supplied call never runs).
    [InlineData("Square(x) = x * x\nApply(f) = f(3)\nApply(Square(trace(2)))", "err", "NotAnAlgorithm", new string[0])]
    // The same absence wins even when VALUE would fail the supplied call's own arity.
    [InlineData("Square(x) = x * x\nApply(f) = f(3)\nApply(Square())", "err", "NotAnAlgorithm", new string[0])]
    // A literal or capture has no callable identity; a written zero-parameter reference does, so
    // supplying it an item is its own arity failure instead.
    [InlineData("Apply0(f) = f()\nApply0(7)", "err", "NotAnAlgorithm", new string[0])]
    [InlineData("Seven = 7\nApply0(f) = f()\nApply0((Seven, Seven))", "err", "NotAnAlgorithm", new string[0])]
    [InlineData("Seven = 7\nApply1(f) = f(1)\nApply1(Seven)", "err", "ArityMismatch", new string[0])]
    // CDO-R5: a callable whose ordinary binder needs a supplied value rejects the bare demand.
    [InlineData("Head(x, *rest) = x\nHead", "err", "ArityMismatch", new string[0])]
    // CDO-R7: bare forwarding never renames a binding.
    [InlineData("F(p) = p * 10\nD(q) = F\nD(2)", "parse", "UnforwardableParameter", new string[0])]
    public async Task EachRejectionKeepsItsConsumersContract(string source, string kind, string code, string[] hostCalls)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(outcome.Kind == kind, $"{outcome}\nsource:\n{source}");
        Assert.StartsWith(code + ": ", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Equal(hostCalls, outcome.HostCalls.ToArray());
    }
}
