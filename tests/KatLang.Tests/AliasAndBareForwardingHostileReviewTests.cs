namespace KatLang.Tests;

/// <summary>
/// The hostile review of aliases and bare forwarding (FWD-02, decided September 29–30 2026). Each
/// row attacks one of the three laws — an exact alias has its target's callable contract; bare
/// forwarding hands its callee the EXISTING bindings of the callee's own parameter names, never
/// renamed, reshaped, positional or added; a written call infers only the names written in it —
/// with a combination the main suite (<see cref="AliasAndBareForwardingTests"/>)
/// does not generate: a property or an enclosing parameter sharing an inherited name, a callee whose
/// signature came from Grace or a dot edge, an alias inside a structural member, redundant
/// grouping, repeated or binderless clause heads, callbacks and dot calls, host effects and the
/// zero-argument cache. Every row runs on every execution route
/// (<see cref="RepeatedNameConstraintTests.OnEveryRouteAsync"/>: sync and async engines, the async
/// engine with a suspending host operation, the generic and optimized evaluators, and the forced
/// async twin), which must agree on the outcome, the location and the host-call log.
/// The rows under "Boundaries" pin a documented limit of the rule rather than attack it.
/// </summary>
public class AliasAndBareForwardingHostileReviewTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void HostBuiltBareForwarding_ComparesStructureRatherThanDisplay(bool binderless, bool reverse)
    {
        ParameterPattern[] items = binderless ? [] : [new CaptureParameterPattern("x"), new CaptureParameterPattern("y")];
        ParameterPattern flat = new ListValueParameterPattern(items);
        ParameterPattern nested = new ListValueParameterPattern([new UnpackingParameterPattern(items)]);
        // The unpacking receiver has no written delimiter. These displays coincide, but one
        // contract opens a nested value and the other binds the outer list's items directly.
        Assert.Equal(flat.DisplayName, nested.DisplayName);
        var target = reverse ? flat : nested;
        var source = reverse ? nested : flat;
        var callee = new Algorithm.User(null, [target], [], [], [new Expr.Num(1)]) { HasExplicitParameterList = true };
        var caller = new Algorithm.User(null, [source], [], [], [new Expr.Resolve("F")]) { HasExplicitParameterList = true };
        var root = new Algorithm.User(null, [], [], [new Property("F", callee), new Property("G", caller)], [new Expr.Num(0)]);
        var (detected, detectionDiagnostics) = ParameterDetector.Detect(root);
        Assert.Empty(detectionDiagnostics);
        var diagnostics = new DiagnosticBag();
        var resolved = Assert.IsType<Algorithm.User>(ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics));
        Assert.Equal(DiagnosticCode.UnforwardableParameter, Assert.Single(diagnostics).Code);
        var body = Assert.IsType<Algorithm.User>(resolved.Properties.Single(property => property.Name == "G").Value);
        Assert.IsType<Expr.Resolve>(Assert.Single(body.Output));
    }

    [Fact]
    public void HostBuiltBareForwarding_ReportsDifferentContractsWithTheSameDisplaySeparately()
    {
        ParameterPattern flat = new ListValueParameterPattern([]);
        ParameterPattern nested = new ListValueParameterPattern([new UnpackingParameterPattern([])]);
        var callee = new Algorithm.User(null, [flat, nested, flat], [], [], [new Expr.Num(1)]) { HasExplicitParameterList = true };
        var caller = new Algorithm.User(null, [new CaptureParameterPattern("unused")], [], [], [new Expr.Resolve("F")]) { HasExplicitParameterList = true };
        var root = new Algorithm.User(null, [], [], [new Property("F", callee), new Property("G", caller)], [new Expr.Num(0)]);
        var (detected, detectionDiagnostics) = ParameterDetector.Detect(root);
        Assert.Empty(detectionDiagnostics);
        var diagnostics = new DiagnosticBag();
        ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics);
        // Repeated occurrences of one contract report once; a different contract reports too,
        // even when its display is identical. Presentation cannot decide diagnostic identity.
        Assert.Equal(2, diagnostics.Count);
        Assert.All(diagnostics, diagnostic => Assert.Equal(DiagnosticCode.UnforwardableParameter, diagnostic.Code));
    }

    public static TheoryData<string, string, string> Programs => new()
    {
        // ── An exact alias has its target's callable contract ────────────────────────────
        // The inherited `x` is F's private binder name: the alias's own property `x` is legal, and
        // the synthesized call reads the PARAMETER, never the property of the same spelling.
        { "inherited-parameter-not-the-property", "F(x) = x + 1\nA = {\n    x = 100\n    F\n}\nA(5)", "ok 6" },
        { "alias-property-reads-its-own-name", "F(x) = x + 1\nA = {\n    x = 100\n    y = x * 2\n    F\n}\nA(5), A.y", "ok S[6, 200]" },
        // The callee's final signature order — Grace-reordered, or dot-edge inferred — is inherited.
        { "alias-keeps-a-grace-order", "F = b - ~a\nA = F\nA(10, 3), F(10, 3)", "ok S[-7, -7]" },
        { "alias-keeps-a-dot-inferred-order", "K = a.t(b)\nA = K\nA(7, { x + y }, 1), K(7, { x + y }, 1)", "ok S[8, 8]" },
        // A repeated name beside a collector survives a three-level chain, and its constraint is
        // enforced by the alias's own binder before anything is called.
        { "chain-keeps-repeated-name-and-collector", "P(x, *rest, x) = x + rest.count\nA = P\nB = A\nB(1, 2, 3, 1)", "ok 3" },
        { "chain-rejects-unequal-repeated-values", "P(x, *rest, x) = x + rest.count\nA = P\nB = A\nB(1, 2, 3, 4)", "err ArityMismatch: while evaluating call to B: Bad arity" },
        { "callee-with-its-own-open", "Lib = { public K = 10 }\nF(x) = {\n    open Lib\n    x + K\n}\nA = F\nA(1)", "ok 11" },
        { "callee-declared-after-the-alias", "A = F\nF(x) = x + 1\nA(1)", "ok 2" },
        { "public-alias-of-a-private-sibling", "Lib = {\n    public A = F\n    F(x) = x + 1\n}\nLib.A(5)", "ok 6" },
        // Parentheses group syntax: `(P)` and `((P))` ARE the lone row `P`.
        { "redundant-groups-around-the-row", "P(x, x) = x\nA = (P)\nB = ((P))\nA(7, 7), B(7, 7)", "ok S[7, 7]" },
        { "redundant-group-keeps-the-arity", "P(x, x) = x\nA = (P)\nA(7)", "err ArityMismatch: Callable `A(x, x)` expects 2 arguments, but was called with 1 argument." },
        { "alias-inside-a-callback-block", "F(x) = x * 10\nmap([1, 2], { F })", "ok L[10, 20]" },
        { "alias-as-a-callback", "Only(*xs) = xs.count\nA = Only\nmap([(1, 2), 3], A)", "ok L[1, 1]" },
        { "dot-calls-on-an-alias", "Coll(*xs) = xs\nA = Coll\n(1, 2).A, 5.A, (1, 2)*.A", "ok S[L[S[1, 2]], L[5], L[1, 2]]" },
        { "inline-block-alias-as-an-argument", "F(x) = x * 3\nApply(f, v) = f(v)\nApply({ F }, 5)", "ok 15" },
        { "declarations-between-alias-levels", "F(x, y) = x - y\nA = {\n    k = 1\n    F\n}\nB = A\nB(10, 3), A.k", "ok S[7, 1]" },
        // A local alias never reuses a same-named enclosing parameter.
        { "local-alias-ignores-the-enclosing-parameter", "F(x) = x + 1\nOuter(x) = {\n    A = F\n    A(5) + x\n}\nOuter(100)", "ok 106" },
        { "local-alias-under-a-closed-list", "F(x) = x * 2\nG(q) = {\n    A = F\n    A(q) + 1\n}\nG(5)", "ok 11" },
        { "alias-failure-is-the-callee-failure", "Single([x]) = x\nA = Single\nA(7)", "err TypeMismatch: while evaluating call to A: Type mismatch: list pattern `[x]` expects a list value, but received numeric value 7" },
        { "user-property-named-like-a-builtin", "count(c) = 42\nA = count\nA((1, 2))", "ok 42" },
        { "qualified-math-member", "A = Math.Pow\nA(2, 10)", "ok 1024" },

        // ── Effects and the zero-argument cache ──────────────────────────────────────────
        { "chain-evaluates-each-argument-once", "R(x) = x\nA = R\nB = A\nB(trace(1)), B(trace(2))", "ok S[1, 2] [trace(1),trace(2)]" },
        { "forwarding-evaluates-each-argument-once", "F(x, y) = x + y\nG(x, y) = F\nG(trace(1), trace(2))", "ok 3 [trace(1),trace(2)]" },
        // Read bare, an alias is its OWN zero-argument binding, read once however often it is used
        // (the two-binding and fresh-call rows are in AliasAndBareForwardingTests).
        { "bare-alias-is-read-once", "Only(*xs) = tick()\nA = Only\nA + A + A", "ok 3 [tick#1]" },
        { "bare-alias-chain-is-read-once-per-binding", "Only(*xs) = tick()\nA = Only\nB = A\nB + B, A + A", "ok S[2, 4] [tick#1,tick#2]" },

        // ── Bare forwarding is by name ────────────────────────────────────────────────────
        { "forwarding-with-a-repeated-list", "F(x, y) = x * 10 + y\nG(x, x, y) = F\nG(3, 3, 4)", "ok 34" },
        { "forwarding-with-a-repeated-list-unequal", "F(x, y) = x * 10 + y\nG(x, x, y) = F\nG(3, 4, 4)", "err ArityMismatch: while evaluating call to G: Bad arity" },
        { "forwarding-with-a-middle-collector", "F(a, *m, z) = a * 100 + m.count * 10 + z\nG(a, *m, z) = F\nG(1, 7, 7, 7, 2)", "ok 132" },
        { "forwarding-branch-with-a-repeated-head", "F(x) = x * 2\nG(x, x) = F\nG(y, z) = 0\nG(3, 3), G(3, 4)", "ok S[6, 0]" },
        // Q-04: a name the closed list does not bind is the enclosing PARAMETER binding it denotes;
        // the list's own parameter comes first.
        { "forwarding-reuses-a-captured-parameter", "F(x) = x * 2\nOuter(x) = {\n    G(q) = F\n    G(0)\n}\nOuter(21)", "ok 42" },
        { "forwarding-prefers-its-own-parameter", "F(x) = x * 2\nOuter(x) = {\n    G(x) = F\n    G(1)\n}\nOuter(21)", "ok 2" },

        // ── A written call infers only the names written in it ───────────────────────────
        { "written-call-ignores-callee-binders", "Sub((a, b)) = a - b\nG = Sub((b, a))\nG(10, 3)", "ok 7" },
        { "written-call-with-grace", "Sub((a, b)) = a - b\nG = Sub((y, ~x))\nG(2, 3)", "ok 1" },
        { "nested-written-call", "F(v) = v * 2\nH(w) = w + 1\nG = F(H(x))\nG(5)", "ok 12" },

        // ── Boundaries ───────────────────────────────────────────────────────────────────
        // A deconstruction's right-hand side is a written row of the enclosing body
        // (`AstHelpers.WrittenRows`; its free names are the body's own parameters), so a body with
        // one beside the bare callee has TWO written rows: it is a formula, lifted by binding name.
        { "deconstruction-beside-the-row-is-a-formula", "P(x, x) = x\nA = {\n    a, b = 1, 2\n    P\n}\nA(7)", "ok 7" },
        { "deconstruction-beside-the-row-takes-one-name", "P(x, x) = x\nA = {\n    a, b = 1, 2\n    P\n}\nA(7, 7)", "err ArityMismatch: Callable `A(x)` expects 1 argument, but was called with 2 arguments." },
        { "deconstruction-infers-its-own-names-first", "F(x) = x + 1\nA = {\n    a, b = p, q\n    F\n}\nA(1, 2, 3)", "ok 4" },
        // Not alias targets (PV-14 / Q-13, PV-26 / Q-12; a clause family is pinned in the main
        // suite): the row stays a zero-argument demand.
        { "non-math-builtin-is-no-alias-target", "A = { if }\nA(true, 1, 2)", "err ArityMismatch: Callable `A` expects 0 arguments, but was called with 3 arguments." },
        { "callable-parameter-is-no-alias-target", "F(x) = x + 1\nG(F) = {\n    A = F\n    A(1)\n}\nG(F)", "err ArityMismatch: while evaluating call to G: Callable `A` expects 0 arguments, but was called with 1 argument." },
        { "opened-member-is-no-alias-target", "open Lib\nLib = { public F(x) = x + 1 }\nA = F\nA(5)", "err ArityMismatch: Callable `A` expects 0 arguments, but was called with 1 argument." },
        { "dotted-member-is-no-alias-target", "Lib = { public F(x) = x + 1 }\nA = Lib.F\nA(5)", "err ArityMismatch: Callable `A` expects 0 arguments, but was called with 1 argument." },
        { "shadowed-math-name-is-a-value", "sin = 5\nA = sin\nA", "ok 5" },
    };

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task EveryRoute_AgreesWithTheReviewedOutcome(string id, string source, string expected)
    {
        var actual = RepeatedNameConstraintTests.Rendered(await RepeatedNameConstraintTests.OnEveryRouteAsync(source, seed: 7));
        Assert.True(expected == actual, $"{id}\nexpected: {expected}\nactual:   {actual}");
    }

    /// <summary>
    /// Each implicit form equals the call a programmer would write (bare forwarding and the written
    /// call elaborate to ordinary calls; the alias's own frame name aside, the alias is its callee).
    /// </summary>
    public static TheoryData<string, string, string> WrittenEquivalents => new()
    {
        { "forwarding-is-not-positional", "F(y, x) = y - x\nG(x, y) = F\nG(10, 3), G(4, 9)", "F(y, x) = y - x\nG(x, y) = F(y, x)\nG(10, 3), G(4, 9)" },
        { "forwarding-with-a-middle-collector", "F(a, *m, z) = a * 100 + m.count * 10 + z\nG(a, *m, z) = F\nG(1, 2), G(1, 7, 2), G(1, 7, 7, 2)", "F(a, *m, z) = a * 100 + m.count * 10 + z\nG(a, *m, z) = F(a, m*, z)\nG(1, 2), G(1, 7, 2), G(1, 7, 7, 2)" },
        { "forwarding-branch-with-a-repeated-head", "F(x) = x * 2\nG(x, x) = F\nG(y, z) = 0\nG(3, 3), G(3, 4)", "F(x) = x * 2\nG(x, x) = F(x)\nG(y, z) = 0\nG(3, 3), G(3, 4)" },
        { "written-call-ignores-callee-binders", "Sub((a, b)) = a - b\nG = Sub((b, a))\nG(10, 3)", "Sub((a, b)) = a - b\nG(b, a) = Sub((b, a))\nG(10, 3)" },
        { "written-call-with-grace", "Sub((a, b)) = a - b\nG = Sub((y, ~x))\nG(2, 3)", "Sub((a, b)) = a - b\nG(x, y) = Sub((y, x))\nG(2, 3)" },
        { "alias-keeps-a-grace-order", "F = b - ~a\nA = F\nA(10, 3)", "F = b - ~a\nF(10, 3)" },
    };

    [Theory]
    [MemberData(nameof(WrittenEquivalents))]
    public async Task EachImplicitForm_EqualsTheWrittenCall(string id, string implicitSource, string writtenSource)
    {
        var implicitOutcome = RepeatedNameConstraintTests.Rendered(await RepeatedNameConstraintTests.OnEveryRouteAsync(implicitSource, seed: 7));
        var writtenOutcome = RepeatedNameConstraintTests.Rendered(await RepeatedNameConstraintTests.OnEveryRouteAsync(writtenSource, seed: 7));
        Assert.True(implicitOutcome == writtenOutcome, $"{id}\nimplicit: {implicitOutcome}\nwritten:  {writtenOutcome}");
    }

    /// <summary>
    /// Mutually dependent lone rows elaborate identically in either declaration order: the alias
    /// `A = B` inherits B's written list, and the bare forwarding `B(y) = A` calls `A(y)` — so
    /// evaluation recurses without end in both orders (the recursion itself is the run's limit, whose
    /// location no route promises, so the elaboration is what is compared).
    /// </summary>
    [Theory]
    [InlineData("A = B\nB(y) = A\n0")]
    [InlineData("B(y) = A\nA = B\n0")]
    public void MutualAliasAndBareForwarding_ElaborateAlikeInEitherOrder(string source)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var alias = Assert.IsType<Algorithm.User>(root.Properties.Single(property => property.Name == "A").Value);
        var forwarding = Assert.IsType<Algorithm.User>(root.Properties.Single(property => property.Name == "B").Value);

        Assert.Equal(["y"], alias.Parameters.Select(static parameter => parameter.Name));
        Assert.True(alias.InheritsCalleeSignature);
        var aliasCall = Assert.IsType<Expr.Call>(Assert.Single(alias.Output));
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(aliasCall.Function).Name);
        Assert.Equal("y", Assert.IsType<Expr.Param>(Assert.Single(aliasCall.Args)).Name);

        Assert.Equal(["y"], forwarding.Parameters.Select(static parameter => parameter.Name));
        Assert.False(forwarding.InheritsCalleeSignature);
        var forwardingCall = Assert.IsType<Expr.Call>(Assert.Single(forwarding.Output));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(forwardingCall.Function).Name);
        Assert.Equal("y", Assert.IsType<Expr.Param>(Assert.Single(forwardingCall.Args)).Name);
    }
}
