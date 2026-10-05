using System.Text.RegularExpressions;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// ALIASES, BARE FORWARDING AND WRITTEN CALLS (FWD-02, decided September 29–30 2026). Four
/// mechanisms, never conflated:
/// <list type="bullet">
///   <item><c>A = F</c> — a body whose ONE written row is a bare callable that declares parameterized
///   callable structure — is a CALLABLE ALIAS (binding indirection, decided October 1 2026): a binding
///   of its own (<see cref="Algorithm.Alias"/>) whose callable IS <c>F</c> — no wrapper, no inherited
///   signature — so <c>A(S)</c> is <c>F(S)</c> through F's own invocation for every supply <c>S</c>
///   (arity, structural kinds, collectors, repeated names, binderless groups are F's own).</item>
///   <item><c>A(p) = F</c> — the same lone row under a written parameter list or a clause-branch
///   pattern — is BARE FORWARDING, by NAME: <c>F</c> receives the EXISTING bindings of its own
///   parameters' names (<c>A</c>'s own top-level parameters, else an enclosing parameter binding,
///   Q-04). Nothing is renamed (<c>F(q)</c> under <c>A(p) = F</c> is rejected), nothing is added to
///   the closed list (<c>F(p, q)</c> under <c>A(p) = F</c> is rejected), nothing is positional
///   (<c>F(y, x)</c> under <c>G(x, y) = F</c> calls <c>F(y, x)</c>), and a structural parameter is
///   supplied only by the same pattern (<c>Single([x])</c> under <c>G(x) = Single</c> is rejected;
///   under <c>G([x]) = Single</c> it forwards). The rejection is the front-end error
///   <see cref="DiagnosticCode.UnforwardableParameter"/>.</item>
///   <item><c>A(p) = F(p)</c> is an ordinary EXPLICIT CALL: arguments are passed as written, so the
///   caller's and callee's parameter names need not match. It is deliberately NOT the same as the
///   bare <c>A(p) = F</c>.</item>
///   <item><c>A = F(exprs)</c> infers exactly the free names written in <c>exprs</c>, and
///   <c>A = F + 1</c> is FORMULA LIFTING, by binding name
///   (<see cref="ImplicitForwardingByBindingNameTests"/>): <c>F</c>'s required parameters join the
///   inferred signature. Formula lifting and bare forwarding are deliberately different mechanisms.</item>
/// </list>
/// <para>Evidence: six execution routes with host-call logs and seeded random streams
/// (<see cref="RepeatedNameConstraintTests.OnEveryRouteAsync"/>), the elaborated tree, the
/// front-end diagnostics, and the editor model. Lean: <c>bareForwardingArguments</c> and
/// <c>ParameterPattern.sourceArguments</c> with the <c>bare_forwarding_*</c> / <c>source_arguments_*</c>
/// laws in <c>KatLangArityLaws.lean</c> and the guards in <c>CoreTests/AliasForwarding.lean</c>.</para>
/// </summary>
public class AliasAndBareForwardingTests
{
    private const string Vocabulary = "Bad = trace(1) / 0\nInc(y) = y + 1\n";

    private static Task<RepeatedNameConstraintTests.Observation> OnEveryRoute(string source, long? seed = null)
        => RepeatedNameConstraintTests.OnEveryRouteAsync(source, seed);

    private static async Task<string> Outcome(string source, long? seed = null)
        => RepeatedNameConstraintTests.Rendered(await OnEveryRoute(source, seed));

    private static Algorithm.User Owner(Algorithm.User root, string name)
        => Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == name).Value);

    /// <summary>A property that is a callable alias (binding indirection).</summary>
    private static Algorithm.Alias AliasOf(Algorithm.User root, string name)
        => Assert.IsType<Algorithm.Alias>(Assert.Single(root.Properties, property => property.Name == name).Value);

    /// <summary>The signature of an alias's callable: its target's, as a programmer would write it.</summary>
    private static string AliasSignature(Algorithm.Alias alias)
        => string.Join(", ", alias.ResolvedTarget!.Signature.Signature!.ParameterPatterns.Select(static pattern => pattern.DisplayName));

    /// <summary>A signature's parameter patterns as a programmer would write them.</summary>
    private static string Signature(Algorithm.User algorithm)
        => string.Join(", ", algorithm.ParameterPatterns.Select(static pattern => pattern.DisplayName));

    /// <summary>A call's arguments as written, spans ignored (<c>[x]</c>, <c>(x, y)</c>, <c>rest*</c>, <c>()</c>).</summary>
    private static string Arguments(IEnumerable<Expr> arguments)
        => string.Join(", ", arguments.Select(static argument => argument switch
        {
            Expr.Param param => param.Name,
            Expr.SequenceSpread spread => Arguments([spread.Operand]) + "*",
            Expr.ListLiteral list => "[" + Arguments(list.Items) + "]",
            Expr.Capture capture => "(" + Arguments(capture.Body) + ")",
            Expr.EmptySequence => "()",
            Expr.Num number => Rendering.ValueTextRenderer.FormatNumberInvariant(number.Value),
            _ => argument.GetType().Name,
        }));

    /// <summary>The one row of an owner: the synthesized (or written) call to <paramref name="callee"/>.</summary>
    private static Expr.Call LoneCall(Algorithm.User owner, string callee)
    {
        var call = Assert.IsType<Expr.Call>(Assert.Single(owner.Output));
        Assert.Equal(callee, Assert.IsType<Expr.Resolve>(call.Function).Name);
        return call;
    }

    /// <summary>A signature with every name erased: its arity, kinds, collectors and nesting only.</summary>
    private static string Shape(string signature) => Regex.Replace(signature, @"[A-Za-z_][A-Za-z_0-9]*", "_");

    /// <summary>A written pattern as the argument that rebuilds it: each <c>*name</c> re-spread as <c>name*</c>.</summary>
    private static string Rebuilt(string pattern) => Regex.Replace(pattern, @"\*([A-Za-z_][A-Za-z_0-9]*)", "$1*");

    /// <summary>
    /// An outcome with the evaluation-context frames of the given names removed and the alias's
    /// own name in a callable display replaced by the callee's: what an alias may differ in from
    /// its callee (the alias is its own callable, so its call adds one frame and its binder
    /// reports under its name).
    /// </summary>
    private static string ModuloAlias(string outcome, string callee, params string[] aliases)
    {
        foreach (var name in aliases.Append(callee))
            outcome = outcome.Replace($"while evaluating call to {name}: ", "", StringComparison.Ordinal);
        foreach (var alias in aliases)
        {
            outcome = outcome
                .Replace($"`{alias}(", $"`{callee}(", StringComparison.Ordinal)
                .Replace($"`{alias}`", $"`{callee}`", StringComparison.Ordinal)
                .Replace($"'{alias}'", $"'{callee}'", StringComparison.Ordinal);
        }

        return outcome;
    }

    private static string CalleeName(string declaration)
    {
        var end = declaration.IndexOfAny(['(', ' ']);
        return declaration[..end];
    }

    /// <summary>
    /// Asserts the front end rejects <paramref name="source"/> with exactly the unforwardable
    /// callee parameters named, each reported at the bare reference, and nothing else.
    /// </summary>
    private static void AssertUnforwardable(string source, params string[] parameters)
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError(source);
        Assert.All(diagnostics, static diagnostic => Assert.Equal(DiagnosticCode.UnforwardableParameter, diagnostic.Code));
        Assert.Equal(
            parameters,
            diagnostics.Select(static diagnostic => Regex.Match(diagnostic.Message, "parameter '([^']*)'").Groups[1].Value));
        Assert.All(diagnostics, static diagnostic => Assert.NotNull(diagnostic.Span));
    }

    // ── 1. The required examples ──────────────────────────────────────────────────────

    public static TheoryData<string, string, string> RequiredExamples => new()
    {
        // A. A callable alias is F itself.
        { "A", "F(p) = p * 2\nA = F\nA(5)", "ok 10" },
        // B. Bare same-name forwarding.
        { "B", "F(p) = p * 2\nA(p) = F\nA(5)", "ok 10" },
        // D. An explicit call: the names need not match.
        { "D", "F(q) = q * 2\nA(p) = F(p)\nA(5)", "ok 10" },
        // E. A zero-parameter target needs nothing from A: the row is its (cached) value.
        { "E", "F = 10\nA(p) = F\nA(999)", "ok 10" },
        // G. An extra source parameter may stay unused.
        { "G", "F(p) = p * 2\nA(p, unused) = F\nA(5, 999)", "ok 10" },
        // H. Formula lifting lifts x.
        { "H", "F(x) = x * 2\nA = F + 1\nA(5)", "ok 11" },
        // I. Shared formula lifting: one x for both callees.
        { "I", "F(x) = x * 2\nG(x) = x + 10\nA = F + G\nA(5)", "ok 25" },
        // J. An explicit inferred call infers the written x and y.
        { "J", "Add((a, b)) = a + b\nG = Add((x, y))\nG(2, 3)", "ok 5" },
        // Structural: the explicit call passes G's whole x as Single's list argument.
        { "S-explicit", "Single([x]) = x\nG(x) = Single(x)\nG([7])", "ok 7" },
        // Structural: the same pattern forwards.
        { "S-same-list", "Single([x]) = x\nG([x]) = Single\nG([7])", "ok 7" },
        { "S-same-sequence", "Add((x, y)) = x + y\nG((x, y)) = Add\nG((2, 3))", "ok 5" },
        // An exact list alias and a sequence alias.
        { "S-alias-list", "Single([x]) = x\nA = Single\nA([7])", "ok 7" },
        { "S-alias-sequence", "Pair((x, y)) = x + y\nA = Pair\nA((2, 3))", "ok 5" },
        // Not positional: G.y reaches F.y and G.x reaches F.x, whatever their order.
        { "N", "F(y, x) = y - x\nG(x, y) = F\nG(10, 3)", "ok -7" },
        // A repeated-name alias keeps P's two independent arguments and their constraint.
        { "R-alias", "P(x, x) = x\nA = P\nA(5, 5)", "ok 5" },
        { "R-alias-unequal", "P(x, x) = x\nA = P\nA(5, 6)", "err ArityMismatch: while evaluating call to A: repeated parameter 'x' requires equal arguments: Bad arity" },
        { "R-alias-arity", "P(x, x) = x\nA = P\nA(5)", "err ArityMismatch: Callable `A(x, x)` expects 2 arguments, but was called with 1 argument." },
        // Bare forwarding is by binding name: A's one x feeds both of P's occurrences.
        { "R-bare", "P(x, x) = x\nA(x) = P\nA(7)", "ok 7" },
        // A binderless alias keeps E's two structural parameters.
        { "binderless-alias", "E((), []) = 1\nA = E\nA((), [])", "ok 1" },
        { "binderless-alias-arity", "E((), []) = 1\nA = E\nA()", "err ArityMismatch: Callable `A((), [])` expects 2 arguments, but was called with 0 arguments." },
    };

    [Theory]
    [MemberData(nameof(RequiredExamples))]
    public async Task TheRequiredExamples(string id, string source, string expected)
    {
        var actual = await Outcome(source);
        Assert.True(expected == actual, $"{id}\nexpected: {expected}\nactual:   {actual}");
    }

    /// <summary>
    /// The required REJECTIONS: bare forwarding never renames (C), never adds a parameter to a closed
    /// list (F), and never reshapes an argument from a same-named binding (the structural cases) —
    /// each is the front-end error <see cref="DiagnosticCode.UnforwardableParameter"/> naming the
    /// callee parameter it cannot supply, and the program does not run.
    /// </summary>
    public static TheoryData<string, string, string[]> RequiredRejections => new()
    {
        { "C", "F(q) = q * 2\nA(p) = F\nA(5)", ["q"] },
        { "F", "F(p, q) = p + q\nA(p) = F\nA(5)", ["q"] },
        { "S-leaf-coincidence", "Single([x]) = x\nG(x) = Single\nG([7])", ["[x]"] },
        { "S-no-manufactured-sequence", "Add((x, y)) = x + y\nG(x, y) = Add\nG(2, 3)", ["(x, y)"] },
        { "S-element-is-not-a-whole-value", "F(x) = x\nA([x]) = F\nA([7])", ["x"] },
        { "S-no-positional-renaming-inside", "F([a, b]) = a + b\nA([x, y]) = F\nA([1, 2])", ["[a, b]"] },
        { "R-renamed", "P(x, x) = x\nA(y) = P\nA(7)", ["x"] },
        { "binderless-bare", "E((), []) = 1\nA(u, v) = E\nA((), [])", ["()", "[]"] },
    };

    [Theory]
    [MemberData(nameof(RequiredRejections))]
    public void TheRequiredRejections(string id, string source, string[] parameters)
    {
        _ = id;
        AssertUnforwardable(source, parameters);
        var result = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.All(result.Errors, static error => Assert.Equal(KatLangErrorCode.UnforwardableParameter, error.Code));
    }

    [Fact]
    public void AnUnforwardableParameter_IsReportedAtTheBareReference_InKatLangTerms()
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError("F(q) = q * 2\nA(p) = F\n0"));
        Assert.Equal(new SourceSpan(2, 8, 2, 9), diagnostic.Span);
        Assert.Equal(
            "'F' is forwarded by name here, but its parameter 'q' is not a parameter of the enclosing explicit parameter list."
                + Environment.NewLine
                + "Bare forwarding reuses an existing parameter only under its own name, and explicit parameter lists are closed, "
                + "so 'q' is neither renamed nor added. Declare 'q' in the parameter list, or call 'F' with explicit arguments.",
            diagnostic.Message);

        var reshaped = Assert.Single(SourceProvenance.ExpectFrontEndError("Single([x]) = x\nG(x) = Single\n0"));
        Assert.Equal(
            "'Single' is forwarded by name here, but the enclosing explicit parameter list does not declare its parameter '[x]' in that form."
                + Environment.NewLine
                + "Bare forwarding reuses an existing parameter only with the same pattern and never reshapes an argument. "
                + "Declare the parameter '[x]', or call 'Single' with explicit arguments.",
            reshaped.Message);

        var branch = Assert.Single(SourceProvenance.ExpectFrontEndError("F(q) = q * 2\nG(0) = 0\nG(n) = F\n0"));
        Assert.Contains("is not bound by the pattern of conditional branch 'G'", branch.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// The required examples' elaborated shapes: bare forwarding keeps the written signature and
    /// calls the callee with the SAME-NAMED bindings in the callee's order; an explicit or written
    /// call is exactly what it writes. (An alias synthesizes no call at all:
    /// <see cref="TheRequiredAliases_AreBindingIndirection"/>.)
    /// (program, owner, callee, signature, call arguments)
    /// </summary>
    public static TheoryData<string, string, string, string, string> RequiredShapes => new()
    {
        { "F(p) = p * 2\nA(p) = F", "A", "F", "p", "p" },
        { "F(q) = q * 2\nA(p) = F(p)", "A", "F", "p", "p" },
        { "F(p) = p * 2\nA(p, unused) = F", "A", "F", "p, unused", "p" },
        { "F(y, x) = y - x\nG(x, y) = F", "G", "F", "x, y", "y, x" },
        { "P(x, x) = x\nA(x) = P", "A", "P", "x", "x, x" },
        { "Single([x]) = x\nG([x]) = Single", "G", "Single", "[x]", "[x]" },
        { "Single([x]) = x\nG(x) = Single(x)", "G", "Single", "x", "x" },
        { "Single([a]) = a\nG = Single([x])", "G", "Single", "x", "[x]" },
        { "Add((a, b)) = a + b\nG = Add((x, y))", "G", "Add", "x, y", "(x, y)" },
        { "Add((x, y)) = x + y\nG((x, y)) = Add", "G", "Add", "(x, y)", "(x, y)" },
        { "E((), []) = 1\nA((), []) = E", "A", "E", "(), []", "(), []" },
        { "F(*xs) = xs\nA(*xs) = F", "A", "F", "*xs", "xs*" },
        { "F(*xs) = xs\nA(xs) = F", "A", "F", "xs", "xs" },
        { "F(xs) = xs\nA(*xs) = F", "A", "F", "*xs", "xs" },
        { "F(p, *rest) = p\nA(p) = F", "A", "F", "p", "p" },
    };

    [Theory]
    [MemberData(nameof(RequiredShapes))]
    public void TheRequiredExamples_ElaborateToTheirCalls(string program, string owner, string callee, string signature, string arguments)
    {
        var algorithm = Owner(SourceProvenance.ParseValid(program + "\n0").Root, owner);
        Assert.Equal(signature, Signature(algorithm));
        Assert.Equal(arguments, Arguments(LoneCall(algorithm, callee).Args));
    }

    /// <summary>
    /// The required ALIASES elaborate to binding indirection: the alias keeps its written target and
    /// owns no parameter, and its callable — recorded by the front end — is the callee with the
    /// callee's own signature, repeated names and binderless groups included.
    /// </summary>
    [Theory]
    [InlineData("P(x, x) = x\nA = P", "P", "x, x")]
    [InlineData("E((), []) = 1\nA = E", "E", "(), []")]
    [InlineData("F(p) = p * 2\nA = F", "F", "p")]
    [InlineData("Single([x]) = x\nA = Single", "Single", "[x]")]
    public void TheRequiredAliases_AreBindingIndirection(string program, string callee, string signature)
    {
        var root = SourceProvenance.ParseValid(program + "\n0").Root;
        var alias = AliasOf(root, "A");
        Assert.Equal(callee, Assert.IsType<Expr.Resolve>(alias.Target).Name);
        Assert.Empty(alias.Properties);
        Assert.Equal(signature, AliasSignature(alias));
        Assert.Same(Owner(root, callee).Declaration, alias.ResolvedTarget!.Algorithm.Declaration);
    }

    /// <summary>
    /// When bare forwarding supplies NOTHING — the callee needs nothing from the closed list: a
    /// zero-parameter property, or a callee whose only parameter is a collector that no binding of
    /// its name supplies — the row stays the callee's bare name, its cached zero-argument value
    /// (Q-03); no call is invented.
    /// </summary>
    [Theory]
    [InlineData("F = 10\nA(p) = F")]
    [InlineData("F(*xs) = xs\nA(p) = F")]
    [InlineData("F(*xs) = xs\nA([ys]) = F")]
    public void NothingToForward_LeavesTheBareName(string program)
        => Assert.Equal("F", Assert.IsType<Expr.Resolve>(Assert.Single(Owner(SourceProvenance.ParseValid(program + "\n0").Root, "A").Output)).Name);

    // ── 2. Alias transparency: A(S) ≡ F(S) for every signature shape and supply ────────

    private static readonly string[] AliasCallees =
    [
        "Id(v) = v",
        "Two(a, b) = [a, b]",
        "P(x, x) = x",
        "P3(x, y, x) = [x, y]",
        "Single([x]) = x",
        "Add((a, b)) = a + b",
        "Pair((x, y)) = x, y",
        "LPair([x, y]) = x, y",
        "C((*xs)) = xs.count",
        "LC([*xs]) = xs",
        "Coll(*xs) = xs",
        "Head(h, *rest) = h, rest",
        "Mid((first, *middle, last)) = first, middle, last",
        "LMid([first, *middle, last]) = first, middle, last",
        "SL(([x, y], z)) = x, y, z",
        "LS([(x, y), z]) = x, y, z",
        "SHead((first, *rest)) = first, rest",
        "LHead([first, *rest]) = first, rest",
        "Nest([[x]]) = x",
        "Rest([(x, *r), *s]) = x, r, s",
        "Kinds([x], (y, z)) = x, y, z",
        "Mixed(a, [b]) = a, b",
        "E((), []) = 1",
        "ME(x, ()) = x",
        "RG((x, a), x) = a",
        "RL([x, x]) = x",
        "Div(a, b) = a / b",
        "Eff(v) = trace(v), tick()",
    ];

    private static readonly string[] AliasSupplies =
    [
        "", "7", "7, 7", "7, 8", "1, 0", "[7]", "[[7]]", "(1, 2)", "[1, 2]", "(1, 2, 3)", "[1, 2, 3]",
        "((1, 2), 3)", "([1, 2], 3)", "[(1, 2), 3]", "(), []", "[], ()", "()", "[]", "7, ()", "((7, 1), 7)",
        "'a'", "true", "((1, 2), (3, 4))", "[(1, 2)]", "[()]", "[[]]", "[[1, 2], 3]", "[(1, 2, 3), 4]", "[1], (2, 3)", "0, [7]",
        "trace(7)", "trace(7), trace(7)", "[trace(7)]", "(trace(1), trace(2))", "tick(), tick()",
        "Bad", "7, Bad", "Inc", "randomInt(0, 9), randomInt(0, 9)",
    ];

    public static TheoryData<int> AliasCalleeIndexes()
    {
        var data = new TheoryData<int>();
        for (var index = 0; index < AliasCallees.Length; index++)
            data.Add(index);
        return data;
    }

    /// <summary>
    /// THE ALIAS TRANSPARENCY LAW: for every callee shape and every supply, <c>A = F</c> and the
    /// three-level chain <c>A = F</c>, <c>B = A</c>, <c>C = B</c> agree with the direct call on every
    /// route — the same success or failure, the same result, the same error kind and message
    /// modulo the aliases' own frames and names, the same host calls (hence the same argument
    /// evaluations and effects) and the same seeded random draws.
    /// </summary>
    [Theory]
    [MemberData(nameof(AliasCalleeIndexes))]
    public async Task AnAlias_IsItsCallee_ForEverySupply(int calleeIndex)
    {
        var declaration = Vocabulary + AliasCallees[calleeIndex] + "\n";
        var callee = CalleeName(AliasCallees[calleeIndex]);
        foreach (var supply in AliasSupplies)
        {
            var direct = await OnEveryRoute(declaration + $"{callee}({supply})", seed: 11);
            var alias = await OnEveryRoute(declaration + $"Al1 = {callee}\nAl1({supply})", seed: 11);
            var chain = await OnEveryRoute(declaration + $"Al1 = {callee}\nAl2 = Al1\nAl3 = Al2\nAl3({supply})", seed: 11);
            var expected = ModuloAlias(direct.Outcome, callee);
            foreach (var (observation, form) in new[] { (alias, "Al1"), (chain, "Al3") })
            {
                Assert.True(
                    expected == ModuloAlias(observation.Outcome, callee, "Al1", "Al2", "Al3")
                        && direct.HostCalls.SequenceEqual(observation.HostCalls),
                    $"{AliasCallees[calleeIndex]} via {form} with ({supply})\ndirect: {direct}\nalias:  {observation}");
            }
        }
    }

    /// <summary>
    /// Every level of a chain is binding indirection: each alias keeps its own written target (the
    /// previous level) and owns no parameter, and every level's callable is the ONE callee — the
    /// chain normalizes to it, with its signature unchanged (nothing deduplicated, dropped, flattened
    /// or re-kinded).
    /// </summary>
    public static TheoryData<int> PureAliasCalleeIndexes()
    {
        var data = new TheoryData<int>();
        for (var index = 0; index < AliasCallees.Length; index++)
        {
            if (!AliasCallees[index].Contains("trace(", StringComparison.Ordinal))
                data.Add(index);
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(PureAliasCalleeIndexes))]
    public void AnAlias_IsBindingIndirection_AtEveryLevel(int calleeIndex)
    {
        var declaration = AliasCallees[calleeIndex];
        var callee = CalleeName(declaration);
        var root = SourceProvenance.ParseValid(declaration + $"\nAl1 = {callee}\nAl2 = Al1\nAl3 = Al2\n0").Root;
        var target = Owner(root, callee);
        foreach (var (name, next) in new[] { ("Al1", callee), ("Al2", "Al1"), ("Al3", "Al2") })
        {
            var alias = AliasOf(root, name);
            Assert.Equal(next, Assert.IsType<Expr.Resolve>(alias.Target).Name);
            Assert.Empty(alias.Properties);
            Assert.Equal(Signature(target), AliasSignature(alias));
            Assert.Same(target.Declaration, alias.ResolvedTarget!.Algorithm.Declaration);
        }
    }

    // ── 3. Bare forwarding: the source × target compatibility matrix ───────────────────

    /// <summary>(target signature, the callee declaration with that signature)</summary>
    private static readonly (string Signature, string Declaration)[] MatrixTargets =
    [
        ("", "F = 10"),
        ("p", "F(p) = [p]"),
        ("q", "F(q) = [q]"),
        ("p, q", "F(p, q) = [p, q]"),
        ("q, p", "F(q, p) = [q, p]"),
        ("p, p", "F(p, p) = p"),
        ("*p", "F(*p) = p"),
        ("[p]", "F([p]) = p"),
        ("[p, q]", "F([p, q]) = [p, q]"),
        ("[*p]", "F([*p]) = p"),
        ("(p, q)", "F((p, q)) = [p, q]"),
        ("(p, *rest)", "F((p, *rest)) = [p, rest]"),
        ("(), []", "F((), []) = 1"),
    ];

    /// <summary>(source signature, supplies for <c>A(source)</c>)</summary>
    private static readonly (string Signature, string[] Supplies)[] MatrixSources =
    [
        ("p", ["5", "[5]"]),
        ("q", ["5", "(5, 6)"]),
        ("p, q", ["1, 2", "[1], 2"]),
        ("q, p", ["1, 2", "3, [4]"]),
        ("*p", ["", "1, 2"]),
        ("p, *rest", ["5", "5, 6, 7"]),
        ("[p]", ["[7]", "[[7]]"]),
        ("[p, q]", ["[1, 2]", "[[1], 2]"]),
        ("[*p]", ["[]", "[1, 2]"]),
        ("(p, q)", ["(1, 2)", "((1, 2), 3)"]),
        ("(p, *rest)", ["(1, 2, 3)", "(1, 2)"]),
        ("(), []", ["(), []"]),
        ("p, extra", ["5, 9"]),
    ];

    /// <summary>Top-level patterns of a written signature (commas at nesting depth 0).</summary>
    private static List<string> TopLevelPatterns(string signature)
    {
        var patterns = new List<string>();
        if (signature.Length == 0)
            return patterns;

        var depth = 0;
        var start = 0;
        for (var index = 0; index < signature.Length; index++)
        {
            switch (signature[index])
            {
                case '(' or '[': depth++; break;
                case ')' or ']': depth--; break;
                case ',' when depth == 0:
                    patterns.Add(signature[start..index].Trim());
                    start = index + 1;
                    break;
            }
        }

        patterns.Add(signature[start..].Trim());
        return patterns;
    }

    private static readonly Regex CapturePattern = new(@"^(\*?)([A-Za-z_][A-Za-z_0-9]*)$", RegexOptions.CultureInvariant);

    /// <summary>
    /// The test-side restatement of bare forwarding over written signatures — an oracle independent
    /// of the resolver: every target parameter is supplied BY NAME from the source's own TOP-LEVEL
    /// capture of that name (a collecting source into a collecting target re-spread), a target
    /// collector no source name matches receives nothing, and a structural target pattern needs the
    /// identical source pattern; a name the source binds only inside a structural pattern, a missing
    /// fixed name, or a missing structural pattern rejects the program. (No enclosing bindings here.)
    /// Returns the rebuilt call arguments, or null when the program is rejected.
    /// </summary>
    private static List<string>? ExpectedBareForwarding(string target, string source)
    {
        var sourcePatterns = TopLevelPatterns(source);
        var topLevelCaptures = new Dictionary<string, bool>(StringComparer.Ordinal);
        foreach (var pattern in sourcePatterns)
        {
            if (CapturePattern.Match(pattern) is { Success: true } match)
                topLevelCaptures.TryAdd(match.Groups[2].Value, match.Groups[1].Value == "*");
        }

        var boundNames = Regex.Matches(source, "[A-Za-z_][A-Za-z_0-9]*").Select(static match => match.Value).ToHashSet(StringComparer.Ordinal);
        var arguments = new List<string>();
        foreach (var parameter in TopLevelPatterns(target))
        {
            if (CapturePattern.Match(parameter) is { Success: true } capture)
            {
                var name = capture.Groups[2].Value;
                var collecting = capture.Groups[1].Value == "*";
                if (topLevelCaptures.TryGetValue(name, out var sourceCollecting))
                    arguments.Add(collecting && sourceCollecting ? name + "*" : name);
                else if (boundNames.Contains(name) || !collecting)
                    return null;
            }
            else if (sourcePatterns.Contains(parameter))
            {
                arguments.Add(Rebuilt(parameter));
            }
            else
            {
                return null;
            }
        }

        return arguments;
    }

    public static TheoryData<int> MatrixTargetIndexes()
    {
        var data = new TheoryData<int>();
        for (var index = 0; index < MatrixTargets.Length; index++)
            data.Add(index);
        return data;
    }

    /// <summary>
    /// THE BARE-FORWARDING LAW over a source × target matrix: for every target signature and every
    /// written source signature, <c>A(source) = F</c> is accepted exactly when the by-name rule
    /// supplies every target parameter (<see cref="ExpectedBareForwarding"/>); an accepted program
    /// keeps its written signature and elaborates to the explicit by-name call — the same tree, the
    /// same outcome on every route for every supply — or, when nothing is forwarded, to the bare
    /// name; a rejected one is <see cref="DiagnosticCode.UnforwardableParameter"/> and nothing
    /// else. Accepted/rejected, tree, runtime result, failure kind and host calls are all compared.
    /// </summary>
    [Theory]
    [MemberData(nameof(MatrixTargetIndexes))]
    public async Task BareForwarding_IsByName_AcrossTheSignatureMatrix(int targetIndex)
    {
        var (target, declaration) = MatrixTargets[targetIndex];
        foreach (var (source, supplies) in MatrixSources)
        {
            var program = $"{declaration}\nA({source}) = F\n";
            var expected = ExpectedBareForwarding(target, source);
            if (expected is null)
            {
                var diagnostics = SourceProvenance.ExpectFrontEndError(program + "0");
                Assert.True(
                    diagnostics.Count > 0 && diagnostics.All(static diagnostic => diagnostic.Code == DiagnosticCode.UnforwardableParameter),
                    $"F({target}) under A({source}) = F: expected only UnforwardableParameter, got {string.Join(" | ", diagnostics)}");
                continue;
            }

            var owner = Owner(SourceProvenance.ParseValid(program + "0").Root, "A");
            Assert.Equal(source, Signature(owner));
            Assert.Null(owner.ForwardingParameterStart);
            if (expected.Count == 0)
            {
                Assert.Equal("F", Assert.IsType<Expr.Resolve>(Assert.Single(owner.Output)).Name);
                continue;
            }

            var explicitProgram = $"{declaration}\nA({source}) = F({string.Join(", ", expected)})\n";
            var explicitOwner = Owner(SourceProvenance.ParseValid(explicitProgram + "0").Root, "A");
            Assert.True(
                Arguments(LoneCall(explicitOwner, "F").Args) == Arguments(LoneCall(owner, "F").Args),
                $"F({target}) under A({source}) = F: expected F({string.Join(", ", expected)}), got F({Arguments(LoneCall(owner, "F").Args)})");
            foreach (var supply in supplies)
            {
                var implicitOutcome = await Outcome(program + $"A({supply})");
                var explicitOutcome = await Outcome(explicitProgram + $"A({supply})");
                Assert.True(
                    implicitOutcome == explicitOutcome,
                    $"F({target}) under A({source}) = F with A({supply})\nexplicit: {explicitOutcome}\nimplicit: {implicitOutcome}");
            }
        }
    }

    // ── 4. No renaming, no positions: names decide ───────────────────────────────────────

    /// <summary>
    /// THE RENAMING LAWS, one per mechanism. Renaming the TARGET's parameters: an alias follows (its
    /// callable IS the target); bare forwarding may stop compiling (names must match — intended); an
    /// explicit call is unaffected (arguments are written); formula lifting renames the lifted
    /// parameter (by-name dependency inference — intended).
    /// </summary>
    [Fact]
    public async Task RenamingTheTarget_HasADifferentEffectOnEachMechanism()
    {
        // Alias: the callable is the target, so its signature is the target's.
        Assert.Equal("x", AliasSignature(AliasOf(SourceProvenance.ParseValid("F(x) = x * 2\nA = F\n0").Root, "A")));
        Assert.Equal("value", AliasSignature(AliasOf(SourceProvenance.ParseValid("F(value) = value * 2\nA = F\n0").Root, "A")));
        Assert.Equal("ok 10", await Outcome("F(value) = value * 2\nA = F\nA(5)"));

        // Bare forwarding: F(x) forwards from A(x); F(value) does not.
        Assert.Equal("ok 10", await Outcome("F(x) = x * 2\nA(x) = F\nA(5)"));
        AssertUnforwardable("F(value) = value * 2\nA(x) = F\nA(5)", "value");

        // Explicit call: unaffected.
        Assert.Equal("ok 10", await Outcome("F(x) = x * 2\nA(x) = F(x)\nA(5)"));
        Assert.Equal("ok 10", await Outcome("F(value) = value * 2\nA(x) = F(x)\nA(5)"));

        // Formula lifting: the lifted parameter takes the target's name.
        Assert.Equal("x", Signature(Owner(SourceProvenance.ParseValid("F(x) = x * 2\nH = F + 1\n0").Root, "H")));
        Assert.Equal("value", Signature(Owner(SourceProvenance.ParseValid("F(value) = value * 2\nH = F + 1\n0").Root, "H")));
        Assert.Equal("ok 11", await Outcome("F(value) = value * 2\nH = F + 1\nH(5)"));
    }

    /// <summary>
    /// Bare forwarding never renames, whatever the arity: with one fixed parameter on each side, two,
    /// or three, a single differing name rejects the program; the explicit call accepts it.
    /// </summary>
    [Theory]
    [InlineData("F(q) = q", "A(p) = F", "q")]
    [InlineData("F(a, b) = a - b", "A(a, c) = F", "b")]
    [InlineData("F(a, b, c) = a", "A(a, b, d) = F", "c")]
    [InlineData("F(*items) = items", "A(p, *xs) = F", null)]
    public void BareForwarding_NeverRenames(string callee, string definition, string? rejected)
    {
        if (rejected is null)
            Assert.Equal("F", Assert.IsType<Expr.Resolve>(Assert.Single(Owner(SourceProvenance.ParseValid($"{callee}\n{definition}\n0").Root, "A").Output)).Name);
        else
            AssertUnforwardable($"{callee}\n{definition}\n0", rejected);
    }

    /// <summary>
    /// Bare forwarding is not positional: every target parameter takes the source binding of its OWN
    /// name, so the source's order is irrelevant and the call follows the target's order.
    /// </summary>
    [Theory]
    [InlineData("G(x, y) = F\nG(10, 3)", "ok -7")]
    [InlineData("G(y, x) = F\nG(10, 3)", "ok 7")]
    [InlineData("G(x, y) = F(x, y)\nG(10, 3)", "ok 7")]
    [InlineData("G(x, y) = F(y, x)\nG(10, 3)", "ok -7")]
    public async Task BareForwarding_IsNotPositional(string program, string expected)
        => Assert.Equal(expected, await Outcome("F(y, x) = y - x\n" + program));

    /// <summary>
    /// A Math function is forwarded by the names of its registry signature like any callee
    /// (<c>sqrt(x)</c>, <c>pow(x, y)</c>, <c>randomInt(start, end)</c>): the same names forward
    /// through the alias and the qualified <c>Math.X</c> spelling alike, a swapped list is still by
    /// name, and another name is rejected, never renamed.
    /// </summary>
    [Theory]
    [InlineData("R(x) = sqrt\nR(9)", "ok 3")]
    [InlineData("R(x) = Math.Sqrt\nR(9)", "ok 3")]
    [InlineData("P(x, y) = pow\nP(2, 3)", "ok 8")]
    [InlineData("P(y, x) = pow\nP(2, 3)", "ok 9")]
    [InlineData("D(start, end) = randomInt\nD(4, 5)", "ok 4")]
    [InlineData("R(value) = sqrt\nR(9)", null)]
    public async Task MathFunctions_AreForwardedByTheirSignatureNames(string program, string? expected)
    {
        if (expected is null)
            AssertUnforwardable(program, "x");
        else
            Assert.Equal(expected, await Outcome(program));
    }

    // ── 5. Closed lists and closed formulas ───────────────────────────────────────────────

    /// <summary>
    /// An explicit parameter list is closed: bare forwarding never adds a missing callee parameter to
    /// it, while unused source parameters are fine and the list is always exactly the written one.
    /// </summary>
    [Fact]
    public async Task AClosedList_NeverGainsTheCalleesOtherParameters()
    {
        AssertUnforwardable("F(x, y, z) = x + y + z\nG(x) = F\n0", "y", "z");
        var g = Owner(SourceProvenance.ParseValid("F(x) = x\nG(x, y, z) = F\n0").Root, "G");
        Assert.Equal("x, y, z", Signature(g));
        Assert.Equal("ok 1", await Outcome("F(x) = x\nG(x, y, z) = F\nG(1, 2, 3)"));
    }

    /// <summary>
    /// A FORMULA body under a closed list keeps formula lifting's closed-list rule (PAR-04): it may
    /// use the list's own same-named bindings and an enclosing parameter binding (Q-04), and a
    /// callee parameter neither supplies leaves the reference the zero-argument demand — the
    /// program compiles and that demand fails at run time; nothing is renamed or added either way.
    /// </summary>
    [Theory]
    [InlineData("F(p) = p * 2\nA(p) = F + 1\nA(5)", "ok 11")]
    [InlineData("F(q) = q * 2\nA(p) = F + 1\nA(5)", "err ArityMismatch: while evaluating call to A: Property 'F' expects 1 parameter, but was called with 0 arguments.")]
    [InlineData("F(q) = q * 2\nOuter(q) = {\n  A(p) = F + 1\n  A(5)\n}\nOuter(3)", "ok 7")]
    [InlineData("F(q) = q * 2\nOuter(q) = {\n  A(p) = F\n  A(5)\n}\nOuter(3)", "ok 6")]
    public async Task AClosedFormula_UsesOnlyExistingBindings_AndNeverRenames(string program, string expected)
        => Assert.Equal(expected, await Outcome(program));

    [Theory]
    [InlineData("F(p) = p * 2\nA(p) = F + 1")]
    [InlineData("F(q) = q * 2\nA(p) = F + 1")]
    public void AClosedFormula_KeepsItsWrittenSignature(string program)
        => Assert.Equal("p", Signature(Owner(SourceProvenance.ParseValid(program + "\n0").Root, "A")));

    // ── 6. Structural compatibility is top-level pattern compatibility ──────────────────

    /// <summary>
    /// A structural callee parameter is supplied only by a source parameter with the SAME contract —
    /// kind, shape, names, collectors — never assembled from same-named leaves and never unwrapped
    /// into an element; a clause head item that holds a literal declares no literal-free pattern.
    /// (callee, definition, argument, outcome — or null when the definition is rejected)
    /// </summary>
    [Theory]
    [InlineData("F([x, y]) = x + y", "G([x, y]) = F", "[1, 2]", "ok 3")]
    [InlineData("F([x, y]) = x + y", "G([y, x]) = F", "[1, 2]", null)]
    [InlineData("F((x, *rest)) = [x, rest]", "G((x, *rest)) = F", "(1, 2, 3)", "ok L[1, L[2, 3]]")]
    [InlineData("F((x, *rest)) = [x, rest]", "G(x, *rest) = F", "1, 2, 3", null)]
    [InlineData("F([*xs]) = xs", "G([*xs]) = F", "[1, 2]", "ok L[1, 2]")]
    [InlineData("F([*xs]) = xs", "G(*xs) = F", "1, 2", null)]
    [InlineData("F(([x, y], z)) = [x, y, z]", "G(([x, y], z)) = F", "([1, 2], 3)", "ok L[1, 2, 3]")]
    [InlineData("F(([x, y], z)) = [x, y, z]", "G([x, y], z) = F", "[1, 2], 3", null)]
    public async Task StructuralForwarding_NeedsTheSamePattern(string callee, string definition, string argument, string? expected)
    {
        var program = $"{callee}\n{definition}\n";
        if (expected is null)
        {
            Assert.All(
                SourceProvenance.ExpectFrontEndError(program + "0"),
                static diagnostic => Assert.Equal(DiagnosticCode.UnforwardableParameter, diagnostic.Code));
            return;
        }

        Assert.Equal(expected, await Outcome(program + $"G({argument})"));
    }

    /// <summary>
    /// A clause branch forwards from its HEAD by name: its top-level binders and its literal-free
    /// groups. A literal is never forwarded (it binds nothing), so a branch that binds no name the
    /// callee needs is rejected, and a group holding a literal declares no pattern.
    /// </summary>
    [Fact]
    public async Task AClauseBranch_ForwardsItsHeadByName()
    {
        Assert.Equal("ok S[5, 30]", await Outcome("F(n) = n * 10\nG(0) = 5\nG(n) = F\nG(0), G(3)"));
        Assert.Equal("ok S[L[1, 2], 0]", await Outcome("Id([a, b]) = [a, b]\nG([a, b]) = Id\nG(n) = 0\nG([1, 2]), G(5)"));
        Assert.Equal("ok S[5, 0]", await Outcome("F(y) = y\nG(0, y) = F\nG(k, y) = 0\nG(0, 5), G(1, 5)"));
        AssertUnforwardable("F(n) = n * 10\nG(0) = F\nG(n) = 1\n0", "n");
        AssertUnforwardable("Single([x]) = x\nG([0, x]) = Single\nG(n) = 0\n0", "[x]");
    }

    /// <summary>
    /// Branch bodies sharing ONE bare-forwarding body share its rewrite when their heads have the
    /// same structure — literal VALUES never split a region (a literal is never forwarded) — while a
    /// head whose literal sits in another position gets a region of its own.
    /// </summary>
    [Fact]
    public void BranchesSharingABareForwardingBody_ShareItsRewriteByHeadStructure()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot("F(n) = n\n0");
        var body = new Algorithm.User(null, [], [], [], new OutputBundle([new Expr.Resolve("F")]));
        var family = new Algorithm.Conditional(null, [],
        [
            .. Enumerable.Range(0, 3).Select(i => new CondBranch(new Pattern.SequenceValue([new Pattern.LitInt(i), new Pattern.Bind("n")]), body)),
            new CondBranch(new Pattern.SequenceValue([new Pattern.Bind("n"), new Pattern.LitInt(0)]), body),
            new CondBranch(new Pattern.SequenceValue([new Pattern.Bind("k"), new Pattern.Bind("n")]), body),
        ]);
        root = root with { Properties = [.. root.Properties, new Property("G", family)] };
        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(root);
        Assert.Empty(diagnostics);
        var resolved = Assert.IsType<Algorithm.User>(ImplicitArgumentResolver.ResolvePrevalidated(detected));
        var branches = Assert.IsType<Algorithm.Conditional>(resolved.Properties.Single(property => property.Name == "G").Value).Branches;
        Assert.All(branches, branch => Assert.Equal("n", Arguments(LoneCall(Assert.IsType<Algorithm.User>(branch.Body), "F").Args)));
        Assert.Same(branches[0].Body, branches[1].Body);
        Assert.Same(branches[0].Body, branches[2].Body);
        Assert.NotSame(branches[0].Body, branches[3].Body);
    }

    // ── 7. Written calls: parameters are the free names written in the arguments ───────

    /// <summary>(callee, formula body, the inferred signature, a call of the formula, its outcome)</summary>
    public static TheoryData<string, string, string, string, string> WrittenCalls => new()
    {
        { "Add((a, b)) = a + b", "Add((x, y))", "x, y", "2, 3", "ok 5" },
        { "Add((a, b)) = a + b", "Add((y, x))", "y, x", "2, 3", "ok 5" },
        { "Single([a]) = a", "Single([x])", "x", "7", "ok 7" },
        { "Single([a]) = a", "Single([[x]])", "x", "7", "ok L[7]" },
        { "Two(a, b) = [a, b]", "Two(x, x)", "x", "7", "ok L[7, 7]" },
        { "Two(a, b) = [a, b]", "Two([x, y], (y, z))", "x, y, z", "1, 2, 3", "ok L[L[1, 2], S[2, 3]]" },
        { "Coll(*vs) = vs", "Coll(xs*, y)", "xs, y", "(1, 2), 3", "ok L[1, 2, 3]" },
        { "P(x, x) = x", "P(q, q)", "q", "7", "ok 7" },
        { "P(x, x) = x", "P(q, r)", "q, r", "7, 8", "err ArityMismatch: while evaluating call to G: while evaluating call to P: repeated parameter 'x' requires equal arguments: Bad arity" },
        { "Add((a, b)) = a + b", "Add((x + 1, y * 2))", "x, y", "2, 3", "ok 9" },
        { "Add((a, b)) = a + b", "Add((x~, y))", "y, x", "2, 3", "ok 5" },
    };

    /// <summary>
    /// THE WRITTEN-CALL INFERENCE LAW: <c>G = F(exprs)</c> infers exactly the free names written in
    /// <c>exprs</c>, in first-appearance order with the ordinary Grace arithmetic, and is the
    /// explicit <c>G(names) = F(exprs)</c> on every route.
    /// </summary>
    [Theory]
    [MemberData(nameof(WrittenCalls))]
    public async Task AWrittenCall_InfersTheFreeNamesItWrites(string callee, string formula, string signature, string arguments, string expected)
    {
        var implicitProgram = $"{callee}\nG = {formula}\n";
        var explicitProgram = $"{callee}\nG({signature}) = {formula.Replace("~", "", StringComparison.Ordinal)}\n";
        Assert.Equal(signature, Signature(Owner(SourceProvenance.ParseValid(implicitProgram + "0").Root, "G")));
        Assert.Equal(expected, await Outcome(implicitProgram + $"G({arguments})"));
        Assert.Equal(expected, await Outcome(explicitProgram + $"G({arguments})"));
    }

    /// <summary>(a callee, the same callee with every binder renamed, a supply)</summary>
    public static TheoryData<string, string, string> RenamedCallees => new()
    {
        { "Add((a, b)) = a + b", "Add((left, right)) = left + right", "(2, 3)" },
        { "Single([x]) = x", "Single([item]) = item", "[7]" },
        { "P(x, x) = x", "P(q, q) = q", "7, 7" },
        { "Head(h, *rest) = [h, rest]", "Head(first, *others) = [first, others]", "1, 2, 3" },
        { "Mid((f, *m, l)) = [f, m, l]", "Mid((u, *v, w)) = [u, v, w]", "(1, 2, 3)" },
        { "LS([(x, y), z]) = x + y + z", "LS([(p, q), r]) = p + q + r", "[(1, 2), 3]" },
    };

    /// <summary>
    /// Renaming a callee's binders changes nothing an alias's callers or a written call observe: the
    /// alias's shape and behavior (its callable is the callee, so its names are the callee's), a
    /// written call's inferred signature, and every outcome on every route.
    /// </summary>
    [Theory]
    [MemberData(nameof(RenamedCallees))]
    public async Task RenamingCalleeBinders_ChangesNoAliasOrWrittenCall(string original, string renamed, string supply)
    {
        var callee = CalleeName(original);
        string Callers(string declaration) => $"{declaration}\nA = {callee}\nWritten = {callee}(s)\nExplicit(s) = {callee}(s)\n";

        var before = SourceProvenance.ParseValid(Callers(original) + "0").Root;
        var after = SourceProvenance.ParseValid(Callers(renamed) + "0").Root;
        Assert.Equal(Shape(AliasSignature(AliasOf(before, "A"))), Shape(AliasSignature(AliasOf(after, "A"))));
        Assert.Equal(Signature(Owner(after, callee)), AliasSignature(AliasOf(after, "A")));
        foreach (var owner in new[] { "Written", "Explicit" })
        {
            Assert.Equal(Signature(Owner(before, owner)), Signature(Owner(after, owner)));
            Assert.Equal(Arguments(LoneCall(Owner(before, owner), callee).Args), Arguments(LoneCall(Owner(after, owner), callee).Args));
        }

        foreach (var call in new[] { $"A({supply})", $"Written({supply})", $"Explicit({supply})" })
            Assert.Equal(await Outcome(Callers(original) + call), await Outcome(Callers(renamed) + call));
    }

    /// <summary>
    /// FORMULA LIFTING AND BARE FORWARDING ARE DIFFERENT MECHANISMS (decided September 30 2026): a
    /// formula lifts the callee's required
    /// parameter NAMES into its inferred signature, while a closed list only reuses existing
    /// bindings — the bare row is rejected at the front end, the closed formula keeps the
    /// zero-argument demand and fails at run time, and neither renames. With an enclosing binding of
    /// the callee's name both reuse it (Q-04).
    /// </summary>
    [Fact]
    public async Task FormulaLiftingAndBareForwarding_AreDeliberatelyDifferent()
    {
        Assert.Equal("x", Signature(Owner(SourceProvenance.ParseValid("F(x) = x * 2\nH = [F]:0\n0").Root, "H")));
        AssertUnforwardable("F(x) = x * 2\nG(q) = F\n0", "x");
        Assert.StartsWith(
            "err ArityMismatch: while evaluating call to G: Property 'F' expects 1 parameter, but was called with 0 arguments.",
            await Outcome("F(x) = x * 2\nG(q) = [F]:0\nG(7)"),
            StringComparison.Ordinal);
        Assert.Equal("ok 20", await Outcome("F(x) = x * 2\nOuter(x) = {\n  G(q) = [F]:0\n  G(7)\n}\nOuter(10)"));
        Assert.Equal("ok 20", await Outcome("F(x) = x * 2\nOuter(x) = {\n  G(q) = F\n  G(7)\n}\nOuter(10)"));
    }

    // ── 8. Repeated names, binderless groups, collectors, zero-argument callables ─────────

    /// <summary>
    /// A repeated-name callee through each mechanism: the alias takes P's two independent arguments
    /// that must agree (Q-05); bare forwarding supplies the one existing binding of the name to both
    /// occurrences (the established by-name rule), so its list needs only that name; a written
    /// <c>P(x, x)</c> reads the formula's one free name twice; two DIFFERENT source names are never
    /// merged into one.
    /// </summary>
    [Theory]
    [InlineData("A = P\nB = A\nB(7, 8)", "err ArityMismatch: while evaluating call to B: repeated parameter 'x' requires equal arguments: Bad arity")]
    [InlineData("G(x) = P\nG(7)", "ok 7")]
    [InlineData("G(x) = P\nG(trace(7))", "ok 7 [trace(7)]")]
    [InlineData("G(x, y) = P\nG(7, 8)", "ok 7")]
    [InlineData("G(x, x) = P\nG(7, 7)", "ok 7")]
    [InlineData("G(x, x) = P\nG(7, 8)", "err ArityMismatch: while evaluating call to G: repeated parameter 'x' requires equal arguments: Bad arity")]
    [InlineData("G = P(x, x)\nG(7)", "ok 7")]
    [InlineData("G = P(x, x)\nG(trace(7))", "ok 7 [trace(7)]")]
    [InlineData("A = P\nA(trace(7), trace(7))", "ok 7 [trace(7),trace(7)]")]
    [InlineData("A = P\nA(Inc, Inc)", "err ArityMismatch: while evaluating call to A: Property 'Inc' expects 1 parameter, but was called with 0 arguments.")]
    public async Task RepeatedNames_KeepTheCalleeContract(string program, string expected)
        => Assert.Equal(expected, await Outcome(Vocabulary + "P(x, x) = x\n" + program));

    /// <summary>
    /// A binderless structural parameter survives an alias: the alias keeps E's arity
    /// and kinds at every level. Bare forwarding supplies a binderless group only from the identical
    /// group of the source list.
    /// </summary>
    [Theory]
    [InlineData("A = E\nB = A\nB((), [])", "ok 1")]
    [InlineData("A = E\nA", "err ArityMismatch: Property 'A' expects 2 parameters, but was called with 0 arguments.")]
    [InlineData("A = E\nA([], ())", "err TypeMismatch: while evaluating call to A: Type mismatch: sequence pattern `()` expects a sequence value, but received a list value with 0 elements: []")]
    [InlineData("A = E\nA((1, 2), [])", "err ArityMismatch: Sequence pattern `()` expects 0 elements, but received 2 elements.")]
    [InlineData("G((), []) = E\nG((), [])", "ok 1")]
    [InlineData("M = ME\nM(7, ())", "ok 7")]
    [InlineData("M = ME\nM(7)", "err ArityMismatch: Callable `M(x, ())` expects 2 arguments, but was called with 1 argument.")]
    [InlineData("G(x, ()) = ME\nG(7, ())", "ok 7")]
    public async Task BinderlessGroups_SurviveAliasesAndBareForwarding(string program, string expected)
        => Assert.Equal(expected, await Outcome("E((), []) = 1\nME(x, ()) = x\n" + program));

    [Fact]
    public void BinderlessAlias_IsTheBinderlessCallee()
    {
        var root = SourceProvenance.ParseValid("E((), []) = 1\nA = E\nB = A\n0").Root;
        Assert.Equal("(), []", AliasSignature(AliasOf(root, "A")));
        Assert.Equal("(), []", AliasSignature(AliasOf(root, "B")));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(AliasOf(root, "B").Target).Name);
    }

    /// <summary>
    /// Collectors keep their kind (FWD-01, FWD-02's source-kind rule): a collecting source re-spreads
    /// into the same-named collecting target, a fixed source is ONE item for it and a collected list
    /// is ONE argument for a fixed target — never spread, never reinterpreted — and a target collector
    /// no source name matches receives nothing.
    /// </summary>
    [Theory]
    [InlineData("F(*xs) = xs\nA(*xs) = F\nA(), A(1), A(1, 2)", "ok S[L[], L[1], L[1, 2]]")]
    [InlineData("F(*xs) = xs\nA(xs) = F\nA([1, 2])", "ok L[L[1, 2]]")]
    [InlineData("F(xs) = xs\nA(*xs) = F\nA(1, 2)", "ok L[1, 2]")]
    [InlineData("F(p, *rest) = [p, rest]\nA(p, *rest) = F\nA(1, 2, 3)", "ok L[1, L[2, 3]]")]
    [InlineData("F(p, *rest) = [p, rest]\nA(p) = F\nA(1)", "ok L[1, L[]]")]
    [InlineData("F(*rest, z) = [rest, z]\nA(z) = F\nA(9)", "ok L[L[], 9]")]
    [InlineData("F(*xs) = xs\nA(p) = F\nA(5)", "ok L[]")]
    public async Task Collectors_KeepTheirKind(string program, string expected)
        => Assert.Equal(expected, await Outcome(program));

    /// <summary>
    /// A callable that also works with no arguments, but DECLARES a (collecting) parameter: its lone
    /// row is a CALLABLE ALIAS whose callable is the callee (FWD-02 supersedes Q-03's alias clause),
    /// and its BARE name is still a cached zero-argument read (Q-03) of the alias's own binding — one
    /// evaluation for the alias, one for the callee — while <c>A()</c> is fresh. Under a closed list,
    /// bare forwarding that supplies nothing reads the CALLEE's cached value; one that supplies a
    /// binding is a call.
    /// </summary>
    [Theory]
    [InlineData("A = Cnt\nA(1, 2, 3), A(), A", "ok S[3, 0, 0]")]
    [InlineData("A = Cnt\nmap([1, 2], A), map([(10, 7), 20], A)", "ok S[L[1, 1], L[1, 1]]")]
    [InlineData("A = Cnt\nA == A", "ok true")]
    [InlineData("A = Only\nA(), A(), A", "ok S[1, 2, 3] [tick#1,tick#2,tick#3]")]
    [InlineData("A = Only\nOnly, Only, A, A", "ok S[1, 1, 2, 2] [tick#1,tick#2]")]
    [InlineData("W(p) = Only\nW(1), W(2), Only", "ok S[1, 1, 1] [tick#1]")]
    [InlineData("W(*xs) = Only\nW(1), W(2)", "ok S[1, 2] [tick#1,tick#2]")]
    [InlineData("G(*xs) = Cnt\nG(), G(1), G(1, 2)", "ok S[0, 1, 2]")]
    [InlineData("G(xs) = Cnt\nG((1, 2))", "ok 1")]
    public async Task ZeroArgumentCallables_AreAliasedForwardedOrRead(string program, string expected)
        => Assert.Equal(expected, await Outcome("Cnt(*xs) = xs.count\nOnly(*xs) = tick()\n" + program));

    /// <summary>
    /// A zero-parameter target under bare forwarding is its cached value however often the
    /// forwarding definition is called (E), a random-producing property included; an explicit call
    /// of it stays fresh.
    /// </summary>
    [Theory]
    [InlineData("A(p) = Cached\nA(1), A(2), Cached", "ok S[1, 1, 1] [tick#1]")]
    [InlineData("A(p) = Rand\nA(1) == A(2), A(1) == Rand", "ok S[true, true]")]
    [InlineData("A(p) = Cached()\nA(1), A(2)", "ok S[1, 2] [tick#1,tick#2]")]
    public async Task AZeroParameterTarget_IsItsCachedValue(string program, string expected)
        => Assert.Equal(expected, await Outcome("Cached = tick()\nRand = randomInt(1, 1000000)\n" + program, seed: 7));

    /// <summary>
    /// A clause family declares parameterized callable structure (dispatch over its clause heads), so
    /// its lone row is a CALLABLE ALIAS (binding indirection, October 2026): the alias call is the
    /// family's own dispatch, including its cardinality rejection. A nameable family is also a bare-forwarding target through its derived
    /// whole-slot contract (<c>W(n) = F</c> is <c>W(n) = F(n)</c>).
    /// </summary>
    [Fact]
    public async Task AClauseFamily_IsAnAliasAndAForwardingTarget()
    {
        const string family = "F(0) = 1\nF(n) = n\n";
        Assert.Equal("ok 3", await Outcome(family + "A = F\nA(3)"));
        Assert.Equal("ok 1", await Outcome(family + "A = F\nA(0)"));
        Assert.Equal("err ArityMismatch: Property 'A' expects 1 parameter, but was called with 2 arguments.", await Outcome(family + "A = F\nA(1, 2)"));
        var alias = AliasOf(SourceProvenance.ParseValid(family + "A = F\n0").Root, "A");
        Assert.IsType<Algorithm.Conditional>(alias.ResolvedTarget!.Algorithm);
        Assert.Equal("ok 3", await Outcome(family + "W(n) = F\nW(3)"));
    }

    // ── 9. Effects, caching and random draws are exactly once ────────────────────────────

    /// <summary>
    /// Forwarding re-evaluates nothing: every argument is evaluated once, whatever alias levels or
    /// by-name forwarding hand it on, exactly like the direct call — host calls, effects, failures,
    /// cached property reads and seeded random draws alike.
    /// </summary>
    [Theory]
    [InlineData("A = Eff\nA(trace(7))", "Eff(trace(7))")]
    [InlineData("A = Eff\nB = A\nB(trace(7))", "Eff(trace(7))")]
    [InlineData("G(v) = Eff\nG(trace(7))", "Eff(trace(7))")]
    [InlineData("G([v]) = LEff\nG([trace(7)])", "LEff([trace(7)])")]
    [InlineData("G(*vs) = Eff2\nG(trace(1), trace(2))", "Eff2(trace(1), trace(2))")]
    [InlineData("G((a, b)) = Pair2\nH((a, b)) = G\nH((trace(1), trace(2)))", "Pair2((trace(1), trace(2)))")]
    [InlineData("A = Eff\nA(Bad)", "Eff(Bad)")]
    [InlineData("G(v) = Eff\nG(Bad)", "Eff(Bad)")]
    [InlineData("A = Eff2\nA(tick(), tick())", "Eff2(tick(), tick())")]
    [InlineData("G(a, b) = Eff3\nG(randomInt(0, 99), randomInt(0, 99)), randomInt(0, 99)", "Eff3(randomInt(0, 99), randomInt(0, 99)), randomInt(0, 99)")]
    [InlineData("A = Eff3\nA(Cached, Cached), Cached", "Eff3(Cached, Cached), Cached")]
    [InlineData("G(a, b) = Eff3\nG(Cached, Cached()), Cached", "Eff3(Cached, Cached()), Cached")]
    [InlineData("G(a, b) = Eff3\nG(Rand, Rand), Rand", "Eff3(Rand, Rand), Rand")]
    [InlineData("G(a, b) = Eff3\nG(Rand, Rand()), Rand", "Eff3(Rand, Rand()), Rand")]
    [InlineData("Outer(a, b) = {\n  Local(q) = Eff3\n  Local(0)\n}\nOuter(trace(1), trace(2))", "Eff3(trace(1), trace(2))")]
    [InlineData("Outer(a, b) = {\n  Local(q) = Eff3\n  Local(0), Local(1)\n}\nOuter(Rand, tick())", "Eff3(Rand, tick()), Eff3(Rand, 1)")]
    public async Task ForwardingEvaluatesEveryArgumentExactlyOnce(string program, string direct)
    {
        const string prelude = Vocabulary
            + "Eff(v) = trace(v), tick()\nLEff([v]) = trace(v), tick()\nEff2(*vs) = vs, tick()\nEff3(a, b) = [a, b], tick()\n"
            + "Pair2((a, b)) = [a, b], tick()\nCached = tick()\nRand = randomInt(1, 1000000)\n";
        var implicitObservation = await OnEveryRoute(prelude + program, seed: 3);
        var directObservation = await OnEveryRoute(prelude + direct, seed: 3);
        Assert.Equal(directObservation.HostCalls, implicitObservation.HostCalls);
        Assert.Equal(directObservation.Outcome.Split(':')[0], implicitObservation.Outcome.Split(':')[0]);
    }

    // ── 10. Nested scopes, callbacks and dot calls ────────────────────────────────────────

    /// <summary>
    /// Q-04 decides which EXISTING binding a name denotes, and bare forwarding reuses exactly that
    /// one: a local list's own parameter first, else an enclosing parameter binding — never a
    /// property, and never renamed. A local ALIAS preserves the callee instead and reuses nothing.
    /// </summary>
    [Theory]
    [InlineData("Outer(x) = {\n  Local = F\n  Local(5) + x\n}\nOuter(100)", "ok 110")]
    [InlineData("Outer(x) = {\n  Local(y) = F\n  Local(5)\n}\nOuter(100)", "ok 200")]
    [InlineData("Outer(x) = {\n  Local(x) = F\n  Local(5)\n}\nOuter(100)", "ok 10")]
    [InlineData("Outer(x) = {\n  Local(y) = F(y)\n  Local(5)\n}\nOuter(100)", "ok 10")]
    [InlineData("Outer(x) = {\n  Local = F\n  Local\n}\nOuter(100)", "ok 200")]
    [InlineData("A = y + 1\nG = {\n  F(x) = A\n  F(1) + y\n}\nG(10)", "ok 21")]
    [InlineData("x = 3\nOuter(q) = {\n  Local(p) = F\n  Local(5)\n}\nOuter(1)", null)]
    public async Task NestedScopes_ReuseTheBindingANameDenotes(string program, string? expected)
    {
        if (expected is null)
        {
            AssertUnforwardable("F(x) = x * 2\n" + program, "x");
            return;
        }

        Assert.Equal(expected, await Outcome("F(x) = x * 2\n" + program));
    }

    [Theory]
    [InlineData("map([[1], [2]], A)", "map([[1], [2]], Single)")]
    [InlineData("map([[1], [2]], B)", "map([[1], [2]], Single)")]
    [InlineData("[7].A, [7].B, [[7]].C", "[7].Single, [7].Single, [[7]].Single")]
    [InlineData("(2, 3).Q", "(2, 3).Add")]
    [InlineData("filter([[1], [2]], { A == 1 })", "filter([[1], [2]], { Single == 1 })")]
    [InlineData("reduce([[1], [2]], RA, 0)", "reduce([[1], [2]], R, 0)")]
    [InlineData("Apply(A, [7])", "Apply(Single, [7])")]
    public async Task CallbacksAndDotCalls_ReachTheAliasAsTheCallee(string aliased, string direct)
    {
        const string prelude = "Single([x]) = x\nAdd((a, b)) = a + b\nA = Single\nB([x]) = Single\nC(x) = Single(x)\n"
            + "Q = Add\nR(e, acc) = Single(e) + acc\nRA = R\nApply(f, v) = f(v)\n";
        Assert.Equal(await Outcome(prelude + direct), await Outcome(prelude + aliased));
    }

    // ── 11. Module text and the editor model ──────────────────────────────────────────────

    [Fact]
    public async Task LoadedModuleText_AliasesAndForwardsLikeTheDocument()
    {
        static RunOptions Serving(string module) => new() { DownloadCode = (_, _) => ValueTask.FromResult(module) };
        const string Module = "public Single([x]) = x\npublic A = Single\npublic B([x]) = Single\npublic P(x, x) = x\npublic Q = P\npublic W(x) = P";
        var result = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(
            "M = load('https://katlang.org/forwarding/alias.kat')\nM.A([7]), M.B([7]), M.Q(8, 8), M.W(9)", Serving(Module)));
        Assert.Equal([7m, 7m, 8m, 9m], result.Atoms);

        // Imported text is elaborated with the loading document, so the rejection is the ordinary
        // front-end diagnostic, positioned at the import site in the document's own coordinates.
        var rejected = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(
            "0\nM = load('https://katlang.org/forwarding/rejected.kat')\nM.G([7])", Serving("public Single([x]) = x\npublic G(x) = Single")));
        var error = Assert.Single(rejected.Errors);
        Assert.Equal(KatLangErrorCode.UnforwardableParameter, error.Code);
        Assert.Equal(2, error.Span?.Start.Line);
    }

    /// <summary>
    /// The editor shows an alias's TARGET signature (the alias declares none of its own), a
    /// bare-forwarding definition's WRITTEN one (never renamed to the callee's), a written call's
    /// inferred one and a formula's lifted one — and the target's parameters create no declaration
    /// site at the alias.
    /// </summary>
    [Theory]
    [InlineData("Add((a, b)) = a + b\nG = Add", "G", "G((a, b))")]
    [InlineData("Add((a, b)) = a + b\nG = Add((x, y))", "G", "G(x, y)")]
    [InlineData("Single([x]) = x\nG([x]) = Single", "G", "G([x])")]
    [InlineData("F(p) = p * 2\nA(p) = F", "A", "A(p)")]
    [InlineData("F(p) = p * 2\nA(p, unused) = F", "A", "A(p, unused)")]
    [InlineData("F(x) = x * 2\nA = F + 1", "A", "A(x)")]
    [InlineData("P(x, x) = x\nA = P", "A", "A(x, x)")]
    [InlineData("E((), []) = 1\nA = E", "A", "A((), [])")]
    [InlineData("C(*xs) = xs\nA = C", "A", "A(*xs)")]
    [InlineData("C([*xs]) = xs\nA = C", "A", "A([*xs])")]
    [InlineData("C((*xs)) = xs\nA = C", "A", "A((*xs))")]
    [InlineData("Single([x]) = x\nA = Single\nB = A", "B", "B([x])")]
    public void EditorSignatures_ShowTargetWrittenInferredAndLiftedParameters(string source, string name, string signature)
    {
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source + "\n0").Parsed);
        Assert.Equal(signature, Assert.Single(model.FindProperties(name)).DisplaySignature);
    }

    [Fact]
    public void AnAliasRow_ResolvesToItsCallee_AndItsTargetParametersHaveNoSiteThere()
    {
        const string source = "Add((a, b)) = a + b\nG = Add\nG((1, 2))";
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        var reference = model.FindResolutionAt(new SourcePosition(2, 5));
        Assert.NotNull(reference);
        Assert.Equal("Add", reference.ResolvedProperty?.Name);
        Assert.Equal(new SourceSpan(1, 1, 1, 4), reference.ResolvedDeclaration!.Span);

        // `a` and `b` are declared once, at Add's own binders, and read in Add's body; line 2 has no site for them.
        var sites = model.IdentifierOccurrences.Concat(model.Declarations).Where(static site => site.Name is "a" or "b").ToList();
        Assert.All(sites, static site => Assert.Equal(1, site.Span.Start.Line));
    }

    [Fact]
    public void ARejectedForwardingRow_StillResolvesToItsCalleeInTheEditor()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("F(q) = q * 2\nA(p) = F\n0").Parsed;
        Assert.Contains(parsed.Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.UnforwardableParameter);
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Equal("F", model.FindResolutionAt(new SourcePosition(2, 8))?.ResolvedProperty?.Name);
        Assert.Equal("A(p)", Assert.Single(model.FindProperties("A")).DisplaySignature);
    }
}
