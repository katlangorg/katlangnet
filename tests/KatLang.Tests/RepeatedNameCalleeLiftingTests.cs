using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// NO IMPLICIT FORWARDING INTO A REPEATED-NAME CALLEE (Q-72, decided September 29 2026).
///
/// <para>A callable whose parameter patterns repeat a binding name — <c>P(x, x)</c>,
/// <c>P((x, a), x)</c>, <c>P((x, y), (z, x))</c>, <c>P((x, *rest), x)</c>, at any depth — never
/// takes part in implicit parameter forwarding. A bare reference to it in a lifting position
/// (an alias row, an operator, comparison, or unary operand, a list element, an index part, a
/// spread operand, a strict Math argument or dot-fallback receiver, a deconstruction right-hand
/// side, a block row) is left unlifted and reported as the front-end error
/// <see cref="DiagnosticCode.RepeatedParameterNotForwardable"/> at the reference, in open and
/// closed bodies alike; the program writes the call instead (<c>Alias(a, b) = P(a, b)</c>, or
/// <c>Same(x) = P(x, x)</c> to supply one value to both occurrences).</para>
///
/// <para>THE INVARIANT: repeated occurrences represent independently supplied inputs whose
/// compatibility is checked at binding time (Q-05, <see cref="RepeatedNameConstraintTests"/>).
/// No implicit transformation may collapse those occurrences into one input unless the source
/// explicitly supplies that same input to each occurrence. Automatic forwarding is BY NAME, so
/// before the decision it did exactly that: <c>P(x, x) = x</c> / <c>Alias = P</c> elaborated to
/// <c>Alias(x) = P(x, x)</c> — one parameter forwarded to both slots — so the alias took one
/// argument where P takes two, and P's equality constraint held by construction; an existing
/// binding fed every slot of its name the same way (<c>Q(x) = P</c> became
/// <c>Q(x) = P(x, x)</c>). Nothing else changed: by-name sharing ACROSS callees
/// (<c>H = F + G</c>), callables that accept zero supplied arguments (Q-03), neutral positions
/// (a call argument, a callee, a callback), opened and structural names, and a bare ROOT row
/// (the callable's own zero-argument demand) behave as before.</para>
///
/// <para>Lean states the decision (<c>refusesImplicitForwarding</c>,
/// <c>bareValueReferenceTreatment</c>; laws <c>repeated_name_callee_is_never_lifted</c>,
/// <c>lifted_callee_binds_each_capture_name_once</c>) and evaluates the explicit forms
/// (<c>CoreTests/RepeatedNameConstraints.lean</c>); the refusal itself is a C# front-end rule.</para>
/// </summary>
public class RepeatedNameCalleeLiftingTests
{
    private const string P = "P(x, x) = x\n";

    private static string RefusalMessage(string callee = "P", string repeated = "x")
        => string.Join(
            Environment.NewLine,
            $"'{callee}' is used here without arguments, but its arguments cannot be forwarded implicitly: "
                + $"its parameter list repeats '{repeated}'.",
            "Each occurrence of a repeated parameter takes its own argument, so implicit forwarding cannot supply them. "
                + $"Call '{callee}' with explicit arguments instead, for example in a wrapper that declares its own parameters.");

    private static string Display(string source)
        => KatLangEngine.Run(source) switch
        {
            RunResult.Success success => success.ToDisplayString().ReplaceLineEndings("\n"),
            RunResult.EvalFailure failure => "err " + string.Join(",", failure.Errors.Select(static error => $"{error.Code}: {error.Message}")),
            RunResult.ParseFailure failure => "parse " + string.Join(",", failure.Errors.Select(static error => error.Code)),
            var other => other.GetType().Name,
        };

    private static Algorithm.User Property(Algorithm.User root, string name)
        => Assert.IsType<Algorithm.User>(root.Properties.Single(property => property.Name == name).Value);

    /// <summary>
    /// Requires the front end to report EXACTLY the given refusals — nothing else — each at the
    /// written reference, with the one code, severity, and message.
    /// </summary>
    private static ParseResult AssertRefusedAt(string source, params (int Line, int Column)[] references)
        => AssertRefusedAt(source, "P", "x", references);

    private static ParseResult AssertRefusedAt(
        string source, string callee, string repeated, params (int Line, int Column)[] references)
    {
        var parsed = Parser.Parse(source);
        var expected = references
            .Select(reference => new SourceSpan(reference.Line, reference.Column, reference.Line, reference.Column + callee.Length))
            .ToList();
        Assert.True(
            parsed.Diagnostics.Count == expected.Count,
            $"expected {expected.Count} diagnostic(s), got:\n{string.Join("\n", parsed.Diagnostics.Select(static d => $"[{d.Code}] {d.Span} {d.Message}"))}\nsource:\n{source}");
        Assert.All(parsed.Diagnostics, diagnostic =>
        {
            Assert.Equal(DiagnosticCode.RepeatedParameterNotForwardable, diagnostic.Code);
            Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
            Assert.Equal(RefusalMessage(callee, repeated), diagnostic.Message);
        });
        Assert.Equal(expected, parsed.Diagnostics.Select(static diagnostic => diagnostic.Span!.Value).ToList());
        return parsed;
    }

    // ── 1. The motivating alias ─────────────────────────────────────────────────────

    [Fact]
    public void AliasOfARepeatedNameCallee_IsRefusedAtTheReference_AndNothingIsLifted()
    {
        var parsed = AssertRefusedAt(P + "Alias = P\nAlias(7)", (2, 9));

        // Formerly `Alias(x) = P(x, x)`: now the alias gains no parameter and the reference
        // stays the bare written name — no synthesized call feeds both of P's slots.
        var alias = Property(parsed.Root, "Alias");
        Assert.Empty(alias.ParameterPatterns);
        Assert.Null(alias.ForwardingParameterStart);
        Assert.Equal("P", Assert.IsType<Expr.Resolve>(Assert.Single(alias.Output)).Name);

        // The host sees ONE structured front-end error and nothing is evaluated.
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(P + "Alias = P\nAlias(7)"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.RepeatedParameterNotForwardable, error.Code);
        Assert.Equal(new SourceSpan(2, 9, 2, 10), error.Span);
        Assert.Equal(RefusalMessage(), error.Message);
    }

    [Fact]
    public async Task AliasRefusal_IsTheSameOnTheAsyncFrontEnd()
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(P + "Alias = P\nAlias(7)"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.RepeatedParameterNotForwardable, error.Code);
        Assert.Equal(new SourceSpan(2, 9, 2, 10), error.Span);

        var parsed = await Parser.ParseAsync(P + "Alias = P\nAlias(7)");
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.RepeatedParameterNotForwardable, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 9, 2, 10), diagnostic.Span);
    }

    [Fact]
    public void RefusedReference_StillResolvesToTheCalleeForEditorTooling()
    {
        var parsed = AssertRefusedAt(P + "Alias = P\nAlias(7)", (2, 9));
        var model = SemanticModelBuilder.Build(parsed);

        var reference = model.FindResolutionAt(new SourcePosition(2, 9));
        Assert.NotNull(reference);
        Assert.Equal("P", reference.ResolvedProperty?.Name);
        Assert.Equal(new SourceSpan(1, 1, 1, 2), reference.ResolvedDeclaration!.Span);
    }

    // ── 2. Repeated names at any depth ──────────────────────────────────────────────

    /// <summary>
    /// The refusal reads the callee's semantic binding structure — every capture of its
    /// flattened parameter patterns, at any nesting depth, a collector included — and names
    /// the first capture, left to right, that an earlier capture already binds.
    /// </summary>
    [Theory]
    [InlineData("P(x, x) = x", "x")]
    [InlineData("P(x, x, x) = x", "x")]
    [InlineData("P(x, y, x) = y", "x")]
    [InlineData("P((x, a), x) = a", "x")]
    [InlineData("P(x, (x, a)) = a", "x")]
    [InlineData("P((x, y), (z, x)) = y + z", "x")]
    [InlineData("P((x, *rest), x) = rest", "x")]
    [InlineData("P(x, *rest, x) = rest", "x")]
    [InlineData("P((x, x)) = x", "x")]
    [InlineData("P(((x, a)), x) = a", "x")]
    [InlineData("P(x, y, y, x) = x", "y")]
    [InlineData("P(y, x, x, y) = x", "x")]
    [InlineData("P(a, (b, c), (c, a)) = b", "c")]
    public void RepeatedNamesAtAnyDepth_AreRefused(string declaration, string repeated)
        => AssertRefusedAt(declaration + "\nAlias = P\n0", "P", repeated, (2, 9));

    /// <summary>
    /// Different callables' parameters never meet: the same spelling in two signatures, in a
    /// nested scope, or in a nested helper is no repetition.
    /// </summary>
    [Theory]
    [InlineData("F(x) = x + 1\nG(x) = x * 2\nH = F + G\nH(3)", "10")]
    [InlineData("P(x) = { Inner(x) = x * 2\nInner(x) + x }\nAlias = P\nAlias(3)", "9")]
    [InlineData("P(x, y) = x + y\nQ(x, y) = x * y\nD = P + Q\nD(2, 3)", "11")]
    [InlineData("P((x, a), y) = a + y\nAlias = P\nAlias((1, 2), 3)", "5")]
    public void SameSpellingInSeparateScopes_IsNoRepetition(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, Display(source));
    }

    // ── 3. An existing binding never feeds the repeated occurrences ─────────────────

    /// <summary>
    /// The refusal precedes every forwarding decision: a same-named caller parameter — written,
    /// inferred, captured from an enclosing owner, or a clause-branch binder — would have fed
    /// every occurrence from ONE binding (formerly <c>Q(x) = P(x, x)</c>), and a closed list
    /// lacking the name no longer leaves a doomed zero-argument demand for run time.
    /// </summary>
    [Theory]
    [InlineData(P + "Q(x) = P\nQ(7)", 2, 8)]
    [InlineData(P + "Q(y) = P\nQ(7)", 2, 8)]
    [InlineData(P + "Q(x) = P + x\nQ(7)", 2, 8)]
    [InlineData(P + "Q = x + P\nQ(7)", 2, 9)]
    [InlineData(P + "Outer(x) = {\n  Inner = P\n  Inner\n}\nOuter(7)", 3, 11)]
    [InlineData(P + "F(0) = 0\nF(x) = P + x\nF(7)", 3, 8)]
    [InlineData(P + "F(0) = 0\nF(y) = P\nF(7)", 3, 8)]
    public void ExistingSameNamedBinding_NeverFeedsTheRepeatedOccurrences(string source, int line, int column)
    {
        var parsed = AssertRefusedAt(source, (line, column));
        Assert.DoesNotContain(
            AllExpressions(parsed.Root),
            expr => expr is Expr.Call { Function: Expr.Resolve { Name: "P" } });
    }

    [Fact]
    public void ClosedListWithTheSameName_KeepsItsOwnSignature()
    {
        var parsed = AssertRefusedAt(P + "Q(x) = P\nQ(7)", (2, 8));
        var q = Property(parsed.Root, "Q");
        Assert.Equal(["x"], q.Params);
        Assert.Equal("P", Assert.IsType<Expr.Resolve>(Assert.Single(q.Output)).Name);
    }

    [Fact]
    public void OpenOwnerWithAnInferredSameName_GainsNoForwardedParameter()
    {
        var parsed = AssertRefusedAt(P + "Q = x + P\nQ(7)", (2, 9));
        var q = Property(parsed.Root, "Q");
        Assert.Equal(["x"], q.Params);
        Assert.Null(q.ForwardingParameterStart);
    }

    // ── 4. Every lifting position refuses identically ───────────────────────────────

    /// <summary>
    /// (source, line, column of the refused reference). Each lifting position reports exactly
    /// one refusal — same code, severity, message — at the written reference, and nothing else.
    /// </summary>
    public static TheoryData<string, int, int> LiftingPositions => new()
    {
        { P + "D = P\nD(7)", 2, 5 },
        { P + "D = P + 1\nD(7)", 2, 5 },
        { P + "D = 1 + P\nD(7)", 2, 9 },
        { P + "D = P == 1\nD(7)", 2, 5 },
        { P + "D = 1 < P <= 3\nD(7)", 2, 9 },
        { P + "D = -P\nD(7)", 2, 6 },
        { P + "D = not P\nD(7)", 2, 9 },
        { P + "D = [P, 1]\nD(7)", 2, 6 },
        { P + "D = P:0\nD(7)", 2, 5 },
        { P + "D = [1, 2]:P\nD(0)", 2, 12 },
        { P + "D = P*, 1\nD(7)", 2, 5 },
        { P + "D = sin(P)\nD(0)", 2, 9 },
        { P + "D = Math.Pow(P, 2)\nD(1)", 2, 14 },
        { P + "D = P.sin\nD(0)", 2, 5 },
        { P + "D = {\n  a, b = P\n  a\n}\nD", 3, 10 },
        { P + "D = { P }\nD", 2, 7 },
        { P + "D = {\n  Inner = P\n  Inner\n}\nD", 3, 11 },
        { P + "Apply(f) = f(1)\nApply({ P })", 3, 9 },
        { P + "P + 1", 2, 1 },
        { P + "Q(x) = P\nQ(7)", 2, 8 },
        // A strict Math position under a closed list or a branch pattern: the refusal precedes
        // the closed-list gate, so the blocked-forwarding diagnostic never joins it.
        { P + "Q(y) = sin(P)\nQ(0)", 2, 12 },
        { P + "F(0) = 0\nF(y) = P + y\nF(1)", 3, 8 },
        { P + "F(0) = 0\nF(y) = sin(P) + y\nF(1)", 3, 12 },
    };

    [Theory]
    [MemberData(nameof(LiftingPositions))]
    public void EveryLiftingPosition_RefusesIdentically(string source, int line, int column)
    {
        AssertRefusedAt(source, (line, column));
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.RepeatedParameterNotForwardable, Assert.Single(failure.Errors).Code);
    }

    /// <summary>A refused reference gives its owner no parameter, so nothing downstream lifts or cascades.</summary>
    [Theory]
    [InlineData(P + "A = P\nB = A\nB", 2, 5)]
    [InlineData(P + "A = P\nB = A + 1\nC = [B, A]\nC", 2, 5)]
    [InlineData(P + "Outer = {\n  Inner = P\n  Inner + 1\n}\nOuter", 3, 11)]
    [InlineData(P + "A = P\nUse(v) = v + A\nUse(1)", 2, 5)]
    public void RefusalDoesNotCascade(string source, int line, int column)
    {
        var parsed = AssertRefusedAt(source, (line, column));
        Assert.All(parsed.Root.Properties.Where(static property => property.Name != "P" && property.Name != "Use"),
            property => Assert.Empty(property.Value.Params));
    }

    [Fact]
    public void EachWrittenOccurrence_IsReportedOnce()
    {
        AssertRefusedAt(P + "D = P + P\nD(7)", (2, 5), (2, 9));
        AssertRefusedAt(P + "D = sin(P) + [P]:0\nD(0)", (2, 9), (2, 15));
        AssertRefusedAt(P + "A = P\nB = P\n0", (2, 5), (3, 5));
    }

    /// <summary>
    /// A host may share ONE node between a neutral-first and a strict-later position of one
    /// region: the strict-value observation re-walks the already rewritten node, which re-enters
    /// the refusal. The report stays one per occurrence per region, in either row order.
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void HostSharedReference_ReachedNeutrallyAndStrictly_ReportsOnce(bool strictRowFirst)
    {
        var sharedValue = new Expr.Unary(UnaryOp.Minus, new Expr.Resolve("P"));
        var strictRow = new Expr.DotCall(new Expr.Resolve("Math"), "Abs", new OutputBundle([sharedValue]));
        var repeated = new Algorithm.User(
            null,
            Algorithm.NormalParameters(["x", "x"]),
            [],
            [],
            [new Expr.Param("x")])
        {
            HasExplicitParameterList = true,
        };
        var owner = new Algorithm.User(null, [], [], [], strictRowFirst ? [strictRow, sharedValue] : [sharedValue, strictRow]);
        var root = new Algorithm.User(null, [], [], [new Property("P", repeated), new Property("D", owner)], []);

        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(root, observations: null, diagnostics);

        Assert.Equal(DiagnosticCode.RepeatedParameterNotForwardable, Assert.Single(diagnostics).Code);
        var d = resolved.Properties.Single(static property => property.Name == "D").Value;
        Assert.Empty(d.Params);
        var rows = d.Output.ToList();
        Assert.Same(rows[strictRowFirst ? 1 : 0], Assert.Single(Assert.IsType<Expr.DotCall>(rows[strictRowFirst ? 0 : 1]).Args!));
    }

    /// <summary>
    /// Module text is elaborated by the same resolver: an alias of a repeated-name callee inside a
    /// loaded module is refused like one in the document (imported content has no coordinates of
    /// its own, so the report stands at the import site), while a module's written wrapper works.
    /// </summary>
    [Fact]
    public async Task LoadedModuleText_FollowsTheSameRule()
    {
        static RunOptions Serving(string module) => new() { DownloadCode = (_, _) => ValueTask.FromResult(module) };
        const string Document = "M = load('https://katlang.org/q72/module.kat')\nM.Both(7, 7)";

        var refused = Assert.IsType<RunResult.ParseFailure>(
            await KatLangEngine.RunAsync(Document, Serving("public P(x, x) = x\npublic Both = P")));
        var error = Assert.Single(refused.Errors);
        Assert.Equal(KatLangErrorCode.RepeatedParameterNotForwardable, error.Code);
        // The import site of a module spliced as a property is that property's declaration (`M`).
        Assert.Equal(new SourceSpan(1, 1, 1, 2), error.Span);

        var written = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync(Document, Serving("public P(x, x) = x\npublic Both(a, b) = P(a, b)")));
        Assert.Equal([7m], written.Atoms);
    }

    /// <summary>
    /// The resolver refuses only in its user-property arm: the Math alias and canonical
    /// <c>Math.X</c> arms, and every other builtin signature, never repeat a parameter name, and
    /// host operations reject a duplicate name when they are created. Pinned here so that arm
    /// asymmetry stays a checked fact rather than an assumption.
    /// </summary>
    [Fact]
    public void BuiltinAndMathSignatures_NeverRepeatAParameterName()
    {
        foreach (var builtin in Enum.GetValues<BuiltinId>())
        {
            foreach (var style in Enum.GetValues<BuiltinCallStyle>())
                Assert.Null(BuiltinRegistry.GetBuiltin(builtin).GetSignature(style).RepeatedParameterName);
        }

        foreach (var member in BuiltinRegistry.MathMemberNames)
        {
            if (BuiltinRegistry.TryGetMathMemberFacts(member, out var facts))
                Assert.Null(facts.Signature.RepeatedParameterName);
        }

        foreach (var alias in BuiltinRegistry.MathAliasNames)
        {
            if (BuiltinRegistry.TryGetMathAliasFacts(alias, out var facts))
                Assert.Null(facts.Signature.RepeatedParameterName);
        }

        var duplicate = Assert.Throws<ArgumentException>(
            () => HostOperation.Create("twice", static (_, _) => new Result.Atom(0), "x", "x"));
        Assert.Contains("duplicate parameter name 'x'", duplicate.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RepeatedParameterName_IsTheFirstCaptureAnEarlierOneBinds()
    {
        static string? Repeated(string declaration)
            => CallableSignature.FromAlgorithm("P", Property(SourceProvenance.ParseValid(declaration + "\n0").Root, "P")).RepeatedParameterName;

        Assert.Null(Repeated("P(x, y) = x + y"));
        Assert.Null(Repeated("P((x, a), (y, b)) = a + b"));
        Assert.Null(Repeated("P(x, *rest) = x"));
        Assert.Equal("x", Repeated("P(x, x) = x"));
        Assert.Equal("y", Repeated("P(x, y, y, x) = x"));
        Assert.Equal("x", Repeated("P((x, a), (b, x)) = a + b"));
        Assert.Equal("a", Repeated("P(a, (b, (c, a))) = b + c"));
        Assert.Equal("x", Repeated("P((x, *rest), x) = rest"));
        // A lifted (implicit) signature is a shared FE-3 template; it answers from its facts.
        var lifted = CallableSignature.FromAlgorithm("K", Property(SourceProvenance.ParseValid("Inc(x) = x + 1\nK = Inc + y\n0").Root, "K"));
        Assert.IsType<ImplicitSignatureTemplate>(lifted.ParameterPatterns);
        Assert.Null(lifted.RepeatedParameterName);
    }

    // ── 5. Positions that never forward are unchanged ───────────────────────────────

    /// <summary>
    /// Neutral positions pass the callable, callees and dot fallbacks receive written arguments,
    /// opened and structural names are never implicitly forwarded, and a bare root row is the
    /// callable's own zero-argument demand — none of them is a forwarding route, so none reports.
    /// </summary>
    [Theory]
    [InlineData(P + "Apply(f) = f(4, 4)\nApply(P)", "4")]
    [InlineData(P + "P(7, 7)", "7")]
    [InlineData(P + "(7, 7)*.P", "7")]
    [InlineData(P + "D = y.P(y)\nD(3)", "3")]
    [InlineData(P + "Twice(f, v) = f(v, v)\nTwice(P, 5)", "5")]
    [InlineData(P + "P", "err ArityMismatch: Property 'P' expects 2 parameters, but was called with 0 arguments.")]
    [InlineData(P + "7.P", "err ArityMismatch: Callable `P(x, x)` expects 2 arguments, but was called with 1 argument.")]
    [InlineData(P + "map([1, 2], P)", "err ArityMismatch: while evaluating call to map: while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact): Expected 2 parameters, but was called with 1 argument.")]
    [InlineData("M = {\n  public P(x, x) = x\n}\nD = {\n  open M\n  P + 1\n}\nD", "err ArityMismatch: Property 'P' expects 2 parameters, but was called with 0 arguments.")]
    [InlineData("M = {\n  public P(x, x) = x\n}\nD = M.P + 1\nD", "err ArityMismatch: Property 'P' on `M` expects 2 parameters, but was called with 0 arguments.")]
    public void PositionsThatNeverForward_AreUnchanged(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, Display(source));
    }

    // ── 6. The written forms (six routes) ───────────────────────────────────────────

    /// <summary>
    /// (id, source, outcome with host calls) on every execution route. A wrapper with its OWN
    /// parameters keeps the callee's independently supplied arguments, so Q-05 holds through it
    /// unchanged: equal values match, unequal ones are the callee's own failure, a failed argument
    /// propagates after one evaluation, and a callable-only argument is its own value demand. A
    /// wrapper that WRITES one value into every occurrence supplies that same input explicitly.
    /// </summary>
    public static TheoryData<string, string, string> WrittenForms => new()
    {
        { "wrapper-equal", P + "Alias(a, b) = P(a, b)\nAlias(7, 7)", "ok 7" },
        { "wrapper-unequal", P + "Alias(a, b) = P(a, b)\nAlias(7, 8)", "err ArityMismatch: while evaluating call to Alias: while evaluating call to P: Bad arity" },
        { "wrapper-renamed", P + "W(u, v) = P(u, v)\nW(3, 3)", "ok 3" },
        { "wrapper-traced", P + "W(u, v) = P(u, v)\nW(trace(3), trace(3))", "ok 3 [trace(3),trace(3)]" },
        { "wrapper-failed", "Bad = trace(1) / 0\n" + P + "W(u, v) = P(u, v)\nW(Bad, 7)", "err DivisionByZero: while evaluating call to W: while evaluating call to P: Division by zero [trace(1)]" },
        { "wrapper-callable-only", "Inc(y) = y + 1\n" + P + "W(u, v) = P(u, v)\nW(Inc, 1)", "err ArityMismatch: while evaluating call to W: while evaluating call to P: Property 'Inc' expects 1 parameter, but was called with 0 arguments." },
        { "wrapper-nested", "P((x, a), x) = a\nW(p, q) = P(p, q)\nW((7, 8), 7)", "ok 8" },
        { "wrapper-nested-unequal", "P((x, a), x) = a\nW(p, q) = P(p, q)\nW((7, 8), 9)", "err ArityMismatch: while evaluating call to W: while evaluating call to P: Bad arity" },
        { "wrapper-three", "P(x, x, x) = x\nW(a, b, c) = P(a, b, c)\nW(1, 1, 1)", "ok 1" },
        { "wrapper-three-unequal", "P(x, x, x) = x\nW(a, b, c) = P(a, b, c)\nW(1, 1, 2)", "err ArityMismatch: while evaluating call to W: while evaluating call to P: Bad arity" },
        { "wrapper-collecting", "P(x, *rest, x) = rest\nW(a, *m, b) = P(a, m*, b)\nW(1, 2, 3, 1)", "ok L[2, 3]" },
        { "wrapper-grouped-collector", "P((x, *rest), x) = rest\nW(p, q) = P(p, q)\nW((1, 2, 3), 1)", "ok L[2, 3]" },
        { "same-value", P + "Same(x) = P(x, x)\nSame(7)", "ok 7" },
        { "same-value-once", P + "Same(x) = P(x, x)\nSame(tick())", "ok 1 [tick#1]" },
        { "same-value-failed", "Bad = trace(1) / 0\n" + P + "Same(x) = P(x, x)\nSame(Bad)", "err DivisionByZero: while evaluating call to Same: while evaluating call to P: Division by zero [trace(1)]" },
        { "same-value-callable-only", "Inc(y) = y + 1\n" + P + "Same(x) = P(x, x)\nSame(Inc)", "err ArityMismatch: while evaluating call to Same: while evaluating call to P: Property 'Inc' expects 1 parameter, but was called with 0 arguments." },
        { "family-wrapper", "E(x, x) = true\nE(x, y) = false\nW(a, b) = E(a, b)\nW(1, 1), W(1, 2)", "ok S[true, false]" },
        { "wrapper-as-callback", P + "W(u, v) = P(u, v)\nreduce([4, 4], W, 4)", "ok 4" },
        { "wrapper-alias-lifts", P + "W(u, v) = P(u, v)\nAlias = W\nAlias(5, 5)", "ok 5" },
    };

    [Theory]
    [MemberData(nameof(WrittenForms))]
    public async Task WrittenForms_AgreeOnEveryRoute(string id, string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        var oracle = await RepeatedNameConstraintTests.OnEveryRouteAsync(source);
        var actual = RepeatedNameConstraintTests.Rendered(oracle);
        Assert.True(expected == actual, $"{id}\nexpected: {expected}\nactual:   {actual}");
    }

    /// <summary>
    /// An alias of a wrapper with distinct parameters lifts as any alias does, so the explicit
    /// form composes: <c>Alias = W</c> becomes <c>Alias(u, v) = W(u, v)</c>, two parameters.
    /// </summary>
    [Fact]
    public void AliasOfAnExplicitWrapper_LiftsBothParameters()
    {
        var root = SourceProvenance.ParseValid(P + "W(u, v) = P(u, v)\nAlias = W\nAlias(5, 5)").Root;
        var alias = Property(root, "Alias");
        Assert.Equal(["u", "v"], alias.Params);
        var call = Assert.IsType<Expr.Call>(Assert.Single(alias.Output));
        Assert.Equal(["u", "v"], call.Args.Select(static argument => Assert.IsType<Expr.Param>(argument).Name));
    }

    // ── 7. Non-repeating callees lift exactly as before ─────────────────────────────

    [Theory]
    [InlineData("Inc(x) = x + 1\nAlias = Inc\nAlias(7)", "8", new[] { "x" })]
    [InlineData("Pair(x, y) = x + y\nAlias = Pair\nAlias(1, 2)", "3", new[] { "x", "y" })]
    [InlineData("P((x, a), y) = a + y\nAlias = P\nAlias((1, 2), 3)", "5", new[] { "x", "a", "y" })]
    [InlineData("Head(x, *rest) = x\nAlias = Head\nAlias(5, 6, 7)", "5", new[] { "x", "rest" })]
    [InlineData("H((*xs)) = xs.count\nAlias = H\nAlias((1, 2))", "2", new[] { "xs" })]
    [InlineData("Inc(x) = x + 1\nAlias = Inc + 1\nAlias(7)", "9", new[] { "x" })]
    public void NonRepeatingCallees_LiftAsBefore(string source, string expected, string[] liftedNames)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(liftedNames, Property(root, "Alias").Params);
        Assert.Equal(expected, Display(source));
    }

    [Fact]
    public async Task CrossCalleeByNameSharing_IsUnchanged()
    {
        const string Source = "F(x) = x + 1\nG(x) = x * 2\nH = F + G\nH(3)";
        var h = Property(SourceProvenance.ParseValid(Source).Root, "H");
        Assert.Equal(["x"], h.Params);
        var sum = Assert.IsType<Expr.Binary>(Assert.Single(h.Output));
        Assert.Equal("x", Assert.IsType<Expr.Param>(Assert.Single(Assert.IsType<Expr.Call>(sum.Left).Args)).Name);
        Assert.Equal("x", Assert.IsType<Expr.Param>(Assert.Single(Assert.IsType<Expr.Call>(sum.Right).Args)).Name);
        Assert.Equal("ok 10", RepeatedNameConstraintTests.Rendered(await RepeatedNameConstraintTests.OnEveryRouteAsync(Source)));
    }

    // ── 8. Collecting aliases and clause families ───────────────────────────────────

    [Theory]
    [InlineData("Cnt(*xs) = xs.count\nAlias = Cnt\nAlias", "0")]
    [InlineData("Cnt(*xs) = xs.count\nAlias = Cnt\nAlias == Alias", "true")]
    [InlineData("Cnt(*xs) = xs.count\nAlias(*xs) = Cnt(xs*)\nAlias(1, 2, 3)", "3")]
    [InlineData("Cnt(*xs) = xs.count\nUse(t, *items) = Cnt\nUse(0, 1, 2)", "0")]
    [InlineData("Coll(*xs) = xs\nFwd(*ys) = Coll(ys*)\nFwd((1, 2), 3)", "[(1, 2), 3]")]
    public void CollectingAliases_AreUnaffected(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, Display(source));
    }

    /// <summary>
    /// A clause family is never lifted (its lifting signature is empty, PV-14), so a family whose
    /// branch repeats a name is neither refused nor forwarded: the alias is a zero-parameter
    /// property, unchanged.
    /// </summary>
    [Fact]
    public void ClauseFamilyWithARepeatedBranch_IsNeverLiftedAndNeverRefused()
    {
        const string Source = "Same(x, x) = true\nSame(x, y) = false\nAlias = Same\nAlias(1, 1)";
        var alias = Property(SourceProvenance.ParseValid(Source).Root, "Alias");
        Assert.Empty(alias.Params);
        Assert.Equal("err ArityMismatch: Callable `Alias` expects 0 arguments, but was called with 2 arguments.", Display(Source));
    }

    // ── 9. Metamorphic family: no implicit transformation erases the constraint ─────

    /// <summary>A generated repeated-name signature with argument tuples that satisfy and violate it.</summary>
    public sealed record Shape(string Parameters, string Body, string Repeated, string Matching, string Violating, string Distinct);

    private static readonly Shape[] Shapes =
    [
        new("x, x", "x", "x", "7, 7", "7, 8", "x, x2"),
        new("x, y, x", "[x, y]", "x", "7, 1, 7", "7, 1, 8", "x, y, x2"),
        new("x, x, y", "[x, y]", "x", "7, 7, 1", "7, 8, 1", "x, x2, y"),
        new("y, x, x", "[x, y]", "x", "1, 7, 7", "1, 7, 8", "y, x, x2"),
        new("x, x, x", "x", "x", "7, 7, 7", "7, 7, 8", "x, x2, x3"),
        new("(x, a), x", "a", "x", "(7, 1), 7", "(7, 1), 8", "(x, a), x2"),
        new("x, (x, a)", "a", "x", "7, (7, 1)", "8, (7, 1)", "x, (x2, a)"),
        new("(x, y), (z, x)", "[y, z]", "x", "(7, 1), (2, 7)", "(7, 1), (2, 8)", "(x, y), (z, x2)"),
        new("(x, *rest), x", "rest", "x", "(7, 1, 2), 7", "(7, 1, 2), 8", "(x, *rest), x2"),
        new("x, *rest, x", "rest", "x", "7, 1, 2, 7", "7, 1, 2, 8", "x, *rest, x2"),
        new("(x, x)", "x", "x", "(7, 7)", "(7, 8)", "(x, x2)"),
        new("(x, y), x, y", "[x, y]", "x", "(7, 1), 7, 1", "(7, 1), 7, 2", "(x, y), x2, y2"),
    ];

    /// <summary>Lifting-position templates; <c>@</c> marks the callee reference.</summary>
    private static readonly string[] PositionTemplates =
    [
        "Alias = @\n0",
        "D = @ + 0\n0",
        "D = [@]\n0",
        "D = @:0\n0",
        "D = sin(@)\n0",
        "Q(x) = @\n0",
        "D = { @ }\n0",
        "D = {\n  Inner = @\n  Inner\n}\n0",
        "D = {\n  a, b = @\n  a\n}\n0",
        "F(0) = 0\nF(z) = @ + z\n0",
    ];

    public static TheoryData<int, int> ShapeByPosition()
    {
        var data = new TheoryData<int, int>();
        for (var shape = 0; shape < Shapes.Length; shape++)
        {
            for (var position = 0; position < PositionTemplates.Length; position++)
                data.Add(shape, position);
        }

        return data;
    }

    private static (string Source, int Line, int Column) Place(string declaration, string template)
    {
        var body = template.Replace("@", "P", StringComparison.Ordinal);
        var prefix = declaration + "\n" + template[..template.IndexOf('@', StringComparison.Ordinal)];
        var lines = prefix.Split('\n');
        return (declaration + "\n" + body, lines.Length, lines[^1].Length + 1);
    }

    /// <summary>
    /// For every generated repeated-name signature and every lifting position, the reference is
    /// refused at the written occurrence. Renaming the repeated occurrences apart removes this
    /// refusal. Other lifting conditions still apply (a closed list may lack the renamed inputs).
    /// </summary>
    [Theory]
    [MemberData(nameof(ShapeByPosition))]
    public void GeneratedShapes_AreRefusedInEveryPosition_AndEligibleOnceRenamedApart(int shapeIndex, int positionIndex)
    {
        var shape = Shapes[shapeIndex];
        var template = PositionTemplates[positionIndex];

        var (source, line, column) = Place($"P({shape.Parameters}) = {shape.Body}", template);
        AssertRefusedAt(source, "P", shape.Repeated, (line, column));

        var (renamed, _, _) = Place($"P({shape.Distinct}) = {shape.Body}", template);
        var parsed = Parser.Parse(renamed);
        Assert.DoesNotContain(parsed.Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.RepeatedParameterNotForwardable);
        if (positionIndex == 0)
        {
            Assert.Empty(parsed.Diagnostics);
            var target = Property(parsed.Root, "P");
            var alias = Property(parsed.Root, "Alias");
            Assert.Equal(target.Params, alias.Params);
            Assert.IsType<Expr.Call>(Assert.Single(alias.Output));
        }
    }

    /// <summary>
    /// The written positional wrapper that the refusal asks for is observationally the callee:
    /// on a satisfying and a violating argument tuple, <c>W(a1, ..., an) = P(a1, ..., an)</c>
    /// reports exactly what the direct call reports (the wrapper adds only its own call frame),
    /// so the constraint over independently supplied arguments survives the written form.
    /// </summary>
    [Theory]
    [MemberData(nameof(ShapeIndexes))]
    public void GeneratedShapes_WrittenWrapperPreservesTheConstraint(int shapeIndex)
    {
        var shape = Shapes[shapeIndex];
        // One wrapper parameter per top-level slot; a top-level collector stays a collector and
        // is forwarded by spread (a collector nested in a group travels inside its slot).
        var slots = TopLevelSlots(shape.Parameters);
        var wrapperParameters = Enumerable.Range(0, slots.Count).Select(static index => $"a{index}").ToList();
        var collectorIndex = slots.FindIndex(static slot => slot.StartsWith('*'));
        if (collectorIndex >= 0)
            wrapperParameters[collectorIndex] = "*m";

        var wrapperArguments = wrapperParameters.Select(static parameter => parameter.StartsWith('*') ? parameter[1..] + "*" : parameter);
        var declaration = $"P({shape.Parameters}) = {shape.Body}\n";
        var wrapper = $"W({string.Join(", ", wrapperParameters)}) = P({string.Join(", ", wrapperArguments)})\n";

        foreach (var arguments in new[] { shape.Matching, shape.Violating })
        {
            var direct = Display(declaration + $"P({arguments})");
            var wrapped = Display(declaration + wrapper + $"W({arguments})");
            var expected = direct.StartsWith("err ", StringComparison.Ordinal)
                ? direct.Replace("while evaluating call to P: ", "while evaluating call to W: while evaluating call to P: ", StringComparison.Ordinal)
                : direct;
            Assert.True(expected == wrapped, $"{shape.Parameters} with ({arguments})\ndirect:  {direct}\nwrapped: {wrapped}");
        }

        Assert.DoesNotContain("err", Display(declaration + $"P({shape.Matching})"), StringComparison.Ordinal);
        Assert.StartsWith("err ArityMismatch", Display(declaration + $"P({shape.Violating})"), StringComparison.Ordinal);
    }

    public static TheoryData<int> ShapeIndexes()
    {
        var data = new TheoryData<int>();
        for (var shape = 0; shape < Shapes.Length; shape++)
            data.Add(shape);
        return data;
    }

    private static List<string> TopLevelSlots(string parameters)
    {
        var slots = new List<string>();
        var depth = 0;
        var start = 0;
        for (var index = 0; index < parameters.Length; index++)
        {
            switch (parameters[index])
            {
                case '(':
                    depth++;
                    break;
                case ')':
                    depth--;
                    break;
                case ',' when depth == 0:
                    slots.Add(parameters[start..index].Trim());
                    start = index + 1;
                    break;
            }
        }

        slots.Add(parameters[start..].Trim());
        return slots;
    }

    private static IEnumerable<Expr> AllExpressions(Algorithm algorithm)
    {
        var pending = new Stack<Expr>(algorithm.Output);
        foreach (var property in algorithm.Properties)
        {
            foreach (var expr in AllExpressions(property.Value))
                yield return expr;
        }

        while (pending.Count > 0)
        {
            var expr = pending.Pop();
            yield return expr;
            switch (expr)
            {
                case Expr.Call call:
                    pending.Push(call.Function);
                    foreach (var argument in call.Args)
                        pending.Push(argument);
                    break;
                case Expr.Binary binary:
                    pending.Push(binary.Left);
                    pending.Push(binary.Right);
                    break;
                case Expr.AlgorithmExpr block:
                    foreach (var nested in AllExpressions(block.Algorithm))
                        yield return nested;
                    break;
            }
        }
    }
}
