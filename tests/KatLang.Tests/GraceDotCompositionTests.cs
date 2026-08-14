namespace KatLang.Tests;

/// <summary>
/// Focused regression matrix for Grace composed with ordinary DotCall syntax.
///
/// The language law: `~` affects inferred parameter ORDERING ONLY. It never
/// changes the property body's executable semantics, so `recv~.t(args...)` and
/// `recv.~t(args...)` have the SAME executable body as the ordinary dot edge
/// `recv.t(args...)` — structural member first, stored lexical fallback
/// second. Inferred parameters follow semantic source-occurrence order, so
/// `K = a.t` corresponds to `K(a, t) = a.t`; the fallback's runtime call
/// assembly as `t(a)` is a separate concern. In `a~.t`, postfix Grace decorates
/// `a`; in `a.~t`, prefix Grace decorates the participating fallback occurrence
/// `t`. Both use the same weight arithmetic as standalone Grace.
///
/// The architectural rule: each written marker contributes ordinary ordering
/// <see cref="Expr.Grace"/> on its individual name occurrence at parse time,
/// which parameter detection consumes and strips. After elaboration, graced and
/// ungraced dot sources are the SAME <see cref="Expr.DotCall"/> body; the
/// evaluator, the optimizer, and Lean cannot observe that the marker was
/// written. There is no additional resolution mode and no lowering to a call.
///
/// The eligibility rule follows the decorated occurrence. Postfix Grace before
/// a dot requires the receiver itself to be one bare name, so compound forms
/// such as `(x + y)~.t` and a second `~.` edge reject. Prefix Grace after a dot
/// decorates the bare member/fallback name, so `(x + y).~t` is valid.
/// </summary>
public class GraceDotCompositionTests
{
    private const string GraceEligibilityFragment =
        "Grace `~` can only be applied to a parameter or name occurrence.";

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result List(params Result[] items) => new Result.ListValue(items);

    private static Result Seq(params Result[] items) => new Result.SequenceValue(items);

    /// <summary>
    /// STRICT-SOURCE: requires a clean front end, then evaluates through both
    /// the plain and the counted evaluator entry points and asserts they agree
    /// on the same value before returning it.
    /// </summary>
    private static Result Evaluate(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        var expr = new Expr.AlgorithmExpr(provenance.Root);

        var plain = Evaluator.Run(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");

        Assert.True(
            Result.ValueComparer.Equals(plain.Value, counted.Value.Value),
            $"Plain/counted divergence: {plain.Value} vs {counted.Value.Value}");
        return plain.Value;
    }

    private static void AssertResult(string source, Result expected)
    {
        var actual = Evaluate(source);
        Assert.True(
            Result.ValueComparer.Equals(expected, actual),
            $"Expected {expected} but got {actual}{Environment.NewLine}Source:{Environment.NewLine}{source}");
    }

    /// <summary>
    /// The central law assertion: two sources elaborate to the SAME executable
    /// body. Compared structurally, because source spans legitimately differ —
    /// the marker occupies source columns, and span provenance is the ONE
    /// thing a graced source is still allowed to carry.
    /// </summary>
    private static void AssertSameElaboratedBody(string left, string right, string propertyName = "K")
    {
        static string BodyShapeOf(string source, string propertyName)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            var property = Assert.Single(root.Properties, p => p.Name == propertyName);
            return Shape(Assert.Single(property.Value.Output));
        }

        Assert.Equal(BodyShapeOf(right, propertyName), BodyShapeOf(left, propertyName));
    }

    /// <summary>Span-free structural rendering of an elaborated expression.</summary>
    private static string Shape(Expr expr) => expr switch
    {
        Expr.Num(var value) => value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Expr.StringLiteral(var text) => $"'{text}'",
        Expr.Param(var name) => $"Param({name})",
        Expr.Resolve(var name) => $"Resolve({name})",
        Expr.Grace(var inner, var weight) => $"Grace({Shape(inner)},{weight})",
        Expr.Unary(var op, var operand) => $"Unary({op},{Shape(operand)})",
        Expr.Binary(var op, var left, var right) => $"Binary({op},{Shape(left)},{Shape(right)})",
        Expr.Index(var target, var selector) => $"Index({Shape(target)},{Shape(selector)})",
        Expr.SequenceSpread(var operand) => $"Spread({Shape(operand)})",
        Expr.EmptySequence => "()",
        Expr.ListLiteral(var items) => $"List([{string.Join(",", items.Select(Shape))}])",
        Expr.Capture(var body) => $"Capture([{string.Join(",", body.Select(Shape))}])",
        Expr.Call(var function, var args) => $"Call({Shape(function)},[{string.Join(",", args.Select(Shape))}])",
        Expr.DotCall dotCall =>
            $"DotCall({Shape(dotCall.Target)},{dotCall.Name},"
            + $"{(dotCall.Args is null ? "null" : "[" + string.Join(",", dotCall.Args.Select(Shape)) + "]")},"
            + $"fallback={Shape(dotCall.EffectiveLexicalFallback)})",
        Expr.AlgorithmExpr(var algorithm) =>
            $"Alg([{string.Join(",", algorithm.Params)}],[{string.Join(",", algorithm.Output.Select(Shape))}])",
        _ => expr.GetType().Name,
    };

    private static IReadOnlyList<string> ParamsOf(string source, string propertyName = "K")
    {
        var root = SourceProvenance.ParseValid(source).Root;
        return Assert.Single(root.Properties, p => p.Name == propertyName).Value.Params;
    }

    private static EvalError AssertBothEvaluatorsFail(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        var expr = new Expr.AlgorithmExpr(provenance.Root);

        var plain = Evaluator.Run(expr);
        Assert.True(plain.IsError, $"Expected plain evaluation error but got: {(plain.IsError ? null : plain.Value)}");

        var counted = Evaluator.RunCounted(expr);
        Assert.True(counted.IsError, $"Expected counted evaluation error but got: {(counted.IsError ? null : counted.Value.Value)}");

        var plainInner = Innermost(plain.Error);
        var countedInner = Innermost(counted.Error);
        Assert.Equal(plainInner.GetType(), countedInner.GetType());
        return plainInner;
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext withContext ? Innermost(withContext.Inner) : error;

    private static void AssertParseFails(string source, string diagnosticFragment)
    {
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors, $"Expected a parse diagnostic but the source parsed cleanly:{Environment.NewLine}{source}");
        Assert.Contains(parse.Diagnostics, diagnostic => diagnostic.Message.Contains(diagnosticFragment, StringComparison.Ordinal));
    }

    // ── A. THE CENTRAL LAW: source occurrence order, same executable body ──

    [Fact]
    public void Law_PrimaryCase_OrdinaryDotInfersSemanticSourceOrder()
    {
        // `K = a.t` has ordinary DotCall semantics: structural `t` on `a` if
        // present, otherwise the lexical call `t(a)`. Because `a` is an opaque
        // implicit parameter, that fallback MAY be selected, so the fallback
        // callable participates at the member's semantic source occurrence:
        // receiver `a`, member/fallback `t` => K(a, t).
        Assert.Equal(["a", "t"], ParamsOf("K = a.t\nK(7, {x+1})"));
        AssertResult("K = a.t\nK(7, {x+1})", Atom(8));
    }

    [Fact]
    public void Law_PrimaryTrace_RawOccurrenceAndElaboratedFallbackIdentityAgree()
    {
        var syntax = Parser.ParseSyntax("K = a.t");
        Assert.Empty(syntax.Diagnostics);
        var rawK = Assert.Single(syntax.Root.Properties).Value;
        Assert.Empty(rawK.Params);
        var rawEdge = Assert.IsType<Expr.DotCall>(Assert.Single(rawK.Output));
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(rawEdge.Target).Name);
        Assert.Equal("t", Assert.IsType<Expr.Resolve>(rawEdge.LexicalFallback).Name);

        var (detected, diagnostics) = ParameterDetector.Detect(syntax.Root);
        Assert.Empty(diagnostics);
        var detectedK = Assert.Single(detected.Properties).Value;
        Assert.Equal(["a", "t"], detectedK.Params);
        var detectedEdge = Assert.IsType<Expr.DotCall>(Assert.Single(detectedK.Output));
        Assert.Equal("a", Assert.IsType<Expr.Param>(detectedEdge.Target).Name);
        Assert.Equal("t", Assert.IsType<Expr.Param>(detectedEdge.LexicalFallback).Name);

        var elaboratedK = Assert.Single(SourceProvenance.ParseValid("K = a.t").Root.Properties).Value;
        Assert.Equal(detectedK.Params, elaboratedK.Params);
        Assert.Equal(Shape(detectedEdge), Shape(Assert.Single(elaboratedK.Output)));
    }

    [Fact]
    public void Law_RawGraceOwnership_ReusesOrdinaryPrefixAndPostfixRepresentation()
    {
        var postfixSyntax = Parser.ParseSyntax("K = a~.t");
        Assert.Empty(postfixSyntax.Diagnostics);
        var postfixEdge = Assert.IsType<Expr.DotCall>(
            Assert.Single(Assert.Single(postfixSyntax.Root.Properties).Value.Output));
        var receiverGrace = Assert.IsType<Expr.Grace>(postfixEdge.Target);
        Assert.Equal(+1, receiverGrace.Weight);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(receiverGrace.Inner).Name);
        Assert.Equal("t", Assert.IsType<Expr.Resolve>(postfixEdge.LexicalFallback).Name);

        var prefixSyntax = Parser.ParseSyntax("K = a.~t");
        Assert.Empty(prefixSyntax.Diagnostics);
        var prefixEdge = Assert.IsType<Expr.DotCall>(
            Assert.Single(Assert.Single(prefixSyntax.Root.Properties).Value.Output));
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(prefixEdge.Target).Name);
        var memberGrace = Assert.IsType<Expr.Grace>(prefixEdge.LexicalFallback);
        Assert.Equal(-1, memberGrace.Weight);
        Assert.Equal("t", Assert.IsType<Expr.Resolve>(memberGrace.Inner).Name);

        var (postfixDetected, postfixDiagnostics) = ParameterDetector.Detect(postfixSyntax.Root);
        var (prefixDetected, prefixDiagnostics) = ParameterDetector.Detect(prefixSyntax.Root);
        Assert.Empty(postfixDiagnostics);
        Assert.Empty(prefixDiagnostics);
        Assert.Equal(["t", "a"], Assert.Single(postfixDetected.Properties).Value.Params);
        Assert.Equal(["t", "a"], Assert.Single(prefixDetected.Properties).Value.Params);
        Assert.Equal(
            Shape(Assert.Single(postfixDetected.Properties[0].Value.Output)),
            Shape(Assert.Single(prefixDetected.Properties[0].Value.Output)));
    }

    [Fact]
    public void Law_GraceCounterpart_UsesOrdinaryWeightOnTheSameBody()
    {
        // Base occurrence order is a,t. Postfix Grace moves `a` one place
        // later; prefix Grace moves `t` one place earlier. Both yield t,a.
        Assert.Equal(["t", "a"], ParamsOf("K = a~.t\nK({x+1}, 7)"));
        AssertResult("K = a~.t\nK({x+1}, 7)", Atom(8));

        Assert.Equal(["t", "a"], ParamsOf("K = a.~t\nK({x+1}, 7)"));
        AssertResult("K = a.~t\nK({x+1}, 7)", Atom(8));
    }

    [Fact]
    public void Law_EquivalenceMatrix_ImplicitAndExplicitAgree()
    {
        // Inference differs only by ordinary Grace; explicit declarations keep
        // their written parameter order. Every property body is the same edge.
        AssertResult("K1 = a.t\nK1(7, {x+1})", Atom(8));
        AssertResult("K2(a, t) = a.t\nK2(7, {x+1})", Atom(8));
        AssertResult("K3 = a~.t\nK3({x+1}, 7)", Atom(8));
        AssertResult("K4(t, a) = a~.t\nK4({x+1}, 7)", Atom(8));
        AssertResult("K5 = a.~t\nK5({x+1}, 7)", Atom(8));
        AssertResult("K6(t, a) = a.~t\nK6({x+1}, 7)", Atom(8));
    }

    [Fact]
    public void Law_BothSpellings_ElaborateToTheOrdinaryDotBody()
    {
        // The marker leaves NO trace: all three spellings share one elaborated
        // body (with the same param names bound), and none of them is a Call.
        AssertSameElaboratedBody("K(t, a) = a~.t", "K(a, t) = a.t");
        AssertSameElaboratedBody("K(t, a) = a.~t", "K(a, t) = a.t");

        var body = Assert.IsType<Expr.DotCall>(
            Assert.Single(SourceProvenance.ParseValid("K(t, a) = a~.t\nK({a+1}, 7)")
                .Root.Properties[0].Value.Output));
        Assert.Equal("t", body.Name);
        Assert.Equal("a", Assert.IsType<Expr.Param>(body.Target).Name);
        Assert.Equal("t", Assert.IsType<Expr.Param>(body.EffectiveLexicalFallback).Name);
        Assert.Null(body.Args);
    }

    [Fact]
    public void Law_ExplicitParameterLists_KeepTheirDeclaredOrder()
    {
        Assert.Equal(["a", "t"], ParamsOf("K(a, t) = a~.t"));
        Assert.Equal(["t", "a"], ParamsOf("K(t, a) = a~.t"));
        Assert.Equal(["a", "t"], ParamsOf("K(a, t) = a.~t"));
        Assert.Equal(["t", "a"], ParamsOf("K(t, a) = a.~t"));
    }

    [Fact]
    public void Law_DirectCallComparison_HasItsOwnSourceOrderAndDifferentBody()
    {
        // Direct-call traversal sees callee then argument; DotCall traversal
        // sees receiver then semantic member/fallback occurrence.
        Assert.Equal(["t", "a"], ParamsOf("K = t(a)\nK({x+1}, 7)"));
        Assert.Equal(["a", "t"], ParamsOf("K = a.t\nK(7, {x+1})"));

        // Their bodies are also NOT equivalent: only the dot edge consults
        // structural members first.
        AssertResult(StructuralSplit + "K(o) = o.V\nK(Obj)", Atom(42));
        AssertResult(StructuralSplit + "K(o) = V(o)\nK(Obj)", Atom(99));
    }

    [Fact]
    public void Law_GeneralExpressionTraversal_IsLeftToRightSemanticSourceOrder()
    {
        Assert.Equal(["a", "b"], ParamsOf("K = a + b"));
        Assert.Equal(["f", "a"], ParamsOf("K = f(a)"));
        Assert.Equal(["a", "b"], ParamsOf("K = a:b"));

        Assert.Equal(["z", "a", "t"], ParamsOf("K = z + a.t"));
        Assert.Equal(["z", "t", "a"], ParamsOf("K = z + a~.t"));
        Assert.Equal(["z", "t", "a"], ParamsOf("K = z + a.~t"));
        Assert.Equal(["a", "t", "z"], ParamsOf("K = a.t + z"));
        Assert.Equal(["f", "a", "t"], ParamsOf("K = f(a.t)"));
        Assert.Equal(["a", "t", "b"], ParamsOf("K = a.t(b)"));
        Assert.Equal(["q", "a", "t", "z"], ParamsOf("K = q(a.t, z)"));
    }

    [Fact]
    public void Law_BlockOwnsItsSourceOrderedParameters()
    {
        var k = Assert.Single(SourceProvenance.ParseValid("K = { a.t }").Root.Properties).Value;
        Assert.Equal(["a", "t"], k.Params);
        Assert.IsType<Expr.DotCall>(Assert.Single(k.Output));
    }

    [Fact]
    public void Law_MultipleDotsAndRepeatedNames_PreserveFirstOccurrenceOrder()
    {
        Assert.Equal(["a", "t", "b", "u"], ParamsOf("K = a.t + b.u"));
        Assert.Equal(["a", "t", "b"], ParamsOf("K = a.t + b.t"));
        Assert.Equal(["a", "t"], ParamsOf("K = a.t + a.t"));

        Assert.Equal(["t", "a", "b", "u"], ParamsOf("K = a~.t + b.u"));
        Assert.Equal(["a", "t", "u", "b"], ParamsOf("K = a.t + b~.u"));
        Assert.Equal(["t", "a", "b", "u"], ParamsOf("K = a.~t + b.u"));
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a.t + b.~t"));
    }

    [Fact]
    public void Law_MultiArgument_FollowsReceiverMemberArgumentsOrder()
    {
        // Runtime fallback still invokes `t(a, b, c)`, but signature order is
        // the DotCall's semantic source occurrence order.
        Assert.Equal(["a", "t", "b", "c"], ParamsOf("K = a.t(b, c)"));
        Assert.Equal(["t", "a", "b", "c"], ParamsOf("K = a~.t(b, c)"));
        Assert.Equal(["t", "a", "b", "c"], ParamsOf("K = a.~t(b, c)"));
        AssertSameElaboratedBody("K(t, a, b, c) = a~.t(b, c)", "K(a, t, b, c) = a.t(b, c)");
        AssertSameElaboratedBody("K(t, a, b, c) = a.~t(b, c)", "K(a, t, b, c) = a.t(b, c)");
        AssertResult("K = a.t(b, c)\nK(1, {a+b+c}, 10, 100)", Atom(111));
        AssertResult("K = a~.t(b, c)\nK({a+b+c}, 1, 10, 100)", Atom(111));
        AssertResult("K = a.~t(b, c)\nK({a+b+c}, 1, 10, 100)", Atom(111));
    }

    [Fact]
    public void Law_GraceAffectsSignatureOnly_OrdinaryGraceIdiomsUnchanged()
    {
        // Standalone Grace keeps the same sign and one-position arithmetic.
        Assert.Equal(["a", "t"], ParamsOf("K = t~(a)\nK(7, {a+1})"));
        AssertResult("K = t~(a)\nK(7, {a+1})", Atom(8));

        // Prefix grace on an ordinary argument still just reorders.
        Assert.Equal(["t", "b", "a"], ParamsOf("K = t(a~, b)\nK(1, 2, {x + y})"));

        // The same base name order a,t,b plus postfix Grace on `a` produces
        // the same one-position move with or without DotCall structure.
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a~ + t + b"));
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a~.t(b)"));
        // Likewise, prefix Grace on `t` is identical inside and outside dot.
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a.~t + b"));
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a + ~t + b"));
    }

    [Fact]
    public void Law_RepeatedPostfixGrace_UsesOrdinaryWeightArithmetic()
    {
        // `a~~.t` is two ordinary postfix markers (+2) on `a`. Only `t`
        // follows it, so the final order is still t,a.
        Assert.Equal(["t", "a"], ParamsOf("K = a~~.t\nK({x + 1}, 7)"));
        AssertResult("K = a~~.t\nK({x + 1}, 7)", Atom(8));
        AssertSameElaboratedBody("K(t, a) = a~~.t", "K(a, t) = a.t");
    }

    [Fact]
    public void Law_RepeatedCallableName_OrdersByOrdinaryGraceBubbling()
    {
        // Postfix Grace moves a name ONE position per unit through the
        // ordinary bubble pass; with the callable also written directly, the
        // outcome is plain grace arithmetic, not a bespoke source-order rule.
        Assert.Equal(["a", "t", "b"], ParamsOf("K = a.t + t(b)\nK(1, {x + 1}, 2)"));
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a~.t + t(b)"));
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a.t + b.~t"));
    }

    [Fact]
    public void Law_GracedDotsInsideArgumentSlots_ComposeSourceOrder()
    {
        // Each edge's receiver is its own bare name — nesting needs no
        // distribution, only the two one-name graces.
        // Base occurrence order is a,t,b,u. Each receiver moves one place
        // later, yielding t,a,u,b through the general bubble pass.
        Assert.Equal(["t", "a", "u", "b"], ParamsOf("K = a~.t(b~.u)"));
    }

    [Fact]
    public void Law_ReceiverEvaluatesExactlyOnce()
    {
        // The receiver is ONE expression in ONE dot edge, so a failing
        // receiver surfaces its one failure identically on both paths.
        var error = AssertBothEvaluatorsFail("F(x) = x + 1\nbad = 1/0\nbad~.F");
        Assert.IsType<EvalError.DivByZero>(error);
    }

    [Fact]
    public void Law_NestedLexicalScope_ResolvesLikeTheOrdinaryEdge()
        => AssertResult(
            """
            Outer = {
                t(a) = a + 1
                K1 = a.t
                K2 = a~.t
                K3 = a.~t
                K1(41)
                K2(41)
                K3(41)
            }
            Outer
            """,
            Seq(Atom(42), Atom(42), Atom(42)));

    // ── B. Structural precedence: Grace NEVER changes member selection ─────

    private const string StructuralSplit =
        """
        V(x) = 99
        Obj = {
            public V = 42
            0
        }
        """;

    [Fact]
    public void Law_StructuralCollision_AllSpellingsSelectTheStructuralMember()
    {
        // The receiver HAS the member, so every spelling uses it. `~` orders
        // parameters; it does not bypass structural lookup.
        AssertResult(StructuralSplit + "\nObj.V", Atom(42));
        AssertResult(StructuralSplit + "\nObj~.V", Atom(42));
        AssertResult(StructuralSplit + "\nObj.~V", Atom(42));
    }

    [Fact]
    public void Law_StructuralCollision_OnOpaqueReceiver_AllFormsAgree()
    {
        // With a runtime receiver the selection is decided at runtime, and the
        // two spellings agree in BOTH directions — only the argument ORDER of
        // the enclosing signature differs.
        AssertResult(StructuralSplit + "\nK(o, V) = o.V\nK(Obj, {x + 1})", Atom(42));
        AssertResult(StructuralSplit + "\nK(o, V) = o~.V\nK(Obj, {x + 1})", Atom(42));
        AssertResult(StructuralSplit + "\nK(o, V) = o.~V\nK(Obj, {x + 1})", Atom(42));
        // No structural member on the receiver → the lexical parameter is used.
        AssertResult("K(o, V) = o.V\nK(7, {x + 1})", Atom(8));
        AssertResult("K(o, V) = o~.V\nK(7, {x + 1})", Atom(8));
        AssertResult("K(o, V) = o.~V\nK(7, {x + 1})", Atom(8));
    }

    [Fact]
    public void Law_StructuralPrivateMember_IsReachedByBothSpellings()
    {
        // Structural dot access ignores `public`: a private member is still
        // reached, and Grace does not change that.
        const string privateMember = "Obj = {\n    V = 42\n    0\n}\n";
        AssertResult(privateMember + "K(o, V) = o.V\nK(Obj, {x + 100})", Atom(42));
        AssertResult(privateMember + "K(o, V) = o~.V\nK(Obj, {x + 100})", Atom(42));
        AssertResult(privateMember + "K(o, V) = o.~V\nK(Obj, {x + 100})", Atom(42));
    }

    [Fact]
    public void Law_NoStructuralMember_FallsBackInAllSpellings()
    {
        // `Obj` has no `Inc`, so both spellings call `Inc` lexically with the
        // receiver's own value (its output row `0`).
        const string defs = "Inc(x) = x + 1\nObj = {\n    V = 42\n    0\n}\n";
        AssertResult(defs + "Obj.Inc", Atom(1));
        AssertResult(defs + "Obj~.Inc", Atom(1));
        AssertResult(defs + "Obj.~Inc", Atom(1));
    }

    // ── C. Static fallback certainty drives inference ───────────────────────

    [Fact]
    public void Certainty_GuaranteedStructuralMember_InfersNoFallbackParameter()
    {
        // The receiver's statically known algorithm declares `t`, so the
        // fallback can NEVER be selected: no spurious `t` parameter.
        Assert.Empty(ParamsOf(
            """
            Obj = {
                public t = 42
                0
            }
            K = Obj.t
            K
            """));
        Assert.Empty(ParamsOf("Obj = { public t = 42 0 }\nK = Obj~.t"));
        Assert.Empty(ParamsOf("Obj = { public t = 42 0 }\nK = Obj.~t"));
        AssertResult(
            """
            Obj = {
                public t = 42
                0
            }
            K = Obj.t
            K
            """,
            Atom(42));
    }

    [Fact]
    public void Certainty_KnownStructuralMiss_InfersTheFallbackParameter()
    {
        // The receiver is a statically known algorithm WITHOUT the member, so
        // the fallback is unconditionally selected and its callable
        // participates. (`S` itself is a visible sibling, not a free name.)
        Assert.Equal(["t"], ParamsOf("S = 1, 2, 3\nK = S.t\nK({a:0 + 100})"));
        Assert.Equal(["t"], ParamsOf("S = 1, 2, 3\nK = S~.t"));
        Assert.Equal(["t"], ParamsOf("S = 1, 2, 3\nK = S.~t"));
        AssertResult("S = 1, 2, 3\nK = S.t\nK({a:0 + 100})", Atom(101));
    }

    [Fact]
    public void Certainty_OpaqueReceiver_InfersTheFallbackParameter()
    {
        // An implicit-parameter receiver is runtime-valued: the fallback MAY
        // be selected, so it participates (the primary law case).
        Assert.Equal(["a", "t"], ParamsOf("K = a.t"));
    }

    [Fact]
    public void Certainty_VisibleLexicalMember_IsNotAFreeName()
    {
        // A member name that resolves lexically is not free, so it never
        // becomes a parameter regardless of fallback certainty.
        Assert.Equal(["a"], ParamsOf("t(x) = x + 1\nK = a.t\nK(7)"));
        Assert.Equal(["a"], ParamsOf("t(x) = x + 1\nK = a~.t\nK(7)"));
        Assert.Equal(["a"], ParamsOf("t(x) = x + 1\nK = a.~t\nK(7)"));
        AssertResult("t(x) = x + 1\nK = a.t\nK(7)", Atom(8));
    }

    [Fact]
    public void Certainty_StringIntrinsic_IsNeverAFallback()
    {
        // The dot-only `.string` intrinsic pre-empts both channels on every
        // receiver shape, so it contributes no fallback parameter in any spelling.
        Assert.Equal(["v"], ParamsOf("K = v.string"));
        Assert.Equal(["v"], ParamsOf("K = v~.string"));
        Assert.Equal(["v"], ParamsOf("K = v.~string"));
    }

    // ── D. May-selection (signature) vs must-selection (closed lists) ───────

    [Fact]
    public void MayVsMust_ClosedExplicitListDoesNotRequireTheFallbackName()
    {
        // Parameter inference asks "CAN the fallback be needed?" — the closed
        // explicit-parameter-list rule asks the DEFINITE question and takes no
        // fallback contribution, so the common structural-accessor idiom stays
        // legal without declaring every member name.
        var source =
            """
            Get(obj) = obj.size
            Obj = {
                public size = 11
                0
            }
            Get(Obj)
            """;
        Assert.Equal(["obj"], ParamsOf(source, "Get"));
        AssertResult(source, Atom(11));

        // The same body still reaches the lexical fallback at runtime.
        AssertResult("Get(obj) = obj.size\nsize(v) = 77\nGet(3)", Atom(77));

        // And an unresolvable member in a closed list is a RUNTIME miss, not a
        // parse-time undeclared-identifier error — in both spellings.
        Assert.IsType<EvalError.UnknownName>(AssertBothEvaluatorsFail("K(a) = a.t\nK(7)"));
        Assert.IsType<EvalError.UnknownName>(AssertBothEvaluatorsFail("K(a) = a~.t\nK(7)"));
    }

    [Fact]
    public void MayVsMust_ConditionalBranchBodyDoesNotRequireTheFallbackName()
        // The full-input-specification rule is the same DEFINITE question: a
        // dot member is not reported as an undeclared branch identifier, and
        // the fallback arm still resolves lexically at runtime.
        => AssertResult(
            """
            size(v) = v * 2
            P(0) = 0
            P(x) = x.size
            P(21)
            """,
            Atom(42));

    // ── E. Special forms are shared, never Grace-sensitive ──────────────────

    [Fact]
    public void SpecialForm_StringIntrinsic_IsIdenticalInBothSpellings()
    {
        AssertResult("v = 5\nv.string", Str("5"));
        AssertResult("v = 5\nv~.string", Str("5"));
        AssertResult("v = 5\nv.~string", Str("5"));
        AssertSameElaboratedBody("K(v) = v~.string", "K(v) = v.string");

        // The intrinsic pre-empts a same-named lexical callable in every
        // spelling — it is an ordinary-dot member rule, not a Grace rule.
        AssertResult("string(x) = x + 100\nv = 5\nv.string", Str("5"));
        AssertResult("string(x) = x + 100\nv = 5\nv~.string", Str("5"));
        AssertResult("string(x) = x + 100\nv = 5\nv.~string", Str("5"));
    }

    [Fact]
    public void SpecialForm_SequenceBuiltins_AreIdenticalInBothSpellings()
    {
        Assert.Equal(["v"], ParamsOf("K = v.count"));
        Assert.Equal(["v", "n"], ParamsOf("K = v.take(n)"));
        AssertResult("S = 1, 2, 3\nS.count", Atom(3));
        AssertResult("S = 1, 2, 3\nS~.count", Atom(3));
        AssertResult("S = 1, 2, 3\nS.~count", Atom(3));
        AssertResult("S = 1, 2, 3\nS.take(2)", List(Atom(1), Atom(2)));
        AssertResult("S = 1, 2, 3\nS~.take(2)", List(Atom(1), Atom(2)));
        AssertResult("S = 1, 2, 3\nS.~take(2)", List(Atom(1), Atom(2)));
        AssertSameElaboratedBody("K(S) = S~.take(2)", "K(S) = S.take(2)");

        // A user `count` shadows the builtin in BOTH spellings.
        AssertResult("count(x) = 99\nS = 1, 2, 3\nS.count", Atom(99));
        AssertResult("count(x) = 99\nS = 1, 2, 3\nS~.count", Atom(99));

        // The dotted-receiver view stays DIFFERENT from the direct call — that
        // distinction belongs to DotCall, not to Grace.
        AssertResult("S = 1, 2, 3\nS~.count", Atom(3));
        AssertResult("S = 1, 2, 3\ncount(S)", Atom(3));
        AssertResult("Collect(*items) = items\nS = 1, 2, 3\nS~.Collect", List(Seq(Atom(1), Atom(2), Atom(3))));
        AssertResult("Collect(*items) = items\n(1, 2, 3).Collect", List(Atom(1), Atom(2), Atom(3)));
    }

    [Fact]
    public void SpecialForm_ReceiverSegmentSupply_IsSharedByBothSpellings()
    {
        // Receiver-segment supply is ordinary dot semantics, so Grace
        // inherits it unchanged: a WRITTEN GROUP receiver supplies its rows to
        // a flat collecting parameter, while a NAMED receiver supplies one
        // item. A group is not a Grace-eligible receiver, so only the named
        // form has both spellings — and they agree exactly.
        AssertResult("Mean(*Vector) = Vector.sum / Vector.count\n(1, 2, 2.718).Mean", Atom(1.906m));
        AssertResult("Collect(*items) = items\nS = 1, 2, 3\nS.Collect", List(Seq(Atom(1), Atom(2), Atom(3))));
        AssertResult("Collect(*items) = items\nS = 1, 2, 3\nS~.Collect", List(Seq(Atom(1), Atom(2), Atom(3))));
        AssertSameElaboratedBody("K(S) = S~.Collect", "K(S) = S.Collect");
        AssertParseFails("Collect(*items) = items\n(1, 2, 3)~.Collect", GraceEligibilityFragment);
    }

    [Fact]
    public void SpecialForm_ValueKindsWorkThroughBoundNames()
    {
        AssertResult("L = [1, 2, 3]\nL~.sum", Atom(6));
        AssertResult("E = ()\nE~.count", Atom(0));
        AssertResult("S = 1, 2, 3\nS~.first", Atom(1));
    }

    [Fact]
    public void SpecialForm_MemberResolvesThroughOpen()
        => AssertResult(
            """
            Lib = {
                public V(x) = 99
            }
            R = {
                open Lib
                v = 5
                v~.V
            }
            R
            """,
            Atom(99));

    [Fact]
    public void SpecialForm_GracedDotIsNotAnOpenTarget()
        // `open` consumes structural algorithm identity; there is no parameter
        // inference there, so a grace-marked target is not an open form. The
        // ordinary dotted path stays valid.
        => AssertParseFails(
            """
            M = {
                public C = 5
            }
            R = {
                open M~.C
                C
            }
            R
            """,
            "'grace' is not allowed in open declarations");

    [Fact]
    public void SpecialForm_InArgumentListAndCallbackSlots()
    {
        AssertResult("Inc(x) = x + 1\nF(a, b) = a * 10 + b\nv = 5\nF(v~.Inc, 2)", Atom(62));
        AssertResult("Inc(x) = x + 1\nv = 5\n[v~.Inc, 9]", List(Atom(6), Atom(9)));
        AssertResult("Inc(x) = x + 1\nmap((1, 2, 3), {a~.Inc})", List(Atom(2), Atom(3), Atom(4)));
        AssertResult("Id(x) = x\nv = 5\nreduce((1, 2, 3), {a + b}, v~.Id)", Atom(11));
    }

    [Fact]
    public void SpecialForm_SequencePipelineEdge_IsSharedByBothSpellings()
    {
        AssertResult("K(xs) = xs.filter({a > 1}).count\nK((1, 2, 3))", Atom(2));
        AssertResult("K(xs) = xs~.filter({a > 1}).count\nK((1, 2, 3))", Atom(2));
        AssertSameElaboratedBody("K(xs) = xs~.filter({a > 1}).count", "K(xs) = xs.filter({a > 1}).count");
    }

    // ── F. Argument-list forms ──────────────────────────────────────────────

    [Fact]
    public void ArgumentList_ExtraArgumentsFollowTheReceiver()
    {
        AssertResult("F(x, y, z) = x*100 + y*10 + z\nv = 3\nv.F(1, 2)", Atom(312));
        AssertResult("F(x, y, z) = x*100 + y*10 + z\nv = 3\nv~.F(1, 2)", Atom(312));
        AssertResult("F(x, y, z) = x*100 + y*10 + z\nF(3, 1, 2)", Atom(312));
    }

    [Fact]
    public void ArgumentList_ExplicitEmptyArgsKeepTheOrdinaryDotDistinction()
    {
        // `v~.F()` and `v~.F` keep the ordinary dot edge's property-style vs
        // explicit-argument-list distinction (Args null vs empty) — the marker
        // changes neither.
        var withArgs = Assert.IsType<Expr.DotCall>(
            SourceProvenance.ParseValid("F(x) = x + 1\nv = 3\nv~.F()").Root.Output[^1]);
        Assert.NotNull(withArgs.Args);
        Assert.Empty(withArgs.Args);

        var propertyStyle = Assert.IsType<Expr.DotCall>(
            SourceProvenance.ParseValid("F(x) = x + 1\nv = 3\nv~.F").Root.Output[^1]);
        Assert.Null(propertyStyle.Args);

        AssertResult("F(x) = x + 1\nv = 3\nv~.F()", Atom(4));
        AssertResult("F(x) = x + 1\nv = 3\nv~.F", Atom(4));
    }

    [Fact]
    public void ArgumentList_MemberIdentifierKeepsItsSourceSpan()
    {
        static Expr.DotCall Body(string source)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            return Assert.IsType<Expr.DotCall>(root.Properties[0].Value.Output[0]);
        }

        // The member identifier keeps its exact source span in every spelling
        // (hover/navigation anchor), and the receiver keeps its own span.
        foreach (var source in new[] { "K(a, t) = a~.t\nK(7, {a+1})", "K(a, t) = a.~t\nK(7, {a+1})" })
        {
            var dotCall = Body(source);
            Assert.Equal(new SourceSpan(1, 14, 1, 14), dotCall.MemberSpan);
            Assert.Equal(new SourceSpan(1, 11, 1, 11), dotCall.Target.Span);
        }

        var ordinary = Body("K(a, t) = a.t\nK(7, {a+1})");
        Assert.Equal(new SourceSpan(1, 13, 1, 13), ordinary.MemberSpan);
    }

    // ── G. Chaining ─────────────────────────────────────────────────────────

    [Fact]
    public void Chain_GracedDotThenOrdinaryContinuation()
    {
        // The first edge is an ordinary dot edge; `.string` then applies to
        // its result exactly as after an ungraced edge.
        AssertResult("K(a, t) = a~.t.string\nK(7, {a+1})", Str("8"));
        AssertResult("K(a, t) = a.~t.string\nK(7, {a+1})", Str("8"));
        AssertSameElaboratedBody("K(a, t) = a~.t.string", "K(a, t) = a.t.string");
    }

    [Fact]
    public void Chain_SecondPostfixGraceEdge_IsRejected()
        // The second edge's receiver is the first edge's RESULT — a non-name
        // expression — so it cannot carry the single-name Grace ordering.
        => AssertParseFails(
            """
            Dub(x) = x * 2
            Inc(x) = x + 1
            v = 5
            v~.Inc~.Dub
            """,
            GraceEligibilityFragment);

    [Fact]
    public void Chain_StructuralEdgeThenPostfixGrace_IsRejected()
        => AssertParseFails(
            """
            Inc(x) = x + 1
            Obj = {
                public V = 42
                0
            }
            Obj.V~.Inc
            """,
            GraceEligibilityFragment);

    [Fact]
    public void Chain_OrdinaryDotChain_IsUnchanged()
    {
        AssertResult("Inc(x) = x + 1\n1.Inc.Inc.Inc", Atom(4));
        AssertResult("Inc(x) = x + 1\nInc(Inc(Inc(1)))", Atom(4));
    }

    // ── H. Name-occurrence eligibility (the narrow Grace law) ───────────────

    [Fact]
    public void Eligibility_CompoundReceiver_IsRejectedNotDistributed()
    {
        AssertParseFails("K = (x + y)~.t", GraceEligibilityFragment);
        // The ORDINARY complex-receiver edge stays valid.
        AssertResult("K(x, y) = (x + y).t\nt(v) = v * 2\nK(1, 2)", Atom(6));
        // Prefix Grace after the dot decorates the bare fallback name, not the
        // compound receiver, and therefore remains eligible.
        AssertResult("K(x, y, t) = (x + y).~t\nK(1, 2, {v * 2})", Atom(6));
    }

    [Fact]
    public void Eligibility_RejectsEveryNonNameShape()
    {
        // The ONE eligibility law across receiver shapes: literals, groups,
        // calls, dot results, index results, lists, braces, strings, and
        // spreads all reject with the same diagnostic when postfix Grace is
        // applied to the receiver expression.
        AssertParseFails("t(a) = a + 1\n5~.t", GraceEligibilityFragment);
        AssertParseFails("K = f(x)~.t", GraceEligibilityFragment);
        AssertParseFails("K = [x, y]~.t", GraceEligibilityFragment);
        AssertParseFails("K = a.b~.t", GraceEligibilityFragment);
        AssertParseFails("S = 1, 2, 3\nK = (S:0)~.t", GraceEligibilityFragment);
        AssertParseFails("t(a) = a\n{1}~.t", GraceEligibilityFragment);
        AssertParseFails("t(a) = a\n'text'~.t", GraceEligibilityFragment);
        AssertParseFails("[1, 2, 3]~.sum", GraceEligibilityFragment);
        AssertParseFails("()~.count", GraceEligibilityFragment);
        AssertParseFails("(1, 2, 3)~.first", GraceEligibilityFragment);

        // The corresponding prefix-member forms are eligible because the
        // decorated occurrence is the bare member/fallback name.
        AssertResult("t(a) = a + 1\n5.~t", Atom(6));
        AssertResult("t(a) = a\n[1, 2].~t", List(Atom(1), Atom(2)));
    }

    [Fact]
    public void Eligibility_CaptureReceiver_IsRejected_OrdinaryCaptureUnchanged()
    {
        // Parentheses never smuggle an expression into Grace.
        AssertParseFails(StructuralSplit + "\n(Obj)~.V", GraceEligibilityFragment);
        // The ordinary capture receiver keeps its established semantics: a
        // capture has no structural identity, so the lexical `V` wins.
        AssertResult(StructuralSplit + "\n(Obj).V", Atom(99));
    }

    [Fact]
    public void Eligibility_SpreadReceiver_IsRejected_FluentSupplyUnchanged()
    {
        AssertResult("Collect(*items) = items\n[1, 2]*.Collect", List(Atom(1), Atom(2)));
        AssertParseFails("Collect(*items) = items\n[1, 2]*~.Collect", GraceEligibilityFragment);
        AssertResult("Collect(*items) = items\n[1, 2]*.~Collect", List(Atom(1), Atom(2)));
        AssertParseFails("K = xs*~.F", GraceEligibilityFragment);
    }

    [Fact]
    public void Eligibility_InvalidReceiver_RecoversAsTheOrdinaryGracelessEdge()
    {
        const string source = "K = f(x)~.t";
        var syntax = Parser.ParseSyntax(source);

        Assert.Single(
            syntax.Diagnostics,
            diagnostic => diagnostic.Message.Contains(GraceEligibilityFragment, StringComparison.Ordinal));

        // Recovery is the ordinary dot edge (as if the marker were absent):
        // useful structure and spans for tooling, no ordering assigned.
        var rawK = Assert.IsType<Algorithm.User>(Assert.Single(syntax.Root.Properties).Value);
        var rawEdge = Assert.IsType<Expr.DotCall>(Assert.Single(rawK.Output));
        Assert.Equal("t", rawEdge.Name);
        Assert.IsType<Expr.Call>(rawEdge.Target);
        Assert.Equal(new SourceSpan(1, 11, 1, 11), rawEdge.MemberSpan);
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(syntax.Root));

        var elaborated = Parser.Parse(source);
        Assert.True(elaborated.HasErrors);
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(elaborated.Root));
        // No Grace ordering was assigned: the recovered signature is the
        // ordinary semantic occurrence order (the receiver call's names,
        // then the member/fallback occurrence).
        Assert.Equal(
            ["f", "x", "t"],
            Assert.Single(elaborated.Root.Properties).Value.Params);
    }

    // ── I. Adjacency and Grace preservation ─────────────────────────────────

    [Fact]
    public void Adjacency_DetachedTilde_KeepsGraceMeaning()
        // `a ~ .t`: the tilde is not attached to the dot, so it stays postfix
        // grace on `a` and the dot edge is ordinary. Postfix grace (+1) moves
        // `a` later than the following member/fallback occurrence.
        => AssertResult("K(a, t) = a ~ .t\nK(7, {a+1})", Atom(8));

    [Fact]
    public void Adjacency_DetachedTilde_HasTheOrdinaryPostfixGraceOrder()
        => Assert.Equal(["t", "a"], ParamsOf("K = a ~ .t"));

    [Fact]
    public void Adjacency_RepeatedPostfixGrace_ComposesWithDot()
        => AssertResult("K(a, t) = a~~.t\nK(7, {a+1})", Atom(8));

    [Fact]
    public void Adjacency_PostfixReceiverAndPrefixMemberGrace_BothCompose()
    {
        Assert.Equal(["t", "a"], ParamsOf("K = a~.~t"));
        AssertResult("K = a~.~t\nK({a+1}, 7)", Atom(8));
    }

    [Fact]
    public void Adjacency_PostfixGrace_DoesNotContinueFromANewPhysicalLine()
        => AssertParseFails(
            "K(a, t) = a\n~.t\nK(7, {a+1})",
            "Grace `~` can only be applied to a parameter or name occurrence");

    [Fact]
    public void Adjacency_LeadingDotContinuation_CanCarryPrefixMemberGrace()
    {
        var source = "K(a, t) = a\n.~t\nK(7, {a+1})";
        var root = SourceProvenance.ParseValid(source).Root;
        var edge = Assert.IsType<Expr.DotCall>(root.Properties[0].Value.Output[0]);
        Assert.Equal("t", edge.Name);
        AssertResult(source, Atom(8));
    }

    [Fact]
    public void Adjacency_PrefixMemberGrace_MemberOnNextLine_MirrorsOrdinaryTrailingDot()
    {
        var graced = Parser.Parse("K(a, t) = a.~\nt\nK(7, {a+1})");
        var ordinary = Parser.Parse("Obj = {public V = 42}\nObj.\nV");
        Assert.Equal(ordinary.HasErrors, graced.HasErrors);
        if (!graced.HasErrors)
            AssertResult("K(a, t) = a.~\nt\nK(7, {a+1})", Atom(8));
    }

    // ── J. The stored fallback decides — wrapper topology is irrelevant ─────

    [Fact]
    public void WrapperDivergence_IsGone_ChainedDotAgreesWithPlainForm()
    {
        // 0.8.159 residual defect: with a same-name visible property, the
        // chained `a.t.string` evaluated its inner dot edge under a synthetic
        // algorithm-position wrapper that hid the parameter's local ownership
        // from the runtime gate, so the dotted form resolved the property
        // while plain `t(a).string` resolved the parameter. The binding now
        // rides the expression itself, so wrapper topology cannot change it.
        AssertResult("t = 5\nK(a, t) = a.t.string\nK(7, {a+1})", Str("8"));
        AssertResult("t = 5\nK(a, t) = t(a).string\nK(7, {a+1})", Str("8"));
    }

    [Fact]
    public void HostBuiltDotCall_WithoutFallback_KeepsPlainLexicalSemantics()
    {
        // A host-built DotCall carries no elaborated fallback (null =>
        // Resolve(Name)): with no lexical `t` in sight the member fails as
        // unknown even though a dynamically visible `t` binding exists — the
        // stored identity, not the runtime environment, decides.
        var k = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("a"), new ParameterDeclaration("t")],
            Opens: [],
            Properties: [],
            Output: [new Expr.DotCall(new Expr.Param("a"), "t")]);
        var increment = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("x")],
            Opens: [],
            Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1m))]);
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("K", k)],
            Output:
            [
                new Expr.Call(
                    new Expr.Resolve("K"),
                    [new Expr.Num(7m), new Expr.AlgorithmExpr(increment)]),
            ]);

        var plain = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.True(plain.IsError);
        Assert.IsType<EvalError.UnknownName>(Innermost(plain.Error));
    }

    [Fact]
    public void OptimizerOnOrOff_SeesTheSameEdgeInBothSpellings()
    {
        // Optimizer eligibility is decided on the elaborated body, which is
        // identical for both spellings, so neither the results nor the
        // optimizer's own view can depend on source grace provenance.
        static Result Run(string source, bool loops, bool pipelines)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            var evaluated = Evaluator.Run(
                new Expr.AlgorithmExpr(root),
                new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(),
                loops,
                loopDiagnostics: null,
                pipelines,
                sequenceDiagnostics: null);
            Assert.False(evaluated.IsError, $"Unexpected error: {(evaluated.IsError ? evaluated.Error : null)}");
            return evaluated.Value;
        }

        foreach (var (ordinary, graced) in new[]
        {
            ("K = a.t\nK(7, {x + 1})", "K = a~.t\nK({x + 1}, 7)"),
            ("K = a.t\nK(7, {x + 1})", "K = a.~t\nK({x + 1}, 7)"),
            ("K(xs) = xs.filter({a > 1}).count\nK((1, 2, 3))", "K(xs) = xs~.filter({a > 1}).count\nK((1, 2, 3))"),
            ("K(xs) = xs.filter({a > 1}).count\nK((1, 2, 3))", "K(xs) = xs.~filter({a > 1}).count\nK((1, 2, 3))"),
            ("S = 1, 2, 3\nS.take(2)", "S = 1, 2, 3\nS~.take(2)"),
            ("S = 1, 2, 3\nS.take(2)", "S = 1, 2, 3\nS.~take(2)"),
            ("V(x) = 99\nObj = {\n    public V = 42\n    0\n}\nObj.V", "V(x) = 99\nObj = {\n    public V = 42\n    0\n}\nObj~.V"),
            ("V(x) = 99\nObj = {\n    public V = 42\n    0\n}\nObj.V", "V(x) = 99\nObj = {\n    public V = 42\n    0\n}\nObj.~V"),
        })
        {
            foreach (var (loops, pipelines) in new[] { (true, true), (false, false) })
            {
                Assert.True(
                    Result.ValueComparer.Equals(
                        Run(ordinary, loops, pipelines),
                        Run(graced, loops, pipelines)),
                    $"Spellings diverged with loops={loops}, pipelines={pipelines}:{Environment.NewLine}{ordinary}");
            }

            Assert.True(
                Result.ValueComparer.Equals(
                    Run(graced, true, true),
                    Run(graced, false, false)),
                $"Optimizer changed the result of:{Environment.NewLine}{graced}");
        }
    }

    [Fact]
    public void UnknownMember_RendersTheOrdinaryDotDiagnostic_InBothSpellings()
    {
        // Both spellings ARE the dot edge, so a member miss renders the dot
        // diagnostic — the marker never switches to call-style wording.
        static string MessageOf(string source)
            => KatLangError.FromEvalError(
                Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root)).Error).Message;

        var ordinary = MessageOf("K(a) = a.Missing\nK(1)");
        var graced = MessageOf("K(a) = a~.Missing\nK(1)");
        Assert.Contains("Property 'Missing' was not found on", ordinary);
        Assert.Equal(ordinary, graced);
    }
}
